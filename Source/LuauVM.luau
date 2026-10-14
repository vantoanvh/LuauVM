--!optimize 2
--!strict

--[[
	Loads Luau bytecode and runs it with a direct-threaded closure interpreter written for speed.

	Paradigm
		Each bytecode instruction is decoded once into its own handler closure with its operands captured as upvalues, so executing
		an instruction is one call: no opcode dispatch tree and no operand array loads.
		AUX words, CAPTURE words, FASTCALL hints and other no-ops are removed, and pure jumps (JUMP, JUMPX, JUMPBACK, CMPPROTO) are
		threaded away: edges into them lead straight to their destination. Constants and resolved imports are captured directly.
		Handlers are direct-threaded: a handler finishes by calling its successor (`return OnNext(Stack)`) instead of returning it to
		a dispatch loop. Edges that could grow the host call stack without bound return the successor to the Entry loop instead:
		backward edges, edges into calls and into the FORGLOOP of a plain FORGPREP (so recursion costs two host frames per level),
		and edges past ChainLimit chained frames. Every maker therefore has a chained copy and a trampolined copy of its handler.
		Every VM closure is a host function; a VM-to-VM call is an ordinary host call, so recursion, coroutines, and pcall behave natively.

	Invariants
		A handler takes the register file and returns the next handler to run, or nil to end the function.
		Handlers are made back to front, so every forward successor exists when its maker runs and is passed in: a chained edge
		calls it as a captured constant. A trampolined edge reads a patchable successor, which Decode links once every handler of the
		proto exists; only backward edges need that.
		Register file layout: [1] upvalues, [2] varargs, [3] vararg count, [4] open upvalues, [5] top, registers from [6].
		Return handlers store their results in the register file and a result kind in [3]: 0 none, 1 one value at [1], 2 two values at [1] and [2], 3 the range [1]..[2].
		Imports resolve once at load against the Env table, exactly like the reference VM does for a safe environment.

	Design Notes
		Errors propagate unwrapped with host positions; there are no hooks, no error wrapper, and no per-instruction bookkeeping.
		Close() relinks every backward edge to a handler that ends the function, so loops stop at their next iteration without any
		per-iteration check; a generic-for loop still calls its iterator once more first.
]]

-- Environment changes in the VM are not supposed to alter the behaviour of the VM so we localise globals beforehand ( from Fiu )

const Type = type
const Typeof = typeof
const Error = error
const Next = next
const Select = select
const Tonumber = tonumber
const Rawget = rawget
const Rawequal = rawequal
const Getmetatable = getmetatable

const StringFormat = string.format

const TablePack = table.pack
const TableClone = table.clone
const TableCreate = table.create
const TableMove = table.move
const TableUnpack = table.unpack

const BufferFromString = buffer.fromstring
const BufferLen = buffer.len
const BufferReadU8 = buffer.readu8
const BufferReadU32 = buffer.readu32
const BufferReadF32 = buffer.readf32
const BufferReadF64 = buffer.readf64
const BufferReadString = buffer.readstring

const Bit32BOr = bit32.bor
const Bit32BAnd = bit32.band
const Bit32BTest = bit32.btest
const Bit32RShift = bit32.rshift
const Bit32LShift = bit32.lshift
const Bit32Extract = bit32.extract

const IntegerFromString = integer and integer.fromstring or nil

const MathMax = math.max
const MathSqrt = math.sqrt

-- The iterator ipairs returns (luaB_inext); every ipairs of the host state returns this same function.
const Inext = (ipairs({}))

type Store = { [any]: any }

type Registers = { any }

type Handler = (Registers) -> Handler?

type Linker = (Handler, Handler) -> ()

type Factory = (Upvalues: { any }) -> (...any) -> ...any

-- An upvalue cell captured by reference: [1] the table holding the value, [2] its index there, [3] the value once closed. An open
-- cell points into the register file; closing it points it at its own slot 3. Numeric fields keep every read on the array fast path.
type Upvalue = { any }

type Cached = {
	Closure: any,
	Upvalues: { any },
}

type Proto = {
	MaxStackSize: number,
	ParamCount: number,
	UpvalueCount: number,
	IsVararg: boolean,
	First: Handler,
	Cells: { boolean },
	Make: Factory,
}

type Raw = {
	MaxStackSize: number,
	ParamCount: number,
	UpvalueCount: number,
	IsVararg: boolean,
	Words: { number },
	Constants: { any },
	ConstantKinds: { number },
	Protos: { number },
}

type BackEdge = {
	Link: Linker,
	OnNext: Handler,
	OnTarget: Handler,
	NextBack: boolean,
	TargetBack: boolean,
}

type Settings = {
	VectorCtor: (...number) -> any,
	VectorSize: number,
}

const LuaMultRet = -1
const EmptyVarargs: { any } = {}
const RegisterBase = 5

-- Upvalue table of every closure that captures nothing; no handler ever indexes it.
const NoUpvalues: { any } = {}

-- Longest run of handlers that call each other directly before one returns its successor to the Entry loop.
const ChainLimit = 64

-- Bytecode opcodes followed by an AUX word.
const HasAux: { [number]: boolean } = {
	[7] = true, [8] = true, [12] = true, [15] = true, [16] = true, [20] = true, [27] = true, [28] = true, [29] = true,
	[30] = true, [31] = true, [32] = true, [53] = true, [55] = true, [58] = true, [60] = true, [66] = true, [74] = true,
	[75] = true, [77] = true, [78] = true, [79] = true, [80] = true, [83] = true, [84] = true, [85] = true, [86] = true,
	[87] = true, [88] = true, [90] = true, [91] = true,
}

-- Bytecode opcodes that decode to nothing: NOP, BREAK, FASTCALL3, PREPVARARGS, FASTCALL, COVERAGE, CAPTURE, FASTCALL1/2/2K, FASTPCALL.
const Removed: { [number]: boolean } = {
	[0] = true, [1] = true, [60] = true, [65] = true, [68] = true, [69] = true, [70] = true, [73] = true, [74] = true,
	[75] = true, [89] = true,
}

-- Unconditional jumps that decode threads away: JUMP, JUMPBACK, JUMPX, CMPPROTO (which never matches here).
const PureJumps: { [number]: boolean } = {
	[23] = true, [24] = true, [67] = true, [88] = true,
}

-- Two-successor opcodes: conditional jumps and loop instructions; their D operand is the branch target.
const Branches: { [number]: boolean } = {
	[25] = true, [26] = true, [27] = true, [28] = true, [29] = true, [30] = true, [31] = true, [32] = true, [56] = true,
	[57] = true, [58] = true, [77] = true, [78] = true, [79] = true, [80] = true,
}

-- Opcodes always entered from the Entry loop, so a call into VM code starts at chain depth one: CALL and CALLFB. The FORGLOOP of a
-- loop prepared by plain FORGPREP is too, since its iterator may be VM code; pairs/ipairs loops iterate with next/inext and chain.
const Bounced: { [number]: boolean } = {
	[21] = true, [87] = true,
}

const function NewSettings(): Settings
	return {
		VectorCtor = vector.create :: (...number) -> any,
		VectorSize = 3,
	}
end

const function CloseUpvalue(Captured: Upvalue)
	Captured[3] = Captured[1][Captured[2]]
	Captured[1] = Captured
	Captured[2] = 3
end

-- The open upvalue cell for a register captured by reference, shared by every closure that captures that register.
const function Capture(Stack: Registers, Slot: number): Upvalue
	local Pending: { [number]: Upvalue } = Stack[4]

	if Pending == nil then
		Pending = {}
		Stack[4] = Pending
	end

	const Existing = Pending[Slot]

	if Existing == nil then
		-- slot 3 exists from the start, so closing the cell never grows it
		const Opened: Upvalue = { Stack, Slot, false }

		Pending[Slot] = Opened

		return Opened
	end

	return Existing
end

-- Replaces Inext in the iterator register of an ipairs loop over a table; ipairs-style FORGLOOP handlers recognize it and step
-- inline, and calling it behaves exactly like Inext on a table.
const function IpairsStep(Table: { any }, Index: number): (number?, any)
	const Following = Index + 1
	const Value = Rawget(Table, Following)

	if Value == nil then
		return nil, nil
	end

	return Following, Value
end

-- Ends the function with no results; unlinked edges and edges relinked by Close() lead here.
const function Stop(Stack: Registers): Handler?
	Stack[1] = nil
	Stack[2] = nil
	Stack[3] = 0

	return nil
end

const function Unlinked(OnNext: Handler, OnTarget: Handler) end

const function Unprepared(Upvalues: { any }): (...any) -> ...any
	return Error("proto used before it was prepared")
end

const function ResolveImport(Env: Store, Count: number, K0: any, K1: any, K2: any): any
	local Result = Env[K0]

	if Count < 2 or Result == nil then
		return Result
	end

	Result = Result[K1]

	if Count < 3 or Result == nil then
		return Result
	end

	return Result[K2]
end

-- Creates the closure factory of a decoded proto: it takes a closure's upvalues and returns the host function for that closure,
-- specialized by parameter count and varargs. Every closure of the proto shares one spare register file plus, for recursion, a
-- free list linked through slot [5] (top is always written before it is read).
const function MakeFactory(Proto: Proto): Factory
	const First = Proto.First
	const MaxStack = Proto.MaxStackSize
	const Params = Proto.ParamCount
	local Spare: Registers? = nil
	local Head: Registers? = nil

	if Proto.IsVararg and Params <= 2 then
		if Params == 0 then
			return function(Upvalues: { any }): (...any) -> ...any
				return function(...: any): ...any
					const Count = Select("#", ...)
					local Stack: Registers
					const Cached = Spare

					if Cached ~= nil then
						Stack = Cached
						Spare = nil
					else
						const Pooled = Head

						if Pooled ~= nil then
							Stack = Pooled
							Head = Pooled[5]
						else
							Stack = TableCreate(MaxStack) :: Registers
						end
					end

					Stack[1] = Upvalues
					Stack[2] = if Count == 0 then EmptyVarargs else { ... }
					Stack[3] = Count

					local Fn = First(Stack)

					while Fn do
						Fn = Fn(Stack)
					end

					const Pending: { [number]: Upvalue }? = Stack[4]

					if Pending ~= nil then
						for _, Captured in Pending do
							CloseUpvalue(Captured)
						end

						Stack[4] = nil
					end

					-- the register file is free again before the results are read: nothing runs in between
					if Spare == nil then
						Spare = Stack
					else
						Stack[5] = Head
						Head = Stack
					end

					const Kind = Stack[3]

					if Kind == 1 then
						return Stack[1]
					elseif Kind == 0 then
						return
					elseif Kind == 2 then
						return Stack[1], Stack[2]
					end

					return TableUnpack(Stack, Stack[1], Stack[2])
				end
			end
		elseif Params == 1 then
			return function(Upvalues: { any }): (...any) -> ...any
				return function(P1: any, ...: any): ...any
					const Count = Select("#", ...)
					local Stack: Registers
					const Cached = Spare

					if Cached ~= nil then
						Stack = Cached
						Spare = nil
					else
						const Pooled = Head

						if Pooled ~= nil then
							Stack = Pooled
							Head = Pooled[5]
						else
							Stack = TableCreate(MaxStack) :: Registers
						end
					end

					Stack[1] = Upvalues
					Stack[2] = if Count == 0 then EmptyVarargs else { ... }
					Stack[3] = Count
					Stack[6] = P1

					local Fn = First(Stack)

					while Fn do
						Fn = Fn(Stack)
					end

					const Pending: { [number]: Upvalue }? = Stack[4]

					if Pending ~= nil then
						for _, Captured in Pending do
							CloseUpvalue(Captured)
						end

						Stack[4] = nil
					end

					-- the register file is free again before the results are read: nothing runs in between
					if Spare == nil then
						Spare = Stack
					else
						Stack[5] = Head
						Head = Stack
					end

					const Kind = Stack[3]

					if Kind == 1 then
						return Stack[1]
					elseif Kind == 0 then
						return
					elseif Kind == 2 then
						return Stack[1], Stack[2]
					end

					return TableUnpack(Stack, Stack[1], Stack[2])
				end
			end
		elseif Params == 2 then
			return function(Upvalues: { any }): (...any) -> ...any
				return function(P1: any, P2: any, ...: any): ...any
					const Count = Select("#", ...)
					local Stack: Registers
					const Cached = Spare

					if Cached ~= nil then
						Stack = Cached
						Spare = nil
					else
						const Pooled = Head

						if Pooled ~= nil then
							Stack = Pooled
							Head = Pooled[5]
						else
							Stack = TableCreate(MaxStack) :: Registers
						end
					end

					Stack[1] = Upvalues
					Stack[2] = if Count == 0 then EmptyVarargs else { ... }
					Stack[3] = Count
					Stack[6] = P1
					Stack[7] = P2

					local Fn = First(Stack)

					while Fn do
						Fn = Fn(Stack)
					end

					const Pending: { [number]: Upvalue }? = Stack[4]

					if Pending ~= nil then
						for _, Captured in Pending do
							CloseUpvalue(Captured)
						end

						Stack[4] = nil
					end

					-- the register file is free again before the results are read: nothing runs in between
					if Spare == nil then
						Spare = Stack
					else
						Stack[5] = Head
						Head = Stack
					end

					const Kind = Stack[3]

					if Kind == 1 then
						return Stack[1]
					elseif Kind == 0 then
						return
					elseif Kind == 2 then
						return Stack[1], Stack[2]
					end

					return TableUnpack(Stack, Stack[1], Stack[2])
				end
			end
		end
	elseif not Proto.IsVararg and Params <= 4 then
		if Params == 0 then
			return function(Upvalues: { any }): (...any) -> ...any
				return function(): ...any
					local Stack: Registers
					const Cached = Spare

					if Cached ~= nil then
						Stack = Cached
						Spare = nil
					else
						const Pooled = Head

						if Pooled ~= nil then
							Stack = Pooled
							Head = Pooled[5]
						else
							Stack = TableCreate(MaxStack) :: Registers
							Stack[2] = EmptyVarargs
						end
					end

					Stack[1] = Upvalues

					local Fn = First(Stack)

					while Fn do
						Fn = Fn(Stack)
					end

					const Pending: { [number]: Upvalue }? = Stack[4]

					if Pending ~= nil then
						for _, Captured in Pending do
							CloseUpvalue(Captured)
						end

						Stack[4] = nil
					end

					-- the register file is free again before the results are read: nothing runs in between
					if Spare == nil then
						Spare = Stack
					else
						Stack[5] = Head
						Head = Stack
					end

					const Kind = Stack[3]

					if Kind == 1 then
						return Stack[1]
					elseif Kind == 0 then
						return
					elseif Kind == 2 then
						return Stack[1], Stack[2]
					end

					return TableUnpack(Stack, Stack[1], Stack[2])
				end
			end
		elseif Params == 1 then
			return function(Upvalues: { any }): (...any) -> ...any
				return function(P1: any): ...any
					local Stack: Registers
					const Cached = Spare

					if Cached ~= nil then
						Stack = Cached
						Spare = nil
					else
						const Pooled = Head

						if Pooled ~= nil then
							Stack = Pooled
							Head = Pooled[5]
						else
							Stack = TableCreate(MaxStack) :: Registers
							Stack[2] = EmptyVarargs
						end
					end

					Stack[1] = Upvalues
					Stack[6] = P1

					local Fn = First(Stack)

					while Fn do
						Fn = Fn(Stack)
					end

					const Pending: { [number]: Upvalue }? = Stack[4]

					if Pending ~= nil then
						for _, Captured in Pending do
							CloseUpvalue(Captured)
						end

						Stack[4] = nil
					end

					-- the register file is free again before the results are read: nothing runs in between
					if Spare == nil then
						Spare = Stack
					else
						Stack[5] = Head
						Head = Stack
					end

					const Kind = Stack[3]

					if Kind == 1 then
						return Stack[1]
					elseif Kind == 0 then
						return
					elseif Kind == 2 then
						return Stack[1], Stack[2]
					end

					return TableUnpack(Stack, Stack[1], Stack[2])
				end
			end
		elseif Params == 2 then
			return function(Upvalues: { any }): (...any) -> ...any
				return function(P1: any, P2: any): ...any
					local Stack: Registers
					const Cached = Spare

					if Cached ~= nil then
						Stack = Cached
						Spare = nil
					else
						const Pooled = Head

						if Pooled ~= nil then
							Stack = Pooled
							Head = Pooled[5]
						else
							Stack = TableCreate(MaxStack) :: Registers
							Stack[2] = EmptyVarargs
						end
					end

					Stack[1] = Upvalues
					Stack[6] = P1
					Stack[7] = P2

					local Fn = First(Stack)

					while Fn do
						Fn = Fn(Stack)
					end

					const Pending: { [number]: Upvalue }? = Stack[4]

					if Pending ~= nil then
						for _, Captured in Pending do
							CloseUpvalue(Captured)
						end

						Stack[4] = nil
					end

					-- the register file is free again before the results are read: nothing runs in between
					if Spare == nil then
						Spare = Stack
					else
						Stack[5] = Head
						Head = Stack
					end

					const Kind = Stack[3]

					if Kind == 1 then
						return Stack[1]
					elseif Kind == 0 then
						return
					elseif Kind == 2 then
						return Stack[1], Stack[2]
					end

					return TableUnpack(Stack, Stack[1], Stack[2])
				end
			end
		elseif Params == 3 then
			return function(Upvalues: { any }): (...any) -> ...any
				return function(P1: any, P2: any, P3: any): ...any
					local Stack: Registers
					const Cached = Spare

					if Cached ~= nil then
						Stack = Cached
						Spare = nil
					else
						const Pooled = Head

						if Pooled ~= nil then
							Stack = Pooled
							Head = Pooled[5]
						else
							Stack = TableCreate(MaxStack) :: Registers
							Stack[2] = EmptyVarargs
						end
					end

					Stack[1] = Upvalues
					Stack[6] = P1
					Stack[7] = P2
					Stack[8] = P3

					local Fn = First(Stack)

					while Fn do
						Fn = Fn(Stack)
					end

					const Pending: { [number]: Upvalue }? = Stack[4]

					if Pending ~= nil then
						for _, Captured in Pending do
							CloseUpvalue(Captured)
						end

						Stack[4] = nil
					end

					-- the register file is free again before the results are read: nothing runs in between
					if Spare == nil then
						Spare = Stack
					else
						Stack[5] = Head
						Head = Stack
					end

					const Kind = Stack[3]

					if Kind == 1 then
						return Stack[1]
					elseif Kind == 0 then
						return
					elseif Kind == 2 then
						return Stack[1], Stack[2]
					end

					return TableUnpack(Stack, Stack[1], Stack[2])
				end
			end
		else
			return function(Upvalues: { any }): (...any) -> ...any
				return function(P1: any, P2: any, P3: any, P4: any): ...any
					local Stack: Registers
					const Cached = Spare

					if Cached ~= nil then
						Stack = Cached
						Spare = nil
					else
						const Pooled = Head

						if Pooled ~= nil then
							Stack = Pooled
							Head = Pooled[5]
						else
							Stack = TableCreate(MaxStack) :: Registers
							Stack[2] = EmptyVarargs
						end
					end

					Stack[1] = Upvalues
					Stack[6] = P1
					Stack[7] = P2
					Stack[8] = P3
					Stack[9] = P4

					local Fn = First(Stack)

					while Fn do
						Fn = Fn(Stack)
					end

					const Pending: { [number]: Upvalue }? = Stack[4]

					if Pending ~= nil then
						for _, Captured in Pending do
							CloseUpvalue(Captured)
						end

						Stack[4] = nil
					end

					-- the register file is free again before the results are read: nothing runs in between
					if Spare == nil then
						Spare = Stack
					else
						Stack[5] = Head
						Head = Stack
					end

					const Kind = Stack[3]

					if Kind == 1 then
						return Stack[1]
					elseif Kind == 0 then
						return
					elseif Kind == 2 then
						return Stack[1], Stack[2]
					end

					return TableUnpack(Stack, Stack[1], Stack[2])
				end
			end
		end
	end

	return function(Upvalues: { any }): (...any) -> ...any
		return function(...: any): ...any
			const Passed = TablePack(...)
			local Stack: Registers
			const Cached = Spare

			if Cached ~= nil then
				Stack = Cached
				Spare = nil
			else
				const Pooled = Head

				if Pooled ~= nil then
					Stack = Pooled
					Head = Pooled[5]
				else
					Stack = TableCreate(MaxStack) :: Registers
				end
			end

			Stack[1] = Upvalues
			TableMove(Passed, 1, Params, RegisterBase + 1, Stack)

			if Passed.n > Params then
				Stack[2] = TableMove(Passed, Params + 1, Passed.n, 1, {})
				Stack[3] = Passed.n - Params
			else
				Stack[2] = EmptyVarargs
				Stack[3] = 0
			end

			local Fn = First(Stack)

			while Fn do
				Fn = Fn(Stack)
			end

			const Pending: { [number]: Upvalue }? = Stack[4]

			if Pending ~= nil then
				for _, Captured in Pending do
					CloseUpvalue(Captured)
				end

				Stack[4] = nil
			end

			-- the register file is free again before the results are read: nothing runs in between
			if Spare == nil then
				Spare = Stack
			else
				Stack[5] = Head
				Head = Stack
			end

			const Kind = Stack[3]

			if Kind == 1 then
				return Stack[1]
			elseif Kind == 0 then
				return
			elseif Kind == 2 then
				return Stack[1], Stack[2]
			end

			return TableUnpack(Stack, Stack[1], Stack[2])
		end
	end
end

const function MakeAdd(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, B: number, C: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A] = Stack[B] + Stack[C]

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A] = Stack[B] + Stack[C]

		return NextFn
	end, Link
end

const function MakeSub(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, B: number, C: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A] = Stack[B] - Stack[C]

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A] = Stack[B] - Stack[C]

		return NextFn
	end, Link
end

const function MakeMul(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, B: number, C: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A] = Stack[B] * Stack[C]

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A] = Stack[B] * Stack[C]

		return NextFn
	end, Link
end

const function MakeDiv(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, B: number, C: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A] = Stack[B] / Stack[C]

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A] = Stack[B] / Stack[C]

		return NextFn
	end, Link
end

const function MakeMod(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, B: number, C: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A] = Stack[B] % Stack[C]

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A] = Stack[B] % Stack[C]

		return NextFn
	end, Link
end

const function MakePow(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, B: number, C: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A] = Stack[B] ^ Stack[C]

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A] = Stack[B] ^ Stack[C]

		return NextFn
	end, Link
end

const function MakeIDiv(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, B: number, C: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A] = Stack[B] // Stack[C]

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A] = Stack[B] // Stack[C]

		return NextFn
	end, Link
end

const function MakeAddK(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, B: number, K: any): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A] = Stack[B] + K

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A] = Stack[B] + K

		return NextFn
	end, Link
end

const function MakeSubK(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, B: number, K: any): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A] = Stack[B] - K

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A] = Stack[B] - K

		return NextFn
	end, Link
end

const function MakeMulK(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, B: number, K: any): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A] = Stack[B] * K

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A] = Stack[B] * K

		return NextFn
	end, Link
end

const function MakeDivK(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, B: number, K: any): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A] = Stack[B] / K

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A] = Stack[B] / K

		return NextFn
	end, Link
end

const function MakeModK(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, B: number, K: any): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A] = Stack[B] % K

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A] = Stack[B] % K

		return NextFn
	end, Link
end

const function MakeIDivK(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, B: number, K: any): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A] = Stack[B] // K

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A] = Stack[B] // K

		return NextFn
	end, Link
end

const function MakeSubRK(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, C: number, K: any): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A] = K - Stack[C]

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A] = K - Stack[C]

		return NextFn
	end, Link
end

const function MakeDivRK(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, C: number, K: any): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A] = K / Stack[C]

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A] = K / Stack[C]

		return NextFn
	end, Link
end

const function MakePowK(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, B: number, K: any): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			const Base = Stack[B]

			-- pow is slow, so the reference VM specializes ^2, ^0.5 and ^3 for numbers; results differ in the last digits
			if Type(Base) ~= "number" then
				Stack[A] = Base ^ K
			elseif K == 2 then
				Stack[A] = Base * Base
			elseif K == 0.5 then
				Stack[A] = MathSqrt(Base)
			elseif K == 3 then
				Stack[A] = Base * Base * Base
			else
				Stack[A] = Base ^ K
			end

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		const Base = Stack[B]

		-- pow is slow, so the reference VM specializes ^2, ^0.5 and ^3 for numbers; results differ in the last digits
		if Type(Base) ~= "number" then
			Stack[A] = Base ^ K
		elseif K == 2 then
			Stack[A] = Base * Base
		elseif K == 0.5 then
			Stack[A] = MathSqrt(Base)
		elseif K == 3 then
			Stack[A] = Base * Base * Base
		else
			Stack[A] = Base ^ K
		end

		return NextFn
	end, Link
end

const function MakeAnd(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, B: number, C: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A] = Stack[B] and Stack[C]

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A] = Stack[B] and Stack[C]

		return NextFn
	end, Link
end

const function MakeOr(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, B: number, C: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A] = Stack[B] or Stack[C]

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A] = Stack[B] or Stack[C]

		return NextFn
	end, Link
end

const function MakeAndK(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, B: number, K: any): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A] = Stack[B] and K

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A] = Stack[B] and K

		return NextFn
	end, Link
end

const function MakeOrK(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, B: number, K: any): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A] = Stack[B] or K

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A] = Stack[B] or K

		return NextFn
	end, Link
end

const function MakeNot(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, B: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A] = not Stack[B]

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A] = not Stack[B]

		return NextFn
	end, Link
end

const function MakeMinus(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, B: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A] = -Stack[B]

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A] = -Stack[B]

		return NextFn
	end, Link
end

const function MakeLength(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, B: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A] = #Stack[B]

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A] = #Stack[B]

		return NextFn
	end, Link
end

const function MakeLoadK(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, K: any): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A] = K

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A] = K

		return NextFn
	end, Link
end

const function MakeLoadNil(Mode: number, OnNext: Handler, OnTarget: Handler, A: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A] = nil

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A] = nil

		return NextFn
	end, Link
end

const function MakeMove(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, B: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A] = Stack[B]

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A] = Stack[B]

		return NextFn
	end, Link
end

const function MakeJump(Mode: number, OnNext: Handler, OnTarget: Handler): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		return NextFn
	end, Link
end

const function MakeGetTable(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, B: number, C: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A] = Stack[B][Stack[C]]

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A] = Stack[B][Stack[C]]

		return NextFn
	end, Link
end

const function MakeSetTable(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, B: number, C: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[B][Stack[C]] = Stack[A]

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[B][Stack[C]] = Stack[A]

		return NextFn
	end, Link
end

const function MakeGetTableKS(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, B: number, K: any): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A] = Stack[B][K]

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A] = Stack[B][K]

		return NextFn
	end, Link
end

const function MakeSetTableKS(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, B: number, K: any): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[B][K] = Stack[A]

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[B][K] = Stack[A]

		return NextFn
	end, Link
end

const function MakeGetTableN(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, B: number, Index: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A] = Stack[B][Index]

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A] = Stack[B][Index]

		return NextFn
	end, Link
end

const function MakeSetTableN(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, B: number, Index: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[B][Index] = Stack[A]

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[B][Index] = Stack[A]

		return NextFn
	end, Link
end

const function MakeNewClassMember(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, C: number, K: any): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A][K] = Stack[C]

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A][K] = Stack[C]

		return NextFn
	end, Link
end

const function MakeNewTable(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, Size: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A] = TableCreate(Size)

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A] = TableCreate(Size)

		return NextFn
	end, Link
end

const function MakeNewTableEmpty(Mode: number, OnNext: Handler, OnTarget: Handler, A: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A] = {}

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A] = {}

		return NextFn
	end, Link
end

const function MakeDupTable(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, Template: Store): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A] = TableClone(Template)

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A] = TableClone(Template)

		return NextFn
	end, Link
end

const function MakeSetList(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, B: number, CountPlusOne: number, Start: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			const Count = if CountPlusOne == 0 then Stack[5] - B + 1 else CountPlusOne - 1

			TableMove(Stack, B, B + Count - 1, Start, Stack[A])

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		const Count = if CountPlusOne == 0 then Stack[5] - B + 1 else CountPlusOne - 1

		TableMove(Stack, B, B + Count - 1, Start, Stack[A])

		return NextFn
	end, Link
end

const function MakeNameCall(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, A1: number, B: number, Method: any): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			const Object = Stack[B]
			const Found = Object[Method]

			if Found == nil then
				Error(`attempt to call missing method '{Method}' of {Typeof(Object)}`)
			end

			Stack[A1] = Object
			Stack[A] = Found

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		const Object = Stack[B]
		const Found = Object[Method]

		if Found == nil then
			Error(`attempt to call missing method '{Method}' of {Typeof(Object)}`)
		end

		Stack[A1] = Object
		Stack[A] = Found

		return NextFn
	end, Link
end

const function MakeConcat2(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, B: number, B1: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A] = Stack[B] .. Stack[B1]

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A] = Stack[B] .. Stack[B1]

		return NextFn
	end, Link
end

const function MakeConcat3(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, B: number, B1: number, B2: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A] = Stack[B] .. Stack[B1] .. Stack[B2]

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A] = Stack[B] .. Stack[B1] .. Stack[B2]

		return NextFn
	end, Link
end

const function MakeConcatN(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, B: number, C: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			local Result = Stack[C]

			for Index = C - 1, B, -1 do
				Result = Stack[Index] .. Result
			end

			Stack[A] = Result

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		local Result = Stack[C]

		for Index = C - 1, B, -1 do
			Result = Stack[Index] .. Result
		end

		Stack[A] = Result

		return NextFn
	end, Link
end

const function MakeGetGlobal(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, K: any, Env: Store): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A] = Env[K]

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A] = Env[K]

		return NextFn
	end, Link
end

const function MakeSetGlobal(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, K: any, Env: Store): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Env[K] = Stack[A]

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Env[K] = Stack[A]

		return NextFn
	end, Link
end

const function MakeGetImportSlow(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, Import: { any }, Env: Store): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			const Count = Import[1]
			local Result = Env[Import[2]]

			if Count >= 2 then
				Result = Result[Import[3]]

				if Count >= 3 then
					Result = Result[Import[4]]
				end
			end

			Stack[A] = Result

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		const Count = Import[1]
		local Result = Env[Import[2]]

		if Count >= 2 then
			Result = Result[Import[3]]

			if Count >= 3 then
				Result = Result[Import[4]]
			end
		end

		Stack[A] = Result

		return NextFn
	end, Link
end

const function MakeGetUpvalValue(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, B: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A] = Stack[1][B]

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A] = Stack[1][B]

		return NextFn
	end, Link
end

const function MakeGetUpval(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, B: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			const Captured = Stack[1][B]

			Stack[A] = Captured[1][Captured[2]]

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		const Captured = Stack[1][B]

		Stack[A] = Captured[1][Captured[2]]

		return NextFn
	end, Link
end

const function MakeSetUpval(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, B: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			const Captured = Stack[1][B]

			Captured[1][Captured[2]] = Stack[A]

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		const Captured = Stack[1][B]

		Captured[1][Captured[2]] = Stack[A]

		return NextFn
	end, Link
end

const function MakeCloseUpvals(Mode: number, OnNext: Handler, OnTarget: Handler, A: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			const Pending: { [number]: Upvalue }? = Stack[4]

			if Pending ~= nil then
				for Index, Captured in Pending do
					if Index >= A then
						CloseUpvalue(Captured)
						Pending[Index] = nil
					end
				end
			end

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		const Pending: { [number]: Upvalue }? = Stack[4]

		if Pending ~= nil then
			for Index, Captured in Pending do
				if Index >= A then
					CloseUpvalue(Captured)
					Pending[Index] = nil
				end
			end
		end

		return NextFn
	end, Link
end

const function MakeGetVarargs(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, CountPlusOne: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			local Count = CountPlusOne - 1

			if Count == LuaMultRet then
				Count = Stack[3]
				Stack[5] = A + Count - 1
			end

			TableMove(Stack[2], 1, Count, A, Stack)

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		local Count = CountPlusOne - 1

		if Count == LuaMultRet then
			Count = Stack[3]
			Stack[5] = A + Count - 1
		end

		TableMove(Stack[2], 1, Count, A, Stack)

		return NextFn
	end, Link
end

const function MakeNewClosureEmpty(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, Child: Proto): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A] = Child.Make(NoUpvalues)

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A] = Child.Make(NoUpvalues)

		return NextFn
	end, Link
end

const function MakeNewClosure(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, Description: { any }): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			const Child: Proto = Description[1]
			const Inherited = Stack[1]
			const Upvalues: { any } = TableCreate(Child.UpvalueCount)

			Stack[A] = Child.Make(Upvalues)

			for Index = 1, Child.UpvalueCount do
				const Kind = Description[Index * 2]
				const Slot = Description[Index * 2 + 1]

				if Kind == 0 then -- value
					Upvalues[Index] = Stack[Slot]
				elseif Kind == 1 then -- reference
					Upvalues[Index] = Capture(Stack, Slot)
				else -- upvalue
					Upvalues[Index] = Inherited[Slot]
				end
			end

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		const Child: Proto = Description[1]
		const Inherited = Stack[1]
		const Upvalues: { any } = TableCreate(Child.UpvalueCount)

		Stack[A] = Child.Make(Upvalues)

		for Index = 1, Child.UpvalueCount do
			const Kind = Description[Index * 2]
			const Slot = Description[Index * 2 + 1]

			if Kind == 0 then -- value
				Upvalues[Index] = Stack[Slot]
			elseif Kind == 1 then -- reference
				Upvalues[Index] = Capture(Stack, Slot)
			else -- upvalue
				Upvalues[Index] = Inherited[Slot]
			end
		end

		return NextFn
	end, Link
end

const function MakeDupClosure(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, Description: { any }): (Handler, Linker)
	local Cached: Cached? = nil

	if Mode == 1 then
		return function(Stack: Registers): Handler?
			const Child: Proto = Description[1]
			const Inherited = Stack[1]
			local CanReuse = Cached ~= nil

			if Cached then
				-- the cached closure is saved first because it may capture itself by value
				Stack[A] = Cached.Closure

				for Index = 1, Child.UpvalueCount do
					const Kind = Description[Index * 2]
					const Slot = Description[Index * 2 + 1]
					const Previous = Cached.Upvalues[Index]

					if Kind == 0 then -- value capture
						if not Rawequal(Previous, Stack[Slot]) then
							CanReuse = false

							break
						end
					elseif not Rawequal(Previous, Inherited[Slot]) then -- upvalue capture
						CanReuse = false

						break
					end
				end
			end

			if not CanReuse then
				const Upvalues: { any } = {}
				const Closure = Child.Make(Upvalues)

				Stack[A] = Closure

				for Index = 1, Child.UpvalueCount do
					const Kind = Description[Index * 2]
					const Slot = Description[Index * 2 + 1]

					if Kind == 0 then -- value
						Upvalues[Index] = Stack[Slot]
					else -- upvalue; references are not handled by DUPCLOSURE
						Upvalues[Index] = Inherited[Slot]
					end
				end

				if Cached == nil then
					Cached = { Closure = Closure, Upvalues = Upvalues }
				end
			end

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		const Child: Proto = Description[1]
		const Inherited = Stack[1]
		local CanReuse = Cached ~= nil

		if Cached then
			-- the cached closure is saved first because it may capture itself by value
			Stack[A] = Cached.Closure

			for Index = 1, Child.UpvalueCount do
				const Kind = Description[Index * 2]
				const Slot = Description[Index * 2 + 1]
				const Previous = Cached.Upvalues[Index]

				if Kind == 0 then -- value capture
					if not Rawequal(Previous, Stack[Slot]) then
						CanReuse = false

						break
					end
				elseif not Rawequal(Previous, Inherited[Slot]) then -- upvalue capture
					CanReuse = false

					break
				end
			end
		end

		if not CanReuse then
			const Upvalues: { any } = {}
			const Closure = Child.Make(Upvalues)

			Stack[A] = Closure

			for Index = 1, Child.UpvalueCount do
				const Kind = Description[Index * 2]
				const Slot = Description[Index * 2 + 1]

				if Kind == 0 then -- value
					Upvalues[Index] = Stack[Slot]
				else -- upvalue; references are not handled by DUPCLOSURE
					Upvalues[Index] = Inherited[Slot]
				end
			end

			if Cached == nil then
				Cached = { Closure = Closure, Upvalues = Upvalues }
			end
		end

		return NextFn
	end, Link
end

const function MakeCall0x0(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, A1: number, A2: number, A3: number, A4: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A]()

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A]()

		return NextFn
	end, Link
end

const function MakeCall0x1(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, A1: number, A2: number, A3: number, A4: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A] = Stack[A]()

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A] = Stack[A]()

		return NextFn
	end, Link
end

const function MakeCall0x2(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, A1: number, A2: number, A3: number, A4: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A], Stack[A1] = Stack[A]()

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A], Stack[A1] = Stack[A]()

		return NextFn
	end, Link
end

const function MakeCall0x3(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, A1: number, A2: number, A3: number, A4: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A], Stack[A1], Stack[A2] = Stack[A]()

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A], Stack[A1], Stack[A2] = Stack[A]()

		return NextFn
	end, Link
end

const function MakeCall0(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, A1: number, A2: number, A3: number, A4: number, C: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			const Results = TablePack(Stack[A]())
			local ResultCount = Results.n

			if C == 0 then
				Stack[5] = A + ResultCount - 1
			else
				ResultCount = C - 1
			end

			TableMove(Results, 1, ResultCount, A, Stack)

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		const Results = TablePack(Stack[A]())
		local ResultCount = Results.n

		if C == 0 then
			Stack[5] = A + ResultCount - 1
		else
			ResultCount = C - 1
		end

		TableMove(Results, 1, ResultCount, A, Stack)

		return NextFn
	end, Link
end

const function MakeCall1x0(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, A1: number, A2: number, A3: number, A4: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A](Stack[A1])

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A](Stack[A1])

		return NextFn
	end, Link
end

const function MakeCall1x1(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, A1: number, A2: number, A3: number, A4: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A] = Stack[A](Stack[A1])

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A] = Stack[A](Stack[A1])

		return NextFn
	end, Link
end

const function MakeCall1x2(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, A1: number, A2: number, A3: number, A4: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A], Stack[A1] = Stack[A](Stack[A1])

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A], Stack[A1] = Stack[A](Stack[A1])

		return NextFn
	end, Link
end

const function MakeCall1x3(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, A1: number, A2: number, A3: number, A4: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A], Stack[A1], Stack[A2] = Stack[A](Stack[A1])

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A], Stack[A1], Stack[A2] = Stack[A](Stack[A1])

		return NextFn
	end, Link
end

const function MakeCall1(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, A1: number, A2: number, A3: number, A4: number, C: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			const Results = TablePack(Stack[A](Stack[A1]))
			local ResultCount = Results.n

			if C == 0 then
				Stack[5] = A + ResultCount - 1
			else
				ResultCount = C - 1
			end

			TableMove(Results, 1, ResultCount, A, Stack)

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		const Results = TablePack(Stack[A](Stack[A1]))
		local ResultCount = Results.n

		if C == 0 then
			Stack[5] = A + ResultCount - 1
		else
			ResultCount = C - 1
		end

		TableMove(Results, 1, ResultCount, A, Stack)

		return NextFn
	end, Link
end

const function MakeCall2x0(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, A1: number, A2: number, A3: number, A4: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A](Stack[A1], Stack[A2])

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A](Stack[A1], Stack[A2])

		return NextFn
	end, Link
end

const function MakeCall2x1(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, A1: number, A2: number, A3: number, A4: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A] = Stack[A](Stack[A1], Stack[A2])

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A] = Stack[A](Stack[A1], Stack[A2])

		return NextFn
	end, Link
end

const function MakeCall2x2(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, A1: number, A2: number, A3: number, A4: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A], Stack[A1] = Stack[A](Stack[A1], Stack[A2])

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A], Stack[A1] = Stack[A](Stack[A1], Stack[A2])

		return NextFn
	end, Link
end

const function MakeCall2x3(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, A1: number, A2: number, A3: number, A4: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A], Stack[A1], Stack[A2] = Stack[A](Stack[A1], Stack[A2])

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A], Stack[A1], Stack[A2] = Stack[A](Stack[A1], Stack[A2])

		return NextFn
	end, Link
end

const function MakeCall2(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, A1: number, A2: number, A3: number, A4: number, C: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			const Results = TablePack(Stack[A](Stack[A1], Stack[A2]))
			local ResultCount = Results.n

			if C == 0 then
				Stack[5] = A + ResultCount - 1
			else
				ResultCount = C - 1
			end

			TableMove(Results, 1, ResultCount, A, Stack)

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		const Results = TablePack(Stack[A](Stack[A1], Stack[A2]))
		local ResultCount = Results.n

		if C == 0 then
			Stack[5] = A + ResultCount - 1
		else
			ResultCount = C - 1
		end

		TableMove(Results, 1, ResultCount, A, Stack)

		return NextFn
	end, Link
end

const function MakeCall3x0(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, A1: number, A2: number, A3: number, A4: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A](Stack[A1], Stack[A2], Stack[A3])

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A](Stack[A1], Stack[A2], Stack[A3])

		return NextFn
	end, Link
end

const function MakeCall3x1(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, A1: number, A2: number, A3: number, A4: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A] = Stack[A](Stack[A1], Stack[A2], Stack[A3])

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A] = Stack[A](Stack[A1], Stack[A2], Stack[A3])

		return NextFn
	end, Link
end

const function MakeCall3x2(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, A1: number, A2: number, A3: number, A4: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A], Stack[A1] = Stack[A](Stack[A1], Stack[A2], Stack[A3])

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A], Stack[A1] = Stack[A](Stack[A1], Stack[A2], Stack[A3])

		return NextFn
	end, Link
end

const function MakeCall3x3(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, A1: number, A2: number, A3: number, A4: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A], Stack[A1], Stack[A2] = Stack[A](Stack[A1], Stack[A2], Stack[A3])

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A], Stack[A1], Stack[A2] = Stack[A](Stack[A1], Stack[A2], Stack[A3])

		return NextFn
	end, Link
end

const function MakeCall3(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, A1: number, A2: number, A3: number, A4: number, C: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			const Results = TablePack(Stack[A](Stack[A1], Stack[A2], Stack[A3]))
			local ResultCount = Results.n

			if C == 0 then
				Stack[5] = A + ResultCount - 1
			else
				ResultCount = C - 1
			end

			TableMove(Results, 1, ResultCount, A, Stack)

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		const Results = TablePack(Stack[A](Stack[A1], Stack[A2], Stack[A3]))
		local ResultCount = Results.n

		if C == 0 then
			Stack[5] = A + ResultCount - 1
		else
			ResultCount = C - 1
		end

		TableMove(Results, 1, ResultCount, A, Stack)

		return NextFn
	end, Link
end

const function MakeCall4x0(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, A1: number, A2: number, A3: number, A4: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A](Stack[A1], Stack[A2], Stack[A3], Stack[A4])

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A](Stack[A1], Stack[A2], Stack[A3], Stack[A4])

		return NextFn
	end, Link
end

const function MakeCall4x1(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, A1: number, A2: number, A3: number, A4: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A] = Stack[A](Stack[A1], Stack[A2], Stack[A3], Stack[A4])

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A] = Stack[A](Stack[A1], Stack[A2], Stack[A3], Stack[A4])

		return NextFn
	end, Link
end

const function MakeCall4x2(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, A1: number, A2: number, A3: number, A4: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A], Stack[A1] = Stack[A](Stack[A1], Stack[A2], Stack[A3], Stack[A4])

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A], Stack[A1] = Stack[A](Stack[A1], Stack[A2], Stack[A3], Stack[A4])

		return NextFn
	end, Link
end

const function MakeCall4x3(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, A1: number, A2: number, A3: number, A4: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			Stack[A], Stack[A1], Stack[A2] = Stack[A](Stack[A1], Stack[A2], Stack[A3], Stack[A4])

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		Stack[A], Stack[A1], Stack[A2] = Stack[A](Stack[A1], Stack[A2], Stack[A3], Stack[A4])

		return NextFn
	end, Link
end

const function MakeCall4(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, A1: number, A2: number, A3: number, A4: number, C: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			const Results = TablePack(Stack[A](Stack[A1], Stack[A2], Stack[A3], Stack[A4]))
			local ResultCount = Results.n

			if C == 0 then
				Stack[5] = A + ResultCount - 1
			else
				ResultCount = C - 1
			end

			TableMove(Results, 1, ResultCount, A, Stack)

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		const Results = TablePack(Stack[A](Stack[A1], Stack[A2], Stack[A3], Stack[A4]))
		local ResultCount = Results.n

		if C == 0 then
			Stack[5] = A + ResultCount - 1
		else
			ResultCount = C - 1
		end

		TableMove(Results, 1, ResultCount, A, Stack)

		return NextFn
	end, Link
end

const function MakeCallN(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, B: number, C: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			const Params = if B == 0 then Stack[5] - A else B - 1
			const Results = TablePack(Stack[A](TableUnpack(Stack, A + 1, A + Params)))
			local ResultCount = Results.n

			if C == 0 then
				Stack[5] = A + ResultCount - 1
			else
				ResultCount = C - 1
			end

			TableMove(Results, 1, ResultCount, A, Stack)

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		const Params = if B == 0 then Stack[5] - A else B - 1
		const Results = TablePack(Stack[A](TableUnpack(Stack, A + 1, A + Params)))
		local ResultCount = Results.n

		if C == 0 then
			Stack[5] = A + ResultCount - 1
		else
			ResultCount = C - 1
		end

		TableMove(Results, 1, ResultCount, A, Stack)

		return NextFn
	end, Link
end

const function MakeReturn0(): (Handler, Linker)
	return function(Stack: Registers): Handler?
		Stack[3] = 0

		return nil
	end, Unlinked
end

const function MakeReturn1(A: number): (Handler, Linker)
	return function(Stack: Registers): Handler?
		Stack[1] = Stack[A]
		Stack[3] = 1

		return nil
	end, Unlinked
end

const function MakeReturn2(A: number, A1: number): (Handler, Linker)
	return function(Stack: Registers): Handler?
		Stack[1] = Stack[A]
		Stack[2] = Stack[A1]
		Stack[3] = 2

		return nil
	end, Unlinked
end

const function MakeReturnRange(A: number, B: number): (Handler, Linker)
	return function(Stack: Registers): Handler?
		Stack[2] = if B == 0 then Stack[5] else A + B - 2
		Stack[1] = A
		Stack[3] = 3

		return nil
	end, Unlinked
end

const function MakeUnsupported(Opcode: number): (Handler, Linker)
	return function(Stack: Registers): Handler?
		Error(`Unsupported Opcode: {Opcode}`)

		return nil
	end, Unlinked
end

const function MakeJumpIf(Mode: number, OnNext: Handler, OnTarget: Handler, A: number): (Handler, Linker)
	if Mode == 3 then
		return function(Stack: Registers): Handler?
			return if Stack[A] then OnTarget(Stack) else OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext
	local TargetFn = OnTarget

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
		TargetFn = LinkedTarget
	end

	if Mode == 2 then
		return function(Stack: Registers): Handler?
			return if Stack[A] then OnTarget(Stack) else NextFn
		end, Link
	elseif Mode == 1 then
		return function(Stack: Registers): Handler?
			return if Stack[A] then TargetFn else OnNext(Stack)
		end, Link
	end

	return function(Stack: Registers): Handler?
		return if Stack[A] then TargetFn else NextFn
	end, Link
end

const function MakeJumpIfNot(Mode: number, OnNext: Handler, OnTarget: Handler, A: number): (Handler, Linker)
	if Mode == 3 then
		return function(Stack: Registers): Handler?
			return if Stack[A] then OnNext(Stack) else OnTarget(Stack)
		end, Unlinked
	end

	local NextFn = OnNext
	local TargetFn = OnTarget

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
		TargetFn = LinkedTarget
	end

	if Mode == 2 then
		return function(Stack: Registers): Handler?
			return if Stack[A] then NextFn else OnTarget(Stack)
		end, Link
	elseif Mode == 1 then
		return function(Stack: Registers): Handler?
			return if Stack[A] then OnNext(Stack) else TargetFn
		end, Link
	end

	return function(Stack: Registers): Handler?
		return if Stack[A] then NextFn else TargetFn
	end, Link
end

const function MakeJumpIfEq(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, C: number): (Handler, Linker)
	if Mode == 3 then
		return function(Stack: Registers): Handler?
			return if Stack[A] == Stack[C] then OnTarget(Stack) else OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext
	local TargetFn = OnTarget

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
		TargetFn = LinkedTarget
	end

	if Mode == 2 then
		return function(Stack: Registers): Handler?
			return if Stack[A] == Stack[C] then OnTarget(Stack) else NextFn
		end, Link
	elseif Mode == 1 then
		return function(Stack: Registers): Handler?
			return if Stack[A] == Stack[C] then TargetFn else OnNext(Stack)
		end, Link
	end

	return function(Stack: Registers): Handler?
		return if Stack[A] == Stack[C] then TargetFn else NextFn
	end, Link
end

const function MakeJumpIfLe(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, C: number): (Handler, Linker)
	if Mode == 3 then
		return function(Stack: Registers): Handler?
			return if Stack[A] <= Stack[C] then OnTarget(Stack) else OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext
	local TargetFn = OnTarget

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
		TargetFn = LinkedTarget
	end

	if Mode == 2 then
		return function(Stack: Registers): Handler?
			return if Stack[A] <= Stack[C] then OnTarget(Stack) else NextFn
		end, Link
	elseif Mode == 1 then
		return function(Stack: Registers): Handler?
			return if Stack[A] <= Stack[C] then TargetFn else OnNext(Stack)
		end, Link
	end

	return function(Stack: Registers): Handler?
		return if Stack[A] <= Stack[C] then TargetFn else NextFn
	end, Link
end

const function MakeJumpIfLt(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, C: number): (Handler, Linker)
	if Mode == 3 then
		return function(Stack: Registers): Handler?
			return if Stack[A] < Stack[C] then OnTarget(Stack) else OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext
	local TargetFn = OnTarget

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
		TargetFn = LinkedTarget
	end

	if Mode == 2 then
		return function(Stack: Registers): Handler?
			return if Stack[A] < Stack[C] then OnTarget(Stack) else NextFn
		end, Link
	elseif Mode == 1 then
		return function(Stack: Registers): Handler?
			return if Stack[A] < Stack[C] then TargetFn else OnNext(Stack)
		end, Link
	end

	return function(Stack: Registers): Handler?
		return if Stack[A] < Stack[C] then TargetFn else NextFn
	end, Link
end

const function MakeJumpIfNotEq(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, C: number): (Handler, Linker)
	if Mode == 3 then
		return function(Stack: Registers): Handler?
			return if Stack[A] ~= Stack[C] then OnTarget(Stack) else OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext
	local TargetFn = OnTarget

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
		TargetFn = LinkedTarget
	end

	if Mode == 2 then
		return function(Stack: Registers): Handler?
			return if Stack[A] ~= Stack[C] then OnTarget(Stack) else NextFn
		end, Link
	elseif Mode == 1 then
		return function(Stack: Registers): Handler?
			return if Stack[A] ~= Stack[C] then TargetFn else OnNext(Stack)
		end, Link
	end

	return function(Stack: Registers): Handler?
		return if Stack[A] ~= Stack[C] then TargetFn else NextFn
	end, Link
end

const function MakeJumpIfNotLe(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, C: number): (Handler, Linker)
	if Mode == 3 then
		return function(Stack: Registers): Handler?
			return if Stack[A] <= Stack[C] then OnNext(Stack) else OnTarget(Stack)
		end, Unlinked
	end

	local NextFn = OnNext
	local TargetFn = OnTarget

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
		TargetFn = LinkedTarget
	end

	if Mode == 2 then
		return function(Stack: Registers): Handler?
			return if Stack[A] <= Stack[C] then NextFn else OnTarget(Stack)
		end, Link
	elseif Mode == 1 then
		return function(Stack: Registers): Handler?
			return if Stack[A] <= Stack[C] then OnNext(Stack) else TargetFn
		end, Link
	end

	return function(Stack: Registers): Handler?
		return if Stack[A] <= Stack[C] then NextFn else TargetFn
	end, Link
end

const function MakeJumpIfNotLt(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, C: number): (Handler, Linker)
	if Mode == 3 then
		return function(Stack: Registers): Handler?
			return if Stack[A] < Stack[C] then OnNext(Stack) else OnTarget(Stack)
		end, Unlinked
	end

	local NextFn = OnNext
	local TargetFn = OnTarget

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
		TargetFn = LinkedTarget
	end

	if Mode == 2 then
		return function(Stack: Registers): Handler?
			return if Stack[A] < Stack[C] then NextFn else OnTarget(Stack)
		end, Link
	elseif Mode == 1 then
		return function(Stack: Registers): Handler?
			return if Stack[A] < Stack[C] then OnNext(Stack) else TargetFn
		end, Link
	end

	return function(Stack: Registers): Handler?
		return if Stack[A] < Stack[C] then NextFn else TargetFn
	end, Link
end

const function MakeJumpIfK(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, K: any): (Handler, Linker)
	if Mode == 3 then
		return function(Stack: Registers): Handler?
			return if Stack[A] == K then OnTarget(Stack) else OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext
	local TargetFn = OnTarget

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
		TargetFn = LinkedTarget
	end

	if Mode == 2 then
		return function(Stack: Registers): Handler?
			return if Stack[A] == K then OnTarget(Stack) else NextFn
		end, Link
	elseif Mode == 1 then
		return function(Stack: Registers): Handler?
			return if Stack[A] == K then TargetFn else OnNext(Stack)
		end, Link
	end

	return function(Stack: Registers): Handler?
		return if Stack[A] == K then TargetFn else NextFn
	end, Link
end

const function MakeJumpIfNotK(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, K: any): (Handler, Linker)
	if Mode == 3 then
		return function(Stack: Registers): Handler?
			return if Stack[A] == K then OnNext(Stack) else OnTarget(Stack)
		end, Unlinked
	end

	local NextFn = OnNext
	local TargetFn = OnTarget

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
		TargetFn = LinkedTarget
	end

	if Mode == 2 then
		return function(Stack: Registers): Handler?
			return if Stack[A] == K then NextFn else OnTarget(Stack)
		end, Link
	elseif Mode == 1 then
		return function(Stack: Registers): Handler?
			return if Stack[A] == K then OnNext(Stack) else TargetFn
		end, Link
	end

	return function(Stack: Registers): Handler?
		return if Stack[A] == K then NextFn else TargetFn
	end, Link
end

const function MakeJumpIfNil(Mode: number, OnNext: Handler, OnTarget: Handler, A: number): (Handler, Linker)
	if Mode == 3 then
		return function(Stack: Registers): Handler?
			return if Stack[A] == nil then OnTarget(Stack) else OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext
	local TargetFn = OnTarget

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
		TargetFn = LinkedTarget
	end

	if Mode == 2 then
		return function(Stack: Registers): Handler?
			return if Stack[A] == nil then OnTarget(Stack) else NextFn
		end, Link
	elseif Mode == 1 then
		return function(Stack: Registers): Handler?
			return if Stack[A] == nil then TargetFn else OnNext(Stack)
		end, Link
	end

	return function(Stack: Registers): Handler?
		return if Stack[A] == nil then TargetFn else NextFn
	end, Link
end

const function MakeJumpIfNotNil(Mode: number, OnNext: Handler, OnTarget: Handler, A: number): (Handler, Linker)
	if Mode == 3 then
		return function(Stack: Registers): Handler?
			return if Stack[A] == nil then OnNext(Stack) else OnTarget(Stack)
		end, Unlinked
	end

	local NextFn = OnNext
	local TargetFn = OnTarget

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
		TargetFn = LinkedTarget
	end

	if Mode == 2 then
		return function(Stack: Registers): Handler?
			return if Stack[A] == nil then NextFn else OnTarget(Stack)
		end, Link
	elseif Mode == 1 then
		return function(Stack: Registers): Handler?
			return if Stack[A] == nil then OnNext(Stack) else TargetFn
		end, Link
	end

	return function(Stack: Registers): Handler?
		return if Stack[A] == nil then NextFn else TargetFn
	end, Link
end

const function MakeForNPrep(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, A1: number, A2: number): (Handler, Linker)
	if Mode == 3 then
		return function(Stack: Registers): Handler?
			local Limit = Stack[A]
			local Step = Stack[A1]
			local Index = Stack[A2]

			if Type(Index) ~= "number" then
				Index = Tonumber(Index)

				if Index == nil then
					Error(`invalid 'for' initial value (number expected, got {Type(Stack[A2])})`)
				end

				Stack[A2] = Index
			end

			if Type(Limit) ~= "number" then
				Limit = Tonumber(Limit)

				if Limit == nil then
					Error(`invalid 'for' limit (number expected, got {Type(Stack[A])})`)
				end

				Stack[A] = Limit
			end

			if Type(Step) ~= "number" then
				Step = Tonumber(Step)

				if Step == nil then
					Error(`invalid 'for' step (number expected, got {Type(Stack[A1])})`)
				end

				Stack[A1] = Step
			end

			return if (if Step > 0 then Index <= Limit else Limit <= Index) then OnNext(Stack) else OnTarget(Stack)
		end, Unlinked
	end

	local NextFn = OnNext
	local TargetFn = OnTarget

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
		TargetFn = LinkedTarget
	end

	if Mode == 2 then
		return function(Stack: Registers): Handler?
			local Limit = Stack[A]
			local Step = Stack[A1]
			local Index = Stack[A2]

			if Type(Index) ~= "number" then
				Index = Tonumber(Index)

				if Index == nil then
					Error(`invalid 'for' initial value (number expected, got {Type(Stack[A2])})`)
				end

				Stack[A2] = Index
			end

			if Type(Limit) ~= "number" then
				Limit = Tonumber(Limit)

				if Limit == nil then
					Error(`invalid 'for' limit (number expected, got {Type(Stack[A])})`)
				end

				Stack[A] = Limit
			end

			if Type(Step) ~= "number" then
				Step = Tonumber(Step)

				if Step == nil then
					Error(`invalid 'for' step (number expected, got {Type(Stack[A1])})`)
				end

				Stack[A1] = Step
			end

			return if (if Step > 0 then Index <= Limit else Limit <= Index) then NextFn else OnTarget(Stack)
		end, Link
	elseif Mode == 1 then
		return function(Stack: Registers): Handler?
			local Limit = Stack[A]
			local Step = Stack[A1]
			local Index = Stack[A2]

			if Type(Index) ~= "number" then
				Index = Tonumber(Index)

				if Index == nil then
					Error(`invalid 'for' initial value (number expected, got {Type(Stack[A2])})`)
				end

				Stack[A2] = Index
			end

			if Type(Limit) ~= "number" then
				Limit = Tonumber(Limit)

				if Limit == nil then
					Error(`invalid 'for' limit (number expected, got {Type(Stack[A])})`)
				end

				Stack[A] = Limit
			end

			if Type(Step) ~= "number" then
				Step = Tonumber(Step)

				if Step == nil then
					Error(`invalid 'for' step (number expected, got {Type(Stack[A1])})`)
				end

				Stack[A1] = Step
			end

			return if (if Step > 0 then Index <= Limit else Limit <= Index) then OnNext(Stack) else TargetFn
		end, Link
	end

	return function(Stack: Registers): Handler?
		local Limit = Stack[A]
		local Step = Stack[A1]
		local Index = Stack[A2]

		if Type(Index) ~= "number" then
			Index = Tonumber(Index)

			if Index == nil then
				Error(`invalid 'for' initial value (number expected, got {Type(Stack[A2])})`)
			end

			Stack[A2] = Index
		end

		if Type(Limit) ~= "number" then
			Limit = Tonumber(Limit)

			if Limit == nil then
				Error(`invalid 'for' limit (number expected, got {Type(Stack[A])})`)
			end

			Stack[A] = Limit
		end

		if Type(Step) ~= "number" then
			Step = Tonumber(Step)

			if Step == nil then
				Error(`invalid 'for' step (number expected, got {Type(Stack[A1])})`)
			end

			Stack[A1] = Step
		end

		return if (if Step > 0 then Index <= Limit else Limit <= Index) then NextFn else TargetFn
	end, Link
end

const function MakeForNLoop(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, A1: number, A2: number): (Handler, Linker)
	local NextFn = OnNext
	local TargetFn = OnTarget

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
		TargetFn = LinkedTarget
	end

	if Mode == 1 then
		return function(Stack: Registers): Handler?
			const Step = Stack[A1]
			const Index = Stack[A2] + Step

			Stack[A2] = Index

			return if (if Step > 0 then Index <= Stack[A] else Stack[A] <= Index) then TargetFn else OnNext(Stack)
		end, Link
	end

	return function(Stack: Registers): Handler?
		const Step = Stack[A1]
		const Index = Stack[A2] + Step

		Stack[A2] = Index

		return if (if Step > 0 then Index <= Stack[A] else Stack[A] <= Index) then TargetFn else NextFn
	end, Link
end

const function MakeForNLoopStepOne(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, A2: number): (Handler, Linker)
	local NextFn = OnNext
	local TargetFn = OnTarget

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
		TargetFn = LinkedTarget
	end

	if Mode == 1 then
		return function(Stack: Registers): Handler?
			const Index = Stack[A2] + 1

			Stack[A2] = Index

			return if Index <= Stack[A] then TargetFn else OnNext(Stack)
		end, Link
	end

	return function(Stack: Registers): Handler?
		const Index = Stack[A2] + 1

		Stack[A2] = Index

		return if Index <= Stack[A] then TargetFn else NextFn
	end, Link
end

const function MakeForNLoopStepOneLimit(Mode: number, OnNext: Handler, OnTarget: Handler, A2: number, Limit: number): (Handler, Linker)
	local NextFn = OnNext
	local TargetFn = OnTarget

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
		TargetFn = LinkedTarget
	end

	if Mode == 1 then
		return function(Stack: Registers): Handler?
			const Index = Stack[A2] + 1

			Stack[A2] = Index

			return if Index <= Limit then TargetFn else OnNext(Stack)
		end, Link
	end

	return function(Stack: Registers): Handler?
		const Index = Stack[A2] + 1

		Stack[A2] = Index

		return if Index <= Limit then TargetFn else NextFn
	end, Link
end

const function MakeForGPrep(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, A1: number, A2: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			const Iterator = Stack[A]
			const Kind = Type(Iterator)

			if Kind == "function" then
				return OnNext(Stack)
			end

			if Kind == "table" or Kind == "userdata" then
				const Meta = Getmetatable(Iterator) :: any
				const IterFunction = if Type(Meta) == "table" then Rawget(Meta, "__iter") else nil

				if IterFunction ~= nil then
					const Generator, State, Control = (IterFunction :: (any) -> (any, any, any))(Iterator)

					if Generator == nil then
						Error("attempt to call a nil value")
					end

					Stack[A] = Generator
					Stack[A1] = State
					Stack[A2] = Control
				elseif Type(Meta) ~= "table" or Rawget(Meta, "__call") == nil then
					if Kind == "userdata" then
						Error(`attempt to iterate over a {Typeof(Iterator)} value`)
					end

					Stack[A] = Next
					Stack[A1] = Iterator
					Stack[A2] = nil
				end
			else
				Error(`attempt to iterate over a {Typeof(Iterator)} value`)
			end

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		const Iterator = Stack[A]
		const Kind = Type(Iterator)

		if Kind == "function" then
			return NextFn
		end

		if Kind == "table" or Kind == "userdata" then
			const Meta = Getmetatable(Iterator) :: any
			const IterFunction = if Type(Meta) == "table" then Rawget(Meta, "__iter") else nil

			if IterFunction ~= nil then
				const Generator, State, Control = (IterFunction :: (any) -> (any, any, any))(Iterator)

				if Generator == nil then
					Error("attempt to call a nil value")
				end

				Stack[A] = Generator
				Stack[A1] = State
				Stack[A2] = Control
			elseif Type(Meta) ~= "table" or Rawget(Meta, "__call") == nil then
				if Kind == "userdata" then
					Error(`attempt to iterate over a {Typeof(Iterator)} value`)
				end

				Stack[A] = Next
				Stack[A1] = Iterator
				Stack[A2] = nil
			end
		else
			Error(`attempt to iterate over a {Typeof(Iterator)} value`)
		end

		return NextFn
	end, Link
end

const function MakeForGPrepNext(Mode: number, OnNext: Handler, OnTarget: Handler, A: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			const Iterator = Stack[A]

			if Type(Iterator) ~= "function" then
				Error(`attempt to iterate over a {Type(Iterator)} value`)
			end

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		const Iterator = Stack[A]

		if Type(Iterator) ~= "function" then
			Error(`attempt to iterate over a {Type(Iterator)} value`)
		end

		return NextFn
	end, Link
end

const function MakeForGPrepInext(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, A1: number, A2: number): (Handler, Linker)
	if Mode == 1 then
		return function(Stack: Registers): Handler?
			const Iterator = Stack[A]

			-- like the reference VM's ipairs fast path, a verified ipairs loop over a table is marked for inline stepping
			if Iterator == Inext and Type(Stack[A1]) == "table" and Getmetatable(Stack[A1]) == nil and Stack[A2] == 0 then
				Stack[A] = IpairsStep
			elseif Type(Iterator) ~= "function" then
				Error(`attempt to iterate over a {Type(Iterator)} value`)
			end

			return OnNext(Stack)
		end, Unlinked
	end

	local NextFn = OnNext

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
	end

	return function(Stack: Registers): Handler?
		const Iterator = Stack[A]

		-- like the reference VM's ipairs fast path, a verified ipairs loop over a table is marked for inline stepping
		if Iterator == Inext and Type(Stack[A1]) == "table" and Getmetatable(Stack[A1]) == nil and Stack[A2] == 0 then
			Stack[A] = IpairsStep
		elseif Type(Iterator) ~= "function" then
			Error(`attempt to iterate over a {Type(Iterator)} value`)
		end

		return NextFn
	end, Link
end

const function MakeForGLoop1(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, A1: number, A2: number, A3: number): (Handler, Linker)
	local NextFn = OnNext
	local TargetFn = OnTarget

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
		TargetFn = LinkedTarget
	end

	if Mode == 1 then
		return function(Stack: Registers): Handler?
			const Value = Stack[A](Stack[A1], Stack[A2])

			if Value ~= nil then
				Stack[A2] = Value
				Stack[A3] = Value

				return TargetFn
			end

			return OnNext(Stack)
		end, Link
	end

	return function(Stack: Registers): Handler?
		const Value = Stack[A](Stack[A1], Stack[A2])

		if Value ~= nil then
			Stack[A2] = Value
			Stack[A3] = Value

			return TargetFn
		end

		return NextFn
	end, Link
end

const function MakeForGLoop2(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, A1: number, A2: number, A3: number, A4: number): (Handler, Linker)
	local NextFn = OnNext
	local TargetFn = OnTarget

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
		TargetFn = LinkedTarget
	end

	if Mode == 1 then
		return function(Stack: Registers): Handler?
			const Key, Value = Stack[A](Stack[A1], Stack[A2])

			if Key ~= nil then
				Stack[A2] = Key
				Stack[A3] = Key
				Stack[A4] = Value

				return TargetFn
			end

			return OnNext(Stack)
		end, Link
	end

	return function(Stack: Registers): Handler?
		const Key, Value = Stack[A](Stack[A1], Stack[A2])

		if Key ~= nil then
			Stack[A2] = Key
			Stack[A3] = Key
			Stack[A4] = Value

			return TargetFn
		end

		return NextFn
	end, Link
end

const function MakeForGLoopIpairs(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, A1: number, A2: number, A3: number, A4: number): (Handler, Linker)
	local NextFn = OnNext
	local TargetFn = OnTarget

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
		TargetFn = LinkedTarget
	end

	if Mode == 1 then
		return function(Stack: Registers): Handler?
			const Iterator = Stack[A]

			if Iterator == IpairsStep then
				const Index = Stack[A2] + 1
				-- plain indexing equals inext's raw read on a table that had no metatable when the loop started
				const Value = Stack[A1][Index]

				if Value ~= nil then
					Stack[A2] = Index
					Stack[A3] = Index
					Stack[A4] = Value

					return TargetFn
				end

				return OnNext(Stack)
			end

			const Key, Value = Iterator(Stack[A1], Stack[A2])

			if Key ~= nil then
				Stack[A2] = Key
				Stack[A3] = Key
				Stack[A4] = Value

				return TargetFn
			end

			return OnNext(Stack)
		end, Link
	end

	return function(Stack: Registers): Handler?
		const Iterator = Stack[A]

		if Iterator == IpairsStep then
			const Index = Stack[A2] + 1
			-- plain indexing equals inext's raw read on a table that had no metatable when the loop started
			const Value = Stack[A1][Index]

			if Value ~= nil then
				Stack[A2] = Index
				Stack[A3] = Index
				Stack[A4] = Value

				return TargetFn
			end

			return NextFn
		end

		const Key, Value = Iterator(Stack[A1], Stack[A2])

		if Key ~= nil then
			Stack[A2] = Key
			Stack[A3] = Key
			Stack[A4] = Value

			return TargetFn
		end

		return NextFn
	end, Link
end

const function MakeForGLoopN(Mode: number, OnNext: Handler, OnTarget: Handler, A: number, A1: number, A2: number, A3: number, Count: number): (Handler, Linker)
	local NextFn = OnNext
	local TargetFn = OnTarget

	const function Link(LinkedNext: Handler, LinkedTarget: Handler)
		NextFn = LinkedNext
		TargetFn = LinkedTarget
	end

	if Mode == 1 then
		return function(Stack: Registers): Handler?
			const Values = TablePack(Stack[A](Stack[A1], Stack[A2]))

			TableMove(Values, 1, Count, A3, Stack)

			if Stack[A3] ~= nil then
				Stack[A2] = Stack[A3]

				return TargetFn
			end

			return OnNext(Stack)
		end, Link
	end

	return function(Stack: Registers): Handler?
		const Values = TablePack(Stack[A](Stack[A1], Stack[A2]))

		TableMove(Values, 1, Count, A3, Stack)

		if Stack[A3] ~= nil then
			Stack[A2] = Stack[A3]

			return TargetFn
		end

		return NextFn
	end, Link
end

const function Deserialize(Bytecode: string | buffer, Config: Settings): ({ Raw }, number)
	const Stream = if Type(Bytecode) == "string" then BufferFromString(Bytecode :: any) else Bytecode :: buffer
	local Cursor = 0

	const function ReadByte(): number
		const Byte = BufferReadU8(Stream, Cursor)

		Cursor += 1

		return Byte
	end

	const function ReadWord(): number
		const Word = BufferReadU32(Stream, Cursor)

		Cursor += 4

		return Word
	end

	const function ReadFloat(): number
		const Float = BufferReadF32(Stream, Cursor)

		Cursor += 4

		return Float
	end

	const function ReadDouble(): number
		const Double = BufferReadF64(Stream, Cursor)

		Cursor += 8

		return Double
	end

	const function ReadVarInt(): number
		local Result = 0

		for Index = 0, 4 do
			const Value = ReadByte()

			Result = Bit32BOr(Result, Bit32LShift(Bit32BAnd(Value, 0x7F), Index * 7))

			if not Bit32BTest(Value, 0x80) then
				break
			end
		end

		return Result
	end

	const function ReadVarInt64(): (number, number)
		const Bytes: { number } = {}

		for Index = 1, 10 do
			const Value = ReadByte()

			Bytes[Index] = Bit32BAnd(Value, 0x7F)

			if Value < 0x80 then
				break
			end
		end

		local High = 0
		local Low = 0

		for Index = #Bytes, 1, -1 do
			const Value = Low * 128 + Bytes[Index]

			Low = Value % 0x100000000
			High = High * 128 + Value // 0x100000000
		end

		return High, Low
	end

	const LuauVersion = ReadByte()
	local TypesVersion = 0

	if LuauVersion == 0 then
		Error(BufferReadString(Stream, 1, BufferLen(Stream) - 1), 0)
	elseif LuauVersion == 100 then
		Error("bytecode version 100 is unsupported", 0)
	elseif LuauVersion < 3 or LuauVersion > 14 then
		Error("the version of the provided bytecode is unsupported", 0)
	elseif LuauVersion >= 4 then
		TypesVersion = ReadByte()
	end

	const StringCount = ReadVarInt()
	const StringList: { string } = {}

	for Index = 1, StringCount do
		const Size = ReadVarInt()

		StringList[Index] = BufferReadString(Stream, Cursor, Size)
		Cursor += Size
	end

	if TypesVersion == 3 then
		local Index = ReadByte()

		while Index ~= 0 do
			ReadVarInt()

			Index = ReadByte()
		end
	end

	const function ReadProto(): Raw
		local ProtoSize = 0

		if LuauVersion >= 12 then
			ProtoSize = ReadVarInt()
		end

		const ProtoStart = Cursor
		const MaxStackSize = ReadByte()
		const ParamCount = ReadByte()
		const UpvalueCount = ReadByte()
		const IsVararg = ReadByte() ~= 0
		local Flags = 0

		if LuauVersion >= 4 then
			Flags = ReadByte()

			const TypeSize = ReadVarInt()

			Cursor += TypeSize
		end

		const CodeSize = ReadVarInt()
		const Words: { number } = {}

		for Index = 1, CodeSize do
			Words[Index] = ReadWord()
		end

		const ConstantCount = ReadVarInt()
		const Constants: { any } = TableCreate(ConstantCount)
		const ConstantKinds: { number } = {}

		for Index = 1, ConstantCount do
			const Kind = ReadByte()
			local Constant: any

			ConstantKinds[Index] = Kind

			if Kind == 0 then -- Nil
				Constant = nil
			elseif Kind == 1 then -- Bool
				Constant = ReadByte() ~= 0
			elseif Kind == 2 then -- Number
				Constant = ReadDouble()
			elseif Kind == 3 then -- String
				Constant = StringList[ReadVarInt()]
			elseif Kind == 4 then -- Import
				Constant = ReadWord()
			elseif Kind == 5 then -- Table
				const Keys: { number } = {}

				for KeyIndex = 1, ReadVarInt() do
					Keys[KeyIndex] = ReadVarInt()
				end

				Constant = Keys
			elseif Kind == 6 then -- Closure
				Constant = ReadVarInt()
			elseif Kind == 7 then -- Vector
				const X = ReadFloat()
				const Y = ReadFloat()
				const Z = ReadFloat()
				const W = ReadFloat()

				Constant = if Config.VectorSize == 4 then Config.VectorCtor(X, Y, Z, W) else Config.VectorCtor(X, Y, Z)
			elseif Kind == 8 then -- Table with pre-filled constants
				const Pairs: { number } = {}

				for _ = 1, ReadVarInt() do
					const Key = ReadVarInt()
					const Value = ReadWord()

					table.insert(Pairs, Key)
					table.insert(Pairs, if Value < 0x80000000 then Value else Value - 0x100000000)
				end

				Constant = Pairs
			elseif Kind == 9 then -- 64-bit integer
				const Negative = ReadByte() ~= 0
				const High, Low = ReadVarInt64()
				const Digits = StringFormat("%08x%08x", High, Low)

				const FromString = IntegerFromString

				if FromString == nil then
					Error("64-bit integer constants need the integer library, which this environment does not have", 0)
				else
					Constant = FromString(if Negative then `-{Digits}` else Digits, 16)
				end
			elseif Kind == 10 then -- Class shape
				ReadVarInt()

				const MemberCount = ReadVarInt() + ReadVarInt()

				for _ = 1, MemberCount do
					ReadVarInt()
				end
			elseif Kind == 11 then -- Double-precision vector
				const X = ReadDouble()
				const Y = ReadDouble()
				const Z = ReadDouble()
				const W = ReadDouble()

				Constant = if Config.VectorSize == 4 then Config.VectorCtor(X, Y, Z, W) else Config.VectorCtor(X, Y, Z)
			else
				Error(`unsupported bytecode constant type: {Kind}`)
			end

			Constants[Index] = Constant
		end

		const ProtoCount = ReadVarInt()
		const Protos: { number } = {}

		for Index = 1, ProtoCount do
			Protos[Index] = ReadVarInt() + 1
		end

		ReadVarInt() -- line defined
		ReadVarInt() -- debug name

		if ReadByte() ~= 0 then -- line info
			const LineGapLog2 = ReadByte()
			const Intervals = Bit32RShift(CodeSize - 1, LineGapLog2) + 1

			Cursor += CodeSize + Intervals * 4
		end

		if ReadByte() ~= 0 then -- debug info
			for _ = 1, ReadVarInt() do
				ReadVarInt()
				ReadVarInt()
				ReadVarInt()
				ReadByte()
			end

			for _ = 1, ReadVarInt() do
				ReadVarInt()
			end
		end

		if LuauVersion >= 11 then
			for _ = 1, ReadVarInt() do
				ReadByte() -- slot type
				ReadVarInt() -- instruction offset
			end
		end

		if LuauVersion >= 12 then
			if Bit32BTest(Flags, 0x8) then
				ReadVarInt64() -- inlining cost
			end

			Cursor = ProtoStart + ProtoSize
		end

		return {
			MaxStackSize = MaxStackSize,
			ParamCount = ParamCount,
			UpvalueCount = UpvalueCount,
			IsVararg = IsVararg,
			Words = Words,
			Constants = Constants,
			ConstantKinds = ConstantKinds,
			Protos = Protos,
		}
	end

	const ProtoCount = ReadVarInt()
	const RawList: { Raw } = {}

	for Index = 1, ProtoCount do
		RawList[Index] = ReadProto()
	end

	const MainIndex = ReadVarInt() + 1

	assert(Cursor == BufferLen(Stream), "deserializer cursor position mismatch")

	return RawList, MainIndex
end

type CallMaker = (Mode: number, OnNext: Handler, OnTarget: Handler, A: number, A1: number, A2: number, A3: number, A4: number) -> (Handler, Linker)

type VariableCallMaker = (Mode: number, OnNext: Handler, OnTarget: Handler, A: number, A1: number, A2: number, A3: number, A4: number, C: number) -> (Handler, Linker)

-- Call handlers for a fixed argument count and 0 to 3 results, indexed by (argument count) * 4 + result count.
const FixedCalls: { [number]: CallMaker } = {
	[0] = MakeCall0x0, MakeCall0x1, MakeCall0x2, MakeCall0x3,
	MakeCall1x0, MakeCall1x1, MakeCall1x2, MakeCall1x3,
	MakeCall2x0, MakeCall2x1, MakeCall2x2, MakeCall2x3,
	MakeCall3x0, MakeCall3x1, MakeCall3x2, MakeCall3x3,
	MakeCall4x0, MakeCall4x1, MakeCall4x2, MakeCall4x3,
}

-- Call handlers for a fixed argument count and any other result count, indexed by argument count.
const VariableCalls: { [number]: VariableCallMaker } = {
	[0] = MakeCall0, MakeCall1, MakeCall2, MakeCall3, MakeCall4,
}

const function Decode(Raw: Raw, Proto: Proto, RawList: { Raw }, ProtoList: { Proto }, Env: Store, BackEdges: { BackEdge })
	const Words = Raw.Words
	const Constants = Raw.Constants
	const WordCount = #Words
	const Ordinal: { number } = {}
	const IsStart: { [number]: boolean } = {}
	const Starts: { number } = {}
	local Kept = 0
	local Word = 1

	while Word <= WordCount do
		const Opcode = Bit32BAnd(Words[Word], 0xFF)
		const Length = if HasAux[Opcode] then 2 else 1

		IsStart[Word] = true

		if Removed[Opcode] then
			Ordinal[Word] = Kept + 1
		else
			Kept += 1
			Ordinal[Word] = Kept
			Starts[Kept] = Word
		end

		if Length == 2 then
			Ordinal[Word + 1] = Kept + 1
		end

		Word += Length
	end

	Ordinal[WordCount + 1] = Kept + 1

	-- successors: Primary is the fallthrough (or the only destination), Secondary the branch target of two-successor opcodes
	const Opcodes: { number } = {}
	const Primary: { number } = {}
	const Secondary: { number } = {}

	for Index = 1, Kept do
		const Start = Starts[Index]
		const Value = Words[Start]
		const Opcode = Bit32BAnd(Value, 0xFF)
		const Operand = Bit32RShift(Value, 16)
		const SignedD = if Operand < 0x8000 then Operand else Operand - 0x10000
		const Jump = Ordinal[Start + 1 + SignedD]

		Opcodes[Index] = Opcode
		Primary[Index] = Index + 1
		Secondary[Index] = 0

		if Opcode == 67 then -- JUMPX
			const Offset = Bit32RShift(Value, 8)

			Primary[Index] = Ordinal[Start + 1 + (if Offset >= 0x800000 then Offset - 0x1000000 else Offset)]
		elseif PureJumps[Opcode] or Opcode == 59 or Opcode == 61 or Opcode == 76 then -- jumps and FORGPREP*
			Primary[Index] = Jump
		elseif Branches[Opcode] then
			Secondary[Index] = Jump
		elseif Opcode == 3 and Bit32RShift(Value, 24) ~= 0 then -- LOADB with skip
			Primary[Index] = Ordinal[Start + 1 + Bit32RShift(Value, 24)]
		elseif Opcode == 22 then -- RETURN
			Primary[Index] = 0
		end
	end

	-- The instruction an edge into Index really reaches once pure jumps are skipped; a cycle of pure jumps keeps one of them.
	const function Resolve(Index: number): number
		local Current = Index

		for _ = 1, Kept do
			if Current < 1 or Current > Kept or not PureJumps[Opcodes[Current]] or Primary[Current] == Current then
				return Current
			end

			Current = Primary[Current]
		end

		return Current
	end

	-- link modes: an edge is chained (bit 1 fallthrough, bit 2 branch) only when it moves forward, its destination may be
	-- entered at any depth, and the chain behind it is shorter than ChainLimit
	const Depth: { number } = TableCreate(Kept + 1, 1)
	const Bounce: { [number]: boolean } = {}
	const Modes: { number } = {}

	for Index = 1, Kept do
		if Bounced[Opcodes[Index]] then
			Bounce[Index] = true
		end
	end

	for Index = 1, Kept do
		const First = Resolve(Primary[Index])
		const Second = if Secondary[Index] ~= 0 then Resolve(Secondary[Index]) else 0
		const Room = Depth[Index] < ChainLimit
		local Mode = 0

		if Opcodes[Index] == 76 then -- FORGPREP: its FORGLOOP comes later, so it is marked before any edge into it is linked
			Bounce[First] = true
		end

		if First > Index and Room and not Bounce[First] then
			Mode += 1
			Depth[First] = MathMax(Depth[First], Depth[Index] + 1)
		end

		if Second > Index and Room and not Bounce[Second] then
			Mode += 2
			Depth[Second] = MathMax(Depth[Second], Depth[Index] + 1)
		end

		Primary[Index] = First
		Secondary[Index] = Second
		Modes[Index] = Mode
	end

	-- The number a LOADN at the given word loads into the given register, when that word really is such an instruction.
	const function LoadedNumber(At: number, Register: number): number?
		if At < 1 or not IsStart[At] then
			return nil
		end

		const Previous = Words[At]

		if Bit32BAnd(Previous, 0xFF) ~= 4 or Bit32BAnd(Bit32RShift(Previous, 8), 0xFF) ~= Register then
			return nil
		end

		const Loaded = Bit32RShift(Previous, 16)

		return if Loaded < 0x8000 then Loaded else Loaded - 0x10000
	end

	const function Describe(Start: number, ChildIndex: number): { any }
		const Description: { any } = { ProtoList[ChildIndex] }

		for Index = 1, RawList[ChildIndex].UpvalueCount do
			const Capture = Words[Start + Index]
			const Kind = Bit32BAnd(Bit32RShift(Capture, 8), 0xFF)
			const Slot = Bit32BAnd(Bit32RShift(Capture, 16), 0xFF)

			Description[Index * 2] = Kind
			Description[Index * 2 + 1] = if Kind == 2 then Slot + 1 else Slot + RegisterBase + 1
		end

		return Description
	end

	-- a numeric loop whose step is the literal 1 (and whose limit may be literal) gets a cheaper loop handler; FORNPREP comes
	-- before its FORNLOOP while handlers are made back to front, so the loop shapes are found in a forward pass first
	const LoopStepOne: { [number]: boolean } = {}
	const LoopLimit: { [number]: number? } = {}
	const StepOneAt: { [number]: boolean } = {}
	const LimitAt: { [number]: number? } = {}

	for Index = 1, Kept do
		const Start = Starts[Index]
		const Register = Bit32BAnd(Bit32RShift(Words[Start], 8), 0xFF)

		if Opcodes[Index] == 56 then -- FORNPREP
			LoopStepOne[Register] = LoadedNumber(Start - 1, Register + 1) == 1
			LoopLimit[Register] = LoadedNumber(Start - 2, Register)
		elseif Opcodes[Index] == 57 then -- FORNLOOP
			StepOneAt[Index] = LoopStepOne[Register] == true
			LimitAt[Index] = LoopLimit[Register]
		end
	end

	-- handlers are made back to front, so every forward successor already exists and is passed to its maker; a chained edge,
	-- which always moves forward, captures it as a constant. Backward edges get Stop for now and are linked afterwards
	const Handlers: { Handler } = {}
	const Links: { Linker } = {}

	for Index = Kept, 1, -1 do
		const First = Primary[Index]
		const Second = Secondary[Index]
		const OnNext = if First > Index then Handlers[First] or Stop else Stop
		const OnTarget = if Second > Index then Handlers[Second] or Stop else Stop
		const Mode = Modes[Index]
		const Start = Starts[Index]
		const Value = Words[Start]
		const Opcode = Opcodes[Index]
		const Aux = if HasAux[Opcode] then Words[Start + 1] else 0
		const A = Bit32BAnd(Bit32RShift(Value, 8), 0xFF) + RegisterBase + 1
		const B = Bit32BAnd(Bit32RShift(Value, 16), 0xFF)
		const C = Bit32RShift(Value, 24)
		const Operand = B + C * 256
		const SignedD = if Operand < 0x8000 then Operand else Operand - 0x10000
		local Made: Handler
		local Link: Linker

		if Opcode == 2 then -- LOADNIL
			Made, Link = MakeLoadNil(Mode, OnNext, OnTarget, A)
		elseif Opcode == 3 then -- LOADB; a skip is its successor
			Made, Link = MakeLoadK(Mode, OnNext, OnTarget, A, B == 1)
		elseif Opcode == 4 then -- LOADN
			Made, Link = MakeLoadK(Mode, OnNext, OnTarget, A, SignedD)
		elseif Opcode == 5 then -- LOADK
			Made, Link = MakeLoadK(Mode, OnNext, OnTarget, A, Constants[SignedD + 1])
		elseif Opcode == 6 then -- MOVE
			Made, Link = MakeMove(Mode, OnNext, OnTarget, A, B + RegisterBase + 1)
		elseif Opcode == 7 then -- GETGLOBAL
			Made, Link = MakeGetGlobal(Mode, OnNext, OnTarget, A, Constants[Aux + 1], Env)
		elseif Opcode == 8 then -- SETGLOBAL
			Made, Link = MakeSetGlobal(Mode, OnNext, OnTarget, A, Constants[Aux + 1], Env)
		elseif Opcode == 9 then -- GETUPVAL
			if Proto.Cells[B + 1] then
				Made, Link = MakeGetUpval(Mode, OnNext, OnTarget, A, B + 1)
			else
				Made, Link = MakeGetUpvalValue(Mode, OnNext, OnTarget, A, B + 1)
			end
		elseif Opcode == 10 then -- SETUPVAL
			Made, Link = MakeSetUpval(Mode, OnNext, OnTarget, A, B + 1)
		elseif Opcode == 11 then -- CLOSEUPVALS
			Made, Link = MakeCloseUpvals(Mode, OnNext, OnTarget, A)
		elseif Opcode == 12 then -- GETIMPORT
			const Count = Bit32RShift(Aux, 30)
			const K0 = Constants[Bit32BAnd(Bit32RShift(Aux, 20), 0x3FF) + 1]
			const K1 = Constants[Bit32BAnd(Bit32RShift(Aux, 10), 0x3FF) + 1]
			const K2 = Constants[Bit32BAnd(Aux, 0x3FF) + 1]
			const Resolved = ResolveImport(Env, Count, K0, K1, K2)

			if Resolved ~= nil then
				Made, Link = MakeLoadK(Mode, OnNext, OnTarget, A, Resolved)
			else
				Made, Link = MakeGetImportSlow(Mode, OnNext, OnTarget, A, { Count, K0, K1, K2 }, Env)
			end
		elseif Opcode == 13 then -- GETTABLE
			Made, Link = MakeGetTable(Mode, OnNext, OnTarget, A, B + RegisterBase + 1, C + RegisterBase + 1)
		elseif Opcode == 14 then -- SETTABLE
			Made, Link = MakeSetTable(Mode, OnNext, OnTarget, A, B + RegisterBase + 1, C + RegisterBase + 1)
		elseif Opcode == 15 or Opcode == 83 then -- GETTABLEKS / GETUDATAKS
			Made, Link = MakeGetTableKS(Mode, OnNext, OnTarget, A, B + RegisterBase + 1, Constants[(if Opcode == 83 then Bit32BAnd(Aux, 0xFFFF) else Aux) + 1])
		elseif Opcode == 16 or Opcode == 84 then -- SETTABLEKS / SETUDATAKS
			Made, Link = MakeSetTableKS(Mode, OnNext, OnTarget, A, B + RegisterBase + 1, Constants[(if Opcode == 84 then Bit32BAnd(Aux, 0xFFFF) else Aux) + 1])
		elseif Opcode == 17 then -- GETTABLEN
			Made, Link = MakeGetTableN(Mode, OnNext, OnTarget, A, B + RegisterBase + 1, C + 1)
		elseif Opcode == 18 then -- SETTABLEN
			Made, Link = MakeSetTableN(Mode, OnNext, OnTarget, A, B + RegisterBase + 1, C + 1)
		elseif Opcode == 19 then -- NEWCLOSURE
			const Description = Describe(Start, Raw.Protos[SignedD + 1])
			const Child: Proto = Description[1]

			if Child.UpvalueCount == 0 then
				Made, Link = MakeNewClosureEmpty(Mode, OnNext, OnTarget, A, Child)
			else
				Made, Link = MakeNewClosure(Mode, OnNext, OnTarget, A, Description)
			end
		elseif Opcode == 20 or Opcode == 85 then -- NAMECALL / NAMECALLUDATA
			Made, Link = MakeNameCall(Mode, OnNext, OnTarget, A, A + 1, B + RegisterBase + 1, Constants[(if Opcode == 85 then Bit32BAnd(Aux, 0xFFFF) else Aux) + 1])
		elseif Opcode == 21 or Opcode == 87 then -- CALL / CALLFB
			if B >= 1 and B <= 5 and C >= 1 and C <= 4 then
				Made, Link = FixedCalls[(B - 1) * 4 + C - 1](Mode, OnNext, OnTarget, A, A + 1, A + 2, A + 3, A + 4)
			elseif B >= 1 and B <= 5 then
				Made, Link = VariableCalls[B - 1](Mode, OnNext, OnTarget, A, A + 1, A + 2, A + 3, A + 4, C)
			else
				Made, Link = MakeCallN(Mode, OnNext, OnTarget, A, B, C)
			end
		elseif Opcode == 22 then -- RETURN
			if B == 1 then
				Made, Link = MakeReturn0()
			elseif B == 2 then
				Made, Link = MakeReturn1(A)
			elseif B == 3 then
				Made, Link = MakeReturn2(A, A + 1)
			else
				Made, Link = MakeReturnRange(A, B)
			end
		elseif PureJumps[Opcode] then -- JUMP / JUMPBACK / JUMPX / CMPPROTO, only reached in a cycle of jumps
			Made, Link = MakeJump(Mode, OnNext, OnTarget)
		elseif Opcode == 25 then -- JUMPIF
			Made, Link = MakeJumpIf(Mode, OnNext, OnTarget, A)
		elseif Opcode == 26 then -- JUMPIFNOT
			Made, Link = MakeJumpIfNot(Mode, OnNext, OnTarget, A)
		elseif Opcode == 27 then -- JUMPIFEQ
			Made, Link = MakeJumpIfEq(Mode, OnNext, OnTarget, A, Aux + RegisterBase + 1)
		elseif Opcode == 28 then -- JUMPIFLE
			Made, Link = MakeJumpIfLe(Mode, OnNext, OnTarget, A, Aux + RegisterBase + 1)
		elseif Opcode == 29 then -- JUMPIFLT
			Made, Link = MakeJumpIfLt(Mode, OnNext, OnTarget, A, Aux + RegisterBase + 1)
		elseif Opcode == 30 then -- JUMPIFNOTEQ
			Made, Link = MakeJumpIfNotEq(Mode, OnNext, OnTarget, A, Aux + RegisterBase + 1)
		elseif Opcode == 31 then -- JUMPIFNOTLE
			Made, Link = MakeJumpIfNotLe(Mode, OnNext, OnTarget, A, Aux + RegisterBase + 1)
		elseif Opcode == 32 then -- JUMPIFNOTLT
			Made, Link = MakeJumpIfNotLt(Mode, OnNext, OnTarget, A, Aux + RegisterBase + 1)
		elseif Opcode == 33 then -- ADD
			Made, Link = MakeAdd(Mode, OnNext, OnTarget, A, B + RegisterBase + 1, C + RegisterBase + 1)
		elseif Opcode == 34 then -- SUB
			Made, Link = MakeSub(Mode, OnNext, OnTarget, A, B + RegisterBase + 1, C + RegisterBase + 1)
		elseif Opcode == 35 then -- MUL
			Made, Link = MakeMul(Mode, OnNext, OnTarget, A, B + RegisterBase + 1, C + RegisterBase + 1)
		elseif Opcode == 36 then -- DIV
			Made, Link = MakeDiv(Mode, OnNext, OnTarget, A, B + RegisterBase + 1, C + RegisterBase + 1)
		elseif Opcode == 37 then -- MOD
			Made, Link = MakeMod(Mode, OnNext, OnTarget, A, B + RegisterBase + 1, C + RegisterBase + 1)
		elseif Opcode == 38 then -- POW
			Made, Link = MakePow(Mode, OnNext, OnTarget, A, B + RegisterBase + 1, C + RegisterBase + 1)
		elseif Opcode == 39 then -- ADDK
			Made, Link = MakeAddK(Mode, OnNext, OnTarget, A, B + RegisterBase + 1, Constants[C + 1])
		elseif Opcode == 40 then -- SUBK
			Made, Link = MakeSubK(Mode, OnNext, OnTarget, A, B + RegisterBase + 1, Constants[C + 1])
		elseif Opcode == 41 then -- MULK
			Made, Link = MakeMulK(Mode, OnNext, OnTarget, A, B + RegisterBase + 1, Constants[C + 1])
		elseif Opcode == 42 then -- DIVK
			Made, Link = MakeDivK(Mode, OnNext, OnTarget, A, B + RegisterBase + 1, Constants[C + 1])
		elseif Opcode == 43 then -- MODK
			Made, Link = MakeModK(Mode, OnNext, OnTarget, A, B + RegisterBase + 1, Constants[C + 1])
		elseif Opcode == 44 then -- POWK
			Made, Link = MakePowK(Mode, OnNext, OnTarget, A, B + RegisterBase + 1, Constants[C + 1])
		elseif Opcode == 45 then -- AND
			Made, Link = MakeAnd(Mode, OnNext, OnTarget, A, B + RegisterBase + 1, C + RegisterBase + 1)
		elseif Opcode == 46 then -- OR
			Made, Link = MakeOr(Mode, OnNext, OnTarget, A, B + RegisterBase + 1, C + RegisterBase + 1)
		elseif Opcode == 47 then -- ANDK
			Made, Link = MakeAndK(Mode, OnNext, OnTarget, A, B + RegisterBase + 1, Constants[C + 1])
		elseif Opcode == 48 then -- ORK
			Made, Link = MakeOrK(Mode, OnNext, OnTarget, A, B + RegisterBase + 1, Constants[C + 1])
		elseif Opcode == 49 then -- CONCAT
			const Base = B + RegisterBase + 1

			if C - B == 1 then
				Made, Link = MakeConcat2(Mode, OnNext, OnTarget, A, Base, Base + 1)
			elseif C - B == 2 then
				Made, Link = MakeConcat3(Mode, OnNext, OnTarget, A, Base, Base + 1, Base + 2)
			else
				Made, Link = MakeConcatN(Mode, OnNext, OnTarget, A, Base, C + RegisterBase + 1)
			end
		elseif Opcode == 50 then -- NOT
			Made, Link = MakeNot(Mode, OnNext, OnTarget, A, B + RegisterBase + 1)
		elseif Opcode == 51 then -- MINUS
			Made, Link = MakeMinus(Mode, OnNext, OnTarget, A, B + RegisterBase + 1)
		elseif Opcode == 52 then -- LENGTH
			Made, Link = MakeLength(Mode, OnNext, OnTarget, A, B + RegisterBase + 1)
		elseif Opcode == 53 then -- NEWTABLE
			if Aux == 0 then
				Made, Link = MakeNewTableEmpty(Mode, OnNext, OnTarget, A)
			else
				Made, Link = MakeNewTable(Mode, OnNext, OnTarget, A, Aux)
			end
		elseif Opcode == 54 then -- DUPTABLE
			const Template: Store = {}
			local Filled = false

			if Raw.ConstantKinds[SignedD + 1] == 8 then
				const Pairs = Constants[SignedD + 1]

				for Pair = 1, #Pairs, 2 do
					const FieldValue = if Pairs[Pair + 1] >= 0 then Constants[Pairs[Pair + 1] + 1] else nil

					if FieldValue ~= nil then
						Template[Constants[Pairs[Pair] + 1]] = FieldValue
						Filled = true
					end
				end
			end

			if Filled then
				Made, Link = MakeDupTable(Mode, OnNext, OnTarget, A, Template)
			else
				Made, Link = MakeNewTableEmpty(Mode, OnNext, OnTarget, A)
			end
		elseif Opcode == 55 then -- SETLIST
			Made, Link = MakeSetList(Mode, OnNext, OnTarget, A, B + RegisterBase + 1, C, Aux)
		elseif Opcode == 56 then -- FORNPREP
			Made, Link = MakeForNPrep(Mode, OnNext, OnTarget, A, A + 1, A + 2)
		elseif Opcode == 57 then -- FORNLOOP
			const Limit = LimitAt[Index]

			if StepOneAt[Index] and Limit ~= nil then
				Made, Link = MakeForNLoopStepOneLimit(Mode, OnNext, OnTarget, A + 2, Limit)
			elseif StepOneAt[Index] then
				Made, Link = MakeForNLoopStepOne(Mode, OnNext, OnTarget, A, A + 2)
			else
				Made, Link = MakeForNLoop(Mode, OnNext, OnTarget, A, A + 1, A + 2)
			end
		elseif Opcode == 58 then -- FORGLOOP
			const Count = Bit32BAnd(Aux, 0xFF)

			if Count == 1 then
				Made, Link = MakeForGLoop1(Mode, OnNext, OnTarget, A, A + 1, A + 2, A + 3)
			elseif Count == 2 and Bit32BTest(Aux, 0x80000000) then -- ipairs-style traversal
				Made, Link = MakeForGLoopIpairs(Mode, OnNext, OnTarget, A, A + 1, A + 2, A + 3, A + 4)
			elseif Count == 2 then
				Made, Link = MakeForGLoop2(Mode, OnNext, OnTarget, A, A + 1, A + 2, A + 3, A + 4)
			else
				Made, Link = MakeForGLoopN(Mode, OnNext, OnTarget, A, A + 1, A + 2, A + 3, Count)
			end
		elseif Opcode == 59 then -- FORGPREP_INEXT
			Made, Link = MakeForGPrepInext(Mode, OnNext, OnTarget, A, A + 1, A + 2)
		elseif Opcode == 61 then -- FORGPREP_NEXT
			Made, Link = MakeForGPrepNext(Mode, OnNext, OnTarget, A)
		elseif Opcode == 63 then -- GETVARARGS
			Made, Link = MakeGetVarargs(Mode, OnNext, OnTarget, A, B)
		elseif Opcode == 64 then -- DUPCLOSURE
			Made, Link = MakeDupClosure(Mode, OnNext, OnTarget, A, Describe(Start, Constants[SignedD + 1] + 1))
		elseif Opcode == 66 then -- LOADKX
			Made, Link = MakeLoadK(Mode, OnNext, OnTarget, A, Constants[Aux + 1])
		elseif Opcode == 71 then -- SUBRK
			Made, Link = MakeSubRK(Mode, OnNext, OnTarget, A, C + RegisterBase + 1, Constants[B + 1])
		elseif Opcode == 72 then -- DIVRK
			Made, Link = MakeDivRK(Mode, OnNext, OnTarget, A, C + RegisterBase + 1, Constants[B + 1])
		elseif Opcode == 76 then -- FORGPREP
			Made, Link = MakeForGPrep(Mode, OnNext, OnTarget, A, A + 1, A + 2)
		elseif Opcode == 77 then -- JUMPXEQKNIL
			if Bit32Extract(Aux, 31, 1) == 1 then
				Made, Link = MakeJumpIfNotNil(Mode, OnNext, OnTarget, A)
			else
				Made, Link = MakeJumpIfNil(Mode, OnNext, OnTarget, A)
			end
		elseif Opcode == 78 or Opcode == 79 or Opcode == 80 then -- JUMPXEQKB / JUMPXEQKN / JUMPXEQKS
			const K = if Opcode == 78 then Bit32BAnd(Aux, 1) == 1 else Constants[Bit32Extract(Aux, 0, 24) + 1]

			if Bit32Extract(Aux, 31, 1) == 1 then
				Made, Link = MakeJumpIfNotK(Mode, OnNext, OnTarget, A, K)
			else
				Made, Link = MakeJumpIfK(Mode, OnNext, OnTarget, A, K)
			end
		elseif Opcode == 81 then -- IDIV
			Made, Link = MakeIDiv(Mode, OnNext, OnTarget, A, B + RegisterBase + 1, C + RegisterBase + 1)
		elseif Opcode == 82 then -- IDIVK
			Made, Link = MakeIDivK(Mode, OnNext, OnTarget, A, B + RegisterBase + 1, Constants[C + 1])
		elseif Opcode == 86 then -- NEWCLASSMEMBER
			Made, Link = MakeNewClassMember(Mode, OnNext, OnTarget, A, C + RegisterBase + 1, Constants[Aux + 1])
		else
			Made, Link = MakeUnsupported(Opcode)
		end

		Handlers[Index] = Made
		Links[Index] = Link
	end

	-- only handlers with a backward edge are linked; their copies trampoline that edge through a patchable successor
	for Index = 1, Kept do
		const First = Primary[Index]
		const Second = Secondary[Index]
		const NextBack = First ~= 0 and First <= Index
		const TargetBack = Second ~= 0 and Second <= Index

		if NextBack or TargetBack then
			const OnNext = Handlers[First] or Stop
			const OnTarget = Handlers[Second] or Stop

			Links[Index](OnNext, OnTarget)
			table.insert(BackEdges, {
				Link = Links[Index],
				OnNext = OnNext,
				OnTarget = OnTarget,
				NextBack = NextBack,
				TargetBack = TargetBack,
			})
		end
	end

	Proto.First = Handlers[Resolve(1)] or Stop
end

-- Decides for every proto's upvalues whether they are cells (captured by reference) or plain values (captured by value).
const function ResolveCells(RawList: { Raw }, ProtoList: { Proto }, Index: number)
	const Raw = RawList[Index]
	const Words = Raw.Words
	const Cells = ProtoList[Index].Cells
	local Word = 1

	while Word <= #Words do
		const Opcode = Bit32BAnd(Words[Word], 0xFF)
		local Child = 0

		if Opcode == 19 then -- NEWCLOSURE
			const Operand = Bit32RShift(Words[Word], 16)

			Child = Raw.Protos[(if Operand < 0x8000 then Operand else Operand - 0x10000) + 1]
		elseif Opcode == 64 then -- DUPCLOSURE
			const Operand = Bit32RShift(Words[Word], 16)

			Child = (Raw.Constants[(if Operand < 0x8000 then Operand else Operand - 0x10000) + 1]) + 1
		end

		if Child ~= 0 then
			const ChildCells = ProtoList[Child].Cells

			for Capture = 1, RawList[Child].UpvalueCount do
				const Value = Words[Word + Capture]
				const Kind = Bit32BAnd(Bit32RShift(Value, 8), 0xFF)

				ChildCells[Capture] = Kind == 1 or (Kind == 2 and Cells[Bit32BAnd(Bit32RShift(Value, 16), 0xFF) + 1] == true)
			end

			ResolveCells(RawList, ProtoList, Child)
		end

		Word += if HasAux[Opcode] then 2 else 1
	end
end

const function Load(Bytecode: string | buffer, Env: Store, Config: Settings?)
	const Active = Config or NewSettings()
	const RawList, MainIndex = Deserialize(Bytecode, Active)
	const BackEdges: { BackEdge } = {}
	const ProtoList: { Proto } = {}

	for Index = 1, #RawList do
		const Raw = RawList[Index]

		ProtoList[Index] = {
			MaxStackSize = Raw.MaxStackSize + RegisterBase + 1,
			ParamCount = Raw.ParamCount,
			UpvalueCount = Raw.UpvalueCount,
			IsVararg = Raw.IsVararg,
			First = Stop,
			Cells = {},
			Make = Unprepared,
		}
	end

	ResolveCells(RawList, ProtoList, MainIndex)

	for Index = 1, #RawList do
		Decode(RawList[Index], ProtoList[Index], RawList, ProtoList, Env, BackEdges)
	end

	for _, Proto in ProtoList do
		Proto.Make = MakeFactory(Proto)
	end

	const function Close()
		for _, Edge in BackEdges do
			Edge.Link(if Edge.NextBack then Stop else Edge.OnNext, if Edge.TargetBack then Stop else Edge.OnTarget)
		end
	end

	return ProtoList[MainIndex].Make({}), Close
end

return {
	NewSettings = NewSettings,
	Load = Load,
}
