--!optimize 2
--!strict

--[[
	Generates Source/BakedVM, the operand-baked and direct-threaded sibling of Source/VM.luau.
	Run from the repository root: `lute run Tools/BakeVM.luau`.

	Output
		Source/BakedVM/init.luau holds the loader, decoder and closure factories; Runtime.luau the types and helpers every module
		shares; the remaining modules hold the handler families, grouped so each module stays small enough for the type checker.

	Design Notes
		Every handler family is written once below as a template. The generator emits one Make function per family holding a
		decode-time if-tree over small operand values, where each leaf is a copy of the handler with register numbers baked into
		literal table indexes, followed by the generic handler for operands outside the baked range.
		Each handler body exists once per link mode: a chained edge calls its successor directly, a trampolined edge returns it to
		the Entry loop. The generic copy has every mode (four for two-successor handlers); baked copies only the modes edges use.
		Every proto is traversed by each GC cycle of the host process, so the baked ranges and modes are a speed/heap trade-off.
		Template placeholders: `{A}` is the register slot of operand A, `{A+2}` the slot two above it, `{#A}` and `{#A+2}` the slot
		indexes themselves, and `{Next}` / `{Target}` the return statements for the fallthrough and branch successors.
]]

const Fs = require("@lute/fs")

type Operand = {
	Name: string,
	Kind: string,
	Range: number,
}

type Param = {
	Name: string,
	Type: string,
}

type Family = {
	Name: string,
	Doc: string,
	Module: string,
	Operands: { Operand },
	Params: { Param },
	Successors: number,
	Locals: { string },
	Distinct: { { string } },
	Body: string,
}

type Module = {
	Name: string,
	Description: string,
	Families: { string },
	Prefixes: { string }?,
	Lazy: boolean?,
}

type Builtin = {
	Id: number,
	Expressions: { string },
	Arities: { number },
	Returns: boolean,
	Module: string,
}

const OutputDirectory = "Source/BakedVM"

-- Bake ranges: registers below these values get their own handler copies.
const HotTripleRange = 12
const ColdTripleRange = 4
const PairRange = 16
const ColdPairRange = 8
const UpvalueRange = 8
const SingleRange = 32
const CallRange = 32
const CallTopRange = 16

-- Families whose instructions often precede a call also get a baked trampolined copy (mode 0): an edge into a call is always
-- trampolined. NAMECALL is always followed by its call, so it only needs that copy.
const BakedModeOverrides: { [string]: { number } } = {
	NameCall = { 0 },
	Move = { 1, 0 },
	LoadK = { 1, 0 },
	GetUpvalValue = { 1, 0 },
	GetUpval = { 1, 0 },
	GetTableKS = { 1, 0 },
	AddK = { 1, 0 },
	SubK = { 1, 0 },
}

-- Fixed-argument call families cover up to this many arguments; Entry closures cover up to MaxEntryParams fixed parameters.
const MaxCallArgs = 6
const MaxMethodArgs = 4
const MaxEntryParams = 8

-- Handler modules in output order; call families (named Call...) go to Calls. Modules hold the generic handlers and the loaders
-- of the baked variants, which live in Variants/.
const Modules: { Module } = {
	{
		Name = "Arithmetic",
		Description = "Arithmetic and logic on registers and constants.",
		Families = {
			"Add", "Sub", "Mul", "Div", "Mod", "Pow", "IDiv", "AddK", "SubK", "MulK", "DivK", "ModK", "IDivK", "SubRK", "DivRK", "PowK",
			"Minus", "And", "Or", "AndK", "OrK", "Not",
		},
	},
	{
		Name = "Tables",
		Description = "Table reads and writes, method lookup, table construction and length.",
		Families = {
			"GetTable", "SetTable", "GetTableKS", "SetTableKS", "GetTableN", "SetTableN", "NewClassMember", "NameCall", "NewTableEmpty",
			"NewTable", "DupTable", "SetList", "Length",
		},
	},
	{
		Name = "Control",
		Description = "Jumps, conditional jumps and loops.",
		Families = {
			"JumpIfEq", "JumpIfLe", "JumpIfLt", "JumpIfNotEq", "JumpIfNotLe", "JumpIfNotLt", "Jump", "JumpIf", "JumpIfNot", "JumpIfK",
			"JumpIfNotK", "JumpIfNil", "JumpIfNotNil", "ForNPrep", "ForNLoop", "ForNLoopStepOne", "ForNLoopStepOneLimit", "ForGPrep",
			"ForGPrepInext", "ForGLoop1", "ForGLoop2", "ForGLoopIpairs", "ForGLoopN",
		},
	},
	{
		Name = "Values",
		Description = "Register moves, constant and global loads, upvalue access, concatenation and varargs.",
		Families = {
			"Move", "LoadK", "LoadNil", "LoadSkip", "GetGlobal", "SetGlobal", "GetImportSlow", "GetUpvalValue", "GetUpval", "SetUpval",
			"CloseUpvals", "Concat2", "Concat3", "ConcatN", "GetVarargs1", "GetVarargs2", "GetVarargsN", "GetVarargsMulti",
		},
	},
	{
		Name = "Frames",
		Description = "Returns, closure creation and unsupported opcodes.",
		Families = { "ReturnNone", "ReturnOne", "ReturnTwo", "Return0", "Return1", "Return2", "ReturnRange", "NewClosure", "DupClosure", "Unsupported" },
		Prefixes = { "NewClosureWith" },
	},
	{ Name = "Calls", Description = "Calls by argument and result count.", Families = {} },
	{ Name = "Methods", Description = "Method calls: a NAMECALL fused with the CALL right after it.", Families = {} },
	{ Name = "BuiltinsCore", Description = "Calls hinted by FASTCALL to base, string and table builtins.", Families = {}, Lazy = true },
	{ Name = "BuiltinsMath", Description = "Calls hinted by FASTCALL to math builtins.", Families = {}, Lazy = true },
	{ Name = "BuiltinsBit32", Description = "Calls hinted by FASTCALL to bit32 builtins.", Families = {}, Lazy = true },
	{ Name = "BuiltinsVector", Description = "Calls hinted by FASTCALL to vector builtins.", Families = {}, Lazy = true },
	{ Name = "BuiltinsBuffer", Description = "Calls hinted by FASTCALL to buffer builtins.", Families = {}, Lazy = true },
	{ Name = "BuiltinsInteger", Description = "Calls hinted by FASTCALL to integer builtins.", Families = {}, Lazy = true },
}

-- Builtins the compiler emits FASTCALL hints for, by LuauBuiltinFunction id (Common/include/Luau/Bytecode.h): the host functions
-- the hinted call may be, the argument counts that get a handler, whether it returns a value, and the module holding them.
-- Omitted: table.unpack and select (variable results or arguments) and setmetatable.
const Builtins: { Builtin } = {}

const function Hint(Id: number, Module: string, Expressions: { string }, Arities: { number }, Returns: boolean?)
	table.insert(Builtins, { Id = Id, Expressions = Expressions, Arities = Arities, Returns = Returns ~= false, Module = Module })
end

Hint(1, "BuiltinsCore", { "assert" }, { 1, 2 })
Hint(40, "BuiltinsCore", { "type" }, { 1 })
Hint(41, "BuiltinsCore", { "string.byte" }, { 1, 2, 3 })
Hint(42, "BuiltinsCore", { "string.char" }, { 1, 2, 3 })
Hint(43, "BuiltinsCore", { "string.len" }, { 1 })
Hint(44, "BuiltinsCore", { "typeof" }, { 1 })
Hint(45, "BuiltinsCore", { "string.sub" }, { 2, 3 })
Hint(49, "BuiltinsCore", { "rawset" }, { 3 })
Hint(50, "BuiltinsCore", { "rawget" }, { 2 })
Hint(51, "BuiltinsCore", { "rawequal" }, { 2 })
Hint(52, "BuiltinsCore", { "table.insert" }, { 2, 3 }, false)
Hint(58, "BuiltinsCore", { "rawlen" }, { 1 })
Hint(60, "BuiltinsCore", { "getmetatable" }, { 1 })
Hint(62, "BuiltinsCore", { "tonumber" }, { 1, 2 })
Hint(63, "BuiltinsCore", { "tostring" }, { 1 })

for Id, Name in { [2] = "abs", [3] = "acos", [4] = "asin", [6] = "atan", [7] = "ceil", [8] = "cosh", [9] = "cos", [10] = "deg", [11] = "exp", [12] = "floor", [14] = "frexp", [16] = "log10", [20] = "modf", [22] = "rad", [23] = "sinh", [24] = "sin", [25] = "sqrt", [26] = "tanh", [27] = "tan", [47] = "sign", [48] = "round", [91] = "isnan", [92] = "isinf", [93] = "isfinite" } do
	Hint(Id, "BuiltinsMath", { `math.{Name}` }, { 1 })
end

for Id, Name in { [5] = "atan2", [13] = "fmod", [15] = "ldexp", [21] = "pow" } do
	Hint(Id, "BuiltinsMath", { `math.{Name}` }, { 2 })
end

Hint(17, "BuiltinsMath", { "math.log" }, { 1, 2 })
Hint(18, "BuiltinsMath", { "math.max" }, { 2, 3 })
Hint(19, "BuiltinsMath", { "math.min" }, { 2, 3 })
Hint(46, "BuiltinsMath", { "math.clamp" }, { 3 })
Hint(89, "BuiltinsMath", { "math.lerp" }, { 3 })

for Id, Name in { [28] = "arshift", [33] = "btest", [35] = "lrotate", [36] = "lshift", [38] = "rrotate", [39] = "rshift" } do
	Hint(Id, "BuiltinsBit32", { `bit32.{Name}` }, { 2 })
end

for Id, Name in { [30] = "bnot", [55] = "countlz", [56] = "countrz", [64] = "byteswap" } do
	Hint(Id, "BuiltinsBit32", { `bit32.{Name}` }, { 1 })
end

Hint(29, "BuiltinsBit32", { "bit32.band" }, { 1, 2, 3 })
Hint(31, "BuiltinsBit32", { "bit32.bor" }, { 2, 3 })
Hint(32, "BuiltinsBit32", { "bit32.bxor" }, { 2, 3 })
Hint(34, "BuiltinsBit32", { "bit32.extract" }, { 2, 3 })
Hint(59, "BuiltinsBit32", { "bit32.extract" }, { 2, 3 })
Hint(37, "BuiltinsBit32", { "bit32.replace" }, { 3, 4 })

for Id, Name in { [78] = "magnitude", [79] = "normalize", [82] = "floor", [83] = "ceil", [84] = "abs", [85] = "sign" } do
	Hint(Id, "BuiltinsVector", { `vector.{Name}` }, { 1 })
end

Hint(54, "BuiltinsVector", { "vector.create" }, { 2, 3 })
Hint(80, "BuiltinsVector", { "vector.cross" }, { 2 })
Hint(81, "BuiltinsVector", { "vector.dot" }, { 2 })
Hint(86, "BuiltinsVector", { "vector.clamp" }, { 3 })
Hint(87, "BuiltinsVector", { "vector.min" }, { 2, 3 })
Hint(88, "BuiltinsVector", { "vector.max" }, { 2, 3 })
Hint(90, "BuiltinsVector", { "vector.lerp" }, { 3 })

for Id, Name in { [65] = "readi8", [66] = "readu8", [68] = "readi16", [69] = "readu16", [71] = "readi32", [72] = "readu32", [74] = "readf32", [76] = "readf64", [131] = "readinteger" } do
	Hint(Id, "BuiltinsBuffer", { `buffer.{Name}` }, { 2 })
end

Hint(67, "BuiltinsBuffer", { "buffer.writeu8", "buffer.writei8" }, { 3 }, false)
Hint(70, "BuiltinsBuffer", { "buffer.writeu16", "buffer.writei16" }, { 3 }, false)
Hint(73, "BuiltinsBuffer", { "buffer.writeu32", "buffer.writei32" }, { 3 }, false)
Hint(75, "BuiltinsBuffer", { "buffer.writef32" }, { 3 }, false)
Hint(77, "BuiltinsBuffer", { "buffer.writef64" }, { 3 }, false)
Hint(132, "BuiltinsBuffer", { "buffer.writeinteger" }, { 3 }, false)

for Id, Name in { [94] = "create", [95] = "tonumber", [96] = "neg", [111] = "bnot", [128] = "countrz", [129] = "countlz", [130] = "bswap" } do
	Hint(Id, "BuiltinsInteger", { `integer.{Name}` }, { 1 })
end

for Id, Name in { [97] = "add", [98] = "sub", [99] = "mul", [100] = "div", [103] = "rem", [104] = "idiv", [105] = "udiv", [106] = "urem", [107] = "mod", [113] = "lt", [114] = "le", [115] = "ult", [116] = "ule", [117] = "gt", [118] = "ge", [119] = "ugt", [120] = "uge", [121] = "lshift", [122] = "rshift", [123] = "arshift", [124] = "lrotate", [125] = "rrotate", [127] = "btest" } do
	Hint(Id, "BuiltinsInteger", { `integer.{Name}` }, { 2 })
end

for Id, Name in { [101] = "min", [102] = "max", [109] = "band", [110] = "bor", [112] = "bxor", [126] = "extract" } do
	Hint(Id, "BuiltinsInteger", { `integer.{Name}` }, { 2, 3 })
end

Hint(108, "BuiltinsInteger", { "integer.clamp" }, { 3 })

table.sort(Builtins, function(Left: Builtin, Right: Builtin): boolean
	return Left.Id < Right.Id
end)

-- The local alias generated code uses for a library expression: math.floor -> MathFloor, rawget -> Rawget.
-- The value a builtin alias is declared with: the integer library is missing on Roblox, so its members alias to nil there
-- instead of failing when the module loads. They keep their function type, since Matches never proves a call to a nil builtin.
const function AliasValue(Expression: string): string
	return if string.sub(Expression, 1, 8) == "integer." then `(integer and {Expression} or nil) :: typeof({Expression})` else Expression
end

const function AliasOf(Expression: string): string
	const Parts: { string } = {}

	for Part in string.gmatch(Expression, "[^%.]+") do
		table.insert(Parts, `{string.upper(string.sub(Part, 1, 1))}{string.sub(Part, 2)}`)
	end

	return table.concat(Parts)
end

-- The handler family name for a builtin called with Count arguments for Results (0 or 1) results.
const function FastName(Expression: string, Count: number, Results: number): string
	return `Fast{AliasOf(Expression)}{Count}x{Results}`
end

-- Library globals the generated modules may alias, and what Runtime.luau exports; each module declares only the names it uses.
const GlobalAliases: { { string } } = {
	{ "Type", "type" },
	{ "Typeof", "typeof" },
	{ "Error", "error" },
	{ "Next", "next" },
	{ "Select", "select" },
	{ "Tonumber", "tonumber" },
	{ "Rawget", "rawget" },
	{ "Rawequal", "rawequal" },
	{ "Getmetatable", "getmetatable" },
	{ "StringFormat", "string.format" },
	{ "TablePack", "table.pack" },
	{ "TableClone", "table.clone" },
	{ "TableCreate", "table.create" },
	{ "TableInsert", "table.insert" },
	{ "TableMove", "table.move" },
	{ "TableUnpack", "table.unpack" },
	{ "BufferFromString", "buffer.fromstring" },
	{ "BufferLen", "buffer.len" },
	{ "BufferReadU8", "buffer.readu8" },
	{ "BufferReadU32", "buffer.readu32" },
	{ "BufferReadF32", "buffer.readf32" },
	{ "BufferReadF64", "buffer.readf64" },
	{ "BufferReadString", "buffer.readstring" },
	{ "Bit32BOr", "bit32.bor" },
	{ "Bit32BAnd", "bit32.band" },
	{ "Bit32BTest", "bit32.btest" },
	{ "Bit32RShift", "bit32.rshift" },
	{ "Bit32LShift", "bit32.lshift" },
	{ "Bit32Extract", "bit32.extract" },
	{ "IntegerFromString", "integer and integer.fromstring or nil" },
	{ "MathMax", "math.max" },
	{ "MathSqrt", "math.sqrt" },
}

for _, Hinted in Builtins do
	for _, Expression in Hinted.Expressions do
		const Alias = AliasOf(Expression)
		local Known = false

		for _, Existing in GlobalAliases do
			Known = Known or Existing[1] == Alias
		end

		if not Known then
			table.insert(GlobalAliases, { Alias, Expression })
		end
	end
end

-- Module of each builtin handler family, filled as the families are defined.
const FastModules: { [string]: string } = {}

const RuntimeValues = { "Capture", "NoUpvalues", "LuaMultRet", "EmptyVarargs", "RegisterBase", "Inext", "IpairsStep", "CloseUpvalue", "Stop", "Unlinked", "Spread" }
const RuntimeTypes = { "Store", "Registers", "Handler", "Linker", "Factory", "Upvalue", "Cached", "Proto" }

type VariantBlock = {
	Module: string,
	Label: string,
	Lines: { string },
}

type VariantPack = {
	Module: string,
	Name: string,
	Labels: { string },
	Lines: { string },
}

-- Baked handlers per variant block: a family's baked copies are split into blocks of first-operand values, and a block is only
-- required on first use, so only the variants a loaded program needs ever exist in the heap. Blocks of one module are packed
-- into variant files of about PackLines lines.
const VariantsPerFile = 288
const PackLines = 3000

local Output: { string } = {}
const Families: { Family } = {}
const VariantBlocks: { VariantBlock } = {}
const VariantPacks: { VariantPack } = {}
const PackOf: { [string]: VariantPack } = {}

const function Push(Line: string)
	table.insert(Output, Line)
end

const function ModuleOf(Name: string): string
	for _, Module in Modules do
		if table.find(Module.Families, Name) ~= nil then
			return Module.Name
		end

		for _, Prefix in Module.Prefixes or {} do
			if string.sub(Name, 1, #Prefix) == Prefix then
				return Module.Name
			end
		end
	end

	if FastModules[Name] ~= nil then
		return FastModules[Name]
	elseif string.sub(Name, 1, 6) == "Method" then
		return "Methods"
	end

	assert(string.sub(Name, 1, 4) == "Call", `family {Name} belongs to no module`)

	return "Calls"
end

const function Register(Name: string, Range: number): Operand
	return { Name = Name, Kind = "Register", Range = Range }
end

const function Upvalue(Name: string, Range: number): Operand
	return { Name = Name, Kind = "Upvalue", Range = Range }
end

const function Param(Name: string, Type: string): Param
	return { Name = Name, Type = Type }
end

-- Doc is what the instruction does, written with the body's operand placeholders and rendered into the comments of every copy.
-- Distinct lists operand pairs whose baked copies would be degenerate when equal (MOVE R R, comparing a register with itself);
-- those combinations are left to the generic handler.
const function Define(Name: string, Doc: string, Operands: { Operand }, Params: { Param }, Successors: number, Body: string, Locals: { string }?, Distinct: { { string } }?)
	const Defined: Family = {
		Name = Name,
		Doc = Doc,
		Module = ModuleOf(Name),
		Operands = Operands,
		Params = Params,
		Successors = Successors,
		Locals = Locals or {},
		Distinct = Distinct or {},
		Body = Body,
	}

	table.insert(Families, Defined)
end

-- Binary operators with a compound assignment form.
const CompoundOperators: { [string]: boolean } = {
	["+"] = true,
	["-"] = true,
	["*"] = true,
	["/"] = true,
	["//"] = true,
	["%"] = true,
	["^"] = true,
	[".."] = true,
}

const function IsChained(Family: Family, Mode: number, Which: number): boolean
	if Family.Successors == 1 then
		return Mode == 1
	elseif Which == 1 then
		return Mode % 2 == 1
	end

	return Mode >= 2
end

-- Renders a family's Doc: R(A) and U(B) name the operands of the generic copy; Baked maps every operand to its value for a baked
-- copy, which renders as R5 or U1.
const function RenderDoc(Family: Family, Baked: { [string]: number }?): string
	const function Replace(...: string): string
		const Whole, Hash, Name, Digits = ...
		local Found: Operand? = nil

		for _, Operand in Family.Operands do
			if Operand.Name == Name then
				Found = Operand
			end
		end

		if Found == nil then
			return Whole
		end

		const Shift = if Digits == "" then 0 else tonumber(Digits) :: number
		const Prefix = if Hash == "#" then "" elseif Found.Kind == "Register" then "R" else "U"

		if Baked ~= nil then
			return `{Prefix}{Baked[Name] + Shift}`
		end

		const Index = if Shift == 0 then Name else `{Name}+{Shift}`

		return if Hash == "#" then Index else `{Prefix}({Index})`
	end

	return (string.gsub(Family.Doc, "({(#?)(%a+)%+?(%d*)})", Replace))
end

-- Describes which operand values get baked copies, for example "A, B, C < 12" or "A < 16, B < 8, A ~= B"; First overrides the
-- first operand's part.
const function RangesOf(Family: Family, First: string?): string
	const Parts: { string } = {}
	local Names: { string } = {}
	local Range = -1

	const function Flush()
		if #Names > 0 then
			table.insert(Parts, `{table.concat(Names, ", ")} < {Range}`)
		end
	end

	for Position, Operand in Family.Operands do
		if Position == 1 and First ~= nil then
			table.insert(Parts, First)
		elseif Operand.Range == Range then
			table.insert(Names, Operand.Name)
		else
			Flush()
			Names = { Operand.Name }
			Range = Operand.Range
		end
	end

	Flush()

	for _, Pair in Family.Distinct do
		table.insert(Parts, `{Pair[1]} ~= {Pair[2]}`)
	end

	return table.concat(Parts, ", ")
end

-- Doc text as the start of a sentence.
const function Sentence(Text: string): string
	return `{string.upper(string.sub(Text, 1, 1))}{string.sub(Text, 2)}`
end

-- The comment on a link mode's branch: which edges of the copy call their successor directly.
const function ModeNote(Family: Family, Mode: number): string
	if Family.Successors == 1 then
		return "chained"
	elseif Mode == 3 then
		return "both edges chained"
	end

	return if Mode == 2 then "branch chained" else "fallthrough chained"
end

-- Expands a family body for one link mode; Baked maps operand names to their values, or is nil for the generic handler.
const function Expand(Family: Family, Baked: { [string]: number }?, Mode: number): { string }
	const Lines: { string } = {}

	const function Replace(...: string): string
		const Whole, Hash, Name, Digits = ...

		--// a chained edge always moves forward, so its successor exists when the maker runs and is captured as a constant;
		--// a trampolined edge may move backward, so it reads a successor that Link patches
		if Name == "Next" then
			return if IsChained(Family, Mode, 1) then "return OnNext(Stack)" else "return NextFn"
		elseif Name == "Target" then
			return if IsChained(Family, Mode, 2) then "return OnTarget(Stack)" else "return TargetFn"
		end

		local Found: Operand? = nil

		for _, Operand in Family.Operands do
			if Operand.Name == Name then
				Found = Operand
			end
		end

		if Found == nil then
			return Whole
		end

		const Shift = if Digits == "" then 0 else tonumber(Digits) :: number
		local Index: string

		if Baked ~= nil then
			const Base = if Found.Kind == "Register" then 6 else 1

			Index = tostring(Baked[Name] + Base + Shift)
		else
			const Prefix = if Found.Kind == "Register" then "Slot" else "Index"

			Index = if Shift == 0 then `{Prefix}{Name}` else `{Prefix}{Name} + {Shift}`
		end

		if Hash == "#" then
			return Index
		elseif Found.Kind == "Register" then
			return `Stack[{Index}]`
		end

		return `Stack[1][{Index}]`
	end

	for Line in string.gmatch(`{Family.Body}\n`, "(.-)\n") do
		const Expanded = string.gsub(Line, "({(#?)(%a+)%+?(%d*)})", Replace)
		const Indent, Target, Left, Operator, Right = string.match(Expanded, "^(%s*)([%w_%[%]]+) = ([%w_%[%]]+) (%S+) ([%w_%.%[%]]+)$")

		--// a baked copy whose target is also its left operand reads better as a compound assignment, with the same semantics
		if Target ~= nil and Operator ~= nil and Target == Left and CompoundOperators[Operator] then
			table.insert(Lines, `{Indent}{Target} {Operator}= {Right}`)
		else
			table.insert(Lines, Expanded)
		end
	end

	--// `if C then return X end` followed by `return Y` is `return if C then X else Y`
	for Index = #Lines - 4, 1, -1 do
		const Indent, Condition = string.match(Lines[Index], "^(%s*)if (.+) then$")

		if Indent ~= nil and Condition ~= nil and Lines[Index + 3] == "" and Lines[Index + 2] == `{Indent}end` then
			const Taken = string.match(Lines[Index + 1], `^{Indent}\treturn (.+)$`)
			const Otherwise = string.match(Lines[Index + 4], `^{Indent}return (.+)$`)

			if Taken ~= nil and Otherwise ~= nil then
				Lines[Index] = `{Indent}return if {Condition} then {Taken} else {Otherwise}`

				for _ = 1, 4 do
					table.remove(Lines, Index + 1)
				end
			end
		end
	end

	--// drop a write-back of a local into the slot it was copied from when nothing wrote that slot in between (NAMECALL whose
	--// object already sits in A + 1); no code outside the handler can write the register file
	for Index = #Lines, 1, -1 do
		const Slot, Name = string.match(Lines[Index], "^%s*(Stack%[%d+%]) = (%w+)$")

		if Slot ~= nil and Name ~= nil then
			for Earlier = Index - 1, 1, -1 do
				const Copied, Source = string.match(Lines[Earlier], "^%s*const (%w+) = (Stack%[%d+%])$")

				if Copied == Name and Source == Slot then
					table.remove(Lines, Index)

					break
				elseif string.find(Lines[Earlier], `{Slot} =`, 1, true) ~= nil then
					break
				end
			end
		end
	end

	return Lines
end

-- Whether code reads the patchable successor Name (NextFn or TargetFn).
const function ReadsSuccessor(Code: string, Name: string): boolean
	return string.find(Code, `%f[%w]{Name}%f[^%w]`) ~= nil
end

-- Emits one handler copy; only a copy with a trampolined edge returns Link, so a fully chained copy is never patched.
const function EmitClosure(Family: Family, Indent: string, Baked: { [string]: number }?, Mode: number)
	const Lines = Expand(Family, Baked, Mode)
	const Code = table.concat(Lines, "\n")
	const Patched = ReadsSuccessor(Code, "NextFn") or ReadsSuccessor(Code, "TargetFn")

	Push(`{Indent}return function(Stack: Registers): Handler?`)

	for _, Line in Lines do
		Push(if Line == "" then "" else `{Indent}\t{Line}`)
	end

	Push(`{Indent}end, {if Patched then "Link" else "Unlinked"}`)
end

-- Link modes that get baked copies: the chained ones, which nearly every edge uses. Other modes fall back to the generic copy, so
-- the module holds fewer protos for the garbage collector to traverse on every cycle.
const function BakedModesOf(Family: Family): { number }
	const Override = BakedModeOverrides[Family.Name]

	if Override ~= nil then
		return Override
	elseif string.sub(Family.Name, 1, 8) == "ForGLoop" or string.sub(Family.Name, 1, 6) == "Method" then
		return { 1, 0 }
	elseif Family.Successors == 1 then
		return { 1 }
	elseif string.sub(Family.Name, 1, 8) == "ForNLoop" then
		return { 1 }
	end

	return { 3 }
end

-- Link modes a family's instructions can be decoded with: a loop instruction's branch target is always a back edge, so it is
-- never chained (bit 2).
const function PossibleModesOf(Family: Family): { number }
	if Family.Successors == 0 then
		return { 0 }
	elseif Family.Successors == 1 or string.sub(Family.Name, 1, 8) == "ForNLoop" or string.sub(Family.Name, 1, 8) == "ForGLoop" then
		return { 1, 0 }
	end

	return { 3, 2, 1, 0 }
end

-- Emits one closure per mode, the last one unconditional: the baked modes for a baked copy, every possible mode otherwise.
const function EmitModes(Family: Family, Indent: string, Baked: { [string]: number }?)
	const Modes = if Baked ~= nil and Family.Successors > 0 then BakedModesOf(Family) else PossibleModesOf(Family)

	for Index = 1, #Modes - 1 do
		Push(`{Indent}if Mode == {Modes[Index]} then --// {ModeNote(Family, Modes[Index])}`)
		EmitClosure(Family, `{Indent}\t`, Baked, Modes[Index])
		Push(`{Indent}end`)
		Push("")
	end

	EmitClosure(Family, Indent, Baked, Modes[#Modes])
end

-- The values of operand Depth from Low to High - 1 that get a baked copy, given the operands already baked: values equal to
-- a Distinct partner are skipped.
const function ValuesOf(Family: Family, Depth: number, Low: number, High: number, Baked: { [string]: number }): { number }
	const Name = Family.Operands[Depth].Name
	const Values: { number } = {}

	for Value = Low, High - 1 do
		local Allowed = true

		for _, Pair in Family.Distinct do
			const Partner = if Pair[1] == Name then Pair[2] elseif Pair[2] == Name then Pair[1] else nil

			if Partner ~= nil and Baked[Partner] == Value then
				Allowed = false
			end
		end

		if Allowed then
			table.insert(Values, Value)
		end
	end

	return Values
end

-- Emits a binary decision tree over the allowed values of operand Depth, so nesting stays logarithmic in the range.
const function EmitTree(Family: Family, Indent: string, Depth: number, Values: { number }, Baked: { [string]: number })
	const Operand = Family.Operands[Depth]

	if #Values == 1 then
		Baked[Operand.Name] = Values[1]

		if Depth == #Family.Operands then
			Push(`{Indent}--// {RenderDoc(Family, Baked)}`)
			EmitModes(Family, Indent, Baked)
		else
			EmitTree(Family, Indent, Depth + 1, ValuesOf(Family, Depth + 1, 0, Family.Operands[Depth + 1].Range, Baked), Baked)
		end

		Baked[Operand.Name] = nil

		return
	end

	const Middle = #Values // 2 + 1

	Push(`{Indent}if {Operand.Name} < {Values[Middle]} then`)
	EmitTree(Family, `{Indent}\t`, Depth, table.move(Values, 1, Middle - 1, 1, {}), Baked)
	Push(`{Indent}end`)
	Push("")
	EmitTree(Family, Indent, Depth, table.move(Values, Middle, #Values, 1, {}), Baked)
end

-- The parameter list of a family's Make function (and of its variant makers). A family with successors also takes them: chained
-- copies capture them as constants, trampolined copies start their patchable successors from them.
const function ArgumentsOf(Family: Family): { string }
	const Arguments: { string } = { "Mode: number" }

	for _, Operand in Family.Operands do
		table.insert(Arguments, `{Operand.Name}: number`)
	end

	for _, Parameter in Family.Params do
		table.insert(Arguments, `{Parameter.Name}: {Parameter.Type}`)
	end

	if Family.Successors >= 1 then
		table.insert(Arguments, "OnNext: Handler")
		table.insert(Arguments, "OnTarget: Handler")
	end

	return Arguments
end

-- Emits a maker's body behind the state it needs: the family's locals, and the patchable successors with their Link function
-- when some copy in Body trampolines an edge. Link only ever patches backward edges, which the decoder links after every
-- handler exists, and Close() relinks.
const function EmitLinkage(Family: Family, Body: { string })
	const Code = table.concat(Body, "\n")
	const PatchesNext = ReadsSuccessor(Code, "NextFn")
	const PatchesTarget = ReadsSuccessor(Code, "TargetFn")

	if PatchesNext then
		Push("\tlocal NextFn: Handler = OnNext")
	end

	if PatchesTarget then
		Push("\tlocal TargetFn: Handler = OnTarget")
	end

	for _, Line in Family.Locals do
		Push(`\t{Line}`)
	end

	if PatchesNext or PatchesTarget or #Family.Locals > 0 then
		Push("")
	end

	if PatchesNext or PatchesTarget then
		Push("\tconst function Link(LinkedNext: Handler, LinkedTarget: Handler)")

		if PatchesNext then
			Push("\t\tNextFn = LinkedNext")
		end

		if PatchesTarget then
			Push("\t\tTargetFn = LinkedTarget")
		end

		Push("\tend")
		Push("")
	end

	for _, Line in Body do
		Push(Line)
	end
end

-- Runs Emit into a fresh buffer and returns the lines it pushed.
const function Collect(Emit: () -> ()): { string }
	const Saved = Output

	Output = {}
	Emit()

	const Lines = Output

	Output = Saved

	return Lines
end

-- How many values of a family's first operand one variant block covers, so each block holds about VariantsPerFile handlers.
const function BlockSizeOf(Family: Family): number
	local Below = 1

	for Index = 2, #Family.Operands do
		Below *= Family.Operands[Index].Range
	end

	--// the type checker gives up on a file with a few hundred multiple assignments from calls, so those families use half blocks
	const Limit = if string.find(Family.Body, "{A}, {A+1}", 1, true) ~= nil then VariantsPerFile // 2 - 16 else VariantsPerFile

	return math.max(1, Limit // Below)
end

-- The name of the variant block of a family that covers first-operand values Low to High: the family name, plus the register range
-- when the family is split into several blocks (AddR0ToR1).
const function BlockLabel(Family: Family, Low: number): string
	const First = Family.Operands[1]
	const Block = BlockSizeOf(Family)
	const High = math.min(Low + Block, First.Range) - 1

	if Block >= First.Range then
		return Family.Name
	elseif High == Low then
		return `{Family.Name}R{Low}`
	end

	return `{Family.Name}R{Low}ToR{High}`
end

-- Collects the variant blocks of a baked family: each block is a maker with the baked tree for one block of first-operand values.
const function EmitVariants(Family: Family)
	const First = Family.Operands[1]
	const Block = BlockSizeOf(Family)

	for Low = 0, First.Range - 1, Block do
		const Label = BlockLabel(Family, Low)
		const High = math.min(Low + Block, First.Range) - 1
		const Saved = Output
		local Values: string? = nil

		if Block < First.Range then
			Values = if High == Low then `{First.Name} = {Low}` else `{First.Name} = {Low} to {High}`
		end

		Output = {}
		Push(`-- {Sentence(RenderDoc(Family, nil))}, baked for {RangesOf(Family, Values)}: one copy per operand combination.`)
		Push(`const function Make{Label}({table.concat(ArgumentsOf(Family), ", ")}): (Handler, Linker)`)
		EmitLinkage(
			Family,
			Collect(function()
				EmitTree(Family, "\t", 1, ValuesOf(Family, 1, Low, math.min(Low + Block, First.Range), {}), {})
			end)
		)
		Push("end")
		Push("")
		table.insert(VariantBlocks, { Module = Family.Module, Label = Label, Lines = Output })
		Output = Saved
	end
end

-- Packs each module's variant blocks, in order, into files of about PackLines lines, named after the blocks they hold.
const function PackVariants()
	for _, Module in Modules do
		local Current: VariantPack? = nil

		for _, Block in VariantBlocks do
			if Block.Module == Module.Name then
				if Current == nil or (#Current.Lines > 0 and #Current.Lines + #Block.Lines > PackLines) then
					const Created: VariantPack = { Module = Module.Name, Name = "", Labels = {}, Lines = {} }

					table.insert(VariantPacks, Created)
					Current = Created
				end

				const Pack = Current :: VariantPack

				table.insert(Pack.Labels, Block.Label)
				PackOf[Block.Label] = Pack

				for _, Line in Block.Lines do
					table.insert(Pack.Lines, Line)
				end
			end
		end
	end

	for _, Pack in VariantPacks do
		const Labels = Pack.Labels

		Pack.Name = if #Labels <= 3 then table.concat(Labels, "And") else `{Labels[1]}Through{Labels[#Labels]}`
	end
end

-- Emits the loader that requires the variant file for a first-operand value on first use and caches its maker.
const function EmitLoader(Family: Family, MakerType: string)
	const First = Family.Operands[1]
	const Block = BlockSizeOf(Family)

	const function RequireOf(Low: number): string
		const Label = BlockLabel(Family, Low * Block)
		const Pack = PackOf[Label]
		const Field = if #Pack.Labels == 1 then "" else `.Make{Label}`

		return `require("./Variants/{Pack.Module}/{Pack.Name}"){Field}`
	end

	const function EmitRequires(Indent: string, Count: number)
		for Low = 0, Count - 1 do
			const Keyword = if Low == 0 then "if" else "elseif"

			if Low == Count - 1 then
				Push(`{Indent}else`)
			else
				Push(`{Indent}{Keyword} Index == {Low} then`)
			end

			Push(`{Indent}\tMaker = {RequireOf(Low)}`)
		end

		Push(`{Indent}end`)
	end

	--// a family with a single variant file caches one maker; otherwise makers are cached per first-operand block
	if Block >= First.Range then
		Push(`local {Family.Name}Maker: ({MakerType})? = nil`)
		Push("")
		Push(`const function Load{Family.Name}(): {MakerType}`)
		Push(`\tconst Maker = {Family.Name}Maker or {RequireOf(0)}`)
		Push("")
		Push(`\t{Family.Name}Maker = Maker`)
		Push("")
		Push("\treturn Maker")
		Push("end")
		Push("")

		return
	end

	Push(`const {Family.Name}Variants: \{ [number]: {MakerType} } = \{}`)
	Push("")
	Push(`const function Load{Family.Name}({First.Name}: number): {MakerType}`)
	Push(`\tconst Index = {First.Name} // {Block}`)
	Push(`\tlocal Maker = {Family.Name}Variants[Index]`)
	Push("")
	Push("\tif Maker == nil then")
	EmitRequires("\t\t", (First.Range + Block - 1) // Block)
	Push("")
	Push(`\t\t{Family.Name}Variants[Index] = Maker`)
	Push("\tend")
	Push("")
	Push("\treturn Maker")
	Push("end")
	Push("")
end

const function EmitFamily(Family: Family)
	const Arguments = ArgumentsOf(Family)
	const Names: { string } = { "Mode" }
	const Guards: { string } = {}
	local Baked = #Family.Operands > 0

	for _, Operand in Family.Operands do
		table.insert(Names, Operand.Name)
		table.insert(Guards, `{Operand.Name} < {Operand.Range}`)

		if Operand.Range == 0 then
			Baked = false
		end
	end

	for _, Parameter in Family.Params do
		table.insert(Names, Parameter.Name)
	end

	if Family.Successors >= 1 then
		table.insert(Names, "OnNext")
		table.insert(Names, "OnTarget")
	end

	for _, Pair in Family.Distinct do
		table.insert(Guards, `{Pair[1]} ~= {Pair[2]}`)
	end

	if Baked then
		EmitLoader(Family, `({table.concat(Arguments, ", ")}) -> (Handler, Linker)`)
	end

	Push(`-- {Sentence(RenderDoc(Family, nil))}.`)

	if Baked then
		Push(`-- Baked copies ({RangesOf(Family, nil)}) load from Variants/{Family.Module} on first use; other operands run the generic copy below.`)
	end

	Push(`const function Make{Family.Name}({table.concat(Arguments, ", ")}): (Handler, Linker)`)

	--// the mode is only checked when some possible mode has no baked copy
	if Family.Successors >= 1 then
		const BakedModes = BakedModesOf(Family)
		const Accepted: { string } = {}
		local Covered = true

		for _, Mode in PossibleModesOf(Family) do
			Covered = Covered and table.find(BakedModes, Mode) ~= nil
		end

		for _, Mode in BakedModes do
			table.insert(Accepted, `Mode == {Mode}`)
		end

		if not Covered then
			table.insert(Guards, 1, if #Accepted == 1 then Accepted[1] else `({table.concat(Accepted, " or ")})`)
		end
	end

	if Baked then
		const Single = BlockSizeOf(Family) >= Family.Operands[1].Range

		Push(`\tif {table.concat(Guards, " and ")} then`)
		Push(`\t\treturn Load{Family.Name}({if Single then "" else Family.Operands[1].Name})({table.concat(Names, ", ")})`)
		Push("\tend")
		Push("")
	end

	EmitLinkage(
		Family,
		Collect(function()
			const Generic = table.concat(Expand(Family, nil, 0), "\n")
			local Declared = false

			for _, Operand in Family.Operands do
				const Name = if Operand.Kind == "Register" then `Slot{Operand.Name}` else `Index{Operand.Name}`

				if string.find(Generic, Name, 1, true) ~= nil then
					Push(if Operand.Kind == "Register" then `\tconst {Name} = {Operand.Name} + RegisterBase + 1` else `\tconst {Name} = {Operand.Name} + 1`)
					Declared = true
				end
			end

			if Declared then
				Push("")
			end

			EmitModes(Family, "\t", nil)
		end)
	)
	Push("end")
	Push("")
end

--// Handler families

for _, Spec in { { "Add", "+", HotTripleRange }, { "Sub", "-", HotTripleRange }, { "Mul", "*", HotTripleRange }, { "Div", "/", ColdTripleRange }, { "Mod", "%", ColdTripleRange }, { "Pow", "^", ColdTripleRange }, { "IDiv", "//", ColdTripleRange } } do
	const Range = Spec[3] :: number

	Define(Spec[1] :: string, `\{A} = \{B} {Spec[2]} \{C}`, { Register("A", Range), Register("B", Range), Register("C", Range) }, {}, 1, `\{A} = \{B} {Spec[2]} \{C}\n\n\{Next}`)
end

for _, Spec in { { "AddK", "+" }, { "SubK", "-" }, { "MulK", "*" }, { "DivK", "/" }, { "ModK", "%" }, { "IDivK", "//" } } do
	Define(Spec[1], `\{A} = \{B} {Spec[2]} K`, { Register("A", PairRange), Register("B", PairRange) }, { Param("K", "any") }, 1, `\{A} = \{B} {Spec[2]} K\n\n\{Next}`)
end

for _, Spec in { { "SubRK", "-" }, { "DivRK", "/" } } do
	Define(Spec[1], `\{A} = K {Spec[2]} \{C}`, { Register("A", ColdPairRange), Register("C", ColdPairRange) }, { Param("K", "any") }, 1, `\{A} = K {Spec[2]} \{C}\n\n\{Next}`)
end

Define(
	"PowK",
	"{A} = {B} ^ K",
	{ Register("A", ColdPairRange), Register("B", ColdPairRange) },
	{ Param("K", "any") },
	1,
	[=[
const Base = {B}

--// pow is slow, so the reference VM specializes ^2, ^0.5 and ^3 for numbers; results differ in the last digits
if Type(Base) ~= "number" then
	{A} = Base ^ K
elseif K == 2 then
	{A} = Base * Base
elseif K == 0.5 then
	{A} = MathSqrt(Base)
elseif K == 3 then
	{A} = Base * Base * Base
else
	{A} = Base ^ K
end

{Next}]=]
)

Define("And", "{A} = {B} and {C}", { Register("A", ColdTripleRange), Register("B", ColdTripleRange), Register("C", ColdTripleRange) }, {}, 1, "{A} = {B} and {C}\n\n{Next}", nil, { { "B", "C" } })
Define("Or", "{A} = {B} or {C}", { Register("A", ColdTripleRange), Register("B", ColdTripleRange), Register("C", ColdTripleRange) }, {}, 1, "{A} = {B} or {C}\n\n{Next}", nil, { { "B", "C" } })
Define("AndK", "{A} = {B} and K", { Register("A", ColdPairRange), Register("B", ColdPairRange) }, { Param("K", "any") }, 1, "{A} = {B} and K\n\n{Next}")
Define("OrK", "{A} = {B} or K", { Register("A", ColdPairRange), Register("B", ColdPairRange) }, { Param("K", "any") }, 1, "{A} = {B} or K\n\n{Next}")
Define("Not", "{A} = not {B}", { Register("A", ColdPairRange), Register("B", ColdPairRange) }, {}, 1, "{A} = not {B}\n\n{Next}")
Define("Minus", "{A} = -{B}", { Register("A", PairRange), Register("B", PairRange) }, {}, 1, "{A} = -{B}\n\n{Next}")
Define("Length", "{A} = #{B}", { Register("A", PairRange), Register("B", PairRange) }, {}, 1, "{A} = #{B}\n\n{Next}")
-- One host CONCAT over the whole range, so concatenation and __concat behave exactly like the reference VM.
Define("Concat2", "{A} = {B} .. {B+1}", { Register("A", ColdPairRange), Register("B", ColdPairRange) }, {}, 1, "{A} = {B} .. {B+1}\n\n{Next}")
Define("Concat3", "{A} = {B} .. {B+1} .. {B+2}", { Register("A", ColdPairRange), Register("B", ColdPairRange) }, {}, 1, "{A} = {B} .. {B+1} .. {B+2}\n\n{Next}")

Define(
	"ConcatN",
	"{A} = {B} .. ... .. {C}",
	{ Register("A", 0), Register("B", 0), Register("C", 0) },
	{},
	1,
	[=[
local Result = {C}

for Index = {#C} - 1, {#B}, -1 do
	Result = Stack[Index] .. Result
end

{A} = Result

{Next}]=]
)

Define("Move", "{A} = {B}", { Register("A", PairRange), Register("B", PairRange) }, {}, 1, "{A} = {B}\n\n{Next}", nil, { { "A", "B" } })
Define("LoadK", "{A} = K", { Register("A", SingleRange) }, { Param("K", "any") }, 1, "{A} = K\n\n{Next}")
Define("LoadNil", "{A} = nil", { Register("A", SingleRange) }, {}, 1, "{A} = nil\n\n{Next}")
Define("LoadSkip", "{A} = K, then jump (LOADB with a jump, linked as the next handler)", { Register("A", SingleRange) }, { Param("K", "any") }, 1, "{A} = K\n\n{Next}")
Define("GetGlobal", "{A} = Env[K]", { Register("A", SingleRange) }, { Param("K", "any"), Param("Env", "Store") }, 1, "{A} = Env[K]\n\n{Next}")
Define("SetGlobal", "Env[K] = {A}", { Register("A", SingleRange) }, { Param("K", "any"), Param("Env", "Store") }, 1, "Env[K] = {A}\n\n{Next}")

Define(
	"GetImportSlow",
	"{A} = the import Import (up to three names from Env), looked up on every run",
	{ Register("A", 0) },
	{ Param("Import", "{ any }"), Param("Env", "Store") },
	1,
	[=[
const Count = Import[1]
local Result = Env[Import[2]]

if Count >= 2 then
	Result = Result[Import[3]]

	if Count >= 3 then
		Result = Result[Import[4]]
	end
end

{A} = Result

{Next}]=]
)

Define("GetUpvalValue", "{A} = {B}, an upvalue captured by value", { Register("A", PairRange), Upvalue("B", UpvalueRange) }, {}, 1, "{A} = {B}\n\n{Next}")
Define("GetUpval", "{A} = {B}, an upvalue captured by reference", { Register("A", PairRange), Upvalue("B", UpvalueRange) }, {}, 1, "const Captured = {B}\n\n{A} = Captured[1][Captured[2]]\n\n{Next}")
Define("SetUpval", "{B} = {A}", { Register("A", PairRange), Upvalue("B", UpvalueRange) }, {}, 1, "const Captured = {B}\n\nCaptured[1][Captured[2]] = {A}\n\n{Next}")

Define(
	"CloseUpvals",
	"close the open upvalues of {A} and above",
	{ Register("A", 0) },
	{},
	1,
	[=[
const Pending: { [number]: Upvalue }? = Stack[4]

if Pending ~= nil then
	for Index, Captured in Pending do
		if Index >= {#A} then
			CloseUpvalue(Captured)
			Pending[Index] = nil
		end
	end
end

{Next}]=]
)

Define("GetTable", "{A} = {B}[{C}]", { Register("A", HotTripleRange), Register("B", HotTripleRange), Register("C", HotTripleRange) }, {}, 1, "{A} = {B}[{C}]\n\n{Next}")
Define("SetTable", "{B}[{C}] = {A}", { Register("A", HotTripleRange), Register("B", HotTripleRange), Register("C", HotTripleRange) }, {}, 1, "{B}[{C}] = {A}\n\n{Next}")
Define("GetTableKS", "{A} = {B}[K]", { Register("A", PairRange), Register("B", PairRange) }, { Param("K", "any") }, 1, "{A} = {B}[K]\n\n{Next}")
Define("SetTableKS", "{B}[K] = {A}", { Register("A", PairRange), Register("B", PairRange) }, { Param("K", "any") }, 1, "{B}[K] = {A}\n\n{Next}")
Define("GetTableN", "{A} = {B}[Index]", { Register("A", PairRange), Register("B", PairRange) }, { Param("Index", "number") }, 1, "{A} = {B}[Index]\n\n{Next}")
Define("SetTableN", "{B}[Index] = {A}", { Register("A", ColdPairRange), Register("B", ColdPairRange) }, { Param("Index", "number") }, 1, "{B}[Index] = {A}\n\n{Next}")
Define("NewClassMember", "{A}[K] = {C}", { Register("A", 0), Register("C", 0) }, { Param("K", "any") }, 1, "{A}[K] = {C}\n\n{Next}")

Define(
	"NameCall",
	"{A+1} = {B}, {A} = {B}[Method]",
	{ Register("A", PairRange), Register("B", PairRange) },
	{ Param("Method", "any") },
	1,
	[=[
const Object = {B}
const Found = Object[Method]

if Found == nil then
	Error(`attempt to call missing method '{Method}' of {Typeof(Object)}`)
end

{A+1} = Object
{A} = Found

{Next}]=]
)

Define("NewTableEmpty", "{A} = {}", { Register("A", SingleRange) }, {}, 1, "{A} = {}\n\n{Next}")
Define("NewTable", "{A} = a table with Size preallocated array slots", { Register("A", SingleRange) }, { Param("Size", "number") }, 1, "{A} = TableCreate(Size)\n\n{Next}")
Define("DupTable", "{A} = a copy of the constant table Template", { Register("A", SingleRange) }, { Param("Template", "Store") }, 1, "{A} = TableClone(Template)\n\n{Next}")

Define(
	"SetList",
	"{A}[Start], ... = {B}, ...: Size - 1 values, or every value up to top when Size is 0",
	{ Register("A", 0), Register("B", 0) },
	{ Param("Size", "number"), Param("Start", "number") },
	1,
	[=[
const Count = if Size == 0 then Stack[5] - {#B} + 1 else Size - 1

TableMove(Stack, {#B}, {#B} + Count - 1, Start, {A})

{Next}]=]
)

Define("Jump", "jump to the next handler", {}, {}, 1, "{Next}")
Define("JumpIf", "if {A} then jump", { Register("A", SingleRange) }, {}, 2, "if {A} then\n\t{Target}\nend\n\n{Next}")
Define("JumpIfNot", "if not {A} then jump", { Register("A", SingleRange) }, {}, 2, "if {A} then\n\t{Next}\nend\n\n{Target}")

for _, Spec in { { "JumpIfEq", "==", "Target", "Next" }, { "JumpIfLe", "<=", "Target", "Next" }, { "JumpIfLt", "<", "Target", "Next" }, { "JumpIfNotEq", "~=", "Target", "Next" }, { "JumpIfNotLe", "<=", "Next", "Target" }, { "JumpIfNotLt", "<", "Next", "Target" } } do
	const Condition = if Spec[3] == "Target" then `\{A} {Spec[2]} \{X}` else `not (\{A} {Spec[2]} \{X})`

	Define(Spec[1], `if {Condition} then jump`, { Register("A", PairRange), Register("X", PairRange) }, {}, 2, `if \{A} {Spec[2]} \{X} then\n\t\{{Spec[3]}}\nend\n\n\{{Spec[4]}}`, nil, { { "A", "X" } })
end

Define("JumpIfK", "if {A} == K then jump", { Register("A", SingleRange) }, { Param("K", "any") }, 2, "if {A} == K then\n\t{Target}\nend\n\n{Next}")
Define("JumpIfNotK", "if {A} ~= K then jump", { Register("A", SingleRange) }, { Param("K", "any") }, 2, "if {A} == K then\n\t{Next}\nend\n\n{Target}")
Define("JumpIfNil", "if {A} == nil then jump", { Register("A", SingleRange) }, {}, 2, "if {A} == nil then\n\t{Target}\nend\n\n{Next}")
Define("JumpIfNotNil", "if {A} ~= nil then jump", { Register("A", SingleRange) }, {}, 2, "if {A} == nil then\n\t{Next}\nend\n\n{Target}")

Define(
	"ForNPrep",
	"numeric for setup over limit {A}, step {A+1} and index {A+2}: jump past the loop when it runs zero times",
	{ Register("A", SingleRange) },
	{},
	2,
	[=[
local Limit = {A}
local Step = {A+1}
local Index = {A+2}

if Type(Index) ~= "number" then
	Index = Tonumber(Index)

	if Index == nil then
		Error(`invalid 'for' initial value (number expected, got {Type({A+2})})`)
	end

	{A+2} = Index
end

if Type(Limit) ~= "number" then
	Limit = Tonumber(Limit)

	if Limit == nil then
		Error(`invalid 'for' limit (number expected, got {Type({A})})`)
	end

	{A} = Limit
end

if Type(Step) ~= "number" then
	Step = Tonumber(Step)

	if Step == nil then
		Error(`invalid 'for' step (number expected, got {Type({A+1})})`)
	end

	{A+1} = Step
end

if Step > 0 then
	if Index <= Limit then
		{Next}
	end
elseif Limit <= Index then
	{Next}
end

{Target}]=]
)

Define(
	"ForNLoop",
	"{A+2} += {A+1}, then jump back while {A+2} is within limit {A}",
	{ Register("A", SingleRange) },
	{},
	2,
	[=[
const Step = {A+1}
const Index = {A+2} + Step

{A+2} = Index

if Step > 0 then
	if Index <= {A} then
		{Target}
	end
elseif {A} <= Index then
	{Target}
end

{Next}]=]
)

Define(
	"ForNLoopStepOne",
	"{A+2} += 1, then jump back while {A+2} <= {A}",
	{ Register("A", SingleRange) },
	{},
	2,
	[=[
const Index = {A+2} + 1

{A+2} = Index

if Index <= {A} then
	{Target}
end

{Next}]=]
)

Define(
	"ForNLoopStepOneLimit",
	"{A+2} += 1, then jump back while {A+2} <= Limit",
	{ Register("A", SingleRange) },
	{ Param("Limit", "number") },
	2,
	[=[
const Index = {A+2} + 1

{A+2} = Index

if Index <= Limit then
	{Target}
end

{Next}]=]
)

Define(
	"ForGPrep",
	"generic for setup over {A}: functions run as is, tables iterate by __iter or next",
	{ Register("A", 0) },
	{ Param("Strict", "boolean") },
	1,
	[=[
const Iterator = {A}
const Kind = Type(Iterator)

if Kind == "function" then
	{Next}
end

if Strict then
	Error(`attempt to iterate over a {Kind} value`)
end

if Kind == "table" or Kind == "userdata" then
	const Meta = Getmetatable(Iterator) :: any
	const IterFunction = if Type(Meta) == "table" then Rawget(Meta, "__iter") else nil

	if IterFunction ~= nil then
		const Generator, State, Control = (IterFunction :: (any) -> (any, any, any))(Iterator)

		if Generator == nil then
			Error("attempt to call a nil value")
		end

		{A} = Generator
		{A+1} = State
		{A+2} = Control
	elseif Type(Meta) ~= "table" or Rawget(Meta, "__call") == nil then
		if Kind == "userdata" then
			Error(`attempt to iterate over a {Typeof(Iterator)} value`)
		end

		{A} = Next
		{A+1} = Iterator
		{A+2} = nil
	end
else
	Error(`attempt to iterate over a {Typeof(Iterator)} value`)
end

{Next}]=]
)

Define(
	"ForGPrepInext",
	"ipairs for setup over {A}: a verified ipairs over a plain table steps inline",
	{ Register("A", 0) },
	{},
	1,
	[=[
const Iterator = {A}

--// like the reference VM's ipairs fast path, a verified ipairs loop over a table is marked for inline stepping
if Iterator == Inext and Type({A+1}) == "table" and Getmetatable({A+1}) == nil and {A+2} == 0 then
	{A} = IpairsStep

	{Next}
elseif Type(Iterator) == "function" then
	{Next}
end

Error(`attempt to iterate over a {Type(Iterator)} value`)

{Next}]=]
)

Define(
	"ForGLoopIpairs",
	"{A+3}, {A+4} = the next index and value of {A+1} after {A+2}, then jump back unless nil",
	{ Register("A", SingleRange) },
	{},
	2,
	[=[
const Iterator = {A}

if Iterator == IpairsStep then
	const Index = {A+2} + 1
	--// plain indexing equals inext's raw read on a table that had no metatable when the loop started
	const Value = {A+1}[Index]

	if Value ~= nil then
		{A+2} = Index
		{A+3} = Index
		{A+4} = Value

		{Target}
	end

	{Next}
end

const Key, Value = Iterator({A+1}, {A+2})

if Key ~= nil then
	{A+2} = Key
	{A+3} = Key
	{A+4} = Value

	{Target}
end

{Next}]=]
)

Define(
	"ForGLoop1",
	"{A+3} = {A}({A+1}, {A+2}), then jump back unless nil",
	{ Register("A", SingleRange) },
	{},
	2,
	[=[
const Value = {A}({A+1}, {A+2})

if Value ~= nil then
	{A+2} = Value
	{A+3} = Value

	{Target}
end

{Next}]=]
)

Define(
	"ForGLoop2",
	"{A+3}, {A+4} = {A}({A+1}, {A+2}), then jump back unless {A+3} is nil",
	{ Register("A", SingleRange) },
	{},
	2,
	[=[
const Key, Value = {A}({A+1}, {A+2})

if Key ~= nil then
	{A+2} = Key
	{A+3} = Key
	{A+4} = Value

	{Target}
end

{Next}]=]
)

Define(
	"ForGLoopN",
	"{A+3}, ... = Count values of {A}({A+1}, {A+2}), then jump back unless {A+3} is nil",
	{ Register("A", 0) },
	{ Param("Count", "number") },
	2,
	[=[
const Values = TablePack({A}({A+1}, {A+2}))

TableMove(Values, 1, Count, {#A+3}, Stack)

if {A+3} ~= nil then
	{A+2} = {A+3}

	{Target}
end

{Next}]=]
)

-- Documents a call that keeps Results values ("0" to "3", or "Many") from Call.
const function CallDoc(Call: string, Results: string): string
	if Results == "0" then
		return Call
	elseif Results == "1" then
		return `\{A} = {Call}`
	elseif Results == "2" then
		return `\{A}, \{A+1} = {Call}`
	elseif Results == "3" then
		return `\{A}, \{A+1}, \{A+2} = {Call}`
	end

	return `\{A}, ... = {Call}, keeping every result and setting top`
end

do
	const ResultNames = { "0", "1", "2", "3", "Many" }

	const function CallStatement(Arguments: string, Results: string): string
		if Results == "0" then
			return `\{A}({Arguments})`
		elseif Results == "1" then
			return `\{A} = \{A}({Arguments})`
		elseif Results == "2" then
			return `\{A}, \{A+1} = \{A}({Arguments})`
		elseif Results == "3" then
			return `\{A}, \{A+1}, \{A+2} = \{A}({Arguments})`
		end

		return `Spread(Stack, \{#A}, \{A}({Arguments}))`
	end

	for Count = 0, MaxCallArgs do
		const Arguments: { string } = {}

		for Index = 1, Count do
			table.insert(Arguments, `\{A+{Index}}`)
		end

		for _, Results in ResultNames do
			Define(`Call{Count}x{Results}`, CallDoc(`\{A}({table.concat(Arguments, ", ")})`, Results), { Register("A", CallRange) }, {}, 1, `{CallStatement(table.concat(Arguments, ", "), Results)}\n\n\{Next}`)
		end
	end

	for _, Results in ResultNames do
		Define(`CallTopx{Results}`, CallDoc("{A}({A+1}, ..., top)", Results), { Register("A", CallTopRange) }, {}, 1, `{CallStatement("TableUnpack(Stack, {#A+1}, Stack[5])", Results)}\n\n\{Next}`)
	end
end

Define(
	"CallN",
	"{A}, ... = {A}({A+1}, ...): B - 1 arguments, or up to top when B is 0; C - 1 results, or all of them (setting top) when C is 0",
	{ Register("A", 0) },
	{ Param("B", "number"), Param("C", "number") },
	1,
	[=[
const Params = if B == 0 then Stack[5] - {#A} else B - 1
const Results = TablePack({A}(TableUnpack(Stack, {#A+1}, {#A} + Params)))
local ResultCount = Results.n

if C == 0 then
	Stack[5] = {#A} + ResultCount - 1
else
	ResultCount = C - 1
end

TableMove(Results, 1, ResultCount, {#A}, Stack)

{Next}]=]
)

Define("ReturnNone", "return", {}, {}, 0, "return nil")
Define("ReturnOne", "return {A}", { Register("A", SingleRange) }, {}, 0, "Stack[1] = {A}\n\nreturn nil")
Define("ReturnTwo", "return {A}, {A+1}", { Register("A", SingleRange) }, {}, 0, "Stack[1] = {A}\nStack[2] = {A+1}\n\nreturn nil")
Define("Return0", "return, storing result kind 0", {}, {}, 0, "Stack[3] = 0\n\nreturn nil")
Define("Return1", "return {A}, storing result kind 1", { Register("A", SingleRange) }, {}, 0, "Stack[1] = {A}\nStack[3] = 1\n\nreturn nil")
Define("Return2", "return {A}, {A+1}, storing result kind 2", { Register("A", SingleRange) }, {}, 0, "Stack[1] = {A}\nStack[2] = {A+1}\nStack[3] = 2\n\nreturn nil")

Define(
	"ReturnRange",
	"return {A}, ...: B - 1 values, or every value up to top when B is 0",
	{ Register("A", 0) },
	{ Param("B", "number") },
	0,
	[=[
Stack[2] = if B == 0 then Stack[5] else {#A} + B - 2
Stack[1] = {#A}
Stack[3] = 3

return nil]=]
)

Define("GetVarargs1", "{A} = the first vararg", { Register("A", SingleRange) }, {}, 1, "{A} = Stack[2][1]\n\n{Next}")
Define("GetVarargs2", "{A}, {A+1} = the first two varargs", { Register("A", SingleRange) }, {}, 1, "const Varargs = Stack[2]\n\n{A} = Varargs[1]\n{A+1} = Varargs[2]\n\n{Next}")
Define("GetVarargsN", "{A}, ... = the first Count varargs", { Register("A", 0) }, { Param("Count", "number") }, 1, "TableMove(Stack[2], 1, Count, {#A}, Stack)\n\n{Next}")

Define(
	"GetVarargsMulti",
	"{A}, ... = every vararg, setting top",
	{ Register("A", 0) },
	{},
	1,
	[=[
const Count = Stack[3]

Stack[5] = {#A} + Count - 1
TableMove(Stack[2], 1, Count, {#A}, Stack)

{Next}]=]
)

Define(
	"NewClosure",
	"{A} = a new closure of Description[1], capturing upvalues as the rest of Description lists",
	{ Register("A", 0) },
	{ Param("Description", "{ any }") },
	1,
	[=[
const Child: Proto = Description[1]
const Inherited = Stack[1]
const Upvalues: { any } = {}

{A} = Child.Make(Upvalues)

for Index = 1, Child.UpvalueCount do
	const Kind = Description[Index * 2]
	const Slot = Description[Index * 2 + 1]

	if Kind == 0 then --// value
		Upvalues[Index] = Stack[Slot]
	elseif Kind == 1 then --// reference
		Upvalues[Index] = Capture(Stack, Slot)
	else --// upvalue
		Upvalues[Index] = Inherited[Slot]
	end
end

{Next}]=]
)

Define(
	"DupClosure",
	"{A} = a closure of Description[1], reusing the cached one while its captured values are unchanged",
	{ Register("A", 0) },
	{ Param("Description", "{ any }") },
	1,
	[=[
const Child: Proto = Description[1]
const Inherited = Stack[1]
local CanReuse = Cached ~= nil

if Cached then
	--// the cached closure is saved first because it may capture itself by value
	{A} = Cached.Closure

	for Index = 1, Child.UpvalueCount do
		const Kind = Description[Index * 2]
		const Slot = Description[Index * 2 + 1]
		const Previous = Cached.Upvalues[Index]

		if Kind == 0 then --// value capture
			if not Rawequal(Previous, Stack[Slot]) then
				CanReuse = false

				break
			end
		elseif not Rawequal(Previous, Inherited[Slot]) then --// upvalue capture
			CanReuse = false

			break
		end
	end
end

if not CanReuse then
	const Upvalues: { any } = {}
	const Closure = Child.Make(Upvalues)

	{A} = Closure

	for Index = 1, Child.UpvalueCount do
		const Kind = Description[Index * 2]
		const Slot = Description[Index * 2 + 1]

		if Kind == 0 then --// value
			Upvalues[Index] = Stack[Slot]
		else --// upvalue; references are not handled by DUPCLOSURE
			Upvalues[Index] = Inherited[Slot]
		end
	end

	if Cached == nil then
		Cached = { Closure = Closure, Upvalues = Upvalues }
	end
end

{Next}]=],
	{ "local Cached: Cached? = nil" }
)

Define("Unsupported", "raise an error for Opcode, which this VM does not support", {}, { Param("Opcode", "number") }, 0, "Error(`Unsupported Opcode: {Opcode}`)\n\nreturn nil")

-- NEWCLOSURE for up to three captures, one family per capture-kind string (V by value, R by reference, U inherited upvalue), so
-- the upvalue table is filled without reading the capture description at run time.
do
	const Shapes: { string } = { "" }

	for Length = 1, 3 do
		for _, Shape in table.clone(Shapes) do
			if #Shape == Length - 1 then
				for _, Kind in { "V", "R", "U" } do
					table.insert(Shapes, `{Shape}{Kind}`)
				end
			end
		end
	end

	for _, Shape in Shapes do
		const Params: { Param } = { Param("Child", "Proto") }
		const Captures: { string } = {}
		const Lines: { string } = {}

		if Shape == "" then
			table.insert(Lines, "{A} = Child.Make(NoUpvalues)")
		else
			table.insert(Lines, `const Upvalues: \{ any } = TableCreate({#Shape})`)
			table.insert(Lines, "")
			table.insert(Lines, "{A} = Child.Make(Upvalues)")
		end

		for Index = 1, #Shape do
			const Kind = string.sub(Shape, Index, Index)
			const Source = if Kind == "V" then `Stack[Slot{Index}]` elseif Kind == "R" then `Capture(Stack, Slot{Index})` else `Stack[1][Slot{Index}]`

			table.insert(Captures, if Kind == "V" then `Stack[Slot{Index}] by value` elseif Kind == "R" then `Stack[Slot{Index}] by reference` else `inherited upvalue Slot{Index}`)
			table.insert(Lines, `Upvalues[{Index}] = {Source}`)
		end

		table.insert(Lines, "")
		table.insert(Lines, "{Next}")

		--// every shape takes three slots, so the decoder passes the successors in the same position whatever the shape
		for Index = 1, 3 do
			table.insert(Params, Param(`Slot{Index}`, "number"))
		end

		const Doc = if Shape == "" then "{A} = a new closure of Child, capturing nothing" else `\{A} = a new closure of Child, capturing {table.concat(Captures, ", ")}`

		Define(`NewClosureWith{if Shape == "" then "None" else Shape}`, Doc, { Register("A", 0) }, Params, 1, table.concat(Lines, "\n"))
	end
end

-- A call the decoder proved reaches a builtin (its function register was just loaded by an import that resolved to it): the
-- handler calls the builtin through a library alias, which the host compiles to its own fast builtin call.
do
	const Defined: { [string]: boolean } = {}

	for _, Hinted in Builtins do
		for _, Expression in Hinted.Expressions do
			for _, Count in Hinted.Arities do
				const Arguments: { string } = {}

				for Index = 1, Count do
					table.insert(Arguments, `\{A+{Index}}`)
				end

				for Results = 0, if Hinted.Returns then 1 else 0 do
					const Name = FastName(Expression, Count, Results)
					const Call = `{AliasOf(Expression)}({table.concat(Arguments, ", ")})`

					if not Defined[Name] then
						Defined[Name] = true
						FastModules[Name] = Hinted.Module
						Define(Name, `{if Results == 1 then "{A} = " else ""}{Expression}({table.concat(Arguments, ", ")}), a proven builtin call`, { Register("A", 0) }, {}, 1, `{if Results == 1 then "\{A} = " else ""}{Call}\n\n\{Next}`)
					end
				end
			end
		end
	end
end

-- A NAMECALL fused with the CALL right after it: the method is looked up and called with the object as its first argument.
for Count = 0, MaxMethodArgs do
	const Arguments: { string } = { "Object" }

	for Index = 1, Count do
		table.insert(Arguments, `\{A+{Index + 1}}`)
	end

	const List = table.concat(Arguments, ", ")
	const Passed = table.concat(Arguments, ", ", 2)

	for _, Results in { "0", "1", "2", "3", "Many" } do
		const Statement = if Results == "0"
			then `Found({List})`
			elseif Results == "1" then `\{A} = Found({List})`
			elseif Results == "2" then `\{A}, \{A+1} = Found({List})`
			elseif Results == "3" then `\{A}, \{A+1}, \{A+2} = Found({List})`
			else `Spread(Stack, \{#A}, Found({List}))`

		Define(
			`Method{Count}x{Results}`,
			CallDoc(`\{B}:Method({Passed})`, Results),
			{ Register("A", PairRange), Register("B", PairRange) },
			{ Param("Method", "any") },
			1,
			`const Object = \{B}\nconst Found = Object[Method]\n\nif Found == nil then\n\tError(\`attempt to call missing method '\{Method}' of \{Typeof(Object)}\`)\nend\n\n{Statement}\n\n\{Next}`
		)
	end
end

--// Entry closures

const ShapeNames = { "no values", "one value", "two values", "any results" }

-- Emits a closure factory: it takes a closure's upvalues and returns the host function (the Entry) for that closure.
const function EmitEntry(Indent: string, Params: number?, Vararg: boolean, Open: boolean, Shape: number)
	const Inner = `{Indent}\t\t`
	const Arguments: { string } = {}

	if Params ~= nil then
		for Index = 1, Params do
			table.insert(Arguments, `P{Index}: any`)
		end
	end

	if Vararg or Params == nil then
		table.insert(Arguments, "...: any")
	end

	Push(`{Indent}return function(Upvalues: \{ any }): (...any) -> ...any`)
	Push(`{Indent}\treturn function({table.concat(Arguments, ", ")}): ...any`)

	if Params == nil then
		Push(`{Inner}const Passed = \{ ... }`)
	end

	if Vararg then
		Push(`{Inner}const Count = Select("#", ...)`)
	end

	Push(`{Inner}local Stack: Registers`)
	Push(`{Inner}const Cached = Spare`)
	Push(`{Inner}const Pooled = Head`)
	Push("")
	Push(`{Inner}if Cached ~= nil then`)
	Push(`{Inner}\tStack = Cached`)
	Push(`{Inner}\tSpare = nil`)
	Push(`{Inner}elseif Pooled ~= nil then`)
	Push(`{Inner}\tStack = Pooled`)
	Push(`{Inner}\tHead = Pooled[5]`)
	Push(`{Inner}else`)
	Push(`{Inner}\tStack = TableCreate(MaxStack) :: Registers`)

	if not Vararg then
		Push(`{Inner}\tStack[2] = EmptyVarargs`)
	end

	Push(`{Inner}end`)
	Push("")
	Push(`{Inner}Stack[1] = Upvalues`)

	if Params == nil then
		Push(`{Inner}TableMove(Passed, 1, Params, RegisterBase + 1, Stack)`)

		if Vararg then
			Push("")
			Push(`{Inner}if Count > Params then`)
			Push(`{Inner}\tStack[2] = TableMove(Passed, Params + 1, Count, 1, \{})`)
			Push(`{Inner}\tStack[3] = Count - Params`)
			Push(`{Inner}else`)
			Push(`{Inner}\tStack[2] = EmptyVarargs`)
			Push(`{Inner}\tStack[3] = 0`)
			Push(`{Inner}end`)
		end
	else
		if Vararg then
			Push(`{Inner}Stack[2] = if Count == 0 then EmptyVarargs else \{ ... }`)
			Push(`{Inner}Stack[3] = Count`)
		end

		for Index = 1, Params do
			Push(`{Inner}Stack[{Index + 5}] = P{Index}`)
		end
	end

	Push("")
	Push(`{Inner}local Fn = First(Stack)`)
	Push("")
	Push(`{Inner}while Fn do`)
	Push(`{Inner}\tFn = Fn(Stack)`)
	Push(`{Inner}end`)
	Push("")

	if Open then
		Push(`{Inner}const Pending: \{ [number]: Upvalue }? = Stack[4]`)
		Push("")
		Push(`{Inner}if Pending ~= nil then`)
		Push(`{Inner}\tfor _, Captured in Pending do`)
		Push(`{Inner}\t\tCloseUpvalue(Captured)`)
		Push(`{Inner}\tend`)
		Push("")
		Push(`{Inner}\tStack[4] = nil`)
		Push(`{Inner}end`)
		Push("")
	end

	Push(`{Inner}if Spare == nil then`)
	Push(`{Inner}\tSpare = Stack`)
	Push(`{Inner}else`)
	Push(`{Inner}\tStack[5] = Head`)
	Push(`{Inner}\tHead = Stack`)
	Push(`{Inner}end`)

	if Shape == 1 then
		Push("")
		Push(`{Inner}return Stack[1]`)
	elseif Shape == 2 then
		Push("")
		Push(`{Inner}return Stack[1], Stack[2]`)
	elseif Shape == 3 then
		Push("")
		Push(`{Inner}const Kind = Stack[3]`)
		Push("")
		Push(`{Inner}if Kind == 1 then`)
		Push(`{Inner}\treturn Stack[1]`)
		Push(`{Inner}elseif Kind == 0 then`)
		Push(`{Inner}\treturn`)
		Push(`{Inner}elseif Kind == 2 then`)
		Push(`{Inner}\treturn Stack[1], Stack[2]`)
		Push(`{Inner}end`)
		Push("")
		Push(`{Inner}return TableUnpack(Stack, Stack[1], Stack[2])`)
	end

	Push(`{Indent}\tend`)
	Push(`{Indent}end`)
end

const function EmitShapes(Indent: string, Params: number?, Vararg: boolean)
	Push(`{Indent}if Open then`)

	for _, Open in { true, false } do
		const Inner = `{Indent}\t`

		if not Open then
			Push(`{Indent}else`)
		end

		for Shape = 0, 2 do
			Push(`{Inner}{if Shape == 0 then "if" else "elseif"} Shape == {Shape} then --// {ShapeNames[Shape + 1]}`)
			EmitEntry(`{Inner}\t`, Params, Vararg, Open, Shape)
		end

		Push(`{Inner}end`)
		Push("")
		EmitEntry(Inner, Params, Vararg, Open, 3)
	end

	Push(`{Indent}end`)
end

const function EmitMakeFactory()
	Push("-- Creates the closure factory of a decoded proto. Its Entry body is specialized by parameter count, varargs, open upvalues and")
	Push("-- return shape. Every closure of the proto shares one spare register file plus, for recursion, a free list linked through slot [5].")
	Push("const function MakeFactory(Proto: Proto): Factory")
	Push("\tconst MaxStack = Proto.MaxStackSize")
	Push("\tconst Params = Proto.ParamCount")
	Push("\tconst First = Proto.First")
	Push("\tconst Shape = Proto.Shape")
	Push("\tconst Open = Proto.Open")
	Push("\tlocal Spare: Registers? = nil")
	Push("\tlocal Head: Registers? = nil")
	Push("")

	for _, Vararg in { true, false } do
		Push(`\t{if Vararg then "if" else "else"}{if Vararg then " Proto.IsVararg then" else ""}`)

		for Params = 0, MaxEntryParams do
			Push(`\t\t{if Params == 0 then "if" else "elseif"} Params == {Params} then`)
			EmitShapes("\t\t\t", Params, Vararg)
		end

		Push("\t\tend")
		Push("")
		EmitShapes("\t\t", nil, Vararg)
	end

	Push("\tend")
	Push("end")
	Push("")
end

const function EmitMakeCall()
	Push("-- Picks the call handler family for an argument count (B - 1, or up to top when B is 0) and a result count (C - 1, or multiple when C is 0).")
	Push("const function MakeCall(Mode: number, A: number, B: number, C: number, OnNext: Handler, OnTarget: Handler): (Handler, Linker)")

	const ResultNames = { [0] = "Many", "0", "1", "2", "3" }

	for Count = -1, MaxCallArgs do
		const Prefix = if Count == -1 then "CallTop" else `Call{Count}`

		Push(`\t{if Count == -1 then "if" else "elseif"} B == {Count + 1} then`)

		for Results = 0, 4 do
			Push(`\t\t{if Results == 0 then "if" else "elseif"} C == {Results} then`)
			const Name = `{Prefix}x{ResultNames[Results]}`

			Push(`\t\t\treturn {ModuleOf(Name)}.Make{Name}(Mode, A, OnNext, OnTarget)`)
		end

		Push("\t\tend")
	end

	Push("\tend")
	Push("")
	Push("\treturn Calls.MakeCallN(Mode, A, B, C, OnNext, OnTarget)")
	Push("end")
	Push("")
end

const function EmitMakeMethod()
	Push("-- Picks the handler for a NAMECALL fused with its CALL: Count arguments after the object, and the CALL's C (results + 1, or 0).")
	Push("const function MakeMethod(Mode: number, A: number, B: number, Method: any, Count: number, C: number, OnNext: Handler, OnTarget: Handler): (Handler, Linker)")

	const ResultNames = { [0] = "Many", "0", "1", "2", "3" }

	for Count = 0, MaxMethodArgs do
		const Opening = if Count == 0 then "if" elseif Count == MaxMethodArgs then "else" else "elseif"

		Push(if Count == MaxMethodArgs then "\telse" else `\t{Opening} Count == {Count} then`)

		for Results = 0, 4 do
			const Name = `Method{Count}x{ResultNames[Results]}`
			const Line = `\t\t\treturn {ModuleOf(Name)}.Make{Name}(Mode, A, B, Method, OnNext, OnTarget)`

			if Results == 4 then
				Push("\t\telse")
			else
				Push(`\t\t{if Results == 0 then "if" else "elseif"} C == {Results} then`)
			end

			Push(Line)
		end

		Push("\t\tend")
	end

	Push("\tend")
	Push("end")
	Push("")
end

-- Emits into init the lazy loaders of the builtin modules and BuiltinModule, which maps a FASTCALL builtin id to its module.
const function EmitBuiltinRouter()
	const Lazy: { string } = {}

	for _, Module in Modules do
		if Module.Lazy then
			table.insert(Lazy, Module.Name)
		end
	end

	for _, Name in Lazy do
		Push(`local {Name}Module: any = nil`)
	end

	Push("")

	for _, Name in Lazy do
		Push(`const function Load{Name}(): any`)
		Push(`\t{Name}Module = {Name}Module or require("@self/{Name}")`)
		Push("")
		Push(`\treturn {Name}Module`)
		Push("end")
		Push("")
	end

	Push("-- The loader of the module with the handlers for each FASTCALL builtin id; builtins without handlers are absent.")
	Push("const BuiltinLoaders: { [number]: () -> any } = {")

	for _, Hinted in Builtins do
		Push(`\t[{Hinted.Id}] = Load{Hinted.Module},`)
	end

	Push("}")
	Push("")
	Push("-- The module with the handlers for FASTCALL builtin Id (loaded on first use), or nil for builtins without handlers.")
	Push("const function BuiltinModule(Id: number): any")
	Push("\tconst Loader = BuiltinLoaders[Id]")
	Push("")
	Push("\treturn if Loader == nil then nil else Loader()")
	Push("end")
	Push("")
end

-- Emits into a builtin module Matches, which tells whether a value is the builtin with a given id and that call shape has a handler,
-- and MakeFast, which picks the
-- handler for a proven builtin call by argument and result count.
const function EmitBuiltinDispatch(ModuleName: string)
	Push("const function Matches(Id: number, Value: any, Count: number, Results: number): boolean")
	Push("\t--// a builtin missing from the host (the integer library on Roblox) proves nothing")
	Push("\tif Value == nil then")
	Push("\t\treturn false")
	Push("\tend")
	Push("")

	for _, Hinted in Builtins do
		if Hinted.Module == ModuleName then
			const Values: { string } = {}
			const Shapes: { string } = {}

			for _, Expression in Hinted.Expressions do
				table.insert(Values, `Value == {AliasOf(Expression)}`)
			end

			for _, Count in Hinted.Arities do
				table.insert(Shapes, `Count == {Count}`)
			end

			const Results = if Hinted.Returns then "Results <= 1" else "Results == 0"

			Push(`\tif Id == {Hinted.Id} then`)
			Push(`\t\treturn ({table.concat(Values, " or ")}) and ({table.concat(Shapes, " or ")}) and {Results}`)
			Push("\tend")
			Push("")
		end
	end

	Push("\treturn false")
	Push("end")
	Push("")
	Push("const function MakeFast(Mode: number, Id: number, Value: any, A: number, Count: number, Results: number, OnNext: Handler, OnTarget: Handler): (Handler?, Linker?)")

	for _, Hinted in Builtins do
		if Hinted.Module == ModuleName then
			for _, Expression in Hinted.Expressions do
				Push(`\tif Id == {Hinted.Id} and Value == {AliasOf(Expression)} then`)

				for _, Count in Hinted.Arities do
					for Results = 0, if Hinted.Returns then 1 else 0 do
						Push(`\t\tif Count == {Count} and Results == {Results} then`)
						Push(`\t\t\treturn Make{FastName(Expression, Count, Results)}(Mode, A, OnNext, OnTarget)`)
						Push("\t\tend")
						Push("")
					end
				end

				Push("\t\treturn nil, nil")
				Push("\tend")
				Push("")
			end
		end
	end

	Push("\treturn nil, nil")
	Push("end")
	Push("")
end

--// Fixed source sections

const GeneratedNote = "\tGenerated by Tools/BakeVM.luau; edit the generator, not this file."

-- How the comments of handler modules and variant files read.
const HandlerNotation = [==[


	Notation
		R(A) is register A, stored at Stack[A + 6]; U(B) is upvalue B, stored at Stack[1][B + 1]. A baked copy's comment names
		its registers by number (R0 is Stack[6]). K, Method and similar names are decode-time constants captured by the handler.
		A chained edge calls its successor directly (return OnNext(Stack)); any other edge returns the successor to the Entry
		loop. Mode bit 1 chains the fallthrough edge and bit 2 the branch edge.]==]

const InitDocumentation = [==[
	Loads Luau bytecode and runs it with a direct-threaded closure interpreter whose operands are baked into the handler code.

	Paradigm
		Each bytecode instruction is decoded once into its own handler closure. Small register numbers are not upvalues but literal
		table indexes: every handler family exists as one copy per combination of small operands, so `R6 = R7 + R8` executes as
		`Stack[12] = Stack[13] + Stack[14]`. Larger operands fall back to a generic copy that captures them as upvalues.
		Handlers are direct-threaded: a handler finishes by calling its successor (`return NextFn(Stack)`) instead of returning it to
		a dispatch loop, so straight-line code and forward branches run as one chain of host calls. Edges that could grow the host
		call stack without bound return the successor to the Entry loop instead (the trampoline): backward edges, edges into calls
		and generic-for iterations (so recursion costs two host frames per level), and edges past ChainLimit chained frames.
		Pure jumps (JUMP, JUMPX, JUMPBACK, CMPPROTO) are threaded away at decode: edges into them lead straight to their destination.

	Invariants
		Register file layout: [1] upvalues, [2] varargs, [3] vararg count / return kind, [4] open upvalues, [5] top, registers from [6].
		Return handlers store results in the register file; a proto whose returns all have the same fixed count stores no kind and
		its Entry returns that shape directly, otherwise [3] holds 0 none, 1 one value at [1], 2 two values at [1] and [2], 3 the range [1]..[2].
		Imports resolve once at load against the Env table, exactly like the reference VM does for a safe environment.

	Design Notes
		Errors propagate unwrapped with host positions; there are no hooks, no error wrapper, and no per-instruction bookkeeping.
		Close() relinks every backward edge to a handler that ends the function, so loops stop at their next iteration without any
		per-iteration check; a generic-for loop still calls its iterator once more first.
		The handler families live in sibling modules generated from one template each; this module decodes and links them.]==]

const RuntimeSource = [==[
--!optimize 2
--!strict

--[[
	Generated by Tools/BakeVM.luau; edit the generator, not this file.

	Types and helpers shared by the BakedVM loader and its generated handler families.
]]

--// Environment changes in the VM are not supposed to alter the behaviour of the VM so we localise globals beforehand

const Select = select
const Rawget = rawget
const TableMove = table.move

-- The iterator ipairs returns (luaB_inext); every ipairs of the host state returns this same function.
const Inext = (ipairs({}))

export type Store = { [any]: any }

export type Registers = { any }

export type Handler = (Registers) -> Handler?

export type Linker = (Handler, Handler) -> ()

export type Factory = (Upvalues: { any }) -> (...any) -> ...any

-- An upvalue cell captured by reference: [1] the table holding the value, [2] its index there, [3] the value once closed. An open
-- cell points into the register file; closing it points it at its own slot 3. Numeric fields keep every read on the array fast path.
export type Upvalue = { any }

export type Cached = {
	Closure: any,
	Upvalues: { any },
}

export type Proto = {
	MaxStackSize: number,
	ParamCount: number,
	UpvalueCount: number,
	IsVararg: boolean,
	First: Handler,
	Shape: number,
	Open: boolean,
	Cells: { boolean },
	Make: Factory,
}

const LuaMultRet = -1
const EmptyVarargs: { any } = {}

-- Upvalue table of every closure that captures nothing; no handler ever indexes it.
const NoUpvalues: { any } = {}
const RegisterBase = 5

const function CloseUpvalue(Captured: Upvalue)
	Captured[3] = Captured[1][Captured[2]]
	Captured[1] = Captured
	Captured[2] = 3
end

-- Ends the function with no results; unlinked edges and edges relinked by Close() lead here.
const function Stop(Stack: Registers): Handler?
	Stack[1] = nil
	Stack[2] = nil
	Stack[3] = 0

	return nil
end

const function Unlinked(OnNext: Handler, OnTarget: Handler) end

-- The open upvalue cell for a register captured by reference, shared by every closure that captures that register.
const function Capture(Stack: Registers, Slot: number): Upvalue
	local Pending: { [number]: Upvalue } = Stack[4]

	if Pending == nil then
		Pending = {}
		Stack[4] = Pending
	end

	const Existing = Pending[Slot]

	if Existing == nil then
		--// slot 3 exists from the start, so closing the cell never grows it
		const Opened: Upvalue = { Stack, Slot, false }

		Pending[Slot] = Opened

		return Opened
	end

	return Existing
end

-- Stores the results of a call with multiple results at At and moves top past them.
const function Spread(Stack: Registers, At: number, ...: any)
	const Count = Select("#", ...)

	Stack[5] = At + Count - 1

	if Count <= 3 then
		Stack[At], Stack[At + 1], Stack[At + 2] = ...
	else
		TableMove({ ... }, 1, Count, At, Stack)
	end
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

return {
	LuaMultRet = LuaMultRet,
	EmptyVarargs = EmptyVarargs,
	RegisterBase = RegisterBase,
	Inext = Inext,
	IpairsStep = IpairsStep,
	CloseUpvalue = CloseUpvalue,
	Stop = Stop,
	Unlinked = Unlinked,
	Spread = Spread,
	Capture = Capture,
	NoUpvalues = NoUpvalues,
}
]==]

const InitPrelude = [==[
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

-- Letter of each NEWCLOSURE capture kind in the names of the specialized closure handlers: by value, by reference, upvalue.
const CaptureKinds: { [number]: string } = {
	[0] = "V", "R", "U",
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

-- FASTCALL hints: FASTCALL3, FASTCALL, FASTCALL1, FASTCALL2, FASTCALL2K. A = builtin id; the hinted CALL is at word + 1 + C.
const FastCalls: { [number]: boolean } = {
	[60] = true, [68] = true, [73] = true, [74] = true, [75] = true,
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

-- Closure factory of a proto that Load has not finished preparing; no handler can reach it.
const function Unprepared(Upvalues: { any }): (...any) -> ...any
	return Error("proto used before it was prepared")
end
]==]

const Footer = [==[
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

			if Kind == 0 then --// Nil
				Constant = nil
			elseif Kind == 1 then --// Bool
				Constant = ReadByte() ~= 0
			elseif Kind == 2 then --// Number
				Constant = ReadDouble()
			elseif Kind == 3 then --// String
				Constant = StringList[ReadVarInt()]
			elseif Kind == 4 then --// Import
				Constant = ReadWord()
			elseif Kind == 5 then --// Table
				const Keys: { number } = {}

				for KeyIndex = 1, ReadVarInt() do
					Keys[KeyIndex] = ReadVarInt()
				end

				Constant = Keys
			elseif Kind == 6 then --// Closure
				Constant = ReadVarInt()
			elseif Kind == 7 then --// Vector
				const X = ReadFloat()
				const Y = ReadFloat()
				const Z = ReadFloat()
				const W = ReadFloat()

				Constant = if Config.VectorSize == 4 then Config.VectorCtor(X, Y, Z, W) else Config.VectorCtor(X, Y, Z)
			elseif Kind == 8 then --// Table with pre-filled constants
				const Pairs: { number } = {}

				for _ = 1, ReadVarInt() do
					const Key = ReadVarInt()
					const Value = ReadWord()

					TableInsert(Pairs, Key)
					TableInsert(Pairs, if Value < 0x80000000 then Value else Value - 0x100000000)
				end

				Constant = Pairs
			elseif Kind == 9 then --// 64-bit integer
				const Negative = ReadByte() ~= 0
				const High, Low = ReadVarInt64()
				const Digits = StringFormat("%08x%08x", High, Low)

				const FromString = IntegerFromString

				if FromString == nil then
					Error("64-bit integer constants need the integer library, which this environment does not have", 0)
				else
					Constant = FromString(if Negative then `-{Digits}` else Digits, 16)
				end
			elseif Kind == 10 then --// Class shape
				ReadVarInt()

				const MemberCount = ReadVarInt() + ReadVarInt()

				for _ = 1, MemberCount do
					ReadVarInt()
				end
			elseif Kind == 11 then --// Double-precision vector
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

		ReadVarInt() --// line defined
		ReadVarInt() --// debug name

		if ReadByte() ~= 0 then --// line info
			const LineGapLog2 = ReadByte()
			const Intervals = Bit32RShift(CodeSize - 1, LineGapLog2) + 1

			Cursor += CodeSize + Intervals * 4
		end

		if ReadByte() ~= 0 then --// debug info
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
				ReadByte() --// slot type
				ReadVarInt() --// instruction offset
			end
		end

		if LuauVersion >= 12 then
			if Bit32BTest(Flags, 0x8) then
				ReadVarInt64() --// inlining cost
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

const function Decode(Raw: Raw, Proto: Proto, RawList: { Raw }, ProtoList: { Proto }, Env: Store, BackEdges: { BackEdge })
	const Words = Raw.Words
	const Constants = Raw.Constants
	const WordCount = #Words
	const Ordinal: { number } = {}
	const IsStart: { [number]: boolean } = {}
	const Starts: { number } = {}
	const Hints: { [number]: number } = {}
	local Kept = 0
	local Word = 1

	while Word <= WordCount do
		const Opcode = Bit32BAnd(Words[Word], 0xFF)
		const Length = if HasAux[Opcode] then 2 else 1

		IsStart[Word] = true

		if FastCalls[Opcode] then --// the builtin id, keyed by the word of the CALL the hint belongs to
			Hints[Word + 1 + Bit32RShift(Words[Word], 24)] = Bit32BAnd(Bit32RShift(Words[Word], 8), 0xFF)
		end

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

	--// successors: Primary is the fallthrough (or the only destination), Secondary the branch target of two-successor opcodes
	const Opcodes: { number } = {}
	const Primary: { number } = {}
	const Secondary: { number } = {}
	local Shape = -1
	local Open = false

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

		if PureJumps[Opcode] or Opcode == 59 or Opcode == 61 or Opcode == 76 then --[[ jumps and FORGPREP* ]]
			Primary[Index] = Jump
		elseif Branches[Opcode] then
			Secondary[Index] = Jump
		elseif Opcode == 3 and Bit32RShift(Value, 24) ~= 0 then --[[ LOADB with skip ]]
			Primary[Index] = Ordinal[Start + 1 + Bit32RShift(Value, 24)]
		elseif Opcode == 22 then --[[ RETURN ]]
			const Count = Bit32BAnd(Operand, 0xFF) - 1
			const Kind = if Count >= 0 and Count <= 2 then Count else 3

			Primary[Index] = 0
			Shape = if Shape == -1 or Shape == Kind then Kind else 3
		elseif Opcode == 19 then --[[ NEWCLOSURE ]]
			for Position = 1, RawList[Raw.Protos[SignedD + 1]].UpvalueCount do
				if Bit32BAnd(Bit32RShift(Words[Start + Position], 8), 0xFF) == 1 then
					Open = true
				end
			end
		end

		if Opcode == 67 then --[[ JUMPX ]]
			const Offset = Bit32RShift(Value, 8)

			Primary[Index] = Ordinal[Start + 1 + (if Offset >= 0x800000 then Offset - 0x1000000 else Offset)]
		end
	end

	--// a NAMECALL directly followed by its CALL, which no jump enters, becomes one method-call handler that skips the CALL
	const IsTarget: { [number]: boolean } = {}
	const Fused: { [number]: number } = {}

	for Index = 1, Kept do
		IsTarget[Secondary[Index]] = true

		if Primary[Index] ~= Index + 1 then
			IsTarget[Primary[Index]] = true
		end
	end

	for Index = 1, Kept - 1 do
		const Following = Opcodes[Index + 1]

		if (Opcodes[Index] == 20 or Opcodes[Index] == 85) and (Following == 21 or Following == 87) and not IsTarget[Index + 1] then
			const Call = Words[Starts[Index + 1]]
			const B = Bit32BAnd(Bit32RShift(Call, 16), 0xFF)
			const SameBase = Bit32BAnd(Bit32RShift(Call, 8), 0xFF) == Bit32BAnd(Bit32RShift(Words[Starts[Index]], 8), 0xFF)

			if SameBase and B >= 2 and B - 2 <= MaxMethodArgs and Bit32RShift(Call, 24) <= 4 then
				Fused[Index] = Call
				Primary[Index] = Index + 2
			end
		end
	end

	--// a FASTCALL-hinted CALL is proven to call its builtin when the instruction before it, which no jump skips, is an import of
	--// that builtin into the function register; Proven maps such calls to the builtin. The proven call never reads that register,
	--// so the import is Skipped: edges into it lead straight to the call
	const Proven: { [number]: any } = {}
	const Skipped: { [number]: boolean } = {}

	const function ImportAt(Start: number): any
		const Aux = Words[Start + 1]
		const K0 = Constants[Bit32BAnd(Bit32RShift(Aux, 20), 0x3FF) + 1]
		const K1 = Constants[Bit32BAnd(Bit32RShift(Aux, 10), 0x3FF) + 1]
		const K2 = Constants[Bit32BAnd(Aux, 0x3FF) + 1]

		return ResolveImport(Env, Bit32RShift(Aux, 30), K0, K1, K2)
	end

	for Index = 2, Kept do
		const Id = Hints[Starts[Index]]
		const Previous = Starts[Index - 1]

		const Call = Words[Starts[Index]]
		const Count = Bit32BAnd(Bit32RShift(Call, 16), 0xFF) - 1
		const Results = Bit32RShift(Call, 24) - 1

		if Id ~= nil and Opcodes[Index - 1] == 12 and not IsTarget[Index] and Bit32BAnd(Bit32RShift(Words[Previous], 8), 0xFF) == Bit32BAnd(Bit32RShift(Call, 8), 0xFF) then
			const Module = BuiltinModule(Id)
			const Imported = ImportAt(Previous)

			if Module ~= nil and Count >= 0 and Results >= 0 and Module.Matches(Id, Imported, Count, Results) then
				Proven[Index] = Imported
				Skipped[Index - 1] = true
			end
		end
	end

	-- The instruction an edge into Index really reaches once pure jumps are skipped; a cycle of pure jumps keeps one of them.
	const function Resolve(Index: number): number
		local Current = Index

		for _ = 1, Kept do
			if Current < 1 or Current > Kept or not (PureJumps[Opcodes[Current]] or Skipped[Current]) or Primary[Current] == Current then
				return Current
			end

			Current = Primary[Current]
		end

		return Current
	end

	--// link modes: an edge is chained (bit 1 fallthrough, bit 2 branch) only when it moves forward, its destination may be
	--// entered at any depth, and the chain behind it is shorter than ChainLimit
	const Depth: { number } = TableCreate(Kept + 1, 1)
	const Bounce: { [number]: boolean } = {}
	const Modes: { number } = {}

	--// calls start at chain depth one, except proven builtin calls, which cannot run VM code
	for Index = 1, Kept do
		if (Bounced[Opcodes[Index]] and Proven[Index] == nil) or Fused[Index] ~= nil then
			Bounce[Index] = true
		end
	end

	for Index = 1, Kept do
		const First = Resolve(Primary[Index])
		const Second = if Secondary[Index] ~= 0 then Resolve(Secondary[Index]) else 0
		const Room = Depth[Index] < ChainLimit
		local Mode = 0

		if Opcodes[Index] == 76 then --[[ FORGPREP: its FORGLOOP comes later, so it is marked before any edge into it is linked ]]
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
			const Word = Words[Start + Index]
			const Kind = Bit32BAnd(Bit32RShift(Word, 8), 0xFF)
			const Slot = Bit32BAnd(Bit32RShift(Word, 16), 0xFF)

			Description[Index * 2] = Kind
			Description[Index * 2 + 1] = if Kind == 2 then Slot + 1 else Slot + RegisterBase + 1
		end

		return Description
	end

	if Shape == -1 then
		Shape = 3
	end

	--// a numeric loop whose step is the literal 1 (and whose limit may be literal) gets a cheaper loop handler; FORNPREP comes
	--// before its FORNLOOP while handlers are made back to front, so the loop shapes are found in a forward pass first
	const LoopStepOne: { [number]: boolean } = {}
	const LoopLimit: { [number]: number? } = {}
	const StepOneAt: { [number]: boolean } = {}
	const LimitAt: { [number]: number? } = {}

	for Index = 1, Kept do
		const Start = Starts[Index]
		const A = Bit32BAnd(Bit32RShift(Words[Start], 8), 0xFF)

		if Opcodes[Index] == 56 then --[[ FORNPREP ]]
			LoopStepOne[A] = LoadedNumber(Start - 1, A + 1) == 1
			LoopLimit[A] = LoadedNumber(Start - 2, A)
		elseif Opcodes[Index] == 57 then --[[ FORNLOOP ]]
			StepOneAt[Index] = LoopStepOne[A] == true
			LimitAt[Index] = LoopLimit[A]
		end
	end

	--// handlers are made back to front, so every forward successor already exists and is passed to its maker; a chained edge,
	--// which always moves forward, captures it as a constant. Backward edges get Stop for now and are linked afterwards
	const Handlers: { Handler } = {}
	const Links: { Linker } = {}

	for Index = Kept, 1, -1 do
		const First = Primary[Index]
		const Second = Secondary[Index]
		const OnNext = if First > Index then Handlers[First] or Stop else Stop
		const OnTarget = if Second > Index then Handlers[Second] or Stop else Stop
		const Start = Starts[Index]
		const Value = Words[Start]
		const Opcode = Opcodes[Index]
		const Aux = if HasAux[Opcode] then Words[Start + 1] else 0
		const A = Bit32BAnd(Bit32RShift(Value, 8), 0xFF)
		const B = Bit32BAnd(Bit32RShift(Value, 16), 0xFF)
		const C = Bit32RShift(Value, 24)
		const Operand = B + C * 256
		const SignedD = if Operand < 0x8000 then Operand else Operand - 0x10000
		const Mode = Modes[Index]
		local Made: Handler
		local Link: Linker

		if Opcode == 2 then --[[ LOADNIL ]]
			Made, Link = MakeLoadNil(Mode, A, OnNext, OnTarget)
		elseif Opcode == 3 then --[[ LOADB ]]
			if C == 0 then
				Made, Link = MakeLoadK(Mode, A, B == 1, OnNext, OnTarget)
			else
				Made, Link = MakeLoadSkip(Mode, A, B == 1, OnNext, OnTarget)
			end
		elseif Opcode == 4 then --[[ LOADN ]]
			Made, Link = MakeLoadK(Mode, A, SignedD, OnNext, OnTarget)
		elseif Opcode == 5 then --[[ LOADK ]]
			Made, Link = MakeLoadK(Mode, A, Constants[SignedD + 1], OnNext, OnTarget)
		elseif Opcode == 6 then --[[ MOVE ]]
			Made, Link = MakeMove(Mode, A, B, OnNext, OnTarget)
		elseif Opcode == 7 then --[[ GETGLOBAL ]]
			Made, Link = MakeGetGlobal(Mode, A, Constants[Aux + 1], Env, OnNext, OnTarget)
		elseif Opcode == 8 then --[[ SETGLOBAL ]]
			Made, Link = MakeSetGlobal(Mode, A, Constants[Aux + 1], Env, OnNext, OnTarget)
		elseif Opcode == 9 then --[[ GETUPVAL ]]
			if Proto.Cells[B + 1] then
				Made, Link = MakeGetUpval(Mode, A, B, OnNext, OnTarget)
			else
				Made, Link = MakeGetUpvalValue(Mode, A, B, OnNext, OnTarget)
			end
		elseif Opcode == 10 then --[[ SETUPVAL ]]
			Made, Link = MakeSetUpval(Mode, A, B, OnNext, OnTarget)
		elseif Opcode == 11 then --[[ CLOSEUPVALS ]]
			Made, Link = MakeCloseUpvals(Mode, A, OnNext, OnTarget)
		elseif Opcode == 12 then --[[ GETIMPORT ]]
			const Count = Bit32RShift(Aux, 30)
			const K0 = Constants[Bit32BAnd(Bit32RShift(Aux, 20), 0x3FF) + 1]
			const K1 = Constants[Bit32BAnd(Bit32RShift(Aux, 10), 0x3FF) + 1]
			const K2 = Constants[Bit32BAnd(Aux, 0x3FF) + 1]
			const Resolved = ResolveImport(Env, Count, K0, K1, K2)

			if Resolved ~= nil then
				Made, Link = MakeLoadK(Mode, A, Resolved, OnNext, OnTarget)
			else
				Made, Link = MakeGetImportSlow(Mode, A, { Count, K0, K1, K2 }, Env, OnNext, OnTarget)
			end
		elseif Opcode == 13 then --[[ GETTABLE ]]
			Made, Link = MakeGetTable(Mode, A, B, C, OnNext, OnTarget)
		elseif Opcode == 14 then --[[ SETTABLE ]]
			Made, Link = MakeSetTable(Mode, A, B, C, OnNext, OnTarget)
		elseif Opcode == 15 or Opcode == 83 then --[[ GETTABLEKS / GETUDATAKS ]]
			Made, Link = MakeGetTableKS(Mode, A, B, Constants[(if Opcode == 83 then Bit32BAnd(Aux, 0xFFFF) else Aux) + 1], OnNext, OnTarget)
		elseif Opcode == 16 or Opcode == 84 then --[[ SETTABLEKS / SETUDATAKS ]]
			Made, Link = MakeSetTableKS(Mode, A, B, Constants[(if Opcode == 84 then Bit32BAnd(Aux, 0xFFFF) else Aux) + 1], OnNext, OnTarget)
		elseif Opcode == 17 then --[[ GETTABLEN ]]
			Made, Link = MakeGetTableN(Mode, A, B, C + 1, OnNext, OnTarget)
		elseif Opcode == 18 then --[[ SETTABLEN ]]
			Made, Link = MakeSetTableN(Mode, A, B, C + 1, OnNext, OnTarget)
		elseif Opcode == 19 then --[[ NEWCLOSURE ]]
			const Description = Describe(Start, Raw.Protos[SignedD + 1])
			const Child: Proto = Description[1]

			if Child.UpvalueCount <= 3 then
				local Captures = ""

				for Position = 1, Child.UpvalueCount do
					Captures ..= CaptureKinds[Description[Position * 2]]
				end

				Made, Link = (Frames :: any)[if Captures == "" then "MakeNewClosureWithNone" else `MakeNewClosureWith{Captures}`](Mode, A, Child, Description[3], Description[5], Description[7], OnNext, OnTarget)
			else
				Made, Link = MakeNewClosure(Mode, A, Description, OnNext, OnTarget)
			end
		elseif Opcode == 20 or Opcode == 85 then --[[ NAMECALL / NAMECALLUDATA ]]
			const Method = Constants[(if Opcode == 85 then Bit32BAnd(Aux, 0xFFFF) else Aux) + 1]
			const Call = Fused[Index]

			if Call ~= nil then
				Made, Link = MakeMethod(Mode, A, B, Method, Bit32BAnd(Bit32RShift(Call, 16), 0xFF) - 2, Bit32RShift(Call, 24), OnNext, OnTarget)
			else
				Made, Link = MakeNameCall(Mode, A, B, Method, OnNext, OnTarget)
			end
		elseif Opcode == 21 or Opcode == 87 then --[[ CALL / CALLFB ]]
			const Builtin = Proven[Index]
			local Fast: Handler?, FastLink: Linker? = nil, nil

			if Builtin ~= nil then
				Fast, FastLink = BuiltinModule(Hints[Start]).MakeFast(Mode, Hints[Start], Builtin, A, B - 1, C - 1, OnNext, OnTarget)
			end

			if Fast ~= nil and FastLink ~= nil then
				Made, Link = Fast, FastLink
			else
				Made, Link = MakeCall(Mode, A, B, C, OnNext, OnTarget)
			end
		elseif Opcode == 22 then --[[ RETURN ]]
			if Shape == 0 then
				Made, Link = MakeReturnNone(Mode)
			elseif Shape == 1 then
				Made, Link = MakeReturnOne(Mode, A)
			elseif Shape == 2 then
				Made, Link = MakeReturnTwo(Mode, A)
			elseif B == 1 then
				Made, Link = MakeReturn0(Mode)
			elseif B == 2 then
				Made, Link = MakeReturn1(Mode, A)
			elseif B == 3 then
				Made, Link = MakeReturn2(Mode, A)
			else
				Made, Link = MakeReturnRange(Mode, A, B)
			end
		elseif PureJumps[Opcode] then --[[ JUMP / JUMPBACK / JUMPX / CMPPROTO ]]
			Made, Link = MakeJump(Mode, OnNext, OnTarget)
		elseif Opcode == 25 then --[[ JUMPIF ]]
			Made, Link = MakeJumpIf(Mode, A, OnNext, OnTarget)
		elseif Opcode == 26 then --[[ JUMPIFNOT ]]
			Made, Link = MakeJumpIfNot(Mode, A, OnNext, OnTarget)
		elseif Opcode == 27 then --[[ JUMPIFEQ ]]
			Made, Link = MakeJumpIfEq(Mode, A, Aux, OnNext, OnTarget)
		elseif Opcode == 28 then --[[ JUMPIFLE ]]
			Made, Link = MakeJumpIfLe(Mode, A, Aux, OnNext, OnTarget)
		elseif Opcode == 29 then --[[ JUMPIFLT ]]
			Made, Link = MakeJumpIfLt(Mode, A, Aux, OnNext, OnTarget)
		elseif Opcode == 30 then --[[ JUMPIFNOTEQ ]]
			Made, Link = MakeJumpIfNotEq(Mode, A, Aux, OnNext, OnTarget)
		elseif Opcode == 31 then --[[ JUMPIFNOTLE ]]
			Made, Link = MakeJumpIfNotLe(Mode, A, Aux, OnNext, OnTarget)
		elseif Opcode == 32 then --[[ JUMPIFNOTLT ]]
			Made, Link = MakeJumpIfNotLt(Mode, A, Aux, OnNext, OnTarget)
		elseif Opcode == 33 then --[[ ADD ]]
			Made, Link = MakeAdd(Mode, A, B, C, OnNext, OnTarget)
		elseif Opcode == 34 then --[[ SUB ]]
			Made, Link = MakeSub(Mode, A, B, C, OnNext, OnTarget)
		elseif Opcode == 35 then --[[ MUL ]]
			Made, Link = MakeMul(Mode, A, B, C, OnNext, OnTarget)
		elseif Opcode == 36 then --[[ DIV ]]
			Made, Link = MakeDiv(Mode, A, B, C, OnNext, OnTarget)
		elseif Opcode == 37 then --[[ MOD ]]
			Made, Link = MakeMod(Mode, A, B, C, OnNext, OnTarget)
		elseif Opcode == 38 then --[[ POW ]]
			Made, Link = MakePow(Mode, A, B, C, OnNext, OnTarget)
		elseif Opcode == 39 then --[[ ADDK ]]
			Made, Link = MakeAddK(Mode, A, B, Constants[C + 1], OnNext, OnTarget)
		elseif Opcode == 40 then --[[ SUBK ]]
			Made, Link = MakeSubK(Mode, A, B, Constants[C + 1], OnNext, OnTarget)
		elseif Opcode == 41 then --[[ MULK ]]
			Made, Link = MakeMulK(Mode, A, B, Constants[C + 1], OnNext, OnTarget)
		elseif Opcode == 42 then --[[ DIVK ]]
			Made, Link = MakeDivK(Mode, A, B, Constants[C + 1], OnNext, OnTarget)
		elseif Opcode == 43 then --[[ MODK ]]
			Made, Link = MakeModK(Mode, A, B, Constants[C + 1], OnNext, OnTarget)
		elseif Opcode == 44 then --[[ POWK ]]
			Made, Link = MakePowK(Mode, A, B, Constants[C + 1], OnNext, OnTarget)
		elseif Opcode == 45 then --[[ AND ]]
			Made, Link = MakeAnd(Mode, A, B, C, OnNext, OnTarget)
		elseif Opcode == 46 then --[[ OR ]]
			Made, Link = MakeOr(Mode, A, B, C, OnNext, OnTarget)
		elseif Opcode == 47 then --[[ ANDK ]]
			Made, Link = MakeAndK(Mode, A, B, Constants[C + 1], OnNext, OnTarget)
		elseif Opcode == 48 then --[[ ORK ]]
			Made, Link = MakeOrK(Mode, A, B, Constants[C + 1], OnNext, OnTarget)
		elseif Opcode == 49 then --[[ CONCAT ]]
			if C - B == 1 then
				Made, Link = MakeConcat2(Mode, A, B, OnNext, OnTarget)
			elseif C - B == 2 then
				Made, Link = MakeConcat3(Mode, A, B, OnNext, OnTarget)
			else
				Made, Link = MakeConcatN(Mode, A, B, C, OnNext, OnTarget)
			end
		elseif Opcode == 50 then --[[ NOT ]]
			Made, Link = MakeNot(Mode, A, B, OnNext, OnTarget)
		elseif Opcode == 51 then --[[ MINUS ]]
			Made, Link = MakeMinus(Mode, A, B, OnNext, OnTarget)
		elseif Opcode == 52 then --[[ LENGTH ]]
			Made, Link = MakeLength(Mode, A, B, OnNext, OnTarget)
		elseif Opcode == 53 then --[[ NEWTABLE ]]
			if Aux == 0 then
				Made, Link = MakeNewTableEmpty(Mode, A, OnNext, OnTarget)
			else
				Made, Link = MakeNewTable(Mode, A, Aux, OnNext, OnTarget)
			end
		elseif Opcode == 54 then --[[ DUPTABLE ]]
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
				Made, Link = MakeDupTable(Mode, A, Template, OnNext, OnTarget)
			else
				Made, Link = MakeNewTableEmpty(Mode, A, OnNext, OnTarget)
			end
		elseif Opcode == 55 then --[[ SETLIST ]]
			Made, Link = MakeSetList(Mode, A, B, C, Aux, OnNext, OnTarget)
		elseif Opcode == 56 then --[[ FORNPREP ]]
			Made, Link = MakeForNPrep(Mode, A, OnNext, OnTarget)
		elseif Opcode == 57 then --[[ FORNLOOP ]]
			const Limit = LimitAt[Index]

			if StepOneAt[Index] and Limit ~= nil then
				Made, Link = MakeForNLoopStepOneLimit(Mode, A, Limit, OnNext, OnTarget)
			elseif StepOneAt[Index] then
				Made, Link = MakeForNLoopStepOne(Mode, A, OnNext, OnTarget)
			else
				Made, Link = MakeForNLoop(Mode, A, OnNext, OnTarget)
			end
		elseif Opcode == 58 then --[[ FORGLOOP ]]
			const Count = Bit32BAnd(Aux, 0xFF)

			if Count == 1 then
				Made, Link = MakeForGLoop1(Mode, A, OnNext, OnTarget)
			elseif Count == 2 and Bit32BTest(Aux, 0x80000000) then --// ipairs-style traversal
				Made, Link = MakeForGLoopIpairs(Mode, A, OnNext, OnTarget)
			elseif Count == 2 then
				Made, Link = MakeForGLoop2(Mode, A, OnNext, OnTarget)
			else
				Made, Link = MakeForGLoopN(Mode, A, Count, OnNext, OnTarget)
			end
		elseif Opcode == 59 then --[[ FORGPREP_INEXT ]]
			Made, Link = MakeForGPrepInext(Mode, A, OnNext, OnTarget)
		elseif Opcode == 61 then --[[ FORGPREP_NEXT ]]
			Made, Link = MakeForGPrep(Mode, A, true, OnNext, OnTarget)
		elseif Opcode == 63 then --[[ GETVARARGS ]]
			if B == 0 then
				Made, Link = MakeGetVarargsMulti(Mode, A, OnNext, OnTarget)
			elseif B == 2 then
				Made, Link = MakeGetVarargs1(Mode, A, OnNext, OnTarget)
			elseif B == 3 then
				Made, Link = MakeGetVarargs2(Mode, A, OnNext, OnTarget)
			else
				Made, Link = MakeGetVarargsN(Mode, A, B - 1, OnNext, OnTarget)
			end
		elseif Opcode == 64 then --[[ DUPCLOSURE ]]
			Made, Link = MakeDupClosure(Mode, A, Describe(Start, Constants[SignedD + 1] + 1), OnNext, OnTarget)
		elseif Opcode == 66 then --[[ LOADKX ]]
			Made, Link = MakeLoadK(Mode, A, Constants[Aux + 1], OnNext, OnTarget)
		elseif Opcode == 71 then --[[ SUBRK ]]
			Made, Link = MakeSubRK(Mode, A, C, Constants[B + 1], OnNext, OnTarget)
		elseif Opcode == 72 then --[[ DIVRK ]]
			Made, Link = MakeDivRK(Mode, A, C, Constants[B + 1], OnNext, OnTarget)
		elseif Opcode == 76 then --[[ FORGPREP ]]
			Made, Link = MakeForGPrep(Mode, A, false, OnNext, OnTarget)
		elseif Opcode == 77 then --[[ JUMPXEQKNIL ]]
			if Bit32Extract(Aux, 31, 1) == 1 then
				Made, Link = MakeJumpIfNotNil(Mode, A, OnNext, OnTarget)
			else
				Made, Link = MakeJumpIfNil(Mode, A, OnNext, OnTarget)
			end
		elseif Opcode == 78 or Opcode == 79 or Opcode == 80 then --[[ JUMPXEQKB / JUMPXEQKN / JUMPXEQKS ]]
			const K = if Opcode == 78 then Bit32BAnd(Aux, 1) == 1 else Constants[Bit32Extract(Aux, 0, 24) + 1]

			if Bit32Extract(Aux, 31, 1) == 1 then
				Made, Link = MakeJumpIfNotK(Mode, A, K, OnNext, OnTarget)
			else
				Made, Link = MakeJumpIfK(Mode, A, K, OnNext, OnTarget)
			end
		elseif Opcode == 81 then --[[ IDIV ]]
			Made, Link = MakeIDiv(Mode, A, B, C, OnNext, OnTarget)
		elseif Opcode == 82 then --[[ IDIVK ]]
			Made, Link = MakeIDivK(Mode, A, B, Constants[C + 1], OnNext, OnTarget)
		elseif Opcode == 86 then --[[ NEWCLASSMEMBER ]]
			Made, Link = MakeNewClassMember(Mode, A, C, Constants[Aux + 1], OnNext, OnTarget)
		else
			Made, Link = MakeUnsupported(Mode, Opcode)
		end

		Handlers[Index] = Made
		Links[Index] = Link
	end

	--// only handlers with a backward edge are linked; their copies trampoline that edge through a patchable successor
	for Index = 1, Kept do
		const First = Primary[Index]
		const Second = Secondary[Index]
		const NextBack = First ~= 0 and First <= Index
		const TargetBack = Second ~= 0 and Second <= Index

		if NextBack or TargetBack then
			const OnNext = Handlers[First] or Stop
			const OnTarget = Handlers[Second] or Stop

			Links[Index](OnNext, OnTarget)
			TableInsert(BackEdges, {
				Link = Links[Index],
				OnNext = OnNext,
				OnTarget = OnTarget,
				NextBack = NextBack,
				TargetBack = TargetBack,
			})
		end
	end

	Proto.First = Handlers[Resolve(1)] or Stop
	Proto.Shape = Shape
	Proto.Open = Open
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

		if Opcode == 19 then --[[ NEWCLOSURE ]]
			const Operand = Bit32RShift(Words[Word], 16)

			Child = Raw.Protos[(if Operand < 0x8000 then Operand else Operand - 0x10000) + 1]
		elseif Opcode == 64 then --[[ DUPCLOSURE ]]
			const Operand = Bit32RShift(Words[Word], 16)

			Child = (Raw.Constants[(if Operand < 0x8000 then Operand else Operand - 0x10000) + 1]) + 1
		end

		if Child ~= 0 then
			const ChildCells = ProtoList[Child].Cells

			for Position = 1, RawList[Child].UpvalueCount do
				const Value = Words[Word + Position]
				const Kind = Bit32BAnd(Bit32RShift(Value, 8), 0xFF)

				ChildCells[Position] = Kind == 1 or (Kind == 2 and Cells[Bit32BAnd(Bit32RShift(Value, 16), 0xFF) + 1] == true)
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
			Shape = 3,
			Open = true,
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
]==]

--// Assembly

-- Whether Name occurs in the code of Source (comments aside) as a whole identifier that is not a field access.
const function Uses(Source: string, Name: string): boolean
	const Code = string.gsub(Source, "%-%-[^\n]*", "")

	return string.find(`\n{Code}`, `[^%w_%.]{Name}%f[^%w_]`) ~= nil
end

-- Turns the one-line `--[[ ... ]]` labels of the fixed source sections (`if Opcode == 2 then --[[ LOADNIL ]]`) into `--`
-- comments; the file header block and `--//` comments stay as they are.
const function InlineLabels(Source: string): string
	const Lines: { string } = {}

	for Line in string.gmatch(Source, "([^\n]*)\n") do
		const Text = string.gsub(Line, "%-%-%[%[%s*(.-)%s*%]%]%s*$", "-- %1")

		table.insert(Lines, Text)
	end

	return `{table.concat(Lines, "\n")}\n`
end

-- Writes one module: header, requires, the aliases, runtime imports and types its body uses, then the body.
const function WriteModule(Name: string, Documentation: string, Requires: { string }, Body: string)
	const Lines: { string } = { "--!optimize 2", "--!strict", "", "--[[", GeneratedNote, "", Documentation, "]]", "" }
	const Aliases: { string } = {}
	const Imports: { string } = {}
	const Types: { string } = {}

	for _, Alias in GlobalAliases do
		if Uses(Body, Alias[1]) then
			table.insert(Aliases, `const {Alias[1]} = {AliasValue(Alias[2])}`)
		end
	end

	for _, Value in RuntimeValues do
		if Uses(Body, Value) then
			table.insert(Imports, `const {Value} = Runtime.{Value}`)
		end
	end

	for _, Type in RuntimeTypes do
		if Uses(Body, Type) then
			table.insert(Types, `type {Type} = Runtime.{Type}`)
			table.insert(Types, "")
		end
	end

	for _, Line in Requires do
		table.insert(Lines, Line)
	end

	table.insert(Lines, "")

	if #Aliases > 0 then
		table.insert(Lines, "--// Environment changes in the VM are not supposed to alter the behaviour of the VM so we localise globals beforehand")
		table.insert(Lines, "")

		for _, Line in Aliases do
			table.insert(Lines, Line)
		end

		table.insert(Lines, "")
	end

	if #Imports > 0 then
		for _, Line in Imports do
			table.insert(Lines, Line)
		end

		table.insert(Lines, "")
	end

	for _, Line in Types do
		table.insert(Lines, Line)
	end

	const Handle = Fs.open(`{OutputDirectory}/{Name}.luau`, "w")

	Fs.write(Handle, InlineLabels(`{table.concat(Lines, "\n")}\n{Body}`))
	Fs.close(Handle)
end

for _, Directory in { OutputDirectory, `{OutputDirectory}/Variants` } do
	if not Fs.exists(Directory) then
		Fs.mkdir(Directory)
	end
end

do
	const Handle = Fs.open(`{OutputDirectory}/Runtime.luau`, "w")

	Fs.write(Handle, InlineLabels(RuntimeSource))
	Fs.close(Handle)
end

const InitRequires: { string } = { `const Runtime = require("@self/Runtime")` }
local Footered = Footer

for _, Family in Families do
	local Baked = #Family.Operands > 0

	for _, Operand in Family.Operands do
		Baked = Baked and Operand.Range > 0
	end

	if Baked then
		EmitVariants(Family)
	end
end

PackVariants()

for _, Module in Modules do
	const Exports: { string } = {}

	Output = {}

	for _, Family in Families do
		if Family.Module == Module.Name then
			EmitFamily(Family)
			table.insert(Exports, `\tMake{Family.Name} = Make{Family.Name},`)
			Footered = string.gsub(Footered, `%f[%w]Make{Family.Name}%(`, `{Module.Name}.Make{Family.Name}(`)
		end
	end

	if Module.Lazy then
		EmitBuiltinDispatch(Module.Name)
		table.insert(Exports, "\tMatches = Matches,")
		table.insert(Exports, "\tMakeFast = MakeFast,")
	end

	Push("return {")

	for _, Line in Exports do
		Push(Line)
	end

	Push("}")
	Push("")

	const Documentation = `\t{Module.Description} Handler families of BakedVM; init.luau describes the handler protocol.{HandlerNotation}`

	WriteModule(Module.Name, Documentation, { `const Runtime = require("./Runtime")` }, table.concat(Output, "\n"))

	if not Module.Lazy then
		table.insert(InitRequires, `const {Module.Name} = require("@self/{Module.Name}")`)
	end
end

Output = {}

Push("-- NAMECALL + CALL pairs are fused when the call passes at most this many arguments after the object.")
Push(`const MaxMethodArgs = {MaxMethodArgs}`)
Push("")

for Line in string.gmatch(InitPrelude, "(.-)\n") do
	Push(Line)
end

Push("")
EmitMakeFactory()
EmitMakeCall()
EmitMakeMethod()
EmitBuiltinRouter()

for Line in string.gmatch(Footered, "(.-)\n") do
	Push(Line)
end

Push("")
WriteModule("init", InitDocumentation, InitRequires, table.concat(Output, "\n"))

for _, Pack in VariantPacks do
	const Directory = `{OutputDirectory}/Variants/{Pack.Module}`
	const Exports: { string } = {}

	for _, Label in Pack.Labels do
		table.insert(Exports, `\tMake{Label} = Make{Label},`)
	end

	if not Fs.exists(Directory) then
		Fs.mkdir(Directory)
	end

	const Returned = if #Pack.Labels == 1 then `Make{Pack.Labels[1]}` else `\{\n{table.concat(Exports, "\n")}\n}`
	const Body = `{table.concat(Pack.Lines, "\n")}\nreturn {Returned}\n`
	const Documentation = `\tBaked copies of {table.concat(Pack.Labels, ", ")} for {Pack.Module}.luau, required on first use.{HandlerNotation}`

	WriteModule(`Variants/{Pack.Module}/{Pack.Name}`, Documentation, { "const Runtime = require(\"../../Runtime\")" }, Body)
end

print(`wrote {OutputDirectory}: {#Modules + 2} modules, {#VariantPacks} variant files, {#Families} handler families`)