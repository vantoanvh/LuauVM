# LuauVM
Very fast luau bytecode interpreter in luau<br>
The main goal is speed, so it doesn't include debugging hooks or tracing. It's meant for running bytecode, not debugging it<br>
Also tries to match stock Luau's behavior as closely as possible<br>

You can choose 2 type of file:
- `LuauVM.luau`: Default one, `~4,800` lines of code
- `BakedVM.luau`: A prebaked version, `~400,000` lines of code, fastest execution speed possible, slower decode time

## Performance

Compared against stock Luau and Fiu across 211 workloads. (Stock Luau is the 1x baseline.) <br>
**Median slowdown compared to stock Luau (lower is better):**

| Category | LuauVM | BakedVM | Fiu |
|---|---:|---:|---:|
| Calls | 12.7x | 9.0x | 65.7x |
| Tables | 9.5x | 6.1x | 36.9x |
| Loops | 13.9x | 8.4x | 67.7x |
| Strings | 4.8x | 3.2x | 17.9x |
| Arithmetic | 8.6x | 5.9x | 41.0x |
| Closures | 13.8x | 9.4x | 63.5x |
| Metatables | 8.4x | 5.7x | 41.3x |
| Coroutines | 4.9x | 3.2x | 22.6x |
| Real-world | 10.7x | 7.1x | 47.3x |
| **Overall median** | **9.7x** | **6.2x** | **41.0x** |

All tests were run without native codegen.
