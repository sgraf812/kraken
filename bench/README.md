# Benchmarks

An independent Lake package (`bench/lakefile.toml`) that requires the parent
`Kraken`. Each benchmark is one file whose `#eval` prints its numbers: open the
file in the editor to run it, or from `bench/`

    lake env lean adcchain.lean

The program under test is a recursive function of `n`, so a run elaborates a
fixed amount of source at any size, and the driver (`lib/Driver.lean`,
`runBenchUsingTactic`) reports stepping, discharge and kernel time separately.
The recursive families live in `Cases/`; each benchmark file selects a family, a
stepping tactic and a discharge tactic.

## Files

| file | family | stepping | left for discharge |
| --- | --- | --- | --- |
| `adcchain.lean` | carry chain, straight line | `vcgen` | none left |
| `carryflags.lean` | carry chain on symbolic registers, post on `zf`, `sf` and `rax` | `vcgen with kfinish` | none left |
| `carryjumps.lean` | `n` copies of `adc %rbx, %rax; jz out` on symbolic registers | `vcgen with kfinish` | none left |
| `manycalls.lean` | `n` calls of `touch`, which stores `rax` at the fixed address `rsi` | `vcgen [touch_spec] invariants … with kfinish` | none left |
| `changingframes.lean` | `n` calls of `poke`, each followed by `addq $8, %rdi` | `vcgen [poke_spec] invariants … with kfinish` | none left |

## Phase split (ms: stepping / kernel)

| family | n | stepping | kernel |
| --- | --- | --- | --- |
| adcchain | 40 | 26 | 21 |
| adcchain | 160 | 64 | 92 |
| adcchain | 640 | 275 | 654 |
| carryflags | 8 | 15 | 5 |
| carryflags | 16 | 14 | 9 |
| carryflags | 32 | 18 | 20 |
| carryjumps | 8 | 305 | 8 |
| carryjumps | 16 | 959 | 20 |
| carryjumps | 32 | 5192 | 85 |
| manycalls | 8 | 1381 | 19 |
| manycalls | 16 | 2102 | 30 |
| manycalls | 32 | 4053 | 83 |
| changingframes | 8 | 1475 | 27 |
| changingframes | 16 | 3137 | 62 |
| changingframes | 32 | 12170 | 242 |

Each time is the median of three runs on a shared machine at load average 1.4
to 2.9.

`adcchain` states a triple for `mov $0, %rax; add $0, %rax; mov $3, %rbx`
followed by `n` copies of `adc %rbx, %rax`, with the post
`s'.regs.rax.toNat = 3 * n`. `vcgen` folds every register write, sum and
carry into a literal, so no verification condition is left.

`manycalls` and `changingframes` state the obligation that `funspec` generates
for the caller (`many_spec.go`) of `Kraken/X64/Examples/WP/ManyCalls.lean`
and `Kraken/X64/Examples/WP/ChangingFrames.lean`. The callee is a fixed
`funspec` with `autoframes` that writes 8 bytes: in `manycalls` every call
writes the same location, in `changingframes` each call writes the next one. `vcgen` steps the caller through
`Program.WP.Spec.cfg`, whose invariant is the entry state at the label `many`.
`with kfinish` discharges each verification condition in the E-graph of
`vcgen`, so the stepping time includes the discharge. The time is linear in
the number of calls. At `n = 32`, the verification condition after the last call
needs more than 1000 E-matching instances, so `changingframes` passes
`(instances := 3000)` to `kfinish`.
