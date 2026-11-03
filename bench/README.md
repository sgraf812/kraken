# Benchmarks

An independent Lake package (`bench/lakefile.toml`) that requires the parent
`Kraken`. Each benchmark is one file whose `#eval` prints its numbers: open the
file in the editor to run it, or from `bench/`

    lake env lean segadc.lean

The program under test is a recursive function of `n`, so a run elaborates a
fixed amount of source at any size, and the driver (`lib/Driver.lean`,
`runBenchUsingTactic`) reports stepping, discharge and kernel time separately.
The recursive families live in `Cases/`; each benchmark file selects a family, a
stepping tactic and a discharge tactic.

## Files

| file | family | stepping | left for discharge |
| --- | --- | --- | --- |
| `segadc.lean` | carry chain, straight line | `vcgen` | none left |
| `manycalls.lean` | `n` calls of `touch` | `Program.Triple.cfg`, `cfg_cases`, `vcgen [touch_spec] with kfinish` | none left |
| `changingframes.lean` | `n` calls of `poke`, each followed by `addq $8, %rdi` | `Program.Triple.cfg`, `cfg_cases`, `vcgen [poke_spec] with kfinish` | none left |

## Phase split (ms: stepping / kernel)

| family | n | stepping | kernel |
| --- | --- | --- | --- |
| segadc | 40 | 64 | 20 |
| segadc | 80 | 121 | 37 |
| segadc | 120 | 192 | 79 |
| manycalls | 8 | 891 | 21 |
| manycalls | 16 | 1393 | 41 |
| manycalls | 32 | 2476 | 119 |
| changingframes | 8 | 1920 | 25 |
| changingframes | 16 | 4263 | 72 |

`segadc` states a triple for `mov $0, %rax; add $0, %rax; mov $3, %rbx`
followed by `n` copies of `adc %rbx, %rax`, with the post
`s'.regs.rax.toNat = 3 * n`. `vcgen` folds every register write, sum and
carry into a literal, so no verification condition is left. At `n ≥ 125` the
program holds 128 directives, and the `NoLabels` instance of
`Program.WP.cons_spec` exceeds `synthInstance.maxSize` (128), so no spec
applies.

`manycalls` and `changingframes` state the obligation that `funspec` generates
for the caller (`many_spec.go`) of `Kraken/X64/Examples/WP/ManyCalls.lean`
and `Kraken/X64/Examples/WP/ChangingFrames.lean`. The callee is a fixed
`funspec` with `autoframes`. `with kfinish` discharges each verification
condition in the E-graph of `vcgen`, so the stepping time includes the
discharge. The time is linear in the number of calls. At `n = 32`,
`changingframes` fails: `grind` reaches its instance threshold (1000) on one
verification condition.
