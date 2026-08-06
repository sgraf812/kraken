# Benchmarks

An independent Lake package (`bench/lakefile.toml`) that requires the parent
`Kraken`. Each benchmark is one file whose `#eval` prints its numbers: open the
file in the editor to run it, or

    lake env lean bench/add.lean

The program under test is a recursive function of `n`, so a run elaborates a
fixed amount of source at any size, and the driver (`lib/Driver.lean`,
`runBenchUsingTactic`) reports stepping, discharge and kernel time separately.
The recursive families live in `Cases/`; each benchmark file selects a family, a
stepping tactic and a discharge tactic.

## Files

| file | family | stepping | discharge |
| --- | --- | --- | --- |
| `add.lean` | register add chain, symbolic start | `vcgen -internalize simplifying_assumptions` | `bv_decide` |
| `dec.lean` | register decrement chain | `vcgen -internalize simplifying_assumptions` | `bv_decide` |
| `adc.lean` | carry chain, ground | `vcgen -internalize simplifying_assumptions` | none left |
| `multireg.lean` | fifteen writes per round, ground | `vcgen -internalize simplifying_assumptions` | none left |
| `mov.lean` | immediate-mov chain | `vcgen -internalize simplifying_assumptions` | `grind` |
| `letspec.lean` | add chain, four pipelines | four rows | `sorry` / `kfold_discharge` / `bv_decide` |

`adc` and `multireg` are ground, so the state-simplification pass reaches the
postcondition's value and closes the goal during stepping, leaving no
verification condition. `letspec` runs the add chain four ways to split the cost:
`sorry` isolates the stepping certificate, and the others add a checked proof,
with and without `simplifying_assumptions`.

## Phase split (ms: stepping / discharge / kernel)

The pipeline is the let-form `@[spec]` triples of `Kraken/X64MNew.lean`, stepped
with `vcgen -internalize simplifying_assumptions` and discharged with
`bv_decide`, over `X64MNew`: a reader over the label environment and a state over
`rip`, above the error-state machine over `Sys D`.

| family | n=40 | n=160 | n=640 |
| --- | --- | --- | --- |
| add | 25 / 5 / 17 | 58 / 3 / 61 | 221 / 4 / 414 |
| dec | 25 / 19 / 18 | 55 / 58 / 66 | 188 / 245 / 418 |
| adc | 31 / — / 29 | 71 / — / 132 | 290 / — / 804 |

`—` marks a family with no verification condition to discharge. `multireg` runs
at n=4/10/40 rounds (fifteen writes each): 26 / — / 20, 33 / — / 32, 90 / — / 123.
