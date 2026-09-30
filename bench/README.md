# Benchmarks

An independent Lake package (`bench/lakefile.toml`) that requires the parent
`Kraken`. Each benchmark is one file whose `#eval` prints its numbers: open the
file in the editor to run it, or

    lake env lean bench/segadc.lean

The program under test is a recursive function of `n`, so a run elaborates a
fixed amount of source at any size, and the driver (`lib/Driver.lean`,
`runBenchUsingTactic`) reports stepping, discharge and kernel time separately.
The recursive families live in `Cases/`; each benchmark file selects a family, a
stepping tactic and a discharge tactic.

## Files

| file | family | stepping | discharge |
| --- | --- | --- | --- |
| `segadc.lean` | carry chain, ground, deep embedding | `kvcgen64` | none left |

## Phase split (ms: stepping / discharge / kernel)

| family | n=40 | n=160 | n=640 |
| --- | --- | --- | --- |
| segadc | 30 / — / 40 | 81 / — / 231 | 346 / — / 1134 |

`segadc` steps a carry chain through the state wp of `Kraken/StateWP.lean`:
the program is the directive list, the specs are one triple per directive,
and a run is the baseline interpreter's burst. `kvcgen64` folds each register
write into the register literal and each ground sum and carry into a literal,
so no verification condition is left after stepping. The certificate grows
by about 1000 nodes per instruction (637118 at n=640), and the kernel check
is the largest cost.

`—` marks a family with no verification condition to discharge.
