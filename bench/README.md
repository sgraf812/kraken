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
| `segadc.lean` | carry chain, ground, deep embedding | `vcgen -internalize simplifying_assumptions` | `grind` |

## Phase split (ms: stepping / discharge / kernel)

| family | n=40 | n=160 | n=640 |
| --- | --- | --- | --- |
| segadc | 19 / 13 / 36 | 53 / 11 / 153 | 248 / 12 / 713 |

`segadc` steps a carry chain through the state wp of `Kraken/StateWP.lean`:
the program is the directive list, the specs are one triple per directive,
and a run is the baseline interpreter's burst. Its goal quantifies over the
label table, so `intro` precedes the stepping tactic. One verification condition survives stepping, the read of the
register the postcondition names, and `grind` closes it.
