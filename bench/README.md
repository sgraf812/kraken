# Benchmarks

Two harnesses, measured on one machine in one sitting.

* `bench/Cases/` plus `bench/lib/Driver.lean`: the program is a recursive
  function of `n`, so a run elaborates a fixed amount of source at any size and
  the driver reports stepping, discharge and kernel time separately. Driven by
  `bench/vcgen_kraken.lean` (one pipeline, four families) and
  `bench/vcgen_letspec.lean` (one family, four pipelines).
* `bench/gen.py`: the same four families as whole files of `n` lines, so a run's
  wall time includes elaborating and compiling the program. `bench/run.sh` times
  them. `bench/gen_master.py` emits the equivalent files for the `main` branch,
  where a program is parsed assembly and the proof runs `kstep`.

Reference points: import-only wall time is 0.60 s here and 0.58 s on `main`.

## Phase split, Cases harness (ms: stepping / discharge / kernel)

The pipeline is the `@[spec]` triples of `Kraken/X64MNew.lean`, stepped with
`vcgen -internalize simplifying_assumptions` and discharged with `bv_decide`, on
`X64MNew`: a reader over the label/layout environment and a state over `rip`,
above the error-state machine over `Sys D`.

| family | n=40 | n=160 | n=640 |
| --- | --- | --- | --- |
| AddChain | 25 / 5 / 17 | 58 / 3 / 61 | 222 / 4 / 412 |
| DecChain | 25 / 19 / 18 | 55 / 58 / 66 | 188 / 245 / 418 |
| AdcChain | 33 / — / 31 | 75 / — / 130 | 289 / — / 799 |

`—` marks a family with no verification condition left to discharge: the carry
chain and the multi-register chain are ground, so the state-simplification pass
reaches the postcondition's value and closes the goal during stepping.

MultiReg runs at n=4/10/40 rounds (15 writes each):

| n=4 | n=10 | n=40 |
| --- | --- | --- |
| 26 / — / 20 | 33 / — / 32 | 90 / — / 123 |

## Whole-file wall time (s)

`gen.py` emits `X64MNew` programs; the `spec` column is their whole-file wall
time, against `main`'s parsed-assembly `kstep`.

| family | n | `main` (kstep) | spec |
| --- | --- | --- | --- |
| add | 40 | 1.22 | 0.68 |
| add | 160 | 8.46 | 0.86 |
| add | 640 | — | 3.12 |
| dec | 40 | 1.16 | 0.71 |
| dec | 160 | 8.25 | 0.85 |
| dec | 640 | — | 3.10 |
| adc | 40 | fails | 0.71 |
| adc | 160 | fails | 0.90 |
| adc | 640 | — | 3.59 |
| multireg | 40 | 0.99 | 0.74 |
| multireg | 160 | 5.69 | 0.90 |
| multireg | 640 | — | 4.45 |

`main` on the carry chain: `kstep` produces a term the kernel rejects
(`application type mismatch: BitVec.unsigned ()`), independent of the discharge,
already at four `adc` instructions. `main` was not run at n=640.

## Example proofs

| proof | `main` | here |
| --- | --- | --- |
| mov+dec (`p4`) | 0.61 s, complete | 0.64 s, complete |
| dynamic stack | 0.85 s, `sorry` after the first of nine instructions | 1.72 s, all nine stepped, seven goals under `sorry` |
| memory store then reload | part of `Kraken/Examples/Examples.lean`, 1.28 s for the file | `Kraken/MemBench.lean`, 0.68 s, complete |

The ported examples, each a standalone file, timed against the same example
extracted from `main`'s `Kraken/Examples/Examples.lean` into its own file (with
the shared helpers `Executable.directivesFromStart` and `BitVec.take_all`).
Import-only wall time is 0.60 s here and 0.58 s on `main`.

All on `X64MNew`, so each `here` time sits at the import floor.

| proof | file | `main` | here |
| --- | --- | --- | --- |
| register swap through three `xor`s | `Kraken/Examples/SwapNew.lean` | 0.84 s | 0.65 s |
| ALU with a memory source operand | `Kraken/Examples/AluMemNew.lean` | 0.94 s | 0.59 s |
| store/reload through a SIB address | `Kraken/Examples/SibRoundtripNew.lean` | 0.84 s | 0.60 s |
| two stores, two loads (adjacent heap slots) | `Kraken/Examples/Move2RegsToHeapNew.lean` | 1.04 s | 0.63 s |
| push, clobber, pop back (stack roundtrip) | `Kraken/Examples/PushPopNew.lean` | — | 0.61 s |
| conditional jump through `jcc` | `Kraken/Examples/CondNew.lean` | — | 0.62 s |
| MMIO increment (device register) | `Kraken/Examples/IncrementMMIONew.lean` | — | 0.66 s |
| DMA increment (buffer transfer) | `Kraken/Examples/IncrementDMANew.lean` | — | 0.64 s |

The push/pop example steps with `vcgen simplifying_assumptions`: the pass folds
the pop's load into a read-over-write over the push's store at the same stack
slot, `easm` reads the mapped-ness and the stored value off the memory
hypotheses, and `BitVec.ofInt_toInt` (the value stored as an integer and
reloaded) closes the register identity. It has no `main` counterpart.

The conditional jump steps through `Op.jcc_spec`, which sends the taken branch to
the exception post and the fall-through to the continuation. The MMIO and DMA
examples run device programs over `Sys D`, where the device state is the `device`
component the framework threads and a control transfer preserves; `vcgen` splits
each memory access on the address being mapped and on the device accepting it.
