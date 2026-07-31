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

`spec` is the current pipeline: the `@[spec]` triples of `Kraken/Specs.lean`,
`vcgen -internalize simplifying_assumptions`, `bv_decide`. `accessor+kfold` and
`accessor+simp` are the two pipelines it replaced, measured at commit b0aea0a.

| family | pipeline | n=40 | n=160 | n=640 |
| --- | --- | --- | --- | --- |
| AddChain | spec | 16 / 3 / 13 | 43 / 2 / 54 | 182 / 3 / 356 |
| AddChain | accessor+kfold | 56 / 17 / 20 | 224 / 61 / 190 | 1171 / 241 / 2208 |
| AddChain | accessor+simp | 62 / 98 / 14 | 229 / 449 / 108 | 1174 / 4536 / 1330 |
| DecChain | spec | 16 / 17 / 15 | 36 / 53 / 54 | 140 / 214 / 346 |
| DecChain | accessor+kfold | 58 / 18 / 17 | 213 / 54 / 155 | 1057 / 235 / 2086 |
| DecChain | accessor+simp | 60 / 270 / 16 | 233 / 2090 / 101 | 1101 / 30105 / 1247 |
| AdcChain | spec | 23 / — / 25 | 59 / — / 111 | 245 / — / 728 |
| AdcChain | accessor+kfold | 71 / 17 / 31 | 252 / 55 / 238 | 1233 / 247 / 2507 |
| AdcChain | accessor+simp | 71 / 45 / 44 | 280 / 170 / 297 | 1326 / 802 / 4077 |

`—` marks a family with no verification condition left to discharge: the carry
chain and the multi-register chain are ground, so the state-simplification pass
reaches the postcondition's value and closes the goal during stepping.

MultiReg runs at n=4/10/40 rounds (15 writes each):

| pipeline | n=4 | n=10 | n=40 |
| --- | --- | --- | --- |
| spec | 16 / — / 16 | 23 / — / 22 | 58 / — / 81 |
| accessor+kfold | 99 / 26 / 43 | 209 / 43 / 156 | 955 / 208 / 2002 |
| accessor+simp | 99 / 137 / 25 | 220 / 310 / 76 | 966 / 2128 / 723 |

## Whole-file wall time (s)

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

| proof | file | `main` | here |
| --- | --- | --- | --- |
| register swap through three `xor`s | `Kraken/Examples/Swap.lean` | 0.84 s | 0.74 s |
| ALU with a memory source operand | `Kraken/Examples/AluMem.lean` | 0.94 s | 0.74 s |
| store/reload through a SIB address | `Kraken/Examples/SibRoundtrip.lean` | 0.84 s | 0.75 s |
| two stores, two loads (adjacent heap slots) | `Kraken/Examples/Move2RegsToHeap.lean` | 1.04 s | 0.74 s |
| push, clobber, pop back (stack roundtrip) | `Kraken/Examples/PushPop.lean` | — | 0.62 s |

The push/pop example steps with `vcgen simplifying_assumptions`: the pass folds
the pop's load into a read-over-write over the push's store at the same stack
slot, `easm` reads the mapped-ness and the stored value off the memory
hypotheses, and `BitVec.ofInt_toInt` (the value stored as an integer and
reloaded) closes the register identity. It has no `main` counterpart.

Ported at the spec level but without a composing example: `jnz` (the
conditional-jump spec puts the continuation's `wp` under an `if` on `ZF` that
stepping does not reduce). Out of scope for the `EStateM` model: the MMIO and DMA
examples, which need a resumable device-state model rather than a throwing
non-memory access. See `TODO.md` for each.
