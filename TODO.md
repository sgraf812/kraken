# TODO

- Engine (lean4/grind): `internalize` does not share/canonicalize its argument
  (`Grind.add`/`addFactStep` likewise); the hash-consing invariant `mkEqProof`
  relies on is unmaintainable caller-side (accessor-obtained terms are only
  sometimes pointer-identical to session nodes, see Kraken.easm mechanism
  trace). Fix: `internalize` runs `preprocessLight`-class sharing itself;
  defense in depth: `mkCongrDefaultProof` treats the all-`isSameExpr` case as
  `rfl`. Reproducer: mkEqProof-panic-mwe.lean. Until then easm carries the
  workaround (preprocessLight before internalize).
- Engine (lean4/grind): directed fold of stratified equation chains
  (constant propagation / hypothesis-chain evaluation). Blocks: Sdyn.lean
  reload VCs (the remaining sorry).
- Engine (vcgen): normalize `And` at Prop-valued preconditions to the lattice
  meet so the spec-authoring trap (raw `∧` stops the driver) disappears.
- Engine (vcgen): `simplifying_assumptions` accepts rewrite theorems only. Its
  methods are `simpControl >> simpArrowTelescope` and `evalGround >> rewrite`,
  and named `Sym.simp` variants are rejected, so a workload cannot contribute a
  simproc. That is why register identity goes through `Reg64.idx`: the pass can
  compare two `Nat` numerals but not two constructors. Either expose a simproc
  hook, or give `evalGround` enum-constructor equality.

- The spec style is one `@[spec]` triple per instruction whose precondition is
  the postcondition applied to a record update of the pre-state. Stating the
  post-state as a `let` instead builds the identical rule, since `Sym`'s
  `preprocessType` zeta-reduces every rule type and `Pattern` cannot represent
  `letE`; measured, the two differ by three nodes in the certificate DAG.

- Kernel checking is super-linear in these proofs because each congruence node
  carries a type that deepens with the chain: cost is the sum over nodes of the
  type size, not the shared term size. Isolated in
  kernel-congr-quadratic-mwe.lean, where holding node count fixed and shrinking
  only the node types takes n=1600 from 3593ms to 4ms. A spine of non-adjacent
  binders is quadratic for the same reason: kernel-letchain-superlinear-mwe.lean.
  Under the current pipeline the exponent is down to about 1.4 (AddChain kernel
  13/54/356 ms at n=40/160/640) from about 1.7, but it is still the largest
  single item at n=640 and the one to attack next.

- `clear_dead` (KrakenTactics/ClearDead.lean) prunes the equation hypotheses
  unreachable from the goal. The analysis needs closure under rewriting of
  projection paths, since steps read components at different granularities;
  closing over every reachable subterm is correct but takes 180s at n=160,
  restricting the rewrite to path-shaped terms is correct and cheap.
  `Lean.Elab.Tactic.Do.elimLets` cannot express the criterion: it only
  eliminates let-bound decls, and use-counting does not separate a dead flag
  equation from a needed register equation, since both have zero fvar-uses.
  The tactic lives in the `KrakenTactics` lean_lib with `precompileModules`,
  without which it runs interpreted (4.02s of a 8.9s run vs 3.87ms compiled).
  It cannot move into `SymM`: rewriting the local context is outside what `Sym`
  supports, so it stays a `MetaM` tactic.

- Proof-sharing through the goal: asserted hypotheses do not survive
  instantiation (`assert` produces `?goal prf`, and instantiating the
  metavariable beta-reduces, splicing `prf` into every use site), while
  `define`d `let`s do. `kfold` `define`s each folded component equation, so the
  certificate tree went from 2^n (Eq.trans count 2^(n+2)-1, from the two
  occurrences of the previous register file per step) to linear, verified by a
  DAG-memoized tree-size count. Pretty-printed size is a misleading proxy:
  indentation alone contributes depth x lines = n^2 bytes.

- Lazy program unfolding: passing the recursive program to vcgen as an equation
  spec (`vcgen [AddChain.chain]` with no upfront unfold) keeps the residual
  program folded in every wp type and makes stepping ~4x faster and linear.
  The bench driver's upfront-unfold path is the slow variant.

- `easm` address canonicalization does not bridge a write to a non-address
  register. When an instruction writes a register that the accessed address does
  not mention, the memory VC carries `Addr.eval a (regs.set64 r v)` while the
  provided `h_load` fact is stated over `Addr.eval a regs`. The first simp pass
  keeps `Addr.eval` folded, so the two addresses differ syntactically and the
  fact does not fire; the second pass unfolds `Addr.eval` and `Reg64s.get64` in
  the VC but leaves the folded fact unmatched. Repro: `Kraken/Examples/AluMem.lean`
  with a `movq $42, %rax` before the store (the `rax` write shifts the store
  address off `s₀.regs`). The examples work around it by keeping addresses
  register-write-free at each access, or by supplying the address equality as a
  hypothesis (`ha8'` in `Kraken/Examples/Move2RegsToHeap.lean`). A direct
  `get64 rsp` address over `set64` writes hits the same wall through a different
  route: the second pass unfolds `Reg64s.get64` before `get64_set64` can fire and
  then stalls on `UInt64.toBitVec (UInt64.ofBitVec _)`. Repro: `pushR`/`popR`
  roundtrip (specs present in `Kraken/Specs.lean`; `push`, clobber, `pop` back
  leaves the `pop` load address as `get64 rsp` over two `set64`s). Fix: canonicalize
  register reads over writes at the folded level (add `Reg64s.get64_set64` to the
  first pass), or pre-normalize the added hypotheses with the address-unfold set so
  both sides of the match are unfolded together.

- Conditional jumps do not compose with straightline `vcgen` stepping. `jnz_spec`
  (`Kraken/Specs.lean`) is proven: its precondition is
  `if s.status.zf then Q () s else E (.jump l) s`. But applying it puts the
  continuation's `wp` under that `if`, and `vcgen` does not reduce the `if` to
  resume stepping the taken/not-taken tail, even when the flag is ground after
  `get64_set64` (e.g. `xor %rax, %rax; jnz; mov`). Stepping halts at the branch.
  Only the spec ports; the multi-instruction example through a conditional does
  not. A branch-aware stepping pass that decides a ground flag condition and
  recurses into the selected continuation would lift this.

- MMIO and DMA are out of scope for the `EStateM X64Exit MachineData` model.
  Master models them (`Kraken/Examples/Increment{MMIO,DMA}.lean`) over the CPS
  `Effects` type: `nonmem_load` carries a continuation `w.type → DataMem → Effects`
  that a `handleEffects` interpreter resumes with a device-supplied value while
  threading a `SystemState = MachineState × DeviceState`. Here a non-memory access
  is `throw (.nonmemLoad …)`, which aborts with no resumption and no device state,
  so a load cannot return a device reply. Porting these needs a device-model
  design: thread device state (a product monad or a state component) and give the
  load access to it, replacing the throwing `MachineData.load`/`store` on the
  non-memory branch. Not a small change.

- Benchmark harness and the current numbers: bench/README.md.
