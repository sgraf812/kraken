module

/-
The separation algebra of `MProp` for the cancellation engine `ecancel` of
Kraken/SeparationTactics.lean. `MProp.sepOps` normalizes register reads to
`get64` reads through the writes and word atoms to byte atoms, so the
addresses of a spec's footprint and of a precondition's atoms agree
syntactically. Its split hook pays a footprint at an address inside a region
by `List.AtM_slice`.
-/
public import Kraken.MProp
public import Kraken.SeparationTactics
public import Kraken.Specs

@[expose] public section

open Std.WP
open Lean.Order

/-! ## Regions -/

/-- The offset of `addr` in the region of `L` bytes at `a₀` leaves room for
eight bytes, and the region fits the address space. -/
def MProp.SliceBound (L : List UInt8) (a₀ addr : BitVec 64) : Prop :=
  (addr - a₀).toNat + 8 ≤ L.length ∧ L.length ≤ 2 ^ 64

theorem MProp.SliceBound.intro {L : List UInt8} {a₀ addr : BitVec 64}
    (h8 : (addr - a₀).toNat + 8 ≤ L.length) (hL : L.length ≤ 2 ^ 64) :
    MProp.SliceBound L a₀ addr := ⟨h8, hL⟩

/-- A region holds a slot: the bytes at `a₀` split at the offset of `addr`
into the bytes before, the eight bytes at `addr`, and the bytes after. -/
theorem List.AtM_slice (L : List UInt8) (a₀ addr : BitVec 64)
    (hb : MProp.SliceBound L a₀ addr) :
    L.AtM a₀
      = (L.take (addr - a₀).toNat).AtM a₀
        ∗ (((L.drop (addr - a₀).toNat).take 8).AtM addr
          ∗ (L.drop ((addr - a₀).toNat + 8)).AtM (addr + 8#64)) := by
  obtain ⟨hk, hL⟩ := hb
  have h1 : L = L.take (addr - a₀).toNat ++ L.drop (addr - a₀).toNat :=
    (List.take_append_drop _ L).symm
  have h2 : L.drop (addr - a₀).toNat
      = (L.drop (addr - a₀).toNat).take 8 ++ L.drop ((addr - a₀).toNat + 8) := by
    rw [← List.drop_drop, List.take_append_drop]
  have hlen1 : (L.take (addr - a₀).toNat).length = (addr - a₀).toNat := by
    rw [List.length_take]; omega
  have hlen2 : ((L.drop (addr - a₀).toNat).take 8).length = 8 := by
    rw [List.length_take, List.length_drop]; omega
  have e1 := Mem.At_append_sep (L.take (addr - a₀).toNat) (L.drop (addr - a₀).toNat) a₀
    (by rw [← List.length_append, ← h1]; exact hL)
  have e2 := Mem.At_append_sep ((L.drop (addr - a₀).toNat).take 8)
    (L.drop ((addr - a₀).toNat + 8)) addr
    (by rw [← List.length_append, ← h2, List.length_drop]; omega)
  rw [hlen1, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel] at e1
  rw [hlen2] at e2
  unfold List.AtM MProp.sep
  simp only [MProp.get_mk]
  rw [← e2, ← h2, ← e1, ← h1]

/-! ## The algebra for `ecancel`

`MProp.sepOps` registers the separation algebra of `MProp` with the
cancellation engine. Its normalizer brings register reads to `get64` reads
through the writes and word atoms to byte atoms, so the addresses of a
spec's footprint and of a precondition's atoms agree syntactically; its split
hook pays a footprint at an address inside a region by `List.AtM_slice`. -/

namespace MProp

open Lean Meta in
/-- Normalize the address of an atom to `get64` reads of the initial registers.
The first pass reads a register through writes and spells a scaled index as
a product of words. The second pass reads a register through a register
literal down to the field of the initial registers. The third pass spells
the field read as `get64`. -/
meta def normalizeAddr (a : Expr) : MetaM Simp.Result := do
  let regs := [``Reg64s.get64_r10, ``Reg64s.get64_r11, ``Reg64s.get64_r12, ``Reg64s.get64_r13,
    ``Reg64s.get64_r14, ``Reg64s.get64_r15, ``Reg64s.get64_r8, ``Reg64s.get64_r9,
    ``Reg64s.get64_rax, ``Reg64s.get64_rbp, ``Reg64s.get64_rbx, ``Reg64s.get64_rcx,
    ``Reg64s.get64_rdi, ``Reg64s.get64_rdx, ``Reg64s.get64_rsi, ``Reg64s.get64_rsp]
  let mut writes ← ({} : SimpTheorems).addConst ``Reg64s.get64_set64
  for n in [``eq_self_iff_true, ``BitVec.ofInt_mul, ``BitVec.ofInt_toInt, ``BitVec.add_zero] do
    writes ← writes.addConst n
  let mut fields : SimpTheorems := {}
  for n in regs do
    fields ← fields.addConst n
  let mut back : SimpTheorems := {}
  for n in regs do
    back ← back.addConst n (inv := true)
  let simprocs := #[← Simp.getSimprocs]
  let mut r : Simp.Result := { expr := a }
  for thms in [writes, fields, back] do
    let (r', _) ← Meta.simp r.expr (← Simp.mkContext {} (simpTheorems := #[thms])) (simprocs := simprocs)
    r ← r.mkEqTrans r'
  return r

open Lean Meta in
/-- Normalize the atoms of a `∗`-tree: a word atom becomes the byte atom it
abbreviates, and the address of a byte atom is normalized by `normalizeAddr`.
The bytes of an atom are left as they are. -/
meta partial def normalizeAtoms (e : Expr) : MetaM (Expr × Option Expr) := do
  if e.isAppOfArity ``MProp.sep 3 then
    let (p, hp) ← normalizeAtoms e.appFn!.appArg!
    let (q, hq) ← normalizeAtoms e.appArg!
    if hp.isNone && hq.isNone then return (mkApp2 e.appFn!.appFn! p q, none)
    let f := e.appFn!.appFn!
    let hp ← hp.getDM (mkEqRefl p)
    let hq ← hq.getDM (mkEqRefl q)
    return (mkApp2 f p q, some (← mkCongr (← mkCongrArg f hp) hq))
  let e := if e.isAppOfArity ``UInt64.AtM 3 || e.isAppOfArity ``UInt32.AtM 3
      || e.isAppOfArity ``UInt16.AtM 3 || e.isAppOfArity ``UInt8.AtM 3 then
    mkApp3 (mkConst ``List.AtM) e.appFn!.appFn!.appArg!
      (mkApp (mkConst (e.getAppFn.constName!.getPrefix ++ `toBytes)) e.appFn!.appArg!) e.appArg!
  else e
  unless e.isAppOfArity ``List.AtM 3 do return (e, none)
  let r ← normalizeAddr e.appArg!
  let some h := r.proof? | return (mkApp e.appFn! r.expr, none)
  return (mkApp e.appFn! r.expr, some (← mkCongrArg e.appFn! h))

open Lean Meta in
/-- Pay an address inside a region: split the region atom at the address by
`List.AtM_slice`, with the bound as the side goal. Stored values
(`Int.toBytes …`) are never split. -/
meta def splitAtom (atom addr : Expr) : MetaM (Option (Expr × Expr × MVarId)) := do
  unless atom.isAppOfArity ``List.AtM 3 do return none
  let L := atom.appFn!.appArg!
  if L.isAppOf ``Int.toBytes then return none
  let a₀ := atom.appArg!
  let hb ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``MProp.SliceBound #[L, a₀, addr])
  let heq ← mkAppM ``List.AtM_slice #[L, a₀, addr, hb]
  let some (_, _, sliced) := (← instantiateMVars (← inferType heq)).eq? | return none
  return some (sliced, heq, hb.mvarId!)

open Lean Meta in
meta def sepOps : Kraken.Tactic.SepOps where
  sep := ``MProp.sep
  emp := ``MProp.emp
  isCarrier := fun ty => pure (ty.isAppOfArity ``MProp 1)
  mkSep := fun predType p q => mkAppOptM ``MProp.sep #[predType.appArg!, p, q]
  mkEmp := fun predType => mkAppOptM ``MProp.emp #[predType.appArg!]
  normalize := normalizeAtoms
  split? := splitAtom
  addr? := fun e => if e.isAppOfArity ``List.AtM 3 then some e.appArg! else none

meta initialize Kraken.Tactic.sepOpsRef.modify (sepOps :: ·)

end MProp
