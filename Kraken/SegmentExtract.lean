/-
Partial evaluation of the layout. `Executable.addrOf` names the address of
the directive at an index; `Executable.label_addrOf` computes a label's
address and `Executable.directivesFromAddress_addrOf` cuts the directive list
at an index whose address is fresh, so one `simp` with these two equations
rewrites a straightline judgment's segment into a literal directive list.
`Executable.ValidLayout` packages the facts that make the addresses
well-behaved: labels occupy no bytes, every other directive occupies at least
one, and the program fits in the address space; `addrOf_ne_of_valid`
discharges the freshness hypothesis at any index that follows a non-label
directive.
-/
import Kraken.Semantics

namespace Executable

/-- Bytes occupied by the first `n` directives. -/
def sizeBefore (e : Executable) (n : Nat) : Nat := ((e.2.take n).map (·.2)).sum

/-- The address of the directive at index `n`. -/
def addrOf (e : Executable) (n : Nat) : Int64 := e.1 + .ofNat (e.sizeBefore n)

@[simp] theorem addrOf_zero (e : Executable) : e.addrOf 0 = e.1 := by
  simp [addrOf, sizeBefore]

private theorem int64_ofNat_add (a b : Nat) :
    Int64.ofNat (a + b) = Int64.ofNat a + Int64.ofNat b := by
  apply Int64.toBitVec_inj.mp
  simp

private theorem getElem?_scanl_zero (ds : List (Directive × Nat))
    (t : Int64 × Directive × Nat) :
    (List.scanl (fun (p, _, _) (d, z) => (p + .ofNat z, d, z)) t ds)[0]? = some t := by
  cases ds <;> simp [List.scanl_nil, List.scanl_cons]

private theorem getElem?_scanl_succ :
    ∀ (ds : List (Directive × Nat)) (t : Int64 × Directive × Nat) (k : Nat),
      (List.scanl (fun (p, _, _) (d, z) => (p + .ofNat z, d, z)) t ds)[k + 1]?
        = ds[k]?.map (fun dz => (t.1 + .ofNat ((ds.take (k + 1)).map (·.2)).sum, dz.1, dz.2))
  | [], t, k => by simp [List.scanl_nil]
  | (d, z) :: ds, t, 0 => by
    rw [List.scanl_cons, List.getElem?_cons_succ, getElem?_scanl_zero]
    simp
  | (d, z) :: ds, t, k + 1 => by
    rw [List.scanl_cons, List.getElem?_cons_succ, getElem?_scanl_succ ds _ k,
      List.getElem?_cons_succ]
    simp [Int64.add_assoc]

private theorem getElem?_withAddresses (e : Executable) (k : Nat) (hk : k ≤ e.2.length) :
    e.withAddresses[k]?.map (·.1) = some (e.addrOf k) := by
  unfold withAddresses
  cases k with
  | zero =>
    rw [getElem?_scanl_zero]
    simp [addrOf, sizeBefore]
  | succ m =>
    rw [getElem?_scanl_succ]
    obtain ⟨dz, hdz⟩ : ∃ dz, e.2[m]? = some dz :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rw [hdz]
    simp [addrOf, sizeBefore]

private theorem idxOf_eq_of {α} [BEq α] [LawfulBEq α] {l : List α} {a : α} :
    ∀ {n : Nat}, l[n]? = some a → (∀ k, k < n → l[k]? ≠ some a) → l.idxOf a = n := by
  induction l with
  | nil => intro n hn _; simp at hn
  | cons x xs ih =>
    intro n hn hlt
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hn
      subst hn; simp
    | succ m =>
      have hx : (x == a) = false := by
        have h0 := hlt 0 (Nat.succ_pos m)
        simp only [List.getElem?_cons_zero, ne_eq, Option.some.injEq] at h0
        simpa using h0
      simp only [List.idxOf_cons, hx]
      rw [ih (by simpa using hn) (fun k hk => by simpa using hlt (k + 1) (by omega))]
      simp

/-- Cutting the directive list at an index whose address is fresh: the
segment at the address of directive `n` is the directive list from `n` on. -/
theorem directivesFromAddress_addrOf (e : Executable) (n : Nat) (hn : n ≤ e.2.length)
    (hfresh : ∀ k, k < n → e.addrOf k ≠ e.addrOf n) :
    e.directivesFromAddress (e.addrOf n) = e.2.drop n := by
  unfold directivesFromAddress
  congr 1
  apply idxOf_eq_of
  · rw [List.getElem?_map, getElem?_withAddresses e n hn]
  · intro k hk
    rw [List.getElem?_map, getElem?_withAddresses e k (by omega)]
    simpa using hfresh k hk

private theorem findSome?_eq_of {α β} {f : α → Option β} {l : List α} :
    ∀ {n : Nat} {b : β}, l[n]?.bind f = some b →
      (∀ k, k < n → l[k]?.bind f = none) → l.findSome? f = some b := by
  induction l with
  | nil => intro n b hn _; simp at hn
  | cons x xs ih =>
    intro n b hn hlt
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.bind_some] at hn
      simp [hn]
    | succ m =>
      have h0 : f x = none := by simpa using hlt 0 (Nat.succ_pos m)
      rw [List.findSome?_cons, h0,
        ih (by simpa using hn) (fun k hk => by simpa using hlt (k + 1) (by omega))]

/-- The address of a label: the address of the index holding its first
occurrence, provided the label occupies no bytes there. -/
theorem label_addrOf (e : Executable) (l : Label) (n : Nat)
    (hn : e.2[n]? = some (.label l, 0))
    (hfirst : ∀ dz ∈ e.2.take n, dz.1 ≠ Directive.label l) :
    e.labels.label l = e.addrOf n := by
  replace hfirst : ∀ k, k < n → e.2[k]?.map (·.1) ≠ some (Directive.label l) := by
    intro k hk hcontra
    obtain ⟨dz, hdz⟩ : ∃ dz, e.2[k]? = some dz := by
      rcases h : e.2[k]? with _ | dz
      · rw [h] at hcontra; simp at hcontra
      · exact ⟨dz, rfl⟩
    rw [hdz] at hcontra
    refine hfirst dz (List.mem_iff_getElem?.mpr ⟨k, ?_⟩) (by simpa using hcontra)
    rw [List.getElem?_take_of_lt hk, hdz]
  have hstep : e.1 + .ofNat ((e.2.take (n + 1)).map (·.2)).sum = e.addrOf n := by
    unfold addrOf sizeBefore
    rw [List.take_add_one, hn]
    simp
  show (e.withAddresses.findSome? _).getD (-1) = e.addrOf n
  rw [findSome?_eq_of (n := n + 1) ?hit ?miss]
  · exact rfl
  case hit =>
    show (e.withAddresses[n + 1]?.bind _) = some (e.addrOf n)
    unfold withAddresses
    rw [getElem?_scanl_succ, hn]
    simpa using hstep
  case miss =>
    intro k hk
    show (e.withAddresses[k]?.bind _) = none
    unfold withAddresses
    cases k with
    | zero => rw [getElem?_scanl_zero]; simp
    | succ m =>
      rw [getElem?_scanl_succ]
      rcases hm : e.2[m]? with _ | ⟨d, z⟩
      · simp
      · have hd : d ≠ .label l := by
          have := hfirst m (by omega)
          rw [hm] at this
          simpa using this
        simp [hd]

/-! ## Valid layouts -/

/-- The facts about a laid-out executable that keep its addresses
well-behaved: labels occupy no bytes, every other directive occupies at least
one, and the program fits in the address space. Distinct cut points that
follow a non-label directive then sit at distinct addresses
(`addrOf_ne_of_valid`). -/
class ValidLayout (e : Executable) : Prop where
  label_size : ∀ (i : Nat) l z, e.2[i]? = some (Directive.label l, z) → z = 0
  instr_size : ∀ (i : Nat) d z, e.2[i]? = some (d, z) → (∀ l, d ≠ Directive.label l) → 0 < z
  no_wrap : (e.2.map (·.2)).sum < 2 ^ 64

private theorem sum_map_take_le {α} (f : α → Nat) (l : List α) (k : Nat) :
    ((l.take k).map f).sum ≤ (l.map f).sum := by
  conv => rhs; rw [← List.take_append_drop k l]
  simp only [List.map_append, List.sum_append]
  omega

private theorem sizeBefore_le_sum (e : Executable) (n : Nat) :
    e.sizeBefore n ≤ (e.2.map (·.2)).sum :=
  sum_map_take_le _ e.2 n

private theorem sizeBefore_mono (e : Executable) {k n : Nat} (h : k ≤ n) :
    e.sizeBefore k ≤ e.sizeBefore n := by
  unfold sizeBefore
  rw [show e.2.take k = (e.2.take n).take k by rw [List.take_take, Nat.min_eq_left h]]
  exact sum_map_take_le _ _ k

private theorem sizeBefore_succ (e : Executable) {n : Nat} {d : Directive} {z : Nat}
    (hd : e.2[n]? = some (d, z)) :
    e.sizeBefore (n + 1) = e.sizeBefore n + z := by
  unfold sizeBefore
  rw [List.take_add_one, hd]
  simp

/-- Stepping one directive advances the address by that directive's size. -/
theorem addrOf_succ (e : Executable) {n : Nat} {d : Directive} {z : Nat}
    (hd : e.2[n]? = some (d, z)) : e.addrOf (n + 1) = e.addrOf n + .ofNat z := by
  unfold addrOf
  rw [sizeBefore_succ e hd, int64_ofNat_add, Int64.add_assoc]

/-- Distinct addresses at a cut point that follows a non-label directive. -/
theorem addrOf_ne_of_valid (e : Executable) [hv : ValidLayout e] {k n : Nat}
    (hk : k < n) (hsome : (e.2[n - 1]?).isSome)
    (hd : ∀ l z, e.2[n - 1]? ≠ some (Directive.label l, z)) :
    e.addrOf k ≠ e.addrOf n := by
  obtain ⟨⟨d, z⟩, hdz⟩ := Option.isSome_iff_exists.mp hsome
  have hz : 0 < z := hv.instr_size _ _ _ hdz (fun l hl => hd l z (by rw [hdz, hl]))
  replace hd := hdz
  have h1 : e.sizeBefore k ≤ e.sizeBefore (n - 1) := sizeBefore_mono e (by omega)
  have h2 : e.sizeBefore n = e.sizeBefore (n - 1) + z := by
    have hs := sizeBefore_succ e hdz
    rw [show n - 1 + 1 = n by omega] at hs
    exact hs
  have hbn : e.sizeBefore n < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (sizeBefore_le_sum e n) hv.no_wrap
  intro heq
  have hbv : BitVec.ofNat 64 (e.sizeBefore k) = BitVec.ofNat 64 (e.sizeBefore n) := by
    have h4 := congrArg Int64.toBitVec heq
    simp only [addrOf, Int64.toBitVec_add, Int64.toBitVec_ofNat'] at h4
    exact (BitVec.add_right_inj _).mp h4
  have hnat := congrArg BitVec.toNat hbv
  simp only [BitVec.toNat_ofNat] at hnat
  omega

end Executable

/-- The start address a layout gives a program. -/
theorem _root_.Layout.apply_fst [layout : Layout] (p : Program) :
    (layout p).1 = layout.start := rfl

/-- The directive list a layout gives a program: each directive paired with the
size the layout assigns to its position. -/
theorem _root_.Layout.apply_snd [layout : Layout] (p : Program) :
    (layout p).2 = p.mapIdx (fun i d => (d, layout.size i)) := rfl

/-- Dropping a leading subprogram leaves the rest laid out, with the size table
shifted past it. -/
theorem _root_.Layout.apply_drop [layout : Layout] (as bs : Program) :
    ((layout (as ++ bs)).2).drop as.length
      = bs.mapIdx (fun i d => (d, layout.size (as.length + i))) := by
  simp [Layout.apply_snd, List.mapIdx_append, Nat.add_comm]

