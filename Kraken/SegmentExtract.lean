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
import Kraken.SegmentWP

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

/-- Cutting the directive list at an address: the segment at the address of
directive `n` is the directive list from the first index `j` that sits at
this address. -/
theorem directivesFromAddress_addrOf_first (e : Executable) (j n : Nat)
    (hjn : j ≤ n) (hn : n ≤ e.2.length) (hj : e.addrOf j = e.addrOf n)
    (hfresh : ∀ k, k < j → e.addrOf k ≠ e.addrOf n) :
    e.directivesFromAddress (e.addrOf n) = e.2.drop j := by
  unfold directivesFromAddress
  congr 1
  apply idxOf_eq_of
  · rw [List.getElem?_map, getElem?_withAddresses e j (by omega), hj]
  · intro k hk
    rw [List.getElem?_map, getElem?_withAddresses e k (by omega)]
    simpa using hfresh k hk

/-- Cutting the directive list at an index whose address is fresh: the
segment at the address of directive `n` is the directive list from `n` on. -/
theorem directivesFromAddress_addrOf (e : Executable) (n : Nat) (hn : n ≤ e.2.length)
    (hfresh : ∀ k, k < n → e.addrOf k ≠ e.addrOf n) :
    e.directivesFromAddress (e.addrOf n) = e.2.drop n :=
  directivesFromAddress_addrOf_first e n n (Nat.le_refl n) hn rfl hfresh

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

/-- A nonempty segment starts at a cell, and the segment is the text from
that cell on. -/
theorem exists_pos_of_directivesFromAddress (e : Executable) {a : Int64}
    (h : e.directivesFromAddress a ≠ []) :
    ∃ k, k < e.2.length ∧ e.addrOf k = a ∧ e.directivesFromAddress a = e.2.drop k := by
  have hlen : (e.withAddresses.map (·.1)).idxOf a < e.2.length := by
    by_cases hk : (e.withAddresses.map (·.1)).idxOf a < e.2.length
    · exact hk
    · exact absurd (by
        show e.directivesFromAddress a = []
        unfold Executable.directivesFromAddress
        exact List.drop_eq_nil_of_le (by omega)) h
  have hwlen : (e.withAddresses.map (·.1)).length = e.2.length + 1 := by
    unfold withAddresses
    simp
  have hwlen2 : e.withAddresses.length = e.2.length + 1 := by
    unfold withAddresses
    simp
  have hidx : (e.withAddresses.map (·.1)).idxOf a < e.withAddresses.length := by omega
  have hget := List.getElem_idxOf (x := a) (xs := e.withAddresses.map (·.1))
    (by rw [List.length_map]; omega)
  have hw := getElem?_withAddresses e ((e.withAddresses.map (·.1)).idxOf a) (by omega)
  rw [List.getElem?_eq_getElem hidx] at hw
  simp only [Option.map_some, Option.some.injEq] at hw
  rw [List.getElem_map] at hget
  exact ⟨(e.withAddresses.map (·.1)).idxOf a, hlen, by rw [← hw, hget], rfl⟩

/-- Coincident addresses have equal byte counts: the total byte count fits
the address space, so `Int64.ofNat` acts injectively on the counts. -/
theorem sizeBefore_eq_of_addrOf_eq (e : Executable) [hv : ValidLayout e] {k n : Nat}
    (heq : e.addrOf k = e.addrOf n) : e.sizeBefore k = e.sizeBefore n := by
  have hbk : e.sizeBefore k < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (sizeBefore_le_sum e k) hv.no_wrap
  have hbn : e.sizeBefore n < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (sizeBefore_le_sum e n) hv.no_wrap
  have hbv : BitVec.ofNat 64 (e.sizeBefore k) = BitVec.ofNat 64 (e.sizeBefore n) := by
    have h4 := congrArg Int64.toBitVec heq
    simp only [addrOf, Int64.toBitVec_add, Int64.toBitVec_ofNat'] at h4
    exact (BitVec.add_right_inj _).mp h4
  have hnat := congrArg BitVec.toNat hbv
  simp only [BitVec.toNat_ofNat] at hnat
  omega

/-- Distinct addresses at a cut point that follows a non-label directive. -/
theorem addrOf_ne_of_valid (e : Executable) [hv : ValidLayout e] {k n : Nat}
    (hk : k < n) (hsome : (e.2[n - 1]?).isSome)
    (hd : ∀ l z, e.2[n - 1]? ≠ some (Directive.label l, z)) :
    e.addrOf k ≠ e.addrOf n := by
  obtain ⟨⟨d, z⟩, hdz⟩ := Option.isSome_iff_exists.mp hsome
  have hz : 0 < z := hv.instr_size _ _ _ hdz (fun l hl => hd l z (by rw [hdz, hl]))
  have h1 : e.sizeBefore k ≤ e.sizeBefore (n - 1) := sizeBefore_mono e (by omega)
  have h2 : e.sizeBefore n = e.sizeBefore (n - 1) + z := by
    have hs := sizeBefore_succ e hdz
    rw [show n - 1 + 1 = n by omega] at hs
    exact hs
  intro heq
  have h3 := sizeBefore_eq_of_addrOf_eq e heq
  omega

/-- The least index that satisfies a predicate, at or below a witness. -/
theorem _root_.Nat.exists_least_le {P : Nat → Prop} {n : Nat} (h : P n) :
    ∃ j, j ≤ n ∧ P j ∧ ∀ k, k < j → ¬P k := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hb : ∃ m, m < n ∧ P m
    · obtain ⟨m, hm, hPm⟩ := hb
      obtain ⟨j, hj, hPj, hmin⟩ := ih m hm hPm
      exact ⟨j, by omega, hPj, hmin⟩
    · exact ⟨n, Nat.le_refl n, h, fun k hk hPk => hb ⟨k, hk, hPk⟩⟩

/-- Between two cut points with one address every cell is a label: a
non-label cell occupies at least one byte and separates the addresses. -/
theorem label_between_of_addrOf_eq (e : Executable) [hv : ValidLayout e] {j k n : Nat}
    (hjk : j ≤ k) (hkn : k < n) (hn : n ≤ e.2.length)
    (heq : e.addrOf j = e.addrOf n) :
    ∃ l z, e.2[k]? = some (Directive.label l, z) := by
  obtain ⟨⟨d, z⟩, hdz⟩ : ∃ dz, e.2[k]? = some dz :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  cases d with
  | label l => exact ⟨l, z, hdz⟩
  | instr i | byteArray a =>
    exfalso
    have hz : 0 < z := hv.instr_size _ _ _ hdz (fun l h => Directive.noConfusion h)
    have h1 : e.sizeBefore j ≤ e.sizeBefore k := sizeBefore_mono e hjk
    have h2 : e.sizeBefore (k + 1) = e.sizeBefore k + z := sizeBefore_succ e hdz
    have h3 : e.sizeBefore (k + 1) ≤ e.sizeBefore n := sizeBefore_mono e hkn
    have h4 := sizeBefore_eq_of_addrOf_eq e heq
    omega

/-- The cut point of the address of index `n`: the segment there starts at
the least index `j` with that address, and every cell from `j` up to `n` is a
label. -/
theorem exists_cut (e : Executable) [ValidLayout e] {n : Nat} (hn : n ≤ e.2.length) :
    ∃ j, j ≤ n ∧ e.directivesFromAddress (e.addrOf n) = e.2.drop j
      ∧ ∀ m, j ≤ m → m < n → ∃ l z, e.2[m]? = some (Directive.label l, z) := by
  obtain ⟨j, hjn, hj, hmin⟩ :=
    Nat.exists_least_le (P := fun k => e.addrOf k = e.addrOf n) rfl
  exact ⟨j, hjn, directivesFromAddress_addrOf_first e j n hjn hn hj hmin,
    fun m hjm hmn => label_between_of_addrOf_eq e hjm hmn hn hj⟩

end Executable

/-- The start address a layout gives a program. -/
theorem _root_.Layout.apply_fst [layout : Layout] (p : Program) :
    (layout p).1 = layout.start := rfl

/-- The directive list a layout gives a program is that program laid out from
position zero. -/
theorem _root_.Layout.apply_snd [layout : Layout] (p : Program) :
    (layout p).2 = Layout.frag 0 p := by simp [Layout.frag, Layout.apply]
