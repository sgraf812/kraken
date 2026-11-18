module

public import Kraken.X64.Semantics
public import Kraken.Data.List.Infix

open Kraken (Layout WellFormedLayout)

private theorem findSome?_eq_of {α β : Type _} {f : α → Option β} {l : List α} :
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

public inductive Instr.IsPadding : Instr → Prop
  | nop {asz osz : Width} {n : Nat} : Instr.IsPadding (.regular asz osz (.nop n))
  | nopalign {asz osz : Width} {a : Nat} {p : Option Nat} : Instr.IsPadding (.regular asz osz (.nopalign a p))

attribute [grind cases] Instr.IsPadding

public class Host where
  prog : Program
  layout : WellFormedLayout prog
  labels_nodup : (Program.labels prog).Nodup

public instance [Host] : WellFormedLayout Host.prog := Host.layout

@[expose] public def Host.exe [Host] : Executable := Host.prog.toExecutable

@[expose] public def Host.addrOf [Host] (k : Nat) : Int64 := Host.exe.addrOf k

public abbrev Host.size [Host] (i : Nat) : Nat := Host.layout.size i

public instance [Host] : Labels := Executable.labels Host.exe

public theorem Host.sizeBefore_eq_of_addrOf_eq [Host] {j k : Nat} (h : Host.addrOf j = Host.addrOf k) :
    Host.exe.sizeBefore j = Host.exe.sizeBefore k :=
  Kraken.Program.sizeBefore_eq_of_addrOf_eq Host.prog h

@[expose] public def Host.startAddr [Host] {p : Program} (h : p.IsInfix Host.prog) : Int64 :=
  Host.addrOf (p.infixIdx Host.prog h)

@[expose] public def Host.endAddr [Host] {p : Program} (h : p.IsInfix Host.prog) : Int64 :=
  Host.addrOf (p.infixIdx Host.prog h + p.length)

export Host (startAddr endAddr)

public theorem Host.label_size [Host] (i : Nat) (l : Label) (h : Host.prog[i]? = some (.label l)) :
    Host.layout.size i = 0 := by
  simp [Kraken.Layout.size, h]

public theorem Host.instr_size_pos [Host] (i : Nat) (ins : Instr) (h : Host.prog[i]? = some (.instr ins))
    (_ : ¬ ins.IsPadding) : 0 < Host.layout.size i := by
  simp [Kraken.Layout.size, h, Host.layout.instrSize_pos]

public theorem Host.exe_getElem? [Host] (i : Nat) :
    Host.exe.program[i]? = Host.prog[i]?.map (fun d => {directive := d, size := Host.layout.size i}) :=
  Kraken.Layout.apply_getElem? Host.prog i

public theorem Host.addrOf_succ [Host] {k : Nat} {d : Directive} (hd : Host.prog[k]? = some d) :
    Host.addrOf (k + 1) = Host.addrOf k + .ofNat (Host.layout.size k) :=
  Kraken.Executable.addrOf_succ _ (c := {directive := d, size := Host.layout.size k}) (by rw [Host.exe_getElem?, hd]; rfl)

section
variable [Host]

public theorem Host.directivesAtAddress_addrOf {k : Nat} {c : Kraken.Sized Directive}
    (hc : Host.exe.program[k]? = some c) (hz : 0 < c.size) :
    ∃ pre : List (Kraken.Sized Directive), Host.exe.directivesAtAddress (Host.addrOf k) = pre ++ [c] ∧
      ∀ c' ∈ pre, ∃ m d', Host.prog[m]? = some d' ∧ c' = {directive := d', size := 0} ∧ Host.layout.size m = 0 := by
  rw [Host.exe_getElem?] at hc
  obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp hc
  exact Kraken.Program.directivesAtAddress_addrOf Host.prog hd hz

end

public theorem Kraken.Executable.label_addrOf (e : _root_.Executable) (l : Label) (n : Nat)
    (hn : e.program[n]? = some {directive := .label l, size := 0})
    (hfirst : ∀ k z, k < n → e.program[k]? ≠ some {directive := .label l, size := z}) :
    (_root_.Executable.labels e).label l = e.addrOf n := by
  show (e.withAddresses.findSome? _).getD (-1) = e.addrOf n
  rw [findSome?_eq_of (n := n)]
  · rfl
  · simp [Kraken.Executable.getElem?_withAddresses_eq, hn, Kraken.Executable.addrOf]
  · intro k hk
    rcases hm : e.program[k]? with _ | ⟨d, z⟩ <;> simp only [Kraken.Executable.getElem?_withAddresses_eq, hm] <;> simp
    rintro rfl
    exact hfirst k z hk hm

public theorem Host.label_eq [Host] {p : Program} {k i : Nat} {l : Label}
    (hp : p.IsInfixAt Host.prog k) (hi : p[i]? = some (.label l)) :
    label l = Host.addrOf (k + i) := by
  obtain ⟨hlt, hpi⟩ := List.getElem?_eq_some_iff.mp hi
  have hP : Host.prog[k + i]? = some (.label l) := by
    rw [List.isInfixAt_iff_getElem?.mp hp i hlt, hpi]
  have hdir : Host.exe.program[k + i]? = some {directive := .label l, size := 0} := by
    rw [Host.exe_getElem?, hP, Host.label_size _ l hP]
    rfl
  refine Kraken.Executable.label_addrOf Host.exe l (k + i) hdir fun m z hm hdm => ?_
  rw [Host.exe_getElem?] at hdm
  obtain ⟨d', hd', heq⟩ := Option.map_eq_some_iff.mp hdm
  simp only [Kraken.Sized.mk.injEq] at heq
  rw [heq.1] at hd'
  exact absurd (Host.labels_nodup.eq_of_getElem?_label hd' hP) (by omega)

public theorem Host.label_ne [Host] {p : Program} {k : Nat} (i j : Nat) {l l' : Label} {ins : Instr}
    (hp : p.IsInfixAt Host.prog k) (hij : i < j := by omega)
    (hi : p[i]? = some (.label l) := by rfl) (hi1 : p[i + 1]? = some (.instr ins) := by rfl)
    (hj : p[j]? = some (.label l') := by rfl) (hpad : ¬ ins.IsPadding := by nofun) :
    label l ≠ label l' := by
  rw [Host.label_eq hp hi, Host.label_eq hp hj]
  intro h
  have hj1 : i + 1 < j := by
    refine Nat.lt_of_le_of_ne hij fun e => ?_
    rw [e, hj] at hi1
    cases hi1
  obtain ⟨hlt, hpm⟩ := List.getElem?_eq_some_iff.mp hi1
  have hP : Host.prog[k + (i + 1)]? = some (.instr ins) := by
    rw [List.isInfixAt_iff_getElem?.mp hp (i + 1) hlt, hpm]
  have hc : Host.exe.program[k + (i + 1)]? =
      some {directive := .instr ins, size := Host.layout.size (k + (i + 1))} := by
    rw [Host.exe_getElem?, hP]
    rfl
  have := Host.exe.sizeBefore_succ hc
  have := Host.exe.sizeBefore_mono (show k + i ≤ k + (i + 1) by omega)
  have := Host.exe.sizeBefore_mono (show k + (i + 1) + 1 ≤ k + j by omega)
  have := Host.instr_size_pos (k + (i + 1)) ins hP hpad
  have := Host.sizeBefore_eq_of_addrOf_eq h
  simp only at *
  omega
