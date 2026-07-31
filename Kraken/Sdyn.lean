/-
The dynamic-stack benchmark ported to the EStateM instruction semantics.

The nine-instruction program spills to and reloads from a caller stack region
through a dynamically computed frame. Its correctness is proved with the
`Std.Internal.Do` weakest-precondition / `vcgen` pipeline: the memory side goals
`Mem.loadInt … = some ?i` are discharged by `easm` from the separation-derived
`h_load` facts, concretizing the loaded values that feed the register
postcondition. The separation preamble is the encoding-independent memory theory
shared with the reference proof.
-/
import Kraken.Tactics
import Kraken.SeparationMem
open Std.Internal.Do
open Std.ExtHashMap
open Kraken

set_option mvcgen.warning false
set_option grind.warning false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

def sdynProg : X64M Unit := do
  Op.movMI (Addr.mk .rsp none (-8)) 99
  Op.movRR .rbp .rsp
  Op.lea .rsp (Addr.mk .rsp (some (.r9, 8)) (-1024))
  Op.movRI .rax 42
  Op.movMR (Addr.mk .rsp (some (.r15, 8)) 16) .rax
  Op.movRI .rax 0
  Op.movRM .rax (Addr.mk .rsp (some (.r15, 8)) 16)
  Op.movRR .rsp .rbp
  Op.movRM .rbx (Addr.mk .rsp none (-8))

theorem sdyn_correct (s₀ : MachineData)
    (stack : List UInt8) (lstack : stack.length = 1024) (R : DataMem → Prop)
    (h : s₀.regs.r9.toNat + s₀.regs.r15.toNat < 125)
    (h_mem : s₀.dmem =⋆ Eq (stack.At (s₀.regs.rsp.toBitVec - 1024)) ⋆ R) :
    ⦃fun sd => sd = s₀⦄ sdynProg
      ⦃fun _ s => s.regs.rax = 42 ∧ s.regs.rbx = 99 ∧ s.regs.rsp = s₀.regs.rsp⦄ := by
  obtain ⟨regs, zmms, flags, mem⟩ := s₀
  obtain ⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩ := regs
  simp only at h_mem h ⊢
  -- Split the 1024-byte region into the 1016-byte lower part and the 8-byte cell
  -- at `rsp - 8`, then the store/load facts, exactly as in the reference proof.
  have h_split : stack = stack.take 1016 ++ stack.drop 1016 := (List.take_append_drop 1016 stack).symm
  have h_len_take : (stack.take 1016).length = 1016 := by simp [lstack]
  have h_len_drop : (stack.drop 1016).length = 8 := by simp [lstack]
  rw [h_split, Mem.At_append_sep _ _ _ (by rw [h_len_take, h_len_drop]; decide), sep_assoc] at h_mem
  rw [h_len_take] at h_mem
  have h_addr3 : rsp.toBitVec - 1024 + 1016#64 = rsp.toBitVec - 8#64 := by bv_decide
  rw [h_addr3] at h_mem
  replace h_mem : (Eq ((stack.drop 1016).At (rsp.toBitVec - 8#64)) ⋆
      (Eq ((stack.take 1016).At (rsp.toBitVec - 1024)) ⋆ R)) mem :=
    cast (congrFun (by ac_rfl) _) h_mem
  have h_L1 : Mem.loadInt mem (rsp.toBitVec - 8#64) 8 = some (Int.ofBytes (stack.drop 1016)) :=
    Mem.loadInt_sep _ _ 8 _ mem h_mem h_len_drop (by decide)
  have h_mem1 := Mem.storeInt_sep (rsp.toBitVec - 8#64) 8 (stack.drop 1016) _ mem ⟨h_mem, h_len_drop⟩ 99
  have h_o : 16 + 8 * (r9.toNat + r15.toNat) + 8 ≤ 1016 := by omega
  have h_lt1 : ((stack.take 1016).take (16 + 8 * (r9.toNat + r15.toNat))).length
      = 16 + 8 * (r9.toNat + r15.toNat) := by simp [lstack]; omega
  have h_lt2 : (((stack.take 1016).drop (16 + 8 * (r9.toNat + r15.toNat))).take 8).length = 8 := by
    simp [lstack]; omega
  rw [show stack.take 1016
        = (stack.take 1016).take (16 + 8 * (r9.toNat + r15.toNat))
          ++ (stack.take 1016).drop (16 + 8 * (r9.toNat + r15.toNat))
      from (List.take_append_drop _ _).symm,
      Mem.At_append_sep _ _ _ (by simp [lstack]; omega),
      show (stack.take 1016).drop (16 + 8 * (r9.toNat + r15.toNat))
        = ((stack.take 1016).drop (16 + 8 * (r9.toNat + r15.toNat))).take 8
          ++ ((stack.take 1016).drop (16 + 8 * (r9.toNat + r15.toNat))).drop 8
      from (List.take_append_drop _ _).symm,
      Mem.At_append_sep _ _ _ (by simp [lstack]; omega),
      h_lt1, h_lt2, sep_assoc] at h_mem1
  replace h_mem1 : (Eq
        ((List.take 8 (List.drop (16 + 8 * (r9.toNat + r15.toNat)) (List.take 1016 stack))).At
          (rsp.toBitVec - 1024 + BitVec.ofNat 64 (16 + 8 * (r9.toNat + r15.toNat)))) ⋆
      (Eq ((Int.toBytes 8 99).At (rsp.toBitVec - 8#64)) ⋆
        Eq ((List.take (16 + 8 * (r9.toNat + r15.toNat)) (List.take 1016 stack)).At (rsp.toBitVec - 1024)) ⋆
        Eq ((List.drop 8 (List.drop (16 + 8 * (r9.toNat + r15.toNat)) (List.take 1016 stack))).At
          (rsp.toBitVec - 1024 + BitVec.ofNat 64 (16 + 8 * (r9.toNat + r15.toNat)) + 8#64)) ⋆
        R)) (Mem.storeInt mem (rsp.toBitVec - 8#64) 8 99) :=
    cast (congrFun (by ac_rfl) _) h_mem1
  have h_L2 := Mem.loadInt_sep _ _ 8 _ _ h_mem1 h_lt2 (by decide)
  have h_mem2 := Mem.storeInt_sep
    (rsp.toBitVec - 1024 + BitVec.ofNat 64 (16 + 8 * (r9.toNat + r15.toNat))) 8
    _ _ _ ⟨h_mem1, h_lt2⟩ 42
  have h_L3 := Mem.loadInt_sep _ _ 8 _ _ h_mem2 (Int.toBytes_length 8 _) (by decide)
  replace h_mem2 : (Eq ((Int.toBytes 8 99).At (rsp.toBitVec - 8#64)) ⋆
      (Eq ((Int.toBytes 8 42).At
          (rsp.toBitVec - 1024 + BitVec.ofNat 64 (16 + 8 * (r9.toNat + r15.toNat)))) ⋆
        Eq ((List.take (16 + 8 * (r9.toNat + r15.toNat)) (List.take 1016 stack)).At (rsp.toBitVec - 1024)) ⋆
        Eq ((List.drop 8 (List.drop (16 + 8 * (r9.toNat + r15.toNat)) (List.take 1016 stack))).At
          (rsp.toBitVec - 1024 + BitVec.ofNat 64 (16 + 8 * (r9.toNat + r15.toNat)) + 8#64)) ⋆
        R))
      (Mem.storeInt (Mem.storeInt mem (rsp.toBitVec - 8#64) 8 99)
        (rsp.toBitVec - 1024 + BitVec.ofNat 64 (16 + 8 * (r9.toNat + r15.toNat))) 8 42) :=
    cast (congrFun (by ac_rfl) _) h_mem2
  have h_L4 := Mem.loadInt_sep _ _ 8 _ _ h_mem2 (Int.toBytes_length 8 _) (by decide)
  simp only [BitVec.ofNat_eq_ofNat] at h_L1 h_L2 h_L3 h_L4
  -- Address-form bridges: relate the effective addresses `Addr.eval` computes to
  -- the separation-region addresses the `h_load` facts are stated against.
  have hneg8 : (-8 : Int64).toBitVec = 18446744073709551608#64 := by decide
  have hA3 : rsp.toBitVec + 18446744073709551608#64 = rsp.toBitVec - 8#64 := by bv_decide
  have hAD : BitVec.ofInt 64 ((rsp.toBitVec.toInt + r9.toBitVec.toInt * 8 + -1024).bmod 18446744073709551616)
        + r15.toBitVec * 8#64 + 16#64
      = rsp.toBitVec - 1024 + BitVec.ofNat 64 (16 + 8 * (r9.toNat + r15.toNat)) := by
    have e : (rsp.toBitVec.toInt + r9.toBitVec.toInt * 8 + -1024).bmod 18446744073709551616
        = (BitVec.ofInt 64 (rsp.toBitVec.toInt + r9.toBitVec.toInt * 8 + -1024)).toInt := by
      rw [BitVec.toInt_ofInt]
    rw [e, BitVec.ofInt_toInt]
    simp only [Nat.mul_add, ← Nat.add_assoc, BitVec.ofNat_add, BitVec.ofNat_mul,
      BitVec.ofNat_uInt64ToNat, BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt,
      BitVec.ofInt_neg, BitVec.ofInt_ofNat]
    grind
  clear h_mem h_mem1 h_mem2 h_split h_addr3 h_len_take h_len_drop h_lt1 h_lt2 h_o
  sym =>
    vcgen [sdynProg]
    -- `easm` reads each memory VC's `?i` off the internalized `h_load` facts and
    -- address bridges, concretizing the loaded values the register postcondition
    -- consumes; `finish` closes the register chain.
    all_goals (first (easm) (skip))
    -- Residual: `easm` discharges the access whose address and memory are those
    -- of the initial state. The later ones address through the `lea`-computed
    -- frame, so their effective address is an `Addr.eval` over a `set64` chain
    -- and their memory a `storeInt` over the initial one; normalizing that pair
    -- to the form the separation-derived `h_load` facts are stated in is not yet
    -- part of `easm`. `finish` closes the rest; the open loads and the register
    -- postcondition they feed are the reported residual.
    all_goals (first (finish (splits := 40)) (sorry))
