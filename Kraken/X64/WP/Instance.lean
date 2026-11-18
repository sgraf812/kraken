module

public import Kraken.X64.WP
public import Kraken.X64.Registers
public import Kraken.KVCGen
public import Std.WP
public import Std.Tactic.Do

open Std.WP
open Lean.Order

public theorem Int64.add_sub_self_left (a b : Int64) : a + (b - a) = b := by
  apply Int64.toBitVec_inj.mp
  simp only [Int64.toBitVec_add, Int64.toBitVec_sub]
  rw [BitVec.add_comm, BitVec.sub_add_cancel]

@[expose] public def MachineData.retAddr (t : MachineData) : Option Int64 :=
  (Mem.loadInt t.dmem (t.regs.get64 .rsp) 8).map (fun i => Int64.ofBitVec (BitVec.ofInt 64 i))

@[grind =] public theorem MachineData.retAddr_eq (t : MachineData) :
    t.retAddr = (Mem.loadInt t.dmem (t.regs.get64 .rsp) 8).map
      (fun i => Int64.ofBitVec (BitVec.ofInt 64 i)) := rfl

@[vcgen_simp] public theorem MachineData.retAddr_mk (r z st f d) :
    (MachineData.mk r z st f d).retAddr = (Mem.loadInt d (r.get64 .rsp) 8).map
      (fun i => Int64.ofBitVec (BitVec.ofInt 64 i)) := rfl

namespace Program.WP

public scoped instance instWP [Host] [FunDecls] : WP Program Unit (MachineData → Prop) (Int64 → MachineData → Prop) where
  trans p := PredTrans.mk
    (fun Q E s => Program.wp p (fun st => Q () st.data) (fun st => E st.pc st.data) s)
    (fun hQ hE _ h => Program.wp_mono (fun st => hQ () st.data) (fun st => hE st.pc st.data) h)

public scoped instance [Host] [FunDecls] : WP Directive Unit (MachineData → Prop) (Int64 → MachineData → Prop) where
  trans d := WP.trans (self := instWP) [d]

public scoped instance [Host] [FunDecls] (p : Program) : WPConjunctive p where
  wp_meet_wp_le Q₁ Q₂ E₁ E₂ s h := by
    simp only [WP.trans, PredTrans.apply_mk, meet_apply, meet_prop_eq_and] at h ⊢
    exact Program.wp_mono (fun _ h => by simpa only [meet_apply, meet_prop_eq_and] using h)
      (fun _ h => by simpa only [meet_apply, meet_prop_eq_and] using h) (Program.wp_and h.1 h.2)

public scoped instance [Host] [FunDecls] (d : Directive) : WPConjunctive d where
  wp_meet_wp_le Q₁ Q₂ E₁ E₂ s h := by
    simp only [WP.trans, PredTrans.apply_mk, meet_apply, meet_prop_eq_and] at h ⊢
    exact Program.wp_mono (fun _ h => by simpa only [meet_apply, meet_prop_eq_and] using h)
      (fun _ h => by simpa only [meet_apply, meet_prop_eq_and] using h) (Program.wp_and h.1 h.2)

end Program.WP

namespace Program.WP

public theorem wp_def [Host] [FunDecls] {p : Program}
    {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop} {s : MachineData} :
    WP.wp p Q E s = Program.wp p (fun st => Q () st.data) (fun st => E st.pc st.data) s := by
  simp only [WP.wp, WP.trans, PredTrans.apply_mk]

public theorem wp_directive_def [Host] [FunDecls] {d : Directive}
    {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop} {s : MachineData} :
    WP.wp d Q E s = Program.wp [d] (fun st => Q () st.data) (fun st => E st.pc st.data) s := by
  simp only [WP.wp, WP.trans, PredTrans.apply_mk]

public theorem wp_single [Host] [FunDecls] {d : Directive}
    {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop} {s : MachineData}
    (hw : ∀ (h : Embeds [d]) ⦃P : MachineState → Prop⦄ ⦃next : MachineData → Effects⦄
        ⦃jmp : Int64 → MachineData → Effects⦄,
      (∀ s', Q () s' → (next s').All P) →
      (∀ a s', Host.exe.StepOut (fun a => (FunDecls.at a).map fun f => f.prog.wp (fun _ => False))
        ⟨s, h.embedding.startAddr⟩ (fun u => u.pc = h.embedding.endAddr ∧ Q () u.data)
        (fun u => E u.pc u.data) ⟨s', a⟩ → (jmp a s').All P) →
      (d.interp s ⟨h.embedding.startAddr, h.embedding.endAddr⟩ next jmp).All P) :
    WP.wp d Q E s := by
  rw [wp_directive_def]
  exact Program.wp_single hw

public theorem step1_of_wp_at [Host] [FunDecls] {p : Program} [h : Embeds p] {s : MachineData}
    {post : @Post MachineState} {E : Int64 → MachineData → Prop}
    (hw : WP.wp p (fun _ s' => post ⟨s', h.embedding.endAddr⟩) E s)
    (hE : ∀ a s', E a s' → False := by
      intro _ _ h; first | exact h | exact bot_le (α := Int64 → MachineData → Prop) (fun _ _ => False) _ _ h) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf h.embedding.start⟩ := by
  simp only [WP.wp, WP.trans, PredTrans.apply_mk] at hw
  exact Program.step1_of_wp hw (fun ⟨_, _⟩ hu hq => by subst hu; exact hq)
    (fun u hu => (hE u.pc u.data hu).elim)

public theorem step1_of_wp [Host] [FunDecls] {p : Program} {s : MachineData}
    {post : @Post MachineState} {E : Int64 → MachineData → Prop} (hp : p.IsInfix Host.prog)
    (hw : WP.wp p (fun _ s' => post ⟨s', endAddr hp⟩) E s)
    (hE : ∀ a s', E a s' → False := by
      intro _ _ h; first | exact h | exact bot_le (α := Int64 → MachineData → Prop) (fun _ _ => False) _ _ h) :
    Eventually (step1 Host.exe) post ⟨s, startAddr hp⟩ :=
  @step1_of_wp_at _ _ p (Embeds.ofIsInfix hp) s post E hw hE

end Program.WP
