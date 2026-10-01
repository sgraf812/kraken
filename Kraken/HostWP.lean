module

/- The run of a fragment inside the executable that hosts it. -/
public import Kraken.StateCfg

@[expose] public section

open Std.WP
open Lean.Order

/-- The executable that hosts the fragment under verification. -/
class Host where
  exe : Executable

namespace HostWP

variable [layout : Layout] [host : Host]

def burst (k : Nat) (s : MachineData) (post : MachineState → Prop) : Prop :=
  (@Directives.interp (Executable.labels Host.exe) (Host.exe.2.drop k) s (Host.exe.addrOf k)
    fun pc s => .done (s, pc)).All (Eventually (straightlineStep Host.exe) post)

/-- `q` sits at index `k` of the host. It falls through to the burst from `k + q.length`, or
exits at an address. -/
def run (q : Program) (Q : MachineData → Prop) (E : Int64 → MachineData → Prop)
    (s : MachineData) : Prop :=
  ∀ k post, q <+: (Host.exe.2.map (·.1)).drop k →
    (∀ s', Q s' → burst (k + q.length) s' post) →
    (∀ a s', E a s' → Eventually (straightlineStep Host.exe) post (s', a)) →
    burst k s post

theorem run_mono {q : Program} {Q₁ Q₂ : MachineData → Prop}
    {E₁ E₂ : Int64 → MachineData → Prop} (hQ : ∀ s, Q₁ s → Q₂ s)
    (hE : ∀ a s, E₁ a s → E₂ a s) {s : MachineData} (h : run q Q₁ E₁ s) : run q Q₂ E₂ s :=
  fun k post hs hQ₂ hE₂ =>
    h k post hs (fun s' h' => hQ₂ s' (hQ s' h')) (fun a s' h' => hE₂ a s' (hE a s' h'))

scoped instance : Labels := Executable.labels Host.exe

scoped instance instWP : WP Program Unit (MachineData → Prop) (Int64 → MachineData → Prop) where
  trans q := ⟨fun Q E s => run q (Q ()) E s⟩
  trans_monotone _ := fun _ _ _ _ hE hQ _ h => run_mono (hQ ()) hE h

scoped instance : WP Directive Unit (MachineData → Prop) (Int64 → MachineData → Prop) where
  trans d := WP.trans (self := instWP) [d]
  trans_monotone d := WP.trans_monotone (self := instWP) [d]

theorem triple_directive {d : Directive} {pre : MachineData → Prop}
    {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop} :
    (⦃ pre ⦄ d ⦃ Q; E ⦄) ↔ (⦃ pre ⦄ [d] ⦃ Q; E ⦄) :=
  ⟨fun h => ⟨h.1⟩, fun h => ⟨h.1⟩⟩

theorem cons_prefix_drop {α : Type} {d : α} {q L : List α} {k : Nat} (h : (d :: q) <+: L.drop k) :
    L[k]? = some d ∧ q <+: L.drop (k + 1) := by
  obtain ⟨t, ht⟩ := h
  have hk : L.drop k = d :: (q ++ t) := ht.symm
  refine ⟨?_, t, ?_⟩
  · simpa [List.head?_drop] using congrArg List.head? hk
  · rw [← List.drop_drop, hk]
    rfl

theorem cell_of_prefix {d : Directive} {q : Program} {k : Nat}
    (h : (d :: q) <+: (Host.exe.2.map (·.1)).drop k) : ∃ z, Host.exe.2[k]? = some (d, z) := by
  have hd := (cons_prefix_drop h).1
  rw [List.getElem?_map] at hd
  cases hc : Host.exe.2[k]? with
  | none => rw [hc] at hd; cases hd
  | some c =>
    rw [hc] at hd
    obtain ⟨d', z⟩ := c
    cases hd
    exact ⟨z, rfl⟩

theorem burst_cell {k : Nat} {d : Directive} {z : Nat} (hd : Host.exe.2[k]? = some (d, z))
    (s : MachineData) (post : MachineState → Prop) :
    burst k s post =
      (@Directive.interp (Executable.labels Host.exe) d s
        ⟨Host.exe.addrOf k, Host.exe.addrOf (k + 1)⟩
        (fun s' => @Directives.interp (Executable.labels Host.exe) (Host.exe.2.drop (k + 1)) s'
          (Host.exe.addrOf (k + 1)) fun pc s => .done (s, pc))
        (fun pc s => .done (s, pc))).All (Eventually (straightlineStep Host.exe) post) := by
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hd
  unfold burst
  rw [List.drop_eq_getElem_cons hlt, hget, Kraken.Executable.addrOf_succ _ hd]
  rfl

theorem burst_label {k : Nat} {l : Label} {z : Nat}
    (hd : Host.exe.2[k]? = some (Directive.label l, z)) (s : MachineData)
    (post : MachineState → Prop) : burst k s post = burst (k + 1) s post := by
  rw [burst_cell hd]
  rfl

theorem burst_end {k : Nat} (hk : Host.exe.2.length ≤ k) {s : MachineData}
    {post : MachineState → Prop} (h : ∀ pc, post (s, pc)) : burst k s post := by
  unfold burst
  rw [List.drop_eq_nil_of_le hk]
  exact Eventually.done _ (h _)

variable {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}

@[spec] theorem nil_spec : ⦃ fun s => Q () s ⦄ ([] : Program) ⦃ Q; E ⦄ :=
  ⟨fun _ hpre _ _ _ hQ _ => hQ _ hpre⟩

@[spec] theorem cons_spec (d : Directive) (p : Program) :
    ⦃ WP.wp d (fun _ => WP.wp p Q E) E ⦄ (d :: p) ⦃ Q; E ⦄ := by
  refine ⟨fun s h k post hs hQ hE => ?_⟩
  have hp := (cons_prefix_drop hs).2
  refine h k post ((List.prefix_append [d] p).trans hs) (fun s' h' => ?_) hE
  have hidx : k + (d :: p).length = k + 1 + p.length := by simp only [List.length_cons]; omega
  exact h' (k + 1) post hp (fun s'' h'' => hidx ▸ hQ s'' h'') hE

/-! ## Every state run is a host run -/

theorem endPc_addrOf {k : Nat} {cs : List (Directive × Nat)} (h : cs <+: Host.exe.2.drop k) :
    Program.endPc (Host.exe.addrOf k) (cs.map (·.2)) = Host.exe.addrOf (k + cs.length) := by
  induction cs generalizing k with
  | nil => rfl
  | cons c cs ih =>
    obtain ⟨hc, hcs⟩ := cons_prefix_drop h
    obtain ⟨d, z⟩ := c
    have hstep : Program.endPc (Host.exe.addrOf k) (((d, z) :: cs).map (·.2))
        = Program.endPc (Host.exe.addrOf k + .ofNat z) (cs.map (·.2)) := rfl
    rw [hstep, ← Kraken.Executable.addrOf_succ _ hc, ih hcs, List.length_cons]
    congr 1
    omega

theorem run_of_stateRun {q : Program} {Q : MachineData → Prop} {E : Int64 → MachineData → Prop}
    {s : MachineData} (h : @Program.run (Executable.labels Host.exe) q Q E s) : run q Q E s := by
  intro k post hs hQ hE
  have hds : ((Host.exe.2.drop k).take q.length).map (·.1) = q := by
    rw [List.map_take, List.map_drop]
    exact (List.prefix_iff_eq_take.mp hs).symm
  have hlen : ((Host.exe.2.drop k).take q.length).length = q.length := by
    rw [← List.length_map (f := (·.1)), hds]
  have hsplit : Host.exe.2.drop k
      = (Host.exe.2.drop k).take q.length ++ Host.exe.2.drop (k + q.length) := by
    conv => lhs; rw [← List.take_append_drop q.length (Host.exe.2.drop k)]
    rw [List.drop_drop]
  unfold burst
  rw [hsplit]
  refine h _ _ _ _ hds (fun s' hq => ?_) hE
  rw [endPc_addrOf (List.take_prefix _ _), hlen]
  exact hQ s' hq

theorem lift {d : Directive} {pre : MachineData → Prop} {Q : Unit → MachineData → Prop}
    {E : Int64 → MachineData → Prop}
    (h : ∀ s, pre s → Program.run [d] (Q ()) E s) : ⦃ pre ⦄ d ⦃ Q; E ⦄ :=
  triple_directive.mpr ⟨fun s hpre => run_of_stateRun (h s hpre)⟩

local macro "lift_state " n:ident : tactic =>
  `(tactic| (refine HostWP.lift (StateWP.run_of_triple ?_); apply $(Lean.mkIdent (`StateWP ++ n.getId))))

@[spec] theorem mov_reg_imm_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s => Q () { s with regs := s.regs.set64 r (BitVec.setWidth 64 i.toBitVec) } ⦄
      Directive.instr (.regular asz .W64 (.mov (.reg (.low r .W64)) (.imm (.int64 i))))
    ⦃ Q ⦄ := by
  lift_state mov_reg_imm_spec

@[spec] theorem mov_store_reg_spec (b : Reg64) (d : Int64) (rs : Reg64) :
    ⦃ fun s => ((Mem.loadInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 8).isSome = true)
        ⊓ Q () { s with
            dmem := Mem.storeInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 8
              (s.regs.get64 rs).toInt } ⦄
      Directive.instr (.regular .W64 .W64
          (.mov (.mem ⟨some (.reg b), none, .int64 d⟩)
            (.regOrMem (.reg (.low rs .W64)))))
    ⦃ Q ⦄ := by
  lift_state mov_store_reg_spec

@[spec] theorem add_reg_mem_spec (rd b : Reg64) (d : Int64) :
    ⦃ fun s => ((Mem.loadInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 8).isSome = true)
        ⊓ ∀ i, Mem.loadInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 8 = some i →
          let a := BitVec.ofInt 64 i
          let bv := s.regs.get64 rd
          let v := a + bv
          Q () { s with
            regs := s.regs.set64 rd v
            status := StatusFlags.from_result v
              { cf := v.unsigned != a.unsigned + bv.unsigned,
                af := (v.take 4).unsigned != (a.take 4).unsigned + (bv.take 4).unsigned,
                of := v.signed != a.signed + bv.signed } } ⦄
      Directive.instr (.regular .W64 .W64
          (.add (.reg (.low rd .W64))
            (.regOrMem (.mem ⟨some (.reg b), none, .int64 d⟩))))
    ⦃ Q ⦄ := by
  lift_state add_reg_mem_spec

@[spec] theorem label_spec (l : Label) : ⦃ fun s => Q () s ⦄ Directive.label l ⦃ Q ⦄ := by
  lift_state label_spec

@[spec] theorem nop_spec (asz osz : Width) (n : Nat) :
    ⦃ fun s => Q () s ⦄ Directive.instr (.regular asz osz (.nop n)) ⦃ Q ⦄ := by
  lift_state nop_spec

@[spec] theorem sub_reg_imm_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let b := s.regs.get64 r
        let a := BitVec.setWidth 64 i.toBitVec
        let v := b - a
        Q () { s with
          regs := s.regs.set64 r v
          status := StatusFlags.from_result v
            { cf := v.unsigned != b.unsigned - a.unsigned,
              af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned,
              of := v.signed != b.signed - a.signed } } ⦄
      Directive.instr (.regular asz .W64 (.sub (.reg (.low r .W64)) (.imm (.int64 i))))
    ⦃ Q ⦄ := by
  lift_state sub_reg_imm_spec

@[spec] theorem mulx_reg_spec (asz : Width) (hi lo rs : Reg64) :
    ⦃ fun s =>
        let v := (s.regs.get64 rs).unsigned * (s.regs.get64 .rdx).unsigned
        Q () { s with regs :=
          (s.regs.set64 lo (BitVec.ofInt 64 v)).set64 hi (BitVec.ofInt 64 (v >>> 64)) } ⦄
      Directive.instr (.regular asz .W64
          (.mulx (.low hi .W64) (.low lo .W64) (.reg (.low rs .W64))))
    ⦃ Q ⦄ := by
  lift_state mulx_reg_spec

@[spec] theorem add_reg_imm_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let a := BitVec.setWidth 64 i.toBitVec
        let b := s.regs.get64 r
        let v := a + b
        Q () { s with
          regs := s.regs.set64 r v
          status := StatusFlags.from_result v
            { cf := v.unsigned != a.unsigned + b.unsigned,
              af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned,
              of := v.signed != a.signed + b.signed } } ⦄
      Directive.instr (.regular asz .W64 (.add (.reg (.low r .W64)) (.imm (.int64 i))))
    ⦃ Q ⦄ := by
  lift_state add_reg_imm_spec

@[spec] theorem adc_reg_reg_spec (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        let a := s.regs.get64 rs
        let b := s.regs.get64 rd
        let c := s.status.cf
        let v := a + b + BitVec.ofNat 64 c.toNat
        Q () { s with
          regs := s.regs.set64 rd v
          status := StatusFlags.from_result v
            { cf := v.unsigned != a.unsigned + b.unsigned + c,
              af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned + c,
              of := v.signed != a.signed + b.signed + c } } ⦄
      Directive.instr (.regular asz .W64
          (.adc (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64)))))
    ⦃ Q ⦄ := by
  lift_state adc_reg_reg_spec

@[spec] theorem xor_reg_reg_spec (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        let v := s.regs.get64 rd ^^^ s.regs.get64 rs
        ∀ af : Bool, Q () { s with
          regs := s.regs.set64 rd v
          status := StatusFlags.from_result v { cf := false, of := false, af } } ⦄
      Directive.instr (.regular asz .W64
          (.xor (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64)))))
    ⦃ Q ⦄ := by
  lift_state xor_reg_reg_spec

@[spec] theorem dec_reg_spec (asz : Width) (r : Reg64) :
    ⦃ fun s =>
        let a := s.regs.get64 r
        let v := a - 1
        Q () { s with
          regs := s.regs.set64 r v
          status := StatusFlags.from_result v
            { cf := s.status.cf,
              af := (v.take 4).unsigned != (a.take 4).unsigned - 1,
              of := v.signed != a.signed - 1 } } ⦄
      Directive.instr (.regular asz .W64 (.dec (.reg (.low r .W64))))
    ⦃ Q ⦄ := by
  lift_state dec_reg_spec

@[spec] theorem jmp_label_spec (asz osz : Width) (l : Label) :
    ⦃ fun s => E (Labels.label l) s ⦄
      Directive.instr (.regular asz osz (.jmp (.rel (.sub (.label l) .after_current_instruction))))
    ⦃ Q; E ⦄ := by
  lift_state jmp_label_spec

@[spec] theorem jcc_spec (asz osz : Width) (cc : CondCode) (l : Label) :
    ⦃ fun s => (cc.interp s.status = true → E (Labels.label l) s) ⊓ (cc.interp s.status = false → Q () s) ⦄
      Directive.instr (.regular asz osz (.jcc cc l))
    ⦃ Q; E ⦄ := by
  lift_state jcc_spec

@[spec] theorem ret_spec (asz osz : Width) :
    ⦃ fun s => (s.retAddr.isSome = true)
        ⊓ (∀ ra, s.retAddr = some ra →
            E ra { s with regs := s.regs.set64 .rsp (s.regs.get64 .rsp + 8#64) }) ⦄
      Directive.instr (.regular asz osz .ret)
    ⦃ Q; E ⦄ := by
  lift_state ret_spec

/-! ## Calls -/

def _root_.MachineData.pushRa (s : MachineData) (ra : Int64) : MachineData :=
  { s with regs := s.regs.set64 .rsp (s.regs.get64 .rsp - 8#64),
           dmem := Mem.storeInt s.dmem (s.regs.get64 .rsp - 8#64) 8 ra.toBitVec.toInt }

@[grind =] theorem _root_.MachineData.regs_pushRa (s : MachineData) (ra : Int64) :
    (s.pushRa ra).regs = s.regs.set64 .rsp (s.regs.get64 .rsp - 8#64) := rfl

@[grind =] theorem _root_.MachineData.dmem_pushRa (s : MachineData) (ra : Int64) :
    (s.pushRa ra).dmem = Mem.storeInt s.dmem (s.regs.get64 .rsp - 8#64) 8 ra.toBitVec.toInt := rfl

@[grind =] theorem _root_.Mem.loadInt_storeInt_64 (m : DataMem) (a : BitVec 64) (v : Int) :
    (m.storeInt a 8 v).loadInt a 8 = some (Int.ofBytes (Int.toBytes 8 v)) :=
  Mem.loadInt_storeInt m a _ v (by decide)

@[grind =] theorem _root_.Int64.ofBitVec_ofBytes_toBytes (ra : Int64) :
    Int64.ofBitVec (BitVec.ofInt 64 (Int.ofBytes (Int.toBytes 8 ra.toBitVec.toInt))) = ra := by
  rw [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec]

@[grind =] theorem _root_.MachineData.retAddr_pushRa (s : MachineData) (ra : Int64) :
    (s.pushRa ra).retAddr = some ra := by
  simp only [MachineData.retAddr, MachineData.pushRa, Reg64s.get64_set64, reduceIte,
    Mem.loadInt_storeInt _ _ _ _ (by decide : 8 ≤ 2 ^ 64), Option.map_some,
    BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec]

/-- Entering the host at the address of index `k` runs the host from index `k`. -/
def Placed : Prop :=
  ∀ k s post, burst k s post → Eventually (straightlineStep Host.exe) post (s, Host.exe.addrOf k)

structure Contract where
  f : Label
  Pre : MachineData → Prop
  Post : MachineData → MachineData → Prop

/-- The code at `c.f`, entered with a return address `ra` on the stack, returns to `ra`. -/
def Contract.Implemented (c : Contract) : Prop :=
  ∀ s ra, c.Pre s →
    Eventually (straightlineStep Host.exe) (fun st => st.2 = ra ∧ c.Post s st.1)
      (s.pushRa ra, Labels.label c.f)

theorem _root_.Int64.add_sub_self_left (a b : Int64) : a + (b - a) = b := by
  apply Int64.toBitVec_inj.mp
  simp only [Int64.toBitVec_add, Int64.toBitVec_sub]
  rw [BitVec.add_comm, BitVec.sub_add_cancel]

@[spec] theorem call_spec (asz osz : Width) (c : Contract) :
    ⦃ fun s => (Placed ∧ c.Implemented)
        ⊓ ((Mem.loadInt s.dmem (s.regs.get64 .rsp - 8#64) 8).isSome = true)
        ⊓ c.Pre s ⊓ (∀ s', c.Post s s' → Q () s') ⦄
      Directive.instr (.regular asz osz (.call (.rel (.sub (.label c.f) .after_current_instruction))))
    ⦃ Q; E ⦄ := by
  refine triple_directive.mpr ⟨fun s hpre k post hs hQ _ => ?_⟩
  obtain ⟨z, hz⟩ := cell_of_prefix hs
  rw [burst_cell hz]
  simp only [meet_prop_eq_and] at hpre
  obtain ⟨⟨⟨⟨hplaced, himpl⟩, hmapped⟩, hpre⟩, hcont⟩ := hpre
  obtain ⟨i, hload⟩ := Option.isSome_iff_exists.mp hmapped
  simp only [Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp,
    ConstExpr.interp, MachineData.store, Width.bytesv_W64, hload, Effects.All]
  rw [Int64.ofBitVec_toBitVec, Int64.add_sub_self_left]
  refine eventually_trans _ _ _ _ (himpl s _ hpre) ?_
  rintro ⟨s'', a⟩ ⟨rfl, hpost⟩
  exact hplaced (k + 1) s'' post (hQ s'' (hcont s'' hpost))

/-! ## Placement -/

theorem placed_of_valid [hv : Kraken.Executable.ValidLayout Host.exe] : Placed := by
  intro k s post h
  by_cases hk : k ≤ Host.exe.2.length
  · obtain ⟨j, hjk, hdir, hlab⟩ := Kraken.Executable.exists_cut Host.exe hk
    refine Eventually.step _ _ ?_ fun _ h => h
    rw [straightlineStep_eq_interp]
    dsimp only
    have hsplit : Host.exe.2.drop j = (Host.exe.2.drop j).take (k - j) ++ Host.exe.2.drop k := by
      conv => lhs; rw [← List.take_append_drop (k - j) (Host.exe.2.drop j)]
      rw [List.drop_drop, show j + (k - j) = k by omega]
    letI : Labels := Executable.labels Host.exe
    rw [hdir, hsplit, Directives.interp_labels_append]
    · exact h
    · intro c hc
      obtain ⟨m, hm, hcm⟩ := List.getElem_of_mem hc
      simp only [List.length_take, List.length_drop] at hm
      have hmc : Host.exe.2[j + m]? = some c := by
        rw [← hcm, List.getElem?_eq_getElem (by omega)]
        simp [List.getElem_take, List.getElem_drop]
      obtain ⟨l, z, hlz⟩ := hlab (j + m) (by omega) (by omega)
      rw [hmc] at hlz
      cases hlz
      exact ⟨rfl, hv.label_size (j + m) l z hmc⟩
  · unfold burst at h
    rw [List.drop_eq_nil_of_le (by omega)] at h
    exact h

/-! ## Reading the wp back as the baseline judgment -/

theorem text_layout {p : Program} : (layout p).2.map (·.1) = p := by
  rw [Layout.apply_snd, Layout.frag_map_fst]

theorem eventually_of_burst {p : Program} (hhost : Host.exe = layout p) {s : MachineData}
    {post : MachineState → Prop} (h : burst 0 s post) :
    Eventually (straightlineStep (layout p)) post (s, layout.start) := by
  obtain ⟨e⟩ := host
  change e = _ at hhost
  subst hhost
  refine Eventually.step _ _ ?_ fun _ h => h
  rw [straightlineStep_eq_interp]
  dsimp only
  rw [Kraken.Executable.directivesFromStart]
  unfold burst at h
  simpa [Layout.apply_snd, Layout.frag, Kraken.Executable.addrOf_zero, Layout.apply_fst] using h

omit host in
theorem eventually_of_wp {p : Program} {s : MachineData} {post : MachineState → Prop}
    (h : ∀ [Host], Host.exe = layout p → ⊤ ⊑ WP.wp p (fun _ s' => ∀ pc, post (s', pc)) ⊥ s) :
    Eventually (straightlineStep (layout p)) post (s, layout.start) := by
  letI : Host := ⟨layout p⟩
  refine eventually_of_burst rfl (of_top_le_prop (h rfl) 0 post ?_ (fun _ hq => burst_end ?_ hq)
    (fun a s' hE => ((bot_le (α := Int64 → MachineData → Prop) fun _ _ => False) a s' hE).elim))
  · show p <+: ((layout p).2.map (·.1)).drop 0
    rw [text_layout, List.drop_zero]
    exact List.prefix_refl _
  · show (layout p).2.length ≤ _
    simp [Layout.apply_snd]

theorem implemented_of_triple {P body rest : Program} [Kraken.Executable.ValidLayout Host.exe]
    (hhost : Host.exe = layout P) (hnd : (Program.labels P).Nodup) (c : Contract)
    (hat : Program.fromLabel P c.f = Directive.label c.f :: (body ++ rest))
    (hbody : ∀ s ra, ⦃ fun t => t = s.pushRa ra ∧ c.Pre s ⦄ body
      ⦃ (fun _ _ => False); fun a s' => a = ra ∧ c.Post s s' ⦄) :
    c.Implemented := by
  have hplaced : Placed := placed_of_valid
  obtain ⟨e⟩ := host
  change e = _ at hhost
  subst hhost
  letI : Host := ⟨layout P⟩
  intro s ra hpre
  have hdrop := Program.drop_fromLabel P c.f
  rw [Program.label_addrOf_drop hnd hdrop (by rw [hat]; exact List.cons_ne_nil _ _)]
  generalize P.length - (Program.fromLabel P c.f).length = i at hdrop
  rw [hat] at hdrop
  have hcell : P[i]? = some (Directive.label c.f) := by
    simpa [List.head?_drop] using congrArg List.head? hdrop
  have hcell' : (layout P).2[i]? = some (Directive.label c.f, Kraken.Layout.size Directive i) := by
    rw [Layout.apply_getElem?, hcell]; rfl
  refine hplaced i _ _ ?_
  rw [burst_label hcell']
  refine (hbody s ra).1 _ ⟨rfl, hpre⟩ (i + 1) _ ?_ (fun _ h => h.elim) ?_
  · show body <+: ((layout P).2.map (·.1)).drop (i + 1)
    rw [text_layout, ← List.drop_drop, hdrop]
    exact List.prefix_append _ _
  · rintro a s' ⟨rfl, hpost⟩
    exact Eventually.done _ ⟨rfl, hpost⟩

/-! ## The control-flow rule -/

omit host in
theorem cfg {p p' : Program} {l₀ : Label} {post : MachineState → Prop}
    [Kraken.Executable.ValidLayout (layout p)]
    (T : Label → MachineData → Prop) (var : Label → MachineData → Nat := fun _ _ => 0)
    (hblocks : ∀ [Host], Host.exe = layout p → ∀ l blk, Program.blockAt p l = some blk → ∀ n : Nat,
      ⦃ fun s => T l s ∧ var l s = n ⦄
        blk.body
      ⦃ (match blk.next with
         | some l' => fun _ s => T l' s ∧ var l' s ≤ n
         | none => fun _ s => ∀ pc, post (s, pc));
        fun a s => ∃ l', Labels.label l' = a
          ∧ (Program.blockAt p l').isSome ∧ T l' s ∧ Program.EdgeLt p var l n l' s ⦄)
    (hp : p = Directive.label l₀ :: p' := by rfl) (hwf : Program.WF p := by decide) :
    ∀ s, T l₀ s → Eventually (straightlineStep (layout p)) post (s, layout.start) := by
  letI : Host := ⟨layout p⟩
  have hplaced : Placed := placed_of_valid
  have hstart := @eventually_of_burst _ _ p rfl
  specialize hblocks rfl
  have hnd := hwf.nodup
  have hK : ∀ l, Program.blockIdx p l ≤ (Program.view p).2.length := Program.blockIdx_le p
  have key : ∀ x : Label × MachineData, (Program.blockAt p x.1).isSome → T x.1 x.2 →
      burst (p.length - (Program.fromLabel p x.1).length) x.2 post := by
    intro x
    induction x using (measure (Program.cfgMeasure p var)).wf.induction with
    | _ x ih =>
      obtain ⟨l, s⟩ := x
      intro hsome hT
      dsimp only at hsome hT ⊢
      obtain ⟨blk, hblk⟩ := Option.isSome_iff_exists.mp hsome
      have htext := Program.fromLabel_block hnd hblk
      have hlen := congrArg List.length htext
      simp only [List.length_cons, List.length_append] at hlen
      have hdrop := Program.drop_fromLabel p l
      have hsuf : (Program.fromLabel p l).length ≤ p.length := by
        have := congrArg List.length hdrop
        simp only [List.length_drop] at this
        omega
      generalize hi : p.length - (Program.fromLabel p l).length = i at hdrop
      rw [htext] at hdrop
      have hcell : p[i]? = some (Directive.label l) := by
        simpa [List.head?_drop] using congrArg List.head? hdrop
      have hcell' : (layout p).2[i]? = some (Directive.label l, Kraken.Layout.size Directive i) := by
        rw [Layout.apply_getElem?, hcell]; rfl
      have hbody : blk.body <+: ((layout p).2.map (·.1)).drop (i + 1) := by
        rw [text_layout, ← List.drop_drop, hdrop]
        exact List.prefix_append _ _
      rw [burst_label hcell']
      refine ((hblocks l blk hblk (var l s)).1 s ⟨hT, rfl⟩) (i + 1) post hbody
        (fun s' hq => ?_) (fun a s' hE => ?_)
      · cases hn : blk.next with
        | none =>
          rw [hn] at hq hlen
          refine burst_end ?_ hq
          show (layout p).2.length ≤ _
          simp only [Option.elim, List.length_nil] at hlen
          simp only [Layout.apply_snd, Layout.frag, List.length_mapIdx]
          omega
        | some l' =>
          rw [hn] at hq hlen
          obtain ⟨hT', hvar⟩ := hq
          obtain ⟨hsome', hidx'⟩ := Program.blockAt_next hnd hblk hn
          simp only [Option.elim] at hlen
          rw [show i + 1 + blk.body.length = p.length - (Program.fromLabel p l').length by omega]
          refine ih (l', s') ?_ hsome' hT'
          have hK' := hK l'
          show Program.cfgMeasure p var (l', s') < Program.cfgMeasure p var (l, s)
          unfold Program.cfgMeasure
          dsimp only
          have hmul : var l' s' * ((Program.view p).2.length + 1)
              ≤ var l s * ((Program.view p).2.length + 1) :=
            Nat.mul_le_mul_right _ hvar
          omega
      · obtain ⟨l', hlab, hsome', hT', hedge⟩ := hE
        subst hlab
        have hne : Program.fromLabel p l' ≠ [] := by
          obtain ⟨blk', hblk'⟩ := Option.isSome_iff_exists.mp hsome'
          rw [Program.fromLabel_block hnd hblk']
          exact List.cons_ne_nil _ _
        rw [Program.label_addrOf_drop hnd (Program.drop_fromLabel p l') hne]
        refine hplaced _ _ _ (ih (l', s') ?_ hsome' hT')
        have hK' := hK l'
        show Program.cfgMeasure p var (l', s') < Program.cfgMeasure p var (l, s)
        unfold Program.cfgMeasure
        dsimp only
        rcases hedge with hlt | ⟨heq, hij⟩
        · have hmul : (var l' s' + 1) * ((Program.view p).2.length + 1)
              ≤ var l s * ((Program.view p).2.length + 1) :=
            Nat.mul_le_mul_right _ hlt
          have hsucc : (var l' s' + 1) * ((Program.view p).2.length + 1)
              = var l' s' * ((Program.view p).2.length + 1)
                + ((Program.view p).2.length + 1) := Nat.succ_mul _ _
          omega
        · rw [heq]
          omega
  intro s hT
  have h0 : (Program.blockAt p l₀).isSome := by
    rw [hp]
    show (Program.blockAtAux (Program.view (Directive.label l₀ :: p')).2 l₀).isSome = true
    simp [Program.view, Program.blockAtAux]
  have hfl : Program.fromLabel p l₀ = p := by
    have hnot : Program.fromLabel p' l₀ = [] := Classical.byContradiction fun hne => by
      have hmem := Program.mem_labels_of_cell (Program.fromLabel_mem hne)
      have hnd' := hnd
      rw [hp] at hnd'
      simp only [Program.labels] at hnd'
      exact (List.nodup_cons.mp hnd').1 hmem
    rw [hp]
    simp [hnot]
  have := key (l₀, s) h0 hT
  rw [hfl, Nat.sub_self] at this
  exact hstart this

end HostWP
