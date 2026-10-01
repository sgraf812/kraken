module

public import Kraken.HostWP
import Kraken.X64.Examples.Examples

open Std.WP
open Lean.Order
open scoped HostWP

set_option experimental.vcgen true

namespace HostEx

@[grind =] private theorem sq_pow (r b : Nat) (hb : b ≠ 0) (hle : b ≤ r) :
    2 ^ 2 ^ (r - b) * 2 ^ 2 ^ (r - b) = 2 ^ 2 ^ (r - (b - 1)) := by
  rw [← Nat.pow_add, ← Nat.mul_two, ← Nat.pow_succ]
  show 2 ^ 2 ^ (r - b + 1) = _
  rw [show r - b + 1 = r - (b - 1) from by omega]

@[grind .] private theorem sq_lt (r b : Nat) (hbound : 2 ^ 2 ^ r < 2 ^ 64)
    (hb : b ≠ 0) (hle : b ≤ r) :
    2 ^ 2 ^ (r - b) * 2 ^ 2 ^ (r - b) < 2 ^ 64 := by
  rw [sq_pow r b hb hle]
  calc 2 ^ 2 ^ (r - (b - 1))
      ≤ 2 ^ 2 ^ r :=
        Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
    _ < 2 ^ 64 := hbound

@[grind .] private theorem idx_start_lt_end :
    Program.blockIdx p3 "start" < Program.blockIdx p3 "_end" := by
  decide

@[grind .] private theorem p3_start_isSome : (Program.blockAt p3 "start").isSome := by decide
@[grind .] private theorem p3_end_isSome : (Program.blockAt p3 "_end").isSome := by decide

private abbrev p3_table (d : MachineData) : Label → MachineData → Prop
  | "init", s => s = d
  | "start", s =>
      s.regs.rdx.toNat = 2 ^ 2 ^ (d.regs.rbx.toNat - s.regs.rbx.toNat)
      ∧ s.regs.rbx.toNat ≤ d.regs.rbx.toNat ∧ s.regs.rax = 0
  | "_end", s => s.regs.rdx.toNat = 2 ^ 2 ^ d.regs.rbx.toNat ∧ s.regs.rax = 0
  | _, _ => False

theorem p3_correct [layout : Layout] [Kraken.Executable.ValidLayout (layout p3)]
    (d : MachineData) (h_bounds : p3_spec d < 2 ^ 64) (h_rax : d.regs.rax = 0) :
    Eventually (straightlineStep (layout p3))
      (fun s => s.1.regs.rdx.toNat = p3_spec d ∧ s.1.regs.rax = 0) (d, layout.start) := by
  simp only [p3_spec] at h_bounds ⊢
  refine HostWP.cfg (p3_table d) (fun _ s => s.regs.rbx.toNat) ?_ (by rfl) (by decide) d rfl
  intro _ _
  cfg_cases [p3]
  all_goals kvcgen64 with finish

theorem swap_correct [layout : Layout] (d : MachineData) :
    Eventually (straightlineStep (layout swap))
      (fun s' =>
          s'.1.regs.get Reg.rax = d.regs.get Reg.rbx ∧
          s'.1.regs.get Reg.rbx = d.regs.get Reg.rax)
      (d, layout.start) := by
  apply HostWP.eventually_of_wp
  intro _ _
  kvcgen64 [swap] with finish

theorem p2_correct [layout : Layout] (s : MachineData) :
    Eventually (straightlineStep (layout p2)) (fun s => s.1.regs.rax = 2) (s, layout.start) := by
  apply HostWP.eventually_of_wp
  intro _ _
  kvcgen64 [p2] with finish

end HostEx
