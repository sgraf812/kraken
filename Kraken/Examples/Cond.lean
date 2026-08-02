/-
Conditional jump: `vcgen` splits `Op.jnz_spec`'s precondition on the flag,
stepping the fall-through tail and sending the taken branch to the exception post.
-/
import Kraken.Tactics
import Std.Tactic.BVDecide

open Std.Internal.Do
open Kraken

set_option mvcgen.warning false
set_option grind.warning false
set_option maxHeartbeats 1000000

def condProg (l : Int64) : X64M Unit := do
  Op.decR .rax
  Op.jnz l
  Op.movRI .rbx 7

-- Fall-through (flag set): `rbx` becomes 7. Taken (flag clear): the jump exits
-- before `rbx` is touched, and the exception post is unconstrained.
theorem cond_correct (l : Int64) :
    ⦃fun _ => True⦄
      condProg l
      ⦃fun _ s => (s.regs.get64 .rbx).toBitVec = 7#64; fun _ _ => True⦄ := by
  sym =>
    vcgen [condProg]
    all_goals finish
