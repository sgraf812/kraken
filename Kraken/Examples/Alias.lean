/-
Alias labels: `alias` and `fin` name the same address, because the label cell
`alias` occupies no bytes. `palias_correct` runs the control-flow rule over
the three blocks, and `palias_correct_run` reads the triple back at the
machine through `Program.run_of_triple`, whose placement handles the shared
address.
-/
import Kraken.Parser
import Kraken.MachineWP

open Kraken.Parser
open Std.Internal.Do
open MachineWP
open Lean.Order

set_option mvcgen.warning false

/-- The prologue: it sets `rdx` and jumps to `fin`. -/
abbrev palias.entry : Program := parse("
init:
  mov $2, %rdx
  jmp fin
")

/-- The tail, with an alias label directly in front of the jump target. -/
abbrev palias.exit : Program := Directive.label "alias" :: parse("
fin:
  nop
")

/-- The program: the prologue, then the aliased tail. -/
def palias : Program := palias.entry ++ palias.exit

/-- The jump edge goes forward in the text. -/
private theorem idx_init_lt_fin :
    Program.blockIdx palias "init" < Program.blockIdx palias "fin" := by
  decide

grind_pattern idx_init_lt_fin => Program.blockIdx palias "fin"

/-- The jump target of `palias` is mapped. -/
@[grind .] private theorem palias_fin_isSome :
    (Program.blockAt palias "fin").isSome := by decide

/-- The spec table: nothing on entry, nothing reaches `alias`, and at `fin`
the register holds the answer. -/
private abbrev palias_table : Label → MachineData → Prop
  | "init", _ => True
  | "fin", s => s.regs.rdx.toNat = 2
  | _, _ => False

variable [layout : Layout] [Executable.ValidLayout (layout palias)]

/-- The ambient code of the example: `palias`, laid out. -/
local instance palias.env : CodeEnv := ⟨layout palias⟩

theorem palias_correct :
    ⦃ fun _ => True ⦄ palias ⦃ fun _ s => s.regs.rdx.toNat = 2 ⦄ := by
  apply MachineWP.cfg palias_table (fun _ _ => 0)
  cfg_cases [palias, palias.entry, palias.exit]
  · vcgen simplifying_assumptions with finish
  · vcgen simplifying_assumptions with finish
  · vcgen simplifying_assumptions with finish

/-- `palias_correct`, read at the machine as the baseline judgment. -/
theorem palias_correct_run (d : MachineData) :
    Eventually (straightlineStep (layout palias))
      (fun s => s.1.regs.rdx.toNat = 2) (d, layout.start) :=
  Program.run_of_triple palias_correct trivial
