/-
Alias labels: `alias` and `fin` name the same address, because the label cell
`alias` occupies no bytes. `palias_correct` runs the control-flow rule over
the three blocks, and `palias_correct_run` reads the triple back at the
machine through `Program.sound`, whose extraction handles the shared address.
-/
import Kraken.Parser
import Kraken.SegmentExtract
import Kraken.SegmentWP
import Kraken.SegmentWPSound

open Kraken.Parser
open Std.Internal.Do
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
private theorem len_fin_lt_init :
    (Program.fromLabel palias "fin").length < (Program.fromLabel palias "init").length := by
  decide

grind_pattern len_fin_lt_init => List.length (Program.fromLabel palias "init")

/-- The jump target of `palias` is mapped. -/
@[grind .] private theorem palias_fin_isSome :
    (Program.blockAt palias "fin").isSome := by decide

/-- The spec table: nothing on entry, nothing reaches `alias`, and at `fin`
the register holds the answer. -/
private abbrev palias_table : Label → MachineData → Prop
  | "init", _ => True
  | "fin", s => s.regs.rdx.toNat = 2
  | _, _ => False

theorem palias_correct :
    ⦃ fun _ => True ⦄ palias ⦃ fun _ s => s.regs.rdx.toNat = 2 ⦄ := by
  apply Program.cfg palias_table (fun _ _ => 0)
  cfg_cases [palias, palias.entry, palias.exit]
  · vcgen simplifying_assumptions with finish
  · vcgen simplifying_assumptions with finish
  · vcgen simplifying_assumptions with finish

variable [layout : Layout] [hv : Executable.ValidLayout (layout palias)]

/-- `palias_correct`, read at the machine as the baseline judgment. -/
theorem palias_correct_run (d : MachineData) :
    Eventually (straightlineStep (layout palias))
      (fun s => s.1.regs.rdx.toNat = 2) (d, layout.start) := by
  have h := palias_correct.le_wp d trivial
  refine (Program.sound h).mono (fun _ _ h => h) ?_
  rintro mid (hq | ⟨l, -, hf⟩)
  · exact hq
  · exact Program.bot_elim hf
