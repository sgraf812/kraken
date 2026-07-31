#!/usr/bin/env python3
"""Generate the blow-up measurement files: the `mov $1,%rax; mov $3,%rbx` + n*adc
program at n = 1,2,3, each stepped by vcgen and left with `trace_state; admit`
so the final VC can be printed and its size measured.

Run e.g.:  for n in 1 2 3; do lake env lean bench/blowup/blow$n.lean; done
and measure the printed goal (excluding the trailing `sorry` warning).
"""
import pathlib

TMPL = '''import Kraken.Specs
open Std.Internal.Do
set_option mvcgen.warning false
set_option grind.warning false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

def blow{n}prog : X64M Unit := do
  Op.movRI .rax 1
  Op.movRI .rbx 3
{adc}

-- Final VC: run vcgen, then print and admit the leftover goal.
example : ⦃fun (_ : MachineData) => True⦄ blow{n}prog ⦃fun _ s => s.regs.rax = {res}⦄ := by
  vcgen [blow{n}prog]
  all_goals (trace_state; admit)
'''

INTERMEDIATE = '''import Kraken.Specs
open Std.Internal.Do
set_option mvcgen.warning false
set_option pp.deepTerms true

def prog3 : X64M Unit := do
  Op.movRI .rax 1
  Op.movRI .rbx 3
  Op.adcRR .rax .rbx
  Op.adcRR .rax .rbx
  Op.adcRR .rax .rbx

-- Intermediate wp goal: the weakest precondition before any spec is applied.
-- The residual program is a single shared `do` block (no duplication).
example : ⦃fun (_ : MachineData) => True⦄ prog3 ⦃fun _ s => s.regs.rax = 10⦄ := by
  apply Triple.intro
  intro s _
  simp only [prog3]
  trace_state
  admit
'''

def main():
    out = pathlib.Path(__file__).parent / "blowup"
    out.mkdir(parents=True, exist_ok=True)
    for n in (1, 2, 3):
        adc = "\n".join(["  Op.adcRR .rax .rbx"] * n)
        (out / f"blow{n}.lean").write_text(TMPL.format(n=n, adc=adc, res=1 + 3 * n))
    (out / "intermediate.lean").write_text(INTERMEDIATE)
    print(f"wrote blow1/2/3.lean and intermediate.lean to {out}")

if __name__ == "__main__":
    main()
