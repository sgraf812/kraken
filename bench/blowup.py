#!/usr/bin/env python3
"""Generate the blow-up measurement files: the `mov $1,%rax; mov $3,%rbx` + n*adc
program at n = 1,2,3, each stepped by vcgen and left with `trace_state; admit`
so the final VC can be printed and its size measured.

Run e.g.:  for n in 1 2 3; do lake env lean bench/blowup/blow$n.lean; done
and measure the printed goal (excluding the trailing `sorry` warning).
"""
import pathlib

HDR = '''import Kraken.X64MNew
open Std.Internal.Do Kraken
set_option mvcgen.warning false
set_option grind.warning false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
'''

TMPL = HDR + '''
def blow{n}prog : X64MNew Unit Unit := do
  Op.mov (.reg (.low .rax .W64)) (.imm (.int64 1))
  Op.mov (.reg (.low .rbx .W64)) (.imm (.int64 3))
{adc}

-- Final VC: run vcgen, then print and admit the leftover goal.
example : ⦃fun _ _ _ => True⦄ blow{n}prog ⦃fun _ _ _ s => s.machine.regs.get64 .rax = {res}#64;
    fun _ _ => True⦄ := by
  vcgen [blow{n}prog]
  all_goals (trace_state; admit)
'''

INTERMEDIATE = HDR + '''
def prog3 : X64MNew Unit Unit := do
  Op.mov (.reg (.low .rax .W64)) (.imm (.int64 1))
  Op.mov (.reg (.low .rbx .W64)) (.imm (.int64 3))
  Op.adc (.reg (.low .rax .W64)) (.regOrMem (.reg (.low .rbx .W64)))
  Op.adc (.reg (.low .rax .W64)) (.regOrMem (.reg (.low .rbx .W64)))
  Op.adc (.reg (.low .rax .W64)) (.regOrMem (.reg (.low .rbx .W64)))

-- Stepped VC: the verification condition vcgen produces for the three-step chain.
example : ⦃fun _ _ _ => True⦄ prog3 ⦃fun _ _ _ s => s.machine.regs.get64 .rax = 10#64;
    fun _ _ => True⦄ := by
  vcgen [prog3]
  all_goals (trace_state; admit)
'''

def main():
    out = pathlib.Path(__file__).parent / "blowup"
    out.mkdir(parents=True, exist_ok=True)
    for n in (1, 2, 3):
        adc = "\n".join(["  Op.adc (.reg (.low .rax .W64)) (.regOrMem (.reg (.low .rbx .W64)))"] * n)
        (out / f"blow{n}.lean").write_text(TMPL.format(n=n, adc=adc, res=1 + 3 * n))
    (out / "intermediate.lean").write_text(INTERMEDIATE)
    print(f"wrote blow1/2/3.lean and intermediate.lean to {out}")

if __name__ == "__main__":
    main()
