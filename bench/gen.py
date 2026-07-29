#!/usr/bin/env python3
"""Generate benchmark families for the EStateM do-block vcgen proofs.

Each program is a literal do-block of the per-instruction `Op.*` actions from
Kraken.AccessorSpecs; the proved property is the final-state register constraint
in the `Std.Internal.Do` triple notation for `EStateM X64Exit MachineData`.

Families:
  dec      -- movRI rax n; n * decR rax                 post: rax = 0
  adc      -- movRI rax 0; addRI rax 0 (clears cf);
              movRI rax 1; movRI rbx 3; n * adcRR rax rbx
                                                          post: rax = 1 + 3n
  multireg -- round-robin movRI over 15 registers        post: all 15 finals

Variants:
  tactic -- vcgen then simp_all <;> bv_decide
  finish -- sym => vcgen simplifying_assumptions; finish (splits := 40)
"""
import sys, pathlib

SIZES = [10, 20, 40, 80]
REGS = ["rax","rbx","rcx","rdx","rsi","rdi","rbp","r8","r9","r10","r11","r12","r13","r14","r15"]

HDR = """import Kraken.AccessorSpecs
open Std.Internal.Do
set_option mvcgen.warning false
set_option grind.warning false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
"""

DISCHARGE = {
  "tactic": """  vcgen -internalize [{name}prog]
  all_goals (simp_all <;> bv_decide)
""",
  "finish": """  sym =>
    vcgen [{name}prog] simplifying_assumptions
    all_goals finish (splits := 40)
""",
}

def emit(name, body, post, variant):
    prog = "\n".join("  " + line for line in body)
    return f'''
def {name}prog : X64M Unit := do
{prog}

example : ⦃fun (_ : MachineData) => True⦄ {name}prog ⦃fun _ s => {post}⦄ := by
{DISCHARGE[variant].format(name=name)}'''

def dec_family(n, variant):
    body = [f"Op.movRI .rax {n}"] + ["Op.decR .rax"] * n
    return emit(f"dec{n}", body, "s.regs.rax = 0", variant)

def adc_family(n, variant):
    body = ["Op.movRI .rax 0", "Op.addRI .rax 0", "Op.movRI .rax 1", "Op.movRI .rbx 3"] \
         + ["Op.adcRR .rax .rbx"] * n
    return emit(f"adc{n}", body, f"s.regs.rax = {1 + 3*n}", variant)

def multireg_family(n, variant):
    body = [f"Op.movRI .{REGS[i % 15]} {i+1}" for i in range(n)]
    last = {}
    for i in range(n):
        last[REGS[i % 15]] = i + 1
    post = " ∧ ".join(f"s.regs.{r} = {v}" for r, v in sorted(last.items()))
    return emit(f"multireg{n}", body, post, variant)

def main():
    outdir = pathlib.Path(sys.argv[1]) if len(sys.argv) > 1 else pathlib.Path("bench/generated")
    outdir.mkdir(parents=True, exist_ok=True)
    for variant in ["tactic", "finish"]:
        for fam, gen in [("dec", dec_family), ("adc", adc_family), ("multireg", multireg_family)]:
            for n in SIZES:
                path = outdir / f"{fam}{n}_{variant}.lean"
                path.write_text(HDR + gen(n, variant))
    print(f"wrote {len(list(outdir.glob('*.lean')))} files to {outdir}")

if __name__ == "__main__":
    main()
