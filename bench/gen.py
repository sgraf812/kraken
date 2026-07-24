#!/usr/bin/env python3
"""Generate benchmark families for the vcgen straightline proofs.

Families:
  dec      -- mov $n, %rax; n * dec %rax          post: rax = 0
  adc      -- carry chain: add $0 clears cf, then n * adc %rbx, %rax
                                                   post: rax = 1 + 3n
  multireg -- round-robin mov $k, %reg over 15 registers
                                                   post: all 15 final values

Variants: baseline (unfold specs, import Kraken.VCGenSpike)
          accessor (accessor specs, import Kraken.AccessorSpecs)
"""
import sys, pathlib

SIZES = [10, 20, 40, 80]
REGS = ["rax","rbx","rcx","rdx","rsi","rdi","rbp","r8","r9","r10","r11","r12","r13","r14","r15"]

HDR = """import {imp}
open Kraken.Parser
open Std.Internal.Do
set_option mvcgen.warning false
set_option grind.warning false
set_option maxHeartbeats 4000000
"""

DISCHARGE = {
  "baseline": """  sym =>
    vcgen -internalize
    all_goals (simp; cbv; tactic => (first | rfl | decide))
""",
  "accessor": """  sym =>
    vcgen -internalize
    all_goals tactic => (simp_all; try decide)
""",
}

PREAMBLE = """  cases s with | mk regs zmms flags mem =>
  cases regs with | mk rax rbx rcx rdx rsi rdi rsp rbp r8 r9 r10 r11 r12 r13 r14 r15 =>
  delta {name}
  dsimp only [straightlineStep, Executable.straightline]
  rw [Executable.directivesFromStart']
  simp [List.mapIdx, List.mapIdx.go]
  apply Effects.all_of_triple
"""

def emit(name, prog, post, n, variant):
    return f'''
def {name} := parse("{prog}")

example [layout : Layout] s :
    straightlineStep (layout {name}) (s, layout.start) (fun s => {post}) := by
{PREAMBLE.format(name=name)}{DISCHARGE[variant]}'''

def dec_family(n, variant):
    prog = f"start: mov ${n}, %rax\\n" + "dec %rax\\n" * n
    return emit(f"dec{n}", prog, "s.1.regs.rax = 0", n, variant)

def adc_family(n, variant):
    prog = "start: mov $0, %rax\\nadd $0, %rax\\nmov $1, %rax\\nmov $3, %rbx\\n" + "adc %rbx, %rax\\n" * n
    return emit(f"adc{n}", prog, f"s.1.regs.rax = {1 + 3*n}", n, variant)

def multireg_family(n, variant):
    prog = "start: " + "".join(f"mov ${i+1}, %{REGS[i % 15]}\\n" for i in range(n))
    last = {}
    for i in range(n):
        last[REGS[i % 15]] = i + 1
    post = " ∧ ".join(f"s.1.regs.{r} = {v}" for r, v in sorted(last.items()))
    return emit(f"multireg{n}", prog, post, n, variant)

def main():
    outdir = pathlib.Path(sys.argv[1]) if len(sys.argv) > 1 else pathlib.Path("bench/generated")
    outdir.mkdir(parents=True, exist_ok=True)
    for variant, imp in [("baseline", "Kraken.VCGenSpike"), ("accessor", "Kraken.AccessorSpecs")]:
        for fam, gen in [("dec", dec_family), ("adc", adc_family), ("multireg", multireg_family)]:
            for n in SIZES:
                path = outdir / f"{fam}{n}_{variant}.lean"
                path.write_text(HDR.format(imp=imp) + gen(n, variant))
    print(f"wrote {len(list(outdir.glob('*.lean')))} files to {outdir}")

if __name__ == "__main__":
    main()
