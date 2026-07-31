#!/usr/bin/env python3
"""Generate whole-file benchmarks for the EStateM do-block vcgen proofs.

Each program is a literal do-block of the per-instruction `Op.*` actions from
Kraken.Specs; the proved property is the final-state register constraint in the
`Std.Internal.Do` triple notation for `EStateM X64Exit MachineData`. The wall
time of one such file covers elaborating and compiling `n` lines of program on
top of the proof, which is what makes it comparable with a hand-written proof
script; use bench/Cases for anything scaling-related.

Families:
  add      -- n * addRI rax 3 over a symbolic start   post: rax = k + 3n
  dec      -- movRI rax n; n * decR rax               post: rax = 0
  adc      -- movRI rax 0; addRI rax 0 (clears cf);
              movRI rax 1; movRI rbx 3; n * adcRR rax rbx
                                                      post: rax = 1 + 3n
  multireg -- round-robin movRI over 15 registers     post: all 15 finals

Variants:
  spec  -- vcgen -internalize simplifying_assumptions, then bv_decide
  kfold -- vcgen -internalize, then kfold_discharge
"""
import sys, pathlib

SIZES = [40, 160]
REGS = ["rax","rbx","rcx","rdx","rsi","rdi","rbp","r8","r9","r10","r11","r12","r13","r14","r15"]

HDR = """import Kraken.Specs
import KrakenTactics.Fold
open Std.Internal.Do
set_option mvcgen.warning false
set_option grind.warning false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
"""

DISCHARGE = {
  "spec": """  vcgen -internalize [{name}prog] simplifying_assumptions
  all_goals bv_decide
""",
  "kfold": """  vcgen -internalize [{name}prog]
  all_goals kfold_discharge
""",
}

def emit(name, body, pre, post, variant):
    prog = "\n".join("  " + line for line in body)
    binder = "(s : MachineData)" if pre != "True" else "(_ : MachineData)"
    return f'''
def {name}prog : X64M Unit := do
{prog}

example : ⦃fun {binder} => {pre}⦄ {name}prog ⦃fun _ s => {post}⦄ := by
{DISCHARGE[variant].format(name=name)}'''

def add_family(n, variant):
    body = ["Op.addRI .rax 3"] * n
    return emit(f"add{n}", body, "s.regs.get64 .rax = 0#64", f"s.regs.get64 .rax = {3*n}#64", variant)

def dec_family(n, variant):
    body = [f"Op.movRI .rax {n}"] + ["Op.decR .rax"] * n
    return emit(f"dec{n}", body, "True", "s.regs.get64 .rax = 0#64", variant)

def adc_family(n, variant):
    body = ["Op.movRI .rax 0", "Op.addRI .rax 0", "Op.movRI .rax 1", "Op.movRI .rbx 3"] \
         + ["Op.adcRR .rax .rbx"] * n
    return emit(f"adc{n}", body, "True", f"s.regs.get64 .rax = {1 + 3*n}#64", variant)

def multireg_family(n, variant):
    body = [f"Op.movRI .{REGS[i % 15]} {i+1}" for i in range(n)]
    last = {}
    for i in range(n):
        last[REGS[i % 15]] = i + 1
    post = " ∧ ".join(f"s.regs.get64 .{r} = {v}#64" for r, v in sorted(last.items()))
    return emit(f"multireg{n}", body, "True", post, variant)

FAMILIES = [("add", add_family), ("dec", dec_family),
            ("adc", adc_family), ("multireg", multireg_family)]

def main():
    outdir = pathlib.Path(sys.argv[1]) if len(sys.argv) > 1 else pathlib.Path("bench/generated")
    outdir.mkdir(parents=True, exist_ok=True)
    for variant in DISCHARGE:
        for fam, gen in FAMILIES:
            for n in SIZES:
                path = outdir / f"{fam}{n}_{variant}.lean"
                path.write_text(HDR + gen(n, variant))
    print(f"wrote {len(list(outdir.glob('*.lean')))} files to {outdir}")

if __name__ == "__main__":
    main()
