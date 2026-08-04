#!/usr/bin/env python3
"""Generate whole-file benchmarks for the X64MNew do-block vcgen proofs.

Each program is a literal do-block of the per-constructor `Op.*` actions of
Kraken.X64MNew; the proved property is the final-state register constraint in the
`Std.Internal.Do` triple notation for the device-parameterized machine monad. The
wall time of one such file covers elaborating and compiling `n` lines of program
on top of the proof, which is what makes it comparable with a hand-written proof
script; use bench/Cases for anything scaling-related.

Families:
  add      -- n * add rax, 3 over a concrete start      post: rax = 3n
  dec      -- mov rax, n; n * dec rax                    post: rax = 0
  adc      -- mov rax, 0; add rax, 0 (clears cf);
              mov rax, 1; mov rbx, 3; n * adc rax, rbx   post: rax = 1 + 3n
  multireg -- round-robin mov over 15 registers          post: all 15 finals

Variants:
  spec  -- vcgen -internalize simplifying_assumptions, then bv_decide
  kfold -- vcgen -internalize, then kfold_discharge
"""
import sys, pathlib

SIZES = [40, 160, 640]
REGS = ["rax","rbx","rcx","rdx","rsi","rdi","rbp","r8","r9","r10","r11","r12","r13","r14","r15"]

HDR = """import Kraken.X64MNew
import KrakenTactics.Fold
open Std.Internal.Do Kraken
set_option mvcgen.warning false
set_option grind.warning false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
"""

def reg(r): return f"(.reg (.low .{r} .W64))"
def mov(r, i): return f"Op.mov {reg(r)} (.imm (.int64 {i}))"
def add(r, i): return f"Op.add {reg(r)} (.imm (.int64 {i}))"
def dec(r): return f"Op.dec {reg(r)}"
def adc(r, s): return f"Op.adc {reg(r)} (.regOrMem {reg(s)})"

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
    binder = "s" if pre != "True" else "_"
    return f'''
def {name}prog : X64MNew Unit Unit := do
{prog}

example : ⦃fun _ _ {binder} => {pre}⦄ {name}prog ⦃fun _ _ _ s => {post}; fun _ _ => True⦄ := by
{DISCHARGE[variant].format(name=name)}'''

def add_family(n, variant):
    body = [add("rax", 3)] * n
    return emit(f"add{n}", body, "s.machine.regs.get64 .rax = 0#64",
                f"s.machine.regs.get64 .rax = {3*n}#64", variant)

def dec_family(n, variant):
    body = [mov("rax", n)] + [dec("rax")] * n
    return emit(f"dec{n}", body, "True", "s.machine.regs.get64 .rax = 0#64", variant)

def adc_family(n, variant):
    body = [mov("rax", 0), add("rax", 0), mov("rax", 1), mov("rbx", 3)] + [adc("rax", "rbx")] * n
    return emit(f"adc{n}", body, "True", f"s.machine.regs.get64 .rax = {1 + 3*n}#64", variant)

def multireg_family(n, variant):
    body = [mov(REGS[i % 15], i + 1) for i in range(n)]
    last = {}
    for i in range(n):
        last[REGS[i % 15]] = i + 1
    post = " ∧ ".join(f"s.machine.regs.get64 .{r} = {v}#64" for r, v in sorted(last.items()))
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
