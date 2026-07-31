#!/usr/bin/env python3
"""Generate the same whole-file benchmarks for the kraken `main` branch.

`main` has no `Op.*` actions: a program is parsed assembly and a proof runs the
CPS straightline judgment through the `kstep` stepping tactic. Each generated
file therefore carries the preamble the `Kraken/Examples` proofs use (refine the
state, expose the layout, rewrite the directive list), one `kstep`, and a
discharge.

Run against a `main` checkout:

    python3 bench/gen_master.py /path/to/main-worktree/bench/generated
    cd /path/to/main-worktree && lake env lean bench/generated/dec40.lean

Families: add, dec, multireg. The carry chain is omitted: `kstep` on an `adc`
program produces a term the kernel rejects, so `main` cannot express it.
"""
import sys, pathlib

SIZES = [40, 160]
REGS = ["rax","rbx","rcx","rdx","rsi","rdi","rbp","r8","r9","r10","r11","r12","r13","r14","r15"]

HDR = """import Kraken.Tactics
import Kraken.Parser
import Kraken.Eval
open Kraken.Parser
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

theorem Executable.directivesFromStart [layout : Layout] prog :
    (layout prog).directivesFromAddress layout.start = prog.mapIdx (fun i d => (d, layout.size i)) := by
  induction prog <;> simp [Executable.directivesFromAddress,Executable.withAddresses,Layout.apply]
"""

NORMALIZE = """  simp only [Nat.shiftRight_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.unsigned,
    BitVec.signed, Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat]
"""

def emit(name, body, post):
    prog = "\n".join(body)
    return f'''
def {name}prog := parse("start: {prog}")

example [layout : Layout] s :
    straightlineStep (layout {name}prog) (s, layout.start) (fun s' => {post}) := by
  let ss := s
  change (straightlineStep _ (ss, _) _)
  cases s with | mk regs flags mem =>
  cases regs with | mk rax =>
  delta {name}prog
  dsimp only [straightlineStep,Executable.straightline]
  rw [Executable.directivesFromStart]
  simp [List.mapIdx,List.mapIdx.go]
  sym => kstep; tactic =>
{NORMALIZE}  bv_decide
'''

def add_family(n):
    return emit(f"add{n}", ["add $3, %rax"] * n, f"s'.1.regs.rax = s.regs.rax + {3*n}")

def dec_family(n):
    return emit(f"dec{n}", [f"mov ${n}, %rax"] + ["dec %rax"] * n, "s'.1.regs.rax = 0")

def multireg_family(n):
    body = [f"mov ${i+1}, %{REGS[i % 15]}" for i in range(n)]
    last = {}
    for i in range(n):
        last[REGS[i % 15]] = i + 1
    post = " ∧ ".join(f"s'.1.regs.{r} = {v}" for r, v in sorted(last.items()))
    return emit(f"multireg{n}", body, post)

FAMILIES = [("add", add_family), ("dec", dec_family), ("multireg", multireg_family)]

def main():
    outdir = pathlib.Path(sys.argv[1]) if len(sys.argv) > 1 else pathlib.Path("bench/generated")
    outdir.mkdir(parents=True, exist_ok=True)
    for fam, gen in FAMILIES:
        for n in SIZES:
            (outdir / f"{fam}{n}.lean").write_text(HDR + gen(n))
    print(f"wrote {len(list(outdir.glob('*.lean')))} files to {outdir}")

if __name__ == "__main__":
    main()
