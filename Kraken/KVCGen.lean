module

/-
`kvcgen64 [defs] with step` is `vcgen` with the register state folded as it
goes: every write to a named register becomes a structure update, so the
state `vcgen` threads through a block stays one register literal. Both the
state wp and the separation wp use it.
-/
public import Kraken.X64.Registers
public import Std.Tactic.Do.Syntax

public section

/-- `vcgen` with the register state folded. -/
syntax (name := kvcgen64) "kvcgen64" (" [" ident,* "]")? (" with " vcgenDischarge)? : tactic

macro_rules
  | `(tactic| kvcgen64 $[[$ids,*]]? $[with $d]?) => do
    let lemmas ← (ids.map (·.getElems) |>.getD #[]).mapM fun i =>
      `(Lean.Parser.Tactic.simpLemma| $i:ident)
    `(tactic| vcgen [$lemmas,*] simplifying_assumptions [
        Reg64s.set64_rax,
        Reg64s.set64_rbx,
        Reg64s.set64_rcx,
        Reg64s.set64_rdx,
        Reg64s.set64_rsi,
        Reg64s.set64_rdi,
        Reg64s.set64_rsp,
        Reg64s.set64_rbp,
        Reg64s.set64_r8,
        Reg64s.set64_r9,
        Reg64s.set64_r10,
        Reg64s.set64_r11,
        Reg64s.set64_r12,
        Reg64s.set64_r13,
        Reg64s.set64_r14,
        Reg64s.set64_r15] $[with $d]?)
