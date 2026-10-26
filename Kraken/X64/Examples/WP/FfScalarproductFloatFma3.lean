module

public import Kraken.StateCfg
public import Kraken.SeparationMem
import Kraken.X64.Parser

open Kraken.X64.Parser
open Std.WP
open Lean.Order
open scoped Program.WP

set_option experimental.vcgen true

namespace State.FfScalarproductFloatFma3

def scalarproduct_fma3_prog : Program := parse("
start:
    xor %r8,%r8
    vxorps %ymm0,%ymm0,%ymm0
    shl $0x2,%edx
    mov %rdx,%rcx
    cmp $0x20,%rcx
    jl .l16
    cmp $0x40,%rcx
    jl .l32
    vxorps %ymm1,%ymm1,%ymm1
    cmp $0x80,%rcx
    jl .l64
    and $0xffffffffffffff80,%rcx
    vxorps %ymm2,%ymm2,%ymm2
    vxorps %ymm3,%ymm3,%ymm3
.loop128:
    vmovups (%rdi,%r8,1),%ymm4
    vmovups 0x20(%rdi,%r8,1),%ymm5
    vmovups 0x40(%rdi,%r8,1),%ymm6
    vmovups 0x60(%rdi,%r8,1),%ymm7
    vfmadd231ps (%rsi,%r8,1),%ymm4,%ymm0
    vfmadd231ps 0x20(%rsi,%r8,1),%ymm5,%ymm1
    vfmadd231ps 0x40(%rsi,%r8,1),%ymm6,%ymm2
    vfmadd231ps 0x60(%rsi,%r8,1),%ymm7,%ymm3
    sub $0xffffffffffffff80,%r8
    cmp %rcx,%r8
    jl .loop128
    vaddps %ymm2,%ymm0,%ymm0
    vaddps %ymm3,%ymm1,%ymm1
    mov %rdx,%rcx
    and $0x7f,%rcx
    cmp $0x40,%rcx
    jge .l64
    vaddps %ymm1,%ymm0,%ymm0
    cmp $0x20,%rcx
    jge .l32
    vextractf128 $0x1,%ymm0,%xmm2
    vaddps %xmm2,%xmm0,%xmm0
    cmp $0x10,%rcx
    jge .l16
    vmovhlps %xmm0,%xmm1,%xmm1
    vaddps %xmm1,%xmm0,%xmm0
    vmovss %xmm0,%xmm1,%xmm1
    vshufps $0x1,%xmm0,%xmm0,%xmm0
    vaddss %xmm1,%xmm0,%xmm0
    vzeroupper
    jmp done
.l64:
    and $0xffffffffffffffc0,%rcx
    add %r8,%rcx
.loop64:
    vmovups (%rdi,%r8,1),%ymm4
    vmovups 0x20(%rdi,%r8,1),%ymm5
    vfmadd231ps (%rsi,%r8,1),%ymm4,%ymm0
    vfmadd231ps 0x20(%rsi,%r8,1),%ymm5,%ymm1
    add $0x40,%r8
    cmp %rcx,%r8
    jl .loop64
    vaddps %ymm1,%ymm0,%ymm0
    mov %rdx,%rcx
    and $0x3f,%rcx
    cmp $0x20,%rcx
    jge .l32
    vextractf128 $0x1,%ymm0,%xmm2
    vaddps %xmm2,%xmm0,%xmm0
    cmp $0x10,%rcx
    jge .l16
    vmovhlps %xmm0,%xmm1,%xmm1
    vaddps %xmm1,%xmm0,%xmm0
    vmovss %xmm0,%xmm1,%xmm1
    vshufps $0x1,%xmm0,%xmm0,%xmm0
    vaddss %xmm1,%xmm0,%xmm0
    vzeroupper
    jmp done
.l32:
    and $0xffffffffffffffe0,%rcx
    add %r8,%rcx
.loop32:
    vmovups (%rdi,%r8,1),%ymm4
    vfmadd231ps (%rsi,%r8,1),%ymm4,%ymm0
    add $0x20,%r8
    cmp %rcx,%r8
    jl .loop32
    vextractf128 $0x1,%ymm0,%xmm2
    vaddps %xmm2,%xmm0,%xmm0
    mov %rdx,%rcx
    and $0x1f,%rcx
    cmp $0x10,%rcx
    jge .l16
    vmovhlps %xmm0,%xmm1,%xmm1
    vaddps %xmm1,%xmm0,%xmm0
    vmovss %xmm0,%xmm1,%xmm1
    vshufps $0x1,%xmm0,%xmm0,%xmm0
    vaddss %xmm1,%xmm0,%xmm0
    vzeroupper
    jmp done
.l16:
    and $0xfffffffffffffff0,%rcx
    add %r8,%rcx
.loop16:
    vmovaps (%rdi,%r8,1),%xmm1
    vmulps (%rsi,%r8,1),%xmm1,%xmm1
    vaddps %xmm1,%xmm0,%xmm0
    add $0x10,%r8
    cmp %rcx,%r8
    jl .loop16
    vmovhlps %xmm0,%xmm1,%xmm1
    vaddps %xmm1,%xmm0,%xmm0
    vmovss %xmm0,%xmm1,%xmm1
    vshufps $0x1,%xmm0,%xmm0,%xmm0
    vaddss %xmm1,%xmm0,%xmm0
    vzeroupper
done:
    nop
")

theorem scalarproduct_fma3_spec [Host] [FunDecls] (d : MachineData) (len : Nat)
    (h_len_reg : (d.regs.get64 .rdx).take 32 = BitVec.ofNat 32 len)
    (h_len_mod : len % 4 = 0) (h_len_pos : 0 < len) (h_len_bound : len * 4 < 2 ^ 32)
    (h_v1_aligned : isAligned 16 (d.regs.get64 .rdi) = true)
    (R₁ R₂ : DataMem → Prop)
    (h_v1 : d.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, len * 4)] ⋆ R₁)
    (h_v2 : d.dmem =⋆ Mem.Blocks [(d.regs.get64 .rsi, len * 4)] ⋆ R₂) :
    WP.wp scalarproduct_fma3_prog (fun _ t => t.dmem = d.dmem) (fun _ _ => False) d := by
  refine Program.WP.cfg
    (fun b t =>
      let r8 := (t.regs.get64 .r8).toNat
      let rcx := (t.regs.get64 .rcx).toNat
      let L := len * 4
      let inv := t.regs.get64 .rdi = d.regs.get64 .rdi ∧ t.regs.get64 .rsi = d.regs.get64 .rsi
        ∧ (t.regs.get64 .rdx).toNat = L ∧ t.dmem = d.dmem ∧ t.regs.get64 .rsp = d.regs.get64 .rsp
      match b with
      | .entry | .label "start" => t = d
      | .label ".loop128" => inv ∧ rcx % 128 = 0 ∧ rcx ≤ L ∧ L < rcx + 128 ∧ r8 % 128 = 0 ∧ r8 < rcx
      | .label ".l64" => inv ∧ rcx + r8 = L ∧ 64 ≤ rcx ∧ rcx < 128 ∧ r8 % 128 = 0
      | .label ".loop64" => inv ∧ rcx = r8 + 64 ∧ r8 + 64 ≤ L ∧ L < r8 + 128 ∧ r8 % 64 = 0
      | .label ".l32" => inv ∧ rcx + r8 = L ∧ 32 ≤ rcx ∧ rcx < 64 ∧ r8 % 64 = 0
      | .label ".loop32" => inv ∧ rcx = r8 + 32 ∧ r8 + 32 ≤ L ∧ L < r8 + 64 ∧ r8 % 32 = 0
      | .label ".l16" => inv ∧ rcx + r8 = L ∧ 16 ≤ rcx ∧ rcx < 32 ∧ r8 % 32 = 0
      | .label ".loop16" => inv ∧ rcx = r8 + 16 ∧ r8 + 16 ≤ L ∧ L < r8 + 32 ∧ r8 % 16 = 0
      | .label "done" => t.dmem = d.dmem ∧ t.regs.get64 .rsp = d.regs.get64 .rsp
      | .exit => t.dmem = d.dmem
      | _ => False)
    (fun l t => match l with
      | "start" => 2 ^ 64
      | ".loop128" => (t.regs.get64 .rcx).toNat - (t.regs.get64 .r8).toNat
      | _ => 0) ?_ rfl
  cfg_cases
  all_goals kvcgen64 with finish

end State.FfScalarproductFloatFma3
