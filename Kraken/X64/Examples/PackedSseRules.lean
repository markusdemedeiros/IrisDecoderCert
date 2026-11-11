import Kraken.X64.Parser
import Kraken.MachineWP
import Kraken.SeparationMem
import Kraken.Rules.PackedSse

/-!
# Checks for the packed SSE/AVX rules

Three small programs, each proved memory-safe by `vcgen with finish` using only
the rules of `Kraken/Rules/PackedSse.lean` for their vector instructions:

* `sse_copy_prog`: a loop that copies 64 bytes with `movdqa (%rdi,%rcx,4)`, an
  aligned 16-byte load with a scaled index, and a legacy `movups` store
  (`(%rsi,%rcx,4)`), plus register-form `pshufd`/`pxor`.
* `sse_legacy_prog`: straight-line legacy SSE with `m32`/`m64` accesses
  (`movss`, `movhps`, `movlps`, `addss`), aligned 128-bit operands (`addps`,
  `shufps`, `punpckldq`, `movdqa` store) and an unaligned `movdqu` store.
* `avx_prog`: straight-line VEX code: `vmovups` of a `ymm`, `vmulps`,
  `vbroadcastss`, `vblendvps` and `vpermilps` with memory sources, an aligned
  `vmovaps` store, `vmovlps`, `vinsertps`, `vpextrd`.

Findings:

* The alignment side conditions behave as the semantics says: the legacy
  `movdqa`, `addps`, `shufps`, `punpckldq` operands need 16-byte alignment
  (the preconditions ask for an aligned `rdi`/`rsi`), while the `movss`,
  `movhps`, `movlps`, `addss` accesses at odd offsets need none, and neither
  do `movups`/`movdqu` stores at offset 3 or any VEX operand other than the
  aligned move.
* `isAligned 16 (rdi + rcx * 4)` follows from `isAligned 16 rdi` and
  `rcx % 4 = 0` without further facts, through `finish`.
-/

open Kraken.X64.Parser
open Kraken
open Std.WP
open MachineWP
open Lean.Order
open scoped Kraken.Rules.GenericMem.Norm

set_option experimental.vcgen true

/-! ## A loop with a scaled, aligned load and a legacy store -/

def sse_copy_prog : Program := parse("
start:
    mov $0x0,%rcx
.loop:
    movdqa (%rdi,%rcx,4),%xmm0
    pshufd $0x1b,%xmm0,%xmm1
    pxor %xmm1,%xmm0
    movups %xmm0,(%rsi,%rcx,4)
    add $0x4,%rcx
    cmp $0x10,%rcx
    jne .loop
")

private abbrev copy_table (d : MachineData) (R : DataMem → Prop) :
    Label → MachineData → Prop
  | "start", s => s = d
  | ".loop", s =>
      s.regs.get64 .rdi = d.regs.get64 .rdi ∧ s.regs.get64 .rsi = d.regs.get64 .rsi ∧
      (s.regs.get64 .rcx).toNat < 16 ∧ (s.regs.get64 .rcx).toNat % 4 = 0 ∧
      (s.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, 64), (d.regs.get64 .rsi, 64)] ⋆ R)
  | _, _ => False

private abbrev copy_var : Label → MachineData → Nat
  | "start", _ => 2 ^ 64
  | ".loop", s => 16 - (s.regs.get64 .rcx).toNat
  | _, _ => 0

section Copy

variable [layout : _root_.Layout] [Executable.ValidLayout (layout sse_copy_prog)]

local instance sse_copy.env : CodeEnv := ⟨layout sse_copy_prog⟩

theorem sse_copy_correct (d : MachineData) (R : DataMem → Prop)
    (h_al : isAligned 16 (d.regs.get64 .rdi) = true)
    (h_mem : d.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, 64), (d.regs.get64 .rsi, 64)] ⋆ R) :
    ⦃ fun s => s = d ⦄
      sse_copy_prog
    ⦃ fun _ s => s.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, 64), (d.regs.get64 .rsi, 64)] ⋆ R ⦄ := by
  apply MachineWP.cfg (copy_table d R) copy_var
  cfg_cases [sse_copy_prog]
  · vcgen with finish
  · vcgen with finish

end Copy

/-! ## Straight-line legacy SSE -/

abbrev sse_legacy_prog : Program := parse("
    movss 0x4(%rdi),%xmm0
    movhps 0x8(%rdi),%xmm0
    addss 0x24(%rdi),%xmm0
    addps 0x10(%rdi),%xmm0
    shufps $0x1b,0x20(%rdi),%xmm0
    movaps %xmm0,%xmm1
    punpckldq 0x30(%rdi),%xmm1
    movlhps %xmm0,%xmm1
    movdqa %xmm1,0x10(%rsi)
    movlps %xmm0,0x5(%rsi)
    movhps %xmm0,0x20(%rsi)
    movss %xmm1,0x2c(%rsi)
    movdqu %xmm0,0x3(%rsi)
")

section Legacy

variable [CodeEnv]

theorem sse_legacy_correct (d : MachineData) (R : DataMem → Prop)
    (h_al_rdi : isAligned 16 (d.regs.get64 .rdi) = true)
    (h_al_rsi : isAligned 16 (d.regs.get64 .rsi) = true)
    (h_mem : d.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, 64), (d.regs.get64 .rsi, 64)] ⋆ R) :
    ⦃ fun s => s = d ⦄
      sse_legacy_prog
    ⦃ (fun _ s => s.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, 64), (d.regs.get64 .rsi, 64)] ⋆ R);
      fun _ _ => False ⦄ := by
  vcgen with finish

end Legacy

/-! ## Straight-line VEX -/

abbrev avx_prog : Program := parse("
    vmovups (%rdi),%ymm0
    vmulps 0x4(%rdi),%xmm0,%xmm2
    vbroadcastss 0x1c(%rdi),%xmm3
    vblendvps %xmm3,0x21(%rdi),%xmm2,%xmm5
    vaddsubps %xmm5,%xmm2,%xmm4
    vpermilps $0x1b,0x30(%rdi),%xmm6
    vinsertps $0x1c,%xmm1,%xmm4,%xmm1
    vmovaps %xmm1,0x20(%rsi)
    vmovups %ymm0,(%rsi,%rax,1)
    vmovlps %xmm6,0x1(%rsi)
    vpextrd $0x1,%xmm3,%ecx
")

section Avx

variable [CodeEnv]

theorem avx_correct (d : MachineData) (R : DataMem → Prop)
    (h_al_rsi : isAligned 16 (d.regs.get64 .rsi) = true)
    (h_rax : (d.regs.get64 .rax).toNat ≤ 16)
    (h_mem : d.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, 64), (d.regs.get64 .rsi, 64)] ⋆ R) :
    ⦃ fun s => s = d ⦄
      avx_prog
    ⦃ (fun _ s => s.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, 64), (d.regs.get64 .rsi, 64)] ⋆ R);
      fun _ _ => False ⦄ := by
  vcgen with finish

end Avx
