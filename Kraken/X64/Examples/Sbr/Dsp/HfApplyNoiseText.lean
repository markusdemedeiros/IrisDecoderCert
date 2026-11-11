import Kraken.X64.Parser
import Kraken.MachineWP

/-!
# `HfApplyNoise`: the program text

The program texts (`body`, `bodyMain`, `body0`, `body1`, `body2`, `body3`) of `Dsp/HfApplyNoise.lean`, as compared with the object
by translation validation (`scripts/sbr/tv`). This module imports only the parser and the
machine model; the proof is in the module of the same name without `Text`.
-/

open Kraken Kraken.X64.Parser

namespace Kraken.Examples.Sbr.HfApplyNoise

/-- The four entries and `apply_noise_main` as they sit in the object, in
order: entries 0, 1, 2 end in `jmp apply_noise_main`; entry 3 falls through
into it. Labels prefixed by the symbol, the final `repz ret` written `ret`
behind a label of its own, the loop cut by extra labels (`.b`, `.c`, `.d`). The NASM
alignment padding behind the `jmp` of entries 0, 1, 2 is in the text (`nop 6`; `nop 8`,
`nop 1`; `nop 6`: the object's `0x39a..0x3a0`, `0x3b7..0x3c0`, `0x3ca..0x3d0`), so that each
entry's block ends at the next entry's address, as `Program.PlacedIn.next` requires. -/
def body : Program := parse("
ff_sbr_hf_apply_noise_0_sse2:
    movdqa ps_noise0(%rip),%xmm0
    jmp apply_noise_main
    nop 6
ff_sbr_hf_apply_noise_1_sse2:
    and $0x1,%r8
    shl $0x4,%r8
    lea ps_noise13(%rip),%rax
    movdqa (%r8,%rax,1),%xmm0
    jmp apply_noise_main
    nop 8
    nop 1
ff_sbr_hf_apply_noise_2_sse2:
    movdqa ps_noise2(%rip),%xmm0
    jmp apply_noise_main
    nop 6
ff_sbr_hf_apply_noise_3_sse2:
    and $0x1,%r8
    shl $0x4,%r8
    lea ps_noise13+16(%rip),%rax
    movdqa (%r8,%rax,1),%xmm0
apply_noise_main:
    movslq %ecx,%rcx
    dec %rcx
    shl $0x2,%r9d
    lea ff_sbr_noise_table(%rip),%rax
    lea (%rdi,%r9,2),%rdi
    add %r9,%rsi
    add %r9,%rdx
    shl $0x3,%rcx
    pxor %xmm5,%xmm5
    neg %r9
apply_noise_main.loop:
    movdqa (%rdx,%r9,1),%xmm1
    movdqu 0x10(%rcx,%rax,1),%xmm3
    movdqu 0x20(%rcx,%rax,1),%xmm4
    add $0x20,%rcx
    and $0xff8,%rcx
apply_noise_main.b:
    movdqa %xmm1,%xmm2
    punpckhdq %xmm1,%xmm2
    punpckldq %xmm1,%xmm1
    mulps %xmm3,%xmm1
    mulps %xmm4,%xmm2
    movdqa (%rsi,%r9,1),%xmm3
    movdqa %xmm3,%xmm4
    punpckhdq %xmm3,%xmm4
    punpckldq %xmm3,%xmm3
    movdqa %xmm3,%xmm6
    pcmpeqd %xmm5,%xmm6
    movdqa %xmm4,%xmm7
    pcmpeqd %xmm5,%xmm7
    mulps %xmm0,%xmm3
    mulps %xmm0,%xmm4
    pand %xmm6,%xmm1
    pand %xmm7,%xmm2
apply_noise_main.c:
    movdqu (%rdi,%r9,2),%xmm6
    movdqu 0x10(%rdi,%r9,2),%xmm7
    addps %xmm1,%xmm3
    addps %xmm2,%xmm4
    addps %xmm3,%xmm6
    addps %xmm4,%xmm7
    movdqu %xmm6,(%rdi,%r9,2)
    movdqu %xmm7,0x10(%rdi,%r9,2)
apply_noise_main.d:
    add $0x10,%r9
    jl apply_noise_main.loop
apply_noise_main.done:
    ret
")

/-- `apply_noise_main` alone. -/
def bodyMain : Program := parse("
apply_noise_main:
    movslq %ecx,%rcx
    dec %rcx
    shl $0x2,%r9d
    lea ff_sbr_noise_table(%rip),%rax
    lea (%rdi,%r9,2),%rdi
    add %r9,%rsi
    add %r9,%rdx
    shl $0x3,%rcx
    pxor %xmm5,%xmm5
    neg %r9
apply_noise_main.loop:
    movdqa (%rdx,%r9,1),%xmm1
    movdqu 0x10(%rcx,%rax,1),%xmm3
    movdqu 0x20(%rcx,%rax,1),%xmm4
    add $0x20,%rcx
    and $0xff8,%rcx
apply_noise_main.b:
    movdqa %xmm1,%xmm2
    punpckhdq %xmm1,%xmm2
    punpckldq %xmm1,%xmm1
    mulps %xmm3,%xmm1
    mulps %xmm4,%xmm2
    movdqa (%rsi,%r9,1),%xmm3
    movdqa %xmm3,%xmm4
    punpckhdq %xmm3,%xmm4
    punpckldq %xmm3,%xmm3
    movdqa %xmm3,%xmm6
    pcmpeqd %xmm5,%xmm6
    movdqa %xmm4,%xmm7
    pcmpeqd %xmm5,%xmm7
    mulps %xmm0,%xmm3
    mulps %xmm0,%xmm4
    pand %xmm6,%xmm1
    pand %xmm7,%xmm2
apply_noise_main.c:
    movdqu (%rdi,%r9,2),%xmm6
    movdqu 0x10(%rdi,%r9,2),%xmm7
    addps %xmm1,%xmm3
    addps %xmm2,%xmm4
    addps %xmm3,%xmm6
    addps %xmm4,%xmm7
    movdqu %xmm6,(%rdi,%r9,2)
    movdqu %xmm7,0x10(%rdi,%r9,2)
apply_noise_main.d:
    add $0x10,%r9
    jl apply_noise_main.loop
apply_noise_main.done:
    ret
")

/-- Each entry as a fragment: 0, 1, 2 one block each; 3 with the routine it
falls into. -/
def body0 : Program := parse("
ff_sbr_hf_apply_noise_0_sse2:
    movdqa ps_noise0(%rip),%xmm0
    jmp apply_noise_main
    nop 6
")

def body1 : Program := parse("
ff_sbr_hf_apply_noise_1_sse2:
    and $0x1,%r8
    shl $0x4,%r8
    lea ps_noise13(%rip),%rax
    movdqa (%r8,%rax,1),%xmm0
    jmp apply_noise_main
    nop 8
    nop 1
")

def body2 : Program := parse("
ff_sbr_hf_apply_noise_2_sse2:
    movdqa ps_noise2(%rip),%xmm0
    jmp apply_noise_main
    nop 6
")

def body3 : Program := parse("
ff_sbr_hf_apply_noise_3_sse2:
    and $0x1,%r8
    shl $0x4,%r8
    lea ps_noise13+16(%rip),%rax
    movdqa (%r8,%rax,1),%xmm0
apply_noise_main:
    movslq %ecx,%rcx
    dec %rcx
    shl $0x2,%r9d
    lea ff_sbr_noise_table(%rip),%rax
    lea (%rdi,%r9,2),%rdi
    add %r9,%rsi
    add %r9,%rdx
    shl $0x3,%rcx
    pxor %xmm5,%xmm5
    neg %r9
apply_noise_main.loop:
    movdqa (%rdx,%r9,1),%xmm1
    movdqu 0x10(%rcx,%rax,1),%xmm3
    movdqu 0x20(%rcx,%rax,1),%xmm4
    add $0x20,%rcx
    and $0xff8,%rcx
apply_noise_main.b:
    movdqa %xmm1,%xmm2
    punpckhdq %xmm1,%xmm2
    punpckldq %xmm1,%xmm1
    mulps %xmm3,%xmm1
    mulps %xmm4,%xmm2
    movdqa (%rsi,%r9,1),%xmm3
    movdqa %xmm3,%xmm4
    punpckhdq %xmm3,%xmm4
    punpckldq %xmm3,%xmm3
    movdqa %xmm3,%xmm6
    pcmpeqd %xmm5,%xmm6
    movdqa %xmm4,%xmm7
    pcmpeqd %xmm5,%xmm7
    mulps %xmm0,%xmm3
    mulps %xmm0,%xmm4
    pand %xmm6,%xmm1
    pand %xmm7,%xmm2
apply_noise_main.c:
    movdqu (%rdi,%r9,2),%xmm6
    movdqu 0x10(%rdi,%r9,2),%xmm7
    addps %xmm1,%xmm3
    addps %xmm2,%xmm4
    addps %xmm3,%xmm6
    addps %xmm4,%xmm7
    movdqu %xmm6,(%rdi,%r9,2)
    movdqu %xmm7,0x10(%rdi,%r9,2)
apply_noise_main.d:
    add $0x10,%r9
    jl apply_noise_main.loop
apply_noise_main.done:
    ret
")

end Kraken.Examples.Sbr.HfApplyNoise
