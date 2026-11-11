import Kraken.X64.Parser

/-!
# `ff_aac_sbr_ctx_alloc_init`: the program text

`ff_aac_sbr_ctx_alloc_init(ac, che, id_aac)` of `libavcodec/aacsbr_template.c` (FFmpeg n8.1,
l.70-113, `aacsbr.o`, section `.text.unlikely.`, see `scripts/sbr/README.md`), from `to_program`
with the relocated operands named (`av_mallocz`, `av_tx_init`, `ff_psdsp_init`, `ff_sbrdsp_init`,
and the four procedures `aacsbr_func_ptr_init` stores), labels `.LXXXX` at the addresses in the
object, and cuts after every second store of the straight-line part (at most two stores per
block). `ff_ps_ctx_init` (`aacps.h`) and `aacsbr_func_ptr_init` are inlined; `sbr_turnoff`
(l.58-68) is inlined as plain stores (`memset` of `spectrum_params` is one 4-byte and one 2-byte
store).
-/

open Kraken Kraken.X64.Parser

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.Init

def body : Program := parse("
ff_aac_sbr_ctx_alloc_init:
    push %rbp
    mov %rsp,%rbp
    push %r15
    push %r14
    push %rbx
    sub $0x18,%rsp
    mov %edx,%r14d
    mov %rsi,%r15
    mov $0x88ba0,%edi
    call av_mallocz
ff_aac_sbr_ctx_alloc_init.L22:
    test %rax,%rax
    je ff_aac_sbr_ctx_alloc_init.L17a
ff_aac_sbr_ctx_alloc_init.L2b:
    mov %rax,%rbx
    mov %rax,(%r15)
    add $0x1e120,%rax
    mov %rax,0x9e40(%rbx)
ff_aac_sbr_ctx_alloc_init.L3e:
    lea 0x23520(%rbx),%rax
    mov %rax,0x13c00(%rbx)
    mov 0x28978(%rbx),%eax
    mov %eax,0x28974(%rbx)
ff_aac_sbr_ctx_alloc_init.L58:
    mov %r14d,0x2892c(%rbx)
    xor %eax,%eax
    mov %eax,0x28930(%rbx)
ff_aac_sbr_ctx_alloc_init.L67:
    mov %rax,0x28924(%rbx)
    movl $0x20,0x28978(%rbx)
ff_aac_sbr_ctx_alloc_init.L78:
    mov %eax,0x28980(%rbx)
    mov $0xffffffff,%ecx
    mov %ecx,0x41d68(%rbx)
ff_aac_sbr_ctx_alloc_init.L89:
    mov %ecx,0x2c2a8(%rbx)
    mov %ecx,0x2893c(%rbx)
ff_aac_sbr_ctx_alloc_init.L95:
    movw $0xffff,0x28940(%rbx)
    mov $0x480,%ecx
    mov %ecx,0x2c2a0(%rbx)
ff_aac_sbr_ctx_alloc_init.La9:
    mov %ecx,0x41d60(%rbx)
    lea -0x1c(%rbp),%r9
    movl $0x35000000,(%r9)
ff_aac_sbr_ctx_alloc_init.Lba:
    lea 0x88af0(%rbx),%rdi
    lea 0x88af8(%rbx),%rsi
    mov %rax,(%rsp)
    mov $0x1,%edx
    mov $0x1,%ecx
    mov $0x40,%r8d
    call av_tx_init
ff_aac_sbr_ctx_alloc_init.Le1:
    test %eax,%eax
    js ff_aac_sbr_ctx_alloc_init.L17f
ff_aac_sbr_ctx_alloc_init.Le9:
    lea -0x1c(%rbp),%r9
    movl $0xc7800000,(%r9)
    lea 0x88ae0(%rbx),%rdi
    lea 0x88ae8(%rbx),%rsi
    movq $0x0,(%rsp)
    mov $0x1,%edx
    mov $0x1,%ecx
    mov $0x40,%r8d
    call av_tx_init
ff_aac_sbr_ctx_alloc_init.L11f:
    test %eax,%eax
    js ff_aac_sbr_ctx_alloc_init.L17f
ff_aac_sbr_ctx_alloc_init.L123:
    lea 0x74ab8(%rbx),%rdi
    call ff_psdsp_init
ff_aac_sbr_ctx_alloc_init.L12f:
    mov %rbx,%rdi
    add $0x88b00,%rdi
    call ff_sbrdsp_init
ff_aac_sbr_ctx_alloc_init.L13e:
    lea sbr_lf_gen(%rip),%rax
    mov %rax,0x88b70(%rbx)
    lea sbr_hf_assemble(%rip),%rax
    mov %rax,0x88b78(%rbx)
ff_aac_sbr_ctx_alloc_init.L15a:
    lea sbr_x_gen(%rip),%rax
    mov %rax,0x88b80(%rbx)
    lea sbr_hf_inverse_filter(%rip),%rax
    mov %rax,0x88b88(%rbx)
    xor %eax,%eax
    jmp ff_aac_sbr_ctx_alloc_init.L17f
ff_aac_sbr_ctx_alloc_init.L17a:
    mov $0xfffffff4,%eax
ff_aac_sbr_ctx_alloc_init.L17f:
    add $0x18,%rsp
    pop %rbx
    pop %r14
    pop %r15
    pop %rbp
ff_aac_sbr_ctx_alloc_init.done:
    ret
")

end Kraken.Examples.Sbr.Init
