/-
Kraken - checks for the integer `@[spec low]` rules in Kraken/Rules/IntMisc.lean

Each theorem runs `vcgen ... with finish` over a short straight-line program.
The register sections compute concrete values; the memory sections access a
64-byte block at `%rdi` (including scaled-index forms `d(%rdi,%rcx,s)` with
`%rcx < 4`) and check that the separation-logic frame survives.
-/

import Kraken.X64.Parser
import Kraken.MachineWP
import Kraken.SeparationMem
import Kraken.Rules.IntMisc

open Kraken.X64.Parser
open Kraken
open Std.WP
open MachineWP
open Lean.Order
open scoped Kraken.Rules.GenericMem.Norm Kraken.Rules.IntMisc.SubReg

set_option experimental.vcgen true

namespace IntMiscExamples

section lea_imul
def lea_imul_prog : Program := parse("mov $0x14,%eax\nlea (%rax,%rax,4),%rdx\nlea 0x4(,%rax,4),%esi\nimul $0x3,%rdx,%rdx\nimul %esi,%eax")
variable [layout : _root_.Layout]
local instance lea_imul_env : CodeEnv := ⟨layout lea_imul_prog⟩
theorem lea_imul_correct (d : MachineData) :
    ⦃ fun s => s = d ⦄ lea_imul_prog ⦃ fun _ s => s.regs.get64 .rdx = 300#64 ∧ s.regs.get64 .rsi = 84#64 ∧ s.regs.get64 .rax = 1680#64 ⦄ := by
  vcgen [lea_imul_prog] with finish
end lea_imul

section ext_cmov_set
def ext_cmov_set_prog : Program := parse("mov $0x1ca,%eax\nmovzbl %al,%ecx\nmovzwl %ax,%r8d\nmovslq %eax,%r9\nmov $0x54,%esi\ncmp %esi,%ecx\ncmovae %esi,%ecx\nsete %r10b\ntest %eax,%eax\nsetne %r11b")
variable [layout : _root_.Layout]
local instance ext_cmov_set_env : CodeEnv := ⟨layout ext_cmov_set_prog⟩
theorem ext_cmov_set_correct (d : MachineData) :
    ⦃ fun s => s = d ⦄ ext_cmov_set_prog ⦃ fun _ s => s.regs.get64 .rcx = 0x54#64 ∧ s.regs.get64 .r8 = 0x1ca#64 ∧ s.regs.get64 .r9 = 0x1ca#64 ∧ (s.regs.get64 .r10).setWidth 8 = 0#8 ∧ (s.regs.get64 .r11).setWidth 8 = 1#8 ⦄ := by
  vcgen [ext_cmov_set_prog] with finish
end ext_cmov_set

section logic_sbb
def logic_sbb_prog : Program := parse("mov $0x6,%eax\nxor $0x3,%eax\nand $0x6,%eax\nor %eax,%ecx\nmov $0x0,%rdx\ncmp $0x1,%rdx\nsbb $0x0,%rdx")
variable [layout : _root_.Layout]
local instance logic_sbb_env : CodeEnv := ⟨layout logic_sbb_prog⟩
theorem logic_sbb_correct (d : MachineData) :
    ⦃ fun s => s = d ⦄ logic_sbb_prog ⦃ fun _ s => s.regs.get64 .rax = 4#64 ∧ s.regs.get64 .rdx = 0xffffffffffffffff#64 ⦄ := by
  vcgen [logic_sbb_prog] with finish
end logic_sbb

section neg_not_dec
def neg_not_dec_prog : Program := parse("mov $0x5,%eax\nneg %eax\nnot %eax\nadd %eax,%eax\ndec %eax")
variable [layout : _root_.Layout]
local instance neg_not_dec_env : CodeEnv := ⟨layout neg_not_dec_prog⟩
theorem neg_not_dec_correct (d : MachineData) :
    ⦃ fun s => s = d ⦄ neg_not_dec_prog ⦃ fun _ s => s.regs.get64 .rax = 7#64 ⦄ := by
  vcgen [neg_not_dec_prog] with finish
end neg_not_dec

section sub16
def sub16_prog : Program := parse("mov $0x5,%eax\nsub $0x1,%ax")
variable [layout : _root_.Layout]
local instance sub16_env : CodeEnv := ⟨layout sub16_prog⟩
theorem sub16_correct (d : MachineData) :
    ⦃ fun s => s = d ⦄ sub16_prog ⦃ fun _ s => s.regs.get64 .rax = 4#64 ∧ s.regs.get64 .rbx = d.regs.get64 .rbx ⦄ := by
  vcgen [sub16_prog] with finish
end sub16

section shr_imm
def shr_imm_prog : Program := parse("mov $0x5,%eax\nshr $0x1,%eax")
variable [layout : _root_.Layout]
local instance shr_imm_env : CodeEnv := ⟨layout shr_imm_prog⟩
theorem shr_imm_correct (d : MachineData) :
    ⦃ fun s => s = d ⦄ shr_imm_prog ⦃ fun _ s => s.regs.get64 .rax = 2#64 ⦄ := by
  vcgen [shr_imm_prog] with finish
end shr_imm

section sar_imm
def sar_imm_prog : Program := parse("mov $0x5,%eax\nsar $0x1,%rax")
variable [layout : _root_.Layout]
local instance sar_imm_env : CodeEnv := ⟨layout sar_imm_prog⟩
theorem sar_imm_correct (d : MachineData) :
    ⦃ fun s => s = d ⦄ sar_imm_prog ⦃ fun _ s => s.regs.get64 .rax = 2#64 ⦄ := by
  vcgen [sar_imm_prog] with finish
end sar_imm

section shl_imm
def shl_imm_prog : Program := parse("mov $0x5,%eax\nshl $0x3,%eax")
variable [layout : _root_.Layout]
local instance shl_imm_env : CodeEnv := ⟨layout shl_imm_prog⟩
theorem shl_imm_correct (d : MachineData) :
    ⦃ fun s => s = d ⦄ shl_imm_prog ⦃ fun _ s => s.regs.get64 .rax = 40#64 ⦄ := by
  vcgen [shl_imm_prog] with finish
end shl_imm

section shift_cl
def shift_cl_prog : Program := parse("mov $0x5,%eax\nmov $0x3,%cl\nshl %cl,%eax\nsar %cl,%rbx\nmov $0x7,%edx")
variable [layout : _root_.Layout]
local instance shift_cl_env : CodeEnv := ⟨layout shift_cl_prog⟩
theorem shift_cl_correct (d : MachineData) :
    ⦃ fun s => s = d ⦄ shift_cl_prog ⦃ fun _ s => s.regs.get64 .rax = 40#64 ∧ s.regs.get64 .rbx = (d.regs.get64 .rbx).sshiftRight 3
        ∧ (s.regs.get64 .rcx).setWidth 8 = 3#8 ∧ s.regs.get64 .rdx = 7#64 ⦄ := by
  vcgen [shift_cl_prog] with finish
end shift_cl

section shift_chain
def shift_chain_prog : Program := parse("mov $0x5,%eax\nshl $0x3,%eax\nshr $0x1,%eax\nsar $0x2,%rax\nmov $0x2,%ecx\nshl %cl,%rax")
variable [layout : _root_.Layout]
local instance shift_chain_env : CodeEnv := ⟨layout shift_chain_prog⟩
theorem shift_chain_correct (d : MachineData) :
    ⦃ fun s => s = d ⦄ shift_chain_prog ⦃ fun _ s => s.regs.get64 .rax = 20#64 ⦄ := by
  vcgen [shift_chain_prog] with finish
end shift_chain

section sub16_sym
def sub16_sym_prog : Program := parse("sub $0x1,%bx")
variable [layout : _root_.Layout]
local instance sub16_sym_env : CodeEnv := ⟨layout sub16_sym_prog⟩
theorem sub16_sym_correct (d : MachineData) :
    ⦃ fun s => s = d ⦄ sub16_sym_prog ⦃ fun _ s => s.regs.get64 .rbx =
        (d.regs.get64 .rbx).replaceLow ((d.regs.get64 .rbx).setWidth 16 - 1#16) ⦄ := by
  vcgen [sub16_sym_prog] with finish
end sub16_sym

section off_base
-- A structure embedded at `rdi + 0x40`: fields at other displacements from `rdi`.
def off_base_prog : Program := parse("mov 0x48(%rdi),%eax\nmov %eax,0x4c(%rdi)\nmov 0x50(%rdi,%rcx,4),%edx\nmov %edx,0x40(%rdi,%rcx,8)")
variable [layout : _root_.Layout]
local instance off_base_env : CodeEnv := ⟨layout off_base_prog⟩
theorem off_base_frame (d : MachineData) (R : DataMem → Prop) (hrcx : (d.regs.get64 .rcx).toNat < 4)
    (h : d.dmem =⋆ Mem.Blocks [(d.regs.get64 .rsi, 8), (d.regs.get64 .rdi + 0x40#64, 32)] ⋆ R) :
    ⦃ fun s => s = d ⦄ off_base_prog
    ⦃ fun _ s => s.dmem =⋆ Mem.Blocks [(d.regs.get64 .rsi, 8), (d.regs.get64 .rdi + 0x40#64, 32)] ⋆ R ⦄ := by
  vcgen [off_base_prog] with finish
end off_base

section mem0
def mem0_prog : Program := parse("mov 0x4(%rdi,%rcx,4),%eax\nadd 0x8(%rdi,%rcx,4),%eax\nsub %eax,0x10(%rdi)\naddq $0x1,0x18(%rdi)")
variable [layout : _root_.Layout]
local instance mem0_env : CodeEnv := ⟨layout mem0_prog⟩
theorem mem0_frame (d : MachineData) (R : DataMem → Prop)
    (_hc : (d.regs.get64 .rcx).toNat < 4)
    (h_mem : d.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, 64)] ⋆ R) :
    ⦃ fun s => s = d ⦄ mem0_prog
    ⦃ fun _ s => s.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, 64)] ⋆ R ⦄ := by
  vcgen [mem0_prog] with finish
end mem0

section mem1
def mem1_prog : Program := parse("andl $0xff,0x20(%rdi,%rcx,4)\norb $0x1,0x1(%rdi)\nxor 0x8(%rdi),%eax\ncmpb $0x1,(%rdi,%rcx,1)")
variable [layout : _root_.Layout]
local instance mem1_env : CodeEnv := ⟨layout mem1_prog⟩
theorem mem1_frame (d : MachineData) (R : DataMem → Prop)
    (_hc : (d.regs.get64 .rcx).toNat < 4)
    (h_mem : d.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, 64)] ⋆ R) :
    ⦃ fun s => s = d ⦄ mem1_prog
    ⦃ fun _ s => s.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, 64)] ⋆ R ⦄ := by
  vcgen [mem1_prog] with finish
end mem1

section mem2
def mem2_prog : Program := parse("cmpl $0x1,0x4(%rdi,%rcx,4)\ncmp %rax,0x8(%rdi)\ncmp 0x8(%rdi,%rcx,1),%r8b\ntest %al,0x8(%rdi)\ntestb $0x1,0x8(%rdi)")
variable [layout : _root_.Layout]
local instance mem2_env : CodeEnv := ⟨layout mem2_prog⟩
theorem mem2_frame (d : MachineData) (R : DataMem → Prop)
    (_hc : (d.regs.get64 .rcx).toNat < 4)
    (h_mem : d.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, 64)] ⋆ R) :
    ⦃ fun s => s = d ⦄ mem2_prog
    ⦃ fun _ s => s.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, 64)] ⋆ R ⦄ := by
  vcgen [mem2_prog] with finish
end mem2

section mem3
def mem3_prog : Program := parse("movw $0x5,0x8(%rdi)\nmovl $0x7,(%rdi,%rcx,4)\nmovq $0x5,(%rdi,%rcx,8)\nmov %ax,0x8(%rdi)\nmov %r8b,(%rdi,%rcx,1)")
variable [layout : _root_.Layout]
local instance mem3_env : CodeEnv := ⟨layout mem3_prog⟩
theorem mem3_frame (d : MachineData) (R : DataMem → Prop)
    (_hc : (d.regs.get64 .rcx).toNat < 4)
    (h_mem : d.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, 64)] ⋆ R) :
    ⦃ fun s => s = d ⦄ mem3_prog
    ⦃ fun _ s => s.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, 64)] ⋆ R ⦄ := by
  vcgen [mem3_prog] with finish
end mem3

section mem4
def mem4_prog : Program := parse("setl 0x8(%rdi)\nnegl 0x8(%rdi)")
variable [layout : _root_.Layout]
local instance mem4_env : CodeEnv := ⟨layout mem4_prog⟩
theorem mem4_frame (d : MachineData) (R : DataMem → Prop)
    (_hc : (d.regs.get64 .rcx).toNat < 4)
    (h_mem : d.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, 64)] ⋆ R) :
    ⦃ fun s => s = d ⦄ mem4_prog
    ⦃ fun _ s => s.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, 64)] ⋆ R ⦄ := by
  vcgen [mem4_prog] with finish
end mem4

section mem5
def mem5_prog : Program := parse("notl 0x8(%rdi)\ndecl 0x8(%rdi)")
variable [layout : _root_.Layout]
local instance mem5_env : CodeEnv := ⟨layout mem5_prog⟩
theorem mem5_frame (d : MachineData) (R : DataMem → Prop)
    (_hc : (d.regs.get64 .rcx).toNat < 4)
    (h_mem : d.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, 64)] ⋆ R) :
    ⦃ fun s => s = d ⦄ mem5_prog
    ⦃ fun _ s => s.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, 64)] ⋆ R ⦄ := by
  vcgen [mem5_prog] with finish
end mem5

section mem6
def mem6_prog : Program := parse("sbb %eax,0x8(%rdi)\nsub %rax,0x10(%rdi,%rcx,8)")
variable [layout : _root_.Layout]
local instance mem6_env : CodeEnv := ⟨layout mem6_prog⟩
theorem mem6_frame (d : MachineData) (R : DataMem → Prop)
    (_hc : (d.regs.get64 .rcx).toNat < 4)
    (h_mem : d.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, 64)] ⋆ R) :
    ⦃ fun s => s = d ⦄ mem6_prog
    ⦃ fun _ s => s.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, 64)] ⋆ R ⦄ := by
  vcgen [mem6_prog] with finish
end mem6

section mem7
def mem7_prog : Program := parse("movslq 0x8(%rdi,%rcx,4),%rdx\ncmove 0x8(%rdi),%rax\nsub 0x8(%rdi),%rdx")
variable [layout : _root_.Layout]
local instance mem7_env : CodeEnv := ⟨layout mem7_prog⟩
theorem mem7_frame (d : MachineData) (R : DataMem → Prop)
    (_hc : (d.regs.get64 .rcx).toNat < 4)
    (h_mem : d.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, 64)] ⋆ R) :
    ⦃ fun s => s = d ⦄ mem7_prog
    ⦃ fun _ s => s.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, 64)] ⋆ R ⦄ := by
  vcgen [mem7_prog] with finish
end mem7

end IntMiscExamples
#print axioms IntMiscExamples.lea_imul_correct
#print axioms IntMiscExamples.ext_cmov_set_correct
#print axioms IntMiscExamples.logic_sbb_correct
#print axioms IntMiscExamples.neg_not_dec_correct
#print axioms IntMiscExamples.sub16_correct
#print axioms IntMiscExamples.shift_chain_correct
#print axioms IntMiscExamples.sub16_sym_correct
#print axioms IntMiscExamples.off_base_frame
#print axioms IntMiscExamples.shr_imm_correct
#print axioms IntMiscExamples.sar_imm_correct
#print axioms IntMiscExamples.shl_imm_correct
#print axioms IntMiscExamples.shift_cl_correct
#print axioms IntMiscExamples.mem0_frame
#print axioms IntMiscExamples.mem1_frame
#print axioms IntMiscExamples.mem2_frame
#print axioms IntMiscExamples.mem3_frame
#print axioms IntMiscExamples.mem4_frame
#print axioms IntMiscExamples.mem5_frame
#print axioms IntMiscExamples.mem6_frame
#print axioms IntMiscExamples.mem7_frame
