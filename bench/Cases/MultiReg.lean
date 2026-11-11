/-
Multi-register chain: `n` rounds writing all fifteen general-purpose
registers, with a postcondition that reads every one of them.

Each round rewrites the same constants, so the final state is reached after
one round; what grows with `n` is the number of write equations the discharge
must look through per queried register.
-/
import Kraken.X64M

open Std.WP
open Kraken

namespace MultiReg

def round : X64M Unit Unit := do
  Op.mov (.reg (.low .rax .W64)) (.imm (.int64 1)); Op.mov (.reg (.low .rbx .W64)) (.imm (.int64 2))
  Op.mov (.reg (.low .rcx .W64)) (.imm (.int64 3)); Op.mov (.reg (.low .rdx .W64)) (.imm (.int64 4))
  Op.mov (.reg (.low .rsi .W64)) (.imm (.int64 5)); Op.mov (.reg (.low .rdi .W64)) (.imm (.int64 6))
  Op.mov (.reg (.low .rbp .W64)) (.imm (.int64 7)); Op.mov (.reg (.low .r8 .W64)) (.imm (.int64 8))
  Op.mov (.reg (.low .r9 .W64)) (.imm (.int64 9)); Op.mov (.reg (.low .r10 .W64)) (.imm (.int64 10))
  Op.mov (.reg (.low .r11 .W64)) (.imm (.int64 11)); Op.mov (.reg (.low .r12 .W64)) (.imm (.int64 12))
  Op.mov (.reg (.low .r13 .W64)) (.imm (.int64 13)); Op.mov (.reg (.low .r14 .W64)) (.imm (.int64 14))
  Op.mov (.reg (.low .r15 .W64)) (.imm (.int64 15))

def chain : Nat → X64M Unit Unit
  | 0 => pure ()
  | n+1 => do round; chain n

def Goal (n : Nat) : Prop :=
  ⦃fun _ _ _ => True⦄ chain (n+1) ⦃fun _ _ _ s =>
    s.machine.regs.get64 .rax = 1#64 ∧ s.machine.regs.get64 .rbx = 2#64 ∧ s.machine.regs.get64 .rcx = 3#64 ∧
    s.machine.regs.get64 .rdx = 4#64 ∧ s.machine.regs.get64 .rsi = 5#64 ∧ s.machine.regs.get64 .rdi = 6#64 ∧
    s.machine.regs.get64 .rbp = 7#64 ∧ s.machine.regs.get64 .r8 = 8#64 ∧ s.machine.regs.get64 .r9 = 9#64 ∧
    s.machine.regs.get64 .r10 = 10#64 ∧ s.machine.regs.get64 .r11 = 11#64 ∧ s.machine.regs.get64 .r12 = 12#64 ∧
    s.machine.regs.get64 .r13 = 13#64 ∧ s.machine.regs.get64 .r14 = 14#64 ∧ s.machine.regs.get64 .r15 = 15#64;
    fun _ _ => True⦄

end MultiReg
