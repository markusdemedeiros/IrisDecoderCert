import Kraken.X64M
import Std.Tactic.BVDecide

open Std.WP
open Kraken

set_option mvcgen.warning false
set_option grind.warning false
set_option maxHeartbeats 1000000

def swapProg : X64M Unit Unit := do
  Op.xor (.reg (.low .rax .W64)) (.regOrMem (.reg (.low .rbx .W64)))
  Op.xor (.reg (.low .rbx .W64)) (.regOrMem (.reg (.low .rax .W64)))
  Op.xor (.reg (.low .rax .W64)) (.regOrMem (.reg (.low .rbx .W64)))

theorem swap_correct (a b : BitVec 64) :
    ⦃fun _ _ s => s.machine.regs.get64 .rax = a ∧ s.machine.regs.get64 .rbx = b⦄
      swapProg
      ⦃fun _ _ _ s => s.machine.regs.get64 .rax = b ∧ s.machine.regs.get64 .rbx = a; fun _ _ => True⦄ := by
  sym =>
    vcgen [swapProg]
    all_goals finish (splits := 40)
