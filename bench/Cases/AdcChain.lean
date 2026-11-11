/-
Carry chain: `n` add-with-carry steps of `rbx` into `rax`.

Each step reads the carry the previous one wrote, so the flag equations are
live and the discharge has to fold a chain of them. The prefix clears the
carry so the result is determined.
-/
import Kraken.X64M

open Std.WP
open Kraken

namespace AdcChain

def chain : Nat → X64M Unit Unit
  | 0 => pure ()
  | n+1 => do
    Op.adc (.reg (.low .rax .W64)) (.regOrMem (.reg (.low .rbx .W64)))
    chain n

def prog (n : Nat) : X64M Unit Unit := do
  Op.mov (.reg (.low .rax .W64)) (.imm (.int64 0))
  Op.add (.reg (.low .rax .W64)) (.imm (.int64 0))   -- clears the carry
  Op.mov (.reg (.low .rbx .W64)) (.imm (.int64 3))
  chain n

def Goal (n : Nat) : Prop :=
  ⦃fun _ _ _ => True⦄
  prog n
  ⦃fun _ _ _ s => s.machine.regs.get64 .rax = BitVec.ofNat 64 (3*n)⦄

end AdcChain
