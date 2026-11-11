/-
Register decrement chain: `n` decrements of `rax` from a concrete start.

Ground values throughout, so the discharge folds constants at every step.
Contrast `AddChain`, whose initial value is symbolic.
-/
import Kraken.X64M

open Std.WP
open Kraken

namespace DecChain

def chain : Nat → X64M Unit Unit
  | 0 => pure ()
  | n+1 => do Op.dec (.reg (.low .rax .W64)); chain n

def Goal (n : Nat) : Prop :=
  ⦃fun _ _ s => s.machine.regs.get64 .rax = BitVec.ofNat 64 n⦄ chain n
    ⦃fun _ _ _ s => s.machine.regs.get64 .rax = 0#64; fun _ _ => True⦄

end DecChain
