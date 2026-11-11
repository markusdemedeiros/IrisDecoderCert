/-
Immediate-mov chain: `n` immediate movs to `rax`.

The program is a recursive function of `n`, so a benchmark run elaborates and
compiles a fixed amount of source no matter the size, and the driver reports
stepping, discharge and kernel time separately.
-/
import Kraken.X64M

open Std.WP
open Kraken

namespace MovChain

def chain : Nat → X64M Unit Unit
  | 0 => pure ()
  | n+1 => do Op.mov (.reg (.low .rax .W64)) (.imm (.int64 1)); chain n

def Goal (n : Nat) : Prop :=
  ⦃fun _ _ _ => True⦄ chain (n+1)
    ⦃fun _ _ _ s => s.machine.regs.get64 .rax = (BitVec.setWidth 64 (1 : Int64).toBitVec);
      fun _ _ => True⦄

end MovChain
