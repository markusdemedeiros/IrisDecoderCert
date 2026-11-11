/-
Carry chain on the deep embedding: `n` add-with-carry instructions stepped by
the machine-founded weakest-precondition specs of Kraken/MachineWP.lean. The
program, the prefix and the postcondition mirror `AdcChain`, so the two report
the stepping cost of the same verification through the two encodings. The
chain holds no jump, so the goal quantifies over the ambient code: the run
computes the sum wherever the chain sits.
-/
import Kraken.MachineWP

open Kraken
open Std.WP
open MachineWP

namespace SegAdcChain

def chain : Nat → Program
  | 0 => []
  | n + 1 =>
    Directive.instr (.regular .W64 .W64
      (.adc (.reg (.low .rax .W64)) (.regOrMem (.reg (.low .rbx .W64))))) :: chain n

def prog (n : Nat) : Program :=
  Directive.instr (.regular .W64 .W64
      (.mov (.reg (.low .rax .W64)) (.imm (.int64 0))))
    :: Directive.instr (.regular .W64 .W64
      (.add (.reg (.low .rax .W64)) (.imm (.int64 0))))   -- clears the carry
    :: Directive.instr (.regular .W64 .W64
      (.mov (.reg (.low .rbx .W64)) (.imm (.int64 3))))
    :: chain n

def Goal (n : Nat) : Prop :=
  ∀ [CodeEnv],
    ⦃ fun _ => True ⦄
    prog n
    ⦃ fun _ s => s.regs.get64 .rax = BitVec.ofNat 64 (3 * n) ⦄

end SegAdcChain
