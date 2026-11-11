import Kraken.X64M
import Std.Tactic.BVDecide

open Std.WP
open Kraken

set_option mvcgen.warning false
set_option grind.warning false
set_option maxHeartbeats 1000000

def condProg (l : Int64) : X64M Unit Unit := do
  Op.dec (.reg (.low .rax .W64))
  Op.jcc .nz l
  Op.mov (.reg (.low .rbx .W64)) (.imm (.int64 7))

theorem cond_correct (l : Int64) :
    ⦃fun _ _ _ => True⦄
      condProg l
      ⦃fun _ _ _ s => (s.machine.regs.get64 .rbx) = 7#64; fun _ _ => True⦄ := by
  vcgen [condProg] with finish
