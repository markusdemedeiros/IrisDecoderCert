import Kraken.X64M
import Kraken.Easm
import Kraken.StateSimp
import Std.Tactic.BVDecide

open Std.WP
open Kraken

set_option mvcgen.warning false
set_option grind.warning false
set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

def pushPopProg : X64M Unit Unit := do
  Op.push (.regOrMem (.reg (.low .rbx .W64)))
  Op.mov (.reg (.low .rbx .W64)) (.imm (.int64 0))
  Op.pop (.reg (.low .rbx .W64))

theorem pushpop_roundtrip (s : MachineData)
    (h_mapped : Mem.loadInt s.dmem ((s.regs.get64 .rsp) - 8#64) 8
      = some ((s.regs.get64 .rbx).toInt))
    (h_back : Mem.loadInt
        (Mem.storeInt s.dmem ((s.regs.get64 .rsp) - 8#64) 8
          ((s.regs.get64 .rbx).toInt))
        ((s.regs.get64 .rsp) - 8#64) 8
      = some ((s.regs.get64 .rbx).toInt)) :
    ⦃fun _ _ s0 => s0 = ⟨s, ()⟩⦄ pushPopProg
      ⦃fun _ _ _ s' => s'.machine.regs.get64 .rbx = s.regs.get64 .rbx; fun _ _ => True⦄ := by
  vcgen [pushPopProg] with (first (easm) (skip))
  simp_all
  -- all_goals (simp_all [BitVec.ofInt_toInt])
