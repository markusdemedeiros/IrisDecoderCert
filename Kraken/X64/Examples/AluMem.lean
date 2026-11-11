import Kraken.X64M
import Kraken.Easm

open Std.WP
open Kraken

set_option mvcgen.warning false
set_option grind.warning false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

def aeRdx136 : AddrExpr := { base := some (.reg .rdx), idx := none, disp := .int64 136 }

def aluMemProg : X64M Unit Unit := do
  Op.mov (.mem aeRdx136) (.imm (.int64 42))
  Op.add (.reg (.low .rcx .W64)) (.regOrMem (.mem aeRdx136))

theorem alu_mem_correct (env₀ : Env) (s₀ : MachineData) (v : Int)
    (h_rcx : (s₀.regs.get64 .rcx) = 100#64)
    (h_mapped : Mem.loadInt s₀.dmem
        (AddrExpr.interp64 env₀.labels aeRdx136 s₀.regs (.mk 0 (0 + Int64.ofNat env₀.curSize))) 8 = some v)
    (h_back : Mem.loadInt
        (Mem.storeInt s₀.dmem (AddrExpr.interp64 env₀.labels aeRdx136 s₀.regs (.mk 0 (0 + Int64.ofNat env₀.curSize))) 8 42)
        (AddrExpr.interp64 env₀.labels aeRdx136 s₀.regs (.mk 0 (0 + Int64.ofNat env₀.curSize))) 8 = some 42) :
    ⦃fun env rip sd => env = env₀ ∧ rip = 0 ∧ sd = ⟨s₀, ()⟩⦄ aluMemProg
      ⦃fun _ _ _ s => s.machine.regs.rcx = BitVec.ofInt 64 142; fun _ _ => True⦄ := by
  have h42 : (BitVec.setWidth 64 ((42 : Int64)).toBitVec).toInt = 42 := by decide
  vcgen [aluMemProg] with (first (easm) (skip))
  all_goals (simp_all <;> bv_decide)
