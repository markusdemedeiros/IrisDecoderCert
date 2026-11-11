import Kraken.X64M
import Kraken.Easm

open Std.WP
open Kraken

set_option mvcgen.warning false
set_option grind.warning false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

/-- `(%rdi,%r15,8)` as an `AddrExpr`. -/
def aeSib : AddrExpr := { base := some (.reg .rdi), idx := some ⟨.r15, .W64⟩, disp := .int64 0 }

-- movq $42, (%rdi,%r15,8); movq (%rdi,%r15,8), %rax
def sibProg : X64M Unit Unit := do
  Op.mov (.mem aeSib) (.imm (.int64 42))
  Op.mov (.reg (.low .rax .W64)) (.regOrMem (.mem aeSib))

theorem sib_correct (env₀ : Env) (s₀ : MachineData) (v : Int)
    (h_mapped : Mem.loadInt s₀.dmem
        (AddrExpr.interp64 env₀.labels aeSib s₀.regs (.mk 0 (0 + Int64.ofNat env₀.curSize))) 8 = some v)
    (h_back : Mem.loadInt
        (Mem.storeInt s₀.dmem (AddrExpr.interp64 env₀.labels aeSib s₀.regs (.mk 0 (0 + Int64.ofNat env₀.curSize))) 8 42)
        (AddrExpr.interp64 env₀.labels aeSib s₀.regs (.mk 0 (0 + Int64.ofNat env₀.curSize))) 8 = some 42) :
    ⦃fun env rip sd => env = env₀ ∧ rip = 0 ∧ sd = ⟨s₀, ()⟩⦄ sibProg
      ⦃fun _ _ _ s => s.machine.regs.rax = BitVec.ofInt 64 42; fun _ _ => True⦄ := by
  have h42 : (BitVec.setWidth 64 ((42 : Int64)).toBitVec).toInt = 42 := by decide
  vcgen [sibProg] with (first (easm) (skip))
  simp_all
  -- all_goals (simp_all <;> bv_decide)
