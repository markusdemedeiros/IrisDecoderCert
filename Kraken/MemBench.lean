/-
Memory-op benchmarks for the `easm` discharge pipeline: a single load, and a
store followed by a reload of the same cell. The `Kraken.easm` trace reports
which discharge path closed each memory VC.
-/
import Kraken.X64M
import Kraken.Easm
open Std.WP
open Kraken

set_option mvcgen.warning false
set_option grind.warning false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

/-- `-8(%rsp)` as an `AddrExpr`. -/
def aeRspM8 : AddrExpr := { base := some (.reg .rsp), idx := none, disp := .int64 (-8) }

def loadProg : X64M Unit Unit :=
  Op.mov (.reg (.low .rax .W64)) (.regOrMem (.mem aeRspM8))

theorem load_single (env₀ : Env) (s₀ : MachineData) (v : Int)
    (h_load : Mem.loadInt s₀.dmem
        (AddrExpr.interp64 env₀.labels aeRspM8 s₀.regs (.mk 0 (0 + Int64.ofNat env₀.curSize))) 8 = some v) :
    ⦃fun env rip sd => env = env₀ ∧ rip = 0 ∧ sd = ⟨s₀, ()⟩⦄ loadProg
      ⦃fun _ _ _ s => s.machine.regs.rax = BitVec.ofInt 64 v; fun _ _ => True⦄ := by
  vcgen [loadProg] with (first (easm) (skip))
  all_goals (simp_all <;> bv_decide)

def storeLoadProg : X64M Unit Unit := do
  Op.mov (.mem aeRspM8) (.imm (.int64 99))
  Op.mov (.reg (.low .rax .W64)) (.regOrMem (.mem aeRspM8))

theorem store_load_back (env₀ : Env) (s₀ : MachineData) (v : Int)
    (h_mapped : Mem.loadInt s₀.dmem
        (AddrExpr.interp64 env₀.labels aeRspM8 s₀.regs (.mk 0 (0 + Int64.ofNat env₀.curSize))) 8 = some v)
    (h_back : Mem.loadInt
        (Mem.storeInt s₀.dmem (AddrExpr.interp64 env₀.labels aeRspM8 s₀.regs (.mk 0 (0 + Int64.ofNat env₀.curSize))) 8 99)
        (AddrExpr.interp64 env₀.labels aeRspM8 s₀.regs (.mk 0 (0 + Int64.ofNat env₀.curSize))) 8 = some 99) :
    ⦃fun env rip sd => env = env₀ ∧ rip = 0 ∧ sd = ⟨s₀, ()⟩⦄ storeLoadProg
      ⦃fun _ _ _ s => s.machine.regs.rax = BitVec.ofInt 64 99; fun _ _ => True⦄ := by
  have h99 : (BitVec.setWidth 64 ((99 : Int64)).toBitVec).toInt = 99 := by decide
  vcgen [storeLoadProg] with (first (easm) (skip))
  all_goals (simp_all <;> bv_decide)
