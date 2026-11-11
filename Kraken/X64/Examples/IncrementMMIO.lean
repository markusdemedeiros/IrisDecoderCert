/-
Memory-mapped incrementer over the `Sys`-based denotational monad: a control-store
latches an incremented value into device state, a load reads it back and idles the
device, and the returned value is fed back through arithmetic to pin it. The device
state lives in `σ`, so it would survive a jump.
-/
import Kraken.Device

open Std.WP
open Kraken

set_option mvcgen.warning false
set_option grind.warning false
set_option maxHeartbeats 1000000

inductive Incr
  | idle
  | done (answer : Int)
  deriving DecidableEq, Repr

abbrev VALUE_ADDR : BitVec 64 := 4096

abbrev incrDev : Device Incr where
  readStep addr dmem d :=
    if addr = VALUE_ADDR then
      match d with
      | .done answer => some (answer, dmem, .idle)
      | .idle => none
    else none
  writeStep addr v dmem _d :=
    if addr = VALUE_ADDR then some (dmem, .done (v + 1)) else none

def mmioProg : X64M Incr Unit := do
  Op.devStore incrDev VALUE_ADDR 41
  let answer ← Op.devLoad incrDev VALUE_ADDR
  Op.devStore incrDev VALUE_ADDR (answer - 1)

theorem mmio_correct :
    ⦃fun _ _ s => s.device = Incr.idle ∧ Mem.loadInt s.machine.dmem VALUE_ADDR 8 = none⦄
      mmioProg
      ⦃fun _ _ _ s => s.device = Incr.done 42; fun _ _ => True⦄ := by
  vcgen [mmioProg] with finish
