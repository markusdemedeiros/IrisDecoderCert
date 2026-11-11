/-
DMA incrementer over the `Sys`-based denotational monad. A control store transitions
device state and DMA-writes into a RAM buffer the store never named (device state
and data memory both change); a control load returns a status word and DMA-writes a
completion marker. All four transfers of the MMIO/DMA matrix, with device state in
`σ` so it survives control transfer.
-/
import Kraken.Device

open Std.WP
open Kraken

set_option mvcgen.warning false
set_option grind.warning false
set_option maxHeartbeats 1000000

inductive Dma
  | idle
  | busy
  deriving DecidableEq, Repr

abbrev CTRL_ADDR : BitVec 64 := 8192
abbrev IN_ADDR : BitVec 64 := 16384
abbrev OUT_ADDR : BitVec 64 := 16392

abbrev dmaDev : Device Dma where
  readStep addr dmem d :=
    if addr = CTRL_ADDR then
      match d with
      | .busy => some (1, Mem.storeInt dmem OUT_ADDR 8 99, .idle)
      | .idle => none
    else none
  writeStep addr v dmem d :=
    if addr = CTRL_ADDR then
      match d with
      | .idle => some (Mem.storeInt dmem IN_ADDR 8 (v + 1), .busy)
      | .busy => none
    else none

def dmaStartProg : X64M Dma Unit :=
  Op.devStore dmaDev CTRL_ADDR 42

theorem dma_start_correct (m0 : DataMem) :
    ⦃fun _ _ s => s.device = Dma.idle ∧ s.machine.dmem = m0 ∧
        Mem.loadInt s.machine.dmem CTRL_ADDR 8 = none⦄
      dmaStartProg
      ⦃fun _ _ _ s => s.device = Dma.busy ∧ s.machine.dmem = Mem.storeInt m0 IN_ADDR 8 43;
        fun _ _ => True⦄ := by
  sym =>
    vcgen [dmaStartProg]
    all_goals finish

def dmaFinishProg : X64M Dma Unit := do
  let _ ← Op.devLoad dmaDev CTRL_ADDR
  pure ()

theorem dma_finish_correct (m0 : DataMem) :
    ⦃fun _ _ s => s.device = Dma.busy ∧ s.machine.dmem = m0 ∧
        Mem.loadInt s.machine.dmem CTRL_ADDR 8 = none⦄
      dmaFinishProg
      ⦃fun _ _ _ s => s.device = Dma.idle ∧ s.machine.dmem = Mem.storeInt m0 OUT_ADDR 8 99;
        fun _ _ => True⦄ := by
  sym =>
    vcgen [dmaFinishProg]
    all_goals finish
