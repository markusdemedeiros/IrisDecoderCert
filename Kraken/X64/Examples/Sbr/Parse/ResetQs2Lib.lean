import Kraken.X64.Examples.Sbr.Parse.ResetQsLib

/-!
# `sbr_reset`, `AV_QSORT` copy 2 (`vk0`): helpers of the median and partition blocks

* `sf_wr`: the frame slots `A2.SF` survive a write below them (the array, the stack).
* `av_toInt`: an element read back as an `int16`.
* `sw16_zx32`: the low half of a 32-bit move (`mov %r14d,%r9d`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse Kraken.Examples.Sbr.Parse.Qsort

namespace Kraken.Examples.Sbr.Reset

/-- The slots of `A2.SF` are above frame offset `0x470`. -/
theorem sf_wr {fr : List UInt8} (hF : FrOk fr) {o n : Nat} (h : o + n ≤ 0x470) (v : Int)
    {e : REnv} {a : RArgs} {t₀ : MachineData} {k0 k2 : Nat} :
    A2.SF (wr fr o (Int.toBytes n v)) e a t₀ k0 k2 ↔ A2.SF fr e a t₀ k0 k2 := by
  have h' : o + n ≤ 0x548 := by omega
  simp only [A2.SF, A2.SE, A2.SD, A2.SC, A2.SB, A2.SA]
  rw [slot_wr32 hF h' v (d := 0x80) (by simp only [rb]; omega),
    slot_wr32 hF h' v (d := 0x88) (by simp only [rb]; omega),
    slot_wr32 hF h' v (d := 0x38) (by simp only [rb]; omega),
    slot_wr32 hF h' v (d := 0x50) (by simp only [rb]; omega),
    slot_wr32 hF h' v (d := 0x100) (by simp only [rb]; omega),
    slot_wr64 hF h' v (d := 0x40) (by simp only [rb]; omega),
    slot_wr64 hF h' v (d := 0x30) (by simp only [rb]; omega),
    slot_wr64 hF h' v (d := 0x48) (by simp only [rb]; omega)]

theorem av_toInt (fr : List UInt8) (o q : Nat) :
    (BitVec.ofInt 16 (QS.av fr o q)).toInt = QS.av fr o q := by
  simp only [QS.av, A2.fv, BitVec.ofInt_toInt]

theorem sw16_zx32 (x : BitVec 64) :
    BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32 x)) = BitVec.setWidth 16 x := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]

variable [CodeEnv]

/-- `stkPhi_eq` for a state literal (after a store). -/
theorem stkPhi_lit {k : Nat} {e : REnv} {a : RArgs} {ra : Int64} {t₀ : MachineData} {st : St}
    {fr : List UInt8} {R : Reg64s} {z} {sf} {D : Mem 64} (hm : D =⋆ Mm k e a ra t₀ st fr)
    (hF : FrOk fr) (hbp : R.get64 .rbp = t₀.regs.get64 .rsp - 8#64)
    (hR : 0x578 ≤ (t₀.regs.get64 .rsp).toNat) {o N : Nat} (hoN : o + 2 * (N + 1) ≤ 0x548)
    {S : List Iv} (hS : QS.StkRel fr t₀ o S) (hW : Within N S) (hn : S.length ≤ 64) :
    QS.stkPhi { regs := R, zmms := z, status := sf, dmem := D } S.length = phi S :=
  stkPhi_eq (s := { regs := R, zmms := z, status := sf, dmem := D }) hm hF hbp hR hoN hS hW hn

end Kraken.Examples.Sbr.Reset
