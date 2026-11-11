import Kraken.X64.Examples.Sbr.Parse.ResetQs2Lib3

/-!
# `sbr_reset`, `AV_QSORT` copy 2: helper lemmas for the pushes (`L1b20`, `L1b52`, `L1b70`)
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Parse Kraken.Examples.Sbr.Parse.Qsort

namespace Kraken.Examples.Sbr.Reset

/-- A signed `jge` after a 64-bit `cmp`. -/
theorem cc_ge64 (a b : BitVec 64) (cf af : Bool) :
    CondCode.ge.interp (StatusFlags.from_result (a - b)
      { cf := cf, af := af, of := (a - b).signed != a.signed - b.signed })
      = decide (b.toInt ≤ a.toInt) := by
  rw [CondCode.interp_ge_cmp, BitVec.slt_eq_decide]
  by_cases h : a.toInt < b.toInt <;> simp [h] <;> omega

/-- The difference of two element pointers, as a signed number. -/
theorem ep_dif_toInt {t₀ : MachineData} (hR : 0x578 ≤ (t₀.regs.get64 .rsp).toNat) {o p q : Nat}
    (hq : q ≤ p) (hp : o + 2 * (p + 1) ≤ 0x548) :
    (QS.ep t₀ o p - QS.ep t₀ o q).toInt = 2 * ((p : Int) - q) := by
  have e1 := ep_toNat hR hp
  have e2 := ep_toNat hR (o := o) (q := q) (by omega)
  have hlt := (t₀.regs.get64 .rsp).isLt
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_sub, e1, e2]
  split <;> omega

/-- The signed comparison of two pointer differences, as numbers of elements. -/
theorem ep_dif_le_iff {t₀ : MachineData} (hR : 0x578 ≤ (t₀.regs.get64 .rsp).toNat)
    {o p q p' q' : Nat} (hq : q ≤ p) (hp : o + 2 * (p + 1) ≤ 0x548) (hq' : q' ≤ p')
    (hp' : o + 2 * (p' + 1) ≤ 0x548) :
    (QS.ep t₀ o p - QS.ep t₀ o q).toInt ≤ (QS.ep t₀ o p' - QS.ep t₀ o q').toInt
      ↔ p - q ≤ p' - q' := by
  rw [ep_dif_toInt hR hq hp, ep_dif_toInt hR hq' hp']
  omega

end Kraken.Examples.Sbr.Reset
