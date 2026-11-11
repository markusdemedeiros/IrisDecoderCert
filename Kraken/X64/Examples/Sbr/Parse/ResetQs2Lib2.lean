import Kraken.X64.Examples.Sbr.Parse.ResetQs2Lib

/-!
# `sbr_reset`, `AV_QSORT` copy 2: more helpers (element addresses)
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse Kraken.Examples.Sbr.Parse.Qsort

namespace Kraken.Examples.Sbr.Reset

/-- `lea -0x4(%rdx)` with `rdx` the last element. -/
theorem ep_sub6 (t₀ : MachineData) (o hi1 : Nat) (h : 3 ≤ hi1) :
    QS.ep t₀ o hi1 - 2#64 + 18446744073709551612#64 = QS.ep t₀ o (hi1 - 3) := by
  have e : (18446744073709551612#64 : BitVec 64) = -2#64 + 18446744073709551614#64 := by decide
  rw [e, ← BitVec.add_assoc, ← BitVec.sub_eq_add_neg, ep_sub2 t₀ o hi1 (by omega),
    ep_sub4 t₀ o (hi1 - 1) (by omega), Nat.sub_sub]

theorem ep_inj {t₀ : MachineData} (hR : 0x578 ≤ (t₀.regs.get64 .rsp).toNat) {o p q : Nat}
    (hp : o + 2 * (p + 1) ≤ 0x548) (hq : o + 2 * (q + 1) ≤ 0x548) :
    QS.ep t₀ o p = QS.ep t₀ o q ↔ p = q := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [ep_toNat hR hp, ep_toNat hR hq] at this
    omega
  · rintro rfl; rfl

/-- `add $2` / `lea 0x2(..)` on an element address. -/
theorem ep_add2 (t₀ : MachineData) (o q : Nat) : QS.ep t₀ o q + 2#64 = QS.ep t₀ o (q + 1) := by
  simp only [QS.ep]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- `add $-2` / `lea -0x2(..)` on an element address. -/
theorem ep_m2 (t₀ : MachineData) (o q : Nat) (h : 1 ≤ q) :
    QS.ep t₀ o q + 18446744073709551614#64 = QS.ep t₀ o (q - 1) := by
  have e : (18446744073709551614#64 : BitVec 64) = -2#64 := by decide
  rw [e, ← BitVec.sub_eq_add_neg, ep_sub2 t₀ o q h]

theorem ep_le_iff {t₀ : MachineData} (hR : 0x578 ≤ (t₀.regs.get64 .rsp).toNat) {o p q : Nat}
    (hp : o + 2 * (p + 1) ≤ 0x548) (hq : o + 2 * (q + 1) ≤ 0x548) :
    (QS.ep t₀ o p).toNat ≤ (QS.ep t₀ o q).toNat ↔ p ≤ q := by
  rw [ep_toNat hR hp, ep_toNat hR hq]; omega

theorem ep_lt_iff {t₀ : MachineData} (hR : 0x578 ≤ (t₀.regs.get64 .rsp).toNat) {o p q : Nat}
    (hp : o + 2 * (p + 1) ≤ 0x548) (hq : o + 2 * (q + 1) ≤ 0x548) :
    (QS.ep t₀ o p).toNat < (QS.ep t₀ o q).toNat ↔ p < q := by
  rw [ep_toNat hR hp, ep_toNat hR hq]; omega

/-- A variant step with an equal measure and a smaller phase. -/
theorem lex_phase_lt {x a b p q d d' : Nat} (h : a = b) (hp : p % 2 ^ 64 < q % 2 ^ 64) :
    lex [x, a, p, d] < lex [x, b, q, d'] := by
  subst h; exact lex_cons_lt_cons rfl (lex_cons_lt_cons rfl (lex_cons_lt_of_lt rfl hp))

end Kraken.Examples.Sbr.Reset
