import Kraken.X64.Examples.Sbr.Parse.ResetQsFr

/-!
# `sbr_reset`, `AV_QSORT` copies 1, 3, 4: block helpers

* `Triple.pinR`: pin the start state with the equation `s₀ = s` (`subst` eliminates the new
  state, so the goals stay in terms of the pinned one).
* Address arithmetic of the code (`end - 2`, `end - 4`, `mid`), 16-bit values, a bound on `phi`.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse Kraken.Examples.Sbr.Parse.Qsort

namespace Kraken.Examples.Sbr.Reset

/-- An opaque box for big hypotheses. -/
structure Box (p : Prop) : Prop where
  get : p

/-- Register reads through `set64`. -/
macro "regs_simp" : tactic => `(tactic| simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte])

/-- The shift count of `sar $2` / `shl` as the semantics computes it. -/
theorem qs_sh2 : (2#64).toNat % 256 % 64 = 2 := rfl

theorem qs_sh4 : (4#64).toNat % 256 % 64 = 4 := rfl

/-- The end pointer `ep q - 2` as a number. -/
theorem ep_m2_toNat {t₀ : MachineData} (hR : 0x578 ≤ (t₀.regs.get64 .rsp).toNat) {o q : Nat}
    (h : o + 2 * (q + 1) ≤ 0x548) :
    (QS.ep t₀ o q - 2#64).toNat = (t₀.regs.get64 .rsp).toNat - 0x578 + (o + 2 * (q + 1)) - 2 := by
  have e := ep_toNat hR h
  rw [BitVec.toNat_sub, e]; simp only [BitVec.toNat_ofNat]; omega

/-- `lea -2(end)`. -/
theorem ep_m4_toNat {t₀ : MachineData} (hR : 0x578 ≤ (t₀.regs.get64 .rsp).toNat) {o q : Nat}
    (h : o + 2 * (q + 1) ≤ 0x548) (ho : 2 ≤ o) :
    (QS.ep t₀ o q - 2#64 + 18446744073709551614#64).toNat
      = (t₀.regs.get64 .rsp).toNat - 0x578 + (o + 2 * (q + 1)) - 4 := by
  have e := ep_m2_toNat hR h
  rw [BitVec.toNat_add, e]; simp only [BitVec.toNat_ofNat]
  have := (t₀.regs.get64 .rsp).isLt
  omega

theorem ep_eq_of_toNat {t₀ : MachineData} (hR : 0x578 ≤ (t₀.regs.get64 .rsp).toNat) {o q : Nat}
    (h : o + 2 * (q + 1) ≤ 0x548) {x : BitVec 64}
    (hx : x.toNat = (t₀.regs.get64 .rsp).toNat - 0x578 + (o + 2 * (q + 1))) : x = QS.ep t₀ o q :=
  BitVec.eq_of_toNat_eq (by rw [hx, ep_toNat hR h])

/-- `mid = start + ((end - start) >> 2) * 2` (`sar $2` of the byte distance, scaled back). -/
theorem qs_mid_addr {t₀ : MachineData} (hR : 0x578 ≤ (t₀.regs.get64 .rsp).toNat) {o lo hi1 : Nat}
    (hl : lo + 2 ≤ hi1) (h : o + 2 * (hi1 + 1) ≤ 0x548) :
    QS.ep t₀ o lo + (QS.ep t₀ o hi1 - 2#64 - QS.ep t₀ o lo).sshiftRight 2 * 2#64
      = QS.ep t₀ o (QS.mid lo (hi1 - 1)) := by
  have e1 : QS.ep t₀ o hi1 - 2#64 - QS.ep t₀ o lo = BitVec.ofNat 64 (2 * (hi1 - 1 - lo)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, ep_m2_toNat hR h, ep_toNat hR (q := lo) (by omega), BitVec.toNat_ofNat]
    have := (t₀.regs.get64 .rsp).isLt
    omega
  have e2 : (BitVec.ofNat 64 (2 * (hi1 - 1 - lo))).sshiftRight 2
      = BitVec.ofNat 64 ((hi1 - 1 - lo) / 2) := by
    rw [BitVec.sshiftRight_eq_of_msb_false (by simp [BitVec.msb_eq_decide]; omega)]
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega
  rw [e1, e2]
  apply ep_eq_of_toNat hR (by unfold QS.mid; omega)
  rw [BitVec.toNat_add, ep_toNat hR (q := lo) (by omega), BitVec.toNat_mul, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat]
  have := (t₀.regs.get64 .rsp).isLt
  unfold QS.mid
  omega

/-- A loaded `int16` zero-extended, back to 16 bits. -/
theorem sw16_zx (x : Int) :
    BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofInt 16 x)))
      = BitVec.ofInt 16 x := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]

/-- An element as loaded. -/
theorem av_bytes (fr : List UInt8) (o q : Nat) :
    BitVec.ofInt 16 (Int.ofBytes (slice fr (o + 2 * (q + 1)) 2)) = BitVec.ofInt 16 (QS.av fr o q) :=
  (av_ofInt fr o q).symm

/-- The weight of intervals inside `[0, N)`. -/
theorem phi_le {N : Nat} : ∀ {S : List Iv}, Within N S → phi S ≤ S.length * (2 * N + 1)
  | [], _ => by simp [phi]
  | I :: S, h => by
    have hI := h I (by simp)
    have ih := phi_le (S := S) (fun J hJ => h J (by simp [hJ]))
    have e : phi (I :: S) = wt I + phi S := by simp [phi]
    rw [e, List.length_cons, Nat.succ_mul]
    unfold wt
    omega

variable [CodeEnv]

/-- `Triple.pin` with the equation the other way round. -/
theorem Triple.pinR {P : MachineData → Prop} {c : Program} {Q : Unit → MachineData → Prop}
    {E : Int64 → MachineData → Prop}
    (h : ∀ s₀, P s₀ → ⦃ fun s => s₀ = s ⦄ c ⦃ Q; E ⦄) : ⦃ P ⦄ c ⦃ Q; E ⦄ :=
  Triple.intro fun s hs => (h s hs).le_wp s rfl

end Kraken.Examples.Sbr.Reset
