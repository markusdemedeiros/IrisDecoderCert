import Kraken.X64.Examples.Sbr.Parse.ResetQsLib

/-!
# `sbr_reset`, `AV_QSORT` copies 1, 3, 4: element stores

* `sd_st`: a 16-bit store to element `q` of the frame array: the new memory, `FrOk`, the saved
  `ac` / `sbr` slots, the stack, and the array (`upd`).
* `sw16_zx64`: the low 16 bits after `movzwl`-style zero extension through 32 bits.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse Kraken.Examples.Sbr.Parse.Qsort

namespace Kraken.Examples.Sbr.Reset

theorem sw16_zx64 (y : BitVec 64) :
    BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32 y)) = BitVec.setWidth 16 y := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]

/-- A 16-bit value read as an element is the element. -/
theorem ofInt_av (fr : List UInt8) (o q : Nat) :
    BitVec.ofInt 16 (QS.av fr o q) = BitVec.ofInt 16 (Int.ofBytes (slice fr (o + 2 * (q + 1)) 2)) :=
  av_ofInt fr o q

theorem toInt_av {fr : List UInt8} {o q : Nat} {x : BitVec 16}
    (h : x = BitVec.ofInt 16 (QS.av fr o q)) : x.toInt = QS.av fr o q := by
  rw [h]; simp only [QS.av, A2.fv, BitVec.ofInt_toInt]

@[simp] theorem toInt_ofInt_av (fr : List UInt8) (o q : Nat) :
    (BitVec.ofInt 16 (QS.av fr o q)).toInt = QS.av fr o q := toInt_av rfl

/-- `lea -4(end)`: element `q - 3`. -/
theorem ep_m6 {t₀ : MachineData} (hR : 0x578 ≤ (t₀.regs.get64 .rsp).toNat) {o q : Nat}
    (h : o + 2 * (q + 1) ≤ 0x548) (hq : 3 ≤ q) :
    QS.ep t₀ o q - 2#64 + 18446744073709551612#64 = QS.ep t₀ o (q - 3) := by
  apply ep_eq_of_toNat hR (by omega)
  rw [BitVec.toNat_add, ep_m2_toNat hR h]; simp only [BitVec.toNat_ofNat]
  have := (t₀.regs.get64 .rsp).isLt
  omega

/-- Element addresses are injective. -/
theorem q1_ep_inj {t₀ : MachineData} (hR : 0x578 ≤ (t₀.regs.get64 .rsp).toNat) {o p q : Nat}
    (hp : o + 2 * (p + 1) ≤ 0x548) (hq : o + 2 * (q + 1) ≤ 0x548) :
    QS.ep t₀ o p = QS.ep t₀ o q ↔ p = q := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [ep_toNat hR hp, ep_toNat hR hq] at this
    omega
  · rintro rfl; rfl

/-- `add $2` / `lea 0x2(..)` on an element address. -/
theorem q1_ep_add2 (t₀ : MachineData) (o q : Nat) :
    QS.ep t₀ o q + 2#64 = QS.ep t₀ o (q + 1) := by
  simp only [QS.ep]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- `add $-2` on an element address. -/
theorem q1_ep_m2 (t₀ : MachineData) (o q : Nat) (h : 1 ≤ q) :
    QS.ep t₀ o q + 18446744073709551614#64 = QS.ep t₀ o (q - 1) := by
  have e : (18446744073709551614#64 : BitVec 64) = -2#64 := by decide
  rw [e, ← BitVec.sub_eq_add_neg, ep_sub2 t₀ o q h]

/-- A variant step with an equal measure and a smaller phase. -/
theorem q1_lex_phase_lt {x a b p q d d' : Nat} (h : a = b) (hp : p % 2 ^ 64 < q % 2 ^ 64) :
    lex [x, a, p, d] < lex [x, b, q, d'] := by
  subst h; exact lex_cons_lt_cons rfl (lex_cons_lt_cons rfl (lex_cons_lt_of_lt rfl hp))

/-- A variant step with an equal measure and phase, and a smaller last digit. -/
theorem q1_lex_last_lt {x a b p d d' : Nat} (h : a = b) (hd : d % 2 ^ 64 < d' % 2 ^ 64) :
    lex [x, a, p, d] < lex [x, b, p, d'] := by
  subst h
  exact lex_cons_lt_cons rfl (lex_cons_lt_cons rfl (lex_cons_lt_cons rfl
    (lex_cons_lt_of_lt rfl hd)))

/-- Two element stores that exchange elements `i` and `j`. -/
theorem av_swap {fr fr1 fr2 : List UInt8} {o i j : Nat} {v1 v2 : Int}
    (h1 : ∀ r, QS.av fr1 o r = upd (QS.av fr o) j v1 r)
    (h2 : ∀ r, QS.av fr2 o r = upd (QS.av fr1 o) i v2 r)
    (e1 : v1 = QS.av fr o i) (e2 : v2 = QS.av fr o j) : QS.av fr2 o = swap (QS.av fr o) i j := by
  have h1' : QS.av fr1 o = upd (QS.av fr o) j v1 := funext h1
  funext r
  rw [h2, h1', e1, e2, upd_upd_swap]

variable [CodeEnv]

/-- A 16-bit store to element `q` of the frame array. -/
theorem sd_st {k : Nat} {e : REnv} {a : RArgs} {ra : Int64} {t₀ : MachineData} {st : St}
    {fr : List UInt8} {m : Mem 64} (hm : m =⋆ Mm k e a ra t₀ st fr) (hF : FrOk fr) {o q : Nat}
    (h : o + 2 * (q + 1) + 2 ≤ 0x530) (ho : 0x400 ≤ o + 2 * (q + 1)) (x : BitVec 16) :
    (m.storeInt (QS.ep t₀ o q) 2 x.toInt
      =⋆ Mm k e a ra t₀ st (wr fr (o + 2 * (q + 1)) (Int.toBytes 2 x.toInt)))
    ∧ FrOk (wr fr (o + 2 * (q + 1)) (Int.toBytes 2 x.toInt))
    ∧ frSlot64 (wr fr (o + 2 * (q + 1)) (Int.toBytes 2 x.toInt)) 0x40 = frSlot64 fr 0x40
    ∧ frSlot64 (wr fr (o + 2 * (q + 1)) (Int.toBytes 2 x.toInt)) 0x30 = frSlot64 fr 0x30
    ∧ (∀ {o' : Nat} {S : List Iv}, S.length ≤ 64 →
        (QS.StkRel (wr fr (o + 2 * (q + 1)) (Int.toBytes 2 x.toInt)) t₀ o' S
          ↔ QS.StkRel fr t₀ o' S))
    ∧ (∀ r, QS.av (wr fr (o + 2 * (q + 1)) (Int.toBytes 2 x.toInt)) o r
        = upd (QS.av fr o) q x.toInt r) := by
  refine ⟨av_store hm hF (by omega) _, ?_, slot_wr64 hF (by omega) _ (by simp only [rb]; omega),
    slot_wr64 hF (by omega) _ (by simp only [rb]; omega),
    fun hS => stk_wr hF (by omega) _ hS ho, av_wr hF (by omega) x⟩
  unfold FrOk at *
  rw [wr_length (by rw [Int.toBytes_length, hF]; omega), hF]

end Kraken.Examples.Sbr.Reset
