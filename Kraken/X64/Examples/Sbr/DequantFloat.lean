import Kraken.X64.Examples.Sbr.Spec

/-! # The dequant float hypothesis (R1) holds

`DequantFloatModel` (`Spec.lean`) says that a binary32 pattern `≤ 0x43000000` (a non-negative
float `≤ 128.0f`), widened by `BitVec.f32to64` and compared with the double `1E20` by
`BitVec.f64cmp`, is ordered and strictly below. `f32to64` is defined through Lean core's float
model (`UnpackedFloat.unpack` / `round` / `pack`), so this is a theorem. The proof:
1. `unpack_binary32_le`: such a pattern (other than `+0`) unpacks to a positive finite value
   `m * 2^e` with `m < 2^24` and `-149 ≤ e ≤ -16`.
2. `round_binary64`: rounding it to binary64 is exact (only shifts the mantissa to 53 bits).
3. `unpack_pack_binary64`: packing a canonical normal binary64 value and unpacking it again is
   the identity (`f64cmp` re-unpacks the bits).
4. `f64cmp_dbl1E20_finite`: `1E20` unpacks to exponent `14`; any positive canonical value with
   a smaller exponent compares below it.
-/

namespace Kraken.F32

open Float.Model UnpackedFloat

theorem log2_shift {m k : Nat} (hm : m ≠ 0) : (m <<< k).log2 = m.log2 + k := by
  have h1 := Nat.log2_self_le hm
  have h2 := (Nat.lt_log2_self (n := m))
  rw [Nat.shiftLeft_eq, Nat.log2_eq_iff (Nat.mul_ne_zero hm (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _)))]
  constructor
  · rw [Nat.pow_add]; exact Nat.mul_le_mul_right _ h1
  · rw [show m.log2 + k + 1 = (m.log2 + 1) + k by omega, Nat.pow_add]
    exact Nat.mul_lt_mul_of_pos_right h2 (Nat.two_pow_pos _)

theorem shiftToTargetExponent_canonical {M : Nat} {E : Int} (hM : M.log2 = 52)
    (hE : -1074 ≤ E) :
    shiftToTargetExponent .binary64 M E .exact = (⟨M, false, false⟩, E) := by
  have h0 : (Format.binary64.targetExponent (totalExponent M E) - E).toNat = 0 := by
    simp only [Format.targetExponent, totalExponent, Format.mantissaBits, Format.minExponent,
      hM, Nat.reduceSub, Nat.reduceAdd, Int.reducePow]
    omega
  simp only [shiftToTargetExponent, shiftToExponent, h0, Int.natCast_zero, Int.add_zero]
  rfl

theorem roundWithAccuracy_canonical (s : Sign) {M : Nat} {E : Int} (hM : M.log2 = 52)
    (hE : -1074 ≤ E) :
    roundWithAccuracy .binary64 s M E .exact =
      .finite s M E (by
        have := Nat.log2_self_le (n := M) (by intro h; simp [h] at hM)
        have := Nat.two_pow_pos M.log2; omega) := by
  unfold roundWithAccuracy
  have hr : ({ mantissa := M, roundBit := false, stickyBit := false } :
      ExtendedMantissa).roundedMantissa = M := rfl
  have hM0 : M ≠ 0 := by intro h; simp [h] at hM
  simp only [shiftToTargetExponent_canonical hM hE, hr, hM0, dite_false]

/-- `round` into binary64 of a value with at most 53 significant bits and a moderate exponent
is exact: it only shifts the mantissa up to 53 bits. -/
theorem round_binary64 (s : Sign) {m : Nat} (e : Int) (hm : 0 < m) (hl : m.log2 ≤ 52)
    (he : -1000 ≤ e) :
    round .binary64 s m e =
      .finite s (m <<< (52 - m.log2)) (e - (52 - m.log2 : Nat))
        (by rw [Nat.shiftLeft_eq]; exact Nat.mul_pos hm (Nat.two_pow_pos _)) := by
  have hL := log2_shift (m := m) (k := 52 - m.log2) (by omega)
  unfold round
  simp only [Format.targetExponent, totalExponent, decreaseExponent, Format.mantissaBits,
    Format.minExponent, Nat.reduceSub, Nat.reduceAdd, Int.reducePow]
  have hk : (e - max (↑m.log2 + 1 + e - ((53 : Nat) : Int)) (3 - 1024 - ((53 : Nat) : Int))).toNat
      = 52 - m.log2 := by omega
  rw [hk]
  rw [roundWithAccuracy_canonical s (by rw [hL]; omega) (by omega)]

theorem unpackSign_packComponents {spec : Format} {sign exponent mantissa} :
    unpackSign (packComponents spec sign exponent mantissa) = sign.toBitVec := by
  ext i hi
  have : i = 0 := by omega
  subst this
  simp [unpackSign, packComponents, BitVec.getLsbD_append, BitVec.getElem_append]

theorem ofBitVec_toBitVec (s : Sign) : Sign.ofBitVec s.toBitVec = s := by
  cases s <;> rfl

/-- Unpacking a packed canonical normal binary64 value gives it back. -/
theorem unpack_pack_binary64 (s : Sign) {M : Nat} {E : Int} (hM : M.log2 = 52)
    (hE1 : -1074 ≤ E) (hE2 : E ≤ 971) (hpos : 0 < M) :
    unpack .binary64 (pack .binary64 (.finite s M E hpos)) = .finite s M E hpos := by
  have h1 := Nat.log2_self_le (n := M) (by omega)
  have h2 := Nat.lt_log2_self (n := M)
  rw [hM] at h1 h2
  have hb : ((E + ↑Format.binary64.exponentBias + ↑Format.binary64.mantissaBitsWithoutImplicit).toNat : Int)
      = E + 1075 := by
    simp only [Format.exponentBias]; omega
  have hlt : ¬ (2 ^ Format.binary64.exponentBits ≤
      (E + ↑Format.binary64.exponentBias + ↑Format.binary64.mantissaBitsWithoutImplicit).toNat + 1) := by
    show ¬ (2 ^ 11 ≤ (E + ((2 ^ (11 - 1) - 1 : Nat) : Int) + ((52 : Nat) : Int)).toNat + 1)
    simp only [Nat.reducePow, Nat.reduceSub]; omega
  simp only [UnpackedFloat.pack, hM, hlt, ite_false, Format.mantissaBits, ite_true]
  have hb' : (E + ↑Format.binary64.exponentBias + ((52 : Nat) : Int)).toNat = (E + 1075).toNat := by
    simp only [Format.exponentBias]; omega
  rw [hb']
  have hne1 : BitVec.ofNat 11 (E + 1075).toNat ≠ -1#11 := by
    intro h; have := congrArg BitVec.toNat h; simp at this; omega
  have hne0 : BitVec.ofNat 11 (E + 1075).toNat ≠ 0#11 := by
    intro h; have := congrArg BitVec.toNat h; simp at this; omega
  unfold UnpackedFloat.unpack
  simp only [unpackMantissa_packComponents, unpackExponent_packComponents,
    unpackSign_packComponents, ofBitVec_toBitVec, hne1, hne0, ite_false, finite.injEq, true_and]
  simp only [BitVec.toNat_append, BitVec.toNat_ofNat, Format.exponentBias]
  constructor
  · rw [← Nat.shiftLeft_add_eq_or_of_lt (Nat.mod_lt _ (Nat.two_pow_pos _)), Nat.shiftLeft_eq]
    simp only [Nat.reducePow, Nat.reduceMod] at h1 h2 ⊢
    omega
  · rw [Nat.mod_eq_of_lt (by omega : (E + 1075).toNat < 2 ^ 11)]; simp only [Nat.reducePow,
      Nat.reduceSub]; omega

/-- A nonzero binary32 pattern `≤ 0x43000000` (`128.0f`) unpacks to a positive finite value
with a mantissa of at most 24 bits and exponent in `[-149, -16]`. -/
theorem unpack_binary32_le (v : BitVec 32) (hv : v.toNat ≤ 0x43000000) (h0 : v ≠ 0) :
    ∃ m e h, unpack .binary32 v = .finite .positive m e h ∧ m.log2 ≤ 23 ∧ -149 ≤ e ∧ e ≤ -16 := by
  have hv0 : v.toNat ≠ 0 := by intro h; exact h0 (BitVec.eq_of_toNat_eq (by simpa using h))
  have hE : (unpackExponent (spec := .binary32) v).toNat = v.toNat / 2 ^ 23 % 2 ^ 8 := by
    simp [unpackExponent, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  have hM : (unpackMantissa (spec := .binary32) v).toNat = v.toNat % 2 ^ 23 := by
    simp [unpackMantissa, BitVec.extractLsb'_toNat]
  have hs : unpackSign (spec := .binary32) v = 0#1 := by
    apply BitVec.eq_of_toNat_eq
    simp only [unpackSign, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
    simp only [Format.binary32, BitVec.toNat_ofNat, Nat.zero_mod]; omega
  have hne1 : unpackExponent (spec := .binary32) v ≠ -1#_ := by
    intro h; have := congrArg BitVec.toNat h; rw [hE] at this; simp at this; omega
  unfold UnpackedFloat.unpack
  have hsp : Sign.ofBitVec 0#1 = .positive := rfl
  simp only [hs, hne1, ite_false, hsp]
  have hbias : ((Format.binary32.exponentBias : Nat) : Int) = 127 := rfl
  have hMlt : (unpackMantissa (spec := .binary32) v).toNat < 2 ^ 23 := by rw [hM]; omega
  by_cases hz : unpackExponent (spec := .binary32) v = 0#8
  · have hz' := congrArg BitVec.toNat hz
    rw [hE, BitVec.toNat_ofNat, Nat.zero_mod] at hz'
    have hm0 : (unpackMantissa (spec := .binary32) v).toNat ≠ 0 := by
      rw [hM]; omega
    have hm0' : unpackMantissa (spec := .binary32) v ≠ 0#23 := by
      intro h; exact hm0 (by rw [h]; rfl)
    simp only [hz, hm0', ite_true, dite_false, BitVec.toNat_ofNat, Nat.zero_mod]
    refine ⟨_, _, ?pf, rfl, ?_, ?_, ?_⟩
    case pf => omega
    · exact Nat.le_of_lt_succ ((Nat.log2_lt hm0).mpr (by omega))
    · rw [hbias]; omega
    · rw [hbias]; omega
  · have hz' : (unpackExponent (spec := .binary32) v).toNat ≠ 0 := by
      intro h; exact hz (BitVec.eq_of_toNat_eq (by simpa using h))
    have hA : (1#1 ++ unpackMantissa (spec := .binary32) v).toNat =
        2 ^ 23 + (unpackMantissa (spec := .binary32) v).toNat := by
      rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt hMlt]; rfl
    simp only [hz, ite_false]
    refine ⟨_, _, ?pf, rfl, ?_, ?_, ?_⟩
    case pf => omega
    · rw [hA]; exact Nat.le_of_lt_succ ((Nat.log2_lt (by omega)).mpr (by omega))
    · rw [hbias]; omega
    · rw [hbias, hE]; omega

theorem unpack_dbl1E20 :
    unpack .binary64 (pack .binary64 (unpack .binary64 (0x4415AF1D78B58C40#64 : BitVec 64))) =
      .finite .positive 0x15AF1D78B58C40 14 (by decide) := by
  rfl

/-- `f64cmp` against `1E20` of the bits of a canonical normal positive binary64 value with
exponent below `14` (i.e. value below `2^67`): ordered, not less, not equal. -/
theorem f64cmp_dbl1E20_finite {M : Nat} {E : Int} (hM : M.log2 = 52)
    (hE1 : -1074 ≤ E) (hE2 : E < 14) (hpos : 0 < M) :
    BitVec.f64cmp 0x4415AF1D78B58C40#64 (UnpackedFloat.pack .binary64 (.finite .positive M E hpos))
      = (false, false, false) := by
  have hR := unpack_pack_binary64 .positive hM hE1 (by omega) hpos
  simp only [BitVec.f64cmp, BitVec.toFloat64, Float.ofBits, Float.isNaN, Float.Model.ofBits,
    Float.Model.isNaN, Float.Model.unpack, Float.Model.pack, UInt64.toBitVec_ofBitVec,
    hR, unpack_dbl1E20, UnpackedFloat.isNaN, Bool.or_false, Bool.not_false, Bool.true_and]
  have hlt : ∀ a b : Float, decide (a < b) = a.toModel.unpack.lt b.toModel.unpack := by
    intro a b; cases h : a.toModel.unpack.lt b.toModel.unpack <;>
      simp [LT.lt, Float.lt, Float.Model.lt, h]
  have heq : ∀ a b : Float, (a == b) = a.toModel.unpack.beq b.toModel.unpack := fun _ _ => rfl
  simp only [hlt, heq, Float.Model.unpack, hR, unpack_dbl1E20]
  have hc : compare (14 : Int) E = .gt := by
    have h1 : ¬ (14 : Int) < E := by omega
    have h2 : ¬ (14 : Int) = E := by omega
    simp only [compare, compareOfLessAndEq, h1, h2, ite_false]
  simp only [UnpackedFloat.lt, UnpackedFloat.beq, UnpackedFloat.compare, hc, Ordering.then]
  decide

/-- (R1) holds: `DequantFloatModel` is a theorem of the float model. -/
theorem dequantFloatModel_holds : Kraken.Examples.Sbr.DequantFloatModel := by
  intro v hv
  by_cases h0 : v = 0
  · subst h0; decide
  obtain ⟨m, e, hm, hu, hl, he1, he2⟩ := unpack_binary32_le v hv h0
  have hL := log2_shift (m := m) (k := 52 - m.log2) (by omega)
  unfold BitVec.f32to64
  rw [hu]
  simp only [Kraken.roundUnpacked]
  rw [round_binary64 .positive e hm (by omega) (by omega)]
  exact f64cmp_dbl1E20_finite (by rw [hL]; omega) (by omega) (by omega) _

end Kraken.F32
