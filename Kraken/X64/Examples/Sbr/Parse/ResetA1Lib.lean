import Kraken.InfoOff
import Kraken.X64.Examples.Sbr.Parse.ResetTable

/-!
# `sbr_reset`, shard A1: shared lemmas

* `cc_*`: the condition codes of a `cmp` (`from_result (a - b)`) as comparisons of `toNat` /
  `toInt` (a `simp` set, `cc_simp`).
* `A1S.congr`: the A1 state survives a step that keeps `rsp`, `rbp` and the memory.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

namespace Kraken.Examples.Sbr.Reset

/-! ## Condition codes of `cmp` -/

theorem borrow_sub {w : Nat} (a b : BitVec w) :
    ((((a - b).toNat : Int) != (a.toNat : Int) - (b.toNat : Int))) = decide (a.toNat < b.toNat) := by
  have ha := a.isLt; have hb := b.isLt
  rw [BitVec.toNat_sub]
  by_cases h : a.toNat < b.toNat
  · have e : (2 ^ w - b.toNat + a.toNat) % 2 ^ w = 2 ^ w - b.toNat + a.toNat := Nat.mod_eq_of_lt (by omega)
    rw [e]; simp only [h, decide_true, bne_iff_ne, ne_eq]; omega
  · have e : (2 ^ w - b.toNat + a.toNat) % 2 ^ w = a.toNat - b.toNat := by
      rw [show 2 ^ w - b.toNat + a.toNat = (a.toNat - b.toNat) + 2 ^ w by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    rw [e]; simp only [h, decide_false, bne_eq_false_iff_eq]; omega

theorem cc_z_sub {w : Nat} (a b : BitVec w) (f : StatusFlags.from_result.Remaining) :
    CondCode.z.interp (StatusFlags.from_result (a - b) f) = decide (a = b) := by
  rw [CondCode.interp_z, StatusFlags.zf_from_result_sub]
  by_cases h : a = b <;> simp [h]

theorem cc_nz_sub {w : Nat} (a b : BitVec w) (f : StatusFlags.from_result.Remaining) :
    CondCode.nz.interp (StatusFlags.from_result (a - b) f) = !decide (a = b) := by
  rw [CondCode.interp_nz, StatusFlags.zf_from_result_sub]
  by_cases h : a = b <;> simp [h]

theorem cc_c_sub {w : Nat} (a b : BitVec w) (af of : Bool) :
    CondCode.c.interp (StatusFlags.from_result (a - b)
      { cf := (a - b).unsigned != a.unsigned - b.unsigned, af := af, of := of })
      = decide (a.toNat < b.toNat) := by
  rw [CondCode.interp_c, StatusFlags.cf_from_result]
  exact borrow_sub a b

theorem cc_nc_sub {w : Nat} (a b : BitVec w) (af of : Bool) :
    CondCode.nc.interp (StatusFlags.from_result (a - b)
      { cf := (a - b).unsigned != a.unsigned - b.unsigned, af := af, of := of })
      = decide (b.toNat ≤ a.toNat) := by
  rw [CondCode.interp_nc, StatusFlags.cf_from_result]
  show (!((((a - b).toNat : Int) != (a.toNat : Int) - (b.toNat : Int)))) = _
  rw [borrow_sub]
  by_cases h : a.toNat < b.toNat <;> simp [h] <;> omega

theorem cc_a_sub {w : Nat} (a b : BitVec w) (af of : Bool) :
    CondCode.a.interp (StatusFlags.from_result (a - b)
      { cf := (a - b).unsigned != a.unsigned - b.unsigned, af := af, of := of })
      = decide (b.toNat < a.toNat) := by
  rw [CondCode.interp_a, StatusFlags.cf_from_result, StatusFlags.zf_from_result_sub]
  show (!((((a - b).toNat : Int) != (a.toNat : Int) - (b.toNat : Int))) && !(a == b)) = _
  rw [borrow_sub]
  by_cases h : a = b
  · subst h; simp
  · have hn : a.toNat ≠ b.toNat := fun h' => h (BitVec.eq_of_toNat_eq h')
    have hb : (a == b) = false := by simpa using h
    rw [hb]
    by_cases h2 : a.toNat < b.toNat <;> simp [h2] <;> omega

theorem cc_be_sub {w : Nat} (a b : BitVec w) (af of : Bool) :
    CondCode.be.interp (StatusFlags.from_result (a - b)
      { cf := (a - b).unsigned != a.unsigned - b.unsigned, af := af, of := of })
      = decide (a.toNat ≤ b.toNat) := by
  rw [CondCode.interp_be, StatusFlags.cf_from_result, StatusFlags.zf_from_result_sub]
  show (((((a - b).toNat : Int) != (a.toNat : Int) - (b.toNat : Int))) || (a == b)) = _
  rw [borrow_sub]
  by_cases h : a = b
  · subst h; simp
  · have hn : a.toNat ≠ b.toNat := fun h' => h (BitVec.eq_of_toNat_eq h')
    have hb : (a == b) = false := by simpa using h
    rw [hb]
    by_cases h2 : a.toNat < b.toNat <;> simp [h2] <;> omega

@[simp] theorem sw32_64 (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]

theorem not_dec_false (p : Prop) [Decidable p] : ((!decide p) = false) = p := by
  by_cases h : p <;> simp [h]

theorem not_dec_true (p : Prop) [Decidable p] : ((!decide p) = true) = ¬ p := by
  by_cases h : p <;> simp [h]

/-! ## The sample rate -/

theorem toInt_of_eq32 {x : BitVec 32} {n : Nat} (h : x = BitVec.ofNat 32 n) (hn : n < 2 ^ 31) :
    x.toInt = n := by
  subst h; rw [BitVec.toInt_ofNat']; simp only [Int.bmod_def]; split <;> omega

theorem toInt_ne_of_ne32 {x : BitVec 32} {n : Nat} (h : ¬ x = BitVec.ofNat 32 n) (hn : n < 2 ^ 31) :
    x.toInt ≠ n := by
  intro h'; apply h; apply BitVec.eq_of_toInt_eq; rw [h']; exact (toInt_of_eq32 rfl hn).symm

/-- `rateRow` at a rate in a range that excludes every supported rate. -/
theorem rateRow_none_of {x : Int} (h : x ≠ 16000 ∧ x ≠ 22050 ∧ x ≠ 24000 ∧ x ≠ 32000 ∧ x ≠ 44100
    ∧ x ≠ 48000 ∧ x ≠ 64000 ∧ x ≠ 88200 ∧ x ≠ 96000 ∧ x ≠ 128000 ∧ x ≠ 176400 ∧ x ≠ 192000) :
    rateRow x = none := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  simp [rateRow, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]

/-! ## Transport of the A1 states -/

section Transport

variable [CodeEnv] {k : Nat} {e : REnv} {a : RArgs} {ra : Int64} {t₀ s s' : MachineData}

theorem A1S.congr {x : Args} {P P' : St → List UInt8 → Prop}
    (h1 : s'.regs.get64 .rsp = s.regs.get64 .rsp) (h2 : s'.regs.get64 .rbp = s.regs.get64 .rbp)
    (h3 : s'.dmem = s.dmem) (hP : ∀ st fr, P st fr → P' st fr) (h : A1S k e a ra t₀ s x P) :
    A1S k e a ra t₀ s' x P' := by
  obtain ⟨hC, hB, ⟨hr, hb⟩, st, fr, hx, hsp, hfm, hfr, hp, hm⟩ := h
  exact ⟨hC, hB, ⟨h1 ▸ hr, h2 ▸ hb⟩, st, fr, hx, hsp, hfm, hfr, hP _ _ hp, h3 ▸ hm⟩

theorem RD.congr (h1 : s'.regs.get64 .rsp = s.regs.get64 .rsp)
    (h2 : s'.regs.get64 .rbp = s.regs.get64 .rbp) (h3 : s'.dmem = s.dmem)
    (h4 : s'.regs.get64 .r12 = s.regs.get64 .r12) (h5 : s'.regs.get64 .r15 = s.regs.get64 .r15)
    (h6 : s'.regs.get64 .rcx = s.regs.get64 .rcx) (h : RD k e a ra t₀ s) : RD k e a ra t₀ s' := by
  obtain ⟨hA, h12, h15, hcx⟩ := h
  exact ⟨A1S.congr h1 h2 h3 (fun _ _ x => x) hA, h4 ▸ h12, h5 ▸ h15, h6 ▸ hcx⟩

theorem AtFail.congr (h1 : s'.regs.get64 .rsp = s.regs.get64 .rsp)
    (h2 : s'.regs.get64 .rbp = s.regs.get64 .rbp) (h3 : s'.dmem = s.dmem)
    (h4 : s'.regs.get64 .r12 = s.regs.get64 .r12) (h5 : s'.regs.get64 .r15 = s.regs.get64 .r15)
    (h : AtFail k e a ra t₀ s) : AtFail k e a ra t₀ s' := by
  obtain ⟨hC, ⟨hr, hb⟩, h12, h15, rest⟩ := h
  exact ⟨hC, ⟨h1 ▸ hr, h2 ▸ hb⟩, h4 ▸ h12, h5 ▸ h15, h3 ▸ rest⟩

omit [CodeEnv] in
theorem ofInt_c8 (v : BitVec 64) : BitVec.ofInt 64 (Int.ofBytes (Int.toBytes 8 v.toInt)) = v :=
  BitVec.ofInt_ofBytes_toBytes 64 8 rfl v

theorem avctx_load {m : Mem 64} {st : St} {fr : List UInt8} (h : m =⋆ Mm k e a ra t₀ st fr) :
    m.loadInt (arg0 t₀ + 8#64) 8 = some (Int.ofBytes (Int.toBytes 8 st.x.avctx.toInt)) :=
  cell8_load (focus (Mm_avctx ..) h)

end Transport

end Kraken.Examples.Sbr.Reset

/-- `rateRow x = none` from linear facts about `x` in the context. -/
macro "rate_none" : tactic => `(tactic| (
  apply Kraken.Examples.Sbr.Reset.rateRow_none_of
  try simp only [Kraken.Examples.Sbr.Reset.srI] at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega))

/-- The condition codes of the dispatch compares, as facts on the values. -/
macro "disp_simp" : tactic => `(tactic| (
  simp only [Kraken.Examples.Sbr.Reset.cc_z_sub, Kraken.Examples.Sbr.Reset.cc_nz_sub,
    CondCode.interp_g_cmp_toInt32, CondCode.interp_le_cmp_toInt32,
    CondCode.interp_l_cmp_toInt32, CondCode.interp_ge_cmp_toInt32,
    Kraken.Examples.Sbr.Reset.cc_a_sub, Kraken.Examples.Sbr.Reset.cc_be_sub,
    Kraken.Examples.Sbr.Reset.cc_c_sub, Kraken.Examples.Sbr.Reset.cc_nc_sub,
    Int64.toBitVec_ofNat, BitVec.setWidth_setWidth_of_le,
    decide_eq_true_eq, decide_eq_false_iff_not, Kraken.Examples.Sbr.Reset.not_dec_false,
    Kraken.Examples.Sbr.Reset.not_dec_true, Kraken.Examples.Sbr.Reset.sw32_64,
    BitVec.reduceSetWidth, BitVec.reduceToInt, Int.not_lt, Int.not_le] at *))
