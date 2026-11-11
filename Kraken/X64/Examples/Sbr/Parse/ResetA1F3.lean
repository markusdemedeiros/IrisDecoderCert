import Kraken.InfoOff
import Kraken.X64.Examples.Sbr.Parse.ResetA1F2

/-!
# `sbr_reset`: `bs_freq_scale = 0`, the exit `L2003` to `L2012` (shard A1)

The prefix sums done (`Summed … nm`): `f_master` is a successful `Master` (`a1_master`).
`L2003` saves `ac` at `rbp - 0x40` and loads `n_master`, `bs_xover_band`.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Reset

variable [CodeEnv]

omit [CodeEnv] in
/-- The `bs_freq_scale = 0` bands give a successful `Master`. -/
theorem a1_master {sr : Int} {row st xo k2 alter : Nat} {fm : List UInt8}
    (hr : rateRow sr = some row) (hk0 : 1 ≤ k0Of sr row st) (hk2 : k2 ≤ 64)
    (hle : (k0Of sr row st).toNat ≤ k2) (hq : (k2 : Int) - k0Of sr row st ≤ maxQ sr)
    (ha : alter ≤ 1) (hxo : xo < nmOf (k2 - (k0Of sr row st).toNat) alter)
    (hS : Summed fm (k0Of sr row st).toNat (alter + 1) (nmOf (k2 - (k0Of sr row st).toNat) alter)
      (diffOf (k0Of sr row st).toNat k2 (nmOf (k2 - (k0Of sr row st).toNat) alter) (alter + 1))
      (nmOf (k2 - (k0Of sr row st).toNat) alter)) :
    Master sr st xo (some (k0Of sr row st))
      (some (nmOf (k2 - (k0Of sr row st).toNat) alter, fun i => u16 fm i)) := by
  generalize hK : k0Of sr row st = K at *
  generalize hk : K.toNat = k0 at *
  have hKe : (k0 : Int) = K := by omega
  subst hKe
  generalize hN : nmOf (k2 - k0) alter = N at *
  have hdb : diffOf k0 k2 N (alter + 1) ≤ 1 ∧ -2 ≤ diffOf k0 k2 N (alter + 1)
      ∧ (alter = 0 → 0 ≤ diffOf k0 k2 N (alter + 1)) := by
    simp only [diffOf]
    rcases Nat.lt_or_ge alter 1 with h | h
    · obtain rfl : alter = 0 := by omega
      simp only [nmOf, ite_true] at hN
      subst hN
      simp only [Nat.zero_add, Int.natCast_one, Int.mul_one]
      omega
    · obtain rfl : alter = 1 := by omega
      simp only [nmOf, show (1 : Nat) ≠ 0 by decide, ite_false] at hN
      subst hN
      have : ((2 * ((k2 - k0 + 2) / 4) : Nat) : Int) * ((1 + 1 : Nat) : Int)
          = 4 * (((k2 - k0 + 2) / 4 : Nat) : Int) := by
        simp only [Int.natCast_mul, Int.natCast_add]; omega
      rw [this]
      omega
  generalize hD : diffOf k0 k2 N (alter + 1) = D at *
  have hstep : ∀ i, 1 ≤ i → 1 ≤ stepOf (alter + 1) N D i := by
    intro i hi
    unfold stepOf
    repeat' split
    all_goals omega
  have hN2 : 2 ≤ N := by
    have hev : N % 2 = 0 := by rw [← hN]; unfold nmOf; split <;> omega
    omega
  rw [← hK]
  refine @Master.ok sr st xo row (k2 : Int) N _ hr (by omega) (by omega)
    (by rw [hK]; simpa only [maxQ] using hq) hxo ?_ ?_ ?_
  · have := hS.1 0 (by omega)
    simp only [fvOf] at this
    rw [hK]; exact this
  · intro i hi
    have h1 := hS.1 i (by omega)
    have h2 := hS.1 (i + 1) (by omega)
    rw [fvOf] at h2
    have := hstep (i + 1) (by omega)
    show u16 fm i < u16 fm (i + 1)
    omega
  · have := hS.1 N (by omega)
    rw [a1_fv_eq] at this
    show (u16 fm N : Int) ≤ k2
    rw [this]
    have : (D : Int) = k2 - k0 - N * (alter + 1 : Nat) := by rw [← hD]
    repeat' split
    all_goals omega


theorem a1_nm_load {k : Nat} {e : REnv} {a : RArgs} {ra : Int64} {t₀ : MachineData} {st : St}
    {fr : List UInt8} {m : Mem 64} (hm : m =⋆ Mm k e a ra t₀ st fr) :
    m.loadInt (arg1 t₀ + 0x68#64) 4 = some (Int.ofBytes (Int.toBytes 4 st.nm.toInt)) :=
  loadInt_sep _ _ 4 _ m (focus (Mm_nm ..) hm) (Int.toBytes_length 4 _) (by omega)

theorem blk_L2003 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2003" ⟨"sbr_reset.L2003", B.L2003, some "sbr_reset.L2012"⟩ := by
  info_off
  measure_hb "L2003"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hr, hk2, hle, hq, h3, ⟨hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2s, h2, hxo, hnm, hsum⟩, hm⟩, h12, h15⟩ := T.L2003.mp hs
    clear hs
    have h48 := f0_nm_48 hr hC.2.1 hq
    have hk0 := k0Of_range hr (st := u8 a.sp 0) hC.2.1
    have hA4 : u8 a.sp 4 ≤ 1 := hC.2.2.2.1
    have hM : Master a.x.sampleRate.toInt (u8 a.sp 0) (u8 a.sp 2) (some (k0A a row))
        (some (nmOf (k2 - k0N a row) (u8 a.sp 4), fOf st)) :=
      a1_master hr hk0.1 hk2 hle hq hA4 hxo hsum
    have hl : st.sp.length = 6 := by rw [hsp]; exact hC.1
    have e40 : t₀.regs.get64 .rsp - 8#64 + 18446744073709551552#64
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x40 := by bv_omega
    have ld40 := fr_load hm hF (d := 0x40) (n := 8) (by omega) (by omega)
    have hst := fr_store hm hF (d := 0x40) (n := 8) (by omega) (by omega) (t₀.regs.get64 .rdi).toInt
    have ldX := a1_sp_load hst hl (i := 2) (by decide)
    rw [a1_slice_one (by rw [hl]; decide), a1_ofBytes_one, hsp,
      show BitVec.ofNat 64 (0x1c + 2) = 30#64 from rfl] at ldX
    have ldN := a1_nm_load hst
    simp only [arg1] at ldX ldN
    have iX : ∀ {x : Option Int} {v : Int}, x = some v → x.isSome = true := fun h => by rw [h]; rfl
    have hF' := fr_wr_len hF (o := rb 0x40) (n := 8) (by simp only [rb]; omega)
      (t₀.regs.get64 .rdi).toInt
    have h40 : frSlot64 (wr fr (rb 0x40) (Int.toBytes 8 (t₀.regs.get64 .rdi).toInt)) 0x40 = arg0 t₀ := by
      rw [frSlot64_wr_same hF (by omega) (by omega), BitVec.ofInt_toInt]
    have hnmv : BitVec.ofInt 32 (Int.ofBytes (Int.toBytes 4 st.nm.toInt)) = BitVec.ofNat 32
        (nmOf (k2 - k0N a row) (u8 a.sp 4)) := by
      rw [BitVec.ofInt_ofBytes_toBytes 32 4 rfl, hnm]
    have h13 : BitVec.setWidth 64 (BitVec.ofNat 32 (nmOf (k2 - k0N a row) (u8 a.sp 4)))
        = BitVec.ofNat 64 (nmOf (k2 - k0N a row) (u8 a.sp 4)) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      omega
    have h14 : BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32
        (BitVec.ofInt 8 ((a.sp.getD 2 0).toNat : Int)))) = BitVec.ofNat 8 (u8 a.sp 2) := by
      rw [BitVec.ofInt_natCast]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, u8]
      omega
    simp only [B.L2003]
    vcgen
    all_goals try subst s₀
    all_goals try subst n
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hrbp, e40,
      AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    · rw [ld40]; rfl
    · exact iX ldN
    · exact iX ldX
    · rename_i v1 hv1 v2 hv2
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hrbp, e40,
        AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero] at hv1 hv2
      rw [ldN] at hv1; obtain rfl := Option.some.inj hv1
      rw [ldX] at hv2; obtain rfl := Option.some.inj hv2
      rw [hnmv, h13]
      refine ⟨T.L2012.mpr ⟨hC, ⟨?_, ?_⟩, ?_, st, _, _, _, hM, hx, hsp,
        ⟨by rw [hk2s]; simp only [BitVec.toNat_ofNat]; omega, hBO.2⟩, hfm, hF', ?_, ?_, h40, hst⟩,
        by var_step⟩
      all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrsp, hrbp, h12]
      all_goals first
        | done
        | exact h14

end Kraken.Examples.Sbr.Reset
