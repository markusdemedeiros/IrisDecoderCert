import Kraken.InfoOff
import Kraken.X64.Examples.Sbr.Parse.ResetA1G2

/-!
# `sbr_reset`: `bs_freq_scale = 0`, the `f_master` fill loops, back edges and exits (shard A1)

`L1e90`: the 8-wide loop (one `vmovdqu` per round); `L1e44`: the second half of the 32-wide body.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Reset

variable [CodeEnv]

theorem blk_L1e90 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1e90" ⟨"sbr_reset.L1e90", B.L1e90, some "sbr_reset.L1ea8"⟩ := by
  info_off
  measure_hb "L1e90"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hr, hk2, hle, hq, h3, ⟨hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2s, ⟨⟨h2, hxo, hnm, hdx⟩, hsi, h13, hax, hcx⟩, hr9, hX, hdi, j, hr8, hj8, hjl, hfil⟩,
      hm⟩, h12, h15⟩ := T.L1e90.mp hs
    clear hs
    have h48 := f0_nm_48 hr hC.2.1 hq
    have hA4 : u8 a.sp 4 ≤ 1 := hC.2.2.2.1
    have hdk : u8 a.sp 4 + 1 = 1 ∨ u8 a.sp 4 + 1 = 2 := by (try simp only [u8] at hA4 ⊢); omega
    simp only [Xbc, BitVec.setWidth_eq] at hX
    generalize hNdef : nmOf (k2 - k0N a row) (u8 a.sp 4) = N at *
    have hj : j + 1 + 8 ≤ 49 := by omega
    have ha1 := a1_fm_addr_c (arg1 t₀) (j := j) (c := 1) (d := 311794) (by omega) rfl (by omega)
    have hm1 := a1_fm16_store hm hfm hj ha1 (bc16 (u8 a.sp 4 + 1)).toInt
    have hfm1 : (wr st.fm (2 * (j + 1)) (Int.toBytes 16 (bc16 (u8 a.sp 4 + 1)).toInt)).length = 98 := by
      rw [wr_length (by rw [Int.toBytes_length, hfm]; omega), hfm]
    have hfil1 := a1_filled_bc hfm hdk hfil hj
    have hadd : BitVec.setWidth 64 8#64 + BitVec.ofNat 64 j = BitVec.ofNat 64 (j + 8) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      omega
    simp only [B.L1e90]
    vcgen
    all_goals try subst s₀
    all_goals try subst n
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hdx, hax, hcx,
      hsi, h13, hr9, hr8, hX, AddrIndex.offset64_scale2, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat]
    · exact a1_fm16_isSome hm hfm hj ha1
    · rename_i g1
      simp only [cc_nz_sub, cc_z_sub, a1_cc_z, decide_eq_true_eq, decide_eq_false_iff_not,
        Bool.not_eq_true', Bool.not_eq_false', Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hr9, hr8,
        hdx, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, hadd] at g1
      try rw [hadd]
      have hlt : j + 8 < N / 8 * 8 := by
        have : N / 8 * 8 ≠ j + 8 := fun h => g1 (by rw [h])
        omega
      subst hNdef
      refine Or.inl (Table.ofLabels_at ⟨S.L1e90, T.L1e90.mpr ⟨row, k2, hr, hk2, hle, hq, h3, ⟨hC, hBO, ⟨hrsp, hrbp⟩, ({ st with fm := wr st.fm (2 * (j + 1)) (Int.toBytes 16 (bc16 (u8 a.sp 4 + 1)).toInt) } : St), fr, hx, hsp, hfm1, hF,
        ⟨hk2s, ⟨⟨h2, hxo, hnm, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, j + 8, ?_, by omega, hlt, hfil1⟩, hm1⟩, ?_, ?_⟩, by
          left
          simp only [lex_var, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hr8, BitVec.toNat_ofNat]
          refine Kraken.lex_cons_lt_cons (by lex_len) ?_
          refine Kraken.lex_cons_lt_of_lt (by lex_len) ?_
          simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hr8, BitVec.toNat_ofNat]
          lex_digit⟩)
      all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hdx, hsi, h13, hax, hcx, hr9, hdi,
        h12, h15, Xbc, BitVec.setWidth_eq, hX]
    · rename_i g1 g2
      simp only [cc_nz_sub, cc_z_sub, a1_cc_z, decide_eq_true_eq, decide_eq_false_iff_not,
        Bool.not_eq_true', Bool.not_eq_false', Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hr9, hr8,
        hdx, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, hadd] at g1 g2
      try rw [hadd]
      have hN8 : N / 8 * 8 = j + 8 := by
        have := congrArg BitVec.toNat g1
        simp only [BitVec.toNat_ofNat] at this
        omega
      have hN : N = j + 8 := by
        have := congrArg BitVec.toNat g2
        simp only [BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at this
        omega
      have hfilN : Filled (wr st.fm (2 * (j + 1)) (Int.toBytes 16 (bc16 (u8 a.sp 4 + 1)).toInt)) (u8 a.sp 4 + 1) (N + 1) := by
        rw [hN]; exact hfil1
      subst hNdef
      refine Or.inl (Table.ofLabels_at ⟨S.L1ec1, T.L1ec1.mpr ⟨row, k2, hr, hk2, hle, hq, h3, ⟨hC, hBO, ⟨hrsp, hrbp⟩, ({ st with fm := wr st.fm (2 * (j + 1)) (Int.toBytes 16 (bc16 (u8 a.sp 4 + 1)).toInt) } : St), fr, hx, hsp, hfm1, hF,
        ⟨hk2s, ⟨⟨h2, hxo, hnm, ?_⟩, ?_, ?_, ?_, ?_⟩, hfilN⟩, hm1⟩, ?_, ?_⟩, by edge_step⟩)
      all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hdx, hsi, h13, hax, hcx, hr9, hdi,
        h12, h15]
    · rename_i g1 g2
      simp only [cc_nz_sub, cc_z_sub, a1_cc_z, decide_eq_true_eq, decide_eq_false_iff_not,
        Bool.not_eq_true', Bool.not_eq_false', Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hr9, hr8,
        hdx, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, hadd] at g1 g2
      try rw [hadd]
      have hN8 : N / 8 * 8 = j + 8 := by
        have := congrArg BitVec.toNat g1
        simp only [BitVec.toNat_ofNat] at this
        omega
      have hj9 : j + 9 ≤ N := by
        have : N ≠ j + 8 := fun h => g2 (by rw [show N / 8 * 8 = N by omega, BitVec.sub_self])
        omega
      have hdi' := hdi
      rw [hN8] at hdi'
      subst hNdef
      refine ⟨T.L1ea8.mpr ⟨row, k2, hr, hk2, hle, hq, h3, ⟨hC, hBO, ⟨hrsp, hrbp⟩, ({ st with fm := wr st.fm (2 * (j + 1)) (Int.toBytes 16 (bc16 (u8 a.sp 4 + 1)).toInt) } : St), fr, hx, hsp, hfm1, hF,
        ⟨hk2s, ⟨⟨h2, hxo, hnm, ?_⟩, ?_, ?_, ?_, ?_⟩, j + 1 + 8, ?_, by omega, by omega, hfil1⟩, hm1⟩, ?_, ?_⟩, by var_step⟩
      all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hdx, hsi, h13, hax, hcx, hr9, hdi',
        h12, h15]

omit [CodeEnv] in
theorem a1_and18 : ∀ n, n < 49 → 32 ≤ n →
    ((BitVec.setWidth 8 (BitVec.ofNat 64 n) &&& BitVec.setWidth 8 24#64 = 0) ↔ n < 40) := by
  decide

theorem blk_L1e44 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1e44" ⟨"sbr_reset.L1e44", B.L1e44, some "sbr_reset.L1e6b"⟩ := by
  info_off
  measure_hb "L1e44"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hr, hk2, hle, hq, h3, ⟨hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2s, ⟨⟨h2, hxo, hnm, hdx⟩, hsi, h13, hax, hcx⟩, h32, hr8, hX, hdi, j, hr9, hj32, hjl, hfil⟩,
      hm⟩, h12, h15⟩ := T.L1e44.mp hs
    clear hs
    have h48 := f0_nm_48 hr hC.2.1 hq
    have hA4 : u8 a.sp 4 ≤ 1 := hC.2.2.2.1
    have hdk : u8 a.sp 4 + 1 = 1 ∨ u8 a.sp 4 + 1 = 2 := by (try simp only [u8] at hA4 ⊢); omega
    simp only [Xbc, BitVec.setWidth_eq] at hX
    generalize hNdef : nmOf (k2 - k0N a row) (u8 a.sp 4) = N at *
    have hj0 : j = 0 := by omega
    have hN32 : N / 32 * 32 = 32 := by omega
    subst hj0
    have hj : 0 + 17 + 8 ≤ 49 ∧ 0 + 25 + 8 ≤ 49 := by omega
    have ha1 := a1_fm_addr_c (arg1 t₀) (j := 0) (c := 17) (d := 311826) (by omega) rfl (by omega)
    have ha2 := a1_fm_addr_c (arg1 t₀) (j := 0) (c := 25) (d := 311842) (by omega) rfl (by omega)
    have hm1 := a1_fm16_store hm hfm hj.1 ha1 (bc16 (u8 a.sp 4 + 1)).toInt
    have hfm1 : (wr st.fm (2 * (0 + 17)) (Int.toBytes 16 (bc16 (u8 a.sp 4 + 1)).toInt)).length = 98 := by
      rw [wr_length (by rw [Int.toBytes_length, hfm]; omega), hfm]
    have hm2 := a1_fm16_store hm1 hfm1 hj.2 ha2 (bc16 (u8 a.sp 4 + 1)).toInt
    have hfil1 := a1_filled_bc hfm hdk hfil hj.1
    have hfil2 := a1_filled_bc hfm1 hdk hfil1 hj.2
    have hfm2 : (wr (wr st.fm (2 * (0 + 17)) (Int.toBytes 16 (bc16 (u8 a.sp 4 + 1)).toInt)) (2 * (0 + 25))
        (Int.toBytes 16 (bc16 (u8 a.sp 4 + 1)).toInt)).length = 98 := by
      rw [wr_length (by rw [Int.toBytes_length, hfm1]; omega), hfm1]
    have hadd : BitVec.setWidth 64 32#64 + BitVec.ofNat 64 0 = BitVec.ofNat 64 32 := by decide
    rw [hN32] at hr8 hdi
    simp only [B.L1e44]
    vcgen
    all_goals try subst s₀
    all_goals try subst n
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hdx, hax, hcx,
      hsi, h13, hr9, hX, AddrIndex.offset64_scale2, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat]
    · exact a1_fm16_isSome hm hfm hj.1 ha1
    · exact a1_fm16_isSome hm1 hfm1 hj.2 ha2
    all_goals rename_i g1
    all_goals simp only [cc_nz_sub, cc_z_sub, a1_cc_z, decide_eq_true_eq, decide_eq_false_iff_not,
        Bool.not_eq_true', Bool.not_eq_false', Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hr9, hr8,
        hdx, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, hadd] at g1
    · exact absurd trivial g1
    · have hN : N = 32 := by
        have := congrArg BitVec.toNat g1
        simp only [BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at this
        omega
      have hfilN : Filled (wr (wr st.fm (2 * (0 + 17)) (Int.toBytes 16 (bc16 (u8 a.sp 4 + 1)).toInt)) (2 * (0 + 25)) (Int.toBytes 16 (bc16 (u8 a.sp 4 + 1)).toInt)) (u8 a.sp 4 + 1) (N + 1) := by
        rw [hN]; exact hfil2
      subst hNdef
      refine Or.inl (Table.ofLabels_at ⟨S.L1ec1, T.L1ec1.mpr ⟨row, k2, hr, hk2, hle, hq, h3, ⟨hC, hBO, ⟨hrsp, hrbp⟩, ({ st with fm := wr (wr st.fm (2 * (0 + 17)) (Int.toBytes 16 (bc16 (u8 a.sp 4 + 1)).toInt)) (2 * (0 + 25)) (Int.toBytes 16 (bc16 (u8 a.sp 4 + 1)).toInt) } : St), fr, hx, hsp, hfm2, hF,
        ⟨hk2s, ⟨⟨h2, hxo, hnm, ?_⟩, ?_, ?_, ?_, ?_⟩, hfilN⟩, hm2⟩, ?_, ?_⟩, by edge_step⟩)
      all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hdx, hsi, h13, hax, hcx, hr9, hdi,
        h12, h15]
    · rename_i g0 _
      try simp only [cc_nz_sub, cc_z_sub, a1_cc_z, decide_eq_true_eq, decide_eq_false_iff_not,
        Bool.not_eq_true', Bool.not_eq_false', Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hr9, hr8,
        hdx, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, hadd] at g0
      have hN : N ≠ 32 := fun h => g0 (by rw [h]; decide)
      have h40 := (a1_and18 N (by omega) h32).mp g1
      have hle33 : 0 + 25 + 8 ≤ N := by omega
      subst hNdef
      refine Or.inl (Table.ofLabels_at ⟨S.L1ea8, T.L1ea8.mpr ⟨row, k2, hr, hk2, hle, hq, h3, ⟨hC, hBO, ⟨hrsp, hrbp⟩, ({ st with fm := wr (wr st.fm (2 * (0 + 17)) (Int.toBytes 16 (bc16 (u8 a.sp 4 + 1)).toInt)) (2 * (0 + 25)) (Int.toBytes 16 (bc16 (u8 a.sp 4 + 1)).toInt) } : St), fr, hx, hsp, hfm2, hF,
        ⟨hk2s, ⟨⟨h2, hxo, hnm, ?_⟩, ?_, ?_, ?_, ?_⟩, 0 + 25 + 8, ?_, by omega, hle33, hfil2⟩, hm2⟩, ?_, ?_⟩, by edge_step⟩)
      all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hdx, hsi, h13, hax, hcx, hr9, hdi,
        h12, h15]
    · rename_i g0 _
      try simp only [cc_nz_sub, cc_z_sub, a1_cc_z, decide_eq_true_eq, decide_eq_false_iff_not,
        Bool.not_eq_true', Bool.not_eq_false', Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hr9, hr8,
        hdx, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, hadd] at g0
      have h40 : ¬ N < 40 := fun h => g1 ((a1_and18 N (by omega) h32).mpr h)
      have hle40 : 32 + 8 ≤ N := by omega
      subst hNdef
      refine ⟨T.L1e6b.mpr ⟨row, k2, hr, hk2, hle, hq, h3, ⟨hC, hBO, ⟨hrsp, hrbp⟩, ({ st with fm := wr (wr st.fm (2 * (0 + 17)) (Int.toBytes 16 (bc16 (u8 a.sp 4 + 1)).toInt)) (2 * (0 + 25)) (Int.toBytes 16 (bc16 (u8 a.sp 4 + 1)).toInt) } : St), fr, hx, hsp, hfm2, hF,
        ⟨hk2s, ⟨⟨h2, hxo, hnm, ?_⟩, ?_, ?_, ?_, ?_⟩, 32, ?_, rfl, hle40, hfil2⟩, hm2⟩, ?_, ?_⟩, by var_step⟩
      all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hdx, hsi, h13, hax, hcx, hr9, hdi,
        h12, h15, hr8]

end Kraken.Examples.Sbr.Reset
