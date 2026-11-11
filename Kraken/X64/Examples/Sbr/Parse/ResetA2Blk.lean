import Kraken.X64.Examples.Sbr.Parse.ResetA2Lib
import Kraken.X64.Examples.Sbr.Parse.ResetA1Lib
import Kraken.X64.Examples.Sbr.Parse.ResetLog
import Kraken.X64.Examples.Sbr.Parse.ResetA2Spec
import Kraken.X64.Examples.Sbr.Parse.ResetA2Exit

/-!
# `sbr_reset`, shard A2: the straight-line blocks of `bs_freq_scale > 0`
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Reset

variable [CodeEnv]

set_option maxRecDepth 100000 in
theorem blk_L1684 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1684" ⟨"sbr_reset.L1684", B.L1684, some "sbr_reset.L16b7"⟩ := by
  info_off
  measure_hb "L1684"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF, hk2v, hm⟩,
      h12, h15, hsi, h13, hcx⟩ := T.L1684.mp hs
    clear hs
    have ld0 := a2_sp_load hm (by rw [hsp]; exact hC.1) (i := 3) (by omega)
    rw [hsp] at ld0
    have hl80 := fr_load hm hF (d := 0x80) (n := 4) (by omega) (by omega)
    have hF1 := fun v => fr_wr_len hF (o := rb 0x80) (n := 4) (by simp only [rb]; omega) v
    have st80 := fr_store hm hF (d := 0x80) (n := 4) (by omega) (by omega)
    have e80 : t₀.regs.get64 .rsp - 8#64 + 18446744073709551488#64
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x80 := by bv_omega
    have e88 : t₀.regs.get64 .rsp - 8#64 + 18446744073709551480#64
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x88 := by bv_omega
    have e3 : t₀.regs.get64 .rsi + 31#64 = arg1 t₀ + 0x1c#64 + BitVec.ofNat 64 3 := by
      simp only [arg1]; bv_omega
    have hu8 : u8 a.sp 3 < 256 := UInt8.toNat_lt _
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L1684]
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceMod, Nat.reducePow, Nat.reduceSub,
        Option.isSome_some] at *
    all_goals try simp only [hrbp, h12, h13, hsi, hcx, e80, e88, e3, ld0, hl80, Option.isSome_some]
    · rename_i hl hz
      rw [h12, e3, ld0] at hl
      obtain rfl := Option.some.inj hl
      have hu : u8 a.sp 3 = 0 := by
        simp only [u8] at hu8 ⊢
        simp only [CondCode.interp_z, StatusFlags.zf_from_result, BitVec.and_self, beq_iff_eq] at hz
        generalize (a.sp.getD 3 0).toNat = u at hz hu8 ⊢
        have := congrArg BitVec.toNat hz
        simp [BitVec.toNat_setWidth] at this
        omega
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L1779.mpr ⟨⟨row, k2, hrow, hk2, hk02, hkq, ⟨hC, hB, ⟨?_, ?_⟩, st, fr, hx,
        hsp, hfm, hF, hk2v, hm⟩, ?_, ?_, ?_, ?_, ?_⟩, hu⟩, ?_⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15,
        hsi, h13, hcx]
      edge_step
    · rw [fr_load (st80 _) (hF1 _) (d := 0x88) (n := 4) (by omega) (by omega)]; rfl
    · rename_i hl hz
      rw [h12, e3, ld0] at hl
      obtain rfl := Option.some.inj hl
      have hu : 1 ≤ u8 a.sp 3 := by
        simp only [u8] at hu8 ⊢
        simp only [CondCode.interp_z, StatusFlags.zf_from_result, BitVec.and_self,
          beq_eq_false_iff_ne, ne_eq] at hz
        generalize (a.sp.getD 3 0).toNat = u at hz hu8 ⊢
        rcases Nat.eq_zero_or_pos u with h0 | h0
        · subst h0; exact absurd rfl hz
        · exact h0
      refine ⟨T.L16b7.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st, _, hx, hsp, hfm, ?_,
        ⟨hk2v, ?_, ?_⟩, fr_store (st80 _) (hF1 _) (d := 0x88) (n := 4) (by omega) (by omega) _⟩,
        ?_, ?_, ?_, ?_, ?_⟩, by var_step⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15,
        hsi, h13, hcx]
      · exact fr_wr_len (hF1 _) (by simp only [rb]; omega) _
      · rw [frSlot32_wr_other (hF1 _) (d := 0x88) (n := 4) (by omega) (by omega) _ (d' := 0x80)
          (by omega) (by omega) (by omega), frSlot32_wr_same hF (by omega) (by omega), BitVec.ofInt_toInt]
        apply BitVec.eq_of_toNat_eq
        have m1 : k2 % 18446744073709551616 = k2 := Nat.mod_eq_of_lt (by omega)
        have m2 : k2 % 4294967296 = k2 := Nat.mod_eq_of_lt (by omega)
        simp only [BitVec.toNat_setWidth, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.reducePow,
          Nat.reduceMod, m1, m2]
        omega
      · rw [frSlot32_wr_same (hF1 _) (by omega) (by omega), BitVec.ofInt_toInt]
        simp only [k0N, k0A, srI, u8] at hk02 ⊢
        generalize (k0Of a.x.sampleRate.toInt row (a.sp.getD 0 0).toNat).toNat = K at hk02 ⊢
        apply BitVec.eq_of_toNat_eq
        have m1 : K % 18446744073709551616 = K := Nat.mod_eq_of_lt (by omega)
        have m2 : K % 4294967296 = K := Nat.mod_eq_of_lt (by omega)
        simp only [BitVec.toNat_setWidth, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.reducePow,
          Nat.reduceMod, m1, m2]
        omega
      · rw [cc_be_sub]
        simp only [k0N, k0A, srI, u8, A2.k1Of] at hk02 ⊢
        generalize (k0Of a.x.sampleRate.toInt row (a.sp.getD 0 0).toNat).toNat = K at hk02 ⊢
        have m1 : K % 18446744073709551616 = K := Nat.mod_eq_of_lt (by omega)
        have m2 : K % 4294967296 = K := Nat.mod_eq_of_lt (by omega)
        have m3 : k2 % 18446744073709551616 = k2 := Nat.mod_eq_of_lt (by omega)
        have m4 : k2 % 4294967296 = k2 := Nat.mod_eq_of_lt (by omega)
        have m5 : K * 2 % 18446744073709551616 = K * 2 := Nat.mod_eq_of_lt (by omega)
        have m6 : K * 2 % 4294967296 = K * 2 := Nat.mod_eq_of_lt (by omega)
        have m7 : K * 110 % 4294967296 = K * 110 := Nat.mod_eq_of_lt (by omega)
        have m8 : K * 110 % 18446744073709551616 = K * 110 := Nat.mod_eq_of_lt (by omega)
        have m9 : k2 * 49 % 4294967296 = k2 * 49 := Nat.mod_eq_of_lt (by omega)
        have m10 : k2 * 49 % 18446744073709551616 = k2 * 49 := Nat.mod_eq_of_lt (by omega)
        have m11 : 2 * K % 18446744073709551616 = 2 * K := Nat.mod_eq_of_lt (by omega)
        split <;> split <;> rename_i h1 h2 <;>
          simp only [decide_eq_true_eq, BitVec.toNat_setWidth, BitVec.toNat_mul, BitVec.toNat_ofNat,
            Nat.reducePow, Nat.reduceMod, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11] at h1 h2 <;>
          apply BitVec.eq_of_toNat_eq <;>
          simp only [BitVec.toNat_setWidth, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.reducePow,
            Nat.reduceMod, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11] <;>
          omega
      · have h3 := hC.2.2.1
        simp only [u8] at h3 ⊢
        rw [BitVec.ofInt_natCast]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow]
        omega

omit [CodeEnv] in
theorem a2_toInt_ofNat64 {n : Nat} (h : n < 2 ^ 63) : (BitVec.ofNat 64 n).toInt = n := by
  rw [BitVec.toInt_ofNat']; simp only [Int.bmod_def]; split <;> omega

omit [CodeEnv] in
theorem a2_toInt_ofNat32 {n : Nat} (h : n < 2 ^ 31) : (BitVec.ofNat 32 n).toInt = n := by
  rw [BitVec.toInt_ofNat']; simp only [Int.bmod_def]; split <;> omega

omit [CodeEnv] in
theorem a2_sitof32_ofNat64 {n : Nat} (h : n < 2 ^ 31) :
    BitVec.sitof32 (BitVec.ofNat 64 n) = A2.fl n := by
  simp only [A2.fl, BitVec.sitof32]
  rw [a2_toInt_ofNat64 (by omega), a2_toInt_ofNat32 (by omega)]

omit [CodeEnv] in
theorem a2_setWidth32_ofNat64 (n : Nat) : (BitVec.ofNat 64 n).setWidth 32 = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

omit [CodeEnv] in
theorem a2_ex0_app (x : BitVec 96) (v : BitVec 32) : (x ++ v).extractLsb' 0 32 = v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_append, Nat.shiftRight_zero]
  have := v.isLt
  rw [Nat.shiftLeft_eq, Nat.or_mod_two_pow, Nat.mul_mod_left, Nat.zero_or, Nat.mod_eq_of_lt this]

omit [CodeEnv] in
theorem a2_setWidth64_ofNat32 {n : Nat} (h : n < 2 ^ 32) :
    (BitVec.ofNat 32 n).setWidth 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

omit [CodeEnv] in
theorem a2_lo_app (x : BitVec 96) (v : BitVec 32) : (x ++ v).setWidth 32 = v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_append]
  have := v.isLt
  rw [Nat.shiftLeft_eq, Nat.or_mod_two_pow, Nat.mul_mod_left, Nat.zero_or, Nat.mod_eq_of_lt this]

/-- A store of `k[1]`. -/
theorem a2_k1_store {k : Nat} {e : REnv} {a : RArgs} {ra : Int64} {t₀ : MachineData} {st : St}
    {fr : List UInt8} {m : Mem 64} (hm : m =⋆ Mm k e a ra t₀ st fr) (v : BitVec 32) :
    m.storeInt (arg1 t₀ + 0x44#64) 4 v.toInt =⋆ Mm k e a ra t₀ { st with k1 := v } fr :=
  Mm_upd_k1 .. ▸ cell4_store' (focus (Mm_k1 ..) hm) v.toInt v rfl

set_option maxRecDepth 100000 in
theorem blk_L16b7 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L16b7" ⟨"sbr_reset.L16b7", B.L16b7, some "sbr_reset.L16d6"⟩ := by
  info_off
  measure_hb "L16b7"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hs80, hs88⟩, hm⟩, h12, h15, h13, h14, hcx⟩ := T.L16b7.mp hs
    clear hs
    have hk1l := cell4_isSome (focus (Mm_k1 ..) hm)
    have hk1s := a2_k1_store hm
    have e38 : t₀.regs.get64 .rsp - 8#64 + 18446744073709551560#64
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x38 := by bv_omega
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L16b7]
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceMod, Nat.reducePow, Nat.reduceSub,
        Option.isSome_some] at *
    all_goals try simp only [hrbp, h12, h13, h14, h15, hcx, e38, Option.isSome_some]
    · exact hk1l
    · rw [fr_load (a2_k1_store hm _) hF (d := 0x38) (n := 4) (by omega) (by omega)]; rfl
    · simp only [RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne, ne_eq, reduceCtorEq,
        not_false_eq_true, a2_lo_app]
      have hm2 := fr_store (a2_k1_store hm (BitVec.setWidth 32 (BitVec.ofNat 64
        (if 110 * (k0Of a.x.sampleRate.toInt row (a.sp.getD 0 0).toNat).toNat < 49 * k2 then
          2 * (k0Of a.x.sampleRate.toInt row (a.sp.getD 0 0).toNat).toNat else k2))))
        hF (d := 0x38) (n := 4) (by omega) (by omega)
        (BitVec.sitof32 (BitVec.setWidth 32 (BitVec.ofNat 64 (7 - (a.sp.getD 3 0).toNat)))).toInt
      generalize hV1 : BitVec.setWidth 32 (BitVec.ofNat 64
        (if 110 * (k0Of a.x.sampleRate.toInt row (a.sp.getD 0 0).toNat).toNat < 49 * k2 then
          2 * (k0Of a.x.sampleRate.toInt row (a.sp.getD 0 0).toNat).toNat else k2)) = V1 at hm2 ⊢
      generalize hV2 : BitVec.sitof32 (BitVec.setWidth 32 (BitVec.ofNat 64
        (7 - (a.sp.getD 3 0).toNat))) = V2 at hm2 ⊢
      refine ⟨T.L16d6.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, { st with k1 := V1 },
        wr fr (rb 0x38) (Int.toBytes 4 V2.toInt), hx, hsp, hfm,
        ?_, ⟨hk2v, ?_, ?_, ?_, ?_, ?_, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, hm2⟩⟩, by var_step⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15,
        h13, h14, hcx, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne, ne_eq, not_false_eq_true,
        a2_lo_app]
      · exact fr_wr_len hF (by simp only [rb]; omega) _
      · subst hV1; simp only [A2.k1Of, k0N, k0A, srI, u8]; exact a2_setWidth32_ofNat64 _
      · rw [frSlot32_wr_other hF (d := 0x38) (n := 4) (by omega) (by omega) _ (d' := 0x80) (by omega)
          (by omega) (by omega)]; exact hs80
      · rw [frSlot32_wr_other hF (d := 0x38) (n := 4) (by omega) (by omega) _ (d' := 0x88) (by omega)
          (by omega) (by omega)]; exact hs88
      · rw [frSlot32_wr_same hF (by omega) (by omega), BitVec.ofInt_toInt]
        subst hV2; simp only [A2.h0Of, A2.fl, u8, a2_setWidth32_ofNat64]
      · simp only [lo32, RegZmms.get_set_xmm_same, a2_lo_app, a2_ex0_app, a2_setWidth32_ofNat64,
          A2.k1Of, k0N, k0A, srI, u8]
        rw [a2_setWidth64_ofNat32 (by omega), a2_sitof32_ofNat64 (by split <;> omega),
          a2_sitof32_ofNat64 (by omega)]

set_option maxRecDepth 100000 in
/-- `log2f(k[1] / k[0])`. -/
theorem blk_L16d6 (k : Nat) (e : REnv) (hc : ResetCallees k e) (a : RArgs) (ra : Int64)
    (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L16d6" ⟨"sbr_reset.L16d6", B.L16d6, some "sbr_reset.L16db"⟩ := by
  info_off
  measure_hb "L16d6"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, h12, h15, h13, h14, hSB, hlo⟩, hm⟩⟩ := T.L16d6.mp hs
    clear hs
    have hd := reserve_le (focus (Mm_reserve ..) hm)
    rw [Mm_callF _ _ _ _ _ _ _ hd] at hm
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rsp - 8#64) 8).isSome = true := by
      rw [hrsp]
      exact Block.loadInt_isSome hm (by simp)
    have hpush := fun v => Block.storeInt_val hm (Split.here _ _) v
    have e8 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 0x578#64 - 8#64 := by
      rw [hrsp]
    simp only [B.L16d6]
    vcgen [MachineWP.call_proc_spec_at (CallF k e a ra t₀ st fr) "log2f" hc.log2f]
    all_goals try call_simp
    all_goals try subst_vars
    refine ⟨fun ra' => ⟨⟨?_, trivial⟩, fun s' hpost => ?_⟩, hld⟩
    · rw [e8]; exact hpush _
    · rw [e8] at hpost
      obtain ⟨⟨hsp', hbp', ⟨-, h12', h13', h14', h15'⟩, hm'⟩, hlg⟩ := hpost
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨T.L16db.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st, fr, hx, hsp, hfm,
        hF, ⟨hk2v, hk1v, ?_, ?_, ?_, ?_, hSB, ?_⟩, ?_⟩⟩, by var_step⟩
      · rw [hsp']; bv_omega
      · rw [hbp', hrbp]
      · rw [h12', h12]
      · rw [h15', h15]
      · rw [h13', h13]
      · rw [h14', h14]
      · exact hlg.trans (congrArg e.lg hlo)
      · show Mm k e a ra t₀ st fr s'.dmem
        rw [Mm_callF _ _ _ _ _ _ _ hd]; exact hm'

set_option maxRecDepth 100000 in
/-- `powf(k[1] / k[0], 1 / num_bands_0)`. -/
theorem blk_L1736 (k : Nat) (e : REnv) (hc : ResetCallees k e) (a : RArgs) (ra : Int64)
    (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1736" ⟨"sbr_reset.L1736", B.L1736, some "sbr_reset.L173b"⟩ := by
  info_off
  measure_hb "L1736"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, h15, h13, h14, hSE, hN0, hbx, hlo0, hlo1⟩, hm⟩⟩ := T.L1736.mp hs
    clear hs
    have hd := reserve_le (focus (Mm_reserve ..) hm)
    rw [Mm_callF _ _ _ _ _ _ _ hd] at hm
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rsp - 8#64) 8).isSome = true := by
      rw [hrsp]
      exact Block.loadInt_isSome hm (by simp)
    have hpush := fun v => Block.storeInt_val hm (Split.here _ _) v
    have e8 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 0x578#64 - 8#64 := by
      rw [hrsp]
    simp only [B.L1736]
    vcgen [MachineWP.call_proc_spec_at (CallF k e a ra t₀ st fr) "powf" hc.powf]
    all_goals try call_simp
    all_goals try subst_vars
    refine ⟨fun ra' => ⟨⟨?_, trivial⟩, fun s' hpost => ?_⟩, hld⟩
    · rw [e8]; exact hpush _
    · rw [e8] at hpost
      obtain ⟨⟨hsp', hbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩, hlg⟩ := hpost
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨T.L173b.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st, fr, hx, hsp, hfm,
        hF, ⟨hk2v, hk1v, ?_, ?_, ?_, hSE, hN0, ?_, ?_⟩, ?_⟩⟩, by var_step⟩
      · rw [hsp']; bv_omega
      · rw [hbp', hrbp]
      · rw [h15']; exact h15
      · rw [h13']; exact h13
      · rw [h14']; exact h14
      · rw [hbx']; exact hbx
      · exact hlg.trans ((congrArg (e.pw · _) hlo0).trans (congrArg (e.pw _ ·) hlo1))
      · show Mm k e a ra t₀ st fr s'.dmem
        rw [Mm_callF _ _ _ _ _ _ _ hd]; exact hm'

set_option maxRecDepth 100000 in
/-- `log2f(k[2] / k[1])`. -/
theorem blk_L1c76 (k : Nat) (e : REnv) (hc : ResetCallees k e) (a : RArgs) (ra : Int64)
    (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1c76" ⟨"sbr_reset.L1c76", B.L1c76, some "sbr_reset.L1c7b"⟩ := by
  info_off
  measure_hb "L1c76"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hlt, hInc, hN0, h12, h15, h30, h38, h13, h14, hlo, hTA⟩, hm⟩⟩ := T.L1c76.mp hs
    clear hs
    have hd := reserve_le (focus (Mm_reserve ..) hm)
    rw [Mm_callF _ _ _ _ _ _ _ hd] at hm
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rsp - 8#64) 8).isSome = true := by
      rw [hrsp]
      exact Block.loadInt_isSome hm (by simp)
    have hpush := fun v => Block.storeInt_val hm (Split.here _ _) v
    have e8 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 0x578#64 - 8#64 := by
      rw [hrsp]
    simp only [B.L1c76]
    vcgen [MachineWP.call_proc_spec_at (CallF k e a ra t₀ st fr) "log2f" hc.log2f]
    all_goals try call_simp
    all_goals try subst_vars
    refine ⟨fun ra' => ⟨⟨?_, trivial⟩, fun s' hpost => ?_⟩, hld⟩
    · rw [e8]; exact hpush _
    · rw [e8] at hpost
      obtain ⟨⟨hsp', hbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩, hlg⟩ := hpost
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨T.L1c7b.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st, fr, hx, hsp, hfm,
        hF, ⟨hk2v, hk1v, hlt, hInc, hN0, ?_, ?_, h30, h38, ?_, ?_, ?_, hTA⟩, ?_⟩⟩, by var_step⟩
      · rw [hsp']; bv_omega
      · rw [hbp', hrbp]
      · rw [h12']; exact h12
      · rw [h15']; exact h15
      · rw [h13']; exact h13
      · rw [h14']; exact h14
      · exact hlg.trans (congrArg e.lg hlo)
      · show Mm k e a ra t₀ st fr s'.dmem
        rw [Mm_callF _ _ _ _ _ _ _ hd]; exact hm'

set_option maxRecDepth 100000 in
/-- `powf(k[2] / k[1], 1 / num_bands_1)`. -/
theorem blk_L1cb4 (k : Nat) (e : REnv) (hc : ResetCallees k e) (a : RArgs) (ra : Int64)
    (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1cb4" ⟨"sbr_reset.L1cb4", B.L1cb4, some "sbr_reset.L1cb9"⟩ := by
  info_off
  measure_hb "L1cb4"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hlt, hInc, hN0, hN1, h12, h30, h13, h14, h15, hbx, h80, hlo0, hlo1, hTA⟩, hm⟩⟩ := T.L1cb4.mp hs
    clear hs
    have hd := reserve_le (focus (Mm_reserve ..) hm)
    rw [Mm_callF _ _ _ _ _ _ _ hd] at hm
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rsp - 8#64) 8).isSome = true := by
      rw [hrsp]
      exact Block.loadInt_isSome hm (by simp)
    have hpush := fun v => Block.storeInt_val hm (Split.here _ _) v
    have e8 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 0x578#64 - 8#64 := by
      rw [hrsp]
    simp only [B.L1cb4]
    vcgen [MachineWP.call_proc_spec_at (CallF k e a ra t₀ st fr) "powf" hc.powf]
    all_goals try call_simp
    all_goals try subst_vars
    refine ⟨fun ra' => ⟨⟨?_, trivial⟩, fun s' hpost => ?_⟩, hld⟩
    · rw [e8]; exact hpush _
    · rw [e8] at hpost
      obtain ⟨⟨hsp', hbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩, hlg⟩ := hpost
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨T.L1cb9.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st, fr, hx, hsp, hfm,
        hF, ⟨hk2v, hk1v, hlt, hInc, hN0, hN1, ?_, h30, ?_, ?_, ?_, ?_, h80, ?_, hTA⟩, ?_⟩⟩, by var_step⟩
      · rw [hsp']; bv_omega
      · rw [hbp', hrbp]
      · rw [h12']; exact h12
      · rw [h13']; exact h13
      · rw [h14']; exact h14
      · rw [h15']; exact h15
      · rw [hbx']; exact hbx
      · exact hlg.trans ((congrArg (e.pw · _) hlo0).trans (congrArg (e.pw _ ·) hlo1))
      · show Mm k e a ra t₀ st fr s'.dmem
        rw [Mm_callF _ _ _ _ _ _ _ hd]; exact hm'

omit [CodeEnv] in
theorem a2_ofNat_toInt_toNat32 (V : BitVec 32) (h : 0 ≤ V.toInt) : BitVec.ofNat 32 V.toInt.toNat = V := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  rw [BitVec.toInt_eq_msb_cond] at h ⊢
  have := V.isLt
  cases hm : V.msb <;> simp [hm] at h ⊢ <;> omega

omit [CodeEnv] in
theorem a2_sw64_toInt32 (V : BitVec 32) (h : 0 ≤ V.toInt) : V.setWidth 64 = BitVec.ofNat 64 V.toInt.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_setWidth]
  rw [BitVec.toInt_eq_msb_cond] at h ⊢
  have := V.isLt
  cases hm : V.msb <;> simp [hm] at h ⊢ <;> omega

omit [CodeEnv] in
theorem a2_ofInt32_dbl (x : Int) : BitVec.ofInt 32 x + BitVec.ofInt 32 x = BitVec.ofInt 32 (2 * x) := by
  rw [← BitVec.ofInt_add]; congr 1; omega

set_option maxRecDepth 100000 in
/-- `num_bands_0 = 2 lrintf(h0 log2f(k1 / k0))`; `≤ 0` fails; `-0x40 = ac`. -/
theorem blk_L16db (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L16db" ⟨"sbr_reset.L16db", B.L16db, some "sbr_reset.L16f8"⟩ := by
  info_off
  measure_hb "L16db"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, h12, h15, h13, h14, ⟨⟨hs80, hs88⟩, hs38⟩, hlo⟩, hm⟩⟩ := T.L16db.mp hs
    clear hs
    have hl38 := fr_load hm hF (d := 0x38) (n := 4) (by omega) (by omega)
    have hl50 := fr_load hm hF (d := 0x50) (n := 8) (by omega) (by omega)
    have hF1 := fun v => fr_wr_len hF (o := rb 0x50) (n := 8) (by simp only [rb]; omega) v
    have st50 := fr_store hm hF (d := 0x50) (n := 8) (by omega) (by omega)
    have e38 : t₀.regs.get64 .rsp - 8#64 + 18446744073709551560#64
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x38 := by bv_omega
    have e50 : t₀.regs.get64 .rsp - 8#64 + 18446744073709551536#64
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x50 := by bv_omega
    have e40 : t₀.regs.get64 .rsp - 8#64 + 18446744073709551552#64
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x40 := by bv_omega
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L16db]
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceMod, Nat.reducePow, Nat.reduceSub,
        Option.isSome_some] at *
    all_goals try simp only [hrbp, h12, h13, h14, h15, e38, e50, e40, hl38, hl50, Option.isSome_some]
    · rename_i hl hz
      simp only [hrbp] at hl
      rw [show t₀.regs.get64 .rsp - 8#64 + 18446744073709551560#64 = t₀.regs.get64 .rsp - 8#64 - 56#64
        by bv_omega, hl38] at hl
      obtain rfl := Option.some.inj hl
      try simp only [frSlot32] at hs38
      simp only [RegZmms.get_set_xmm_same, a2_lo_app, a2_ex0_eq_sw, hlo, hs38, sw32_64, a2_lea2] at hz ⊢
      generalize hX : BitVec.f32toi64 (BitVec.f32mul (e.lg (BitVec.f32div
        (A2.fl (A2.k1Of (k0N a row) k2)) (A2.fl (k0N a row)))) (A2.h0Of a)) = X at hz ⊢
      have hnI : A2.n0I e a (k0N a row) k2 = (BitVec.ofInt 32 (2 * X.toInt)).toInt := by
        rw [← hX]; rfl
      rw [a2_cc_le_test] at hz
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L17e7.mpr ⟨hC, ⟨?_, ?_⟩, ?_, ?_, st, wr fr (rb 0x50) (Int.toBytes 8 X.toInt),
        ?_, hsp, hfm, hF1 _, st50 _⟩, ?_⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15]
      · rw [hx]; exact a2_fail_reset hrow hC.2.1
      · edge_step
    · rw [fr_load (st50 _) (hF1 _) (d := 0x40) (n := 8) (by omega) (by omega)]; rfl
    · rename_i hl hz
      simp only [hrbp] at hl
      rw [show t₀.regs.get64 .rsp - 8#64 + 18446744073709551560#64 = t₀.regs.get64 .rsp - 8#64 - 56#64
        by bv_omega, hl38] at hl
      obtain rfl := Option.some.inj hl
      try simp only [frSlot32] at hs38
      simp only [RegZmms.get_set_xmm_same, a2_lo_app, a2_ex0_eq_sw, hlo, hs38, sw32_64, a2_lea2] at hz ⊢
      generalize hX : BitVec.f32toi64 (BitVec.f32mul (e.lg (BitVec.f32div
        (A2.fl (A2.k1Of (k0N a row) k2)) (A2.fl (k0N a row)))) (A2.h0Of a)) = X at hz ⊢
      have hnI : A2.n0I e a (k0N a row) k2 = (BitVec.ofInt 32 (2 * X.toInt)).toInt := by
        rw [← hX]; rfl
      rw [a2_cc_le_test] at hz
      simp only [decide_eq_false_iff_not, Int.not_le] at hz
      have hb := (a2_bands_of hB hC hrow hk2 hk02 hkq hu).1 (by rw [hnI]; exact hz)
      have hev := a2_even_nb X.toInt
      refine ⟨T.L16f8.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st,
        wr (wr fr (rb 0x50) (Int.toBytes 8 X.toInt)) (rb 0x40) (Int.toBytes 8 (t₀.regs.get64 .rdi).toInt),
        hx, hsp, hfm, fr_wr_len (hF1 _) (by simp only [rb]; omega) _,
        ⟨hk2v, hk1v, ?_, ?_, ?_, ?_, ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩, ?_, ?_⟩,
        fr_store (st50 _) (hF1 _) (d := 0x40) (n := 8) (by omega) (by omega) _⟩⟩, by var_step⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15,
        h13, h14]
      · rw [frSlot32_wr_other (hF1 _) (d := 0x40) (n := 8) (by omega) (by omega) _ (d' := 0x80)
          (by omega) (by omega) (by omega), frSlot32_wr_other hF (d := 0x50) (n := 8) (by omega)
          (by omega) _ (d' := 0x80) (by omega) (by omega) (by omega)]; exact hs80
      · rw [frSlot32_wr_other (hF1 _) (d := 0x40) (n := 8) (by omega) (by omega) _ (d' := 0x88)
          (by omega) (by omega) (by omega), frSlot32_wr_other hF (d := 0x50) (n := 8) (by omega)
          (by omega) _ (d' := 0x88) (by omega) (by omega) (by omega)]; exact hs88
      · rw [frSlot32_wr_other (hF1 _) (d := 0x40) (n := 8) (by omega) (by omega) _ (d' := 0x38)
          (by omega) (by omega) (by omega), frSlot32_wr_other hF (d := 0x50) (n := 8) (by omega)
          (by omega) _ (d' := 0x38) (by omega) (by omega) (by omega)]; simp only [frSlot32]; exact hs38
      · rw [frSlot32_wr_other (hF1 _) (d := 0x40) (n := 8) (by omega) (by omega) _ (d' := 0x50)
          (by omega) (by omega) (by omega), a2_frSlot32_wr8_same hF (by omega) (by omega), a2_ofInt32_dbl,
          A2.n0N, hnI, a2_ofNat_toInt_toNat32 _ (by omega)]
      · rw [frSlot64_wr_same (hF1 _) (by omega) (by omega), BitVec.ofInt_toInt]
      · refine ⟨by rw [hnI]; exact hz, hb.1, ?_⟩
        simp only [A2.n0N, hnI]; omega
      · simp only [A2.n0N, hnI]; exact a2_sw64_toInt32 _ (by omega)

set_option maxRecDepth 100000 in
/-- One region, `f_master` copied: `jmp L2012` with `Master.ok`. -/
theorem blk_L1dde (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1dde" ⟨"sbr_reset.L1dde", B.L1dde, some "sbr_reset.L1de3"⟩ := by
  info_off
  measure_hb "L1dde"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, h12, hN0, h40, hone, hInc, hnm, h13, h14, hxo, hfmv⟩, hm⟩⟩ := T.L1dde.mp hs
    clear hs
    have hk0 := k0Of_range hrow hC.2.1
    have hM : Master a.x.sampleRate.toInt (u8 a.sp 0) (u8 a.sp 2) (some (k0A a row))
        (some (A2.n0N e a (k0N a row) k2, fOf st)) := by
      obtain ⟨hI0, hIn, hIi⟩ := hInc
      simp only [k0N, k0A, srI, A2.k1Of, if_neg hone] at *
      refine Master.ok (row := row) (k2 : Int) _ _ hrow (by omega) (by omega) ?_ hxo ?_ ?_ ?_
      · simp only [maxQ] at hkq; omega
      · have := hfmv 0 (by omega); simp only [fOf]; omega
      · intro i hi
        have := hfmv i (by omega); have := hfmv (i + 1) (by omega); have := hIi i hi
        simp only [fOf]; omega
      · have := hfmv _ (Nat.le_refl _); simp only [fOf]; omega
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L1dde]
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    left; apply Table.ofLabels_at
    refine ⟨by decide, T.L2012.mpr ⟨hC, ⟨hrsp, hrbp⟩, h12, st, fr, _, _, hM, hx, hsp,
      ⟨by rw [hk2v]; simp only [BitVec.toNat_ofNat]; omega, hB.2⟩, hfm, hF, h13,
      h14, h40, hm⟩, ?_⟩
    edge_step

set_option maxRecDepth 100000 in
/-- Two regions, `f_master` copied: `jmp L2012` with `Master.ok` (`vk0` then `vk1[1..]`). -/
theorem blk_L29a8 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L29a8" ⟨"sbr_reset.L29a8", B.L29a8, some "sbr_reset.L29ad"⟩ := by
  info_off
  measure_hb "L29a8"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hlt, hInc0, hN0, hN1, h12, h40, hInc1, hnm, h13, h14, hxo, hfm0, hfm1⟩, hm⟩⟩ :=
      T.L29a8.mp hs
    clear hs
    have hk0 := k0Of_range hrow hC.2.1
    have hM : Master a.x.sampleRate.toInt (u8 a.sp 0) (u8 a.sp 2) (some (k0A a row))
        (some (A2.n0N e a (k0N a row) k2 + A2.n1N e a (k0N a row) k2, fOf st)) := by
      obtain ⟨hI0, hIn, hIi⟩ := hInc0
      obtain ⟨hJ0, hJn, hJi⟩ := hInc1
      generalize A2.n0N e a (k0N a row) k2 = n0 at *
      generalize A2.n1N e a (k0N a row) k2 = n1 at *
      simp only [k0N, k0A, srI, A2.k1Of, if_pos hlt] at *
      refine Master.ok (row := row) (k2 : Int) _ _ hrow (by omega) (by omega) ?_ hxo ?_ ?_ ?_
      · simp only [maxQ] at hkq; omega
      · have := hfm0 0 (by omega); simp only [fOf]; omega
      · intro i hi
        simp only [fOf]
        rcases Nat.lt_or_ge i n0 with h | h
        · have := hfm0 i (by omega); have := hfm0 (i + 1) (by omega); have := hIi i h; omega
        · obtain ⟨j, rfl⟩ : ∃ j, i = n0 + j := ⟨i - n0, by omega⟩
          have h1 := hfm1 (j + 1) (by omega) (by omega)
          rw [← Nat.add_assoc] at h1
          rcases Nat.eq_zero_or_pos j with hj | hj
          · subst hj
            have := hfm0 n0 (Nat.le_refl _); have := hJi 0 (by omega)
            simp only [Nat.add_zero] at *; omega
          · have := hfm1 j hj (by omega); have := hJi j (by omega); omega
      · simp only [fOf]
        rcases Nat.eq_zero_or_pos n1 with h1 | h1
        · subst h1; have := hfm0 n0 (Nat.le_refl _); simp only [Nat.add_zero] at *; omega
        · have := hfm1 n1 h1 (Nat.le_refl _); omega
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L29a8]
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    left; apply Table.ofLabels_at
    refine ⟨by decide, T.L2012.mpr ⟨hC, ⟨hrsp, hrbp⟩, h12, st, fr, _, _, hM, hx, hsp,
      ⟨by rw [hk2v]; simp only [BitVec.toNat_ofNat]; omega, hB.2⟩, hfm, hF, h13,
      h14, h40, hm⟩, ?_⟩
    edge_step

/-- `make_bands` output telescopes: `Σ_{i ≤ n} mb i = pv n - start` below `nb`. -/
theorem a2_ssum_mb {b : BitVec 32} {start stop nb : Nat} :
    ∀ n, n < nb → A2.ssum (A2.mb b start stop nb) n = A2.pv b start n - start
  | 0, _ => by simp [A2.ssum, A2.pv]
  | n + 1, h => by
    rw [A2.ssum, a2_ssum_mb n (by omega)]
    simp only [A2.mb, if_pos h, Nat.add_sub_cancel]; omega

/-- `MB` with `BandsAt`-bounds is an `Arr` with entries in `[-64, 64]` summing to
`stop - start`. -/
theorem a2_mb_arr {fr : List UInt8} {o : Nat} {pw : BitVec 32 → BitVec 32 → BitVec 32}
    {start stop nb : Nat} (hBA : BandsAt pw start stop nb) (hs : start ≤ 64) (ht : stop ≤ 64)
    (hnb : 1 ≤ nb) (hMB : A2.MB fr o (A2.bOf pw start stop nb) start stop nb nb) {B : Int}
    (hB : 64 ≤ B) : A2.Arr fr o nb B ((stop : Int) - start) := by
  have hb : ∀ j, j < nb → 0 ≤ A2.pv (A2.bOf pw start stop nb) start j
      ∧ A2.pv (A2.bOf pw start stop nb) start j ≤ 64 := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · subst h0
      have : A2.pv (A2.bOf pw start stop nb) start 0 = start := by simp [A2.pv]
      omega
    · have := hBA j h0 hj
      simp only [A2.pv, if_neg (show j ≠ 0 by omega)]; exact this
  refine ⟨A2.mb (A2.bOf pw start stop nb) start stop nb, fun i h1 h2 => ⟨hMB i h1 h2, ?_⟩, ?_⟩
  · have := hb (i - 1) (by omega)
    simp only [A2.mb]
    split
    · have := hb i (by omega); omega
    · obtain rfl : i = nb := by omega
      omega
  · obtain ⟨m, rfl⟩ : ∃ m, nb = m + 1 := ⟨nb - 1, by omega⟩
    rw [A2.ssum, a2_ssum_mb m (by omega)]
    simp only [A2.mb, Nat.lt_irrefl, if_false, Nat.add_sub_cancel]; omega

/-- `movslq` of a small zero-extended value. -/
theorem a2_sext_ofNat (n : Nat) (h : n < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.setWidth 32 (BitVec.ofNat 64 n)) = BitVec.ofNat 64 n := by
  have hm : (BitVec.setWidth 32 (BitVec.ofNat 64 n)).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    simp only [decide_eq_false_iff_not, Nat.not_le]; omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

set_option maxRecDepth 100000 in
/-- `movslq r13d, rcx; jmp L2619`: the `make_bands` output as an `Arr`. -/
theorem blk_L25ca (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L25ca" ⟨"sbr_reset.L25ca", B.L25ca, some "sbr_reset.L25cf"⟩ := by
  info_off
  measure_hb "L25ca"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hlt, hInc0, hN0, hN1, h15, hMB, h12, h13, vm, hvm1, hvm2, hTB, h30, hrax⟩,
      hm⟩⟩ := T.L25ca.mp hs
    clear hs
    have hArr : A2.Arr fr 0x480 (A2.n1N e a (k0N a row) k2) 256
        (((k2 : Nat) : Int) - (((A2.k1Of (k0N a row) k2) : Nat) : Int)) := by
      have hk0 := k0Of_range hrow hC.2.1
      have hb := ((a2_bands_of hB hC hrow hk2 hk02 hkq hu).2 hlt).2.2
      refine a2_mb_arr hb ?_ hk2 ?_ hMB (by omega)
      rotate_left
      · show 1 ≤ (A2.n1I e a (k0N a row) k2).toNat
        have := hN1.1; omega
      unfold A2.k1Of; split <;> omega
    have hn1lt : A2.n1N e a (k0N a row) k2 < 2 ^ 31 := by
      show (A2.n1I e a (k0N a row) k2).toNat < 2 ^ 31
      have := hN1.2.1; omega
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L25ca]
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, BitVec.ofNat_eq_ofNat] at *
    left; apply Table.ofLabels_at
    refine ⟨by decide, T.L2619.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st, fr, hx,
      hsp, hfm, hF, ⟨hk2v, hk1v, hlt, hInc0, hN0, hN1, ?_, ?_, ?_, vm, hTB.1, ?_, ?_, hArr⟩, hm⟩⟩, ?_⟩
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h13, h15, hrax]
    all_goals try edge_step
    exact a2_sext_ofNat _ hn1lt

end Kraken.Examples.Sbr.Reset
