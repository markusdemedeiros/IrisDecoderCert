import Kraken.InfoOff
import Kraken.X64.Examples.Sbr.Parse.ResetA1F1

/-!
# `sbr_reset`: `bs_freq_scale = 0`, the unrolled prefix sums `L1f30`..`L1fa5` (shard A1)
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
theorem a1_cc_z {w : Nat} (x : BitVec w) (f : StatusFlags.from_result.Remaining) :
    CondCode.z.interp (StatusFlags.from_result x f) = decide (x = 0) := by
  rw [CondCode.interp_z]
  by_cases h : x = 0
  · simp [h, StatusFlags.from_result]
  · simp [StatusFlags.from_result]; exact rfl

omit [CodeEnv] in
theorem a1_and6 : ∀ n, n < 49 → n % 2 = 0 →
    ((BitVec.setWidth 8 (BitVec.ofNat 64 n) &&& BitVec.setWidth 8 6#64 = 0) ↔ n % 8 = 0) := by
  decide

section PS

variable {k : Nat} {e : REnv} {a : RArgs} {ra : Int64} {t₀ : MachineData} {st : St}
  {fr : List UInt8} {m : Mem 64}

/-- One prefix-sum step at `f_master[t + 1]`: the load reads the step, the sum is the next prefix
sum, and storing it extends `Summed`. -/
theorem a1_ps_step (hm : m =⋆ Mm k e a ra t₀ st fr) (hl : st.fm.length = 98) {k0 dk nm : Nat}
    {diff : Int} {t : Nat} (hs : Summed st.fm k0 dk nm diff t) (ht : t + 1 ≤ nm) (hnm : nm ≤ 48)
    (h0 : 0 ≤ fvOf k0 dk nm diff (t + 1)) (h1 : fvOf k0 dk nm diff (t + 1) < 32768)
    {addr : BitVec 64} (ha : addr = arg1 t₀ + 0x4c1f0#64 + BitVec.ofNat 64 (2 * (t + 1))) :
    m.loadInt addr 2 = some (u16 st.fm (t + 1) : Int)
    ∧ BitVec.ofInt 16 (u16 st.fm (t + 1) : Int) + BitVec.ofInt 16 (fvOf k0 dk nm diff t)
      = BitVec.ofInt 16 (fvOf k0 dk nm diff (t + 1))
    ∧ (BitVec.ofInt 16 (fvOf k0 dk nm diff (t + 1))).toInt = fvOf k0 dk nm diff (t + 1)
    ∧ (m.loadInt addr 2).isSome = true
    ∧ ∃ st' : St, st'.x = st.x ∧ st'.sp = st.sp ∧ st'.k2 = st.k2 ∧ st'.nm = st.nm
      ∧ st'.fm.length = 98 ∧ Summed st'.fm k0 dk nm diff (t + 1)
      ∧ (m.storeInt addr 2 (fvOf k0 dk nm diff (t + 1)) =⋆ Mm k e a ra t₀ st' fr) := by
  have hld := a1_fmi_load hm hl (i := t + 1) (by omega) ha
  refine ⟨hld, ?_, a1_toInt16 h0 h1, by rw [hld]; rfl,
    { st with fm := wr st.fm (2 * (t + 1)) (Int.toBytes 2 (fvOf k0 dk nm diff (t + 1))) }, rfl, rfl, rfl, rfl,
    by show (wr _ _ _).length = 98; rw [wr_length (by rw [Int.toBytes_length, hl]; omega), hl],
    a1_summed_step hl ht hnm hs h0 (by omega), a1_fmi_store hm hl (by omega) ha _⟩
  rw [hs.2 (t + 1) (by omega) ht, ← BitVec.ofInt_add, fvOf, Int.add_comm]

end PS

theorem blk_L1f30 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1f30" ⟨"sbr_reset.L1f30", B.L1f30, some "sbr_reset.L1f5d"⟩ := by
  info_off
  measure_hb "L1f30"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hr, hk2, hle, hq, h3, ⟨hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2s, ⟨h2, hxo, hnm, hdx⟩, hcx, j, hax, hj8, hjl, hsum, h13⟩, hm⟩, h12, h15⟩ :=
      T.L1f30.mp hs
    clear hs
    have h48 := f0_nm_48 hr hC.2.1 hq
    have hk0 := k0Of_range hr (st := u8 a.sp 0) hC.2.1
    have hA4 : (a.sp.getD 4 0).toNat ≤ 1 := hC.2.2.2.1
    have hk0n : 1 ≤ k0N a row ∧ k0N a row ≤ 32 := by
      have := hk0; simp only [k0N, srI, u8] at this
      show 1 ≤ (k0Of a.x.sampleRate.toInt row (a.sp.getD 0 0).toNat).toNat
        ∧ (k0Of a.x.sampleRate.toInt row (a.sp.getD 0 0).toNat).toNat ≤ 32
      omega
    generalize hNdef : nmOf (k2 - k0N a row) (u8 a.sp 4) = N at *
    generalize hD : diffOf (k0N a row) k2 N (u8 a.sp 4 + 1) = D at *
    have hj8' : j + 8 ≤ N := by omega
    have hdk : u8 a.sp 4 + 1 ≤ 2 := by simp only [u8] at hA4 ⊢; omega
    have R := fun t (ht : t ≤ 48) => a1_fv_range (nm := N) (diff := D) hk0n.1 hk0n.2 (by omega) hdk ht
    have ha1 : t₀.regs.get64 .rsi + BitVec.ofNat 64 j * 2#64 + 311794#64
        = arg1 t₀ + 0x4c1f0#64 + BitVec.ofNat 64 (2 * (j + 1)) := by simp only [arg1]; bv_omega
    have ha2 : t₀.regs.get64 .rsi + BitVec.ofNat 64 j * 2#64 + 311796#64
        = arg1 t₀ + 0x4c1f0#64 + BitVec.ofNat 64 (2 * (j + 1 + 1)) := by simp only [arg1]; bv_omega
    have ha3 : t₀.regs.get64 .rsi + BitVec.ofNat 64 j * 2#64 + 311798#64
        = arg1 t₀ + 0x4c1f0#64 + BitVec.ofNat 64 (2 * (j + 2 + 1)) := by simp only [arg1]; bv_omega
    obtain ⟨L1, S1, V1, I1, st1, X1, P1, K1, N1, W1, U1, M1⟩ := a1_ps_step hm hfm hsum (by omega) h48 (R _ (by omega)).1
      (R _ (by omega)).2 ha1
    obtain ⟨L2, S2, V2, I2, st2, X2, P2, K2, N2, W2, U2, M2⟩ := a1_ps_step M1 W1 U1 (by omega) h48 (R _ (by omega)).1
      (R _ (by omega)).2 ha2
    obtain ⟨L3, S3, V3, I3, st3, X3, P3, K3, N3, W3, U3, M3⟩ := a1_ps_step M2 W2 U2 (by omega) h48 (R _ (by omega)).1
      (R _ (by omega)).2 ha3
    simp only [B.L1f30]
    vcgen
    all_goals try subst s₀
    all_goals try subst n
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hdx, hax, hcx,
      AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2,
      Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    · exact I1
    · exact I1
    · rename_i mv1 hv1
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hdx, hax, hcx, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.setWidth_replaceLow16, h13, S1, V1, S2, V2, S3, V3] at hv1
      rw [L1] at hv1; obtain rfl := Option.some.inj hv1
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hdx, hax, hcx, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.setWidth_replaceLow16, h13, S1, V1, S2, V2, S3, V3]
      exact I2
    · rename_i mv1 hv1 mv2 hv2
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hdx, hax, hcx, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.setWidth_replaceLow16, h13, S1, V1, S2, V2, S3, V3] at hv1
      rw [L1] at hv1; obtain rfl := Option.some.inj hv1
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hdx, hax, hcx, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.setWidth_replaceLow16, h13, S1, V1, S2, V2, S3, V3] at hv2 ⊢
      rw [L2] at hv2; obtain rfl := Option.some.inj hv2
      exact I2
    · rename_i mv1 hv1 mv2 hv2
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hdx, hax, hcx, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.setWidth_replaceLow16, h13, S1, V1, S2, V2, S3, V3] at hv1
      rw [L1] at hv1; obtain rfl := Option.some.inj hv1
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hdx, hax, hcx, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.setWidth_replaceLow16, h13, S1, V1, S2, V2, S3, V3] at hv2 ⊢
      rw [L2] at hv2; obtain rfl := Option.some.inj hv2
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hdx, hax, hcx, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.setWidth_replaceLow16, h13, S1, V1, S2, V2, S3, V3]
      exact I3
    · rename_i mv1 hv1 mv2 hv2 mv3 hv3
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hdx, hax, hcx, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.setWidth_replaceLow16, h13, S1, V1, S2, V2, S3, V3] at hv1
      rw [L1] at hv1; obtain rfl := Option.some.inj hv1
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hdx, hax, hcx, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.setWidth_replaceLow16, h13, S1, V1, S2, V2, S3, V3] at hv2 hv3 ⊢
      rw [L2] at hv2; obtain rfl := Option.some.inj hv2
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hdx, hax, hcx, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.setWidth_replaceLow16, h13, S1, V1, S2, V2, S3, V3] at hv3 ⊢
      rw [L3] at hv3; obtain rfl := Option.some.inj hv3
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hdx, hax, hcx, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.setWidth_replaceLow16, h13, S1, V1, S2, V2, S3, V3]
      subst hD; subst hNdef
      refine ⟨T.L1f5d.mpr ⟨row, k2, hr, hk2, hle, hq, h3, ⟨hC, hBO, ⟨?_, ?_⟩, st2, fr, X2.trans (X1.trans hx),
        P2.trans (P1.trans hsp), W2, hF, ⟨K2.trans (K1.trans hk2s), ⟨h2, hxo, N2.trans (N1.trans hnm), ?_⟩, ?_,
        j, ?_, hj8, hjl, U2, ?_⟩, ?_⟩, ?_, ?_⟩, by
          simp only [lex_var, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
          refine Kraken.lex_cons_le_cons (by lex_len) ?_
          refine Kraken.lex_cons_le_cons (by lex_len) ?_
          refine Kraken.lex_cons_le_of_lt (by lex_len) ?_
          decide⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, BitVec.setWidth_replaceLow16]
      all_goals first
        | (simp only [hrsp, hrbp, h12, h15, hdx, hcx, hax]; done)
        | exact M2
        | exact rfl

theorem blk_L1f5d (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1f5d" ⟨"sbr_reset.L1f5d", B.L1f5d, some "sbr_reset.L1f81"⟩ := by
  info_off
  measure_hb "L1f5d"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hr, hk2, hle, hq, h3, ⟨hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2s, ⟨h2, hxo, hnm, hdx⟩, hcx, j, hax, hj8, hjl, hsum, h13⟩, hm⟩, h12, h15⟩ :=
      T.L1f5d.mp hs
    clear hs
    have h48 := f0_nm_48 hr hC.2.1 hq
    have hk0 := k0Of_range hr (st := u8 a.sp 0) hC.2.1
    have hA4 : (a.sp.getD 4 0).toNat ≤ 1 := hC.2.2.2.1
    have hk0n : 1 ≤ k0N a row ∧ k0N a row ≤ 32 := by
      have := hk0; simp only [k0N, srI, u8] at this
      show 1 ≤ (k0Of a.x.sampleRate.toInt row (a.sp.getD 0 0).toNat).toNat
        ∧ (k0Of a.x.sampleRate.toInt row (a.sp.getD 0 0).toNat).toNat ≤ 32
      omega
    generalize hNdef : nmOf (k2 - k0N a row) (u8 a.sp 4) = N at *
    generalize hD : diffOf (k0N a row) k2 N (u8 a.sp 4 + 1) = D at *
    have hj8' : j + 8 ≤ N := by omega
    have hdk : u8 a.sp 4 + 1 ≤ 2 := by simp only [u8] at hA4 ⊢; omega
    have R := fun t (ht : t ≤ 48) => a1_fv_range (nm := N) (diff := D) hk0n.1 hk0n.2 (by omega) hdk ht
    have ha0 : t₀.regs.get64 .rsi + BitVec.ofNat 64 j * 2#64 + 311798#64
        = arg1 t₀ + 0x4c1f0#64 + BitVec.ofNat 64 (2 * (j + 2 + 1)) := by simp only [arg1]; bv_omega
    have ha1 : t₀.regs.get64 .rsi + BitVec.ofNat 64 j * 2#64 + 311800#64
        = arg1 t₀ + 0x4c1f0#64 + BitVec.ofNat 64 (2 * (j + 2 + 1 + 1)) := by simp only [arg1]; bv_omega
    have ha2 : t₀.regs.get64 .rsi + BitVec.ofNat 64 j * 2#64 + 311802#64
        = arg1 t₀ + 0x4c1f0#64 + BitVec.ofNat 64 (2 * (j + 2 + 1 + 1 + 1)) := by simp only [arg1]; bv_omega
    obtain ⟨L0, S0, V0, I0, st0, X0, P0, K0, N0, W0, U0, M0⟩ := a1_ps_step hm hfm hsum (by omega) h48
      (R _ (by omega)).1 (R _ (by omega)).2 ha0
    obtain ⟨L1, S1, V1, I1, st1, X1, P1, K1, N1, W1, U1, M1⟩ := a1_ps_step M0 W0 U0 (by omega) h48
      (R _ (by omega)).1 (R _ (by omega)).2 ha1
    obtain ⟨L2, S2, V2, I2, st2, X2, P2, K2, N2, W2, U2, M2⟩ := a1_ps_step M1 W1 U1 (by omega) h48
      (R _ (by omega)).1 (R _ (by omega)).2 ha2
    simp only [B.L1f5d]
    vcgen
    all_goals try subst s₀
    all_goals try subst n
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hdx, hax, hcx, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.setWidth_replaceLow16, h13, V0, S1, V1, S2, V2]
    · exact I0
    · exact I1
    · rename_i mv1 hv1
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hdx, hax, hcx, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.setWidth_replaceLow16, h13, V0, S1, V1, S2, V2] at hv1
      rw [L1] at hv1; obtain rfl := Option.some.inj hv1
      try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hdx, hax, hcx, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.setWidth_replaceLow16, h13, V0, S1, V1, S2, V2]
      exact I1
    · rename_i mv1 hv1
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hdx, hax, hcx, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.setWidth_replaceLow16, h13, V0, S1, V1, S2, V2] at hv1
      rw [L1] at hv1; obtain rfl := Option.some.inj hv1
      try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hdx, hax, hcx, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.setWidth_replaceLow16, h13, V0, S1, V1, S2, V2]
      exact I2
    · rename_i mv1 hv1 mv2 hv2
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hdx, hax, hcx, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.setWidth_replaceLow16, h13, V0, S1, V1, S2, V2] at hv1
      rw [L1] at hv1; obtain rfl := Option.some.inj hv1
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hdx, hax, hcx, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.setWidth_replaceLow16, h13, V0, S1, V1, S2, V2] at hv2 ⊢
      rw [L2] at hv2; obtain rfl := Option.some.inj hv2
      try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hdx, hax, hcx, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.setWidth_replaceLow16, h13, V0, S1, V1, S2, V2]
      subst hD; subst hNdef
      refine ⟨T.L1f81.mpr ⟨row, k2, hr, hk2, hle, hq, h3, ⟨hC, hBO, ⟨?_, ?_⟩, st1, fr,
        X1.trans (X0.trans hx), P1.trans (P0.trans hsp), W1, hF, ⟨K1.trans (K0.trans hk2s),
        ⟨h2, hxo, N1.trans (N0.trans hnm), ?_⟩, ?_, j, ?_, hj8, hjl, U1, ?_⟩, ?_⟩, ?_, ?_⟩, by
          simp only [lex_var, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
          refine Kraken.lex_cons_le_cons (by lex_len) ?_
          refine Kraken.lex_cons_le_cons (by lex_len) ?_
          refine Kraken.lex_cons_le_of_lt (by lex_len) ?_
          decide⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, BitVec.setWidth_replaceLow16]
      all_goals first
        | (simp only [hrsp, hrbp, h12, h15, hdx, hcx, hax]; done)
        | exact M1
        | exact rfl

theorem blk_L1f81 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1f81" ⟨"sbr_reset.L1f81", B.L1f81, some "sbr_reset.L1fa5"⟩ := by
  info_off
  measure_hb "L1f81"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hr, hk2, hle, hq, h3, ⟨hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2s, ⟨h2, hxo, hnm, hdx⟩, hcx, j, hax, hj8, hjl, hsum, h13⟩, hm⟩, h12, h15⟩ :=
      T.L1f81.mp hs
    clear hs
    have h48 := f0_nm_48 hr hC.2.1 hq
    have hk0 := k0Of_range hr (st := u8 a.sp 0) hC.2.1
    have hA4 : (a.sp.getD 4 0).toNat ≤ 1 := hC.2.2.2.1
    have hk0n : 1 ≤ k0N a row ∧ k0N a row ≤ 32 := by
      have := hk0; simp only [k0N, srI, u8] at this
      show 1 ≤ (k0Of a.x.sampleRate.toInt row (a.sp.getD 0 0).toNat).toNat
        ∧ (k0Of a.x.sampleRate.toInt row (a.sp.getD 0 0).toNat).toNat ≤ 32
      omega
    generalize hNdef : nmOf (k2 - k0N a row) (u8 a.sp 4) = N at *
    generalize hD : diffOf (k0N a row) k2 N (u8 a.sp 4 + 1) = D at *
    have hj8' : j + 8 ≤ N := by omega
    have hdk : u8 a.sp 4 + 1 ≤ 2 := by simp only [u8] at hA4 ⊢; omega
    have R := fun t (ht : t ≤ 48) => a1_fv_range (nm := N) (diff := D) hk0n.1 hk0n.2 (by omega) hdk ht
    have ha0 : t₀.regs.get64 .rsi + BitVec.ofNat 64 j * 2#64 + 311802#64
        = arg1 t₀ + 0x4c1f0#64 + BitVec.ofNat 64 (2 * (j + 4 + 1)) := by simp only [arg1]; bv_omega
    have ha1 : t₀.regs.get64 .rsi + BitVec.ofNat 64 j * 2#64 + 311804#64
        = arg1 t₀ + 0x4c1f0#64 + BitVec.ofNat 64 (2 * (j + 4 + 1 + 1)) := by simp only [arg1]; bv_omega
    have ha2 : t₀.regs.get64 .rsi + BitVec.ofNat 64 j * 2#64 + 311806#64
        = arg1 t₀ + 0x4c1f0#64 + BitVec.ofNat 64 (2 * (j + 4 + 1 + 1 + 1)) := by simp only [arg1]; bv_omega
    obtain ⟨L0, S0, V0, I0, st0, X0, P0, K0, N0, W0, U0, M0⟩ := a1_ps_step hm hfm hsum (by omega) h48
      (R _ (by omega)).1 (R _ (by omega)).2 ha0
    obtain ⟨L1, S1, V1, I1, st1, X1, P1, K1, N1, W1, U1, M1⟩ := a1_ps_step M0 W0 U0 (by omega) h48
      (R _ (by omega)).1 (R _ (by omega)).2 ha1
    obtain ⟨L2, S2, V2, I2, st2, X2, P2, K2, N2, W2, U2, M2⟩ := a1_ps_step M1 W1 U1 (by omega) h48
      (R _ (by omega)).1 (R _ (by omega)).2 ha2
    simp only [B.L1f81]
    vcgen
    all_goals try subst s₀
    all_goals try subst n
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hdx, hax, hcx, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.setWidth_replaceLow16, h13, V0, S1, V1, S2, V2]
    · exact I0
    · exact I1
    · rename_i mv1 hv1
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hdx, hax, hcx, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.setWidth_replaceLow16, h13, V0, S1, V1, S2, V2] at hv1
      rw [L1] at hv1; obtain rfl := Option.some.inj hv1
      try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hdx, hax, hcx, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.setWidth_replaceLow16, h13, V0, S1, V1, S2, V2]
      exact I1
    · rename_i mv1 hv1
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hdx, hax, hcx, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.setWidth_replaceLow16, h13, V0, S1, V1, S2, V2] at hv1
      rw [L1] at hv1; obtain rfl := Option.some.inj hv1
      try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hdx, hax, hcx, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.setWidth_replaceLow16, h13, V0, S1, V1, S2, V2]
      exact I2
    · rename_i mv1 hv1 mv2 hv2
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hdx, hax, hcx, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.setWidth_replaceLow16, h13, V0, S1, V1, S2, V2] at hv1
      rw [L1] at hv1; obtain rfl := Option.some.inj hv1
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hdx, hax, hcx, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.setWidth_replaceLow16, h13, V0, S1, V1, S2, V2] at hv2 ⊢
      rw [L2] at hv2; obtain rfl := Option.some.inj hv2
      try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hdx, hax, hcx, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.setWidth_replaceLow16, h13, V0, S1, V1, S2, V2]
      subst hD; subst hNdef
      refine ⟨T.L1fa5.mpr ⟨row, k2, hr, hk2, hle, hq, h3, ⟨hC, hBO, ⟨?_, ?_⟩, st1, fr,
        X1.trans (X0.trans hx), P1.trans (P0.trans hsp), W1, hF, ⟨K1.trans (K0.trans hk2s),
        ⟨h2, hxo, N1.trans (N0.trans hnm), ?_⟩, ?_, j, ?_, hj8, hjl, U1, ?_⟩, ?_⟩, ?_, ?_⟩, by
          simp only [lex_var, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
          refine Kraken.lex_cons_le_cons (by lex_len) ?_
          refine Kraken.lex_cons_le_cons (by lex_len) ?_
          refine Kraken.lex_cons_le_of_lt (by lex_len) ?_
          decide⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, BitVec.setWidth_replaceLow16]
      all_goals first
        | (simp only [hrsp, hrbp, h12, h15, hdx, hcx, hax]; done)
        | exact M1
        | exact rfl

theorem blk_L1fa5 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1fa5" ⟨"sbr_reset.L1fa5", B.L1fa5, some "sbr_reset.L1fd5"⟩ := by
  info_off
  measure_hb "L1fa5"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hr, hk2, hle, hq, h3, ⟨hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2s, ⟨h2, hxo, hnm, hdx⟩, hcx, j, hax, hj8, hjl, hsum, h13⟩, hm⟩, h12, h15⟩ :=
      T.L1fa5.mp hs
    clear hs
    have h48 := f0_nm_48 hr hC.2.1 hq
    have hk0 := k0Of_range hr (st := u8 a.sp 0) hC.2.1
    have hA4 : (a.sp.getD 4 0).toNat ≤ 1 := hC.2.2.2.1
    have hk0n : 1 ≤ k0N a row ∧ k0N a row ≤ 32 := by
      have := hk0; simp only [k0N, srI, u8] at this
      show 1 ≤ (k0Of a.x.sampleRate.toInt row (a.sp.getD 0 0).toNat).toNat
        ∧ (k0Of a.x.sampleRate.toInt row (a.sp.getD 0 0).toNat).toNat ≤ 32
      omega
    generalize hNdef : nmOf (k2 - k0N a row) (u8 a.sp 4) = N at *
    have hev : N % 2 = 0 := by rw [← hNdef]; unfold nmOf; split <;> omega
    generalize hD : diffOf (k0N a row) k2 N (u8 a.sp 4 + 1) = D at *
    have hj8' : j + 8 ≤ N := by omega
    have hdk : u8 a.sp 4 + 1 ≤ 2 := by simp only [u8] at hA4 ⊢; omega
    have R := fun t (ht : t ≤ 48) => a1_fv_range (nm := N) (diff := D) hk0n.1 hk0n.2 (by omega) hdk ht
    have ha0 : t₀.regs.get64 .rsi + BitVec.ofNat 64 j * 2#64 + 311806#64
        = arg1 t₀ + 0x4c1f0#64 + BitVec.ofNat 64 (2 * (j + 6 + 1)) := by simp only [arg1]; bv_omega
    have ha1 : t₀.regs.get64 .rsi + BitVec.ofNat 64 j * 2#64 + 311808#64
        = arg1 t₀ + 0x4c1f0#64 + BitVec.ofNat 64 (2 * (j + 6 + 1 + 1)) := by simp only [arg1]; bv_omega
    obtain ⟨L0, S0, V0, I0, st0, X0, P0, K0, N0, W0, U0, M0⟩ := a1_ps_step hm hfm hsum (by omega) h48
      (R _ (by omega)).1 (R _ (by omega)).2 ha0
    obtain ⟨L1, S1, V1, I1, st1, X1, P1, K1, N1, W1, U1, M1⟩ := a1_ps_step M0 W0 U0 (by omega) h48
      (R _ (by omega)).1 (R _ (by omega)).2 ha1
    have hrax : BitVec.setWidth 64 8#64 + BitVec.ofNat 64 j = BitVec.ofNat 64 (j + 8) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      omega
    have hrax1 : BitVec.ofNat 64 (j + 8) + 1#64 = BitVec.ofNat 64 (j + 8 + 1) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    have hrax1' : BitVec.ofNat 64 (j + 8) + 1 = BitVec.ofNat 64 (j + 8 + 1) := hrax1
    rw [show j + 7 = j + 6 + 1 from rfl] at h13
    simp only [B.L1fa5]
    vcgen
    all_goals try subst s₀
    all_goals try subst n
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hdx, hax, hcx, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.setWidth_replaceLow16, h13, V0, S1, V1]
    · exact I0
    · exact I1
    · rename_i mv1 hv1
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hdx, hax, hcx, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.setWidth_replaceLow16, h13, V0, S1, V1] at hv1
      rw [L1] at hv1; obtain rfl := Option.some.inj hv1
      try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hdx, hax, hcx, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.setWidth_replaceLow16, h13, V0, S1, V1]
      exact I1
    · rename_i mv1 hv1 g1
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hdx, hax, hcx, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.setWidth_replaceLow16, h13, V0, S1, V1] at hv1
      rw [L1] at hv1; obtain rfl := Option.some.inj hv1
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hdx, hax, hcx, cc_nz_sub, cc_z_sub, a1_cc_z, hrax, a1_and6 N (by omega) hev, decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true', Bool.not_eq_false', Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat] at g1
      have hlt : j + 8 < N / 8 * 8 := by
        rcases Nat.lt_or_ge (j + 8) (N / 8 * 8) with h | h
        · exact h
        · exfalso; apply g1; rw [show N / 8 * 8 = j + 8 by omega]
      subst hD; subst hNdef
      refine Or.inl (Table.ofLabels_at ⟨S.L1f30, T.L1f30.mpr ⟨row, k2, hr, hk2, hle, hq, h3,
        ⟨hC, hBO, ⟨?_, ?_⟩, st1, fr, X1.trans (X0.trans hx), P1.trans (P0.trans hsp), W1, hF,
        ⟨K1.trans (K0.trans hk2s), ⟨h2, hxo, N1.trans (N0.trans hnm), ?_⟩, ?_, j + 8, ?_, by omega, ?_, U1, ?_⟩,
        ?_⟩, ?_, ?_⟩, by
          left
          simp only [lex_var, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hax, hrax,
            BitVec.toNat_ofNat]
          refine Kraken.lex_cons_lt_cons (by lex_len) ?_
          refine Kraken.lex_cons_lt_of_lt (by lex_len) ?_
          simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hax, hrax, BitVec.toNat_ofNat]
          lex_digit⟩)
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, BitVec.setWidth_replaceLow16,
        hrax, hrax1, hrax1', hax, h13, V0, S1, V1]
      all_goals try simp only [k0N, k0A, u8, srI]
      all_goals first
        | (simp only [hrsp, hrbp, h12, h15, hdx, hcx, hax]; done)
        | exact M1
        | exact rfl
        | omega
    all_goals rename_i mv1 hv1 g1 b1 g2
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hdx, hax, hcx, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.setWidth_replaceLow16, h13, V0, S1, V1] at hv1
    all_goals rw [L1] at hv1
    all_goals obtain rfl := Option.some.inj hv1
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hdx, hax, hcx, cc_nz_sub, cc_z_sub, a1_cc_z, hrax, a1_and6 N (by omega) hev, decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true', Bool.not_eq_false', Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat] at g1 g2
    · have hN : N = j + 8 := by
        have h8 := (a1_and6 N (by omega) hev).mp g2
        have := congrArg BitVec.toNat g1
        simp only [BitVec.toNat_ofNat] at this
        omega
      subst hD; subst hNdef
      refine Or.inl (Table.ofLabels_at ⟨S.L2003, T.L2003.mpr ⟨row, k2, hr, hk2, hle, hq, h3,
        ⟨hC, hBO, ⟨?_, ?_⟩, st1, fr, X1.trans (X0.trans hx), P1.trans (P0.trans hsp), W1, hF,
        ⟨K1.trans (K0.trans hk2s), h2, hxo, N1.trans (N0.trans hnm),
          a1_summed_idx (by have := hN; simp only [k0N, k0A, u8, srI] at this ⊢; omega) U1⟩, ?_⟩,
        ?_, ?_⟩, by edge_step⟩)
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, BitVec.setWidth_replaceLow16,
        hrax, hrax1, hrax1', hax, h13, V0, S1, V1]
      all_goals try simp only [k0N, k0A, u8, srI]
      all_goals first
        | (simp only [hrsp, hrbp, h12, h15, hdx, hcx, hax]; done)
        | exact M1
        | exact rfl
        | omega
    · have hN : N / 8 * 8 = j + 8 := by
        have := congrArg BitVec.toNat g1
        simp only [BitVec.toNat_ofNat] at this
        omega
      have hlt : j + 8 < N := by
        have h8 : ¬ N % 8 = 0 := fun h => by
          first
            | exact g2 ((a1_and6 N (by omega) hev).mpr h)
            | exact absurd ((a1_and6 N (by omega) hev).mpr h) g2
        omega
      subst hD; subst hNdef
      refine ⟨T.L1fd5.mpr ⟨row, k2, hr, hk2, hle, hq, h3,
        ⟨hC, hBO, ⟨?_, ?_⟩, st1, fr, X1.trans (X0.trans hx), P1.trans (P0.trans hsp), W1, hF,
        ⟨K1.trans (K0.trans hk2s), ⟨h2, hxo, N1.trans (N0.trans hnm), ?_⟩, j + 8, ?_, by omega, ?_, ?_,
          U1, ?_⟩, ?_⟩, ?_, ?_⟩, by var_step⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, BitVec.setWidth_replaceLow16,
        hrax, hrax1, hrax1', hax, h13, V0, S1, V1]
      all_goals try simp only [k0N, k0A, u8, srI]
      all_goals first
        | (simp only [hrsp, hrbp, h12, h15, hdx, hcx, hax]; done)
        | exact M1
        | exact rfl
        | omega

end Kraken.Examples.Sbr.Reset
