import Kraken.InfoOff
import Kraken.X64.Examples.Sbr.Parse.ResetA1F2

/-!
# `sbr_reset`: `bs_freq_scale = 0`, the `k2diff` correction `L1ec1` (shard A1)

`L1ec1`: `k2diff = k[2] - (k[0] + n_master * dk)` in 32 bits; negative goes to `L1ed8`, zero to
`L1f08`, positive (`= 1`) adds one to `f_master[n_master]` (`incw`) and goes to `L1f08`.
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
/-- `k2diff` is in `[-2, 1]`, and `≥ 0` for `dk = 1`. -/
theorem a1_diff_bounds {k0 k2 alter : Nat} (hle : k0 ≤ k2) (ha : alter ≤ 1) :
    diffOf k0 k2 (nmOf (k2 - k0) alter) (alter + 1) ≤ 1
      ∧ -2 ≤ diffOf k0 k2 (nmOf (k2 - k0) alter) (alter + 1)
      ∧ (alter = 0 → 0 ≤ diffOf k0 k2 (nmOf (k2 - k0) alter) (alter + 1)) := by
  simp only [diffOf]
  rcases Nat.lt_or_ge alter 1 with h | h
  · obtain rfl : alter = 0 := by omega
    simp only [nmOf, ite_true, Nat.zero_add, Int.natCast_one, Int.mul_one]
    omega
  · obtain rfl : alter = 1 := by omega
    refine ⟨?_, ?_, fun h => absurd h (by decide)⟩
    all_goals simp only [nmOf, show (1 : Nat) ≠ 0 by decide, ite_false, Nat.reduceAdd]
    all_goals rw [← Int.natCast_mul]
    all_goals omega

omit [CodeEnv] in
/-- `k2diff` in 32 bits (`imul`, `add`, `sub` of `L1ec1`). -/
theorem a1_k2diff32 {k0 k2 dk N : Nat} (h0 : k0 ≤ 32) (hk2 : k2 ≤ 64) (hdk : dk ≤ 2) (hN : N ≤ 48) :
    BitVec.setWidth 32 (BitVec.ofNat 64 k2) - BitVec.setWidth 32 (BitVec.setWidth 64
      (BitVec.setWidth 32 (BitVec.ofNat 64 k0) + BitVec.setWidth 32 (BitVec.setWidth 64
        (BitVec.setWidth 32 (BitVec.ofNat 64 dk) * BitVec.setWidth 32 (BitVec.ofNat 64 N)))))
      = BitVec.ofInt 32 ((k2 : Int) - k0 - N * dk) := by
  have hP : dk * N ≤ 96 := Nat.mul_le_mul hdk hN
  have s2 : ∀ x : BitVec 32, BitVec.setWidth 32 (BitVec.setWidth 64 x) = x := fun x => by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth]
    have := x.isLt
    omega
  have hm : BitVec.setWidth 32 (BitVec.ofNat 64 dk) * BitVec.setWidth 32 (BitVec.ofNat 64 N)
      = BitVec.ofNat 32 (dk * N) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := dk) (by omega), Nat.mod_eq_of_lt (a := N) (by omega),
      Nat.mod_eq_of_lt (a := dk) (by omega), Nat.mod_eq_of_lt (a := N) (by omega)]
  rw [hm, s2, s2]
  have e : ((N : Int) * dk) = ((dk * N : Nat) : Int) := by rw [Int.natCast_mul, Int.mul_comm]
  rw [e]
  generalize dk * N = P at *
  have s1 : ∀ x, x < 2 ^ 32 → BitVec.setWidth 32 (BitVec.ofNat 64 x) = BitVec.ofNat 32 x := by
    intro x hx
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  rw [s1 k2 (by omega), s1 k0 (by omega), Int.sub_eq_add_neg, Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_add,
    BitVec.ofInt_neg, BitVec.ofInt_neg, BitVec.ofInt_natCast,
    BitVec.ofInt_natCast, BitVec.ofInt_natCast]
  bv_omega

omit [CodeEnv] in
theorem a1_d_msb {D : Int} (h0 : -2 ≤ D) (h1 : D ≤ 1) : (BitVec.ofInt 32 D).msb = decide (D < 0) := by
  obtain h | h | h | h : D = -2 ∨ D = -1 ∨ D = 0 ∨ D = 1 := by omega
  all_goals subst h; decide

omit [CodeEnv] in
theorem a1_d_zero {D : Int} (h0 : -2 ≤ D) (h1 : D ≤ 1) : (BitVec.ofInt 32 D = 0) ↔ D = 0 := by
  obtain h | h | h | h : D = -2 ∨ D = -1 ∨ D = 0 ∨ D = 1 := by omega
  all_goals subst h; decide

omit [CodeEnv] in
theorem a1_stepped0 {fm : List UInt8} {dk N : Nat} (h : Filled fm dk (N + 1)) : Stepped fm dk N 0 := by
  intro i h1 h2
  rw [h i h1 (by omega)]
  simp only [stepOf]
  omega

omit [CodeEnv] in
theorem a1_stepped1 {fm : List UInt8} {dk N : Nat} (hl : fm.length = 98) (hN : N ≤ 48)
    (h1 : 1 ≤ N) (h : Filled fm dk (N + 1)) (hdk : dk ≤ 2) :
    Stepped (wr fm (2 * N) (Int.toBytes 2 ((dk : Int) + 1))) dk N 1 := by
  have hb : (Int.toBytes 2 ((dk : Int) + 1)).length = 2 := Int.toBytes_length ..
  intro i hi1 hi2
  rcases (show i < N ∨ i = N by omega) with hlt | rfl
  · rw [a1_u16_wr_ne (by omega) (by omega), h i hi1 (by omega)]
    unfold stepOf
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
    omega
  · rw [a1_u16_wr_int (by omega) (by omega) (by omega)]
    unfold stepOf
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
    omega

omit [CodeEnv] in
theorem a1_inc16 {dk : Nat} (hdk : dk ≤ 2) : (BitVec.ofInt 16 (dk : Int) + 1#16).toInt = (dk : Int) + 1 := by
  rw [show (BitVec.ofInt 16 (dk : Int) + 1#16) = BitVec.ofInt 16 ((dk : Int) + 1) by
    rw [BitVec.ofInt_add]; rfl]
  exact a1_toInt16 (by omega) (by omega)

theorem blk_L1ec1 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1ec1" ⟨"sbr_reset.L1ec1", B.L1ec1, some "sbr_reset.L1ed8"⟩ := by
  info_off
  measure_hb "L1ec1"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hr, hk2, hle, hq, h3, ⟨hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2s, ⟨⟨h2, hxo, hnm, hdx⟩, hsi, h13, hax, hcx⟩, hfil⟩, hm⟩, h12, h15⟩ := T.L1ec1.mp hs
    clear hs
    have h48 := f0_nm_48 hr hC.2.1 hq
    have hk0 := k0Of_range hr (st := u8 a.sp 0) hC.2.1
    have hA4 : u8 a.sp 4 ≤ 1 := hC.2.2.2.1
    have hk0n : 1 ≤ k0N a row ∧ k0N a row ≤ 32 := by
      have := hk0; simp only [k0N, srI, u8] at this
      show 1 ≤ (k0Of a.x.sampleRate.toInt row (a.sp.getD 0 0).toNat).toNat
        ∧ (k0Of a.x.sampleRate.toInt row (a.sp.getD 0 0).toNat).toNat ≤ 32
      omega
    have hdb := a1_diff_bounds (k0 := k0N a row) (k2 := k2) hle hA4
    have hR := a1_k2diff32 (k0 := k0N a row) (k2 := k2) (dk := u8 a.sp 4 + 1)
      (N := nmOf (k2 - k0N a row) (u8 a.sp 4)) hk0n.2 hk2 (by omega) h48
    generalize hNdef : nmOf (k2 - k0N a row) (u8 a.sp 4) = N at *
    have hR' : _ = BitVec.ofInt 32 (diffOf (k0N a row) k2 N (u8 a.sp 4 + 1)) := hR
    clear hR
    generalize hD : diffOf (k0N a row) k2 N (u8 a.sp 4 + 1) = D at *
    have hmsb := a1_d_msb hdb.2.1 hdb.1
    have hz := a1_d_zero hdb.2.1 hdb.1
    have ha := a1_fm_addr (t₀.regs.get64 .rsi) (j := N) h48
    have hld := a1_fmi_load hm hfm (i := N) h48 ha
    have hst := a1_fmi_store hm hfm (i := N) h48 ha
    have hu : u16 st.fm N = u8 a.sp 4 + 1 := hfil N (by omega) (by omega)
    simp only [B.L1ec1]
    vcgen
    all_goals try subst s₀
    all_goals try subst n
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hdx, hax, hcx,
      hsi, h13, AddrIndex.offset64_none, AddrIndex.offset64_scale2, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, hR']
    · rename_i g1
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hdx, hax, hcx, hsi, h13, hR',
        CondCode.interp_s, StatusFlags.sf_from_result, hmsb, decide_eq_true_eq] at g1
      subst hD; subst hNdef
      refine Or.inl (Table.ofLabels_at ⟨S.L1ed8, T.L1ed8.mpr ⟨row, k2, hr, hk2, hle, hq, h3,
        ⟨hC, hBO, ⟨?_, ?_⟩, st, fr, hx, hsp, hfm, hF, ⟨hk2s, ⟨h2, hxo, hnm, ?_⟩, ?_, ?_, g1, ?_, hfil⟩,
        hm⟩, ?_, ?_⟩, by edge_step⟩)
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15, hdx,
        hcx, h13]
      all_goals first
        | done
    · rename_i g1 g2
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hdx, hax, hcx, hsi, h13, hR',
        CondCode.interp_s, StatusFlags.sf_from_result, hmsb, a1_cc_z, hz, decide_eq_true_eq,
        decide_eq_false_iff_not, Bool.not_eq_true', Bool.not_eq_false'] at g1 g2
      subst g2
      subst hNdef
      refine Or.inl (Table.ofLabels_at ⟨S.L1f08, T.L1f08.mpr ⟨row, k2, hr, hk2, hle, hq, h3,
        ⟨hC, hBO, ⟨?_, ?_⟩, st, fr, hx, hsp, hfm, hF, ⟨hk2s, ⟨h2, hxo, hnm, ?_⟩, ?_, ?_, ?_⟩,
        hm⟩, ?_, ?_⟩, by edge_step⟩)
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15, hdx,
        hcx, h13]
      all_goals first
        | done
        | (simp only [diffOf, k0N, k0A, srI, u8]; rw [hD]; exact a1_stepped0 hfil)
    · rw [hld]; rfl
    · rename_i g1 g2 mv hv
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hdx, hax, hcx, hsi, h13, hR',
        CondCode.interp_s, StatusFlags.sf_from_result, hmsb, a1_cc_z, hz, decide_eq_true_eq,
        decide_eq_false_iff_not, Bool.not_eq_true', Bool.not_eq_false'] at g1 g2
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, hdx, AddrIndex.offset64_scale2,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat] at hv
      rw [hld] at hv; obtain rfl := Option.some.inj hv
      have hD1 : D = 1 := by omega
      subst hD1
      rw [hu] at *
      rw [a1_inc16 (by (try simp only [u8] at hA4); omega)]
      have hfm' : (wr st.fm (2 * N) (Int.toBytes 2 (((u8 a.sp 4 + 1 : Nat) : Int) + 1))).length = 98 := by
        rw [wr_length (by rw [Int.toBytes_length, hfm]; omega), hfm]
      subst hNdef
      refine Or.inl (Table.ofLabels_at ⟨S.L1f08, T.L1f08.mpr ⟨row, k2, hr, hk2, hle, hq, h3,
        ⟨hC, hBO, ⟨?_, ?_⟩, ({ st with fm := wr st.fm (2 * nmOf (k2 - k0N a row) (u8 a.sp 4)) (Int.toBytes 2 (((u8 a.sp 4 + 1 : Nat) : Int) + 1)) } : St), fr, hx, hsp, hfm', hF, ⟨hk2s, ⟨h2, hxo, hnm, ?_⟩, ?_, ?_, ?_⟩,
        ?_⟩, ?_, ?_⟩, by edge_step⟩)
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15, hdx,
        hcx, h13]
      all_goals first
        | done
        | (simp only [diffOf, k0N, k0A, srI, u8]; rw [hD]; exact a1_stepped1 hfm h48 (by omega) hfil (by (try simp only [u8] at hA4); omega))
        | exact hst _
        | (with_reducible exact hst _)

end Kraken.Examples.Sbr.Reset
