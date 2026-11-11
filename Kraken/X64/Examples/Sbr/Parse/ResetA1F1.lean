import Kraken.InfoOff
import Kraken.X64.Examples.Sbr.Parse.ResetA1F0
import Kraken.X64.Examples.Sbr.Parse.ResetA1Inc

/-!
# `sbr_reset`: `bs_freq_scale = 0`, the `k2diff` fixups and prefix sums (shard A1)
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
theorem a1_mask12 : ∀ n, n < 49 → n % 2 = 0 →
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32
      (BitVec.ofNat 64 n + BitVec.ofNat 64 n))) &&& BitVec.setWidth 32 12#64)
      = BitVec.ofNat 64 (2 * (n % 8)) := by
  decide

omit [CodeEnv] in
theorem a1_rax_addr (b : BitVec 64) (j : Nat) :
    BitVec.setWidth 64 311792#64 + (b + BitVec.ofNat 64 (j + 1) * 2#64)
      = b + BitVec.ofNat 64 (0x4c1f0 + 2 * (j + 1)) := by
  have e : BitVec.ofNat 64 (0x4c1f0 + 2 * (j + 1)) = 311792#64 + BitVec.ofNat 64 (j + 1) * 2#64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
    omega
  rw [e, show BitVec.setWidth 64 311792#64 = 311792#64 from rfl]
  ac_rfl

omit [CodeEnv] in
/-- `f_master[i]` after the prefix sums, in closed form. -/
theorem a1_fv_eq (k0 dk nm : Nat) (diff : Int) : ∀ i, fvOf k0 dk nm diff i
    = (k0 : Int) + i * dk - (if diff < 0 ∧ 1 ≤ i then 1 else 0) - (if diff < -1 ∧ 2 ≤ i then 1 else 0)
      + (if 0 < diff ∧ 1 ≤ nm ∧ nm ≤ i then 1 else 0)
  | 0 => by
    simp [fvOf]
    split <;> omega
  | i + 1 => by
    rw [fvOf, a1_fv_eq k0 dk nm diff i, stepOf, Int.natCast_add, Int.natCast_one, Int.add_mul, Int.one_mul]
    repeat' split
    all_goals omega

omit [CodeEnv] in
theorem a1_fv_range {k0 dk nm : Nat} {diff : Int} (h0 : 1 ≤ k0) (h0' : k0 ≤ 32) (hd : 1 ≤ dk)
    (hd' : dk ≤ 2) {i : Nat} (hi : i ≤ 48) :
    0 ≤ fvOf k0 dk nm diff i ∧ fvOf k0 dk nm diff i < 32768 := by
  rw [a1_fv_eq]
  have : (i : Int) * dk ≤ 96 := by
    have := Int.mul_le_mul (show (i : Int) ≤ 48 by omega) (show (dk : Int) ≤ 2 by omega) (by omega) (by omega)
    omega
  have : (0 : Int) ≤ i * dk := Int.mul_nonneg (by omega) (by omega)
  have : (i : Int) ≤ i * dk := by
    have := Int.mul_le_mul (show (i : Int) ≤ i by omega) (show (1 : Int) ≤ dk by omega) (by omega) (by omega)
    omega
  repeat' split
  all_goals omega

omit [CodeEnv] in
theorem a1_u16_wr_int {l : List UInt8} {j : Nat} {v : Int} (h : 2 * j + 2 ≤ l.length) (h0 : 0 ≤ v)
    (hv : v < 65536) : (u16 (wr l (2 * j) (Int.toBytes 2 v)) j : Int) = v := by
  have hb : (Int.toBytes 2 v).length = 2 := Int.toBytes_length ..
  have h1 := a1_ofBytes_slice2 (wr l (2 * j) (Int.toBytes 2 v)) j (by rw [wr_length (by omega)]; omega)
  have h2 := slice_wr_same (l := l) (o := 2 * j) (v := Int.toBytes 2 v) (by omega)
  rw [hb] at h2
  rw [h2, Int.ofBytes_toBytes_of_lt 2 v h0 (by simp only [Nat.reduceMul]; omega)] at h1
  omega

omit [CodeEnv] in
theorem a1_toInt16 {x : Int} (h0 : 0 ≤ x) (h1 : x < 32768) : (BitVec.ofInt 16 x).toInt = x := by
  rw [BitVec.toInt_ofInt]
  simp only [Int.bmod]
  split <;> omega

section FMI

variable {k : Nat} {e : REnv} {a : RArgs} {ra : Int64} {t₀ : MachineData} {st : St}
  {fr : List UInt8} {m : Mem 64}

theorem a1_fmi_load (hm : m =⋆ Mm k e a ra t₀ st fr) (hl : st.fm.length = 98) {i : Nat} (hi : i ≤ 48)
    {addr : BitVec 64} (ha : addr = arg1 t₀ + 0x4c1f0#64 + BitVec.ofNat 64 (2 * i)) :
    m.loadInt addr 2 = some (u16 st.fm i : Int) := by
  rw [region_load (focus (Mm_fm ..) hm) (o := 2 * i) (n := 2) ha (by omega) (by omega),
    a1_ofBytes_slice2 _ _ (by omega)]

theorem a1_fmi_store (hm : m =⋆ Mm k e a ra t₀ st fr) (hl : st.fm.length = 98) {i : Nat} (hi : i ≤ 48)
    {addr : BitVec 64} (ha : addr = arg1 t₀ + 0x4c1f0#64 + BitVec.ofNat 64 (2 * i)) (v : Int) :
    m.storeInt addr 2 v =⋆ Mm k e a ra t₀ { st with fm := wr st.fm (2 * i) (Int.toBytes 2 v) } fr :=
  Mm_upd_fm .. ▸ region_store (focus (Mm_fm ..) hm) (o := 2 * i) ha (by omega) (by omega) v

end FMI

omit [CodeEnv] in
theorem a1_summed_idx {l : List UInt8} {k0 dk nm : Nat} {diff : Int} {a b : Nat} (h : a = b)
    (hs : Summed l k0 dk nm diff a) : Summed l k0 dk nm diff b := h ▸ hs

omit [CodeEnv] in
/-- `Summed` one step further: `f_master[j + 1]` replaced by the prefix sum. -/
theorem a1_summed_step {l : List UInt8} (hl : l.length = 98) {k0 dk nm : Nat} {diff : Int} {j : Nat}
    (hj : j + 1 ≤ nm) (hnm : nm ≤ 48) (hs : Summed l k0 dk nm diff j)
    (h0 : 0 ≤ fvOf k0 dk nm diff (j + 1)) (h1 : fvOf k0 dk nm diff (j + 1) < 65536) :
    Summed (wr l (2 * (j + 1)) (Int.toBytes 2 (fvOf k0 dk nm diff (j + 1)))) k0 dk nm diff (j + 1) := by
  have hb : (Int.toBytes 2 (fvOf k0 dk nm diff (j + 1))).length = 2 := Int.toBytes_length ..
  constructor
  · intro i hi
    rcases (show i ≤ j ∨ i = j + 1 by omega) with h | rfl
    · rw [a1_u16_wr_ne (by omega) (by omega)]; exact hs.1 i h
    · exact a1_u16_wr_int (by omega) h0 h1
  · intro i h1 h2
    rw [a1_u16_wr_ne (by omega) (by omega)]
    exact hs.2 i (by omega) h2

theorem blk_L1fd5 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1fd5" ⟨"sbr_reset.L1fd5", B.L1fd5, some "sbr_reset.L1ff0"⟩ := by
  info_off
  measure_hb "L1fd5"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hr, hk2, hle, hq, h3, ⟨hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2s, ⟨h2, hxo, hnm, hdx⟩, j, hax, hj8, hjn, hnj, hsum, h13⟩, hm⟩, h12, h15⟩ :=
      T.L1fd5.mp hs
    clear hs
    have h48 := f0_nm_48 hr hC.2.1 hq
    generalize hNdef : nmOf (k2 - k0N a row) (u8 a.sp 4) = N at *
    have hev : N % 2 = 0 := by rw [← hNdef]; unfold nmOf; split <;> omega
    have hmask := a1_mask12 N (by omega) hev
    rw [show N % 8 = N - j by omega] at hmask
    simp only [B.L1fd5]
    vcgen
    all_goals try subst s₀
    all_goals try subst n
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hdx, hax,
      AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2,
      Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    subst hNdef
    refine ⟨T.L1ff0.mpr ⟨row, k2, hr, hk2, hle, hq, h3, ⟨hC, hBO, ⟨?_, ?_⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2s, h2, hxo, hnm, j, 0, ?_, hj8, hjn, hnj, ?_, ?_, ?_, hsum, ?_⟩, hm⟩, ?_, ?_⟩, by var_step⟩
    all_goals try simp only [k0N, k0A, u8, srI]
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    all_goals first
      | (simp only [hrsp, hrbp, h12, h15, h13]; done)
      | omega
      | (simp only [BitVec.xor_self, BitVec.setWidth_zero, BitVec.reduceSetWidth]; done)
      | exact a1_rax_addr _ _
      | (simp only [arg1]; bv_omega)
      | exact hmask
      | exact h13

theorem blk_L1ff0 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1ff0" ⟨"sbr_reset.L1ff0", B.L1ff0, some "sbr_reset.L2003"⟩ := by
  info_off
  measure_hb "L1ff0"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hr, hk2, hle, hq, h3, ⟨hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2s, h2, hxo, hnm, j, i, hax, hj8, hjn, hnj, hij, hcx, hdx, hsum, h13⟩, hm⟩, h12, h15⟩ :=
      T.L1ff0.mp hs
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
    have haddr : t₀.regs.get64 .rsi + 0x4c1f0#64 + BitVec.ofNat 64 (2 * (j + i + 1))
        = t₀.regs.get64 .rsi + BitVec.ofNat 64 (311792 + 2 * (j + 1)) + BitVec.ofNat 64 (2 * i) := by
      bv_omega
    have hld := a1_fmi_load hm hfm (i := j + i + 1) (by omega) haddr.symm
    have hst := a1_fmi_store hm hfm (i := j + i + 1) (by omega) haddr.symm
    have hstep := hsum.2 (j + i + 1) (by omega) (by omega)
    have hrng := a1_fv_range (nm := N) (diff := D) (k0 := k0N a row) (dk := u8 a.sp 4 + 1)
      hk0n.1 hk0n.2 (by omega) (by simp only [u8] at hA4 ⊢; omega) (i := j + i + 1) (by omega)
    have hnew : BitVec.ofInt 16 (u16 st.fm (j + i + 1) : Int)
        + BitVec.ofInt 16 (fvOf (k0N a row) (u8 a.sp 4 + 1) N D (j + i))
        = BitVec.ofInt 16 (fvOf (k0N a row) (u8 a.sp 4 + 1) N D (j + i + 1)) := by
      rw [hstep, ← BitVec.ofInt_add, fvOf, Int.add_comm]
    have hsum' := a1_summed_step hfm (j := j + i) (by omega) h48 hsum hrng.1 (by omega)
    have hv16 := a1_toInt16 hrng.1 hrng.2
    have hrdx : BitVec.setWidth 64 2#64 + BitVec.ofNat 64 (2 * i) = BitVec.ofNat 64 (2 * (i + 1)) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      omega
    have hrdx' : BitVec.setWidth 64 (Int64.toBitVec 2) + BitVec.ofNat 64 (2 * i)
        = BitVec.ofNat 64 (2 * (i + 1)) := hrdx
    simp only [B.L1ff0]
    vcgen
    all_goals try subst s₀
    all_goals try subst n
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hdx, hax, hcx,
      AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2,
      Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    · rw [hld]; rfl
    · rw [hld]; rfl
    · rename_i mv hv g1
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hdx, hax,
        AddrIndex.offset64_none, AddrIndex.offset64_scale1, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero] at hv
      rw [hld] at hv
      obtain rfl := Option.some.inj hv
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hcx, hdx, hrdx, hrdx', cc_nz_sub, Bool.not_eq_true', Bool.not_eq_false',
        decide_eq_true_eq, cc_z_sub, decide_eq_false_iff_not, Bool.not_eq_true, Bool.not_eq_false] at g1
      have hne : i + 1 ≠ N - j := by
        intro h; apply g1; rw [h]
      subst hD; subst hNdef
      refine Or.inl (Table.ofLabels_at ⟨S.L1ff0, T.L1ff0.mpr ⟨row, k2, hr, hk2, hle, hq, h3,
        ⟨hC, hBO, ⟨?_, ?_⟩, { st with fm := wr st.fm (2 * (j + i + 1)) (Int.toBytes 2 (fvOf (k0N a row) (u8 a.sp 4 + 1) (nmOf (k2 - k0N a row) (u8 a.sp 4)) (diffOf (k0N a row) k2 (nmOf (k2 - k0N a row) (u8 a.sp 4)) (u8 a.sp 4 + 1)) (j + i + 1))) }, fr, hx, hsp, ?_, hF,
        ⟨hk2s, h2, hxo, hnm, j, i + 1, ?_, hj8, hjn, hnj, ?_, ?_, ?_, hsum', ?_⟩, ?_⟩, ?_, ?_⟩, ?_⟩)
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, BitVec.setWidth_replaceLow16,
        h13, hnew, hv16, hrdx, hdx, hax, hcx, AddrIndex.offset64_scale1, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero]
      all_goals try simp only [k0N, k0A, u8, srI]
      all_goals first
        | (simp only [hrsp, hrbp, h12, h15]; done)
        | (with_reducible rfl)
        | omega
        | (with_reducible exact hst _)
        | (show (wr _ _ _).length = 98
           rw [wr_length (by rw [Int.toBytes_length, hfm]; omega), hfm])
        | (left
           simp only [lex_var, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hdx, hrdx,
             BitVec.toNat_ofNat]
           refine Kraken.lex_cons_lt_cons (by lex_len) ?_
           refine Kraken.lex_cons_lt_of_lt (by lex_len) ?_
           simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hdx, hrdx, BitVec.toNat_ofNat]
           lex_digit)
        | exact rfl

    · rename_i mv hv g1
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hdx, hax,
        AddrIndex.offset64_none, AddrIndex.offset64_scale1, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero] at hv
      rw [hld] at hv
      obtain rfl := Option.some.inj hv
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hcx, hdx, hrdx, hrdx', cc_nz_sub, Bool.not_eq_true', Bool.not_eq_false',
        decide_eq_true_eq, cc_z_sub, decide_eq_false_iff_not, Bool.not_eq_true, Bool.not_eq_false] at g1
      have heq : i + 1 = N - j := by
        have := congrArg BitVec.toNat g1
        simp only [BitVec.toNat_ofNat] at this
        omega
      subst hD; subst hNdef
      refine ⟨T.L2003.mpr ⟨row, k2, hr, hk2, hle, hq, h3,
        ⟨hC, hBO, ⟨?_, ?_⟩, { st with fm := wr st.fm (2 * (j + i + 1)) (Int.toBytes 2 (fvOf (k0N a row) (u8 a.sp 4 + 1) (nmOf (k2 - k0N a row) (u8 a.sp 4)) (diffOf (k0N a row) k2 (nmOf (k2 - k0N a row) (u8 a.sp 4)) (u8 a.sp 4 + 1)) (j + i + 1))) }, fr, hx, hsp, ?_, hF,
        ⟨hk2s, h2, hxo, hnm, a1_summed_idx (by have := heq; simp only [k0N, k0A, u8, srI] at this ⊢; omega) hsum'⟩, ?_⟩, ?_, ?_⟩, by var_step⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, BitVec.setWidth_replaceLow16,
        h13, hnew, hv16, hrdx, hdx, hax, hcx, AddrIndex.offset64_scale1, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero]
      all_goals try simp only [k0N, k0A, u8, srI]
      all_goals first
        | (simp only [hrsp, hrbp, h12, h15]; done)
        | (with_reducible rfl)
        | omega
        | (with_reducible exact hst _)
        | (show (wr _ _ _).length = 98
           rw [wr_length (by rw [Int.toBytes_length, hfm]; omega), hfm])
        | (left
           simp only [lex_var, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hdx, hrdx,
             BitVec.toNat_ofNat]
           refine Kraken.lex_cons_lt_cons (by lex_len) ?_
           refine Kraken.lex_cons_lt_of_lt (by lex_len) ?_
           simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hdx, hrdx, BitVec.toNat_ofNat]
           lex_digit)
        | exact rfl


end Kraken.Examples.Sbr.Reset
