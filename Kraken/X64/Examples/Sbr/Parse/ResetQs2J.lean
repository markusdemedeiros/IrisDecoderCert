import Kraken.X64.Examples.Sbr.Parse.ResetQs2Lib3
import Kraken.X64.Examples.Sbr.Parse.ResetA2Blk
import Kraken.X64.Examples.Sbr.Parse.ResetA2Mc

/-!
# `sbr_reset`, `AV_QSORT` copy 2 (`vk0`): two elements, and the entry (`L1ba0`, `L194b`)
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse Kraken.Examples.Sbr.Parse.Qsort

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Reset

variable [CodeEnv]

theorem blk_L1ba0 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1ba0" ⟨"sbr_reset.L1ba0", B.L1ba0,
      some "sbr_reset.L1bbd"⟩ := by
  info_off
  measure_hb "L1ba0"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    subst hn
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hSF, hN0, h12, h15, hax, ⟨hN1, hN49, S, A0, lo, hi1, hcx, hD, hDc, hR, hSR, hQ,
        hsi, hdx, h2⟩⟩, hm⟩⟩ := T.L1ba0.mp hs
    clear hs
    have hsi' : s₀.regs.get64 .rsi = QS.ep t₀ 0x400 lo := hsi
    have hdx' : s₀.regs.get64 .rdx = QS.ep t₀ 0x400 hi1 - 2#64 := hdx
    clear hsi hdx
    subst h2
    have hdx2 : s₀.regs.get64 .rdx = QS.ep t₀ 0x400 (lo + 1) := by
      rw [hdx', ep_sub2 _ _ _ (by omega)]; rfl
    have hW := qw_cur hQ
    simp only at hW
    have hrs := rsp_ok hC
    simp only [resetStkMin] at hrs
    have hR' : 0x578 ≤ (t₀.regs.get64 .rsp).toNat := by omega
    have hS6 : S.length ≤ 6 := depth_len (m := 6) hD (by omega)
    have hph := stkPhi_eq hm hF hrbp hR' (o := 0x400) (by omega) hSR
      (fun J hJ => hQ.1 J (by simp [hJ])) (by omega)
    have hpl := phi_le (S := S) (fun J hJ => hQ.1 J (by simp [hJ]))
    have hpl' : phi S ≤ 6 * 99 := Nat.le_trans hpl (Nat.mul_le_mul hS6 (by omega))
    have hwB := ep_wB hR' (o := 0x400) hW.1 (by omega)
    have hΦ : QS.stkPhi s₀ (s₀.regs.get64 .rcx).toNat
        + wBn 2 (s₀.regs.get64 .rsi).toNat (s₀.regs.get64 .rdx).toNat
        = phi S + (2 * (lo + 2 - lo) + 1) := by
      rw [hcx, hsi', hdx', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hph, hwB]; rfl
    have hl0 := av_load hm hF (o := 0x400) (q := lo) (by omega)
    have hl1 := av_load hm hF (o := 0x400) (q := lo + 1) (by omega)
    have hl2g : ∀ v : Int, loadInt (storeInt s₀.dmem (QS.ep t₀ 0x400 (lo + 1)) 2 v)
        (QS.ep t₀ 0x400 lo) 2 = some (Int.ofBytes (slice (wr fr
          (0x400 + 2 * (lo + 1 + 1)) (Int.toBytes 2 v)) (0x400 + 2 * (lo + 1)) 2)) := fun v =>
      av_load (av_store hm hF (by omega) v)
        (fr_wr_len hF (o := 0x400 + 2 * (lo + 1 + 1)) (n := 2) (by omega) v) (by omega)
    -- the exchange of `lo` and `lo + 1`
    have tL := av_toInt fr 0x400 lo
    have tP := av_toInt fr 0x400 (lo + 1)
    have ho1 : 0x400 + 2 * (lo + 1 + 1) + 2 ≤ 0x470 := by omega
    have ho2 : 0x400 + 2 * (lo + 1) + 2 ≤ 0x470 := by omega
    have hm1 := av_store hm hF (o := 0x400) (q := lo + 1) (by omega)
      (BitVec.ofInt 16 (QS.av fr 0x400 lo)).toInt
    have hF1 := fr_wr_len hF (o := 0x400 + 2 * (lo + 1 + 1)) (n := 2) (by omega)
      (BitVec.ofInt 16 (QS.av fr 0x400 lo)).toInt
    have hm2 := av_store hm1 hF1 (o := 0x400) (q := lo) (by omega)
      (BitVec.ofInt 16 (QS.av fr 0x400 (lo + 1))).toInt
    have hF2 := fr_wr_len hF1 (o := 0x400 + 2 * (lo + 1)) (n := 2) (by omega)
      (BitVec.ofInt 16 (QS.av fr 0x400 (lo + 1))).toInt
    have hSF2 := (sf_wr hF1 ho2 (BitVec.ofInt 16 (QS.av fr 0x400 (lo + 1))).toInt).mpr
      ((sf_wr hF ho1 (BitVec.ofInt 16 (QS.av fr 0x400 lo)).toInt).mpr hSF)
    have hSR2 := (stk_wr hF1 (o' := 0x400 + 2 * (lo + 1)) (n := 2) (by omega)
      (BitVec.ofInt 16 (QS.av fr 0x400 (lo + 1))).toInt (t₀ := t₀) (o := 0x400)
      (S := S) (by omega) (by omega)).mpr ((stk_wr hF (o' := 0x400 + 2 * (lo + 1 + 1)) (n := 2)
      (by omega) (BitVec.ofInt 16 (QS.av fr 0x400 lo)).toInt (t₀ := t₀)
      (o := 0x400) (S := S) (by omega) (by omega)).mpr hSR)
    have hAv2 : ∀ r, QS.av (wr (wr fr (0x400 + 2 * (lo + 1 + 1))
        (Int.toBytes 2 (BitVec.ofInt 16 (QS.av fr 0x400 lo)).toInt))
        (0x400 + 2 * (lo + 1))
        (Int.toBytes 2 (BitVec.ofInt 16 (QS.av fr 0x400 (lo + 1))).toInt)) 0x400 r
        = swap (QS.av fr 0x400) lo (lo + 1) r := fun r => by
      rw [av_wr hF1 (by omega) _ r, tP, ← upd_upd_swap]
      simp only [Parse.Qsort.upd]
      rw [av_wr hF (o := 0x400) (q := lo + 1) (by omega) _ r, tL]
      rfl
    have hQ2 := (qw_swap hQ (i := lo) (j := lo + 1) (by simp only [InIv]; omega)
      (by simp only [InIv]; omega))
    have hQ2' := And.intro hQ2.1 (hQ2.2.congr hAv2)
    generalize hf2 : wr (wr fr (0x400 + 2 * (lo + 1 + 1))
        (Int.toBytes 2 (BitVec.ofInt 16 (QS.av fr 0x400 lo)).toInt))
        (0x400 + 2 * (lo + 1))
        (Int.toBytes 2 (BitVec.ofInt 16 (QS.av fr 0x400 (lo + 1))).toInt) = fr2
      at hm2 hF2 hSF2 hSR2 hAv2 hQ2'
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L1ba0]
    vcgen
    all_goals subst s₀
    all_goals subst hP
    all_goals try simp only [hsi', hdx2, AddrIndex.offset64_none,
      BitVec.add_zero, Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm,
      Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, BitVec.ofNat_eq_ofNat]
    all_goals first | (rw [hl0]; rfl) | (rw [hl1]; rfl) | (rw [hl2g]; rfl) | skip
    · -- `A lo ≤ A (lo + 1)`: pop
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L1980.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩,
        st, fr, hx, hsp, hfm, hF, ⟨hk2v, hk1v, hSF, hN0, ?_, ?_, ?_,
          ⟨hN1, hN49, S, A0, ?_, hD, hR, hSR, qw_drop hQ⟩⟩, hm⟩⟩, Or.inl ?_⟩
      all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrsp, hrbp, h12,
        h15, hax, hcx]; done)
      simp only [lex_var, VD.L1980, VD.L1ba0, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      rw [hΦ]
      refine lex_head_lt ?_ (by omega)
      rw [stkPhi_mk _ _ _ _ (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]), hcx,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := S.length) (by omega), hph]
      omega
    · -- exchange, then pop
      rename_i v1 h1 v2 h2 _
      try simp only [hsi', hdx2, AddrIndex.offset64_none, BitVec.add_zero,
        Int64.toBitVec_ofNat_norm, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte,
        BitVec.ofNat_eq_ofNat] at h1 h2
      rw [hl0, Option.some.injEq] at h1
      rw [hl1, Option.some.injEq] at h2
      subst h1 h2
      rw [sw16_zx, sw16_zx, av_bytes fr 0x400 lo, av_bytes fr 0x400 (lo + 1)]
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L1980.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩,
        st, _, hx, hsp, hfm, hF2, ⟨hk2v, hk1v, hSF2, hN0, ?_, ?_, ?_,
          ⟨hN1, hN49, S, A0, ?_, hD, hR, hSR2, qw_drop hQ2'⟩⟩, hm2⟩⟩, Or.inl ?_⟩
      all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrsp, hrbp, h12,
        h15, hax, hcx]; done)
      simp only [lex_var, VD.L1980, VD.L1ba0, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      rw [hΦ]
      refine lex_head_lt ?_ (by omega)
      rw [hcx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := S.length) (by omega), stkPhi_lit hm2 hF2
        (by (try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]); exact hrbp) hR'
        (by omega) hSR2 (fun J hJ => hQ.1 J (by simp [hJ])) (by omega)]
      omega

omit [CodeEnv] in
/-- The `make_bands` output as the initial array (for `QS.Cur`'s range and sum). -/
theorem ab_of_arr {fr : List UInt8} {o N : Nat} {B tot : Int} (h : A2.Arr fr o N B tot) :
    QS.AB N (QS.av fr o) B tot := by
  obtain ⟨A, hA, hs⟩ := h
  have key : ∀ n, n ≤ N → A2.ssum (A2.fv fr o) n = A2.ssum A n := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      rw [A2.ssum, A2.ssum, ih (by omega), (hA (n + 1) (by omega) hn).1]
  refine ⟨fun q hq => ?_, ?_⟩
  · obtain ⟨e1, h1, h2⟩ := hA (q + 1) (by omega) (by omega)
    simp only [QS.av]
    rw [e1]
    exact ⟨h1, h2⟩
  · rw [← ssum_av, key N (Nat.le_refl _), hs]

theorem blk_L194b (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L194b" ⟨"sbr_reset.L194b", B.L194b,
      some "sbr_reset.L1980"⟩ := by
  info_off
  measure_hb "L194b"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    subst hn
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hSF, hN0, hax, hsi, hMB⟩, hm⟩⟩ := T.L194b.mp hs
    clear hs
    have hrs := rsp_ok hC
    simp only [resetStkMin] at hrs
    have hR' : 0x578 ≤ (t₀.regs.get64 .rsp).toNat := by omega
    have hsi' : s₀.regs.get64 .rsi = s₀.regs.get64 .rbp - 366#64 := hsi
    clear hsi
    have hN1 : 1 ≤ A2.n0N e a (k0N a row) k2 := by
      show 1 ≤ (A2.n0I e a (k0N a row) k2).toNat
      have := hN0.1; omega
    have hN49 : A2.n0N e a (k0N a row) k2 ≤ 48 := by
      show (A2.n0I e a (k0N a row) k2).toNat ≤ 48
      have := hN0.2.1; omega
    -- the initial array
    have hArr : A2.Arr fr 0x400 (A2.n0N e a (k0N a row) k2) 64
        (((A2.k1Of (k0N a row) k2 : Nat) : Int) - ((k0N a row : Nat) : Int)) := by
      have hb := ((a2_bands_of hB hC hrow hk2 hk02 hkq hu).1 hN0.1).2
      refine a2_mb_arr hb (by omega) ?_ hN1 hMB (by omega)
      unfold A2.k1Of; split <;> omega
    -- addresses
    have e0 : s₀.regs.get64 .rbp + 18446744073709550224#64
        = t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 0 := by rw [hrbp]; bv_omega
    have e8 : s₀.regs.get64 .rbp + 18446744073709550232#64
        = t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 8 := by rw [hrbp]; bv_omega
    have e48 : s₀.regs.get64 .rbp + 18446744073709551544#64
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x48 := by rw [hrbp]; bv_omega
    have e30 : s₀.regs.get64 .rbp + 18446744073709551568#64
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x30 := by rw [hrbp]; bv_omega
    have e40 : s₀.regs.get64 .rbp + 18446744073709551552#64
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x40 := by rw [hrbp]; bv_omega
    have ep0 : s₀.regs.get64 .rbp - 366#64 = QS.ep t₀ 0x400 0 := by
      rw [hrbp]; simp only [QS.ep]; bv_omega
    -- the stores and loads
    have hl0 := stk_load hm hF (o := 0) (by omega) e0
    have hm1 := stk_store hm hF (o := 0) (by omega) e0 (s₀.regs.get64 .rbp - 366#64).toInt
    have hF1 := fr_wr_len hF (o := 0) (n := 8) (by omega) (s₀.regs.get64 .rbp - 366#64).toInt
    have hSF1 := (sf_wr hF (o := 0) (n := 8) (by omega)
      (s₀.regs.get64 .rbp - 366#64).toInt).mpr hSF
    have hl48 := fr_load hm1 hF1 (d := 0x48) (n := 4) (by omega) (by omega)
    have hl8 := stk_load hm1 hF1 (o := 8) (by omega) e8
    have hl30g := fun v => fr_load (stk_store hm1 hF1 (o := 8) (by omega) e8 v)
      (fr_wr_len hF1 (o := 8) (n := 8) (by omega) v) (d := 0x30) (n := 8) (by omega) (by omega)
    have hl40g := fun v => fr_load (stk_store hm1 hF1 (o := 8) (by omega) e8 v)
      (fr_wr_len hF1 (o := 8) (n := 8) (by omega) v) (d := 0x40) (n := 8) (by omega) (by omega)
    have hrax : BitVec.setWidth 64 (BitVec.ofInt 32 (Int.ofBytes (slice (wr fr 0
        (Int.toBytes 8 (s₀.regs.get64 .rbp - 366#64).toInt)) (rb 0x48) 4)))
        = BitVec.ofNat 64 (A2.n0N e a (k0N a row) k2) := by
      rw [← a2_lo32_slice8 _ (rb 0x48) (by rw [hF1]; decide)]
      have h48 := hSF1.2
      simp only [frSlot64] at h48
      rw [h48, a2_setWidth32_ofNat64]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      omega
    have hv2 : BitVec.setWidth 64 18446744073709551614#64 + (s₀.regs.get64 .rbp - 366#64
        + BitVec.ofNat 64 (A2.n0N e a (k0N a row) k2) * 2#64)
        = QS.ep t₀ 0x400 (A2.n0N e a (k0N a row) k2) - 2#64 := by
      rw [hrbp]; simp only [QS.ep, BitVec.setWidth_eq]; bv_omega
    have hm2 := stk_store hm1 hF1 (o := 8) (by omega) e8
      (QS.ep t₀ 0x400 (A2.n0N e a (k0N a row) k2) - 2#64).toInt
    have hF2 := fr_wr_len hF1 (o := 8) (n := 8) (by omega)
      (QS.ep t₀ 0x400 (A2.n0N e a (k0N a row) k2) - 2#64).toInt
    have hSF2 := (sf_wr hF1 (o := 8) (n := 8) (by omega)
      (QS.ep t₀ 0x400 (A2.n0N e a (k0N a row) k2) - 2#64).toInt).mpr hSF1
    have hSR : QS.StkRel (wr (wr fr 0 (Int.toBytes 8 (s₀.regs.get64 .rbp - 366#64).toInt)) 8
        (Int.toBytes 8 (QS.ep t₀ 0x400 (A2.n0N e a (k0N a row) k2) - 2#64).toInt)) t₀ 0x400
        [(0, A2.n0N e a (k0N a row) k2)] := by
      refine stkRel_push (S := []) (fun j h => absurd h (by simp)) ?_ ?_
      · rw [slot_wr64 hF1 (by omega) _ (by simp only [rb, List.length_nil] <;> omega),
          slot_wr_same hF (by omega) (by simp only [rb, List.length_nil] <;> omega),
          BitVec.ofInt_toInt, ep0]
      · rw [slot_wr_same hF1 (by omega) (by simp only [rb, List.length_nil] <;> omega),
          BitVec.ofInt_toInt]
    have hAv : QS.av (wr (wr fr 0 (Int.toBytes 8 (s₀.regs.get64 .rbp - 366#64).toInt)) 8
        (Int.toBytes 8 (QS.ep t₀ 0x400 (A2.n0N e a (k0N a row) k2) - 2#64).toInt)) 0x400
        = QS.av fr 0x400 := funext fun r => by
      rw [av_wr_other hF1 (by omega) _ (by omega), av_wr_other hF (by omega) _ (by omega)]
    have hR : QS.AB (A2.n0N e a (k0N a row) k2) (QS.av (wr (wr fr 0
        (Int.toBytes 8 (s₀.regs.get64 .rbp - 366#64).toInt)) 8
        (Int.toBytes 8 (QS.ep t₀ 0x400 (A2.n0N e a (k0N a row) k2) - 2#64).toInt)) 0x400) 64
        (((A2.k1Of (k0N a row) k2 : Nat) : Int) - ((k0N a row : Nat) : Int)) := by
      rw [hAv]; exact ab_of_arr hArr
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L194b]
    vcgen
    all_goals subst s₀
    all_goals subst hP
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceMod,
        Nat.reducePow, Nat.reduceSub, hsi', e48, e30, e40]
    all_goals first | (rw [hl0]; rfl) | (rw [hl48]; rfl) | (rw [hl8]; rfl) | skip
    · rename_i v48 h48
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
        AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceMod, Nat.reducePow, Nat.reduceSub,
        hsi', e48, e30, e40] at h48
      rw [hl48, Option.some.injEq] at h48
      subst h48
      rw [hrax, hv2, hl30g]; rfl
    · rename_i v48 h48 _ _
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
        AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceMod, Nat.reducePow, Nat.reduceSub,
        hsi', e48, e30, e40] at h48
      rw [hl48, Option.some.injEq] at h48
      subst h48
      rw [hrax, hv2, hl40g]; rfl
    rename_i v48 h48 v30 h30 v40 h40
    simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceMod, Nat.reducePow, Nat.reduceSub,
      AddrIndex.offset64_scale2, AddrIndex.offset64_scale1, hsi', e48, e30, e40] at h48 h30 h40
    rw [hl48, Option.some.injEq] at h48
    subst h48
    rw [hrax, hv2] at h30 h40 ⊢
    rw [hl30g, Option.some.injEq] at h30
    rw [hl40g, Option.some.injEq] at h40
    subst h30 h40
    left; apply Table.ofLabels_at
    refine ⟨by decide, T.L1988.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩,
      st, _, hx, hsp, hfm, hF2, ⟨hk2v, hk1v, hSF2, hN0, ?_, ?_, ?_,
        ⟨hN1, Nat.le_succ_of_le hN49, [(0, A2.n0N e a (k0N a row) k2)], _, ?_, depth_init hN1,
          hR, hSR, qw_init _ _⟩, ?_⟩, hm2⟩⟩, ?_⟩
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrsp, hrbp]; done)
    · simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      exact hSF2.1.1.2
    · simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      exact hSF2.1.1.1.2.2
    · simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      rfl
    · simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      decide
    · edge_step

end Kraken.Examples.Sbr.Reset
