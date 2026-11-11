import Kraken.X64.Examples.Sbr.Parse.ResetQs2Lib2

/-!
# `sbr_reset`, `AV_QSORT` copy 2 (`vk0`): the partition loop, scans and exchange
(`L1a90`, `L1ab0`, `L1ab4`, `L1a70`)
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse Kraken.Examples.Sbr.Parse.Qsort

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Reset

variable [CodeEnv]

theorem blk_L1ab0 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1ab0" ⟨"sbr_reset.L1ab0", B.L1ab0, some "sbr_reset.L1ab4"⟩ := by
  info_off
  measure_hb "L1ab0"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    subst hn
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hSF, hN0, h12, h15, hax, ⟨hN1, hN49, S, A0, lo, hi1, hcx, hD, hDc, hR, hSR, hQ,
        hsi, hdx, h8, l, rt, pv, hPI, h10, h9, hlr, h14⟩⟩, hm⟩⟩ := T.L1ab0.mp hs
    clear hs
    have hsi' : s₀.regs.get64 .rsi = QS.ep t₀ 0x400 lo := hsi
    have hdx' : s₀.regs.get64 .rdx = QS.ep t₀ 0x400 hi1 - 2#64 := hdx
    have h8' : s₀.regs.get64 .r8 = QS.ep t₀ 0x400 (hi1 - 2) := h8
    have h10' : s₀.regs.get64 .r10 = QS.ep t₀ 0x400 l := h10
    have h9' : s₀.regs.get64 .r9 = QS.ep t₀ 0x400 rt := h9
    clear hsi hdx h8 h10 h9
    have ⟨p1, p2, p3, p4, p5⟩ := hPI
    have hW := qw_cur hQ
    simp only at hW
    have hrs := rsp_ok hC
    simp only [resetStkMin] at hrs
    have hR' : 0x578 ≤ (t₀.regs.get64 .rsp).toNat := by omega
    have em2 := ep_m2 t₀ 0x400 rt (by omega)
    have em2' : 18446744073709551614#64 + QS.ep t₀ 0x400 rt = QS.ep t₀ 0x400 (rt - 1) := by
      rw [BitVec.add_comm]; exact em2
    have hPI' : QS.PInv (QS.av fr 0x400) lo (hi1 - 1) l (rt - 1) pv := by
      unfold QS.PInv; exact ⟨by omega, by omega, by omega, by omega, p5⟩
    have tl := ep_toNat hR' (o := 0x400) (q := l) (by omega)
    have trt := ep_toNat hR' (o := 0x400) (q := rt) (by omega)
    have trt1 := ep_toNat hR' (o := 0x400) (q := rt - 1) (by omega)
    simp only [B.L1ab0]
    vcgen
    all_goals subst s₀
    all_goals try simp only [h9', em2, AddrIndex.offset64_none, BitVec.add_zero,
      Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, Reg64s.get64_set64,
      reduceCtorEq, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.setWidth_eq, Nat.reducePow,
      Nat.reduceMod, Nat.reduceSub]
    all_goals try simp only [em2']
    refine ⟨T.L1ab4.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩,
      st, fr, hx, hsp, hfm, hF, ⟨hk2v, hk1v, hSF, hN0, ?_, ?_, ?_,
        ⟨hN1, hN49, S, A0, lo, hi1, ?_, hD, hDc, hR, hSR, hQ, ?_, ?_, ?_,
          l, rt - 1, pv, hPI', ?_, ?_, by omega, ?_⟩⟩, hm⟩⟩, ?_⟩
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrsp, hrbp, h12,
      h15, hax, hcx, hsi', hdx', h8', h9', h10', h14]; done)
    simp only [lex_var, VD.L1ab4, VD.L1ab0, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    refine lex_phase ?_ ?_
    · rw [stkPhi_mk _ _ _ _ (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte])]
    rw [h9', h10', tl, trt, trt1]
    split <;> omega

theorem blk_L1a90 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1a90" ⟨"sbr_reset.L1a90", B.L1a90,
      some "sbr_reset.L1ab0"⟩ := by
  info_off
  measure_hb "L1a90"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    subst hn
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hSF, hN0, h12, h15, hax, ⟨hN1, hN49, S, A0, lo, hi1, hcx, hD, hDc, hR, hSR, hQ,
        hsi, hdx, h8, l, rt, pv, hPI, h10, h9, hlr, h14⟩⟩, hm⟩⟩ := T.L1a90.mp hs
    clear hs
    have hsi' : s₀.regs.get64 .rsi = QS.ep t₀ 0x400 lo := hsi
    have hdx' : s₀.regs.get64 .rdx = QS.ep t₀ 0x400 hi1 - 2#64 := hdx
    have h8' : s₀.regs.get64 .r8 = QS.ep t₀ 0x400 (hi1 - 2) := h8
    have h10' : s₀.regs.get64 .r10 = QS.ep t₀ 0x400 l := h10
    have h9' : s₀.regs.get64 .r9 = QS.ep t₀ 0x400 rt := h9
    clear hsi hdx h8 h10 h9
    have ⟨p1, p2, p3, p4, p5⟩ := hPI
    have hW := qw_cur hQ
    simp only at hW
    have hrs := rsp_ok hC
    simp only [resetStkMin] at hrs
    have hR' : 0x578 ≤ (t₀.regs.get64 .rsp).toNat := by omega
    have hl := av_load hm hF (o := 0x400) (q := l) (by omega)
    have ea := ep_add2 t₀ 0x400 l
    have ea' : 2#64 + QS.ep t₀ 0x400 l = QS.ep t₀ 0x400 (l + 1) := by
      rw [BitVec.add_comm]; exact ea
    have hle := ep_le_iff hR' (o := 0x400) (p := l + 1) (q := rt) (by omega) (by omega)
    have hPI' : QS.PInv (QS.av fr 0x400) lo (hi1 - 1) (l + 1) rt pv := by
      unfold QS.PInv; exact ⟨by omega, by omega, by omega, by omega, p5⟩
    have tl := ep_toNat hR' (o := 0x400) (q := l) (by omega)
    have tl1 := ep_toNat hR' (o := 0x400) (q := l + 1) (by omega)
    have trt := ep_toNat hR' (o := 0x400) (q := rt) (by omega)
    simp only [B.L1a90]
    vcgen
    all_goals subst s₀
    all_goals try simp only [h10', ea, ea', BitVec.setWidth_eq, AddrIndex.offset64_none,
      BitVec.add_zero,
      Int64.toBitVec_ofNat_norm, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte,
      BitVec.ofNat_eq_ofNat]
    all_goals first | (rw [hl]; rfl) | skip
    · -- `A l ≥ pv`
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L1ab4.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩,
        st, fr, hx, hsp, hfm, hF, ⟨hk2v, hk1v, hSF, hN0, h12, h15, hax,
          ⟨hN1, hN49, S, A0, lo, hi1, hcx, hD, hDc, hR, hSR, hQ, hsi', hdx', h8',
            l, rt, pv, hPI, h10', h9', by omega, h14⟩⟩, hm⟩⟩, Or.inl ?_⟩
      simp only [lex_var, VD.L1ab4, VD.L1a90]
      refine lex_phase_lt (by rw [stkPhi_mk _ _ _ _ rfl]) ?_
      rw [h9', h10', tl, trt]
      split <;> omega
    · -- `l + 1 ≤ rt`: the next element
      rename_i c2
      simp only [h9', h10', ea, ea', BitVec.setWidth_eq, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat,
        Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] at c2
      rw [cc_be_sub] at c2
      simp only [decide_eq_true_eq, hle] at c2
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L1a90.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩,
        st, fr, hx, hsp, hfm, hF, ⟨hk2v, hk1v, hSF, hN0, ?_, ?_, ?_,
          ⟨hN1, hN49, S, A0, lo, hi1, ?_, hD, hDc, hR, hSR, hQ, ?_, ?_, ?_,
            l + 1, rt, pv, hPI', ?_, ?_, c2, ?_⟩⟩, hm⟩⟩, Or.inl ?_⟩
      all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrsp, hrbp, h12,
        h15, hax, hcx, hsi', hdx', h8', h9', h10', h14]; done)
      simp only [lex_var, VD.L1a90, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      refine lex_phase_lt ?_ ?_
      · rw [stkPhi_mk _ _ _ _ (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte])]
      rw [h9', h10', tl, tl1, trt]
      omega
    · -- `rt < l + 1`
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L1ab4.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩,
        st, fr, hx, hsp, hfm, hF, ⟨hk2v, hk1v, hSF, hN0, ?_, ?_, ?_,
          ⟨hN1, hN49, S, A0, lo, hi1, ?_, hD, hDc, hR, hSR, hQ, ?_, ?_, ?_,
            l + 1, rt, pv, hPI', ?_, ?_, by omega, ?_⟩⟩, hm⟩⟩, Or.inl ?_⟩
      all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrsp, hrbp, h12,
        h15, hax, hcx, hsi', hdx', h8', h9', h10', h14]; done)
      simp only [lex_var, VD.L1ab4, VD.L1a90, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      refine lex_phase_lt ?_ ?_
      · rw [stkPhi_mk _ _ _ _ (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte])]
      rw [h9', h10', tl, tl1, trt]
      split <;> omega

theorem blk_L1ab4 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1ab4" ⟨"sbr_reset.L1ab4", B.L1ab4,
      some "sbr_reset.L1ad0"⟩ := by
  info_off
  measure_hb "L1ab4"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    subst hn
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hSF, hN0, h12, h15, hax, ⟨hN1, hN49, S, A0, lo, hi1, hcx, hD, hDc, hR, hSR, hQ,
        hsi, hdx, h8, l, rt, pv, hPI, h10, h9, hlr, h14⟩⟩, hm⟩⟩ := T.L1ab4.mp hs
    clear hs
    have hsi' : s₀.regs.get64 .rsi = QS.ep t₀ 0x400 lo := hsi
    have hdx' : s₀.regs.get64 .rdx = QS.ep t₀ 0x400 hi1 - 2#64 := hdx
    have h8' : s₀.regs.get64 .r8 = QS.ep t₀ 0x400 (hi1 - 2) := h8
    have h10' : s₀.regs.get64 .r10 = QS.ep t₀ 0x400 l := h10
    have h9' : s₀.regs.get64 .r9 = QS.ep t₀ 0x400 rt := h9
    clear hsi hdx h8 h10 h9
    have ⟨p1, p2, p3, p4, p5⟩ := hPI
    have hW := qw_cur hQ
    simp only at hW
    have hrs := rsp_ok hC
    simp only [resetStkMin] at hrs
    have hR' : 0x578 ≤ (t₀.regs.get64 .rsp).toNat := by omega
    have hl := av_load hm hF (o := 0x400) (q := rt) (by omega)
    have hlt := ep_lt_iff hR' (o := 0x400) (p := rt) (q := l) (by omega) (by omega)
    have tl := ep_toNat hR' (o := 0x400) (q := l) (by omega)
    have trt := ep_toNat hR' (o := 0x400) (q := rt) (by omega)
    simp only [B.L1ab4]
    vcgen
    all_goals subst s₀
    all_goals try simp only [h9', h10', AddrIndex.offset64_none, BitVec.add_zero,
      Int64.toBitVec_ofNat_norm, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte,
      BitVec.ofNat_eq_ofNat]
    all_goals first | (rw [hl]; rfl) | skip
    · -- `rt < l`
      rename_i c1
      try simp only [h9', h10'] at c1
      rw [cc_a_sub] at c1
      simp only [decide_eq_true_eq, hlt] at c1
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L1a84.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩,
        st, fr, hx, hsp, hfm, hF, ⟨hk2v, hk1v, hSF, hN0, h12, h15, hax,
          ⟨hN1, hN49, S, A0, lo, hi1, hcx, hD, hDc, hR, hSR, hQ, hsi', hdx', h8',
            l, rt, pv, hPI, h10', h9', trivial⟩⟩, hm⟩⟩, Or.inl ?_⟩
      simp only [lex_var, VD.L1a84, VD.L1ab4]
      refine lex_phase_lt (by rw [stkPhi_mk _ _ _ _ rfl]) ?_
      rw [h9', h10', tl, trt]
      split <;> (try split) <;> omega
    · -- `A rt > pv`
      rename_i c1 _ _ _
      try simp only [h9', h10'] at c1
      rw [cc_a_sub] at c1
      simp only [decide_eq_false_iff_not, hlt] at c1
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L1ab0.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩,
        st, fr, hx, hsp, hfm, hF, ⟨hk2v, hk1v, hSF, hN0, ?_, ?_, ?_,
          ⟨hN1, hN49, S, A0, lo, hi1, ?_, hD, hDc, hR, hSR, hQ, ?_, ?_, ?_,
            l, rt, pv, hPI, ?_, ?_, by omega, ?_⟩⟩, hm⟩⟩, Or.inl ?_⟩
      all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrsp, hrbp, h12,
        h15, hax, hcx, hsi', hdx', h8', h9', h10', h14]; done)
      simp only [lex_var, VD.L1ab0, VD.L1ab4, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      refine lex_phase_lt ?_ ?_
      · rw [stkPhi_mk _ _ _ _ (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte])]
      rw [h9', h10', tl, trt]
      split <;> omega
    · -- `A rt ≤ pv`: exchange
      rename_i c1 v1 h1 _
      try simp only [h9', h10'] at c1
      rw [cc_a_sub] at c1
      simp only [decide_eq_false_iff_not, hlt] at c1
      try simp only [h9', AddrIndex.offset64_none, BitVec.add_zero, Int64.toBitVec_ofNat_norm,
        Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, BitVec.ofNat_eq_ofNat] at h1
      rw [hl, Option.some.injEq] at h1
      subst h1
      rw [av_bytes fr 0x400 rt]
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L1a70.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩,
        st, fr, hx, hsp, hfm, hF, ⟨hk2v, hk1v, hSF, hN0, ?_, ?_, ?_,
          ⟨hN1, hN49, S, A0, lo, hi1, ?_, hD, hDc, hR, hSR, hQ, ?_, ?_, ?_,
            l, rt, pv, hPI, ?_, ?_, by omega, ?_⟩⟩, hm⟩⟩, Or.inl ?_⟩
      all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrsp, hrbp, h12,
        h15, hax, hcx, hsi', hdx', h8', h9', h10', sw16_zx]; done)
      simp only [lex_var, VD.L1a70, VD.L1ab4, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      refine lex_phase_lt ?_ ?_
      · rw [stkPhi_mk _ _ _ _ (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte])]
      rw [h9', h10', tl, trt]
      split <;> omega

theorem blk_L1a70 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1a70" ⟨"sbr_reset.L1a70", B.L1a70, some "sbr_reset.L1a84"⟩ := by
  info_off
  measure_hb "L1a70"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    subst hn
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hSF, hN0, h12, h15, hax, ⟨hN1, hN49, S, A0, lo, hi1, hcx, hD, hDc, hR, hSR, hQ,
        hsi, hdx, h8, l, rt, pv, hPI, h10, h9, hlr, h13⟩⟩, hm⟩⟩ := T.L1a70.mp hs
    clear hs
    have hsi' : s₀.regs.get64 .rsi = QS.ep t₀ 0x400 lo := hsi
    have hdx' : s₀.regs.get64 .rdx = QS.ep t₀ 0x400 hi1 - 2#64 := hdx
    have h8' : s₀.regs.get64 .r8 = QS.ep t₀ 0x400 (hi1 - 2) := h8
    have h10' : s₀.regs.get64 .r10 = QS.ep t₀ 0x400 l := h10
    have h9' : s₀.regs.get64 .r9 = QS.ep t₀ 0x400 rt := h9
    clear hsi hdx h8 h10 h9
    have ⟨p1, p2, p3, p4, p5⟩ := hPI
    have hW := qw_cur hQ
    simp only at hW
    have hrs := rsp_ok hC
    simp only [resetStkMin] at hrs
    have hR' : 0x578 ≤ (t₀.regs.get64 .rsp).toNat := by omega
    have hS6 : S.length ≤ 6 := depth_len (m := 6) hD (by omega)
    have hph := stkPhi_eq hm hF hrbp hR' (o := 0x400) (by omega) hSR
      (fun J hJ => hQ.1 J (by simp [hJ])) (by omega)
    have hl := av_load hm hF (o := 0x400) (q := l) (by omega)
    have hlrt := av_load hm hF (o := 0x400) (q := rt) (by omega)
    have hl2g : ∀ v : Int, loadInt (storeInt s₀.dmem (QS.ep t₀ 0x400 rt) 2 v)
        (QS.ep t₀ 0x400 l) 2 = some (Int.ofBytes (slice (wr fr
          (0x400 + 2 * (rt + 1)) (Int.toBytes 2 v)) (0x400 + 2 * (l + 1)) 2)) := fun v =>
      av_load (av_store hm hF (by omega) v)
        (fr_wr_len hF (o := 0x400 + 2 * (rt + 1)) (n := 2) (by omega) v) (by omega)
    have ea := ep_add2 t₀ 0x400 l
    have ea' : 2#64 + QS.ep t₀ 0x400 l = QS.ep t₀ 0x400 (l + 1) := by
      rw [BitVec.add_comm]; exact ea
    have em2 := ep_m2 t₀ 0x400 rt (by omega)
    have em2' : 18446744073709551614#64 + QS.ep t₀ 0x400 rt = QS.ep t₀ 0x400 (rt - 1) := by
      rw [BitVec.add_comm]; exact em2
    have tl := ep_toNat hR' (o := 0x400) (q := l) (by omega)
    have tl1 := ep_toNat hR' (o := 0x400) (q := l + 1) (by omega)
    have trt := ep_toNat hR' (o := 0x400) (q := rt) (by omega)
    have trt1 := ep_toNat hR' (o := 0x400) (q := rt - 1) (by omega)
    -- the exchange of `l` and `rt`
    have tL := av_toInt fr 0x400 l
    have tR := av_toInt fr 0x400 rt
    have ho1 : 0x400 + 2 * (rt + 1) + 2 ≤ 0x470 := by omega
    have ho2 : 0x400 + 2 * (l + 1) + 2 ≤ 0x470 := by omega
    have hm1 := av_store hm hF (o := 0x400) (q := rt) (by omega)
      (BitVec.ofInt 16 (QS.av fr 0x400 l)).toInt
    have hF1 := fr_wr_len hF (o := 0x400 + 2 * (rt + 1)) (n := 2) (by omega)
      (BitVec.ofInt 16 (QS.av fr 0x400 l)).toInt
    have hm2 := av_store hm1 hF1 (o := 0x400) (q := l) (by omega)
      (BitVec.ofInt 16 (QS.av fr 0x400 rt)).toInt
    have hF2 := fr_wr_len hF1 (o := 0x400 + 2 * (l + 1)) (n := 2) (by omega)
      (BitVec.ofInt 16 (QS.av fr 0x400 rt)).toInt
    have hSF2 := (sf_wr hF1 ho2 (BitVec.ofInt 16 (QS.av fr 0x400 rt)).toInt).mpr
      ((sf_wr hF ho1 (BitVec.ofInt 16 (QS.av fr 0x400 l)).toInt).mpr hSF)
    have hSR2 := (stk_wr hF1 (o' := 0x400 + 2 * (l + 1)) (n := 2) (by omega)
      (BitVec.ofInt 16 (QS.av fr 0x400 rt)).toInt (t₀ := t₀) (o := 0x400)
      (S := S) (by omega) (by omega)).mpr ((stk_wr hF (o' := 0x400 + 2 * (rt + 1)) (n := 2)
      (by omega) (BitVec.ofInt 16 (QS.av fr 0x400 l)).toInt (t₀ := t₀)
      (o := 0x400) (S := S) (by omega) (by omega)).mpr hSR)
    have hAv2 : ∀ r, QS.av (wr (wr fr (0x400 + 2 * (rt + 1))
        (Int.toBytes 2 (BitVec.ofInt 16 (QS.av fr 0x400 l)).toInt)) (0x400 + 2 * (l + 1))
        (Int.toBytes 2 (BitVec.ofInt 16 (QS.av fr 0x400 rt)).toInt)) 0x400 r
        = swap (QS.av fr 0x400) l rt r := fun r => by
      rw [av_wr hF1 (by omega) _ r, tR, ← upd_upd_swap]
      simp only [Parse.Qsort.upd]
      rw [av_wr hF (o := 0x400) (q := rt) (by omega) _ r, tL]
      rfl
    have hQ2 := (qw_swap hQ (i := l) (j := rt) (by simp only [InIv]; omega)
      (by simp only [InIv]; omega))
    have hQ2' := And.intro hQ2.1 (hQ2.2.congr hAv2)
    generalize hf2 : wr (wr fr (0x400 + 2 * (rt + 1))
        (Int.toBytes 2 (BitVec.ofInt 16 (QS.av fr 0x400 l)).toInt)) (0x400 + 2 * (l + 1))
        (Int.toBytes 2 (BitVec.ofInt 16 (QS.av fr 0x400 rt)).toInt) = fr2
      at hm2 hF2 hSF2 hSR2 hAv2 hQ2'
    have hPI' : QS.PInv (QS.av fr2 0x400) lo (hi1 - 1) (l + 1) (rt - 1) pv := by
      unfold QS.PInv
      refine ⟨by omega, by omega, by omega, by omega, ?_⟩
      rw [hAv2, swap_eq, ite_eq_right (show hi1 - 1 - 1 ≠ l by omega),
        ite_eq_right (show hi1 - 1 - 1 ≠ rt by omega)]
      exact p5
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L1a70]
    vcgen
    all_goals subst s₀
    all_goals subst hP
    all_goals try simp only [h9', h10', h13, ea, ea', em2, em2', AddrIndex.offset64_none,
      BitVec.add_zero, Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm,
      Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.setWidth_eq,
      Nat.reducePow, Nat.reduceMod, Nat.reduceSub]
    all_goals try simp only [ea', em2']
    all_goals first | (rw [hl]; rfl) | (rw [hlrt]; rfl) | (rw [hl2g]; rfl) | skip
    rename_i v1 h1
    try simp only [h10', AddrIndex.offset64_none, BitVec.add_zero, Int64.toBitVec_ofNat_norm,
      Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, BitVec.ofNat_eq_ofNat] at h1
    rw [hl, Option.some.injEq] at h1
    subst h1
    rw [sw16_zx, av_bytes fr 0x400 l]
    refine ⟨T.L1a84.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩,
      st, _, hx, hsp, hfm, hF2, ⟨hk2v, hk1v, hSF2, hN0, ?_, ?_, ?_,
        ⟨hN1, hN49, S, A0, lo, hi1, ?_, hD, hDc, hR, hSR2, hQ2', ?_, ?_, ?_,
          l + 1, rt - 1, pv, hPI', ?_, ?_, trivial⟩⟩, hm2⟩⟩, ?_⟩
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrsp, hrbp, h12,
      h15, hax, hcx, hsi', hdx', h8']; done)
    simp only [lex_var, VD.L1a84, VD.L1a70, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    refine lex_phase ?_ ?_
    · rw [hcx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), stkPhi_lit hm2 hF2
        (by (try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]); exact hrbp) hR'
        (by omega) hSR2 (fun J hJ => hQ.1 J (by simp [hJ])) (by omega), hph]
    rw [h9', h10', tl, tl1, trt, trt1]
    split <;> omega

end Kraken.Examples.Sbr.Reset
