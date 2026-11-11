import Kraken.X64.Examples.Sbr.Parse.ResetQs2Lib2

/-!
# `sbr_reset`, `AV_QSORT` copy 2 (`vk0`): the partition loop, tests and pivot loads
(`L1a84`, `L1a89`, `L1ad0`)
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse Kraken.Examples.Sbr.Parse.Qsort

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Reset

variable [CodeEnv]

theorem blk_L1a89 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1a89" ⟨"sbr_reset.L1a89", B.L1a89, some "sbr_reset.L1a90"⟩ := by
  info_off
  measure_hb "L1a89"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    subst hn
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hSF, hN0, h12, h15, hax, ⟨hN1, hN49, S, A0, lo, hi1, hcx, hD, hDc, hR, hSR, hQ,
        hsi, hdx, h8, l, rt, pv, hPI, h10, h9, hlr⟩⟩, hm⟩⟩ := T.L1a89.mp hs
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
    have hl := av_load hm hF (o := 0x400) (q := hi1 - 2) (by omega)
    have hpv : QS.av fr 0x400 (hi1 - 2) = pv := by
      rw [← p5, show hi1 - 1 - 1 = hi1 - 2 by omega]
    simp only [B.L1a89]
    vcgen
    all_goals subst s₀
    all_goals try simp only [h8', AddrIndex.offset64_none, BitVec.add_zero,
      Int64.toBitVec_ofNat_norm, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte,
      BitVec.ofNat_eq_ofNat]
    · rw [hl]; rfl
    rename_i v1 h1
    try simp only [h8', AddrIndex.offset64_none, BitVec.add_zero, Int64.toBitVec_ofNat_norm,
      Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, BitVec.ofNat_eq_ofNat] at h1
    rw [hl, Option.some.injEq] at h1
    subst h1
    rw [av_bytes fr 0x400 (hi1 - 2)]
    subst hpv
    refine ⟨T.L1a90.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩,
      st, fr, hx, hsp, hfm, hF, ⟨hk2v, hk1v, hSF, hN0, ?_, ?_, ?_,
        ⟨hN1, hN49, S, A0, lo, hi1, ?_, hD, hDc, hR, hSR, hQ, ?_, ?_, ?_,
          l, rt, _, hPI, ?_, ?_, hlr, ?_⟩⟩, hm⟩⟩, ?_⟩
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrsp, hrbp, h12,
      h15, hax, hcx, hsi', hdx', h8', h9', h10', sw16_zx]; done)
    simp only [lex_var, VD.L1a90, VD.L1a89, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    rw [stkPhi_mk _ _ _ _ (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte])]
    exact Nat.le_refl _

theorem blk_L1ad0 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1ad0" ⟨"sbr_reset.L1ad0", B.L1ad0, some "sbr_reset.L1ad4"⟩ := by
  info_off
  measure_hb "L1ad0"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    subst hn
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hSF, hN0, h12, h15, hax, ⟨hN1, hN49, S, A0, lo, hi1, hcx, hD, hDc, hR, hSR, hQ,
        hsi, hdx, h8, l, rt, pv, hPI, h10, h9, hlr⟩⟩, hm⟩⟩ := T.L1ad0.mp hs
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
    have hl := av_load hm hF (o := 0x400) (q := hi1 - 2) (by omega)
    have hpv : QS.av fr 0x400 (hi1 - 2) = pv := by
      rw [← p5, show hi1 - 1 - 1 = hi1 - 2 by omega]
    simp only [B.L1ad0]
    vcgen
    all_goals subst s₀
    all_goals try simp only [h8', AddrIndex.offset64_none, BitVec.add_zero,
      Int64.toBitVec_ofNat_norm, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte,
      BitVec.ofNat_eq_ofNat]
    · rw [hl]; rfl
    rename_i v1 h1
    try simp only [h8', AddrIndex.offset64_none, BitVec.add_zero, Int64.toBitVec_ofNat_norm,
      Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, BitVec.ofNat_eq_ofNat] at h1
    rw [hl, Option.some.injEq] at h1
    subst h1
    rw [av_bytes fr 0x400 (hi1 - 2)]
    subst hpv
    refine ⟨T.L1ad4.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩,
      st, fr, hx, hsp, hfm, hF, ⟨hk2v, hk1v, hSF, hN0, ?_, ?_, ?_,
        ⟨hN1, hN49, S, A0, lo, hi1, ?_, hD, hDc, hR, hSR, hQ, ?_, ?_, ?_,
          l, rt, _, hPI, ?_, ?_, hlr, ?_⟩⟩, hm⟩⟩, ?_⟩
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrsp, hrbp, h12,
      h15, hax, hcx, hsi', hdx', h8', h9', h10', sw16_zx]; done)
    simp only [lex_var, VD.L1ad4, VD.L1ad0, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    rw [stkPhi_mk _ _ _ _ (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte])]
    exact Nat.le_refl _

theorem blk_L1a84 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1a84" ⟨"sbr_reset.L1a84", B.L1a84, some "sbr_reset.L1a89"⟩ := by
  info_off
  measure_hb "L1a84"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    subst hn
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hSF, hN0, h12, h15, hax, ⟨hN1, hN49, S, A0, lo, hi1, hcx, hD, hDc, hR, hSR, hQ,
        hsi, hdx, h8, l, rt, pv, hPI, h10, h9, -⟩⟩, hm⟩⟩ := T.L1a84.mp hs
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
    have hle := ep_le_iff hR' (o := 0x400) (p := l) (q := rt) (by omega) (by omega)
    have hlt := ep_lt_iff hR' (o := 0x400) (p := rt) (q := l) (by omega) (by omega)
    simp only [B.L1a84]
    vcgen
    all_goals subst s₀
    · -- `rt < l`
      rename_i c1
      simp only [h9', h10'] at c1
      rw [cc_a_sub] at c1
      simp only [decide_eq_true_eq, hlt] at c1
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L1ad0.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩,
        st, fr, hx, hsp, hfm, hF, ⟨hk2v, hk1v, hSF, hN0, h12, h15, hax,
          ⟨hN1, hN49, S, A0, lo, hi1, hcx, hD, hDc, hR, hSR, hQ, hsi', hdx', h8',
            l, rt, pv, hPI, h10', h9', c1⟩⟩, hm⟩⟩, Or.inl ?_⟩
      simp only [lex_var, VD.L1ad0, VD.L1a84]
      refine lex_phase_lt (by rw [stkPhi_mk _ _ _ _ rfl]) ?_
      rw [h9', h10', ite_eq_right (by omega)]
      decide
    · -- `l ≤ rt`
      rename_i c1
      simp only [h9', h10'] at c1
      rw [cc_a_sub] at c1
      simp only [decide_eq_false_iff_not, hlt] at c1
      refine ⟨T.L1a89.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩,
        st, fr, hx, hsp, hfm, hF, ⟨hk2v, hk1v, hSF, hN0, h12, h15, hax,
          ⟨hN1, hN49, S, A0, lo, hi1, hcx, hD, hDc, hR, hSR, hQ, hsi', hdx', h8',
            l, rt, pv, hPI, h10', h9', by omega⟩⟩, hm⟩⟩, ?_⟩
      simp only [lex_var, VD.L1a89, VD.L1a84]
      rw [h9', h10', ite_eq_left (by omega), stkPhi_mk _ _ _ _ rfl]
      exact Nat.le_refl _

end Kraken.Examples.Sbr.Reset
