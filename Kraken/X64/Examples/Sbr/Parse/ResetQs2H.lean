import Kraken.X64.Examples.Sbr.Parse.ResetQs2Lib3

/-!
# `sbr_reset`, `AV_QSORT` copy 2 (`vk0`): the sortedness scan (`L1af3`, `L1b00`, `L1b17`)
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse Kraken.Examples.Sbr.Parse.Qsort

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Reset

variable [CodeEnv]

theorem blk_L1af3 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1af3" ⟨"sbr_reset.L1af3", B.L1af3, some "sbr_reset.L1b00"⟩ := by
  info_off
  measure_hb "L1af3"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    subst hn
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hSF, hN0, h12, h15, hax, ⟨hN1, hN49, S, A0, lo, hi1, hcx, hD, hDc, hR, hSR, hQ,
        hsi, hdx, l, rt, hPD, h10, h9, -⟩⟩, hm⟩⟩ := T.L1af3.mp hs
    clear hs
    have hsi' : s₀.regs.get64 .rsi = QS.ep t₀ 0x400 lo := hsi
    have hdx' : s₀.regs.get64 .rdx = QS.ep t₀ 0x400 hi1 - 2#64 := hdx
    have h10' : s₀.regs.get64 .r10 = QS.ep t₀ 0x400 l := h10
    have h9' : s₀.regs.get64 .r9 = QS.ep t₀ 0x400 rt := h9
    clear hsi hdx h10 h9
    have ⟨p1, p2, p3, p4⟩ := hPD
    have hW := qw_cur hQ
    simp only at hW
    have hrs := rsp_ok hC
    simp only [resetStkMin] at hrs
    have hR' : 0x578 ≤ (t₀.regs.get64 .rsp).toNat := by omega
    simp only [B.L1af3]
    vcgen
    all_goals subst s₀
    refine ⟨T.L1b00.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩,
      st, fr, hx, hsp, hfm, hF, ⟨hk2v, hk1v, hSF, hN0, ?_, ?_, ?_,
        ⟨hN1, hN49, S, A0, lo, hi1, ?_, hD, hDc, hR, hSR, hQ, ?_, ?_, l, rt, hPD, ?_, ?_,
          lo, Nat.le_refl _, by omega, ?_⟩⟩, hm⟩⟩, Nat.le_of_lt ?_⟩
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrsp, hrbp, h12,
      h15, hax, hcx, hsi', hdx', h9', h10']; done)
    simp only [lex_var, VD.L1b00, VD.L1af3, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    refine lex_phase_lt ?_ ?_
    · rw [stkPhi_mk _ _ _ _ (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte])]
    decide

theorem blk_L1b00 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1b00" ⟨"sbr_reset.L1b00", B.L1b00, some "sbr_reset.L1b17"⟩ := by
  info_off
  measure_hb "L1b00"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    subst hn
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hSF, hN0, h12, h15, hax, ⟨hN1, hN49, S, A0, lo, hi1, hcx, hD, hDc, hR, hSR, hQ,
        hsi, hdx, l, rt, hPD, h10, h9, m, hlm, hmh, h8⟩⟩, hm⟩⟩ := T.L1b00.mp hs
    clear hs
    have hsi' : s₀.regs.get64 .rsi = QS.ep t₀ 0x400 lo := hsi
    have hdx' : s₀.regs.get64 .rdx = QS.ep t₀ 0x400 hi1 - 2#64 := hdx
    have h10' : s₀.regs.get64 .r10 = QS.ep t₀ 0x400 l := h10
    have h9' : s₀.regs.get64 .r9 = QS.ep t₀ 0x400 rt := h9
    clear hsi hdx h10 h9
    have ⟨p1, p2, p3, p4⟩ := hPD
    have hW := qw_cur hQ
    simp only at hW
    have hrs := rsp_ok hC
    simp only [resetStkMin] at hrs
    have hR' : 0x578 ≤ (t₀.regs.get64 .rsp).toNat := by omega
    have h8' : s₀.regs.get64 .r8 = QS.ep t₀ 0x400 m := h8
    clear h8
    have hl := av_load hm hF (o := 0x400) (q := m) (by omega)
    have hl1 := av_load hm hF (o := 0x400) (q := m + 1) (by omega)
    have ea := ep_add2 t₀ 0x400 m
    have ea' : 2#64 + QS.ep t₀ 0x400 m = QS.ep t₀ 0x400 (m + 1) := by
      rw [BitVec.add_comm]; exact ea
    have tm := ep_toNat hR' (o := 0x400) (q := m) (by omega)
    have tm1 := ep_toNat hR' (o := 0x400) (q := m + 1) (by omega)
    have tdx := epm2_toNat hR' (o := 0x400) (hi1 := hi1) (by omega)
    simp only [B.L1b00]
    vcgen
    all_goals subst s₀
    all_goals try simp only [h8', ea, ea', BitVec.setWidth_eq, AddrIndex.offset64_none,
      BitVec.add_zero, Int64.toBitVec_ofNat_norm, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte,
      BitVec.ofNat_eq_ofNat]
    all_goals try simp only [ea, ea']
    all_goals first | (rw [hl]; rfl) | (rw [hl1]; rfl) | skip
    · -- `m ≥ hi1 - 1`
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L1b17.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩,
        st, fr, hx, hsp, hfm, hF, ⟨hk2v, hk1v, hSF, hN0, ?_, ?_, ?_,
          ⟨hN1, hN49, S, A0, lo, hi1, ?_, hD, hDc, hR, hSR, hQ, ?_, ?_, l, rt, hPD, ?_, ?_,
            m, hlm, hmh, ?_⟩⟩, hm⟩⟩, Or.inl ?_⟩
      all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrsp, hrbp, h12,
        h15, hax, hcx, hsi', hdx', h8', h9', h10']; done)
      simp only [lex_var, VD.L1b17, VD.L1b00, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      refine lex_phase_lt ?_ ?_
      · rw [stkPhi_mk _ _ _ _ (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte])]
      decide
    · -- `A m ≤ A (m + 1)`: the next element
      rename_i c1 _ _ _ _ _
      try simp only [h8', hdx', Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] at c1
      rw [cc_nc_sub] at c1
      simp only [decide_eq_false_iff_not, decide_eq_true_eq, tdx, tm] at c1
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L1b00.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩,
        st, fr, hx, hsp, hfm, hF, ⟨hk2v, hk1v, hSF, hN0, ?_, ?_, ?_,
          ⟨hN1, hN49, S, A0, lo, hi1, ?_, hD, hDc, hR, hSR, hQ, ?_, ?_, l, rt, hPD, ?_, ?_,
            m + 1, by omega, by omega, ?_⟩⟩, hm⟩⟩, Or.inl ?_⟩
      all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrsp, hrbp, h12,
        h15, hax, hcx, hsi', hdx', h8', h9', h10']; done)
      simp only [lex_var, VD.L1b00, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      refine lex_last_lt ?_ ?_
      · rw [stkPhi_mk _ _ _ _ (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte])]
      rw [hdx', h8', tdx, tm, tm1]
      omega
    · -- `A m > A (m + 1)`
      refine ⟨T.L1b17.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩,
        st, fr, hx, hsp, hfm, hF, ⟨hk2v, hk1v, hSF, hN0, ?_, ?_, ?_,
          ⟨hN1, hN49, S, A0, lo, hi1, ?_, hD, hDc, hR, hSR, hQ, ?_, ?_, l, rt, hPD, ?_, ?_,
            m, hlm, hmh, ?_⟩⟩, hm⟩⟩, Nat.le_of_lt ?_⟩
      all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrsp, hrbp, h12,
        h15, hax, hcx, hsi', hdx', h8', h9', h10']; done)
      simp only [lex_var, VD.L1b17, VD.L1b00, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      refine lex_phase_lt ?_ ?_
      · rw [stkPhi_mk _ _ _ _ (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte])]
      decide

theorem blk_L1b17 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1b17" ⟨"sbr_reset.L1b17", B.L1b17, some "sbr_reset.L1b20"⟩ := by
  info_off
  measure_hb "L1b17"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    subst hn
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hSF, hN0, h12, h15, hax, ⟨hN1, hN49, S, A0, lo, hi1, hcx, hD, hDc, hR, hSR, hQ,
        hsi, hdx, l, rt, hPD, h10, h9, m, hlm, hmh, h7⟩⟩, hm⟩⟩ := T.L1b17.mp hs
    clear hs
    have hsi' : s₀.regs.get64 .rsi = QS.ep t₀ 0x400 lo := hsi
    have hdx' : s₀.regs.get64 .rdx = QS.ep t₀ 0x400 hi1 - 2#64 := hdx
    have h10' : s₀.regs.get64 .r10 = QS.ep t₀ 0x400 l := h10
    have h9' : s₀.regs.get64 .r9 = QS.ep t₀ 0x400 rt := h9
    clear hsi hdx h10 h9
    have ⟨p1, p2, p3, p4⟩ := hPD
    have hW := qw_cur hQ
    simp only at hW
    have hrs := rsp_ok hC
    simp only [resetStkMin] at hrs
    have hR' : 0x578 ≤ (t₀.regs.get64 .rsp).toNat := by omega
    clear h7
    have hS6 : S.length ≤ 6 := depth_len (m := 6) hD (by omega)
    have hph := stkPhi_eq hm hF hrbp hR' (o := 0x400) (by omega) hSR
      (fun J hJ => hQ.1 J (by simp [hJ])) (by omega)
    have hpl := phi_le (S := S) (fun J hJ => hQ.1 J (by simp [hJ]))
    have hwB := ep_wB hR' (o := 0x400) hW.1 (by omega)
    have hΦ : QS.stkPhi s₀ (s₀.regs.get64 .rcx).toNat
        + wBn 2 (s₀.regs.get64 .rsi).toNat (s₀.regs.get64 .rdx).toNat
        = phi S + (2 * (hi1 - lo) + 1) := by
      rw [hcx, hsi', hdx', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hph, hwB]; rfl
    have hpl' : phi S ≤ 6 * 99 := Nat.le_trans hpl (Nat.mul_le_mul hS6 (by omega))
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L1b17]
    vcgen
    all_goals subst s₀
    all_goals subst hP
    · -- the interval is sorted: pop
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L1980.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩,
        st, fr, hx, hsp, hfm, hF, ⟨hk2v, hk1v, hSF, hN0, h12, h15, hax,
          ⟨hN1, hN49, S, A0, hcx, hD, hR, hSR, qw_drop hQ⟩⟩, hm⟩⟩, Or.inl ?_⟩
      simp only [lex_var, VD.L1980, VD.L1b17]
      rw [hΦ]
      refine lex_head_lt ?_ (by omega)
      rw [stkPhi_mk _ _ _ _ rfl, hcx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hph]
      omega
    · refine ⟨T.L1b20.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩,
        st, fr, hx, hsp, hfm, hF, ⟨hk2v, hk1v, hSF, hN0, h12, h15, hax,
          ⟨hN1, hN49, S, A0, lo, hi1, hcx, hD, hDc, hR, hSR, hQ, hsi', hdx', l, rt, hPD,
            h10', h9', trivial⟩⟩, hm⟩⟩, Nat.le_of_lt ?_⟩
      simp only [lex_var, VD.L1b20, VD.L1b17]
      refine lex_phase_lt (by rw [stkPhi_mk _ _ _ _ rfl]) ?_
      decide

end Kraken.Examples.Sbr.Reset
