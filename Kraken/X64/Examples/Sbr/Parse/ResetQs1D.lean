import Kraken.X64.Examples.Sbr.Parse.ResetQs1Lib

/-!
# `sbr_reset`, `AV_QSORT` copy 1 (`stop_dk`): the partition loop (`L13c0` .. `L1420`)
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse Kraken.Examples.Sbr.Parse.Qsort

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Reset

variable [CodeEnv]

set_option maxRecDepth 100000 in
theorem blk_L13d4 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L13d4" ⟨"sbr_reset.L13d4", B.L13d4, some "sbr_reset.L13d9"⟩ := by
  info_off
  measure_hb "L13d4"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, hr, hsp1, hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨h40, h30, hN1, hN2, S, A0, lo, hi1, hax, hD, hc, hR, hSR, hQ, hdx, hcx, hdi, l, rt, pv,
        hPI, h9, h8, -⟩, hm⟩ := T.L13d4.mp hs
    clear hs
    rw [V.L13d4] at hn
    subst hn
    have hRs : 0x578 ≤ (t₀.regs.get64 .rsp).toNat := by
      have := rsp_ok hC; unfold resetStkMin at this; omega
    have hW := qw_cur hQ
    simp only at hW
    have ⟨p1, p2, p3, p4, p5⟩ := hPI
    have tl := ep_toNat hRs (o := 0x4fe) (q := l) (by omega)
    have trt := ep_toNat hRs (o := 0x4fe) (q := rt) (by omega)
    have hA : Box _ := ⟨hx⟩
    have hmT : Box _ := ⟨hm⟩
    clear hx hm
    simp only [B.L13d4]
    vcgen
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
        AddrIndex.offset64_none,
        Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, Option.isSome_some, BitVec.setWidth_eq, Nat.reducePow, Nat.reduceMod,
        Nat.reduceSub]
    all_goals rename_i e c; subst e
    all_goals rw [cc_a_sub] at c
    · -- `rt < l`: to L1420
      simp only [decide_eq_true_eq] at c
      rw [h8, h9, tl, trt] at c
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L1420.mpr ⟨row, hr, hsp1, hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hA.get, hsp,
        hfm, hF, ⟨h40, h30, hN1, hN2, S, A0, lo, hi1, hax, hD, hc, hR, hSR, hQ, hdx, hcx, hdi,
          l, rt, pv, hPI, h9, h8, by omega⟩, hmT.get⟩, Or.inl ?_⟩
      simp only [V.L1420, VD.L1420, VD.L13d4]
      refine q1_lex_phase_lt (by rw [stkPhi_mk s₀ _ _ _ rfl]) ?_
      rw [h9, h8, tl, trt]
      split <;> omega
    · -- `l ≤ rt`: to L13d9
      simp only [decide_eq_false_iff_not] at c
      rw [h8, h9, tl, trt] at c
      refine ⟨T.L13d9.mpr ⟨row, hr, hsp1, hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hA.get, hsp,
        hfm, hF, ⟨h40, h30, hN1, hN2, S, A0, lo, hi1, hax, hD, hc, hR, hSR, hQ, hdx, hcx, hdi,
          l, rt, pv, hPI, h9, h8, by omega⟩, hmT.get⟩, ?_⟩
      simp only [V.L13d9, VD.L13d9, VD.L13d4]
      have hc' : (s₀.regs.get64 .r9).toNat ≤ (s₀.regs.get64 .r8).toNat := by
        rw [h9, h8, tl, trt]; omega
      rw [ite_eq_left hc', stkPhi_mk s₀ _ _ _ rfl]
      exact Nat.le_refl _

set_option maxRecDepth 100000 in
theorem blk_L13d9 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L13d9" ⟨"sbr_reset.L13d9", B.L13d9, some "sbr_reset.L13e0"⟩ := by
  info_off
  measure_hb "L13d9"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, hr, hsp1, hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨h40, h30, hN1, hN2, S, A0, lo, hi1, hax, hD, hc, hR, hSR, hQ, hdx, hcx, hdi, l, rt, pv,
        hPI, h9, h8, hlr⟩, hm⟩ := T.L13d9.mp hs
    clear hs
    rw [V.L13d9] at hn
    subst hn
    have hRs : 0x578 ≤ (t₀.regs.get64 .rsp).toNat := by
      have := rsp_ok hC; unfold resetStkMin at this; omega
    have hW := qw_cur hQ
    simp only at hW
    have ⟨p1, p2, p3, p4, p5⟩ := hPI
    have hpv : QS.av fr 0x4fe (hi1 - 2) = pv := by
      rw [show hi1 - 2 = hi1 - 1 - 1 by omega]; exact p5
    have hl0 : s₀.dmem.loadInt (s₀.regs.get64 .rdi) 2
        = some (Int.ofBytes (slice fr (0x4fe + 2 * (hi1 - 2 + 1)) 2)) := by
      rw [hdi]; exact av_load hm hF (by omega)
    have hA : Box _ := ⟨hx⟩
    have hmT : Box _ := ⟨hm⟩
    clear hx hm
    simp only [B.L13d9]
    vcgen
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
        AddrIndex.offset64_none,
        Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, Option.isSome_some, BitVec.setWidth_eq, Nat.reducePow, Nat.reduceMod,
        Nat.reduceSub]
    · rename_i e; subst e; rw [hl0]; rfl
    rename_i e v h1; subst e
    simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
      Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at h1
    rw [hl0, Option.some.injEq] at h1
    subst h1
    refine ⟨T.L13e0.mpr ⟨row, hr, hsp1, hC, hBO, ⟨?_, ?_⟩, st, fr, hA.get, hsp,
      hfm, hF, ⟨h40, h30, hN1, hN2, S, A0, lo, hi1, ?_, hD, hc, hR, hSR, hQ, ?_, ?_, ?_,
        l, rt, pv, hPI, ?_, ?_, hlr, ?_⟩, hmT.get⟩, ?_⟩
    · regs_simp; exact hrsp
    · regs_simp; exact hrbp
    · regs_simp; exact hax
    · regs_simp; exact hdx
    · regs_simp; exact hcx
    · regs_simp; exact hdi
    · regs_simp; exact h9
    · regs_simp; exact h8
    · regs_simp; rw [sw16_zx, av_bytes]; exact congrArg _ hpv
    · simp only [V.L13e0, VD.L13e0, VD.L13d9]
      regs_simp
      rw [stkPhi_mk s₀ _ _ _ (by regs_simp)]
      exact Nat.le_refl _

set_option maxRecDepth 100000 in
theorem blk_L1420 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1420" ⟨"sbr_reset.L1420", B.L1420, some "sbr_reset.L1424"⟩ := by
  info_off
  measure_hb "L1420"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, hr, hsp1, hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨h40, h30, hN1, hN2, S, A0, lo, hi1, hax, hD, hc, hR, hSR, hQ, hdx, hcx, hdi, l, rt, pv,
        hPI, h9, h8, hlr⟩, hm⟩ := T.L1420.mp hs
    clear hs
    rw [V.L1420] at hn
    subst hn
    have hRs : 0x578 ≤ (t₀.regs.get64 .rsp).toNat := by
      have := rsp_ok hC; unfold resetStkMin at this; omega
    have hW := qw_cur hQ
    simp only at hW
    have ⟨p1, p2, p3, p4, p5⟩ := hPI
    have hpv : QS.av fr 0x4fe (hi1 - 2) = pv := by
      rw [show hi1 - 2 = hi1 - 1 - 1 by omega]; exact p5
    have hl0 : s₀.dmem.loadInt (s₀.regs.get64 .rdi) 2
        = some (Int.ofBytes (slice fr (0x4fe + 2 * (hi1 - 2 + 1)) 2)) := by
      rw [hdi]; exact av_load hm hF (by omega)
    have hA : Box _ := ⟨hx⟩
    have hmT : Box _ := ⟨hm⟩
    clear hx hm
    simp only [B.L1420]
    vcgen
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
        AddrIndex.offset64_none,
        Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, Option.isSome_some, BitVec.setWidth_eq, Nat.reducePow, Nat.reduceMod,
        Nat.reduceSub]
    · rename_i e; subst e; rw [hl0]; rfl
    rename_i e v h1; subst e
    simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
      Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at h1
    rw [hl0, Option.some.injEq] at h1
    subst h1
    refine ⟨T.L1424.mpr ⟨row, hr, hsp1, hC, hBO, ⟨?_, ?_⟩, st, fr, hA.get, hsp,
      hfm, hF, ⟨h40, h30, hN1, hN2, S, A0, lo, hi1, ?_, hD, hc, hR, hSR, hQ, ?_, ?_, ?_,
        l, rt, pv, hPI, ?_, ?_, hlr, ?_⟩, hmT.get⟩, ?_⟩
    · regs_simp; exact hrsp
    · regs_simp; exact hrbp
    · regs_simp; exact hax
    · regs_simp; exact hdx
    · regs_simp; exact hcx
    · regs_simp; exact hdi
    · regs_simp; exact h9
    · regs_simp; exact h8
    · regs_simp; rw [sw16_zx, av_bytes]; exact congrArg _ hpv
    · simp only [V.L1424, VD.L1424, VD.L1420]
      regs_simp
      rw [stkPhi_mk s₀ _ _ _ (by regs_simp)]
      exact Nat.le_refl _

set_option maxRecDepth 100000 in
theorem blk_L1400 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1400" ⟨"sbr_reset.L1400", B.L1400, some "sbr_reset.L1404"⟩ := by
  info_off
  measure_hb "L1400"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, hr, hsp1, hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨h40, h30, hN1, hN2, S, A0, lo, hi1, hax, hD, hc, hR, hSR, hQ, hdx, hcx, hdi, l, rt, pv,
        hPI, h9, h8, hlr, h11⟩, hm⟩ := T.L1400.mp hs
    clear hs
    rw [V.L1400] at hn
    subst hn
    have hRs : 0x578 ≤ (t₀.regs.get64 .rsp).toNat := by
      have := rsp_ok hC; unfold resetStkMin at this; omega
    have hW := qw_cur hQ
    simp only at hW
    have ⟨p1, p2, p3, p4, p5⟩ := hPI
    have em := q1_ep_m2 t₀ 0x4fe rt (by omega)
    have em' := (BitVec.add_comm _ _).trans em
    have hPI' : QS.PInv (QS.av fr 0x4fe) lo (hi1 - 1) l (rt - 1) pv := by
      unfold QS.PInv; exact ⟨by omega, by omega, by omega, by omega, p5⟩
    have tl := ep_toNat hRs (o := 0x4fe) (q := l) (by omega)
    have trt := ep_toNat hRs (o := 0x4fe) (q := rt) (by omega)
    have trt1 := ep_toNat hRs (o := 0x4fe) (q := rt - 1) (by omega)
    have hA : Box _ := ⟨hx⟩
    have hmT : Box _ := ⟨hm⟩
    clear hx hm
    simp only [B.L1400]
    vcgen
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
        AddrIndex.offset64_none,
        Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, Option.isSome_some, BitVec.setWidth_eq, Nat.reducePow, Nat.reduceMod,
        Nat.reduceSub]
    rename_i e; subst e
    refine ⟨T.L1404.mpr ⟨row, hr, hsp1, hC, hBO, ⟨?_, ?_⟩, st, fr, hA.get, hsp,
      hfm, hF, ⟨h40, h30, hN1, hN2, S, A0, lo, hi1, ?_, hD, hc, hR, hSR, hQ, ?_, ?_, ?_,
        l, rt - 1, pv, hPI', ?_, ?_, by omega, ?_⟩, hmT.get⟩, ?_⟩
    · regs_simp; exact hrsp
    · regs_simp; exact hrbp
    · regs_simp; exact hax
    · regs_simp; exact hdx
    · regs_simp; exact hcx
    · regs_simp; exact hdi
    · regs_simp; exact h9
    · regs_simp; rw [h8]; exact em'
    · regs_simp; exact h11
    · simp only [V.L1404, VD.L1404, VD.L1400]
      regs_simp
      refine lex_phase (by rw [stkPhi_mk s₀ _ _ _ (by regs_simp)]) ?_
      rw [h8, em', h9, tl, trt, trt1]
      split <;> omega

set_option maxRecDepth 100000 in
theorem blk_L13e0 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L13e0" ⟨"sbr_reset.L13e0", B.L13e0, some "sbr_reset.L1400"⟩ := by
  info_off
  measure_hb "L13e0"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, hr, hsp1, hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨h40, h30, hN1, hN2, S, A0, lo, hi1, hax, hD, hc, hR, hSR, hQ, hdx, hcx, hdi, l, rt, pv,
        hPI, h9, h8, hlr, h11⟩, hm⟩ := T.L13e0.mp hs
    clear hs
    rw [V.L13e0] at hn
    subst hn
    have hRs : 0x578 ≤ (t₀.regs.get64 .rsp).toNat := by
      have := rsp_ok hC; unfold resetStkMin at this; omega
    have hW := qw_cur hQ
    simp only at hW
    have ⟨p1, p2, p3, p4, p5⟩ := hPI
    have ea := q1_ep_add2 t₀ 0x4fe l
    have ea' := (BitVec.add_comm _ _).trans ea
    have hPI' : QS.PInv (QS.av fr 0x4fe) lo (hi1 - 1) (l + 1) rt pv := by
      unfold QS.PInv; exact ⟨by omega, by omega, by omega, by omega, p5⟩
    have tl := ep_toNat hRs (o := 0x4fe) (q := l) (by omega)
    have tl1 := ep_toNat hRs (o := 0x4fe) (q := l + 1) (by omega)
    have trt := ep_toNat hRs (o := 0x4fe) (q := rt) (by omega)
    have hl9 : (s₀.dmem.loadInt (s₀.regs.get64 .r9) 2).isSome = true := by
      rw [h9, av_load hm hF (by omega)]; rfl
    have hA : Box _ := ⟨hx⟩
    have hmT : Box _ := ⟨hm⟩
    clear hx hm
    simp only [B.L13e0]
    vcgen
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
        AddrIndex.offset64_none,
        Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, Option.isSome_some, BitVec.setWidth_eq, Nat.reducePow, Nat.reduceMod,
        Nat.reduceSub]
    · rename_i e; subst e; exact hl9
    · -- `A l ≥ pv`: to L1404
      rename_i e v h1 c1; subst e
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L1404.mpr ⟨row, hr, hsp1, hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hA.get, hsp,
        hfm, hF, ⟨h40, h30, hN1, hN2, S, A0, lo, hi1, hax, hD, hc, hR, hSR, hQ, hdx, hcx, hdi,
          l, rt, pv, hPI, h9, h8, by omega, h11⟩, hmT.get⟩, Or.inl ?_⟩
      simp only [V.L1404, VD.L1404, VD.L13e0]
      refine q1_lex_phase_lt (by rw [stkPhi_mk s₀ _ _ _ rfl]) ?_
      rw [h9, h8, tl, trt]
      split <;> omega
    · -- `l + 1 ≤ rt`: the next element
      rename_i e v h1 c1 c2; subst e
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.setWidth_eq] at c2
      rw [cc_be_sub] at c2
      simp only [decide_eq_true_eq] at c2
      rw [h9, ea', h8, tl1, trt] at c2
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L13e0.mpr ⟨row, hr, hsp1, hC, hBO, ⟨?_, ?_⟩, st, fr, hA.get, hsp,
        hfm, hF, ⟨h40, h30, hN1, hN2, S, A0, lo, hi1, ?_, hD, hc, hR, hSR, hQ, ?_, ?_, ?_,
          l + 1, rt, pv, hPI', ?_, ?_, by omega, ?_⟩, hmT.get⟩, Or.inl ?_⟩
      · regs_simp; exact hrsp
      · regs_simp; exact hrbp
      · regs_simp; exact hax
      · regs_simp; exact hdx
      · regs_simp; exact hcx
      · regs_simp; exact hdi
      · regs_simp; rw [h9]; exact ea'
      · regs_simp; exact h8
      · regs_simp; exact h11
      · simp only [V.L13e0, VD.L13e0]
        regs_simp
        refine q1_lex_phase_lt (by rw [stkPhi_mk s₀ _ _ _ (by regs_simp)]) ?_
        rw [h9, ea', h8, tl, tl1, trt]
        omega
    · -- `rt < l + 1`: to L1404
      rename_i e v h1 c1 c2; subst e
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L1404.mpr ⟨row, hr, hsp1, hC, hBO, ⟨?_, ?_⟩, st, fr, hA.get, hsp,
        hfm, hF, ⟨h40, h30, hN1, hN2, S, A0, lo, hi1, ?_, hD, hc, hR, hSR, hQ, ?_, ?_, ?_,
          l + 1, rt, pv, hPI', ?_, ?_, by omega, ?_⟩, hmT.get⟩, Or.inl ?_⟩
      · regs_simp; exact hrsp
      · regs_simp; exact hrbp
      · regs_simp; exact hax
      · regs_simp; exact hdx
      · regs_simp; exact hcx
      · regs_simp; exact hdi
      · regs_simp; rw [h9]; exact ea'
      · regs_simp; exact h8
      · regs_simp; exact h11
      · simp only [V.L1404, VD.L1404, VD.L13e0]
        regs_simp
        refine q1_lex_phase_lt (by rw [stkPhi_mk s₀ _ _ _ (by regs_simp)]) ?_
        rw [h9, ea', h8, tl, tl1, trt]
        split <;> omega

set_option maxRecDepth 100000 in
theorem blk_L1404 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1404" ⟨"sbr_reset.L1404", B.L1404, some "sbr_reset.L1420"⟩ := by
  info_off
  measure_hb "L1404"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, hr, hsp1, hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨h40, h30, hN1, hN2, S, A0, lo, hi1, hax, hD, hc, hR, hSR, hQ, hdx, hcx, hdi, l, rt, pv,
        hPI, h9, h8, hlr, h11⟩, hm⟩ := T.L1404.mp hs
    clear hs
    rw [V.L1404] at hn
    subst hn
    have hRs : 0x578 ≤ (t₀.regs.get64 .rsp).toNat := by
      have := rsp_ok hC; unfold resetStkMin at this; omega
    have hW := qw_cur hQ
    simp only at hW
    have ⟨p1, p2, p3, p4, p5⟩ := hPI
    have tl := ep_toNat hRs (o := 0x4fe) (q := l) (by omega)
    have trt := ep_toNat hRs (o := 0x4fe) (q := rt) (by omega)
    have hl8 : s₀.dmem.loadInt (s₀.regs.get64 .r8) 2
        = some (Int.ofBytes (slice fr (0x4fe + 2 * (rt + 1)) 2)) := by
      rw [h8]; exact av_load hm hF (by omega)
    have hA : Box _ := ⟨hx⟩
    have hmT : Box _ := ⟨hm⟩
    clear hx hm
    simp only [B.L1404]
    vcgen
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
        AddrIndex.offset64_none,
        Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, Option.isSome_some, BitVec.setWidth_eq, Nat.reducePow, Nat.reduceMod,
        Nat.reduceSub]
    · -- `rt < l`: to L13d4
      rename_i e c1; subst e
      rw [cc_a_sub] at c1
      simp only [decide_eq_true_eq] at c1
      rw [h8, h9, tl, trt] at c1
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L13d4.mpr ⟨row, hr, hsp1, hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hA.get, hsp,
        hfm, hF, ⟨h40, h30, hN1, hN2, S, A0, lo, hi1, hax, hD, hc, hR, hSR, hQ, hdx, hcx, hdi,
          l, rt, pv, hPI, h9, h8, trivial⟩, hmT.get⟩, Or.inl ?_⟩
      simp only [V.L13d4, VD.L13d4, VD.L1404]
      refine q1_lex_phase_lt (by rw [stkPhi_mk s₀ _ _ _ rfl]) ?_
      rw [h9, h8, tl, trt]
      split <;> (try split) <;> omega
    · rename_i e c1; subst e; rw [hl8]; rfl
    all_goals rename_i e c1 v h1 c2; subst e
    all_goals rw [cc_a_sub] at c1
    all_goals simp only [decide_eq_false_iff_not] at c1
    all_goals rw [h8, h9, tl, trt] at c1
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
      Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at h1
    all_goals rw [hl8, Option.some.injEq] at h1
    all_goals subst h1
    · -- `A rt > pv`: to L1400
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L1400.mpr ⟨row, hr, hsp1, hC, hBO, ⟨?_, ?_⟩, st, fr, hA.get, hsp,
        hfm, hF, ⟨h40, h30, hN1, hN2, S, A0, lo, hi1, ?_, hD, hc, hR, hSR, hQ, ?_, ?_, ?_,
          l, rt, pv, hPI, ?_, ?_, by omega, ?_⟩, hmT.get⟩, Or.inl ?_⟩
      · regs_simp; exact hrsp
      · regs_simp; exact hrbp
      · regs_simp; exact hax
      · regs_simp; exact hdx
      · regs_simp; exact hcx
      · regs_simp; exact hdi
      · regs_simp; exact h9
      · regs_simp; exact h8
      · regs_simp; exact h11
      · simp only [V.L1400, VD.L1400, VD.L1404]
        regs_simp
        refine q1_lex_phase_lt (by rw [stkPhi_mk s₀ _ _ _ (by regs_simp)]) ?_
        rw [h9, h8, tl, trt]
        split <;> omega
    · -- `A rt ≤ pv`: exchange
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L13c0.mpr ⟨row, hr, hsp1, hC, hBO, ⟨?_, ?_⟩, st, fr, hA.get, hsp,
        hfm, hF, ⟨h40, h30, hN1, hN2, S, A0, lo, hi1, ?_, hD, hc, hR, hSR, hQ, ?_, ?_, ?_,
          l, rt, pv, hPI, ?_, ?_, by omega, ?_⟩, hmT.get⟩, Or.inl ?_⟩
      · regs_simp; exact hrsp
      · regs_simp; exact hrbp
      · regs_simp; exact hax
      · regs_simp; exact hdx
      · regs_simp; exact hcx
      · regs_simp; exact hdi
      · regs_simp; exact h9
      · regs_simp; exact h8
      · regs_simp; rw [sw16_zx]; exact av_bytes _ _ _
      · simp only [V.L13c0, VD.L13c0, VD.L1404]
        regs_simp
        refine q1_lex_phase_lt (by rw [stkPhi_mk s₀ _ _ _ (by regs_simp)]) ?_
        rw [h9, h8, tl, trt]
        split <;> omega

set_option maxRecDepth 100000 in
theorem blk_L13c0 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L13c0" ⟨"sbr_reset.L13c0", B.L13c0, some "sbr_reset.L13d4"⟩ := by
  info_off
  measure_hb "L13c0"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, hr, hsp1, hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨h40, h30, hN1, hN2, S, A0, lo, hi1, hax, hD, hc, hR, hSR, hQ, hdx, hcx, hdi, l, rt, pv,
        hPI, h9, h8, hlr, h14⟩, hm⟩ := T.L13c0.mp hs
    clear hs
    rw [V.L13c0] at hn
    subst hn
    have hS6 : S.length ≤ 6 := depth_len (m := 6) hD (by omega)
    have hRs : 0x578 ≤ (t₀.regs.get64 .rsp).toNat := by
      have := rsp_ok hC; unfold resetStkMin at this; omega
    have hW := qw_cur hQ
    simp only at hW
    have hQS := qw_drop hQ
    have ⟨p1, p2, p3, p4, p5⟩ := hPI
    have ea := q1_ep_add2 t₀ 0x4fe l
    have ea' := (BitVec.add_comm _ _).trans ea
    have em := q1_ep_m2 t₀ 0x4fe rt (by omega)
    have em' := (BitVec.add_comm _ _).trans em
    have tl := ep_toNat hRs (o := 0x4fe) (q := l) (by omega)
    have tl1 := ep_toNat hRs (o := 0x4fe) (q := l + 1) (by omega)
    have trt := ep_toNat hRs (o := 0x4fe) (q := rt) (by omega)
    have trt1 := ep_toNat hRs (o := 0x4fe) (q := rt - 1) (by omega)
    have hphi : QS.stkPhi s₀ S.length = phi S :=
      stkPhi_eq hm hF hrbp hRs (o := 0x4fe) (N := 13) (by omega) hSR hQS.1 (by omega)
    have hl9 : s₀.dmem.loadInt (s₀.regs.get64 .r9) 2
        = some (Int.ofBytes (slice fr (0x4fe + 2 * (l + 1)) 2)) := by
      rw [h9]; exact av_load hm hF (by omega)
    have hld8 : (s₀.dmem.loadInt (s₀.regs.get64 .r8) 2).isSome = true := by
      rw [h8, av_load hm hF (by omega)]; rfl
    have hld9 : ∀ x : BitVec 16, ((s₀.dmem.storeInt (s₀.regs.get64 .r8) 2 x.toInt).loadInt
        (s₀.regs.get64 .r9) 2).isSome = true := fun x => by
      obtain ⟨hm1, hF1, -⟩ := sd_st hm hF (o := 0x4fe) (q := rt) (by omega) (by omega) x
      rw [← h8] at hm1
      rw [h9, av_load hm1 hF1 (by omega)]; rfl
    obtain ⟨hm1, hF1, h401, h301, hSR1, hav1⟩ := sd_st hm hF (o := 0x4fe)
      (q := rt) (by omega) (by omega) (BitVec.ofInt 16 (QS.av fr 0x4fe l))
    rw [← h8] at hm1
    obtain ⟨hm2, hF2, h402, h302, hSR2, hav2⟩ := sd_st hm1 hF1 (o := 0x4fe)
      (q := l) (by omega) (by omega) (BitVec.setWidth 16 (s₀.regs.get64 .r14))
    rw [← h9] at hm2
    have hsw := av_swap hav1 hav2 (toInt_ofInt_av _ _ _) (toInt_av h14)
    have hQ' := qw_swap hQ (i := l) (j := rt)
      (by unfold InIv; simp only; omega) (by unfold InIv; simp only; omega)
    rw [← hsw] at hQ'
    have hPI' : QS.PInv (swap (QS.av fr 0x4fe) l rt) lo (hi1 - 1) (l + 1) (rt - 1)
        (swap (QS.av fr 0x4fe) l rt (hi1 - 1 - 1)) := by
      unfold QS.PInv
      exact ⟨by omega, by omega, by omega, by omega, rfl⟩
    rw [← hsw] at hPI'
    have hSR' := (hSR2 (by omega)).mpr ((hSR1 (by omega)).mpr hSR)
    have hphi' : ∀ R z sf, R.get64 .rbp = s₀.regs.get64 .rbp →
        QS.stkPhi (⟨R, z, sf, (s₀.dmem.storeInt (s₀.regs.get64 .r8) 2
          (BitVec.ofInt 16 (QS.av fr 0x4fe l)).toInt).storeInt (s₀.regs.get64 .r9) 2
          (BitVec.setWidth 16 (s₀.regs.get64 .r14)).toInt⟩ : MachineData) S.length
        = phi S := fun R z sf e2 =>
      stkPhi_eq hm2 hF2 (e2.trans hrbp) hRs (o := 0x4fe) (N := 13) (by omega) hSR' hQS.1
        (by omega)
    have hA : Box _ := ⟨hx⟩
    have hmT2 : Box _ := ⟨hm2⟩
    clear hx hm hm1 hm2 hav1 hav2 hSR1 hSR2
    simp only [B.L13c0]
    vcgen
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
        AddrIndex.offset64_none,
        Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, Option.isSome_some, BitVec.setWidth_eq, Nat.reducePow, Nat.reduceMod,
        Nat.reduceSub]
    · rename_i e; subst e; rw [hl9]; rfl
    · rename_i e v h1; subst e; exact hld8
    · rename_i e v h1; subst e; exact hld9 _
    rename_i e v h1; subst e
    simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
      Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at h1
    rw [hl9, Option.some.injEq] at h1
    subst h1
    rw [sw16_zx, av_bytes fr 0x4fe l]
    refine ⟨T.L13d4.mpr ⟨row, hr, hsp1, hC, hBO, ⟨?_, ?_⟩, st, _, hA.get, hsp,
      hfm, hF2, ⟨h402.trans (h401.trans h40), h302.trans (h301.trans h30), hN1, hN2, S, A0, lo,
        hi1, ?_, hD, hc, hR, hSR', hQ', ?_, ?_, ?_, l + 1, rt - 1, _, hPI', ?_, ?_,
        trivial⟩, hmT2.get⟩, ?_⟩
    · regs_simp; exact hrsp
    · regs_simp; exact hrbp
    · regs_simp; exact hax
    · regs_simp; exact hdx
    · regs_simp; exact hcx
    · regs_simp; exact hdi
    · regs_simp; rw [h9]; exact ea'
    · regs_simp; rw [h8]; exact em'
    · simp only [V.L13d4, VD.L13d4, VD.L13c0]
      regs_simp
      refine lex_phase ?_ ?_
      · rw [hax, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hphi' _ _ _ (by regs_simp),
          hphi]
      · rw [h9, ea', h8, em', tl, tl1, trt, trt1]
        split <;> omega

end Kraken.Examples.Sbr.Reset
