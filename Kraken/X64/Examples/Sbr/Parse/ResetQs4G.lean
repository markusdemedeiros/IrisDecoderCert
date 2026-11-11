import Kraken.X64.Examples.Sbr.Parse.ResetQs4Lib
import Kraken.X64.Examples.Sbr.Parse.ResetQs2Lib4

/-!
# `sbr_reset`, `AV_QSORT` copy 4 (`vk1`): the pushes and two elements
(`L27e0`, `L2812`, `L2830`, `L2860`)
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse Kraken.Examples.Sbr.Parse.Qsort

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Reset

variable [CodeEnv]

set_option hygiene false in
/-- The two stack stores of a push at entry `|S|` (`v1`, `v2` the two words). -/
local macro "q1_push" v1:term:max v2:term:max : tactic => `(tactic| (
    have ha0 : s₀.regs.get64 .rbp + BitVec.ofNat 64 (16 * S.length) + 18446744073709550224#64
        = t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 (16 * S.length) := by
      rw [hrbp]; exact stk_addr0 _ _
    have ha1 : s₀.regs.get64 .rbp + BitVec.ofNat 64 (16 * S.length) + 18446744073709550232#64
        = t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 (16 * S.length + 8) := by
      rw [hrbp]; exact stk_addr1 _ _
    have hv1 := stk_load hm hF (o := 16 * S.length) (by omega) ha0
    have hm1 := stk_store hm hF (o := 16 * S.length) (by omega) ha0 ($v1 : BitVec 64).toInt
    have hF1 := fr_wr_len hF (o := 16 * S.length) (n := 8) (by omega) ($v1 : BitVec 64).toInt
    have hv2 := stk_load hm1 hF1 (o := 16 * S.length + 8) (by omega) ha1
    have hm2 := stk_store hm1 hF1 (o := 16 * S.length + 8) (by omega) ha1
      ($v2 : BitVec 64).toInt
    have hF2 := fr_wr_len hF1 (o := 16 * S.length + 8) (n := 8) (by omega)
      ($v2 : BitVec 64).toInt
    have hSRo := (stk_wr_hi hF1 (o' := 16 * S.length + 8) (n := 8) (by omega)
      ($v2 : BitVec 64).toInt (t₀ := t₀) (o := 0x480) (S := S) (by omega)).mpr
      ((stk_wr_hi hF (o' := 16 * S.length) (n := 8) (by omega) ($v1 : BitVec 64).toInt
      (t₀ := t₀) (o := 0x480) (S := S) (by omega)).mpr hSR)
    have hWf' := (Q4.w_wr hF1 (o := 16 * S.length + 8) (n := 8) (by omega)
      ($v2 : BitVec 64).toInt (Or.inl (by omega))).mpr ((Q4.w_wr hF (o := 16 * S.length)
      (n := 8) (by omega) ($v1 : BitVec 64).toInt (Or.inl (by omega))).mpr hWf)
    have hs1 : frSlot64 (wr (wr fr (16 * S.length) (Int.toBytes 8 ($v1 : BitVec 64).toInt))
        (16 * S.length + 8) (Int.toBytes 8 ($v2 : BitVec 64).toInt)) (0x570 - 16 * S.length)
        = $v1 := by
      rw [slot_wr64 hF1 (by omega) _ (by simp only [rb]; omega),
        slot_wr_same hF (by omega) (by simp only [rb]; omega), BitVec.ofInt_toInt]
    have hs2 : frSlot64 (wr (wr fr (16 * S.length) (Int.toBytes 8 ($v1 : BitVec 64).toInt))
        (16 * S.length + 8) (Int.toBytes 8 ($v2 : BitVec 64).toInt)) (0x568 - 16 * S.length)
        = $v2 := by
      rw [slot_wr_same hF1 (by omega) (by simp only [rb]; omega), BitVec.ofInt_toInt]
    have hAv : ∀ r, QS.av (wr (wr fr (16 * S.length) (Int.toBytes 8 ($v1 : BitVec 64).toInt))
        (16 * S.length + 8) (Int.toBytes 8 ($v2 : BitVec 64).toInt)) 0x480 r
        = QS.av fr 0x480 r := fun r => by
      rw [av_wr_other hF1 (by omega) _ (by omega), av_wr_other hF (by omega) _ (by omega)]
    have hQ' := And.intro hQ.1 (hQ.2.congr hAv)
    generalize hf2 : wr (wr fr (16 * S.length) (Int.toBytes 8 ($v1 : BitVec 64).toInt))
        (16 * S.length + 8) (Int.toBytes 8 ($v2 : BitVec 64).toInt) = fr2
      at hm2 hF2 hWf' hSRo hs1 hs2 hAv hQ'))

set_option maxRecDepth 100000 in
theorem blk_L27e0 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L27e0" ⟨"sbr_reset.L27e0", B.L27e0, some "sbr_reset.L2812"⟩ := by
  info_off
  measure_hb "L27e0"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, st, fr, hX, ⟨hrsp, hrbp⟩, hRg, hF, hWf, hm, hN1, hN2, S, A0, lo, hi1, hax, hD,
      hc, hR, hSR, hQ, hdx, hcx, l, rt, hPD, h9, h8, -⟩ :=
      Q4.g_iff.mp (T.L27e0.mp hs)
    clear hs
    rw [V.L27e0] at hn
    subst hn
    have hdx' : s₀.regs.get64 .rdx = QS.ep t₀ 0x480 lo := hdx
    have hcx' : s₀.regs.get64 .rcx = QS.ep t₀ 0x480 hi1 - 2#64 := hcx
    have h9' : s₀.regs.get64 .r9 = QS.ep t₀ 0x480 l := h9
    have h8' : s₀.regs.get64 .r8 = QS.ep t₀ 0x480 rt := h8
    clear hdx hcx h9 h8
    have ⟨p1, p2, p3, p4⟩ := hPD
    have hW := qw_cur hQ
    simp only at hW
    have hRs : 0x578 ≤ (t₀.regs.get64 .rsp).toNat := hX.rc
    have hS6 : S.length ≤ 6 := depth_len (m := 6) hD (by omega)
    have hcx2 : s₀.regs.get64 .rcx = QS.ep t₀ 0x480 (hi1 - 1) := by
      rw [hcx', ep_sub2 _ _ _ (by omega)]
    have hQS := qw_drop hQ
    have hph := stkPhi_eq hm hF hrbp hRs (o := 0x480) (N := A2.n1N e a (k0N a row) k2) (by omega)
        hSR hQS.1 (by omega)
    have es := qs_shl4 S.length
    have d1 := ep_dif_le_iff hRs (o := 0x480) (p := l) (q := lo) (p' := hi1 - 1) (q' := l)
      (by omega) (by omega) (by omega) (by omega)
    q1_push (QS.ep t₀ 0x480 lo) (QS.ep t₀ 0x480 rt)
    have hs2' : frSlot64 fr2 (0x568 - 16 * S.length) = QS.ep t₀ 0x480 (rt + 1) - 2#64 := by
      rw [hs2, ep_sub2 _ _ _ (by omega)]; rfl
    have hSR2 := stkRel_push (I := (lo, rt + 1)) hSRo hs1 hs2'
    have hPD2 : QS.PDone (QS.av fr2 0x480) lo (hi1 - 1) l rt := by
      unfold QS.PDone; omega
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L27e0]
    vcgen
    all_goals subst s₀
    all_goals subst hP
    all_goals try simp only [AddrIndex.offset64_scale1, Int64.toBitVec_ofNat_norm,
      Int64.toBitVec_neg_ofNat_norm, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
      Nat.reduceSub, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, BitVec.ofNat_eq_ofNat, hax,
      es, hdx', h8', h9']
    all_goals first | (rw [hv1]; rfl) | (rw [hv2]; rfl) | skip
    · -- `l - lo ≤ hi1 - 1 - l`: the larger part is the left one
      rename_i c
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hcx2, h9', hdx'] at c
      rw [cc_ge64] at c
      simp only [decide_eq_true_eq, d1] at c
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L2830.mpr (Q4.g_iff.mpr ⟨row, k2, st, fr, hX, ⟨?_, ?_⟩, (by q4_rg hRg),
          hF, hWf, hm, hN1, hN2, S, A0, lo, hi1, ?_, hD, hc, hR, hSR, hQ, ?_, ?_, l, rt, hPD, ?_,
          ?_, c⟩), Or.inr ⟨?_, by decide⟩⟩
      all_goals try (regs_simp; (first | exact hrsp | exact hrbp | exact hax | exact hdx'))
      all_goals try (regs_simp; (first | exact hcx' | exact h9' | exact h8'))
      simp only [V.L2830, VD.L2830, VD.L27e0]
      regs_simp
      rw [stkPhi_mk _ _ _ _ (by regs_simp), hax, hdx', BitVec.toNat_ofNat]
    · -- the depth check (`|S| < 64`)
      rename_i _ c
      exfalso
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hax] at c
      rw [cc_nc_sub] at c
      simp only [decide_eq_true_eq, BitVec.toNat_ofNat, BitVec.setWidth_eq,
        Int64.toBitVec_ofNat_norm] at c
      omega
    · -- push `(lo, rt + 1)`
      rename_i c _ _ _ _
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hcx2, h9', hdx'] at c
      rw [cc_ge64] at c
      simp only [decide_eq_false_iff_not, d1] at c
      refine ⟨T.L2812.mpr (Q4.g_iff.mpr ⟨row, k2, st, _, hX, ⟨?_, ?_⟩, (by q4_rg hRg), hF2, hWf',
          hm2, hN1, hN2, S, A0, lo, hi1, ?_, hD, hc, hR, hSRo, hQ', ?_, ?_, l, rt, hPD2, ?_, ?_,
          by omega, hSR2⟩), ?_⟩
      all_goals try (regs_simp; (first | exact hrsp | exact hrbp | exact hax | exact hdx'))
      all_goals try (regs_simp; (first | exact hcx' | exact h9' | exact h8'))
      simp only [V.L2812, VD.L2812, VD.L27e0]
      regs_simp
      rw [hax, hdx', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := S.length) (by omega),
        stkPhi_lit hm2 hF2 (by regs_simp; exact hrbp) hRs (by omega) hSRo hQS.1 (by omega), hph]
      exact Nat.le_refl _

set_option maxRecDepth 100000 in
theorem blk_L2812 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2812" ⟨"sbr_reset.L2812", B.L2812, some "sbr_reset.L2830"⟩ := by
  info_off
  measure_hb "L2812"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, st, fr, hX, ⟨hrsp, hrbp⟩, hRg, hF, hWf, hm, hN1, hN2, S, A0, lo, hi1, hax, hD,
      hc, hR, hSR, hQ, hdx, hcx, l, rt, hPD, h9, h8, hlt, hSR2⟩ :=
      Q4.g_iff.mp (T.L2812.mp hs)
    clear hs
    rw [V.L2812] at hn
    subst hn
    have hdx' : s₀.regs.get64 .rdx = QS.ep t₀ 0x480 lo := hdx
    have hcx' : s₀.regs.get64 .rcx = QS.ep t₀ 0x480 hi1 - 2#64 := hcx
    have h9' : s₀.regs.get64 .r9 = QS.ep t₀ 0x480 l := h9
    clear hdx hcx h9
    have ⟨p1, p2, p3, p4⟩ := hPD
    have hW := qw_cur hQ
    simp only at hW
    have hRs : 0x578 ≤ (t₀.regs.get64 .rsp).toNat := hX.rc
    have hS6 : S.length ≤ 6 := depth_len (m := 6) hD (by omega)
    have hQS := qw_drop hQ
    have hph := stkPhi_eq hm hF hrbp hRs (o := 0x480) (N := A2.n1N e a (k0N a row) k2) (by omega)
        hSR hQS.1 (by omega)
    have hpl := phi_le hQS.1
    have hpl' : phi S ≤ 6 * 99 := Nat.le_trans hpl (Nat.mul_le_mul hS6 (by omega))
    have hwB := ep_wB hRs (o := 0x480) hW.1 (by omega)
    have hΦ : QS.stkPhi s₀ (s₀.regs.get64 .rax).toNat
        + wBn 2 (s₀.regs.get64 .rdx).toNat (s₀.regs.get64 .rcx).toNat
        = phi S + (2 * (hi1 - lo) + 1) := by
      rw [hax, hdx', hcx', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hph, hwB]; rfl
    have hQ2 := qw_split hQ (l := l) (rt := rt) (by omega) (by omega) (by omega)
    rw [show S ++ [(lo, rt + 1), (l + 1, hi1)] = (S ++ [(lo, rt + 1)]) ++ [(l + 1, hi1)] by
      simp] at hQ2
    obtain ⟨hD2, hDc2⟩ := depth_push (B := (lo, rt + 1)) (c := hi1 - (l + 1)) hD hc
      (by omega) (by simp only; omega) (by omega)
    have hph2 := stkPhi_eq hm hF hrbp hRs (o := 0x480) (N := A2.n1N e a (k0N a row) k2) (by omega)
        hSR2
      (fun J hJ => hQ2.1 J (List.mem_append_left _ hJ)) (by simp; omega)
    have hwB2 := ep_wB hRs (o := 0x480) (lo := l + 1) (hi1 := hi1) (by omega) (by omega)
    have hinc : s₀.regs.get64 .rax + 1#64 = BitVec.ofNat 64 (S ++ [(lo, rt + 1)]).length := by
      rw [hax, List.length_append, List.length_singleton]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    have ea := q1_ep_add2 t₀ 0x480 l
    have ea' : 2#64 + QS.ep t₀ 0x480 l = QS.ep t₀ 0x480 (l + 1) := by
      rw [BitVec.add_comm]; exact ea
    have hA : Box _ := ⟨hX⟩
    have hmT : Box _ := ⟨hm⟩
    clear hX hm
    simp only [B.L2812]
    vcgen
    all_goals subst s₀
    all_goals try simp only [h9', ea, ea', BitVec.setWidth_eq, AddrIndex.offset64_none,
      BitVec.add_zero, Int64.toBitVec_ofNat_norm, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte,
      BitVec.ofNat_eq_ofNat, hinc]
    all_goals try simp only [ea, ea']
    left; apply Table.ofLabels_at
    refine ⟨by decide, T.L2670.mpr (Q4.g_iff.mpr ⟨row, k2, st, fr, hA.get, ⟨?_, ?_⟩,
        (by q4_rg hRg), hF, hWf, hmT.get, hN1, hN2, S ++ [(lo, rt + 1)], A0, l + 1, hi1, ?_, hD2,
        hDc2, hR, hSR2, hQ2, ?_, ?_, trivial⟩), Or.inl ?_⟩
    all_goals try (regs_simp; (first | exact hrsp | exact hrbp | exact hinc | exact hcx'))
    · regs_simp
    simp only [V.L2670, VD.L2670, VD.L2812]
    regs_simp
    rw [hΦ]
    refine lex_head_lt ?_ (by omega)
    rw [stkPhi_mk _ _ _ _ (by regs_simp)]
    regs_simp
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := (S ++ [(lo, rt + 1)]).length)
        (by simp only [List.length_append, List.length_singleton]; omega), hph2, hcx', hwB2,
      phi_append, phi_one]
    unfold wt
    simp only
    omega

set_option maxRecDepth 100000 in
theorem blk_L2830 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2830" ⟨"sbr_reset.L2830", B.L2830, some "sbr_reset.L2860"⟩ := by
  info_off
  measure_hb "L2830"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, st, fr, hX, ⟨hrsp, hrbp⟩, hRg, hF, hWf, hm, hN1, hN2, S, A0, lo, hi1, hax, hD,
      hc, hR, hSR, hQ, hdx, hcx, l, rt, hPD, h9, h8, hle⟩ :=
      Q4.g_iff.mp (T.L2830.mp hs)
    clear hs
    rw [V.L2830] at hn
    subst hn
    have hdx' : s₀.regs.get64 .rdx = QS.ep t₀ 0x480 lo := hdx
    have hcx' : s₀.regs.get64 .rcx = QS.ep t₀ 0x480 hi1 - 2#64 := hcx
    have h9' : s₀.regs.get64 .r9 = QS.ep t₀ 0x480 l := h9
    have h8' : s₀.regs.get64 .r8 = QS.ep t₀ 0x480 rt := h8
    clear hdx hcx h9 h8
    have ⟨p1, p2, p3, p4⟩ := hPD
    have hW := qw_cur hQ
    simp only at hW
    have hRs : 0x578 ≤ (t₀.regs.get64 .rsp).toNat := hX.rc
    have hS6 : S.length ≤ 6 := depth_len (m := 6) hD (by omega)
    have hQS := qw_drop hQ
    have hph := stkPhi_eq hm hF hrbp hRs (o := 0x480) (N := A2.n1N e a (k0N a row) k2) (by omega)
        hSR hQS.1 (by omega)
    have hpl := phi_le hQS.1
    have hpl' : phi S ≤ 6 * 99 := Nat.le_trans hpl (Nat.mul_le_mul hS6 (by omega))
    have hwB := ep_wB hRs (o := 0x480) hW.1 (by omega)
    have hΦ : QS.stkPhi s₀ (s₀.regs.get64 .rax).toNat
        + wBn 2 (s₀.regs.get64 .rdx).toNat (s₀.regs.get64 .rcx).toNat
        = phi S + (2 * (hi1 - lo) + 1) := by
      rw [hax, hdx', hcx', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hph, hwB]; rfl
    have es := qs_shl4 S.length
    have ea := q1_ep_add2 t₀ 0x480 l
    have ea' : 2#64 + QS.ep t₀ 0x480 l = QS.ep t₀ 0x480 (l + 1) := by
      rw [BitVec.add_comm]; exact ea
    have e8 : QS.ep t₀ 0x480 rt = QS.ep t₀ 0x480 (rt + 1) - 2#64 := by
      rw [ep_sub2 _ _ _ (by omega), Nat.add_sub_cancel]
    have hinc : BitVec.ofNat 64 S.length + 1#64 = BitVec.ofNat 64 (S ++ [(l + 1, hi1)]).length
        := by
      rw [List.length_append, List.length_singleton]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    q1_push (QS.ep t₀ 0x480 (l + 1)) (QS.ep t₀ 0x480 hi1 - 2#64)
    have hSR2 := stkRel_push (I := (l + 1, hi1)) hSRo hs1 hs2
    have hQ2 := qw_comm2 (qw_split hQ' (l := l) (rt := rt) (by omega) (by omega) (by omega))
    rw [show S ++ [(l + 1, hi1), (lo, rt + 1)] = (S ++ [(l + 1, hi1)]) ++ [(lo, rt + 1)] by
      simp] at hQ2
    obtain ⟨hD2, hDc2⟩ := depth_push (B := (l + 1, hi1)) (c := rt + 1 - lo) hD hc
      (by omega) (by simp only; omega) (by omega)
    have hwB2 := ep_wB hRs (o := 0x480) (lo := lo) (hi1 := rt + 1) (by omega) (by omega)
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L2830]
    vcgen
    all_goals subst s₀
    all_goals subst hP
    all_goals try simp only [AddrIndex.offset64_scale1, Int64.toBitVec_ofNat_norm,
      Int64.toBitVec_neg_ofNat_norm, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
      Nat.reduceSub, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, BitVec.ofNat_eq_ofNat, hax,
      es, h8', h9', hcx', ea, ea', BitVec.setWidth_eq]
    all_goals try simp only [ea, ea', hinc]
    all_goals first | (rw [hv1]; rfl) | (rw [hv2]; rfl) | skip
    · -- the depth check (`|S| < 64`)
      rename_i c
      exfalso
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hax] at c
      rw [cc_nc_sub] at c
      simp only [decide_eq_true_eq, BitVec.toNat_ofNat, BitVec.setWidth_eq,
        Int64.toBitVec_ofNat_norm] at c
      omega
    left; apply Table.ofLabels_at
    refine ⟨by decide, T.L2670.mpr (Q4.g_iff.mpr ⟨row, k2, st, _, hX, ⟨?_, ?_⟩, (by q4_rg hRg),
        hF2, hWf', hm2, hN1, hN2, S ++ [(l + 1, hi1)], A0, lo, rt + 1, ?_, hD2, hDc2, hR, hSR2,
        hQ2, ?_, ?_, trivial⟩), Or.inl ?_⟩
    all_goals try (regs_simp; (first | exact hrsp | exact hrbp | exact hinc | exact hdx'))
    all_goals try (regs_simp; exact e8)
    simp only [lex_var, VD.L2670, VD.L2830]
    regs_simp
    rw [Nat.mod_eq_of_lt (a := S.length) (by omega), hph, hdx', hwB]
    refine lex_head_lt ?_ (by unfold wt; simp only; omega)
    simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := (S ++ [(l + 1, hi1)]).length)
        (by simp; omega), stkPhi_lit hm2 hF2 (by regs_simp; exact hrbp) hRs
        (by omega) hSR2 (fun J hJ => hQ2.1 J (List.mem_append_left _ hJ)) (by simp; omega),
      hdx', e8, hwB2, phi_append, phi_one]
    unfold wt
    simp only
    omega

set_option maxRecDepth 100000 in
theorem blk_L2860 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2860" ⟨"sbr_reset.L2860", B.L2860, some "sbr_reset.L287a"⟩ := by
  info_off
  measure_hb "L2860"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, st, fr, hX, ⟨hrsp, hrbp⟩, hRg, hF, hWf, hm, hN1, hN2, S, A0, lo, hi1, hax, hD,
      hc, hR, hSR, hQ, hdx, hcx, h2⟩ :=
      Q4.g_iff.mp (T.L2860.mp hs)
    clear hs
    rw [V.L2860] at hn
    subst hn
    subst h2
    have hdx' : s₀.regs.get64 .rdx = QS.ep t₀ 0x480 lo := hdx
    have hcx' : s₀.regs.get64 .rcx = QS.ep t₀ 0x480 (lo + 2) - 2#64 := hcx
    clear hdx hcx
    have hcx2 : s₀.regs.get64 .rcx = QS.ep t₀ 0x480 (lo + 1) := by
      rw [hcx', ep_sub2 _ _ _ (by omega)]; rfl
    have hS6 : S.length ≤ 6 := depth_len (m := 6) hD (by omega)
    have hRs : 0x578 ≤ (t₀.regs.get64 .rsp).toNat := hX.rc
    have hW := qw_cur hQ
    simp only at hW
    have hQS := qw_drop hQ
    have hphi : QS.stkPhi s₀ S.length = phi S :=
      stkPhi_eq hm hF hrbp hRs (o := 0x480) (N := A2.n1N e a (k0N a row) k2) (by omega) hSR hQS.1
          (by omega)
    have hphiS := Nat.le_trans (phi_le hQS.1) (Nat.mul_le_mul hS6 (Nat.le_refl _))
    have hphiS' : phi S ≤ 6 * 99 := Nat.le_trans hphiS (Nat.mul_le_mul_left _ (by omega))
    have hwI := ep_wB hRs (o := 0x480) hW.1 (by omega)
    have hl0 : s₀.dmem.loadInt (s₀.regs.get64 .rdx) 2
        = some (Int.ofBytes (slice fr (0x480 + 2 * (lo + 1)) 2)) := by
      rw [hdx']; exact av_load hm hF (by omega)
    have hl1 : s₀.dmem.loadInt (s₀.regs.get64 .rcx) 2
        = some (Int.ofBytes (slice fr (0x480 + 2 * (lo + 1 + 1)) 2)) := by
      rw [hcx2]; exact av_load hm hF (by omega)
    have hld : ∀ x : BitVec 16, ((s₀.dmem.storeInt (s₀.regs.get64 .rcx) 2 x.toInt).loadInt
        (s₀.regs.get64 .rdx) 2).isSome = true := fun x => by
      obtain ⟨hm1, hF1, -⟩ := Q4.sd_st hm hF hWf (o := 0x480) (q := lo + 1) (by omega) (by omega) x
      rw [← hcx2] at hm1
      rw [hdx', av_load hm1 hF1 (by omega)]; rfl
    obtain ⟨hm1, hF1, hWf1, hSR1, hav1⟩ := Q4.sd_st hm hF hWf (o := 0x480)
      (q := lo + 1) (by omega) (by omega) (BitVec.ofInt 16 (QS.av fr 0x480 lo))
    rw [← hcx2] at hm1
    obtain ⟨hm2, hF2, hWf2, hSR2, hav2⟩ := Q4.sd_st hm1 hF1 hWf1 (o := 0x480)
      (q := lo) (by omega) (by omega) (BitVec.ofInt 16 (QS.av fr 0x480 (lo + 1)))
    rw [← hdx'] at hm2
    have hsw := av_swap hav1 hav2 (toInt_ofInt_av _ _ _) (toInt_ofInt_av _ _ _)
    have hQ' := qw_swap hQ (i := lo) (j := lo + 1)
      (by unfold InIv; simp only; omega) (by unfold InIv; simp only; omega)
    rw [← hsw] at hQ'
    have hSR' := (hSR2 (by omega)).mpr ((hSR1 (by omega)).mpr hSR)
    have hphi' : ∀ R z sf, R.get64 .rbp = s₀.regs.get64 .rbp →
        QS.stkPhi (⟨R, z, sf, (s₀.dmem.storeInt (s₀.regs.get64 .rcx) 2
          (BitVec.ofInt 16 (QS.av fr 0x480 lo)).toInt).storeInt (s₀.regs.get64 .rdx) 2
          (BitVec.ofInt 16 (QS.av fr 0x480 (lo + 1))).toInt⟩ : MachineData) S.length
        = phi S := fun R z sf e2 =>
      stkPhi_eq hm2 hF2 (e2.trans hrbp) hRs (o := 0x480) (N := A2.n1N e a (k0N a row) k2)
          (by omega) hSR' hQS.1
        (by omega)
    have hA : Box _ := ⟨hX⟩
    have hmT : Box _ := ⟨hm⟩
    have hmT2 : Box _ := ⟨hm2⟩
    clear hX hm hm1 hm2 hav1 hav2 hSR1 hSR2
    simp only [B.L2860]
    vcgen
    all_goals subst s₀
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
        AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, Option.isSome_some, BitVec.setWidth_eq,
        Nat.reducePow, Nat.reduceMod, Nat.reduceSub]
    all_goals first | (rw [hl0]; rfl) | (rw [hl1]; rfl) | skip
    · -- `A lo ≤ A (lo + 1)`: pop
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L2640.mpr (Q4.g_iff.mpr ⟨row, k2, st, fr, hA.get, ⟨?_, ?_⟩,
          (by q4_rg hRg), hF, hWf, hmT.get, hN1, hN2, S, A0, ?_, hD, hR, hSR, hQS⟩), Or.inl ?_⟩
      all_goals try (regs_simp; (first | exact hrsp | exact hrbp | exact hax))
      simp only [V.L2640, VD.L2640, VD.L2860]
      regs_simp
      rw [stkPhi_mk _ _ _ _ (by regs_simp), hax, hdx', hcx', hwI, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), hphi]
      exact lex_head_lt (by unfold wt; simp only; omega) (by unfold wt at *; simp only at *; omega)
    · exact hld _
    · -- exchange, then pop
      rename_i v1 h1 v2 h2 _
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at h1 h2
      rw [hl0, Option.some.injEq] at h1
      rw [hl1, Option.some.injEq] at h2
      subst h1 h2
      rw [sw16_zx, sw16_zx, av_bytes fr 0x480 lo, av_bytes fr 0x480 (lo + 1)]
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L2640.mpr (Q4.g_iff.mpr ⟨row, k2, st, _, hA.get, ⟨?_, ?_⟩,
          (by q4_rg hRg), hF2, hWf2, hmT2.get, hN1, hN2, S, A0, ?_, hD, hR, hSR', qw_drop hQ'⟩),
              Or.inl ?_⟩
      all_goals try (regs_simp; (first | exact hrsp | exact hrbp | exact hax))
      simp only [V.L2640, VD.L2640, VD.L2860]
      regs_simp
      rw [hax, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hphi' _ _ _ (by regs_simp),
        hdx', hcx', hwI, hphi]
      exact lex_head_lt (by unfold wt; simp only; omega) (by unfold wt at *; simp only at *; omega)

end Kraken.Examples.Sbr.Reset
