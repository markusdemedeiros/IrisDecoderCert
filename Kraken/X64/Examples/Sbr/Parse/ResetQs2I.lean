import Kraken.X64.Examples.Sbr.Parse.ResetQs2Lib4

/-!
# `sbr_reset`, `AV_QSORT` copy 2 (`vk0`): the pushes (`L1b20`, `L1b52`, `L1b70`)
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
local macro "qs2_push" v1:term:max v2:term:max : tactic => `(tactic| (
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
    have hSF2 := (sf_wr hF1 (o := 16 * S.length + 8) (n := 8) (by omega)
      ($v2 : BitVec 64).toInt).mpr
      ((sf_wr hF (o := 16 * S.length) (n := 8) (by omega) ($v1 : BitVec 64).toInt).mpr hSF)
    have hSRo := (stk_wr_hi hF1 (o' := 16 * S.length + 8) (n := 8) (by omega)
      ($v2 : BitVec 64).toInt (t₀ := t₀) (o := 0x400) (S := S) (by omega)).mpr
      ((stk_wr_hi hF (o' := 16 * S.length) (n := 8) (by omega) ($v1 : BitVec 64).toInt
      (t₀ := t₀) (o := 0x400) (S := S) (by omega)).mpr hSR)
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
        (16 * S.length + 8) (Int.toBytes 8 ($v2 : BitVec 64).toInt)) 0x400 r
        = QS.av fr 0x400 r := fun r => by
      rw [av_wr_other hF1 (by omega) _ (by omega), av_wr_other hF (by omega) _ (by omega)]
    have hQ' := And.intro hQ.1 (hQ.2.congr hAv)
    generalize hf2 : wr (wr fr (16 * S.length) (Int.toBytes 8 ($v1 : BitVec 64).toInt))
        (16 * S.length + 8) (Int.toBytes 8 ($v2 : BitVec 64).toInt) = fr2
      at hm2 hF2 hSF2 hSRo hs1 hs2 hAv hQ'))

theorem blk_L1b20 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1b20" ⟨"sbr_reset.L1b20", B.L1b20, some "sbr_reset.L1b52"⟩ := by
  info_off
  measure_hb "L1b20"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    subst hn
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hSF, hN0, h12, h15, hax, ⟨hN1, hN49, S, A0, lo, hi1, hcx, hD, hDc, hR, hSR, hQ,
        hsi, hdx, l, rt, hPD, h10, h9, -⟩⟩, hm⟩⟩ := T.L1b20.mp hs
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
    have hS6 : S.length ≤ 6 := depth_len (m := 6) hD (by omega)
    have hdx2 : s₀.regs.get64 .rdx = QS.ep t₀ 0x400 (hi1 - 1) := by
      rw [hdx', ep_sub2 _ _ _ (by omega)]
    have hph := stkPhi_eq hm hF hrbp hR' (o := 0x400) (by omega) hSR
      (fun J hJ => hQ.1 J (by simp [hJ])) (by omega)
    have es := qs_shl4 S.length
    have d1 := ep_dif_le_iff hR' (o := 0x400) (p := l) (q := lo) (p' := hi1 - 1) (q' := l)
      (by omega) (by omega) (by omega) (by omega)
    qs2_push (QS.ep t₀ 0x400 lo) (QS.ep t₀ 0x400 rt)
    have hs2' : frSlot64 fr2 (0x568 - 16 * S.length) = QS.ep t₀ 0x400 (rt + 1) - 2#64 := by
      rw [hs2, ep_sub2 _ _ _ (by omega)]; rfl
    have hSR2 := stkRel_push (I := (lo, rt + 1)) hSRo hs1 hs2'
    have hPD2 : QS.PDone (QS.av fr2 0x400) lo (hi1 - 1) l rt := by
      unfold QS.PDone; omega
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L1b20]
    vcgen
    all_goals subst s₀
    all_goals subst hP
    all_goals try simp only [AddrIndex.offset64_scale1, Int64.toBitVec_ofNat_norm,
      Int64.toBitVec_neg_ofNat_norm, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
      Nat.reduceSub, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, BitVec.ofNat_eq_ofNat, hcx,
      es, hsi', h9', h10']
    all_goals first | (rw [hv1]; rfl) | (rw [hv2]; rfl) | skip
    · -- `l - lo ≤ hi1 - 1 - l`: the larger part is the left one
      rename_i c
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hdx2, h10', hsi'] at c
      rw [cc_ge64] at c
      simp only [decide_eq_true_eq, d1] at c
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L1b70.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩,
        st, fr, hx, hsp, hfm, hF, ⟨hk2v, hk1v, hSF, hN0, ?_, ?_, ?_,
          ⟨hN1, hN49, S, A0, lo, hi1, ?_, hD, hDc, hR, hSR, hQ, ?_, ?_, l, rt, hPD, ?_, ?_,
            ?_⟩⟩, hm⟩⟩, Or.inr ⟨?_, ?_⟩⟩
      all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrsp, hrbp, h12,
        h15, hax, hcx, hsi', hdx', h9', h10']; done)
      · omega
      · simp only [lex_var, VD.L1b70, VD.L1b20, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        rw [stkPhi_mk _ _ _ _ (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte])]
      · simp only [lex_var]; decide
    · -- the depth check (`|S| < 64`)
      rename_i _ c
      exfalso
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hcx] at c
      rw [cc_nc_sub] at c
      simp only [decide_eq_true_eq, BitVec.toNat_ofNat, BitVec.setWidth_eq,
        Int64.toBitVec_ofNat_norm] at c
      omega
    · -- push `(lo, rt + 1)`
      rename_i c _ _ _ _
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hdx2, h10', hsi'] at c
      rw [cc_ge64] at c
      simp only [decide_eq_false_iff_not, d1] at c
      refine ⟨T.L1b52.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩,
        st, _, hx, hsp, hfm, hF2, ⟨hk2v, hk1v, hSF2, hN0, ?_, ?_, ?_,
          ⟨hN1, hN49, S, A0, lo, hi1, ?_, hD, hDc, hR, hSRo, hQ', ?_, ?_, l, rt, hPD2, ?_, ?_,
            ?_, hSR2⟩⟩, hm2⟩⟩, ?_⟩
      all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrsp, hrbp, h12,
        h15, hax, hcx, hsi', hdx', h9', h10']; done)
      · omega
      simp only [lex_var, VD.L1b52, VD.L1b20, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      rw [hcx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := S.length) (by omega), stkPhi_lit hm2 hF2
        (by (try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]); exact hrbp) hR'
        (by omega) hSRo (fun J hJ => hQ.1 J (by simp [hJ])) (by omega), hph]
      exact Nat.le_refl _

theorem blk_L1b52 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1b52" ⟨"sbr_reset.L1b52", B.L1b52,
      some "sbr_reset.L1b70"⟩ := by
  info_off
  measure_hb "L1b52"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    subst hn
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hSF, hN0, h12, h15, hax, ⟨hN1, hN49, S, A0, lo, hi1, hcx, hD, hDc, hR, hSR, hQ,
        hsi, hdx, l, rt, hPD, h10, h9, hlt, hSR2⟩⟩, hm⟩⟩ := T.L1b52.mp hs
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
    have hS6 : S.length ≤ 6 := depth_len (m := 6) hD (by omega)
    have hph := stkPhi_eq hm hF hrbp hR' (o := 0x400) (by omega) hSR
      (fun J hJ => hQ.1 J (by simp [hJ])) (by omega)
    have hpl := phi_le (S := S) (fun J hJ => hQ.1 J (by simp [hJ]))
    have hpl' : phi S ≤ 6 * 99 := Nat.le_trans hpl (Nat.mul_le_mul hS6 (by omega))
    have hwB := ep_wB hR' (o := 0x400) hW.1 (by omega)
    have hΦ : QS.stkPhi s₀ (s₀.regs.get64 .rcx).toNat
        + wBn 2 (s₀.regs.get64 .rsi).toNat (s₀.regs.get64 .rdx).toNat
        = phi S + (2 * (hi1 - lo) + 1) := by
      rw [hcx, hsi', hdx', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hph, hwB]; rfl
    have hQ2 := qw_split hQ (l := l) (rt := rt) (by omega) (by omega) (by omega)
    rw [show S ++ [(lo, rt + 1), (l + 1, hi1)] = (S ++ [(lo, rt + 1)]) ++ [(l + 1, hi1)] by
      simp] at hQ2
    obtain ⟨hD2, hDc2⟩ := depth_push (B := (lo, rt + 1)) (c := hi1 - (l + 1)) hD hDc
      (by omega) (by simp only; omega) (by omega)
    have hph2 := stkPhi_eq hm hF hrbp hR' (o := 0x400) (by omega) hSR2
      (fun J hJ => hQ2.1 J (List.mem_append_left _ hJ)) (by simp; omega)
    have hwB2 := ep_wB hR' (o := 0x400) (lo := l + 1) (hi1 := hi1) (by omega) (by omega)
    have hinc : s₀.regs.get64 .rcx + 1#64 = BitVec.ofNat 64 (S ++ [(lo, rt + 1)]).length := by
      rw [hcx, List.length_append, List.length_singleton]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    have ea := ep_add2 t₀ 0x400 l
    have ea' : 2#64 + QS.ep t₀ 0x400 l = QS.ep t₀ 0x400 (l + 1) := by
      rw [BitVec.add_comm]; exact ea
    simp only [B.L1b52]
    vcgen
    all_goals subst s₀
    all_goals try simp only [h10', ea, ea', BitVec.setWidth_eq, AddrIndex.offset64_none,
      BitVec.add_zero, Int64.toBitVec_ofNat_norm, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte,
      BitVec.ofNat_eq_ofNat, hinc]
    all_goals try simp only [ea, ea']
    left; apply Table.ofLabels_at
    refine ⟨by decide, T.L19b0.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩,
      st, fr, hx, hsp, hfm, hF, ⟨hk2v, hk1v, hSF, hN0, ?_, ?_, ?_,
        ⟨hN1, hN49, S ++ [(lo, rt + 1)], A0, l + 1, hi1, ?_, hD2, hDc2, hR, hSR2, hQ2, ?_, ?_,
          trivial⟩⟩, hm⟩⟩, Or.inl ?_⟩
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrsp, hrbp, h12,
      h15, hax, hinc, hsi', hdx', h9', h10']; done)
    simp only [lex_var, VD.L19b0, VD.L1b52, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    rw [hΦ]
    refine lex_head_lt ?_ (by omega)
    rw [stkPhi_mk _ _ _ _ (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := (S ++ [(lo, rt + 1)]).length)
        (by simp only [List.length_append, List.length_singleton]; omega), hph2, hdx', hwB2,
      phi_append, phi_one]
    unfold wt
    simp only
    omega

theorem blk_L1b70 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1b70" ⟨"sbr_reset.L1b70", B.L1b70,
      some "sbr_reset.L1ba0"⟩ := by
  info_off
  measure_hb "L1b70"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    subst hn
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hSF, hN0, h12, h15, hax, ⟨hN1, hN49, S, A0, lo, hi1, hcx, hD, hDc, hR, hSR, hQ,
        hsi, hdx, l, rt, hPD, h10, h9, hle⟩⟩, hm⟩⟩ := T.L1b70.mp hs
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
    have hS6 : S.length ≤ 6 := depth_len (m := 6) hD (by omega)
    have hph := stkPhi_eq hm hF hrbp hR' (o := 0x400) (by omega) hSR
      (fun J hJ => hQ.1 J (by simp [hJ])) (by omega)
    have hpl := phi_le (S := S) (fun J hJ => hQ.1 J (by simp [hJ]))
    have hpl' : phi S ≤ 6 * 99 := Nat.le_trans hpl (Nat.mul_le_mul hS6 (by omega))
    have hwB := ep_wB hR' (o := 0x400) hW.1 (by omega)
    have hΦ : QS.stkPhi s₀ (s₀.regs.get64 .rcx).toNat
        + wBn 2 (s₀.regs.get64 .rsi).toNat (s₀.regs.get64 .rdx).toNat
        = phi S + (2 * (hi1 - lo) + 1) := by
      rw [hcx, hsi', hdx', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hph, hwB]; rfl
    have es := qs_shl4 S.length
    have ea := ep_add2 t₀ 0x400 l
    have ea' : 2#64 + QS.ep t₀ 0x400 l = QS.ep t₀ 0x400 (l + 1) := by
      rw [BitVec.add_comm]; exact ea
    have e9 : QS.ep t₀ 0x400 rt = QS.ep t₀ 0x400 (rt + 1) - 2#64 := by
      rw [ep_sub2 _ _ _ (by omega), Nat.add_sub_cancel]
    have hinc : BitVec.ofNat 64 S.length + 1#64 = BitVec.ofNat 64 (S ++ [(l + 1, hi1)]).length
        := by
      rw [List.length_append, List.length_singleton]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    qs2_push (QS.ep t₀ 0x400 (l + 1)) (QS.ep t₀ 0x400 hi1 - 2#64)
    have hSR2 := stkRel_push (I := (l + 1, hi1)) hSRo hs1 hs2
    have hQ2 := qw_comm2 (qw_split hQ' (l := l) (rt := rt) (by omega) (by omega) (by omega))
    rw [show S ++ [(l + 1, hi1), (lo, rt + 1)] = (S ++ [(l + 1, hi1)]) ++ [(lo, rt + 1)] by
      simp] at hQ2
    obtain ⟨hD2, hDc2⟩ := depth_push (B := (l + 1, hi1)) (c := rt + 1 - lo) hD hDc
      (by omega) (by simp only; omega) (by omega)
    have hwB2 := ep_wB hR' (o := 0x400) (lo := lo) (hi1 := rt + 1) (by omega) (by omega)
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L1b70]
    vcgen
    all_goals subst s₀
    all_goals subst hP
    all_goals try simp only [AddrIndex.offset64_scale1, Int64.toBitVec_ofNat_norm,
      Int64.toBitVec_neg_ofNat_norm, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
      Nat.reduceSub, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, BitVec.ofNat_eq_ofNat, hcx,
      es, h9', h10', hdx', ea, ea', BitVec.setWidth_eq]
    all_goals try simp only [ea, ea', hinc]
    all_goals first | (rw [hv1]; rfl) | (rw [hv2]; rfl) | skip
    · -- the depth check (`|S| < 64`)
      rename_i c
      exfalso
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hcx] at c
      rw [cc_nc_sub] at c
      simp only [decide_eq_true_eq, BitVec.toNat_ofNat, BitVec.setWidth_eq,
        Int64.toBitVec_ofNat_norm] at c
      omega
    left; apply Table.ofLabels_at
    refine ⟨by decide, T.L19b0.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩,
      st, _, hx, hsp, hfm, hF2, ⟨hk2v, hk1v, hSF2, hN0, ?_, ?_, ?_,
        ⟨hN1, hN49, S ++ [(l + 1, hi1)], A0, lo, rt + 1, ?_, hD2, hDc2, hR, hSR2, hQ2, ?_, ?_,
          trivial⟩⟩, hm2⟩⟩, Or.inl ?_⟩
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrsp, hrbp, h12,
      h15, hax, hinc, hsi', hdx', h9', h10', e9]; done)
    simp only [lex_var, VD.L19b0, VD.L1b70, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    rw [hΦ]
    refine lex_head_lt ?_ (by omega)
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := (S ++ [(l + 1, hi1)]).length)
        (by simp; omega), stkPhi_lit hm2 hF2
        (by (try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]); exact hrbp) hR'
        (by omega) hSR2 (fun J hJ => hQ2.1 J (List.mem_append_left _ hJ)) (by simp; omega),
      hsi', e9, hwB2, phi_append, phi_one]
    unfold wt
    simp only
    omega

end Kraken.Examples.Sbr.Reset
