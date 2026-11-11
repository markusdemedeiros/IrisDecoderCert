import Kraken.X64.Examples.Sbr.Parse.ResetQs3Lib
import Kraken.X64.Examples.Sbr.Parse.ResetQs2J

/-!
# `sbr_reset`, `AV_QSORT` copy 3 (`vk1`): the entry (`L2357`, `L237d`)

`L2357` compares the minimum band with `vdk0_max` (`-0x50`): if it is not smaller it jumps to
`L25ca` (the `make_bands` output as an `Arr`); else it saves the start pointer (stack slot 0) and
`num_bands_1` (`-0x30`) and computes the end pointer. `L237d` saves it (stack slot 1) and enters
the loop with one pending interval.
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
theorem blk_L2357 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2357" ⟨"sbr_reset.L2357", B.L2357, some "sbr_reset.L237d"⟩ := by
  info_off
  measure_hb "L2357"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    subst hn
    obtain ⟨row, k2, hr, hk2, hk0, hq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, h110, hInc, hN0, hN1, h15, hMB, h12, h13, hax, vm, hv1, hv2, hTB, h30⟩, hm⟩⟩ :=
      T.L2357.mp hs
    clear hs
    have hX : Q3.C e a t₀ row k2 st :=
      ⟨hC, hB, hr, hk2, hk0, hq, hu, hx, hsp, hfm, hk2v, hk1v, h110, hN1⟩
    have hN := hX.n1
    have hRs := hX.rc
    have hRg : Q3.Rg e a (k0N a row) k2 t₀ s₀ := ⟨h15, h12, h13⟩
    have hArr : A2.Arr fr 0x480 (A2.n1N e a (k0N a row) k2) 64
        (((k2 : Nat) : Int) - (((A2.k1Of (k0N a row) k2) : Nat) : Int)) := by
      have hk0' := k0Of_range hr hC.2.1
      have hb := ((a2_bands_of hB hC hr hk2 hk0 hq hu).2 h110).2.2
      refine a2_mb_arr hb ?_ hk2 (by omega) hMB (by omega)
      unfold A2.k1Of; split <;> omega
    have hn1lt : A2.n1N e a (k0N a row) k2 < 2 ^ 31 := by omega
    have hrcx : BitVec.signExtend 64 (BitVec.setWidth 32 (s₀.regs.get64 .r13))
        = BitVec.ofNat 64 (A2.n1N e a (k0N a row) k2) := by
      rw [h13]; exact a2_sext_ofNat _ hn1lt
    have e0 : s₀.regs.get64 .rbp + 18446744073709550224#64 = t₀.regs.get64 .rsp - 0x578#64 := by
      rw [hrbp]; bv_omega
    have e30 : s₀.regs.get64 .rbp + 18446744073709551568#64
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x30 := by rw [hrbp]; bv_omega
    have e50 : s₀.regs.get64 .rbp + 18446744073709551536#64
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x50 := by rw [hrbp]; bv_omega
    have hl50 := fr_load hm hF (d := 0x50) (n := 4) (by omega) (by omega)
    have hl0 := stk_load hm hF (o := 0) (by omega) (addr := t₀.regs.get64 .rsp - 0x578#64)
      (by simp)
    have hm1 := stk_store hm hF (o := 0) (by omega) (addr := t₀.regs.get64 .rsp - 0x578#64)
      (by simp) (s₀.regs.get64 .rbp + 18446744073709551378#64).toInt
    have hF1 := fr_wr_len hF (o := 0) (n := 8) (by omega)
      (s₀.regs.get64 .rbp + 18446744073709551378#64).toInt
    have hl30 := fr_load hm1 hF1 (d := 0x30) (n := 8) (by omega) (by omega)
    have hm2 := fr_store hm1 hF1 (d := 0x30) (n := 8) (by omega) (by omega)
      (BitVec.signExtend 64 (BitVec.setWidth 32 (s₀.regs.get64 .r13))).toInt
    have hF2 := fr_wr_len hF1 (o := rb 0x30) (n := 8) (by simp only [rb]; omega)
      (BitVec.signExtend 64 (BitVec.setWidth 32 (s₀.regs.get64 .r13))).toInt
    have hW2 : Q3.W e a t₀ (k0N a row) k2 (wr (wr fr 0
        (Int.toBytes 8 (s₀.regs.get64 .rbp + 18446744073709551378#64).toInt)) (rb 0x30)
        (Int.toBytes 8 (BitVec.signExtend 64 (BitVec.setWidth 32 (s₀.regs.get64 .r13))).toInt)) :=
        by
      have hn0 : A2.n0N e a (k0N a row) k2 ≤ 48 := by
        have := hN0.2.1; simp only [A2.n0N]; omega
      have hI1 := (Q3.inc_congr (fr := fr)
        (fr' := wr fr 0 (Int.toBytes 8 (s₀.regs.get64 .rbp + 18446744073709551378#64).toInt))
        (o := 0x400) fun j hj => by
          simp only [A2.fv]; rw [slice_wr_other hF (by omega) _ (by omega)]).mpr hInc
      have hT1 : A2.TA (wr fr 0
          (Int.toBytes 8 (s₀.regs.get64 .rbp + 18446744073709551378#64).toInt)) t₀
          (A2.n0N e a (k0N a row) k2) vm := by
        have hTA := hTB.1
        unfold A2.TA at *
        rw [slot_wr64 hF (by omega) _ (d := 0x40) (by simp only [rb]; omega),
          slot_wr64 hF (by omega) _ (d := 0x48) (by simp only [rb]; omega),
          slot_wr64 hF (by omega) _ (d := 0x88) (by simp only [rb]; omega),
          slot_wr32 hF (by omega) _ (d := 0x50) (by simp only [rb]; omega)]
        exact hTA
      exact Q3.w_set30 hF1 hN0 hI1 hv1 hv2 hT1 (by rw [BitVec.ofInt_toInt, hrcx])
    have hA2 : A2.Arr (wr (wr fr 0
        (Int.toBytes 8 (s₀.regs.get64 .rbp + 18446744073709551378#64).toInt)) (rb 0x30)
        (Int.toBytes 8 (BitVec.signExtend 64 (BitVec.setWidth 32 (s₀.regs.get64 .r13))).toInt))
        0x480 (A2.n1N e a (k0N a row) k2) 64
        (((k2 : Nat) : Int) - ((A2.k1Of (k0N a row) k2 : Nat) : Int)) :=
      (Q3.arr_wr hF1 (by simp only [rb]; omega) _ (by omega)
        (Or.inr (by simp only [rb]; omega))).mpr
        ((Q3.arr_wr hF (by omega) _ (by omega) (Or.inl (by omega))).mpr hArr)
    have h570 : frSlot64 (wr (wr fr 0
        (Int.toBytes 8 (s₀.regs.get64 .rbp + 18446744073709551378#64).toInt)) (rb 0x30)
        (Int.toBytes 8 (BitVec.signExtend 64 (BitVec.setWidth 32 (s₀.regs.get64 .r13))).toInt))
        0x570 = QS.pA t₀ 0x480 := by
      rw [slot_wr64 hF1 (by simp only [rb]; omega) _ (by simp only [rb]; omega),
        slot_wr_same hF (d := 0x570) (by omega) (by simp only [rb]), BitVec.ofInt_toInt, hrbp]
      simp only [QS.pA]; bv_omega
    have hv2' : BitVec.setWidth 64 18446744073709551614#64
        + (s₀.regs.get64 .rbp + 18446744073709551378#64
          + BitVec.signExtend 64 (BitVec.setWidth 32 (s₀.regs.get64 .r13)) * 2#64)
        = QS.ep t₀ 0x480 (A2.n1N e a (k0N a row) k2) - 2#64 := by
      rw [hrcx, hrbp]
      simp only [QS.ep, QS.pA, BitVec.setWidth_eq]
      have h48 : A2.n1N e a (k0N a row) k2 ≤ 48 := hN.2
      generalize A2.n1N e a (k0N a row) k2 = n at h48 ⊢
      bv_omega
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L2357]
    vcgen
    all_goals subst s₀
    all_goals subst hP
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceMod,
        Nat.reducePow, Nat.reduceSub, e0, e30, e50]
    · rw [hl50]; rfl
    · left; apply Table.ofLabels_at
      refine ⟨by decide, T.L25ca.mpr ⟨row, k2, hr, hk2, hk0, hq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st, fr,
        hx, hsp, hfm, hF, ⟨hk2v, hk1v, h110, hInc, hN0, hN1, ?_, hMB, ?_, ?_, vm, hv1, hv2, hTB,
          h30, ?_⟩, hm⟩⟩, ?_⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12,
        h13, h15]
      · bv_omega
      · edge_step
    · rw [hl0]; rfl
    · rw [hl30]; rfl
    refine ⟨T.L237d.mpr (Q3.g_iff.mpr ⟨row, k2, st, _, hX, ⟨?_, ?_⟩, (by q3_rg hRg), hF2, hW2,
      hm2, h570, ?_, hA2⟩), ?_⟩
    · regs_simp; exact hrsp
    · regs_simp; exact hrbp
    · regs_simp; exact hv2'
    · var_step


set_option maxRecDepth 100000 in
theorem blk_L237d (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L237d" ⟨"sbr_reset.L237d", B.L237d, some "sbr_reset.L2390"⟩ := by
  info_off
  measure_hb "L237d"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    subst hn
    obtain ⟨row, k2, st, fr, hX, ⟨hrsp, hrbp⟩, hRg, hF, hWf, hm, h570, hax, hArr⟩ :=
      Q3.g_iff.mp (T.L237d.mp hs)
    clear hs
    have hN := hX.n1
    have e8 : s₀.regs.get64 .rbp + 18446744073709550232#64
        = t₀.regs.get64 .rsp - 0x578#64 + (8 : BitVec 64) := by rw [hrbp]; bv_omega
    have hl8 := stk_load hm hF (o := 8) (by omega) (addr := t₀.regs.get64 .rsp - 0x578#64 + 8)
      rfl
    have hm1 := stk_store hm hF (o := 8) (by omega) (addr := t₀.regs.get64 .rsp - 0x578#64 + 8)
      rfl (s₀.regs.get64 .rax).toInt
    have hF1 := fr_wr_len hF (o := 8) (n := 8) (by omega) (s₀.regs.get64 .rax).toInt
    have hW1 := (Q3.w_wr hF (o := 8) (n := 8) (by omega) (s₀.regs.get64 .rax).toInt
      (Or.inl (by omega))).mpr hWf
    have hA1 := (Q3.arr_wr hF (o := 8) (n := 8) (by omega) (s₀.regs.get64 .rax).toInt
      (by omega) (Or.inl (by omega))).mpr hArr
    have hSR : QS.StkRel (wr fr 8 (Int.toBytes 8 (s₀.regs.get64 .rax).toInt)) t₀ 0x480
        [(0, A2.n1N e a (k0N a row) k2)] := by
      refine stkRel_push (S := []) (fun j h => absurd h (by simp)) ?_ ?_
      · simp only [List.length_nil, Nat.mul_zero, Nat.sub_zero]
        rw [slot_wr64 hF (by omega) _ (by simp only [rb]; omega), h570]
        simp only [QS.ep, Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
      · rw [slot_wr_same hF (by omega) (by simp only [rb, List.length_nil] <;> omega),
          BitVec.ofInt_toInt, hax]
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L237d]
    vcgen
    all_goals subst s₀
    all_goals subst hP
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, Nat.reduceMod, Nat.reducePow, Nat.reduceSub, e8]
    · exact (show (loadInt _ (t₀.regs.get64 .rsp - 0x578#64 + 8) 8).isSome = true by
        rw [hl8]; rfl)
    left; apply Table.ofLabels_at
    refine ⟨by decide, T.L2398.mpr (Q3.g_iff.mpr ⟨row, k2, st, _, hX, ⟨?_, ?_⟩, (by q3_rg hRg),
      hF1, hW1, hm1, ⟨Nat.le_of_succ_le hN.1, Nat.le_succ_of_le hN.2,
        [(0, A2.n1N e a (k0N a row) k2)], _, ?_, depth_init (Nat.le_of_succ_le hN.1),
        ab_of_arr hA1, hSR, qw_init _ _⟩, ?_⟩), ?_⟩
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrsp, hrbp]; done)
    · simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      rfl
    · simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      decide
    · edge_step

end Kraken.Examples.Sbr.Reset
