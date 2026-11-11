import Kraken.X64.Examples.Sbr.Parse.ResetQs4Lib
import Kraken.X64.Examples.Sbr.Parse.ResetQs2J

/-!
# `sbr_reset`, `AV_QSORT` copy 4 (`vk1`): the entry (`L2619`, `L262c`)

`L2619` saves the start pointer (stack slot 0) and `num_bands_1` (`-0x30`) and computes the end
pointer; `L262c` saves it (stack slot 0) and enters the loop with one pending interval.
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
theorem blk_L2619 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2619" ⟨"sbr_reset.L2619", B.L2619, some "sbr_reset.L262c"⟩ := by
  info_off
  measure_hb "L2619"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    subst hn
    obtain ⟨row, k2, hr, hk2, hk0, hq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, h110, hInc, hN0, hN1, h15, h12, h13, vm, hTA, hax, hcx, hArr⟩, hm⟩⟩ :=
      T.L2619.mp hs
    clear hs
    have hX : Q4.C e a t₀ row k2 st :=
      ⟨hC, hB, hr, hk2, hk0, hq, hu, hx, hsp, hfm, hk2v, hk1v, h110, hN1⟩
    have hN := hX.n1
    have hRs := hX.rc
    have hRg : Q4.Rg e a (k0N a row) k2 t₀ s₀ := ⟨h15, h12, h13⟩
    have e0 : s₀.regs.get64 .rbp + 18446744073709550224#64 = t₀.regs.get64 .rsp - 0x578#64 := by
      rw [hrbp]; bv_omega
    have e30 : s₀.regs.get64 .rbp + 18446744073709551568#64
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x30 := by rw [hrbp]; bv_omega
    have hl0 := stk_load hm hF (o := 0) (by omega) (addr := t₀.regs.get64 .rsp - 0x578#64)
      (by simp)
    have hm1 := stk_store hm hF (o := 0) (by omega) (addr := t₀.regs.get64 .rsp - 0x578#64)
      (by simp) (s₀.regs.get64 .rax).toInt
    have hF1 := fr_wr_len hF (o := 0) (n := 8) (by omega) (s₀.regs.get64 .rax).toInt
    have hl30 := fr_load hm1 hF1 (d := 0x30) (n := 8) (by omega) (by omega)
    have hm2 := fr_store hm1 hF1 (d := 0x30) (n := 8) (by omega) (by omega)
      (s₀.regs.get64 .rcx).toInt
    have hF2 := fr_wr_len hF1 (o := rb 0x30) (n := 8) (by simp only [rb]; omega)
      (s₀.regs.get64 .rcx).toInt
    have hW2 : Q4.W e a t₀ (k0N a row) k2 (wr (wr fr 0 (Int.toBytes 8 (s₀.regs.get64 .rax).toInt))
        (rb 0x30) (Int.toBytes 8 (s₀.regs.get64 .rcx).toInt)) := by
      have hn0 : A2.n0N e a (k0N a row) k2 ≤ 48 := by
        have := hN0.2.1; simp only [A2.n0N]; omega
      have hI1 := (Q4.inc_congr (fr := fr)
        (fr' := wr fr 0 (Int.toBytes 8 (s₀.regs.get64 .rax).toInt))
        (o := 0x400) fun j hj => by
          simp only [A2.fv]; rw [slice_wr_other hF (by omega) _ (by omega)]).mpr hInc
      have hT1 : A2.TA (wr fr 0 (Int.toBytes 8 (s₀.regs.get64 .rax).toInt)) t₀
          (A2.n0N e a (k0N a row) k2) vm := by
        unfold A2.TA at *
        rw [slot_wr64 hF (by omega) _ (d := 0x40) (by simp only [rb]; omega),
          slot_wr64 hF (by omega) _ (d := 0x48) (by simp only [rb]; omega),
          slot_wr64 hF (by omega) _ (d := 0x88) (by simp only [rb]; omega),
          slot_wr32 hF (by omega) _ (d := 0x50) (by simp only [rb]; omega)]
        exact hTA
      exact Q4.w_set30 hF1 hN0 hI1 hT1 (by rw [BitVec.ofInt_toInt, hcx])
    have hA2 : A2.Arr (wr (wr fr 0 (Int.toBytes 8 (s₀.regs.get64 .rax).toInt))
        (rb 0x30) (Int.toBytes 8 (s₀.regs.get64 .rcx).toInt)) 0x480 (A2.n1N e a (k0N a row) k2) 256
        (((k2 : Nat) : Int) - ((A2.k1Of (k0N a row) k2 : Nat) : Int)) :=
      (Q4.arr_wr hF1 (by simp only [rb]; omega) _ (by omega)
        (Or.inr (by simp only [rb]; omega))).mpr
        ((Q4.arr_wr hF (by omega) _ (by omega) (Or.inl (by omega))).mpr hArr)
    have h570 : frSlot64 (wr (wr fr 0 (Int.toBytes 8 (s₀.regs.get64 .rax).toInt))
        (rb 0x30) (Int.toBytes 8 (s₀.regs.get64 .rcx).toInt)) 0x570 = QS.pA t₀ 0x480 := by
      rw [slot_wr64 hF1 (by simp only [rb]; omega) _ (by simp only [rb]; omega),
        slot_wr_same hF (d := 0x570) (by omega) (by simp only [rb]), BitVec.ofInt_toInt, hax, hrbp]
      have := (t₀.regs.get64 .rsp).isLt
      apply BitVec.eq_of_toNat_eq
      simp only [QS.pA, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    have hv2 : BitVec.setWidth 64 18446744073709551614#64 + (s₀.regs.get64 .rax
        + s₀.regs.get64 .rcx * 2#64) = QS.ep t₀ 0x480 (A2.n1N e a (k0N a row) k2) - 2#64 := by
      rw [hax, hcx, hrbp]
      have := (t₀.regs.get64 .rsp).isLt
      apply BitVec.eq_of_toNat_eq
      simp only [QS.ep, QS.pA, BitVec.setWidth_eq, BitVec.toNat_sub, BitVec.toNat_add,
        BitVec.toNat_mul, BitVec.toNat_ofNat]
      omega
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L2619]
    vcgen
    all_goals subst s₀
    all_goals subst hP
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceMod,
        Nat.reducePow, Nat.reduceSub, e0, e30]
    · rw [hl0]; rfl
    · rw [hl30]; rfl
    refine ⟨T.L262c.mpr (Q4.g_iff.mpr ⟨row, k2, st, _, hX, ⟨?_, ?_⟩, (by q4_rg hRg), hF2, hW2,
      hm2, h570, ?_, hA2⟩), ?_⟩
    · regs_simp; exact hrsp
    · regs_simp; exact hrbp
    · regs_simp; exact hv2
    · var_step

set_option maxRecDepth 100000 in
theorem blk_L262c (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L262c" ⟨"sbr_reset.L262c", B.L262c, some "sbr_reset.L2640"⟩ := by
  info_off
  measure_hb "L262c"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    subst hn
    obtain ⟨row, k2, st, fr, hX, ⟨hrsp, hrbp⟩, hRg, hF, hWf, hm, h570, hax, hArr⟩ :=
      Q4.g_iff.mp (T.L262c.mp hs)
    clear hs
    have hN := hX.n1
    have e8 : s₀.regs.get64 .rbp + 18446744073709550232#64
        = t₀.regs.get64 .rsp - 0x578#64 + (8 : BitVec 64) := by rw [hrbp]; bv_omega
    have hl8 := stk_load hm hF (o := 8) (by omega) (addr := t₀.regs.get64 .rsp - 0x578#64 + 8)
      rfl
    have hm1 := stk_store hm hF (o := 8) (by omega) (addr := t₀.regs.get64 .rsp - 0x578#64 + 8)
      rfl (s₀.regs.get64 .rax).toInt
    have hF1 := fr_wr_len hF (o := 8) (n := 8) (by omega) (s₀.regs.get64 .rax).toInt
    have hW1 := (Q4.w_wr hF (o := 8) (n := 8) (by omega) (s₀.regs.get64 .rax).toInt
      (Or.inl (by omega))).mpr hWf
    have hA1 := (Q4.arr_wr hF (o := 8) (n := 8) (by omega) (s₀.regs.get64 .rax).toInt
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
    simp only [B.L262c]
    vcgen
    all_goals subst s₀
    all_goals subst hP
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, Nat.reduceMod, Nat.reducePow, Nat.reduceSub, e8]
    · exact (show (loadInt _ (t₀.regs.get64 .rsp - 0x578#64 + 8) 8).isSome = true by
        rw [hl8]; rfl)
    left; apply Table.ofLabels_at
    refine ⟨by decide, T.L2648.mpr (Q4.g_iff.mpr ⟨row, k2, st, _, hX, ⟨?_, ?_⟩, (by q4_rg hRg),
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
