import Kraken.X64.Examples.Sbr.Parse.ResetQs1Lib

/-!
# `sbr_reset`, `AV_QSORT` copy 1 (`stop_dk`): the entry (`L12ba`)

`L12ba` saves the end pointer (stack slot 1; the start pointer is in slot 0) and enters the loop
with one pending interval.
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
theorem blk_L12ba (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L12ba" ⟨"sbr_reset.L12ba", B.L12ba, some "sbr_reset.L12d0"⟩ := by
  info_off
  measure_hb "L12ba"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    subst hn
    obtain ⟨⟨row, hr, hsp1, hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF, ⟨h40, h30, h570⟩,
      hm⟩, hax⟩ := T.L12ba.mp hs
    clear hs
    have hRs : 0x578 ≤ (t₀.regs.get64 .rsp).toNat := by
      have := rsp_ok hC; unfold resetStkMin at this; omega
    have e8 : s₀.regs.get64 .rbp + 18446744073709550232#64
        = t₀.regs.get64 .rsp - 0x578#64 + (8 : BitVec 64) := by rw [hrbp]; bv_omega
    have hl8 := stk_load hm hF (o := 8) (by omega) (addr := t₀.regs.get64 .rsp - 0x578#64 + 8)
      rfl
    have hm1 := stk_store hm hF (o := 8) (by omega) (addr := t₀.regs.get64 .rsp - 0x578#64 + 8)
      rfl (s₀.regs.get64 .rax).toInt
    have hF1 := fr_wr_len hF (o := 8) (n := 8) (by omega) (s₀.regs.get64 .rax).toInt
    have h40' : frSlot64 (wr fr 8 (Int.toBytes 8 (s₀.regs.get64 .rax).toInt)) 0x40 = arg0 t₀ := by
      rw [slot_wr64 hF (by omega) _ (by simp only [rb]; omega), h40]
    have h30' : frSlot64 (wr fr 8 (Int.toBytes 8 (s₀.regs.get64 .rax).toInt)) 0x30 = arg1 t₀ := by
      rw [slot_wr64 hF (by omega) _ (by simp only [rb]; omega), h30]
    have hSR : QS.StkRel (wr fr 8 (Int.toBytes 8 (s₀.regs.get64 .rax).toInt)) t₀ 0x4fe
        [(0, 13)] := by
      refine stkRel_push (S := []) (fun j h => absurd h (by simp)) ?_ ?_
      · simp only [List.length_nil, Nat.mul_zero, Nat.sub_zero]
        rw [slot_wr64 hF (by omega) _ (by simp only [rb]; omega), h570]
        simp only [QS.ep, QS.pA]; bv_omega
      · rw [slot_wr_same hF (by omega) (by simp only [rb, List.length_nil] <;> omega),
          BitVec.ofInt_toInt, hax]
        simp only [QS.ep, QS.pA]; bv_omega
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L12ba]
    vcgen
    all_goals subst s₀
    all_goals subst hP
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, Nat.reduceMod, Nat.reducePow, Nat.reduceSub, e8]
    · exact (show (loadInt _ (t₀.regs.get64 .rsp - 0x578#64 + 8) 8).isSome = true by
        rw [hl8]; rfl)
    left; apply Table.ofLabels_at
    refine ⟨by decide, T.L12d8.mpr ⟨row, hr, hsp1, hC, hBO, ⟨?_, ?_⟩, st, _, hx, hsp, hfm, hF1,
      ⟨h40', h30', ⟨by decide, by decide, [(0, 13)], _, ?_, depth_init (by decide), trivial, hSR,
        qw_init _ _⟩, ?_⟩, hm1⟩, ?_⟩
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrsp, hrbp]; done)
    · simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      rfl
    · simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      decide
    · edge_step

end Kraken.Examples.Sbr.Reset
