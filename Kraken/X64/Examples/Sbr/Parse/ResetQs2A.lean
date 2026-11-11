import Kraken.X64.Examples.Sbr.Parse.ResetQsFr

/-!
# `sbr_reset`, `AV_QSORT` copy 2 (`vk0`): the pop (`L1980`, `L1988`)
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse Kraken.Examples.Sbr.Parse.Qsort

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Reset

variable [CodeEnv]

theorem blk_L1980 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1980" ⟨"sbr_reset.L1980", B.L1980, some "sbr_reset.L1988"⟩ := by
  info_off
  measure_hb "L1980"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hSF, hN0, h12, h15, hax, hN1, hN49, S, A0, hcx, hD, hR, hSR, hQ⟩, hm⟩⟩ :=
      T.L1980.mp hs
    clear hs
    have hS6 : S.length ≤ 6 := depth_len (m := 6) hD (by omega)
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L1980]
    vcgen
    all_goals try subst_vars
    all_goals rename_i c
    all_goals rw [hcx, cc_z_test32 _ (by omega)] at c
    all_goals simp only [decide_eq_true_eq, decide_eq_false_iff_not] at c
    · obtain rfl : S = [] := List.eq_nil_of_length_eq_zero c
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L1bbd.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩,
        st, fr, hx, hsp, hfm, hF, ⟨hk2v, hk1v, hSF, hN0, h12, h15, hax, arr_of_qw hR hQ⟩, hm⟩⟩,
        ?_⟩
      edge_step
    · refine ⟨T.L1988.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩,
        st, fr, hx, hsp, hfm, hF, ⟨hk2v, hk1v, hSF, hN0, h12, h15, hax,
          ⟨hN1, hN49, S, A0, hcx, hD, hR, hSR, hQ⟩, ?_⟩, hm⟩⟩, ?_⟩
      · rw [hcx]; intro h'
        have := congrArg BitVec.toNat h'
        simp only [BitVec.toNat_ofNat] at this; omega
      · var_step

theorem blk_L1988 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1988" ⟨"sbr_reset.L1988", B.L1988, some "sbr_reset.L19b0"⟩ := by
  info_off
  measure_hb "L1988"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hSF, hN0, h12, h15, hax, ⟨hN1, hN49, S, A0, hcx, hD, hR, hSR, hQ⟩, hc0⟩, hm⟩⟩ :=
      T.L1988.mp hs
    clear hs
    have hS6 : S.length ≤ 6 := depth_len (m := 6) hD (by omega)
    have hS1 : S ≠ [] := by rintro rfl; exact hc0 (by rw [hcx]; rfl)
    obtain ⟨S', I, rfl⟩ : ∃ S' I, S = S' ++ [I] :=
      ⟨S.dropLast, S.getLast hS1, (List.dropLast_concat_getLast hS1).symm⟩
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add] at hS6 hcx
    obtain ⟨hSR', r1, r2⟩ := stkRel_pop hSR
    obtain ⟨hD', hDc⟩ := depth_pop hD
    have hrs := rsp_ok hC
    have hv1 := stk_load hm hF (o := 16 * S'.length) (by omega)
      (addr := s₀.regs.get64 .rbp + BitVec.ofNat 64 (16 * S'.length) + 18446744073709550224#64)
      (by rw [hrbp]; exact stk_addr0 _ _)
    have hv2 := stk_load hm hF (o := 16 * S'.length + 8) (by omega)
      (addr := s₀.regs.get64 .rbp + BitVec.ofNat 64 (16 * S'.length) + 18446744073709550232#64)
      (by rw [hrbp]; exact stk_addr1 _ _)
    have e1 : BitVec.ofInt 64 (Int.ofBytes (slice fr (16 * S'.length) 8)) = QS.ep t₀ 0x400 I.1 := by
      rw [← r1]; simp only [frSlot64, rb]; congr 4; omega
    have e2 : BitVec.ofInt 64 (Int.ofBytes (slice fr (16 * S'.length + 8) 8))
        = QS.ep t₀ 0x400 I.2 - 2#64 := by
      rw [← r2]; simp only [frSlot64, rb]; congr 4; omega
    have hph : QS.stkPhi s₀ (S'.length + 1) = QS.stkPhi s₀ S'.length
        + wBn 2 (QS.ep t₀ 0x400 I.1).toNat (QS.ep t₀ 0x400 I.2 - 2#64).toNat := by
      rw [stkPhi_succ, slot64_fr hm hF hrbp (by omega) (by omega),
        slot64_fr hm hF hrbp (by omega) (by omega), r1, r2]
    have ed := qs_dec32 (S'.length + 1) (by omega) (by omega)
    simp only [Nat.add_sub_cancel] at ed
    have es := qs_shl4 S'.length
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L1988]
    vcgen
    all_goals try subst_vars
    all_goals simp only [AddrIndex.offset64_scale1, Int64.toBitVec_ofNat_norm,
      Int64.toBitVec_neg_ofNat_norm, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
      Nat.reduceSub, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, BitVec.ofNat_eq_ofNat, hcx, ed,
      es, hv1, hv2, Option.isSome_some, Option.some.injEq]
    · rename_i c
      simp only [hcx, Int64.toBitVec_ofNat_norm] at c
      rw [qs_nc32 _ _ (by omega) (by omega)] at c
      exfalso; simp at c; omega
    · rename_i c v1 hl1 v2 hl2
      simp only [AddrIndex.offset64_scale1, Int64.toBitVec_ofNat_norm,
        Int64.toBitVec_neg_ofNat_norm, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
        Nat.reduceSub, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, BitVec.ofNat_eq_ofNat, hcx, ed,
        es, hv1, hv2, Option.some.injEq] at hl1 hl2
      subst hl1 hl2
      refine ⟨T.L19b0.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st, fr, hx, hsp,
        hfm, hF, ⟨hk2v, hk1v, hSF, hN0, ?_, ?_, ?_, ⟨hN1, hN49, S', A0, I.1, I.2, ?_, hD', hDc, hR,
        hSR', hQ, ?_, ?_, trivial⟩⟩, hm⟩⟩, ?_⟩
      all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrsp, hrbp, h12, h15,
        hax, e1, e2]; done)
      simp only [lex_var, VD.L19b0, VD.L1988]
      refine lex_phase ?_ (by decide)
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      rw [stkPhi_mk _ _ _ _ (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]), hcx,
        BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega), hph, e1, e2]

end Kraken.Examples.Sbr.Reset
