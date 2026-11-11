import Kraken.X64.Examples.Sbr.Parse.ResetA1Lib
import Kraken.X64.Examples.Sbr.Parse.ResetModel

/-!
# `sbr_reset`: the failure exits of shard A1 (to the `av_log` at `L1d2a`)
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Reset

variable [CodeEnv]

theorem blk_L1762 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1762" ⟨"sbr_reset.L1762", B.L1762, some "sbr_reset.L1779"⟩ := by
  info_off
  measure_hb "L1762"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hC, ⟨hrsp, hrbp⟩, h12, h15, st, fr, hM, hsp, hfm, hF, hm⟩ := T.L1762.mp hs
    clear hs
    have hav : st.x.avctx = a.x.avctx := (reset_keeps hM).2.2
    have ld1 := avctx_load hm
    simp only [arg0] at ld1
    rw [hav] at ld1
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L1762]
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    · simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h15, AddrIndex.offset64_none,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, ld1, Option.isSome_some]
    · rename_i _ hl
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h15, AddrIndex.offset64_none,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at hl
      rw [ld1] at hl
      obtain rfl := Option.some.inj hl
      refine Or.inl (Table.ofLabels_at ⟨S.L1d2a, T.L1d2a.mpr ⟨⟨hC, ⟨?_, ?_⟩, ?_, ?_, st, fr, hM, hsp, hfm, hF, hm⟩, ?_⟩, by edge_step⟩)
      all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15,
        BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]

theorem blk_L17e7 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L17e7" ⟨"sbr_reset.L17e7", B.L17e7, some "sbr_reset.L17fc"⟩ := by
  info_off
  measure_hb "L17e7"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hC, ⟨hrsp, hrbp⟩, h12, h15, st, fr, hM, hsp, hfm, hF, hm⟩ := T.L17e7.mp hs
    clear hs
    have hav : st.x.avctx = a.x.avctx := (reset_keeps hM).2.2
    have ld1 := avctx_load hm
    simp only [arg0] at ld1
    rw [hav] at ld1
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L17e7]
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    · simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h15, AddrIndex.offset64_none,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, ld1, Option.isSome_some]
    · rename_i _ hl
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h15, AddrIndex.offset64_none,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at hl
      rw [ld1] at hl
      obtain rfl := Option.some.inj hl
      refine Or.inl (Table.ofLabels_at ⟨S.L1d2a, T.L1d2a.mpr ⟨⟨hC, ⟨?_, ?_⟩, ?_, ?_, st, fr, hM, hsp, hfm, hF, hm⟩, ?_⟩, by edge_step⟩)
      all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15,
        BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]

theorem blk_L1820 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1820" ⟨"sbr_reset.L1820", B.L1820, some "sbr_reset.L1830"⟩ := by
  info_off
  measure_hb "L1820"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨⟨⟨hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF, -, hm⟩, h12, h15, -⟩, hnone⟩ := T.L1820.mp hs
    clear hs
    have hM : Reset (spOf a) (lbN a) a.x st.x.turnoff := by
      rw [hx]; exact Reset.badRate hC.2.1 (Master.badRate hnone)
    have hav : st.x.avctx = a.x.avctx := by rw [hx]
    have ld1 := avctx_load hm
    simp only [arg0] at ld1
    rw [hav] at ld1
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L1820]
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    · simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h15, AddrIndex.offset64_none,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, ld1, Option.isSome_some]
    · rename_i _ hl
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h15, AddrIndex.offset64_none,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at hl
      rw [ld1] at hl
      obtain rfl := Option.some.inj hl
      refine Or.inl (Table.ofLabels_at ⟨S.L167a, T.L167a.mpr ⟨⟨hC, ⟨?_, ?_⟩, ?_, ?_, st, fr, hM, hsp, hfm, hF, hm⟩, ?_⟩, by edge_step⟩)
      all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15,
        BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]

/-- `esi = AV_LOG_ERROR`, `jmp L1d2a`. -/
theorem blk_L167a (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L167a" ⟨"sbr_reset.L167a", B.L167a, some "sbr_reset.L1684"⟩ := by
  info_off
  measure_hb "L167a"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hF, hdi⟩ := T.L167a.mp hs
    clear hs
    simp only [B.L167a]
    vcgen
    all_goals try subst_vars
    refine Or.inl (Table.ofLabels_at ⟨S.L1d2a, T.L1d2a.mpr ⟨AtFail.congr (by simp) (by simp) rfl
      (by simp) (by simp) hF, ?_⟩, by edge_step⟩)
    simpa using hdi

end Kraken.Examples.Sbr.Reset
