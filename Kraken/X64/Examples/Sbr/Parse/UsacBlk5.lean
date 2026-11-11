import Kraken.X64.Examples.Sbr.Parse.UsacBlk4
import Kraken.X64.Examples.Sbr.Parse.UsacTbl3
import Kraken.X64.Examples.Sbr.Parse.UsacTbl4
import Kraken.X64.Examples.Sbr.Parse.UsacTbl5
import Kraken.X64.Examples.Sbr.Parse.UsacTbl6
open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse
set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true
/-! # `ff_aac_sbr_decode_usac_data`: the tests of `read_sbr_grid`'s result

`mov %eax,%ecx; mov $-1,%eax; test %ecx,%ecx; jne L3ef1`: a nonzero result returns `-1`;
zero gives the channel's `Live`. -/
namespace Kraken.Examples.Sbr.Usac
variable [CodeEnv]

/-- `read_sbr_grid` ≠ 0 → return −1; single channel element. -/
theorem blk_L3621 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L3621" := by
  cfg_block
  measure_hb "L3621"
    intro n
    simp only [tbl_L3621, var_L3621]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨h, rfl⟩ := hs₀
    obtain ⟨⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, ⟨⟨hmi, hid, hu⟩, hl⟩, hm⟩, h15⟩, hch⟩ := h
    vcgen
    all_goals try subst_vars
    case vc1 af hs =>
      left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, ?_⟩
      rotate_left
      · first
        | exact Or.inl (by rw [var_L3ef1]; decide)
        | exact Or.inr ⟨by rw [var_L3ef1], by decide⟩
      · rw [tbl_L3ef1]
        refine ⟨hF,
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact hsp), st, ?_, hm⟩
        unfold UsacOut
        refine ⟨hmi, fun h0 => ?_, hI⟩
        simp only [Reg64s.get64_set64, ite_true, sw6432] at h0
        exact absurd h0 (by decide)
    case vc2 af hs =>
      simp only [CondCode.interp_nz, StatusFlags.zf_from_result, Reg64s.get64_set64, reduceCtorEq,
        ite_true, ite_false, BitVec.and_self, sw6432, Bool.not_eq_false', beq_iff_eq,
        show BitVec.zero 32 = 0#32 from rfl] at hs
      refine ⟨?_, by rw [var_L3630]; decide⟩
      rw [tbl_L3630]
      exact ⟨⟨⟨hF, ⟨
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact hsp),
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact hbp),
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact h12),
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact hbx),
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact h14)⟩,
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact h13),
        st, hI, ⟨⟨hmi, hid, hu⟩, hl hs⟩, hm⟩,
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact h15)⟩, hch⟩

/-- `read_sbr_grid` ≠ 0 → return −1; coupled pair. -/
theorem blk_L3715 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L3715" := by
  cfg_block
  measure_hb "L3715"
    intro n
    simp only [tbl_L3715, var_L3715]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨h, rfl⟩ := hs₀
    obtain ⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, ⟨⟨hmi, hid, hu⟩, hcp, hl⟩, hm⟩, h15⟩ := h
    vcgen
    all_goals try subst_vars
    case vc1 af hs =>
      left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, ?_⟩
      rotate_left
      · first
        | exact Or.inl (by rw [var_L3ef1]; decide)
        | exact Or.inr ⟨by rw [var_L3ef1], by decide⟩
      · rw [tbl_L3ef1]
        refine ⟨hF,
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact hsp), st, ?_, hm⟩
        unfold UsacOut
        refine ⟨hmi, fun h0 => ?_, hI⟩
        simp only [Reg64s.get64_set64, ite_true, sw6432] at h0
        exact absurd h0 (by decide)
    case vc2 af hs =>
      simp only [CondCode.interp_nz, StatusFlags.zf_from_result, Reg64s.get64_set64, reduceCtorEq,
        ite_true, ite_false, BitVec.and_self, sw6432, Bool.not_eq_false', beq_iff_eq,
        show BitVec.zero 32 = 0#32 from rfl] at hs
      refine ⟨?_, by rw [var_L3724]; decide⟩
      rw [tbl_L3724]
      exact ⟨⟨hF, ⟨
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact hsp),
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact hbp),
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact h12),
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact hbx),
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact h14)⟩,
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact h13),
        st, hI, ⟨⟨⟨hmi, hid, hu⟩, hl hs⟩, hcp⟩, hm⟩,
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact h15)⟩

/-- `read_sbr_grid` (channel 0) ≠ 0 → return −1; channel pair. -/
theorem blk_L394e (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L394e" := by
  cfg_block
  measure_hb "L394e"
    intro n
    simp only [tbl_L394e, var_L394e]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨h, rfl⟩ := hs₀
    obtain ⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, ⟨⟨hmi, hid, hu⟩, hl⟩, hm⟩, h15⟩ := h
    vcgen
    all_goals try subst_vars
    case vc1 af hs =>
      left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, ?_⟩
      rotate_left
      · first
        | exact Or.inl (by rw [var_L3ef1]; decide)
        | exact Or.inr ⟨by rw [var_L3ef1], by decide⟩
      · rw [tbl_L3ef1]
        refine ⟨hF,
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact hsp), st, ?_, hm⟩
        unfold UsacOut
        refine ⟨hmi, fun h0 => ?_, hI⟩
        simp only [Reg64s.get64_set64, ite_true, sw6432] at h0
        exact absurd h0 (by decide)
    case vc2 af hs =>
      simp only [CondCode.interp_nz, StatusFlags.zf_from_result, Reg64s.get64_set64, reduceCtorEq,
        ite_true, ite_false, BitVec.and_self, sw6432, Bool.not_eq_false', beq_iff_eq,
        show BitVec.zero 32 = 0#32 from rfl] at hs
      refine ⟨?_, by rw [var_L395d]; decide⟩
      rw [tbl_L395d]
      exact ⟨⟨hF, ⟨
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact hsp),
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact hbp),
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact h12),
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact hbx),
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact h14)⟩,
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact h13),
        st, hI, ⟨⟨hmi, hid, hu⟩, hl hs⟩, hm⟩,
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact h15)⟩

/-- `read_sbr_grid` (channel 1) ≠ 0 → return −1; channel pair. -/
theorem blk_L3972 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L3972" := by
  cfg_block
  measure_hb "L3972"
    intro n
    simp only [tbl_L3972, var_L3972]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨h, rfl⟩ := hs₀
    obtain ⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, ⟨⟨⟨hmi, hid, hu⟩, hl0⟩, hl⟩, hm⟩, h15⟩ := h
    vcgen
    all_goals try subst_vars
    case vc1 af hs =>
      left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, ?_⟩
      rotate_left
      · first
        | exact Or.inl (by rw [var_L3ef1]; decide)
        | exact Or.inr ⟨by rw [var_L3ef1], by decide⟩
      · rw [tbl_L3ef1]
        refine ⟨hF,
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact hsp), st, ?_, hm⟩
        unfold UsacOut
        refine ⟨hmi, fun h0 => ?_, hI⟩
        simp only [Reg64s.get64_set64, ite_true, sw6432] at h0
        exact absurd h0 (by decide)
    case vc2 af hs =>
      simp only [CondCode.interp_nz, StatusFlags.zf_from_result, Reg64s.get64_set64, reduceCtorEq,
        ite_true, ite_false, BitVec.and_self, sw6432, Bool.not_eq_false', beq_iff_eq,
        show BitVec.zero 32 = 0#32 from rfl] at hs
      refine ⟨?_, by rw [var_L3981]; decide⟩
      rw [tbl_L3981]
      exact ⟨⟨hF, ⟨
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact hsp),
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact hbp),
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact h12),
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact hbx),
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact h14)⟩,
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact h13),
        st, hI, ⟨⟨hmi, hid, hu⟩, hl0, hl hs⟩, hm⟩,
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact h15)⟩

end Kraken.Examples.Sbr.Usac
