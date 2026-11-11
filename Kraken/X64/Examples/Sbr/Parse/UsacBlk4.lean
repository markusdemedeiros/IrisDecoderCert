import Kraken.X64.Examples.Sbr.Parse.UsacBlk2
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
/-! # `ff_aac_sbr_decode_usac_data`: the tests of the callees' results

`test %eax,%eax; js`: a negative result returns it (`UsacOut` holds: `ret ≠ 0`); otherwise
the state passes on unchanged. -/
namespace Kraken.Examples.Sbr.Usac
variable [CodeEnv]

omit [CodeEnv] in
/-- A negative value is not zero. -/
theorem msb_ne0 {v : BitVec 32} (h : v.msb = true) : v ≠ 0#32 := by
  intro e; subst e; simp at h

/-- `read_sbr_envelope` < 0 → return; single channel element. -/
theorem blk_L3666 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L3666" := by
  cfg_block
  measure_hb "L3666"
    intro n
    simp only [tbl_L3666, var_L3666]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨h, rfl⟩ := hs₀
    have h' := h
    obtain ⟨⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, ⟨⟨hmi, hid, hu⟩, hl⟩, hm⟩, h15⟩, hch⟩ := h
    vcgen
    all_goals try subst_vars
    case vc1 af hs =>
      simp only [CondCode.interp_s, StatusFlags.sf_from_result, BitVec.and_self] at hs
      left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, ?_⟩
      rotate_left
      · first
        | exact Or.inl (by rw [var_L3ef1]; decide)
        | exact Or.inr ⟨by rw [var_L3ef1], by decide⟩
      · rw [tbl_L3ef1]
        exact ⟨hF, hsp, st, by unfold UsacOut; exact ⟨hmi, fun h0 => (msb_ne0 hs h0).elim, hI⟩, hm⟩
    case vc2 =>
      exact ⟨by rw [tbl_L366e]; exact h', by rw [var_L366e]; decide⟩

/-- `read_sbr_noise` < 0 → return; single channel element (`LiveC`: `idAac = 0`). -/
theorem blk_L3682 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L3682" := by
  cfg_block
  measure_hb "L3682"
    intro n
    simp only [tbl_L3682, var_L3682]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨h, rfl⟩ := hs₀
    have h' := h
    obtain ⟨⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, ⟨⟨hmi, hid, hu⟩, hl⟩, hm⟩, h15⟩, hch⟩ := h
    vcgen
    all_goals try subst_vars
    case vc1 af hs =>
      simp only [CondCode.interp_s, StatusFlags.sf_from_result, BitVec.and_self] at hs
      left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, ?_⟩
      rotate_left
      · first
        | exact Or.inl (by rw [var_L3aac]; decide)
        | exact Or.inr ⟨by rw [var_L3aac], by decide⟩
      · rw [tbl_L3aac]
        exact ⟨hF, hsp, st, by unfold UsacOut; exact ⟨hmi, fun h0 => (msb_ne0 hs h0).elim, hI⟩, hm⟩
    case vc2 =>
      refine ⟨?_, by rw [var_L368a]; decide⟩
      rw [tbl_L368a]
      exact ⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI,
        ⟨hmi, fun _ => hl, fun h => absurd h.2 (by rw [hid, hch]; decide)⟩, hm⟩

/-- `read_sbr_envelope` (channel 0) < 0 → return; channel pair. -/
theorem blk_L3874 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L3874" := by
  cfg_block
  measure_hb "L3874"
    intro n
    simp only [tbl_L3874, var_L3874]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨h, rfl⟩ := hs₀
    have h' := h
    obtain ⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, ⟨⟨hmi, hid, hu⟩, hl0, hl1⟩, hm⟩, h15⟩ := h
    vcgen
    all_goals try subst_vars
    case vc1 af hs =>
      simp only [CondCode.interp_s, StatusFlags.sf_from_result, BitVec.and_self] at hs
      left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, ?_⟩
      rotate_left
      · first
        | exact Or.inl (by rw [var_L3ef1]; decide)
        | exact Or.inr ⟨by rw [var_L3ef1], by decide⟩
      · rw [tbl_L3ef1]
        exact ⟨hF, hsp, st, by unfold UsacOut; exact ⟨hmi, fun h0 => (msb_ne0 hs h0).elim, hI⟩, hm⟩
    case vc2 =>
      exact ⟨by rw [tbl_L387c]; exact h', by rw [var_L387c]; decide⟩

/-- `read_sbr_noise` (channel 0) < 0 → return; channel pair. -/
theorem blk_L3890 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L3890" := by
  cfg_block
  measure_hb "L3890"
    intro n
    simp only [tbl_L3890, var_L3890]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨h, rfl⟩ := hs₀
    have h' := h
    obtain ⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, ⟨⟨hmi, hid, hu⟩, hl0, hl1⟩, hm⟩, h15⟩ := h
    vcgen
    all_goals try subst_vars
    case vc1 af hs =>
      simp only [CondCode.interp_s, StatusFlags.sf_from_result, BitVec.and_self] at hs
      left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, ?_⟩
      rotate_left
      · first
        | exact Or.inl (by rw [var_L3ef1]; decide)
        | exact Or.inr ⟨by rw [var_L3ef1], by decide⟩
      · rw [tbl_L3ef1]
        exact ⟨hF, hsp, st, by unfold UsacOut; exact ⟨hmi, fun h0 => (msb_ne0 hs h0).elim, hI⟩, hm⟩
    case vc2 =>
      exact ⟨by rw [tbl_L3898]; exact h', by rw [var_L3898]; decide⟩

/-- `read_sbr_envelope` (channel 1) < 0 → return; channel pair. -/
theorem blk_L38b6 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L38b6" := by
  cfg_block
  measure_hb "L38b6"
    intro n
    simp only [tbl_L38b6, var_L38b6]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨h, rfl⟩ := hs₀
    have h' := h
    obtain ⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, ⟨⟨hmi, hid, hu⟩, hl0, hl1⟩, hm⟩, h15⟩ := h
    vcgen
    all_goals try subst_vars
    case vc1 af hs =>
      simp only [CondCode.interp_s, StatusFlags.sf_from_result, BitVec.and_self] at hs
      left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, ?_⟩
      rotate_left
      · first
        | exact Or.inl (by rw [var_L3ef1]; decide)
        | exact Or.inr ⟨by rw [var_L3ef1], by decide⟩
      · rw [tbl_L3ef1]
        exact ⟨hF, hsp, st, by unfold UsacOut; exact ⟨hmi, fun h0 => (msb_ne0 hs h0).elim, hI⟩, hm⟩
    case vc2 =>
      exact ⟨by rw [tbl_L38be]; exact h', by rw [var_L38be]; decide⟩

/-- `read_sbr_envelope` (channel 0) < 0 → return; coupled pair. -/
theorem blk_L39ec (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L39ec" := by
  cfg_block
  measure_hb "L39ec"
    intro n
    simp only [tbl_L39ec, var_L39ec]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨h, rfl⟩ := hs₀
    have h' := h
    obtain ⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, ⟨⟨hmi, hid, hu⟩, hl0, hl1⟩, hm⟩, h15⟩ := h
    vcgen
    all_goals try subst_vars
    case vc1 af hs =>
      simp only [CondCode.interp_s, StatusFlags.sf_from_result, BitVec.and_self] at hs
      left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, ?_⟩
      rotate_left
      · first
        | exact Or.inl (by rw [var_L3ef1]; decide)
        | exact Or.inr ⟨by rw [var_L3ef1], by decide⟩
      · rw [tbl_L3ef1]
        exact ⟨hF, hsp, st, by unfold UsacOut; exact ⟨hmi, fun h0 => (msb_ne0 hs h0).elim, hI⟩, hm⟩
    case vc2 =>
      exact ⟨by rw [tbl_L39f4]; exact h', by rw [var_L39f4]; decide⟩

/-- `read_sbr_envelope` (channel 1) < 0 → return; coupled pair. -/
theorem blk_L3a0f (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L3a0f" := by
  cfg_block
  measure_hb "L3a0f"
    intro n
    simp only [tbl_L3a0f, var_L3a0f]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨h, rfl⟩ := hs₀
    have h' := h
    obtain ⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, ⟨⟨hmi, hid, hu⟩, hl0, hl1⟩, hm⟩, h15⟩ := h
    vcgen
    all_goals try subst_vars
    case vc1 af hs =>
      simp only [CondCode.interp_s, StatusFlags.sf_from_result, BitVec.and_self] at hs
      left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, ?_⟩
      rotate_left
      · first
        | exact Or.inl (by rw [var_L3ef1]; decide)
        | exact Or.inr ⟨by rw [var_L3ef1], by decide⟩
      · rw [tbl_L3ef1]
        exact ⟨hF, hsp, st, by unfold UsacOut; exact ⟨hmi, fun h0 => (msb_ne0 hs h0).elim, hI⟩, hm⟩
    case vc2 =>
      exact ⟨by rw [tbl_L3a17]; exact h', by rw [var_L3a17]; decide⟩

/-- `read_sbr_noise` (channel 0) < 0 → return; coupled pair. -/
theorem blk_L3a2b (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L3a2b" := by
  cfg_block
  measure_hb "L3a2b"
    intro n
    simp only [tbl_L3a2b, var_L3a2b]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨h, rfl⟩ := hs₀
    have h' := h
    obtain ⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, ⟨⟨hmi, hid, hu⟩, hl0, hl1⟩, hm⟩, h15⟩ := h
    vcgen
    all_goals try subst_vars
    case vc1 af hs =>
      simp only [CondCode.interp_s, StatusFlags.sf_from_result, BitVec.and_self] at hs
      left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, ?_⟩
      rotate_left
      · first
        | exact Or.inl (by rw [var_L3ef1]; decide)
        | exact Or.inr ⟨by rw [var_L3ef1], by decide⟩
      · rw [tbl_L3ef1]
        exact ⟨hF, hsp, st, by unfold UsacOut; exact ⟨hmi, fun h0 => (msb_ne0 hs h0).elim, hI⟩, hm⟩
    case vc2 =>
      exact ⟨by rw [tbl_L3a33]; exact h', by rw [var_L3a33]; decide⟩

/-- `read_sbr_noise` (channel 1) < 0 → return; channel pair (`LiveC`). -/
theorem blk_L38d5 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L38d5" := by
  cfg_block
  measure_hb "L38d5"
    intro n
    simp only [tbl_L38d5, var_L38d5]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨h, rfl⟩ := hs₀
    have h' := h
    obtain ⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, ⟨⟨hmi, hid, hu⟩, hl0, hl1⟩, hm⟩ := h
    vcgen
    all_goals try subst_vars
    case vc1 af hs =>
      simp only [CondCode.interp_s, StatusFlags.sf_from_result, BitVec.and_self] at hs
      left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, ?_⟩
      rotate_left
      · first
        | exact Or.inl (by rw [var_L3ef1]; decide)
        | exact Or.inr ⟨by rw [var_L3ef1], by decide⟩
      · rw [tbl_L3ef1]
        exact ⟨hF, hsp, st, by unfold UsacOut; exact ⟨hmi, fun h0 => (msb_ne0 hs h0).elim, hI⟩, hm⟩
    case vc2 =>
      refine ⟨?_, by rw [var_L38dd]; decide⟩
      rw [tbl_L38dd]
      exact ⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI,
        ⟨hmi, fun _ => hl0, fun _ => hl1⟩, hm⟩

/-- `read_sbr_noise` (channel 1) < 0 → return; coupled pair (`LiveC`). -/
theorem blk_L3a4e (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L3a4e" := by
  cfg_block
  measure_hb "L3a4e"
    intro n
    simp only [tbl_L3a4e, var_L3a4e]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨h, rfl⟩ := hs₀
    have h' := h
    obtain ⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, ⟨⟨hmi, hid, hu⟩, hl0, hl1⟩, hm⟩, h15⟩ := h
    vcgen
    all_goals try subst_vars
    case vc1 af hs =>
      simp only [CondCode.interp_s, StatusFlags.sf_from_result, BitVec.and_self] at hs
      left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, ?_⟩
      rotate_left
      · first
        | exact Or.inl (by rw [var_L3ef1]; decide)
        | exact Or.inr ⟨by rw [var_L3ef1], by decide⟩
      · rw [tbl_L3ef1]
        exact ⟨hF, hsp, st, by unfold UsacOut; exact ⟨hmi, fun h0 => (msb_ne0 hs h0).elim, hI⟩, hm⟩
    case vc2 =>
      refine ⟨?_, by rw [var_L3a56]; decide⟩
      rw [tbl_L3a56]
      exact ⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI,
        ⟨hmi, fun _ => hl0, fun _ => hl1⟩, hm⟩

end Kraken.Examples.Sbr.Usac
