import Kraken.X64.Examples.Sbr.Parse.GridMem

/-!
# `read_sbr_grid`: sample blocks of each kind

One proved block per kind of the open obligations (see the work list): a register-only jump into
the `bs_freq_res` fill (`L4ca9`), the returns `0` after the `e_a` stores (`L4fae`, `L4f93`), the
call of `abort` (`L510e`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Grid

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

/-- `xor %eax,%eax; jmp L4e73`: the single `get_bits1` of `bs_freq_res[1]` for `n = 1`. -/
theorem blk_L4ca9 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4ca9" := by
  cfg_block
  measure_hb "L4ca9"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, ⟨hsp, hbp, h13, hbx⟩, hdx, hdi, st, ⟨hF, hn1⟩, hm⟩, hn⟩ := hs₀
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64] at *
    left; apply Table.ofLabels_at
    dsimp only [reduceTable, reduceVar]
    simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, BitVec.xor_self,
      BitVec.setWidth_zero, BitVec.toNat_zero, Nat.zero_add]
    have hf0 : u8 st.fr 0 ≤ 1 := hF.1.2.2.2.2.2.2.2.2
    refine ⟨by decide, ⟨hC, ⟨hsp, hbp, h13, hbx⟩, hdx, hdi, st, ⟨hF, ?_, ?_⟩, hmT⟩,
      by edge_lt⟩
    · rw [hn1]; rfl
    · intro e he
      rw [Nat.le_zero.mp he]; exact hf0

/-- `call abort` (the `av_assert0` of the pointer read): an exit. -/
theorem blk_L510e (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L510e" := by
  cfg_block
  measure_hb "L510e"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hsp, st, hm⟩, hn⟩ := hs₀
    vcgen [call_abort_at]
    refine ⟨fun _ => Or.inr (Or.inr rfl), ?_⟩
    subst_vars
    dsimp only
    have e : t₀.regs.get64 .rsp - 40#64 - BitVec.ofNat 64 8 = t₀.regs.get64 .rsp - 48#64 := by
      bv_omega
    rw [hsp, e]
    grind_cells'

omit [CodeEnv] in
theorem gridOut_ok {x : GArgs} {st : GSt} (hD : DWF False (st.dv x)) (hL : Live st)
    (hI : st.i.toNat ≤ x.p8.toNat) : GridOut x st 0#32 :=
  ⟨hD, hL.2.1 _ (Nat.le_refl _), Or.inl rfl, fun _ => ⟨hL.1, hL.2.1, hL.2.2⟩, hI⟩

/-- `bs_frame_class == VARFIX`, `bs_pointer ≥ 2`: `e_a[1] = bs_pointer - 1`, return 0. -/
theorem blk_L4fae (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4fae" := by
  cfg_block
  measure_hb "L4fae"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨hsp, hbp, h13, hbx⟩, st, ⟨hD, hL, hI⟩, hm⟩, hn⟩ := hs₀
    have hs1 := fun v => T_store_ea1 hm v
    have ld := T_load_ea1 hm 4 (Nat.le_refl _)
    have hmT : Hide _ := hm
    have pbx : PLift (s₀.regs.get64 .rbx = arg3 t₀) := ⟨hbx⟩
    clear hm
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, hbx] at *
    all_goals try with_reducible exact ld
    all_goals (left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar])
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, BitVec.xor_self,
      BitVec.setWidth_zero]
    all_goals refine ⟨by decide, ⟨hC, hsp, h13, st, gridOut_ok hD hL hI, ?_⟩, by edge_lt⟩
    all_goals first | exact hmT | exact hs1 _

/-- `bs_pointer ≠ 0`, `bs_frame_class` odd: `e_a[1] = num_env + 1 - bs_pointer`, return 0. -/
theorem blk_L4f93 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4f93" := by
  cfg_block
  measure_hb "L4f93"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨hsp, hbp, h13, hbx⟩, st, ⟨hD, hL, hI⟩, hm⟩, hn⟩ := hs₀
    have hs1 := fun v => T_store_ea1 hm v
    have ld := T_load_ea1 hm 4 (Nat.le_refl _)
    have hmT : Hide _ := hm
    have pbx : PLift (s₀.regs.get64 .rbx = arg3 t₀) := ⟨hbx⟩
    clear hm
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, hbx] at *
    all_goals try with_reducible exact ld
    all_goals (left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar])
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, BitVec.xor_self,
      BitVec.setWidth_zero]
    all_goals first
      | refine ⟨by decide, ⟨hC, hsp, h13, st, gridOut_ok hD hL hI, ?_⟩, by edge_lt⟩
      | refine ⟨by decide, ⟨hC, ⟨hsp, hbp, h13, pbx.down⟩, st, ⟨hD, hL, hI⟩, ?_⟩, by edge_lt⟩
    all_goals first | exact hmT | exact hs1 _

end Kraken.Examples.Sbr.Grid
