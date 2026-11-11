import Kraken.X64.Examples.Sbr.Parse.GridBase

/-!
# `read_sbr_grid`: the entry blocks (prologue, the copies of `bs_freq_res[bs_num_env]` and
`t_env[bs_num_env]`, `bs_frame_class`, the dispatch)
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Grid

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

theorem blk_entry (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid" := by
  cfg_block
  measure_hb "entry"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨rfl, hC, hm⟩, hn⟩ := hs₀
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals try simp only [BitVec.sub_sub_eight, BitVec.reduceAdd] at *
    all_goals grind_cells'

/-- `mov 0x8(%rcx),%r14d; cmp $0x9,%r14; jae <trap>`. -/
theorem blk_L440b (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L440b" := by
  cfg_block
  measure_hb "L440b"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hR, hcx, hm⟩, hn⟩ := hs₀
    have hn8 : x.v.nenv ≤ 8 := hC.1.2.2.2.2.1
    have hz := zx_small x.v.nenv (by omega)
    simp only [T, GFB, ChB, GArgs.st] at hm
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals try simp only [T, GFB, ChB, GArgs.st] at *
    case vc2 =>
      -- the trap edge: `bs_num_env ≤ 8` contradicts the taken `jae`
      exfalso
      grind_cells'
    all_goals grind_cells'

/-- `mov %rcx,%rbx; movzbl 0xc(%rcx,%r14,1),%eax`: `bs_freq_res[bs_num_env]`, at a variable
index, from the once-proved `FrB_loadInt`. -/
theorem blk_L4419 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4419" := by
  cfg_block
  measure_hb "L4419"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hR, hcx, h14, hm⟩, hn⟩ := hs₀
    have hn8 : x.v.nenv ≤ 8 := hC.1.2.2.2.2.1
    have hm' := hm
    rw [T_fr] at hm'
    have hld := FrB_loadInt hm' x.v.nenv (by omega)
    clear hm'
    simp only [GArgs.st, bv] at hld
    have hz := zx8
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals grind_cells'

end Kraken.Examples.Sbr.Grid
