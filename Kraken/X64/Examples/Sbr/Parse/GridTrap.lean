import Kraken.X64.Examples.Sbr.Parse.GridBase

/-!
# `read_sbr_grid`: the trap blocks

The `ud1` blocks (the compiler's traps for undefined behaviour) have the assertion `False`:
their obligations hold trivially, and every edge into them is shown not taken at its source.
The same for the blocks that are not reached for other reasons: the VARVAR border steps past
`bs_num_rel_0 ≤ 3` (`L4a37` to `L4b9f`), `bs_num_env = 0` in the tail (`L4f51`), and the end
of the border chain (`L506a`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.Grid

variable [CodeEnv]

theorem blk_L50ca (k : Nat) (Ext : Mem 64 → Prop) (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L50ca" := by
  cfg_block
  intro n
  exact Triple.pin fun _ h => h.1.elim

theorem blk_L50cf (k : Nat) (Ext : Mem 64 → Prop) (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L50cf" := by
  cfg_block
  intro n
  exact Triple.pin fun _ h => h.1.elim

theorem blk_L50d4 (k : Nat) (Ext : Mem 64 → Prop) (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L50d4" := by
  cfg_block
  intro n
  exact Triple.pin fun _ h => h.1.elim

theorem blk_L50d9 (k : Nat) (Ext : Mem 64 → Prop) (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L50d9" := by
  cfg_block
  intro n
  exact Triple.pin fun _ h => h.1.elim

theorem blk_L50de (k : Nat) (Ext : Mem 64 → Prop) (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L50de" := by
  cfg_block
  intro n
  exact Triple.pin fun _ h => h.1.elim

theorem blk_L50e3 (k : Nat) (Ext : Mem 64 → Prop) (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L50e3" := by
  cfg_block
  intro n
  exact Triple.pin fun _ h => h.1.elim

theorem blk_L5113 (k : Nat) (Ext : Mem 64 → Prop) (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L5113" := by
  cfg_block
  intro n
  exact Triple.pin fun _ h => h.1.elim

theorem blk_L5118 (k : Nat) (Ext : Mem 64 → Prop) (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L5118" := by
  cfg_block
  intro n
  exact Triple.pin fun _ h => h.1.elim

theorem blk_L511d (k : Nat) (Ext : Mem 64 → Prop) (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L511d" := by
  cfg_block
  intro n
  exact Triple.pin fun _ h => h.1.elim

theorem blk_L5122 (k : Nat) (Ext : Mem 64 → Prop) (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L5122" := by
  cfg_block
  intro n
  exact Triple.pin fun _ h => h.1.elim

theorem blk_L5127 (k : Nat) (Ext : Mem 64 → Prop) (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L5127" := by
  cfg_block
  intro n
  exact Triple.pin fun _ h => h.1.elim

theorem blk_L512c (k : Nat) (Ext : Mem 64 → Prop) (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L512c" := by
  cfg_block
  intro n
  exact Triple.pin fun _ h => h.1.elim

theorem blk_L5131 (k : Nat) (Ext : Mem 64 → Prop) (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L5131" := by
  cfg_block
  intro n
  exact Triple.pin fun _ h => h.1.elim

theorem blk_L5136 (k : Nat) (Ext : Mem 64 → Prop) (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L5136" := by
  cfg_block
  intro n
  exact Triple.pin fun _ h => h.1.elim

theorem blk_L513b (k : Nat) (Ext : Mem 64 → Prop) (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L513b" := by
  cfg_block
  intro n
  exact Triple.pin fun _ h => h.1.elim

theorem blk_L4a37 (k : Nat) (Ext : Mem 64 → Prop) (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4a37" := by
  cfg_block
  intro n
  exact Triple.pin fun _ h => h.1.elim

theorem blk_L4a6b (k : Nat) (Ext : Mem 64 → Prop) (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4a6b" := by
  cfg_block
  intro n
  exact Triple.pin fun _ h => h.1.elim

theorem blk_L4a85 (k : Nat) (Ext : Mem 64 → Prop) (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4a85" := by
  cfg_block
  intro n
  exact Triple.pin fun _ h => h.1.elim

theorem blk_L4ab9 (k : Nat) (Ext : Mem 64 → Prop) (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4ab9" := by
  cfg_block
  intro n
  exact Triple.pin fun _ h => h.1.elim

theorem blk_L4ad3 (k : Nat) (Ext : Mem 64 → Prop) (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4ad3" := by
  cfg_block
  intro n
  exact Triple.pin fun _ h => h.1.elim

theorem blk_L4b07 (k : Nat) (Ext : Mem 64 → Prop) (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4b07" := by
  cfg_block
  intro n
  exact Triple.pin fun _ h => h.1.elim

theorem blk_L4b21 (k : Nat) (Ext : Mem 64 → Prop) (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4b21" := by
  cfg_block
  intro n
  exact Triple.pin fun _ h => h.1.elim

theorem blk_L4b55 (k : Nat) (Ext : Mem 64 → Prop) (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4b55" := by
  cfg_block
  intro n
  exact Triple.pin fun _ h => h.1.elim

theorem blk_L4b6b (k : Nat) (Ext : Mem 64 → Prop) (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4b6b" := by
  cfg_block
  intro n
  exact Triple.pin fun _ h => h.1.elim

theorem blk_L4b9f (k : Nat) (Ext : Mem 64 → Prop) (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4b9f" := by
  cfg_block
  intro n
  exact Triple.pin fun _ h => h.1.elim

theorem blk_L4f51 (k : Nat) (Ext : Mem 64 → Prop) (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4f51" := by
  cfg_block
  intro n
  exact Triple.pin fun _ h => h.1.elim

theorem blk_L506a (k : Nat) (Ext : Mem 64 → Prop) (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L506a" := by
  cfg_block
  intro n
  exact Triple.pin fun _ h => h.1.elim

end Kraken.Examples.Sbr.Grid
