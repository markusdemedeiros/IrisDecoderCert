import Kraken.X64.Examples.Sbr.Parse.PsBase

/-!
# `ff_ps_read_data`: the trap blocks (`L1759`–`L17d1`)

The `ud1` blocks (the compiler's traps) have the assertion `False`: their obligations hold
trivially, and every edge into them is shown not taken at its source.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.Ps

variable [CodeEnv]

set_option maxRecDepth 20000 in
/-- Trap stub (`ud1`). -/
theorem blk_L1759 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L1759" := by
  cfg_block
  intro n
  simp only [tab_L1759]
  exact Triple.pin fun _ h => h.1.elim

set_option maxRecDepth 20000 in
/-- Trap stub (`ud1`). -/
theorem blk_L175e (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L175e" := by
  cfg_block
  intro n
  simp only [tab_L175e]
  exact Triple.pin fun _ h => h.1.elim

set_option maxRecDepth 20000 in
/-- Trap stub (`ud1`). -/
theorem blk_L1763 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L1763" := by
  cfg_block
  intro n
  simp only [tab_L1763]
  exact Triple.pin fun _ h => h.1.elim

set_option maxRecDepth 20000 in
/-- Trap stub (`ud1`). -/
theorem blk_L1768 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L1768" := by
  cfg_block
  intro n
  simp only [tab_L1768]
  exact Triple.pin fun _ h => h.1.elim

set_option maxRecDepth 20000 in
/-- Trap stub (`ud1`). -/
theorem blk_L176d (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L176d" := by
  cfg_block
  intro n
  simp only [tab_L176d]
  exact Triple.pin fun _ h => h.1.elim

set_option maxRecDepth 20000 in
/-- Trap stub (`ud1`). -/
theorem blk_L1772 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L1772" := by
  cfg_block
  intro n
  simp only [tab_L1772]
  exact Triple.pin fun _ h => h.1.elim

set_option maxRecDepth 20000 in
/-- Trap stub (`ud1`). -/
theorem blk_L1777 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L1777" := by
  cfg_block
  intro n
  simp only [tab_L1777]
  exact Triple.pin fun _ h => h.1.elim

set_option maxRecDepth 20000 in
/-- Trap stub (`ud1`). -/
theorem blk_L177c (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L177c" := by
  cfg_block
  intro n
  simp only [tab_L177c]
  exact Triple.pin fun _ h => h.1.elim

set_option maxRecDepth 20000 in
/-- Trap stub (`ud1`). -/
theorem blk_L1781 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L1781" := by
  cfg_block
  intro n
  simp only [tab_L1781]
  exact Triple.pin fun _ h => h.1.elim

set_option maxRecDepth 20000 in
/-- Trap stub (`ud1`). -/
theorem blk_L1786 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L1786" := by
  cfg_block
  intro n
  simp only [tab_L1786]
  exact Triple.pin fun _ h => h.1.elim

set_option maxRecDepth 20000 in
/-- Trap stub (`ud1`). -/
theorem blk_L178b (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L178b" := by
  cfg_block
  intro n
  simp only [tab_L178b]
  exact Triple.pin fun _ h => h.1.elim

set_option maxRecDepth 20000 in
/-- Trap stub (`ud1`). -/
theorem blk_L1790 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L1790" := by
  cfg_block
  intro n
  simp only [tab_L1790]
  exact Triple.pin fun _ h => h.1.elim

set_option maxRecDepth 20000 in
/-- Trap stub (`ud1`). -/
theorem blk_L1795 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L1795" := by
  cfg_block
  intro n
  simp only [tab_L1795]
  exact Triple.pin fun _ h => h.1.elim

set_option maxRecDepth 20000 in
/-- Trap stub (`ud1`). -/
theorem blk_L179a (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L179a" := by
  cfg_block
  intro n
  simp only [tab_L179a]
  exact Triple.pin fun _ h => h.1.elim

set_option maxRecDepth 20000 in
/-- Trap stub (`ud1`). -/
theorem blk_L179f (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L179f" := by
  cfg_block
  intro n
  simp only [tab_L179f]
  exact Triple.pin fun _ h => h.1.elim

set_option maxRecDepth 20000 in
/-- Trap stub (`ud1`). -/
theorem blk_L17a4 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L17a4" := by
  cfg_block
  intro n
  simp only [tab_L17a4]
  exact Triple.pin fun _ h => h.1.elim

set_option maxRecDepth 20000 in
/-- Trap stub (`ud1`). -/
theorem blk_L17a9 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L17a9" := by
  cfg_block
  intro n
  simp only [tab_L17a9]
  exact Triple.pin fun _ h => h.1.elim

set_option maxRecDepth 20000 in
/-- Trap stub (`ud1`). -/
theorem blk_L17ae (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L17ae" := by
  cfg_block
  intro n
  simp only [tab_L17ae]
  exact Triple.pin fun _ h => h.1.elim

set_option maxRecDepth 20000 in
/-- Trap stub (`ud1`). -/
theorem blk_L17b3 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L17b3" := by
  cfg_block
  intro n
  simp only [tab_L17b3]
  exact Triple.pin fun _ h => h.1.elim

set_option maxRecDepth 20000 in
/-- Trap stub (`ud1`). -/
theorem blk_L17b8 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L17b8" := by
  cfg_block
  intro n
  simp only [tab_L17b8]
  exact Triple.pin fun _ h => h.1.elim

set_option maxRecDepth 20000 in
/-- Trap stub (`ud1`). -/
theorem blk_L17bd (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L17bd" := by
  cfg_block
  intro n
  simp only [tab_L17bd]
  exact Triple.pin fun _ h => h.1.elim

set_option maxRecDepth 20000 in
/-- Trap stub (`ud1`). -/
theorem blk_L17c2 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L17c2" := by
  cfg_block
  intro n
  simp only [tab_L17c2]
  exact Triple.pin fun _ h => h.1.elim

set_option maxRecDepth 20000 in
/-- Trap stub (`ud1`). -/
theorem blk_L17c7 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L17c7" := by
  cfg_block
  intro n
  simp only [tab_L17c7]
  exact Triple.pin fun _ h => h.1.elim

set_option maxRecDepth 20000 in
/-- Trap stub (`ud1`). -/
theorem blk_L17cc (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L17cc" := by
  cfg_block
  intro n
  simp only [tab_L17cc]
  exact Triple.pin fun _ h => h.1.elim

set_option maxRecDepth 20000 in
/-- Trap stub (`ud1`). -/
theorem blk_L17d1 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L17d1" := by
  cfg_block
  intro n
  simp only [tab_L17d1]
  exact Triple.pin fun _ h => h.1.elim

end Kraken.Examples.Sbr.Ps
