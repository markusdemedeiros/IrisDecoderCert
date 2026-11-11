import Kraken.X64.Examples.Sbr.Parse.TlimBase

/-!
# `sbr_make_f_tablelim`: the trap blocks

The `ud1` blocks (the compiler's traps for undefined behaviour) have the assertion `False`:
their obligations hold trivially, and every edge into them is shown not taken at its source.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.Tlim

variable [CodeEnv]

theorem blk_L4385 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "sbr_make_f_tablelim.L4385" := by
  cfg_block
  intro n
  exact Triple.pin fun _ h => h.1.elim

theorem blk_L43cd (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "sbr_make_f_tablelim.L43cd" := by
  cfg_block
  intro n
  exact Triple.pin fun _ h => h.1.elim

theorem blk_L43d2 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "sbr_make_f_tablelim.L43d2" := by
  cfg_block
  intro n
  exact Triple.pin fun _ h => h.1.elim

theorem blk_L43d7 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "sbr_make_f_tablelim.L43d7" := by
  cfg_block
  intro n
  exact Triple.pin fun _ h => h.1.elim

theorem blk_L43dc (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "sbr_make_f_tablelim.L43dc" := by
  cfg_block
  intro n
  exact Triple.pin fun _ h => h.1.elim

theorem blk_L43e1 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "sbr_make_f_tablelim.L43e1" := by
  cfg_block
  intro n
  exact Triple.pin fun _ h => h.1.elim

theorem blk_L43e6 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "sbr_make_f_tablelim.L43e6" := by
  cfg_block
  intro n
  exact Triple.pin fun _ h => h.1.elim

theorem blk_L43eb (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "sbr_make_f_tablelim.L43eb" := by
  cfg_block
  intro n
  exact Triple.pin fun _ h => h.1.elim

theorem blk_L43f0 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "sbr_make_f_tablelim.L43f0" := by
  cfg_block
  intro n
  exact Triple.pin fun _ h => h.1.elim

end Kraken.Examples.Sbr.Tlim
