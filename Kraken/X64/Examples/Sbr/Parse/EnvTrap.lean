import Kraken.X64.Examples.Sbr.Parse.EnvBase

/-!
# `read_sbr_envelope`: the trap blocks

The `ud1` blocks (the sanitizer's traps: array bounds, shift exponent) have the assertion
`False`: their obligations hold trivially, and every edge into them is shown not taken at its
source.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.Env

variable [CodeEnv]

theorem blk_L60b8 (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L60b8" := by
  cfg_block
  intro n
  exact Triple.pin fun _ h => h.1.elim

theorem blk_L60bd (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L60bd" := by
  cfg_block
  intro n
  exact Triple.pin fun _ h => h.1.elim

theorem blk_L60c2 (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L60c2" := by
  cfg_block
  intro n
  exact Triple.pin fun _ h => h.1.elim

theorem blk_L60c7 (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L60c7" := by
  cfg_block
  intro n
  exact Triple.pin fun _ h => h.1.elim

theorem blk_L60cc (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L60cc" := by
  cfg_block
  intro n
  exact Triple.pin fun _ h => h.1.elim

theorem blk_L60d1 (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L60d1" := by
  cfg_block
  intro n
  exact Triple.pin fun _ h => h.1.elim

theorem blk_L60d6 (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L60d6" := by
  cfg_block
  intro n
  exact Triple.pin fun _ h => h.1.elim

theorem blk_L60db (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L60db" := by
  cfg_block
  intro n
  exact Triple.pin fun _ h => h.1.elim

theorem blk_L60e0 (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L60e0" := by
  cfg_block
  intro n
  exact Triple.pin fun _ h => h.1.elim

theorem blk_L60e5 (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L60e5" := by
  cfg_block
  intro n
  exact Triple.pin fun _ h => h.1.elim

theorem blk_L60ea (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L60ea" := by
  cfg_block
  intro n
  exact Triple.pin fun _ h => h.1.elim

theorem blk_L60ef (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L60ef" := by
  cfg_block
  intro n
  exact Triple.pin fun _ h => h.1.elim

theorem blk_L60f4 (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L60f4" := by
  cfg_block
  intro n
  exact Triple.pin fun _ h => h.1.elim

theorem blk_L60f9 (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L60f9" := by
  cfg_block
  intro n
  exact Triple.pin fun _ h => h.1.elim

end Kraken.Examples.Sbr.Env
