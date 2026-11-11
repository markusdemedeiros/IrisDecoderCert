import Kraken.InfoOff
import Kraken.Rules.HbOptApply
import Kraken.X64.Examples.Sbr.ApplyTable

/-! # `ff_aac_sbr_apply`: blocks of shard `Trap` -/

open Kraken Kraken.X64.Parser Std.WP MachineWP Kraken.SysV Mem
open scoped Kraken.FrameLemmas.Int32Nat
set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.Apply

variable [CodeEnv]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L6ff7 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6ff7" ⟨"ff_aac_sbr_apply.L6ff7", B.L6ff7, some "ff_aac_sbr_apply.L6ffc"⟩ := by
  info_off
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  exact (T.L6ff7.mp hs₀.1).elim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L99e9 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L99e9" ⟨"ff_aac_sbr_apply.L99e9", B.L99e9, some "ff_aac_sbr_apply.L99ee"⟩ := by
  info_off
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  exact (T.L99e9.mp hs₀.1).elim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L99ee (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L99ee" ⟨"ff_aac_sbr_apply.L99ee", B.L99ee, some "ff_aac_sbr_apply.L99f3"⟩ := by
  info_off
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  exact (T.L99ee.mp hs₀.1).elim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L99f3 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L99f3" ⟨"ff_aac_sbr_apply.L99f3", B.L99f3, some "ff_aac_sbr_apply.L99f8"⟩ := by
  info_off
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  exact (T.L99f3.mp hs₀.1).elim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L99f8 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L99f8" ⟨"ff_aac_sbr_apply.L99f8", B.L99f8, some "ff_aac_sbr_apply.L99fd"⟩ := by
  info_off
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  exact (T.L99f8.mp hs₀.1).elim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L99fd (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L99fd" ⟨"ff_aac_sbr_apply.L99fd", B.L99fd, some "ff_aac_sbr_apply.L9a02"⟩ := by
  info_off
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  exact (T.L99fd.mp hs₀.1).elim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9a50 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9a50" ⟨"ff_aac_sbr_apply.L9a50", B.L9a50, some "ff_aac_sbr_apply.L9a55"⟩ := by
  info_off
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  exact (T.L9a50.mp hs₀.1).elim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9a55 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9a55" ⟨"ff_aac_sbr_apply.L9a55", B.L9a55, some "ff_aac_sbr_apply.L9a5a"⟩ := by
  info_off
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  exact (T.L9a55.mp hs₀.1).elim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9a5a (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9a5a" ⟨"ff_aac_sbr_apply.L9a5a", B.L9a5a, some "ff_aac_sbr_apply.L9a5f"⟩ := by
  info_off
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  exact (T.L9a5a.mp hs₀.1).elim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9a5f (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9a5f" ⟨"ff_aac_sbr_apply.L9a5f", B.L9a5f, some "ff_aac_sbr_apply.L9a64"⟩ := by
  info_off
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  exact (T.L9a5f.mp hs₀.1).elim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9a64 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9a64" ⟨"ff_aac_sbr_apply.L9a64", B.L9a64, some "ff_aac_sbr_apply.L9a69"⟩ := by
  info_off
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  exact (T.L9a64.mp hs₀.1).elim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9b36 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9b36" ⟨"ff_aac_sbr_apply.L9b36", B.L9b36, some "ff_aac_sbr_apply.L9b3b"⟩ := by
  info_off
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  exact (T.L9b36.mp hs₀.1).elim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9b3b (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9b3b" ⟨"ff_aac_sbr_apply.L9b3b", B.L9b3b, some "ff_aac_sbr_apply.L9b40"⟩ := by
  info_off
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  exact (T.L9b3b.mp hs₀.1).elim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9b40 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9b40" ⟨"ff_aac_sbr_apply.L9b40", B.L9b40, some "ff_aac_sbr_apply.L9b45"⟩ := by
  info_off
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  exact (T.L9b40.mp hs₀.1).elim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9b45 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9b45" ⟨"ff_aac_sbr_apply.L9b45", B.L9b45, some "ff_aac_sbr_apply.L9b4a"⟩ := by
  info_off
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  exact (T.L9b45.mp hs₀.1).elim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9b4a (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9b4a" ⟨"ff_aac_sbr_apply.L9b4a", B.L9b4a, some "ff_aac_sbr_apply.L9b4f"⟩ := by
  info_off
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  exact (T.L9b4a.mp hs₀.1).elim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9b4f (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9b4f" ⟨"ff_aac_sbr_apply.L9b4f", B.L9b4f, some "ff_aac_sbr_apply.L9b54"⟩ := by
  info_off
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  exact (T.L9b4f.mp hs₀.1).elim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9b54 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9b54" ⟨"ff_aac_sbr_apply.L9b54", B.L9b54, some "ff_aac_sbr_apply.L9b59"⟩ := by
  info_off
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  exact (T.L9b54.mp hs₀.1).elim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9b59 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9b59" ⟨"ff_aac_sbr_apply.L9b59", B.L9b59, some "ff_aac_sbr_apply.L9b5e"⟩ := by
  info_off
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  exact (T.L9b59.mp hs₀.1).elim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9b5e (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9b5e" ⟨"ff_aac_sbr_apply.L9b5e", B.L9b5e, some "ff_aac_sbr_apply.L9b63"⟩ := by
  info_off
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  exact (T.L9b5e.mp hs₀.1).elim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9b63 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9b63" ⟨"ff_aac_sbr_apply.L9b63", B.L9b63, some "ff_aac_sbr_apply.L9b68"⟩ := by
  info_off
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  exact (T.L9b63.mp hs₀.1).elim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9b68 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9b68" ⟨"ff_aac_sbr_apply.L9b68", B.L9b68, some "ff_aac_sbr_apply.L9b6d"⟩ := by
  info_off
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  exact (T.L9b68.mp hs₀.1).elim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9b6d (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9b6d" ⟨"ff_aac_sbr_apply.L9b6d", B.L9b6d, some "ff_aac_sbr_apply.L9b72"⟩ := by
  info_off
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  exact (T.L9b6d.mp hs₀.1).elim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9b72 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9b72" ⟨"ff_aac_sbr_apply.L9b72", B.L9b72, some "ff_aac_sbr_apply.L9b77"⟩ := by
  info_off
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  exact (T.L9b72.mp hs₀.1).elim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9b77 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9b77" ⟨"ff_aac_sbr_apply.L9b77", B.L9b77, some "ff_aac_sbr_apply.L9b7c"⟩ := by
  info_off
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  exact (T.L9b77.mp hs₀.1).elim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9b7c (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9b7c" ⟨"ff_aac_sbr_apply.L9b7c", B.L9b7c, some "ff_aac_sbr_apply.L9b81"⟩ := by
  info_off
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  exact (T.L9b7c.mp hs₀.1).elim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9b81 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9b81" ⟨"ff_aac_sbr_apply.L9b81", B.L9b81, some "ff_aac_sbr_apply.L9b86"⟩ := by
  info_off
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  exact (T.L9b81.mp hs₀.1).elim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9b86 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9b86" ⟨"ff_aac_sbr_apply.L9b86", B.L9b86, some "ff_aac_sbr_apply.L9b8b"⟩ := by
  info_off
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  exact (T.L9b86.mp hs₀.1).elim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9b8b (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9b8b" ⟨"ff_aac_sbr_apply.L9b8b", B.L9b8b, some "ff_aac_sbr_apply.L9b90"⟩ := by
  info_off
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  exact (T.L9b8b.mp hs₀.1).elim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9b90 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9b90" ⟨"ff_aac_sbr_apply.L9b90", B.L9b90, some "ff_aac_sbr_apply.L9b95"⟩ := by
  info_off
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  exact (T.L9b90.mp hs₀.1).elim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9b95 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9b95" ⟨"ff_aac_sbr_apply.L9b95", B.L9b95, some "ff_aac_sbr_apply.L9b9a"⟩ := by
  info_off
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  exact (T.L9b95.mp hs₀.1).elim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9b9a (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9b9a" ⟨"ff_aac_sbr_apply.L9b9a", B.L9b9a, some "ff_aac_sbr_apply.L9b9a_1"⟩ := by
  info_off
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  exact (T.L9b9a.mp hs₀.1).elim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9b9a_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9b9a_1" ⟨"ff_aac_sbr_apply.L9b9a_1", B.L9b9a_1, some "ff_aac_sbr_apply.L9bc5"⟩ := by
  info_off
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  exact (T.L9b9a_1.mp hs₀.1).elim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9bc5 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9bc5" ⟨"ff_aac_sbr_apply.L9bc5", B.L9bc5, some "ff_aac_sbr_apply.L9bca"⟩ := by
  info_off
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  exact (T.L9bc5.mp hs₀.1).elim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9bca (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9bca" ⟨"ff_aac_sbr_apply.L9bca", B.L9bca, some "ff_aac_sbr_apply.L9bcf"⟩ := by
  info_off
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  exact (T.L9bca.mp hs₀.1).elim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9bcf (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9bcf" ⟨"ff_aac_sbr_apply.L9bcf", B.L9bcf, some "ff_aac_sbr_apply.L9bd4"⟩ := by
  info_off
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  exact (T.L9bcf.mp hs₀.1).elim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9bd4 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9bd4" ⟨"ff_aac_sbr_apply.L9bd4", B.L9bd4, some "ff_aac_sbr_apply.L9bd4_1"⟩ := by
  info_off
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  exact (T.L9bd4.mp hs₀.1).elim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9bd4_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9bd4_1" ⟨"ff_aac_sbr_apply.L9bd4_1", B.L9bd4_1, some "ff_aac_sbr_apply.L9bff"⟩ := by
  info_off
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  exact (T.L9bd4_1.mp hs₀.1).elim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9bff (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9bff" ⟨"ff_aac_sbr_apply.L9bff", B.L9bff, some "ff_aac_sbr_apply.L9c04"⟩ := by
  info_off
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  exact (T.L9bff.mp hs₀.1).elim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9c04 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9c04" ⟨"ff_aac_sbr_apply.L9c04", B.L9c04, some "ff_aac_sbr_apply.L9c09"⟩ := by
  info_off
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  exact (T.L9c04.mp hs₀.1).elim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9c09 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9c09" ⟨"ff_aac_sbr_apply.L9c09", B.L9c09, some "ff_aac_sbr_apply.L9c0e"⟩ := by
  info_off
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  exact (T.L9c09.mp hs₀.1).elim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9c0e (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9c0e" ⟨"ff_aac_sbr_apply.L9c0e", B.L9c0e, some "ff_aac_sbr_apply.L9c13"⟩ := by
  info_off
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  exact (T.L9c0e.mp hs₀.1).elim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9c13 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9c13" ⟨"ff_aac_sbr_apply.L9c13", B.L9c13, some "ff_aac_sbr_apply.L9c18"⟩ := by
  info_off
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  exact (T.L9c13.mp hs₀.1).elim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9c18 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9c18" ⟨"ff_aac_sbr_apply.L9c18", B.L9c18, some "ff_aac_sbr_apply.L9c1d"⟩ := by
  info_off
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  exact (T.L9c18.mp hs₀.1).elim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9c1d (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9c1d" ⟨"ff_aac_sbr_apply.L9c1d", B.L9c1d, some "ff_aac_sbr_apply.L9c22"⟩ := by
  info_off
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  exact (T.L9c1d.mp hs₀.1).elim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9c22 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9c22" ⟨"ff_aac_sbr_apply.L9c22", B.L9c22, some "ff_aac_sbr_apply.L9c27"⟩ := by
  info_off
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  exact (T.L9c22.mp hs₀.1).elim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9c27 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9c27" ⟨"ff_aac_sbr_apply.L9c27", B.L9c27, none⟩ := by
  info_off
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  exact (T.L9c27.mp hs₀.1).elim

end Kraken.Examples.Sbr.Apply
