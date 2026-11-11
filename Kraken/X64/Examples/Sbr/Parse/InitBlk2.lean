import Kraken.X64.Examples.Sbr.Parse.InitMem

/-!
# `ff_aac_sbr_ctx_alloc_init`: the test of the allocation and the first stores
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr
open Kraken.Examples.Sbr.Apply (c8)
open Kraken.Examples.Sbr.Session (zs)

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Init

variable [CodeEnv]

theorem blk_L22 (k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (TxTab X : Mem 64 → Prop)
    (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ctx TxTab X R ra t₀ "ff_aac_sbr_ctx_alloc_init.L22" := by
  cfg_block
  measure_hb "L22"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hR, hbx, hm⟩, hn⟩ := hs₀
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    · rename_i hz
      left
      refine ⟨"ff_aac_sbr_ctx_alloc_init.L17a", rfl, by decide, ⟨hR, ?_⟩, Or.inr ⟨rfl, by decide⟩⟩
      rcases hm with ⟨-, hm⟩ | ⟨h, -⟩
      · exact hm
      · simp [CondCode.interp, StatusFlags.from_result] at hz
        exact absurd hz h
    · rename_i hz
      rcases hm with ⟨h, -⟩ | ⟨h, hm⟩
      · simp [CondCode.interp, StatusFlags.from_result, h] at hz
      · exact ⟨⟨hR, hbx, h, hm⟩, Nat.le_refl 0⟩

theorem blk_L2b (k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (TxTab X : Mem 64 → Prop)
    (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ctx TxTab X R ra t₀ "ff_aac_sbr_ctx_alloc_init.L2b" := by
  cfg_block
  measure_hb "L2b"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hR, hbx, hax, hm⟩, hn⟩ := hs₀
    obtain ⟨hok1, hok2, hfin⟩ := L2b_mem hR.2.2.2.1 hm
    clear hm
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try simp only [Int64.toBitVec_ofNat_norm, BitVec.add_zero, BitVec.setWidth_eq]
    · exact hok1
    · exact hok2
    · exact ⟨⟨hR, hfin⟩, Nat.le_refl 0⟩

theorem blk_L3e (k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (TxTab X : Mem 64 → Prop)
    (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ctx TxTab X R ra t₀ "ff_aac_sbr_ctx_alloc_init.L3e" := by
  cfg_block
  measure_hb "L3e"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hR, hm⟩, hn⟩ := hs₀
    rw [M_BE0] at hm
    have hok1 : (s₀.dmem.loadInt (rbx s₀ + 0x13c00#64) 8).isSome = true := by
      rw [ElemS_ld_pr1 hm rfl]; rfl
    have h1 := fun w => ElemS_st_pr1 hm rfl w
    have hld : ∀ w, (s₀.dmem.storeInt (rbx s₀ + 0x13c00#64) 8 w).loadInt (rbx s₀ + 0x28978#64) 4
        = some 0 := fun w => by rw [ElemS_ld_kx1 (h1 w) rfl]; rfl
    have hok3 : ∀ w, ((s₀.dmem.storeInt (rbx s₀ + 0x13c00#64) 8 w).loadInt
        (rbx s₀ + 0x28974#64) 4).isSome = true := fun w => by rw [ElemS_ld_kx0 (h1 w) rfl]; rfl
    have hfin := fun w1 w2 => BE0_st (ElemS_st_kx0 (h1 w1) rfl w2)
    clear hm h1
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try simp only [Int64.toBitVec_ofNat_norm, BitVec.add_zero, BitVec.setWidth_eq] at *
    all_goals try simp only [hld, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp only
      [show (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.ofInt 32 0))).toInt = 0 by decide]
    · exact hok1
    · exact hok3 _
    · exact ⟨⟨hR, hfin _ _⟩, Nat.le_refl 0⟩

end Kraken.Examples.Sbr.Init
