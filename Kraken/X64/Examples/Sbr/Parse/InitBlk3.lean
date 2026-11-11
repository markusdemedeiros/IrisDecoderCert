import Kraken.X64.Examples.Sbr.Parse.InitMem

/-!
# `ff_aac_sbr_ctx_alloc_init`: the stores of `sbr_turnoff` and the start values
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

theorem blk_L58 (k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (TxTab X : Mem 64 → Prop)
    (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ctx TxTab X R ra t₀ "ff_aac_sbr_ctx_alloc_init.L58" := by
  cfg_block
  measure_hb "L58"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hR, hm⟩, hn⟩ := hs₀
    rw [M_BE0] at hm
    have eid : (BitVec.setWidth 32 (s₀.regs.get64 .r14)).toInt = (idOf t₀).toInt := by
      rw [hR.2.2.1]; simp [idOf, BitVec.setWidth_setWidth_of_le]
    have hok1 : (s₀.dmem.loadInt (rbx s₀ + 0x2892c#64) 4).isSome = true := by
      rw [ElemS_ld_id hm rfl]; rfl
    have h1 := fun w => ElemS_st_id hm rfl w
    have hok2 : ∀ w, ((s₀.dmem.storeInt (rbx s₀ + 0x2892c#64) 4 w).loadInt
        (rbx s₀ + 0x28930#64) 4).isSome = true := fun w => by rw [ElemS_ld_usac (h1 w) rfl]; rfl
    have hfin : ∀ w1 w2, Int.toBytes 4 w1 = Int.toBytes 4 (idOf t₀).toInt
        → Int.toBytes 4 w2 = Int.toBytes 4 0
        → (s₀.dmem.storeInt (rbx s₀ + 0x2892c#64) 4 w1).storeInt (rbx s₀ + 0x28930#64) 4 w2
          =⋆ M k TxTab X R ra t₀ (BE0 t₀ (rbx s₀) (evC (rbx s₀) (idOf t₀))) := by
      intro w1 w2 e1 e2
      have h := BE0_st (ElemS_st_usac (h1 w1) rfl w2)
      rw [e1, e2] at h; exact h
    clear hm h1
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try simp only [Int64.toBitVec_ofNat_norm, AddrIndex.offset64_none,
      BitVec.add_zero, add0, BitVec.setWidth_eq] at *
    · exact hok1
    · exact hok2 _
    · exact ⟨⟨hR, by simp, hfin _ _ (by rw [eid]) (by simp)⟩, Nat.le_refl 0⟩

theorem blk_L67 (k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (TxTab X : Mem 64 → Prop)
    (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ctx TxTab X R ra t₀ "ff_aac_sbr_ctx_alloc_init.L67" := by
  cfg_block
  measure_hb "L67"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hR, hax, hm⟩, hn⟩ := hs₀
    rw [M_BE0] at hm
    have hok1 : (s₀.dmem.loadInt (rbx s₀ + 0x28924#64) 8).isSome = true := by
      rw [ElemS_ld_sr hm rfl]; rfl
    have h1 := fun w => ElemS_st_sr hm rfl w
    have hok2 : ∀ w, ((s₀.dmem.storeInt (rbx s₀ + 0x28924#64) 8 w).loadInt
        (rbx s₀ + 0x28978#64) 4).isSome = true := fun w => by rw [ElemS_ld_kx1 (h1 w) rfl]; rfl
    have hfin : ∀ w1 w2, Int.toBytes 8 w1 = Int.toBytes 8 0
        → Int.toBytes 4 w2 = Int.toBytes 4 32
        → (s₀.dmem.storeInt (rbx s₀ + 0x28924#64) 8 w1).storeInt (rbx s₀ + 0x28978#64) 4 w2
          =⋆ M k TxTab X R ra t₀ (BE0 t₀ (rbx s₀) (evD (rbx s₀) (idOf t₀))) := by
      intro w1 w2 e1 e2
      have h := BE0_st (ElemS_st_kx1 (h1 w1) rfl w2)
      rw [e1, e2] at h; exact h
    clear hm h1
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try simp only [Int64.toBitVec_ofNat_norm, AddrIndex.offset64_none,
      BitVec.add_zero, add0, BitVec.setWidth_eq] at *
    · exact hok1
    · trace_state
      exact hok2 _
    · exact ⟨⟨hR, hax, hfin _ _ (by rw [hax]; rfl) (by decide)⟩, Nat.le_refl 0⟩

theorem blk_L78 (k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (TxTab X : Mem 64 → Prop)
    (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ctx TxTab X R ra t₀ "ff_aac_sbr_ctx_alloc_init.L78" := by
  cfg_block
  measure_hb "L78"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hR, hax, hm⟩, hn⟩ := hs₀
    rw [M_BE0] at hm
    have hok1 : (s₀.dmem.loadInt (rbx s₀ + 0x28980#64) 4).isSome = true := by
      rw [ElemS_ld_m1 hm rfl]; rfl
    have h1 := fun w => ElemS_st_m1 hm rfl w
    have hok2 : ∀ w, ((s₀.dmem.storeInt (rbx s₀ + 0x28980#64) 4 w).loadInt
        (rbx s₀ + 0x41d68#64) 4).isSome = true := fun w => by rw [ElemS_ld_e1 (h1 w) rfl]; rfl
    have hfin : ∀ w1 w2, Int.toBytes 4 w1 = Int.toBytes 4 0
        → Int.toBytes 4 w2 = Int.toBytes 4 (-1)
        → (s₀.dmem.storeInt (rbx s₀ + 0x28980#64) 4 w1).storeInt (rbx s₀ + 0x41d68#64) 4 w2
          =⋆ M k TxTab X R ra t₀ (BE0 t₀ (rbx s₀) (evE (rbx s₀) (idOf t₀))) := by
      intro w1 w2 e1 e2
      have h := BE0_st (ElemS_st_e1 (h1 w1) rfl w2)
      rw [e1, e2] at h; exact h
    clear hm h1
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try simp only [Int64.toBitVec_ofNat_norm, AddrIndex.offset64_none,
      BitVec.add_zero, add0, BitVec.setWidth_eq] at *
    · exact hok1
    · exact hok2 _
    · exact ⟨⟨hR, hax, by decide, hfin _ _ (by rw [hax]; rfl) (by decide)⟩, Nat.le_refl 0⟩

theorem blk_L89 (k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (TxTab X : Mem 64 → Prop)
    (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ctx TxTab X R ra t₀ "ff_aac_sbr_ctx_alloc_init.L89" := by
  cfg_block
  measure_hb "L89"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hR, hax, hcx, hm⟩, hn⟩ := hs₀
    rw [M_BE0] at hm
    have hok1 : (s₀.dmem.loadInt (rbx s₀ + 0x2c2a8#64) 4).isSome = true := by
      rw [ElemS_ld_e0 hm rfl]; rfl
    have h1 := fun w => ElemS_st_e0 hm rfl w
    have hok2 : ∀ w, ((s₀.dmem.storeInt (rbx s₀ + 0x2c2a8#64) 4 w).loadInt
        (rbx s₀ + 0x2893c#64) 4).isSome = true := fun w => by rw [ElemS_ld_spLo (h1 w) rfl]; rfl
    have hfin : ∀ w1 w2, Int.toBytes 4 w1 = Int.toBytes 4 (-1)
        → Int.toBytes 4 w2 = Int.toBytes 4 (-1)
        → (s₀.dmem.storeInt (rbx s₀ + 0x2c2a8#64) 4 w1).storeInt (rbx s₀ + 0x2893c#64) 4 w2
          =⋆ M k TxTab X R ra t₀ (BE0 t₀ (rbx s₀) (evF (rbx s₀) (idOf t₀))) := by
      intro w1 w2 e1 e2
      have h := BE0_st (ElemS_st_spLo (h1 w1) rfl w2)
      rw [e1, e2] at h; exact h
    clear hm h1
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try simp only [Int64.toBitVec_ofNat_norm, AddrIndex.offset64_none,
      BitVec.add_zero, add0, BitVec.setWidth_eq] at *
    · exact hok1
    · exact hok2 _
    · exact ⟨⟨hR, hax, hfin _ _ (by rw [hcx]; decide) (by rw [hcx]; decide)⟩, Nat.le_refl 0⟩

theorem blk_L95 (k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (TxTab X : Mem 64 → Prop)
    (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ctx TxTab X R ra t₀ "ff_aac_sbr_ctx_alloc_init.L95" := by
  cfg_block
  measure_hb "L95"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hR, hax, hm⟩, hn⟩ := hs₀
    rw [M_BE0] at hm
    have hok1 : (s₀.dmem.loadInt (rbx s₀ + 0x28940#64) 2).isSome = true := by
      rw [ElemS_ld_spHi hm rfl]; rfl
    have h1 := fun w => ElemS_st_spHi hm rfl w
    have hok2 : ∀ w, ((s₀.dmem.storeInt (rbx s₀ + 0x28940#64) 2 w).loadInt
        (rbx s₀ + 0x2c2a0#64) 4).isSome = true := fun w => by rw [ElemS_ld_v0 (h1 w) rfl]; rfl
    have hfin : ∀ w1 w2, Int.toBytes 2 w1 = Int.toBytes 2 (-1)
        → Int.toBytes 4 w2 = Int.toBytes 4 0x480
        → (s₀.dmem.storeInt (rbx s₀ + 0x28940#64) 2 w1).storeInt (rbx s₀ + 0x2c2a0#64) 4 w2
          =⋆ M k TxTab X R ra t₀ (BE0 t₀ (rbx s₀) (evG (rbx s₀) (idOf t₀))) := by
      intro w1 w2 e1 e2
      have h := BE0_st (ElemS_st_v0 (h1 w1) rfl w2)
      rw [e1, e2] at h; exact h
    clear hm h1
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try simp only [Int64.toBitVec_ofNat_norm, AddrIndex.offset64_none,
      BitVec.add_zero, add0, BitVec.setWidth_eq] at *
    · exact hok1
    · exact hok2 _
    · exact ⟨⟨hR, hax, by decide, hfin _ _ (by decide) (by decide)⟩, Nat.le_refl 0⟩

theorem blk_La9 (k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (TxTab X : Mem 64 → Prop)
    (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ctx TxTab X R ra t₀ "ff_aac_sbr_ctx_alloc_init.La9" := by
  cfg_block
  measure_hb "La9"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hR, hax, hcx, hm⟩, hn⟩ := hs₀
    rw [M_BE0] at hm
    have hok1 : (s₀.dmem.loadInt (rbx s₀ + 0x41d60#64) 4).isSome = true := by
      rw [ElemS_ld_v1 hm rfl]; rfl
    have h1 := fun w => ElemS_st_v1 hm rfl w
    have hok2 := fun w => (Mo_scale2 (h1 w) 0x35000000).1
    have hfin : ∀ w1, Int.toBytes 4 w1 = Int.toBytes 4 0x480
        → ∀ w2, (s₀.dmem.storeInt (rbx s₀ + 0x41d60#64) 4 w1).storeInt
            (t₀.regs.get64 .rsp - 0x24#64) 4 w2
          =⋆ M k TxTab X R ra t₀ (BE0 t₀ (rbx s₀) (evH (rbx s₀) (idOf t₀))) := by
      intro w1 e1 w2
      have h := BE0_st (Mo_scale2 (h1 w1) w2).2
      rw [e1] at h; exact h
    have ea : s₀.regs.get64 .rbp + (-28 : Int64).toBitVec = t₀.regs.get64 .rsp - 0x24#64 := by
      rw [hR.2.1, show (-28 : Int64).toBitVec = 0xffffffffffffffe4#64 by decide]; bv_omega
    clear hm h1
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try simp only [Int64.toBitVec_ofNat_norm, AddrIndex.offset64_none,
      BitVec.add_zero, add0] at *
    · exact hok1
    · rw [ea]; exact hok2 _
    · rw [ea]; exact ⟨⟨hR, hax, rfl, hfin _ (by rw [hcx]; decide) _⟩, Nat.le_refl 0⟩

end Kraken.Examples.Sbr.Init
