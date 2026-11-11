import Kraken.X64.Examples.Sbr.Parse.InitMem

/-!
# `ff_aac_sbr_ctx_alloc_init`: the four function pointers
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

theorem blk_L13e (k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (TxTab X : Mem 64 → Prop)
    (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ctx TxTab X R ra t₀ "ff_aac_sbr_ctx_alloc_init.L13e" := by
  cfg_block
  measure_hb "L13e"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hR, c, f, c', f', psd, sl, htf, hpl, hok, hm⟩, hn⟩ := hs₀
    rw [M_BE2] at hm
    have hld1 : (s₀.dmem.loadInt (rbx s₀ + 0x88b70#64) 8).isSome = true := by
      rw [ElemS_ld_c0 hm rfl]; rfl
    have h1 := fun w => ElemS_st_c0 hm rfl w
    have hld2 : ∀ w, ((s₀.dmem.storeInt (rbx s₀ + 0x88b70#64) 8 w).loadInt
        (rbx s₀ + 0x88b78#64) 8).isSome = true := fun w => by rw [ElemS_ld_c1 (h1 w) rfl]; rfl
    have hfin : ∀ w1 w2, Int.toBytes 8 w1 = fb (entry "sbr_lf_gen")
        → Int.toBytes 8 w2 = fb (entry "sbr_hf_assemble")
        → (s₀.dmem.storeInt (rbx s₀ + 0x88b70#64) 8 w1).storeInt (rbx s₀ + 0x88b78#64) 8 w2
          =⋆ M k TxTab X R ra t₀
            (BE2 Ctx t₀ (rbx s₀) (evW (rbx s₀) (idOf t₀) c f c' f' psd sl.bytes) c c') := by
      intro w1 w2 e1 e2
      have h := BE2_st Ctx (ElemS_st_c1 (h1 w1) rfl w2)
      rw [e1, e2] at h; exact h
    clear hm h1
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try simp only [Int64.toBitVec_ofNat_norm, AddrIndex.offset64_none,
      BitVec.add_zero, add0, BitVec.setWidth_eq] at *
    · exact hld1
    · exact hld2 _
    · exact ⟨⟨hR, c, f, c', f', psd, sl, htf, hpl, hok, hfin _ _ rfl rfl⟩, Nat.le_refl 0⟩

theorem blk_L15a (k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (TxTab X : Mem 64 → Prop)
    (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ctx TxTab X R ra t₀ "ff_aac_sbr_ctx_alloc_init.L15a" := by
  cfg_block
  measure_hb "L15a"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hR, c, f, c', f', psd, sl, htf, hpl, hok, hm⟩, hn⟩ := hs₀
    rw [M_BE2] at hm
    have hld1 : (s₀.dmem.loadInt (rbx s₀ + 0x88b80#64) 8).isSome = true := by
      rw [ElemS_ld_c2 hm rfl]; rfl
    have h1 := fun w => ElemS_st_c2 hm rfl w
    have hld2 : ∀ w, ((s₀.dmem.storeInt (rbx s₀ + 0x88b80#64) 8 w).loadInt
        (rbx s₀ + 0x88b88#64) 8).isSome = true := fun w => by rw [ElemS_ld_c3 (h1 w) rfl]; rfl
    have hfin : ∀ w1 w2, Int.toBytes 8 w1 = fb (entry "sbr_x_gen")
        → Int.toBytes 8 w2 = fb (entry "sbr_hf_inverse_filter")
        → ∃ r : IR, r.psd.length = 64 ∧ DspSlotsOK r.sl
          ∧ TxSpec Ctx TxTab k r.anaFn ∧ TxSpec Ctx TxTab k r.synFn
          ∧ ((s₀.dmem.storeInt (rbx s₀ + 0x88b80#64) 8 w1).storeInt (rbx s₀ + 0x88b88#64) 8 w2
            =⋆ M k TxTab X R ra t₀ (InitOK Ctx (arg1 t₀) (idOf t₀) r)) := by
      intro w1 w2 e1 e2
      have h := BE2_st Ctx (ElemS_st_c3 (h1 w1) rfl w2)
      rw [e1, e2] at h
      exact ⟨⟨rbx s₀, c', f', c, f, sl, psd⟩, hpl, hok, htf.2, htf.1, h⟩
    clear hm h1
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try simp only [Int64.toBitVec_ofNat_norm, AddrIndex.offset64_none,
      BitVec.add_zero, add0, BitVec.setWidth_eq]
    · exact hld1
    · exact hld2 _
    · left
      refine ⟨"ff_aac_sbr_ctx_alloc_init.L17f", rfl, by decide, ⟨?_, ?_⟩,
        Or.inr ⟨trivial, by decide⟩⟩
      · simpa using hR
      · exact Or.inl ⟨by simp, hfin _ _ rfl rfl⟩

end Kraken.Examples.Sbr.Init
