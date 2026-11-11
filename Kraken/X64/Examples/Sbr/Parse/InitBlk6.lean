import Kraken.X64.Examples.Sbr.Parse.InitTx

/-!
# `ff_aac_sbr_ctx_alloc_init`: `ff_psdsp_init(&sbr->ps.dsp)` and `ff_sbrdsp_init(&sbr->dsp)`
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

omit [CodeEnv] in
theorem ret_sp (r : BitVec 64) : r - 0x40#64 + 8 = r - 56#64 := by bv_omega

theorem blk_L123 (k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (TxTab X : Mem 64 → Prop)
    (hps : PsDspInitSpec X k) (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ctx TxTab X R ra t₀ "ff_aac_sbr_ctx_alloc_init.L123" := by
  cfg_block
  measure_hb "L123"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hR, c, f, c', f', htf, hm⟩, hn⟩ := hs₀
    rw [M_BE2] at hm
    have hP := dsp_pre (ElemS_out_ps hm rfl)
    have hpush := fun w => Block.storeInt_val hP (Split.here _ _) w
    have hld := Block.loadInt_isSome hP (n := 8)
      (addr := t₀.regs.get64 .rsp - 0x40#64) (by simp)
    have e1 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 0x40#64 := by
      rw [hR.1]; show _ - 56#64 - 8#64 = _; bv_omega
    have e1' : t₀.regs.get64 .rsp - 56#64 - Width.W64.bytesv = t₀.regs.get64 .rsp - 0x40#64 := by
      show _ - 56#64 - 8#64 = _; bv_omega
    have hback : ∀ m : Mem 64, (m =⋆ 8 ?@ (t₀.regs.get64 .rsp - 0x40#64)
        ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x40#64) ⋆ ((64 ?@ (rbx s₀ + 0x74ab8#64) ⋆ X)
        ⋆ DF TxTab R ra t₀ (ElemH_ps (rbx s₀) (evT (rbx s₀) (idOf t₀) c f c' f'))
          (c8 (arg1 t₀) (rbx s₀)) (Ctx c') (Ctx c))))
        → ∃ bs : List UInt8, bs.length = 64 ∧ (m =⋆ M k TxTab X R ra t₀
          (BE2 Ctx t₀ (rbx s₀) (evU (rbx s₀) (idOf t₀) c f c' f' bs) c c')) := fun m h => by
      obtain ⟨bs, hl, hq⟩ := ElemS_in_ps (dsp_post h)
      exact ⟨bs, hl, BE2_st Ctx hq⟩
    simp only [DF, Fr, c8, idOf, arg1, arg2] at hback
    obtain ⟨hsp, hbp, h14, h15, h12, h13⟩ := hR
    clear hm hP
    vcgen [MachineWP.call_proc_spec_at (DF TxTab R ra t₀
      (ElemH_ps (rbx s₀) (evT (rbx s₀) (idOf t₀) c f c' f')) (c8 (arg1 t₀) (rbx s₀)) (Ctx c')
      (Ctx c)) "ff_psdsp_init" hps]
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try simp only [Int64.toBitVec_ofNat_norm, AddrIndex.offset64_none,
      BitVec.add_zero, add0, BitVec.setWidth_eq]
    refine ⟨fun ra' => ⟨⟨?_, trivial⟩, fun s' hpost => ?_⟩, ?_⟩
    · rw [e1]; exact hpush _
    · obtain ⟨hsp', hbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩ := hpost
      refine MachineWP.nil_spec.le_wp s' ?_
      simp only [e1, e1', hsp] at hm'
      obtain ⟨bs, hl, hq⟩ := hback _ hm'
      refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, Nat.le_refl 0⟩
      · rw [hsp', e1]; exact ret_sp _
      · exact hbp'.trans hbp
      · exact h14'.trans h14
      · exact h15'.trans h15
      · exact h12'.trans h12
      · exact h13'.trans h13
      · rw [hbx']
        exact ⟨c, f, c', f', bs, htf, hl, hq⟩
    · rw [e1]; exact hld

theorem blk_L12f (k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (TxTab X : Mem 64 → Prop)
    (hsd : SbrDspInitSpec X k) (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ctx TxTab X R ra t₀ "ff_aac_sbr_ctx_alloc_init.L12f" := by
  cfg_block
  measure_hb "L12f"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hR, c, f, c', f', psd, htf, hpl, hm⟩, hn⟩ := hs₀
    rw [M_BE2] at hm
    have hP := dsp_pre (ElemS_out_dsp hm rfl)
    have hpush := fun w => Block.storeInt_val hP (Split.here _ _) w
    have hld := Block.loadInt_isSome hP (n := 8)
      (addr := t₀.regs.get64 .rsp - 0x40#64) (by simp)
    have e1 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 0x40#64 := by
      rw [hR.1]; show _ - 56#64 - 8#64 = _; bv_omega
    have e1' : t₀.regs.get64 .rsp - 56#64 - Width.W64.bytesv = t₀.regs.get64 .rsp - 0x40#64 := by
      show _ - 56#64 - 8#64 = _; bv_omega
    have ead : 559872#64 + s₀.regs.get64 .rbx = rbx s₀ + 0x88b00#64 := BitVec.add_comm _ _
    have hback : ∀ (m : Mem 64) (sl : Slots), (m =⋆ 8 ?@ (t₀.regs.get64 .rsp - 0x40#64)
        ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x40#64) ⋆ ((sl.bytes =@ (rbx s₀ + 0x88b00#64) ⋆ X)
        ⋆ DF TxTab R ra t₀ (ElemH_dsp (rbx s₀) (evU (rbx s₀) (idOf t₀) c f c' f' psd))
          (c8 (arg1 t₀) (rbx s₀)) (Ctx c') (Ctx c))))
        → (m =⋆ M k TxTab X R ra t₀
          (BE2 Ctx t₀ (rbx s₀) (evV (rbx s₀) (idOf t₀) c f c' f' psd sl.bytes) c c')) :=
      fun m sl h => by
        refine BE2_st Ctx ?_
        rw [ElemS_dsp, Std.ExtHashMap.sep_assoc]
        simp only [Mo, DF] at h ⊢
        exact Mem.ac h
    simp only [DF, Fr, c8, idOf, arg1, arg2] at hback
    obtain ⟨hsp, hbp, h14, h15, h12, h13⟩ := hR
    clear hm hP
    vcgen [MachineWP.call_proc_spec_at (DF TxTab R ra t₀
      (ElemH_dsp (rbx s₀) (evU (rbx s₀) (idOf t₀) c f c' f' psd)) (c8 (arg1 t₀) (rbx s₀)) (Ctx c')
      (Ctx c)) "ff_sbrdsp_init" hsd]
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try simp only [Int64.toBitVec_ofNat_norm, AddrIndex.offset64_none,
      BitVec.add_zero, add0, BitVec.setWidth_eq]
    refine ⟨fun ra' => ⟨?_, fun s' hpost => ?_⟩, ?_⟩
    · rw [e1, ead]; exact hpush _
    · obtain ⟨sl, hok, hsp', hbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩ := hpost
      refine MachineWP.nil_spec.le_wp s' ?_
      simp only [e1, e1', hsp, ead] at hm'
      have hq := hback _ sl hm'
      refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, Nat.le_refl 0⟩
      · rw [hsp', e1]; exact ret_sp _
      · exact hbp'.trans hbp
      · exact h14'.trans h14
      · exact h15'.trans h15
      · exact h12'.trans h12
      · exact h13'.trans h13
      · rw [hbx']
        exact ⟨c, f, c', f', psd, sl, htf, hpl, hok, hq⟩
    · rw [e1]; exact hld

end Kraken.Examples.Sbr.Init
