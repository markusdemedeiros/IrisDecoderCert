import Kraken.X64.Examples.Sbr.Parse.InitTx

/-!
# `ff_aac_sbr_ctx_alloc_init`: `av_tx_init(&sbr->mdct_ana, …)` and its test
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

theorem blk_Le9 (k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (TxTab X : Mem 64 → Prop)
    (htx : AvTxInitSpec Ctx TxTab X k) (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ctx TxTab X R ra t₀ "ff_aac_sbr_ctx_alloc_init.Le9" := by
  cfg_block
  measure_hb "Le9"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hR, c, f, htf, hm⟩, hn⟩ := hs₀
    rw [M_BE1, ← Std.ExtHashMap.sep_assoc (c8 (arg1 t₀) (rbx s₀)) (Ctx c)] at hm
    have hoks := (Mo_scale2 hm 0).1
    have hS := fun u => (Mo_scale2 hm u).2
    have hokf := fun u => (Mo_flags2 (hS u) 0).1
    have hP := fun u v => tx_pre (ElemS_out_ana (Mo_flags2 (hS u) v).2 rfl rfl)
    have hpush := fun u v w => Block.storeInt_val (hP u v) (Split.here _ _) w
    have hld := fun u v => Block.loadInt_isSome (hP u v) (n := 8)
      (addr := t₀.regs.get64 .rsp - 0x40#64) (by simp)
    have ea : s₀.regs.get64 .rbp + (-28 : Int64).toBitVec = t₀.regs.get64 .rsp - 0x24#64 := by
      rw [hR.2.1, show (-28 : Int64).toBitVec = 0xffffffffffffffe4#64 by decide]; bv_omega
    have e1 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 0x40#64 := by
      rw [hR.1]; show _ - 56#64 - 8#64 = _; bv_omega
    have e1' : t₀.regs.get64 .rsp - 56#64 - Width.W64.bytesv = t₀.regs.get64 .rsp - 0x40#64 := by
      show _ - 56#64 - 8#64 = _; bv_omega
    have e2 : t₀.regs.get64 .rsp - 0x40#64 + 8#64 = t₀.regs.get64 .rsp - 0x38#64 := by bv_omega
    obtain ⟨hsp, hbp, h14, h15, h12, h13⟩ := hR
    clear hm hP hS
    vcgen [MachineWP.call_proc_spec_at (TxF R ra t₀
      (ElemH_ana (rbx s₀) (evS (rbx s₀) (idOf t₀) c f)) (c8 (arg1 t₀) (rbx s₀) ⋆ Ctx c))
      "av_tx_init" htx]
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try simp only [Int64.toBitVec_ofNat_norm, AddrIndex.offset64_none,
      BitVec.add_zero, add0, BitVec.setWidth_eq]
    · rw [ea]; exact hoks
    · rw [ea, hsp]; exact hokf _
    refine ⟨fun ra' => ⟨?_, fun s' hpost => ?_⟩, ?_⟩
    · rw [e1, e2, ea, hsp]; exact hpush _ _ _
    · obtain ⟨c', f', htf', hsp', hbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩ := hpost
      refine MachineWP.nil_spec.le_wp s' ?_
      simp only [e1', e2, ea, hsp] at hm'
      have hq := tx_post hm'
      refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, Nat.le_refl 0⟩
      · rw [hsp', e1]; bv_omega
      · rw [hbp', hbp]
      · rw [h14', h14]
      · rw [h15', h15]
      · rw [h12', h12]
      · rw [h13', h13]
      · rw [hbx']
        by_cases hc : 0 ≤ (BitVec.setWidth 32 (s'.regs.get64 .rax)).toInt
        · rw [if_pos hc] at hq
          exact Or.inl ⟨hc, c, f, c', f', ⟨htf, htf' hc⟩, BE2_st Ctx (be2_of (tx_ok_ana hq))⟩
        · rw [if_neg hc] at hq
          obtain ⟨bc, bf, hl1, hl2, hf⟩ := tx_fail_ana hq
          exact Or.inr ⟨Int.lt_of_not_ge hc, c, f, bc, bf, hl1, hl2, M_swap hf⟩
    · rw [e1, ea, hsp]; exact hld _ _

theorem blk_L11f (k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (TxTab X : Mem 64 → Prop)
    (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ctx TxTab X R ra t₀ "ff_aac_sbr_ctx_alloc_init.L11f" := by
  cfg_block
  measure_hb "L11f"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hR, hm⟩, hn⟩ := hs₀
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try simp only [CondCode.interp, StatusFlags.from_result, BitVec.and_self] at *
    · rename_i hz
      rw [BitVec.msb_eq_toInt] at hz
      have hneg := of_decide_eq_true hz
      left
      refine ⟨"ff_aac_sbr_ctx_alloc_init.L17f", rfl, by decide, ⟨hR, ?_⟩,
        Or.inr ⟨trivial, by decide⟩⟩
      rcases hm with ⟨h0, -⟩ | ⟨-, c, f, bc, bf, hl1, hl2, hm⟩
      · exact absurd hneg (Int.not_lt.mpr h0)
      · exact Or.inr (Or.inr (Or.inr ⟨hneg, _, c, f, bc, bf, hl1, hl2, hm⟩))
    · rename_i hz
      rw [BitVec.msb_eq_toInt] at hz
      have hpos := Int.not_lt.mp (of_decide_eq_false hz)
      rcases hm with ⟨-, c, f, c', f', htf, hm⟩ | ⟨hl, -⟩
      · exact ⟨⟨hR, c, f, c', f', htf, hm⟩, Nat.le_refl 0⟩
      · exact absurd hl (Int.not_lt.mpr hpos)

end Kraken.Examples.Sbr.Init
