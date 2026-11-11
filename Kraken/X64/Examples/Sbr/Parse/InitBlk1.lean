import Kraken.X64.Examples.Sbr.Parse.InitFrame

/-!
# `ff_aac_sbr_ctx_alloc_init`: the prologue and the call of `av_mallocz`
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

theorem blk_entry (k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (TxTab X : Mem 64 → Prop)
    (hmz : AvMalloczSpec X k) (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ctx TxTab X R ra t₀ "ff_aac_sbr_ctx_alloc_init" := by
  cfg_block
  measure_hb "entry"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨rfl, hm⟩, hn⟩ := hs₀
    obtain ⟨hp1, hp2, hp3, hp4, hP⟩ := M_push _ rfl hm (s₀.regs.get64 .rbp)
      (s₀.regs.get64 .r15) (s₀.regs.get64 .r14) (s₀.regs.get64 .rbx)
    rw [MF_call] at hP
    have hpush := fun v => Block.storeInt_val hP (Split.here _ _) v
    have hld := Block.loadInt_isSome hP (n := 8) (addr := s₀.regs.get64 .rsp - 0x40#64)
      (by simp)
    have e64 : s₀.regs.get64 .rsp - 32#64 - (BitVec.setWidth 64 (Int64.toBitVec 24) + 8#64)
        = s₀.regs.get64 .rsp - 0x40#64 := by
      rw [show Int64.toBitVec 24 = 24#64 from rfl, BitVec.setWidth_eq]; bv_omega
    clear hm hP
    vcgen [MachineWP.call_proc_spec_at (Fr s₀ ⋆ (8 ?@ arg1 s₀ ⋆ (TxTab ⋆ Rest R ra s₀)))
      "av_mallocz" hmz]
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try simp only [BitVec.sub_sub_eight, BitVec.reduceAdd]
    · exact hp1
    · exact hp2
    · exact hp3
    · exact hp4
    refine ⟨fun ra' => ⟨?_, fun s' hpost => ?_⟩, ?_⟩
    · rw [e64]; exact hpush _
    · simp only [e64] at hpost
      refine MachineWP.nil_spec.le_wp s' ?_
      have hn : (BitVec.setWidth 64 (BitVec.setWidth 32 (Int64.toBitVec 560032))).toNat
          = 560032 := by decide
      rcases hpost with ⟨hax, hsp, hbp, ⟨hbx, h12, h13, h14, h15⟩, hm⟩
        | ⟨hax, hsp, hbp, ⟨hbx, h12, h13, h14, h15⟩, hm⟩
      · exact ⟨⟨⟨by rw [hsp]; bv_omega, hbp, h14, h15, h12, h13⟩, hbx, Or.inl ⟨hax, Mem.ac hm⟩⟩,
          Nat.le_refl 0⟩
      · rw [hn] at hm
        exact ⟨⟨⟨by rw [hsp]; bv_omega, hbp, h14, h15, h12, h13⟩, hbx, Or.inr ⟨hax, Mem.ac hm⟩⟩,
          Nat.le_refl 0⟩
    · rw [e64]; exact hld

end Kraken.Examples.Sbr.Init
