import Kraken.X64.Examples.Sbr.Parse.UsacBlk3
open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse
set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true
/-! # `ff_aac_sbr_decode_usac_data`: the calls of `read_sbr_invf` of a channel pair -/
namespace Kraken.Examples.Sbr.Usac
variable [CodeEnv]

omit [CodeEnv] in
/-- `lea 0x28920(%rbx)` is `sbr`. -/
theorem sa0 (c : BitVec 64) : c + Int64.toBitVec 166176 = c + 166176#64 :=
  congrArg (c + ·) rfl

/-- `read_sbr_invf(sbr, gb, &sbr->data[0])` of a channel pair, channel 0 (`r13` reloaded). -/
theorem blk_L3819 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData)
    (hc : InvfSpec k 0 A.1.Ext A.1.Oth) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L3819" := by
  cfg_block
  measure_hb "L3819"
    intro n
    simp only [tbl_L3819, var_L3819, tbl_L382e, var_L382e]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h15, st, hI, hP, hm⟩, rfl⟩ := hs₀
    simp only [UM] at hm
    obtain ⟨⟨hmi, hid, hu⟩, hl0, hl1⟩ := hP
    have e50 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 80#64 := by
      rw [hsp]; show _ - 72#64 - 8#64 = _; bv_omega
    have e72 : s₀.regs.get64 .rsp - Width.W64.bytesv + 8 = t₀.regs.get64 .rsp - 72#64 := by
      rw [hsp]; show _ - 72#64 - 8#64 + 8#64 = _; bv_omega
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rsp - Width.W64.bytesv) 8).isSome = true := by
      rw [e50]
      exact Block.loadInt_isSome hm (by simp)
    have hpush := fun v => Block.storeInt_val hm (Split.here _ _) v
    generalize table k A ra t₀ = T
    generalize var = V
    vcgen [call_procA_spec_at (cA A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) st)
      "read_sbr_invf" hc]
    all_goals try call_simp
    have hs1 := ‹_ = s₀›
    subst hs1
    refine ⟨fun ra' => ⟨⟨⟨?_, trivial, trivial⟩, by rw [hbx]; exact sa0 _, h14, h15, hmi.1.1,
      hmi.1.2.2.1,
      hI.2.2,
      hF.1.2.2.2.1⟩,
      fun s' hpost => ?_⟩, fun _ => Or.inr (Or.inr (Or.inl trivial)), hld⟩
    · rw [e50]; exact hpush _
    · obtain ⟨st', ⟨vals, hst', hi'⟩, hsp', hbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩ := hpost
      rw [e50] at hm'
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨⟨⟨⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, st', ⟨?_, ?_, hi'⟩, ?_, hm'⟩, ?_⟩, trivial⟩,
        Nat.le_refl _⟩
      · exact hsp'.trans e72
      · exact hbp'.trans hbp
      · exact h12'.trans h12
      · exact hbx'.trans hbx
      · exact h14'.trans h14
      · rw [h13', hbx]; exact sa0 _
      · rw [hst']; exact hI.1
      · rw [hst']; exact hI.2.1
      · rw [hst']
        exact ⟨⟨mi_d0 hmi (dwf_invfRead hmi.1.2.2.1)
          (by rw [invfRead_te, invfRead_nenv]; exact hmi.1.2.2.2.2.2.1), hid, hu⟩,
          live_invfRead hl0, hl1⟩
      · exact h15'.trans h15

/-- `read_sbr_invf(sbr, gb, &sbr->data[0])` of a coupled pair, channel 0. -/
theorem blk_L39b8 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData)
    (hc : InvfSpec k 0 A.1.Ext A.1.Oth) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L39b8" := by
  cfg_block
  measure_hb "L39b8"
    intro n
    simp only [tbl_L39b8, var_L39b8, tbl_L39c6, var_L39c6]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, hP, hm⟩, h15⟩, rfl⟩ := hs₀
    simp only [UM] at hm
    obtain ⟨⟨hmi, hid, hu⟩, hl0, hl1⟩ := hP
    have e50 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 80#64 := by
      rw [hsp]; show _ - 72#64 - 8#64 = _; bv_omega
    have e72 : s₀.regs.get64 .rsp - Width.W64.bytesv + 8 = t₀.regs.get64 .rsp - 72#64 := by
      rw [hsp]; show _ - 72#64 - 8#64 + 8#64 = _; bv_omega
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rsp - Width.W64.bytesv) 8).isSome = true := by
      rw [e50]
      exact Block.loadInt_isSome hm (by simp)
    have hpush := fun v => Block.storeInt_val hm (Split.here _ _) v
    generalize table k A ra t₀ = T
    generalize var = V
    vcgen [call_procA_spec_at (cA A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) st)
      "read_sbr_invf" hc]
    all_goals try call_simp
    have hs1 := ‹_ = s₀›
    subst hs1
    refine ⟨fun ra' => ⟨⟨⟨?_, trivial, trivial⟩, h13, h14, h15, hmi.1.1, hmi.1.2.2.1, hI.2.2,
      hF.1.2.2.2.1⟩,
      fun s' hpost => ?_⟩, fun _ => Or.inr (Or.inr (Or.inl trivial)), hld⟩
    · rw [e50]; exact hpush _
    · obtain ⟨st', ⟨vals, hst', hi'⟩, hsp', hbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩ := hpost
      rw [e50] at hm'
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨⟨⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, st', ⟨?_, ?_, hi'⟩, ?_, hm'⟩, ?_⟩,
        Nat.le_refl _⟩
      · exact hsp'.trans e72
      · exact hbp'.trans hbp
      · exact h12'.trans h12
      · exact hbx'.trans hbx
      · exact h14'.trans h14
      · exact h13'.trans h13
      · rw [hst']; exact hI.1
      · rw [hst']; exact hI.2.1
      · rw [hst']
        exact ⟨⟨mi_d0 hmi (dwf_invfRead hmi.1.2.2.1)
          (by rw [invfRead_te, invfRead_nenv]; exact hmi.1.2.2.2.2.2.1), hid, hu⟩,
          live_invfRead hl0, hl1⟩
      · exact h15'.trans h15

/-- `read_sbr_invf(sbr, gb, &sbr->data[1])` of a coupled pair, channel 1. -/
theorem blk_L39c6 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData)
    (hc : InvfSpec k 1 A.1.Ext A.1.Oth) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L39c6" := by
  cfg_block
  measure_hb "L39c6"
    intro n
    simp only [tbl_L39c6, var_L39c6, tbl_L39d8, var_L39d8]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, hP, hm⟩, h15⟩, rfl⟩ := hs₀
    simp only [UM] at hm
    obtain ⟨⟨hmi, hid, hu⟩, hl0, hl1⟩ := hP
    have e50 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 80#64 := by
      rw [hsp]; show _ - 72#64 - 8#64 = _; bv_omega
    have e72 : s₀.regs.get64 .rsp - Width.W64.bytesv + 8 = t₀.regs.get64 .rsp - 72#64 := by
      rw [hsp]; show _ - 72#64 - 8#64 + 8#64 = _; bv_omega
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rsp - Width.W64.bytesv) 8).isSome = true := by
      rw [e50]
      exact Block.loadInt_isSome hm (by simp)
    have hpush := fun v => Block.storeInt_val hm (Split.here _ _) v
    generalize table k A ra t₀ = T
    generalize var = V
    vcgen [call_procA_spec_at (cA A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) st)
      "read_sbr_invf" hc]
    all_goals try call_simp
    have hs1 := ‹_ = s₀›
    subst hs1
    refine ⟨fun ra' => ⟨⟨⟨?_, trivial, trivial⟩, h13, h14, by rw [hbx]; exact dac1 _, hmi.1.1,
      hmi.1.2.2.2.1, hI.2.2,
      hF.1.2.2.2.1⟩,
      fun s' hpost => ?_⟩, fun _ => Or.inr (Or.inr (Or.inl trivial)), hld⟩
    · rw [e50]; exact hpush _
    · obtain ⟨st', ⟨vals, hst', hi'⟩, hsp', hbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩ := hpost
      rw [e50] at hm'
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨⟨⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, st', ⟨?_, ?_, hi'⟩, ?_, hm'⟩, ?_⟩,
        Nat.le_refl _⟩
      · exact hsp'.trans e72
      · exact hbp'.trans hbp
      · exact h12'.trans h12
      · exact hbx'.trans hbx
      · exact h14'.trans h14
      · exact h13'.trans h13
      · rw [hst']; exact hI.1
      · rw [hst']; exact hI.2.1
      · rw [hst']
        exact ⟨⟨mi_d1 hmi (dwf_invfRead hmi.1.2.2.2.1)
          (by rw [invfRead_te, invfRead_nenv]; exact hmi.1.2.2.2.2.2.2), hid, hu⟩,
          hl0, live_invfRead hl1⟩
      · exact h15'.trans h15

end Kraken.Examples.Sbr.Usac
