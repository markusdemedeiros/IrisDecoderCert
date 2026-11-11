import Kraken.X64.Examples.Sbr.Parse.UsacBlk3
open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse
set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true
/-! # `ff_aac_sbr_decode_usac_data`: the calls of `read_sbr_dtdf`

The first argument is the value of `sbr->usac` (loaded from `SHW`), the fourth `indep_flag`
(the local at `-0x2c(%rbp)`). -/
namespace Kraken.Examples.Sbr.Usac
variable [CodeEnv]

/-- `read_sbr_dtdf(sbr->usac, gb, &sbr->data[0], indep_flag)` of the single channel element. -/
theorem blk_L3630 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData)
    (hc : DtdfSpec k 0 A.1.Ext A.1.Oth) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L3630" := by
  cfg_block
  measure_hb "L3630"
    intro n
    simp only [tbl_L3630, var_L3630, tbl_L3644, var_L3644]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, hP, hm⟩, h15⟩, hch⟩, rfl⟩ := hs₀
    simp only [UM] at hm
    obtain ⟨⟨hmi, hid, hu⟩, hl0⟩ := hP
    have hm2 := hm
    simp only [UF, SHW, sA, LocI, BitVec.add_assoc, BitVec.reduceAdd] at hm2
    have a1 : s₀.regs.get64 .rbx + Int64.toBitVec 166192 = A.1.c + 166192#64 := by
      rw [hbx]; exact congrArg (A.1.c + ·) rfl
    have a2 : s₀.regs.get64 .rbp + (-44 : Int64).toBitVec = t₀.regs.get64 .rsp - 52#64 := by
      have e : (-44 : Int64).toBitVec = -44#64 := rfl
      rw [hbp, e]; bv_omega
    have l1 : s₀.dmem.loadInt (s₀.regs.get64 .rbx + Int64.toBitVec 166192) 4
        = some (Int.ofBytes (Int.toBytes 4 st.u.toInt)) := by rw [a1]; sep_mem hm2 <;> rfl
    have l2 : s₀.dmem.loadInt (s₀.regs.get64 .rbp + (-44 : Int64).toBitVec) 4
        = some (Int.ofBytes (Int.toBytes 4 (ivv t₀).toInt)) := by rw [a2]; sep_mem hm2 <;> rfl
    clear hm2 a1 a2
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
      "read_sbr_dtdf" hc]
    all_goals try call_simp
    all_goals try (have hs1 := ‹_ = s₀›; subst hs1)
    case vc1 => rw [l1]; rfl
    case vc2 => rw [l2]; rfl
    case vc3 v1 hv1 v2 hv2 _ =>
    have hv := hv1.symm.trans l1
    simp only [Option.some.injEq] at hv
    subst hv
    refine ⟨fun ra' => ⟨⟨⟨?_, trivial, trivial⟩, by simp only [sw6432,
      BitVec.ofInt_ofBytes_toBytes 32 4 rfl], h14,
      h15, hmi.1.2.2.1, hI.2.2, hF.1.2.2.2.1⟩, fun s' hpost => ?_⟩,
      fun _ => Or.inr (Or.inr (Or.inl trivial)), hld⟩
    · rw [e50]; exact hpush _
    · obtain ⟨st', ⟨hst', hi'⟩, hsp', hbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩ := hpost
      rw [e50] at hm'
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨⟨⟨⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, st', ⟨?_, ?_, hi'⟩, ?_, hm'⟩, ?_⟩, hch⟩,
        Nat.le_refl _⟩
      · exact hsp'.trans e72
      · exact hbp'.trans hbp
      · exact h12'.trans h12
      · exact hbx'.trans hbx
      · exact h14'.trans h14
      · exact h13'.trans h13
      · rw [hst']; exact hI.1
      · rw [hst']; exact hI.2.1
      · rw [hst']; exact ⟨⟨hmi, hid, hu⟩, hl0⟩
      · exact h15'.trans h15

omit [CodeEnv] in
/-- `lea 0x289a0(%rbx)` is `&sbr->data[0]`. -/
theorem dac0 (c : BitVec 64) : c + Int64.toBitVec 166304 = dAc c 0 := by
  unfold dAc; rw [BitVec.add_assoc]; rfl

/-- `read_sbr_dtdf(sbr->usac, gb, &sbr->data[0], indep_flag)` of a coupled pair, channel 0. -/
theorem blk_L3981 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData)
    (hc : DtdfSpec k 0 A.1.Ext A.1.Oth) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L3981" := by
  cfg_block
  measure_hb "L3981"
    intro n
    simp only [tbl_L3981, var_L3981, tbl_L3999, var_L3999]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, hP, hm⟩, h15⟩, rfl⟩ := hs₀
    simp only [UM] at hm
    obtain ⟨⟨hmi, hid, hu⟩, hl0, hl1⟩ := hP
    have hm2 := hm
    simp only [UF, SHW, sA, LocI, BitVec.add_assoc, BitVec.reduceAdd] at hm2
    have a1 : s₀.regs.get64 .rbx + Int64.toBitVec 166192 = A.1.c + 166192#64 := by
      rw [hbx]; exact congrArg (A.1.c + ·) rfl
    have a2 : s₀.regs.get64 .rbp + (-44 : Int64).toBitVec = t₀.regs.get64 .rsp - 52#64 := by
      have e : (-44 : Int64).toBitVec = -44#64 := rfl
      rw [hbp, e]; bv_omega
    have l1 : s₀.dmem.loadInt (s₀.regs.get64 .rbx + Int64.toBitVec 166192) 4
        = some (Int.ofBytes (Int.toBytes 4 st.u.toInt)) := by rw [a1]; sep_mem hm2 <;> rfl
    have l2 : s₀.dmem.loadInt (s₀.regs.get64 .rbp + (-44 : Int64).toBitVec) 4
        = some (Int.ofBytes (Int.toBytes 4 (ivv t₀).toInt)) := by rw [a2]; sep_mem hm2 <;> rfl
    clear hm2 a1 a2
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
      "read_sbr_dtdf" hc]
    all_goals try call_simp
    all_goals try (have hs1 := ‹_ = s₀›; subst hs1)
    case vc1 => rw [l1]; rfl
    case vc2 => rw [l2]; rfl
    case vc3 v1 hv1 v2 hv2 _ =>
    have hv := hv1.symm.trans l1
    simp only [Option.some.injEq] at hv
    subst hv
    refine ⟨fun ra' => ⟨⟨⟨?_, trivial, trivial⟩, by simp only [sw6432,
      BitVec.ofInt_ofBytes_toBytes 32 4 rfl], h14,
      h15, hmi.1.2.2.1, hI.2.2, hF.1.2.2.2.1⟩, fun s' hpost => ?_⟩,
      fun _ => Or.inr (Or.inr (Or.inl trivial)), hld⟩
    · rw [e50]; exact hpush _
    · obtain ⟨st', ⟨hst', hi'⟩, hsp', hbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩ := hpost
      rw [e50] at hm'
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, st', ⟨?_, ?_, hi'⟩, ?_, hm'⟩, Nat.le_refl _⟩
      · exact hsp'.trans e72
      · exact hbp'.trans hbp
      · exact h12'.trans h12
      · exact hbx'.trans hbx
      · exact h14'.trans h14
      · exact h13'.trans h13
      · rw [hst']; exact hI.1
      · rw [hst']; exact hI.2.1
      · rw [hst']; exact ⟨⟨hmi, hid, hu⟩, hl0, hl1⟩

/-- `read_sbr_dtdf(sbr->usac, gb, &sbr->data[1], indep_flag)` of a coupled pair, channel 1. -/
theorem blk_L3999 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData)
    (hc : DtdfSpec k 1 A.1.Ext A.1.Oth) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L3999" := by
  cfg_block
  measure_hb "L3999"
    intro n
    simp only [tbl_L3999, var_L3999, tbl_L39b8, var_L39b8]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, hP, hm⟩, rfl⟩ := hs₀
    simp only [UM] at hm
    obtain ⟨⟨hmi, hid, hu⟩, hl0, hl1⟩ := hP
    have hm2 := hm
    simp only [UF, SHW, sA, LocI, BitVec.add_assoc, BitVec.reduceAdd] at hm2
    have a1 : s₀.regs.get64 .rbx + Int64.toBitVec 166192 = A.1.c + 166192#64 := by
      rw [hbx]; exact congrArg (A.1.c + ·) rfl
    have l1 : s₀.dmem.loadInt (s₀.regs.get64 .rbx + Int64.toBitVec 166192) 4
        = some (Int.ofBytes (Int.toBytes 4 st.u.toInt)) := by rw [a1]; sep_mem hm2 <;> rfl
    clear hm2 a1
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
      "read_sbr_dtdf" hc]
    all_goals try call_simp
    all_goals try (have hs1 := ‹_ = s₀›; subst hs1)
    case vc1 => rw [l1]; rfl
    case vc2 v1 hv1 _ =>
    have hv := hv1.symm.trans l1
    simp only [Option.some.injEq] at hv
    subst hv
    refine ⟨fun ra' => ⟨⟨⟨?_, trivial, trivial⟩, by simp only [sw6432,
      BitVec.ofInt_ofBytes_toBytes 32 4 rfl], h14,
      by rw [hbx]; exact dac1 _, hmi.1.2.2.2.1, hI.2.2, hF.1.2.2.2.1⟩, fun s' hpost => ?_⟩,
      fun _ => Or.inr (Or.inr (Or.inl trivial)), hld⟩
    · rw [e50]; exact hpush _
    · obtain ⟨st', ⟨hst', hi'⟩, hsp', hbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩ := hpost
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
      · rw [hst']; exact ⟨⟨hmi, hid, hu⟩, hl0, hl1⟩
      · rw [h15', hbx]; exact dac0 _

/-- `read_sbr_dtdf(sbr->usac, gb, &sbr->data[0], indep_flag)` of a channel
pair, channel 0 (`r13` takes `&data[0]`). -/
theorem blk_L37e3 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData)
    (hc : DtdfSpec k 0 A.1.Ext A.1.Oth) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L37e3" := by
  cfg_block
  measure_hb "L37e3"
    intro n
    simp only [tbl_L37e3, var_L37e3, tbl_L37fe, var_L37fe]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, hP, hm⟩, h15⟩, rfl⟩ := hs₀
    simp only [UM] at hm
    obtain ⟨⟨hmi, hid, hu⟩, hl0, hl1⟩ := hP
    have hm2 := hm
    simp only [UF, SHW, sA, LocI, BitVec.add_assoc, BitVec.reduceAdd] at hm2
    have a1 : s₀.regs.get64 .rbx + Int64.toBitVec 166192 = A.1.c + 166192#64 := by
      rw [hbx]; exact congrArg (A.1.c + ·) rfl
    have a2 : s₀.regs.get64 .rbp + (-44 : Int64).toBitVec = t₀.regs.get64 .rsp - 52#64 := by
      have e : (-44 : Int64).toBitVec = -44#64 := rfl
      rw [hbp, e]; bv_omega
    have l1 : s₀.dmem.loadInt (s₀.regs.get64 .rbx + Int64.toBitVec 166192) 4
        = some (Int.ofBytes (Int.toBytes 4 st.u.toInt)) := by rw [a1]; sep_mem hm2 <;> rfl
    have l2 : s₀.dmem.loadInt (s₀.regs.get64 .rbp + (-44 : Int64).toBitVec) 4
        = some (Int.ofBytes (Int.toBytes 4 (ivv t₀).toInt)) := by rw [a2]; sep_mem hm2 <;> rfl
    clear hm2 a1 a2
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
      "read_sbr_dtdf" hc]
    all_goals try call_simp
    all_goals try (have hs1 := ‹_ = s₀›; subst hs1)
    case vc1 => rw [l1]; rfl
    case vc2 => rw [l2]; rfl
    case vc3 v1 hv1 v2 hv2 _ =>
    have hv := hv1.symm.trans l1
    simp only [Option.some.injEq] at hv
    subst hv
    refine ⟨fun ra' => ⟨⟨⟨?_, trivial, trivial⟩, by simp only [sw6432,
      BitVec.ofInt_ofBytes_toBytes 32 4 rfl], h14,
      h15, hmi.1.2.2.1, hI.2.2, hF.1.2.2.2.1⟩, fun s' hpost => ?_⟩,
      fun _ => Or.inr (Or.inr (Or.inl trivial)), hld⟩
    · rw [e50]; exact hpush _
    · obtain ⟨st', ⟨hst', hi'⟩, hsp', hbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩ := hpost
      rw [e50] at hm'
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, st', ⟨?_, ?_, hi'⟩, ?_, hm'⟩, Nat.le_refl _⟩
      · exact hsp'.trans e72
      · exact hbp'.trans hbp
      · exact h12'.trans h12
      · exact hbx'.trans hbx
      · exact h14'.trans h14
      · exact h13'.trans h15
      · rw [hst']; exact hI.1
      · rw [hst']; exact hI.2.1
      · rw [hst']; exact ⟨⟨hmi, hid, hu⟩, hl0, hl1⟩

/-- `read_sbr_dtdf(sbr->usac, gb, &sbr->data[1], indep_flag)` of a channel
pair, channel 1 (`r15` takes `&data[0]` back). -/
theorem blk_L37fe (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData)
    (hc : DtdfSpec k 1 A.1.Ext A.1.Oth) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L37fe" := by
  cfg_block
  measure_hb "L37fe"
    intro n
    simp only [tbl_L37fe, var_L37fe, tbl_L3819, var_L3819]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, hP, hm⟩, rfl⟩ := hs₀
    simp only [UM] at hm
    obtain ⟨⟨hmi, hid, hu⟩, hl0, hl1⟩ := hP
    have hm2 := hm
    simp only [UF, SHW, sA, LocI, BitVec.add_assoc, BitVec.reduceAdd] at hm2
    have a1 : s₀.regs.get64 .rbx + Int64.toBitVec 166192 = A.1.c + 166192#64 := by
      rw [hbx]; exact congrArg (A.1.c + ·) rfl
    have l1 : s₀.dmem.loadInt (s₀.regs.get64 .rbx + Int64.toBitVec 166192) 4
        = some (Int.ofBytes (Int.toBytes 4 st.u.toInt)) := by rw [a1]; sep_mem hm2 <;> rfl
    clear hm2 a1
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
      "read_sbr_dtdf" hc]
    all_goals try call_simp
    all_goals try (have hs1 := ‹_ = s₀›; subst hs1)
    case vc1 => rw [l1]; rfl
    case vc2 v1 hv1 _ =>
    have hv := hv1.symm.trans l1
    simp only [Option.some.injEq] at hv
    subst hv
    refine ⟨fun ra' => ⟨⟨⟨?_, trivial, trivial⟩, by simp only [sw6432,
      BitVec.ofInt_ofBytes_toBytes 32 4 rfl], h14,
      by rw [hbx]; exact dac1 _, hmi.1.2.2.2.1, hI.2.2, hF.1.2.2.2.1⟩, fun s' hpost => ?_⟩,
      fun _ => Or.inr (Or.inr (Or.inl trivial)), hld⟩
    · rw [e50]; exact hpush _
    · obtain ⟨st', ⟨hst', hi'⟩, hsp', hbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩ := hpost
      rw [e50] at hm'
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, st', ⟨?_, ?_, hi'⟩, ?_, hm'⟩, Nat.le_refl _⟩
      · exact hsp'.trans e72
      · exact hbp'.trans hbp
      · exact h12'.trans h12
      · exact hbx'.trans hbx
      · exact h14'.trans h14
      · exact h15'.trans h13
      · rw [hst']; exact hI.1
      · rw [hst']; exact hI.2.1
      · rw [hst']; exact ⟨⟨hmi, hid, hu⟩, hl0, hl1⟩

end Kraken.Examples.Sbr.Usac
