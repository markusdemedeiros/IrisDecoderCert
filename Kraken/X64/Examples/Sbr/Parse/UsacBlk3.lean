import Kraken.X64.Examples.Sbr.Parse.UsacBlk2
import Kraken.X64.Examples.Sbr.Parse.UsacTbl3
import Kraken.X64.Examples.Sbr.Parse.UsacTbl4
import Kraken.X64.Examples.Sbr.Parse.UsacTbl5
import Kraken.X64.Examples.Sbr.Parse.UsacTbl6
open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse
set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

/-! # `ff_aac_sbr_decode_usac_data`: the calls of `read_sbr_invf`, `read_sbr_envelope`,
`read_sbr_noise`

Each call block: the frame `UM` is the callee's `CallPre (cneed k)` with the caller's part
`Rst`; the return state goes back into the frame. -/
namespace Kraken.Examples.Sbr.Usac
variable [CodeEnv]

/-- The caller's part of the memory at a call: the locals, the saved registers, the return
address, the caller's rest. -/
abbrev Rst (A : UA) (ra : Int64) (t₀ : MachineData) (Lc : Mem 64 → Prop) : Mem 64 → Prop :=
  Lc ⋆ (Sv t₀ ⋆ (RetCell ra (t₀.regs.get64 .rsp) ⋆ A.1.R))

/-- The logical variables of a callee: `R` the caller's part. -/
abbrev cA (A : UA) (ra : Int64) (t₀ : MachineData) (Lc : Mem 64 → Prop) (st : USt) : UA :=
  ({ A.1 with R := Rst A ra t₀ Lc }, st)

omit [CodeEnv] in
/-- `lea 0x3e460(%rbx)` is `&sbr->data[1]`. -/
theorem dac1 (c : BitVec 64) : c + Int64.toBitVec 255072 = dAc c 1 := by
  unfold dAc; rw [BitVec.add_assoc]; rfl

/-- `read_sbr_invf(sbr, gb, &sbr->data[0])` of the single channel element. -/
theorem blk_L3644 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData)
    (hc : InvfSpec k 0 A.1.Ext A.1.Oth) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L3644" := by
  cfg_block
  measure_hb "L3644"
    intro n
    simp only [tbl_L3644, var_L3644, tbl_L3652, var_L3652]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, hP, hm⟩, h15⟩, hch⟩, rfl⟩ := hs₀
    simp only [UM] at hm
    obtain ⟨⟨hmi, hid, hu⟩, hlive⟩ := hP
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
    rename_i s1 hs1
    subst hs1
    refine ⟨fun ra' => ⟨⟨⟨?_, trivial, trivial⟩, h13, h14, h15, hmi.1.1, hmi.1.2.2.1, hI.2.2,
      hF.1.2.2.2.1⟩,
      fun s' hpost => ?_⟩, fun _ => Or.inr (Or.inr (Or.inl trivial)), hld⟩
    · rw [e50]; exact hpush _
    · obtain ⟨st', ⟨vals, hst', hi'⟩, hsp', hbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩ := hpost
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
      · rw [hst']
        exact ⟨⟨mi_d0 hmi (dwf_invfRead hmi.1.2.2.1)
          (by rw [invfRead_te, invfRead_nenv]; exact hmi.1.2.2.2.2.2.1), hid, hu⟩,
          live_invfRead hlive⟩
      · exact h15'.trans h15

/-- `read_sbr_envelope(ac, sbr, gb, &sbr->data[0], 0)` of the single channel element. -/
theorem blk_L3652 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData)
    (hc : EnvNoiseSpec "read_sbr_envelope" k 0 A.1.Ext A.1.Oth) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L3652" := by
  cfg_block
  measure_hb "L3652"
    intro n
    simp only [tbl_L3652, var_L3652, tbl_L3666, var_L3666]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, hP, hm⟩, h15⟩, hch⟩, rfl⟩ := hs₀
    simp only [UM] at hm
    obtain ⟨⟨hmi, hid, hu⟩, hlive⟩ := hP
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
    vcgen [call_procS_spec_at (cA A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) st)
      "read_sbr_envelope" hc]
    all_goals try call_simp
    have hs1 := ‹_ = s₀›
    subst hs1
    refine ⟨fun ra' => ⟨⟨⟨?_, trivial, trivial⟩, h12, h13, h14, h15, ?_, hmi, hlive, hI.2.2,
      hF.1.2.2.2.1, hF.1.2.2.2.2.2.2.2⟩,
      fun s' hpost => ?_⟩, fun _ ha _ => Or.inr (Or.inr ha), hld⟩
    · rw [e50]; exact hpush _
    · simp
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
      · rw [hst']; exact ⟨⟨hmi, hid, hu⟩, hlive⟩
      · exact h15'.trans h15

/-- `read_sbr_noise(ac, sbr, gb, &sbr->data[0], 0)` of the single channel element. -/
theorem blk_L366e (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData)
    (hc : EnvNoiseSpec "read_sbr_noise" k 0 A.1.Ext A.1.Oth) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L366e" := by
  cfg_block
  measure_hb "L366e"
    intro n
    simp only [tbl_L366e, var_L366e, tbl_L3682, var_L3682]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, hP, hm⟩, h15⟩, hch⟩, rfl⟩ := hs₀
    simp only [UM] at hm
    obtain ⟨⟨hmi, hid, hu⟩, hlive⟩ := hP
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
    vcgen [call_procS_spec_at (cA A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) st)
      "read_sbr_noise" hc]
    all_goals try call_simp
    have hs1 := ‹_ = s₀›
    subst hs1
    refine ⟨fun ra' => ⟨⟨⟨?_, trivial, trivial⟩, h12, h13, h14, h15, ?_, hmi, hlive, hI.2.2,
      hF.1.2.2.2.1, hF.1.2.2.2.2.2.2.2⟩,
      fun s' hpost => ?_⟩, fun _ ha _ => Or.inr (Or.inr ha), hld⟩
    · rw [e50]; exact hpush _
    · simp
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
      · rw [hst']; exact ⟨⟨hmi, hid, hu⟩, hlive⟩
      · exact h15'.trans h15

/-- `read_sbr_envelope(ac, sbr, gb, &sbr->data[0], 0)` of a channel pair. -/
theorem blk_L3860 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData)
    (hc : EnvNoiseSpec "read_sbr_envelope" k 0 A.1.Ext A.1.Oth) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L3860" := by
  cfg_block
  measure_hb "L3860"
    intro n
    simp only [tbl_L3860, var_L3860, tbl_L3874, var_L3874]
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
    vcgen [call_procS_spec_at (cA A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) st)
      "read_sbr_envelope" hc]
    all_goals try call_simp
    have hs1 := ‹_ = s₀›
    subst hs1
    refine ⟨fun ra' => ⟨⟨⟨?_, trivial, trivial⟩, h12, h13, h14, ?_, ?_, hmi, hl0, hI.2.2,
      hF.1.2.2.2.1, hF.1.2.2.2.2.2.2.2⟩,
      fun s' hpost => ?_⟩, fun _ ha _ => Or.inr (Or.inr ha), hld⟩
    · rw [e50]; exact hpush _
    · first | (rw [hbx]; exact dac1 _) | exact h15
    · simp
    · obtain ⟨st', ⟨hst', hi'⟩, hsp', hbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩ := hpost
      rw [e50] at hm'
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨⟨⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, st', ⟨?_, ?_, hi'⟩, ?_, hm'⟩, ?_⟩, Nat.le_refl _⟩
      · exact hsp'.trans e72
      · exact hbp'.trans hbp
      · exact h12'.trans h12
      · exact hbx'.trans hbx
      · exact h14'.trans h14
      · exact h13'.trans h13
      · rw [hst']; exact hI.1
      · rw [hst']; exact hI.2.1
      · rw [hst']; exact ⟨⟨hmi, hid, hu⟩, hl0, hl1⟩
      · first | (rw [h15', hbx]; exact dac1 _) | exact h15'.trans h15

/-- `read_sbr_noise(ac, sbr, gb, &sbr->data[0], 0)` of a channel pair. -/
theorem blk_L387c (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData)
    (hc : EnvNoiseSpec "read_sbr_noise" k 0 A.1.Ext A.1.Oth) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L387c" := by
  cfg_block
  measure_hb "L387c"
    intro n
    simp only [tbl_L387c, var_L387c, tbl_L3890, var_L3890]
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
    vcgen [call_procS_spec_at (cA A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) st)
      "read_sbr_noise" hc]
    all_goals try call_simp
    have hs1 := ‹_ = s₀›
    subst hs1
    refine ⟨fun ra' => ⟨⟨⟨?_, trivial, trivial⟩, h12, h13, h14, ?_, ?_, hmi, hl0, hI.2.2,
      hF.1.2.2.2.1, hF.1.2.2.2.2.2.2.2⟩,
      fun s' hpost => ?_⟩, fun _ ha _ => Or.inr (Or.inr ha), hld⟩
    · rw [e50]; exact hpush _
    · first | (rw [hbx]; exact dac1 _) | exact h15
    · simp
    · obtain ⟨st', ⟨hst', hi'⟩, hsp', hbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩ := hpost
      rw [e50] at hm'
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨⟨⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, st', ⟨?_, ?_, hi'⟩, ?_, hm'⟩, ?_⟩, Nat.le_refl _⟩
      · exact hsp'.trans e72
      · exact hbp'.trans hbp
      · exact h12'.trans h12
      · exact hbx'.trans hbx
      · exact h14'.trans h14
      · exact h13'.trans h13
      · rw [hst']; exact hI.1
      · rw [hst']; exact hI.2.1
      · rw [hst']; exact ⟨⟨hmi, hid, hu⟩, hl0, hl1⟩
      · first | (rw [h15', hbx]; exact dac1 _) | exact h15'.trans h15

/-- `read_sbr_envelope(ac, sbr, gb, &sbr->data[1], 1)` of a channel pair. -/
theorem blk_L3898 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData)
    (hc : EnvNoiseSpec "read_sbr_envelope" k 1 A.1.Ext A.1.Oth) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L3898" := by
  cfg_block
  measure_hb "L3898"
    intro n
    simp only [tbl_L3898, var_L3898, tbl_L38b6, var_L38b6]
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
    vcgen [call_procS_spec_at (cA A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) st)
      "read_sbr_envelope" hc]
    all_goals try call_simp
    have hs1 := ‹_ = s₀›
    subst hs1
    refine ⟨fun ra' => ⟨⟨⟨?_, trivial, trivial⟩, h12, h13, h14, ?_, ?_, hmi, hl1, hI.2.2,
      hF.1.2.2.2.1, hF.1.2.2.2.2.2.2.2⟩,
      fun s' hpost => ?_⟩, fun _ ha _ => Or.inr (Or.inr ha), hld⟩
    · rw [e50]; exact hpush _
    · first | (rw [hbx]; exact dac1 _) | exact h15
    · simp
    · obtain ⟨st', ⟨hst', hi'⟩, hsp', hbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩ := hpost
      rw [e50] at hm'
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨⟨⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, st', ⟨?_, ?_, hi'⟩, ?_, hm'⟩, ?_⟩, Nat.le_refl _⟩
      · exact hsp'.trans e72
      · exact hbp'.trans hbp
      · exact h12'.trans h12
      · exact hbx'.trans hbx
      · exact h14'.trans h14
      · exact h13'.trans h13
      · rw [hst']; exact hI.1
      · rw [hst']; exact hI.2.1
      · rw [hst']; exact ⟨⟨hmi, hid, hu⟩, hl0, hl1⟩
      · first | (rw [h15', hbx]; exact dac1 _) | exact h15'.trans h15

/-- `read_sbr_noise(ac, sbr, gb, &sbr->data[1], 1)` of a channel pair. -/
theorem blk_L38be (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData)
    (hc : EnvNoiseSpec "read_sbr_noise" k 1 A.1.Ext A.1.Oth) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L38be" := by
  cfg_block
  measure_hb "L38be"
    intro n
    simp only [tbl_L38be, var_L38be, tbl_L38d5, var_L38d5]
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
    vcgen [call_procS_spec_at (cA A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) st)
      "read_sbr_noise" hc]
    all_goals try call_simp
    have hs1 := ‹_ = s₀›
    subst hs1
    refine ⟨fun ra' => ⟨⟨⟨?_, trivial, trivial⟩, h12, h13, h14, ?_, ?_, hmi, hl1, hI.2.2,
      hF.1.2.2.2.1, hF.1.2.2.2.2.2.2.2⟩,
      fun s' hpost => ?_⟩, fun _ ha _ => Or.inr (Or.inr ha), hld⟩
    · rw [e50]; exact hpush _
    · first | (rw [hbx]; exact dac1 _) | exact h15
    · simp
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

/-- `read_sbr_envelope(ac, sbr, gb, &sbr->data[0], 0)` of a channel pair. -/
theorem blk_L39d8 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData)
    (hc : EnvNoiseSpec "read_sbr_envelope" k 0 A.1.Ext A.1.Oth) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L39d8" := by
  cfg_block
  measure_hb "L39d8"
    intro n
    simp only [tbl_L39d8, var_L39d8, tbl_L39ec, var_L39ec]
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
    vcgen [call_procS_spec_at (cA A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) st)
      "read_sbr_envelope" hc]
    all_goals try call_simp
    have hs1 := ‹_ = s₀›
    subst hs1
    refine ⟨fun ra' => ⟨⟨⟨?_, trivial, trivial⟩, h12, h13, h14, ?_, ?_, hmi, hl0, hI.2.2,
      hF.1.2.2.2.1, hF.1.2.2.2.2.2.2.2⟩,
      fun s' hpost => ?_⟩, fun _ ha _ => Or.inr (Or.inr ha), hld⟩
    · rw [e50]; exact hpush _
    · first | (rw [hbx]; exact dac1 _) | exact h15
    · simp
    · obtain ⟨st', ⟨hst', hi'⟩, hsp', hbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩ := hpost
      rw [e50] at hm'
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨⟨⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, st', ⟨?_, ?_, hi'⟩, ?_, hm'⟩, ?_⟩, Nat.le_refl _⟩
      · exact hsp'.trans e72
      · exact hbp'.trans hbp
      · exact h12'.trans h12
      · exact hbx'.trans hbx
      · exact h14'.trans h14
      · exact h13'.trans h13
      · rw [hst']; exact hI.1
      · rw [hst']; exact hI.2.1
      · rw [hst']; exact ⟨⟨hmi, hid, hu⟩, hl0, hl1⟩
      · first | (rw [h15', hbx]; exact dac1 _) | exact h15'.trans h15

/-- `read_sbr_envelope(ac, sbr, gb, &sbr->data[1], 1)` of a channel pair. -/
theorem blk_L39f4 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData)
    (hc : EnvNoiseSpec "read_sbr_envelope" k 1 A.1.Ext A.1.Oth) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L39f4" := by
  cfg_block
  measure_hb "L39f4"
    intro n
    simp only [tbl_L39f4, var_L39f4, tbl_L3a0f, var_L3a0f]
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
    vcgen [call_procS_spec_at (cA A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) st)
      "read_sbr_envelope" hc]
    all_goals try call_simp
    have hs1 := ‹_ = s₀›
    subst hs1
    refine ⟨fun ra' => ⟨⟨⟨?_, trivial, trivial⟩, h12, h13, h14, ?_, ?_, hmi, hl1, hI.2.2,
      hF.1.2.2.2.1, hF.1.2.2.2.2.2.2.2⟩,
      fun s' hpost => ?_⟩, fun _ ha _ => Or.inr (Or.inr ha), hld⟩
    · rw [e50]; exact hpush _
    · first | (rw [hbx]; exact dac1 _) | exact h15
    · simp
    · obtain ⟨st', ⟨hst', hi'⟩, hsp', hbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩ := hpost
      rw [e50] at hm'
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨⟨⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, st', ⟨?_, ?_, hi'⟩, ?_, hm'⟩, ?_⟩, Nat.le_refl _⟩
      · exact hsp'.trans e72
      · exact hbp'.trans hbp
      · exact h12'.trans h12
      · exact hbx'.trans hbx
      · exact h14'.trans h14
      · exact h13'.trans h13
      · rw [hst']; exact hI.1
      · rw [hst']; exact hI.2.1
      · rw [hst']; exact ⟨⟨hmi, hid, hu⟩, hl0, hl1⟩
      · first | (rw [h15', hbx]; exact dac1 _) | exact h15'.trans h15

/-- `read_sbr_noise(ac, sbr, gb, &sbr->data[0], 0)` of a channel pair. -/
theorem blk_L3a17 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData)
    (hc : EnvNoiseSpec "read_sbr_noise" k 0 A.1.Ext A.1.Oth) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L3a17" := by
  cfg_block
  measure_hb "L3a17"
    intro n
    simp only [tbl_L3a17, var_L3a17, tbl_L3a2b, var_L3a2b]
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
    vcgen [call_procS_spec_at (cA A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) st)
      "read_sbr_noise" hc]
    all_goals try call_simp
    have hs1 := ‹_ = s₀›
    subst hs1
    refine ⟨fun ra' => ⟨⟨⟨?_, trivial, trivial⟩, h12, h13, h14, ?_, ?_, hmi, hl0, hI.2.2,
      hF.1.2.2.2.1, hF.1.2.2.2.2.2.2.2⟩,
      fun s' hpost => ?_⟩, fun _ ha _ => Or.inr (Or.inr ha), hld⟩
    · rw [e50]; exact hpush _
    · first | (rw [hbx]; exact dac1 _) | exact h15
    · simp
    · obtain ⟨st', ⟨hst', hi'⟩, hsp', hbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩ := hpost
      rw [e50] at hm'
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨⟨⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, st', ⟨?_, ?_, hi'⟩, ?_, hm'⟩, ?_⟩, Nat.le_refl _⟩
      · exact hsp'.trans e72
      · exact hbp'.trans hbp
      · exact h12'.trans h12
      · exact hbx'.trans hbx
      · exact h14'.trans h14
      · exact h13'.trans h13
      · rw [hst']; exact hI.1
      · rw [hst']; exact hI.2.1
      · rw [hst']; exact ⟨⟨hmi, hid, hu⟩, hl0, hl1⟩
      · first | (rw [h15', hbx]; exact dac1 _) | exact h15'.trans h15

/-- `read_sbr_noise(ac, sbr, gb, &sbr->data[1], 1)` of a channel pair. -/
theorem blk_L3a33 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData)
    (hc : EnvNoiseSpec "read_sbr_noise" k 1 A.1.Ext A.1.Oth) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L3a33" := by
  cfg_block
  measure_hb "L3a33"
    intro n
    simp only [tbl_L3a33, var_L3a33, tbl_L3a4e, var_L3a4e]
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
    vcgen [call_procS_spec_at (cA A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) st)
      "read_sbr_noise" hc]
    all_goals try call_simp
    have hs1 := ‹_ = s₀›
    subst hs1
    refine ⟨fun ra' => ⟨⟨⟨?_, trivial, trivial⟩, h12, h13, h14, ?_, ?_, hmi, hl1, hI.2.2,
      hF.1.2.2.2.1, hF.1.2.2.2.2.2.2.2⟩,
      fun s' hpost => ?_⟩, fun _ ha _ => Or.inr (Or.inr ha), hld⟩
    · rw [e50]; exact hpush _
    · first | (rw [hbx]; exact dac1 _) | exact h15
    · simp
    · obtain ⟨st', ⟨hst', hi'⟩, hsp', hbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩ := hpost
      rw [e50] at hm'
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨⟨⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, st', ⟨?_, ?_, hi'⟩, ?_, hm'⟩, ?_⟩, Nat.le_refl _⟩
      · exact hsp'.trans e72
      · exact hbp'.trans hbp
      · exact h12'.trans h12
      · exact hbx'.trans hbx
      · exact h14'.trans h14
      · exact h13'.trans h13
      · rw [hst']; exact hI.1
      · rw [hst']; exact hI.2.1
      · rw [hst']; exact ⟨⟨hmi, hid, hu⟩, hl0, hl1⟩
      · first | (rw [h15', hbx]; exact dac1 _) | exact h15'.trans h15

end Kraken.Examples.Sbr.Usac
