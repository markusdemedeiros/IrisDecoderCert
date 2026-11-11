import Kraken.X64.Examples.Sbr.Parse.EnvBlk3

/-!
# `read_sbr_envelope`: the epilogue and the error path
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Vlc
open Kraken.Examples.Sbr.Parse (Hide eq_r eq_l eq_h)

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Env

variable [CodeEnv]

section Saved

variable (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) (fv : FV)
  (i : BitVec 32)

theorem T_sv_rbp : ∃ F, T k Ext x ra t₀ fv i
    = c8 (t₀.regs.get64 .rsp - 8#64) (t₀.regs.get64 .rbp) ⋆ F := by
  simp only [T, Sv]; exact ⟨_, eq_l eq_h⟩

theorem T_sv_r15 : ∃ F, T k Ext x ra t₀ fv i
    = c8 (t₀.regs.get64 .rsp - 0x10#64) (t₀.regs.get64 .r15) ⋆ F := by
  simp only [T, Sv]; exact ⟨_, eq_l (eq_r eq_h)⟩

theorem T_sv_r14 : ∃ F, T k Ext x ra t₀ fv i
    = c8 (t₀.regs.get64 .rsp - 0x18#64) (t₀.regs.get64 .r14) ⋆ F := by
  simp only [T, Sv]; exact ⟨_, eq_l (eq_r (eq_r eq_h))⟩

theorem T_sv_r13 : ∃ F, T k Ext x ra t₀ fv i
    = c8 (t₀.regs.get64 .rsp - 0x20#64) (t₀.regs.get64 .r13) ⋆ F := by
  simp only [T, Sv]; exact ⟨_, eq_l (eq_r (eq_r (eq_r eq_h)))⟩

theorem T_sv_r12 : ∃ F, T k Ext x ra t₀ fv i
    = c8 (t₀.regs.get64 .rsp - 0x28#64) (t₀.regs.get64 .r12) ⋆ F := by
  simp only [T, Sv]; exact ⟨_, eq_l (eq_r (eq_r (eq_r (eq_r eq_h))))⟩

theorem T_sv_rbx : ∃ F, T k Ext x ra t₀ fv i
    = c8 (t₀.regs.get64 .rsp - 0x30#64) (t₀.regs.get64 .rbx) ⋆ F := by
  simp only [T, Sv]; exact ⟨_, eq_l (eq_r (eq_r (eq_r (eq_r eq_t))))⟩

end Saved

omit [CodeEnv] in
theorem pop_offs' (t : BitVec 64) : BitVec.setWidth 64 (Int64.toBitVec 120) + (t - 168#64) = t - 48#64
    ∧ t - 48#64 + 8#64 = t - 40#64 ∧ t - 40#64 + 8#64 = t - 32#64 ∧ t - 32#64 + 8#64 = t - 24#64
    ∧ t - 24#64 + 8#64 = t - 16#64 ∧ t - 16#64 + 8#64 = t - 8#64 ∧ t - 8#64 + 8#64 = t := by
  rw [show BitVec.setWidth 64 (Int64.toBitVec 120) = 120#64 from rfl]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_omega

theorem T_ld8 {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : EArgs} {ra : Int64}
    {t₀ : MachineData} {fv : FV} {i : BitVec 32} {a v : BitVec 64}
    (h : m =⋆ T k Ext x ra t₀ fv i) (hF : ∃ F, T k Ext x ra t₀ fv i = c8 a v ⋆ F) :
    m.loadInt a 8 = some (Int.ofBytes (Int.toBytes 8 v.toInt)) := by
  obtain ⟨F, hF⟩ := hF
  exact T_ld_at h hF 8 (Int.toBytes_length 8 _) (by omega)

theorem blk_L60a6 (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L60a6" := by
  cfg_block
  measure_hb "L60a6"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, gi, ⟨hC, hsp, hbp, hgi, hm⟩, hret⟩, hn⟩ := hs₀
    have l1 := T_ld8 hm (T_sv_rbx k Ext x ra t₀ fv gi)
    have l2 := T_ld8 hm (T_sv_r12 k Ext x ra t₀ fv gi)
    have l3 := T_ld8 hm (T_sv_r13 k Ext x ra t₀ fv gi)
    have l4 := T_ld8 hm (T_sv_r14 k Ext x ra t₀ fv gi)
    have l5 := T_ld8 hm (T_sv_r15 k Ext x ra t₀ fv gi)
    have l6 := T_ld8 hm (T_sv_rbp k Ext x ra t₀ fv gi)
    have hmT : Hide _ := hm
    clear hm
    have po := pop_offs' (t₀.regs.get64 .rsp)
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hsp, po.1, po.2.1, po.2.2.1,
      po.2.2.2.1, po.2.2.2.2.1, po.2.2.2.2.2.1, po.2.2.2.2.2.2] at *
    all_goals simp only [l1, l2, l3, l4, l5, l6, Option.isSome_some, Option.some.injEq] at *
    subst_vars
    refine ⟨⟨?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, fv, gi, hgi, hmT⟩, ?_⟩
    all_goals try rsimp
    all_goals try simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]
    · show BitVec.setWidth 32 _ = _ ∨ BitVec.setWidth 32 _ = _
      rsimp; exact hret
    · rw [var_done, var_L60a6]; try exact Nat.le_refl _

theorem T_ret (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData)
    (fv : FV) (gi : BitVec 32) :
    T k Ext x ra t₀ fv gi = RetCell ra (t₀.regs.get64 .rsp) ⋆ (Sv t₀
      ⋆ (FrW (t₀.regs.get64 .rsp) fv ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xb0#64)
      ⋆ (Reserve k (t₀.regs.get64 .rsp - 0xb0#64) ⋆ (EF Ext x t₀ gi ⋆ x.R))))) := by
  simp only [T, Rest]; ac_rfl

theorem blk_done (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.done" := by
  cfg_block
  measure_hb "done"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hsp, hbp, hsv, hret, fv, gi, hgi, hm⟩, hn⟩ := hs₀
    rw [T_ret] at hm
    have l0 : s₀.dmem.loadInt (t₀.regs.get64 .rsp) 8
        = some (Int.ofBytes (Int.toBytes 8 ra.toBitVec.toInt)) :=
      loadInt_sep _ _ 8 _ _ hm (Int.toBytes_length _ _) (by omega)
    have hpost := Block.sep_intro (Int.toBytes_length _ _) (by decide) hm
    have hra : s₀.retAddr = some ra := by
      simp only [MachineData.retAddr, hsp, l0, Option.map_some,
        BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Int64.ofBitVec_toBitVec]
    clear hm l0
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals simp only [hra, Option.isSome_some, Option.some.injEq] at *
    subst_vars
    right; left
    refine ⟨rfl, gi, ⟨hgi, ?_⟩, ?_, ?_, ?_, fv, hpost⟩
    all_goals try rsimp
    · exact hret
    · rw [hsp]; rfl
    · exact hbp
    · exact hsv

theorem blk_L6063 (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L6063" := by
  cfg_block
  measure_hb "L6063"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, gi, ⟨hC, hsp, hbp, hgi, hm⟩⟩, hn⟩ := hs₀
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    left; apply Table.ofLabels_at
    refine ⟨by decide, ⟨fv, gi, ⟨hC, ?_, ?_, hgi, hm⟩, ?_⟩, Or.inr ⟨?_, by decide⟩⟩
    all_goals try rsimp
    · exact hsp
    · exact hbp
    · right; rfl
    · rw [var_L60a6, var_L6063]

theorem blk_L603e (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L603e" := by
  cfg_block
  measure_hb "L603e"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, gi, ⟨hC, hsp, hbp, hgi, hm⟩, h50⟩, hn⟩ := hs₀
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    left; apply Table.ofLabels_at
    refine ⟨by decide, ⟨fv, gi, ⟨hC, ?_, ?_, hgi, hm⟩, h50⟩, Or.inr ⟨?_, by decide⟩⟩
    all_goals try rsimp
    · exact hsp
    · exact hbp
    · rw [var_L6048, var_L603e]

theorem blk_L6044 (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L6044" := by
  cfg_block
  measure_hb "L6044"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, gi, ⟨hC, hsp, hbp, hgi, hm⟩, h50⟩, hn⟩ := hs₀
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    refine ⟨⟨fv, gi, ⟨hC, ?_, ?_, hgi, hm⟩, h50⟩, ?_⟩
    all_goals try rsimp
    · exact hsp
    · exact hbp
    · rw [var_L6048, var_L6044]; try exact Nat.le_refl _

/-- `T` with `av_log`'s frame at the head: the return slot, the callee's reservation, `Ext`. -/
theorem T_ext (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData)
    (fv : FV) (i : BitVec 32) :
    ∃ F, T k Ext x ra t₀ fv i = 8 ?@ (t₀.regs.get64 .rsp - 0xb0#64)
      ⋆ (Reserve k (t₀.regs.get64 .rsp - 0xb0#64) ⋆ (Ext ⋆ F)) := by
  refine ⟨Sv t₀ ⋆ (FrW (t₀.regs.get64 .rsp) fv ⋆ (ChE (arg3 t₀) x ⋆ (SbrE (arg1 t₀) x
    ⋆ (GbE (arg2 t₀) x i ⋆ (c8 (arg0 t₀ + 8#64) x.avctx ⋆ (Blocks [(x.buf, x.L)]
    ⋆ VlcW x.vt)))))) ⋆ Rest x.R ra t₀, ?_⟩
  simp only [T, EF, InE]; ac_rfl

/-- `av_log(ac->avctx, AV_LOG_ERROR, …)`. -/
theorem blk_L6048 (k : Nat) (Ext : Mem 64 → Prop) (hAv : AvLogSpec Ext k)
    (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L6048" := by
  cfg_block
  measure_hb "L6048"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, gi, ⟨hC, hsp, hbp, hgi, hm⟩, h50⟩, hn⟩ := hs₀
    have hl50 := T_ld_f50 hm
    have hav := T_ld_avctx hm
    obtain ⟨F, hF⟩ := T_ext k Ext x ra t₀ fv gi
    rw [hF] at hm
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rsp - 8#64) 8).isSome = true := by
      rw [hsp, BitVec.sub_sub_ofNat]
      exact Block.loadInt_isSome hm (by simp)
    have hpush := fun v => Block.storeInt_val hm (Split.here _ _) v
    have e48 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 0xb0#64 := by
      rw [hsp]; show _ - 168#64 - 8#64 = _; bv_omega
    vcgen [MachineWP.call_proc_spec_at F "av_log" hAv]
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    · rsimp; rw [hbp, hl50]; rfl
    · rename_i v hv
      rsimp at hv; rw [hbp, hl50] at hv; cases hv
      rsimp
      rw [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, h50,
        show Int64.toBitVec 8 = 8#64 from rfl, hav]; rfl
    rename_i v hv v2 b hv2
    rsimp at hv; rw [hbp, hl50] at hv; cases hv
    refine ⟨fun ra' => ⟨⟨?_, trivial⟩, fun s' hpost => ?_⟩, hld⟩
    · rw [e48]; exact hpush _
    · rw [e48] at hpost
      obtain ⟨hsp', hbp', -, hm'⟩ := hpost
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨⟨fv, gi, ⟨hC, ?_, ?_, hgi, ?_⟩⟩, ?_⟩
      · rw [hsp']; bv_omega
      · rw [hbp']; exact hbp
      · exact (congrFun hF s'.dmem).mpr hm'
      · rw [var_L6063, var_L6048]; try exact Nat.le_refl _

end Kraken.Examples.Sbr.Env
