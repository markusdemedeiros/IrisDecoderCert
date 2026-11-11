import Kraken.X64.Examples.Sbr.Parse.PsBlkHLib

/-!
# `ff_ps_read_data`: the header fields, the error exits
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Ps

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm


set_option maxRecDepth 20000 in
/-- `iid_mode` out of range: the message, to the error path. -/
theorem blk_Laa (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.Laa" := by
  cfg_block
  measure_hb "Laa"
    intro n
    simp only [tab_Laa, var_Laa]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, ⟨hC, ⟨hsp, hbp, hf, hP, hbl, h08, hid⟩, hm⟩, hbx, hR⟩, hn⟩ := hs₀
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    left
    refine Table.ofLabels_at (l := "ff_ps_read_data.L1464") ⟨rfl, ?_, Or.inl ?_⟩
    · refine (tab_L1464 _ _ _ _ _ _).mpr ?_
      unfold q1464 AtErr Cm Bs
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
      exact ⟨c, f, ⟨hC, ⟨hsp, hbp, hf, hP, hbl, h08, hid⟩, hm⟩, hbx, hR⟩
    · rw [var_L1464]; first | var_step | exact Kraken.lex_cons_lt_of_lt rfl (by decide)

set_option maxRecDepth 20000 in
/-- `icc_mode` out of range: the message, to the error path. -/
theorem blk_L148 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L148" := by
  cfg_block
  measure_hb "L148"
    intro n
    simp only [tab_L148, var_L148]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, ⟨hC, ⟨hsp, hbp, hf, hP, hbl, h08, hid⟩, hm⟩, hbx, hR⟩, hn⟩ := hs₀
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    left
    refine Table.ofLabels_at (l := "ff_ps_read_data.L1464") ⟨rfl, ?_, Or.inl ?_⟩
    · refine (tab_L1464 _ _ _ _ _ _).mpr ?_
      unfold q1464 AtErr Cm Bs
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
      exact ⟨c, f, ⟨hC, ⟨hsp, hbp, hf, hP, hbl, h08, hid⟩, hm⟩, hbx, hR⟩
    · rw [var_L1464]; first | var_step | exact Kraken.lex_cons_lt_of_lt rfl (by decide)

set_option maxRecDepth 20000 in
/-- `iid_mode ≤ 5`: `nr_iid_par` from the table. -/
theorem blk_Lbf (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.Lbf" := by
  cfg_block
  measure_hb "Lbf"
    intro n
    simp only [tab_Lbf, var_Lbf, tab_Ld7, var_Ld7, var_L17a9]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hHB, h0, hix, ha5, hcz⟩, hn⟩ := hs₀
    have hHB' := hHB
    obtain ⟨⟨hC, ⟨hsp, hbp, hf, hP, hbl, h08, hid⟩, hm⟩, ⟨h13, h12⟩, hbx, hKp⟩ := hHB'
    have hcl : c.length = 764 := hP.1
    have hj : (s₀.regs.get64 .rax).toNat < 6 := by omega
    have eidx : BitVec.setWidth 64 (BitVec.setWidth 32 (s₀.regs.get64 .rax))
        + lab "nr_iidicc_par_tab"
        = lab "nr_iidicc_par_tab" + BitVec.ofNat 64 (s₀.regs.get64 .rax).toNat := by
      rw [BitVec.add_comm]; congr 1; apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
    have ecx : BitVec.setWidth 64 (BitVec.setWidth 32 (s₀.regs.get64 .rax)) = s₀.regs.get64 .rax := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth]; omega
    have hL := Fr_iidicc hm _ hj
    have hv := iidicc_val _ hj
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals pnorm at *
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      AddrIndex.offset64, Width.bytes, BitVec.mul_one, BitVec.setWidth_32_64_32] at *
    all_goals try simp only [hbx]
    case vc1 =>
      exfalso; rename_i ha
      simp only [CondCode.interp_a] at ha
      rcases hcz with h | h <;> simp [h] at ha
    case vc2 => rw [eidx, hL]; rfl
    case vc3 => exact Fr_c_isSome hm hcl 12 4 (by omega)
    case vc4 =>
      rename_i hld
      rw [eidx, hL, Option.some.injEq] at hld
      subst hld
      refine ⟨?_, by var_step⟩
      unfold qd7 HB Cm Bs
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
      refine ⟨_, f, ⟨⟨hC, ⟨?_, ?_, hf, PsInv_wr_field hP 12 _ (by omega) (by omega)
          (fun _ => by rcases hv with h | h | h <;> omega),
          hbl, h08, hid⟩, Fr_c_store hm hcl 12 4 (by omega) _⟩,
        ⟨?_, ?_⟩, ?_, Kp_wr hKp 12 4 _ (by omega) (by omega) (by omega)⟩, h0, ?_, ?_, ?_, ?_⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
      all_goals first | assumption | exact ecx | (rw [i32_wr_same _ _ _ (by omega)]; exact hv)

set_option maxRecDepth 20000 in
/-- `quant` and `nr_iid_opd` from `iid_mode`. -/
theorem blk_Ld7 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.Ld7" := by
  cfg_block
  measure_hb "Ld7"
    intro n
    simp only [tab_Ld7, var_Ld7, tab_Lf3, var_Lf3]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hHB, h0, hix, ha5, hrc, hv12⟩, hn⟩ := hs₀
    have hHB' := hHB
    obtain ⟨⟨hC, ⟨hsp, hbp, hf, hP, hbl, h08, hid⟩, hm⟩, ⟨h13, h12⟩, hbx, hKp⟩ := hHB'
    have hcl : c.length = 764 := hP.1
    have hj : (s₀.regs.get64 .rax).toNat < 6 := by omega
    have eidx : s₀.regs.get64 .rcx + lab "nr_iidopd_par_tab"
        = lab "nr_iidopd_par_tab" + BitVec.ofNat 64 (s₀.regs.get64 .rax).toNat := by
      rw [BitVec.add_comm, hrc, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have hL : ∀ v : Int, (s₀.dmem.storeInt (arg2 t₀ + BitVec.ofNat 64 8) 4 v).loadInt
        (lab "nr_iidopd_par_tab" + BitVec.ofNat 64 (s₀.regs.get64 .rax).toNat) 1
        = some (rd [5, 11, 17, 5, 11, 17] (s₀.regs.get64 .rax).toNat 1) := fun v =>
      Fr_iidopd (Fr_c_store hm hcl 8 4 (by omega) v) _ hj
    have hv := iidopd_val _ hj
    have hc1 : ∀ v, (wr c 8 4 v).length = 764 := fun v => (wr_length c 8 4 v (by omega)).trans hcl
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals pnorm at *
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      AddrIndex.offset64, Width.bytes, BitVec.mul_one, BitVec.setWidth_32_64_32] at *
    all_goals try simp only [hbx]
    case vc1 => exact Fr_c_isSome hm hcl 8 4 (by omega)
    case vc2 => rw [eidx, hL]; rfl
    case vc3 =>
      exact Fr_c_isSome (Fr_c_store hm hcl 8 4 (by omega) _)
        (by rw [wr_length _ _ _ _ (by omega)]; exact hcl) 16 4 (by omega)
    case vc4 =>
      rename_i hld
      rw [hbx, eidx, hL, Option.some.injEq] at hld
      subst hld
      refine ⟨?_, by var_step⟩
      unfold qf3 HB Cm Bs
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
      refine ⟨_, f, ⟨⟨hC, ⟨?_, ?_, hf,
          PsInv_wr_field (PsInv_wr_field hP 8 _ (by omega) (fun _ => setb_toInt _ _) (by omega))
            16 _ (by omega) (by omega) (fun _ => hv),
          hbl, h08, hid⟩, Fr_c_store (Fr_c_store hm hcl 8 4 (by omega) _) (hc1 _) 16 4
            (by omega) _⟩,
        ⟨?_, ?_⟩, ?_, Kp_wr (Kp_wr hKp 8 4 _ (by omega) (by omega) (by omega)) 16 4 _ (by omega)
          (by omega) (by rw [hc1]; omega)⟩, h0, ?_, ?_⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
      all_goals try assumption
      intro _
      rw [i32_wr _ _ _ _ _ (by rw [hc1]; omega) (by omega), i32_wr _ _ _ _ _ (by omega) (by omega)]
      exact hv12

set_option maxRecDepth 20000 in
/-- The `enable_icc` bit read: its byte loaded, the index past it in `r8`. -/
theorem blk_Lf3 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.Lf3" := by
  cfg_block
  measure_hb "Lf3"
    intro n
    simp only [tab_Lf3, var_Lf3, tab_L10b, var_L10b]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hHB, h0, hix, hI⟩, hn⟩ := hs₀
    have hHB' := hHB
    obtain ⟨⟨hC, ⟨hsp, hbp, hf, hP, hbl, h08, hid⟩, hm⟩, ⟨h13, h12⟩, hbx, hKp⟩ := hHB'
    have hp31 : x.p8.toNat < 2 ^ 31 := hC.2.2.2.1
    have hpL : x.p8.toNat / 8 + 4 ≤ x.L := hC.2.2.2.2.1
    have hr32 : (s₀.regs.get64 .rdx).toNat < 2 ^ 32 := by omega
    have hdn : (BitVec.setWidth 32 (s₀.regs.get64 .rdx)).toNat = (s₀.regs.get64 .rdx).toNat := by
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hr32]
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals pnorm at *
    all_goals try simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      ite_self, AddrIndex.offset64, Width.bytes, BitVec.mul_one, BitVec.setWidth_32_64_32] at *
    all_goals try simp only [h13, h12, BitVec.setWidth_32_64_32]
    case vc1 =>
      exact Fr_buf_load hm _ 1 (by
        simp only [BitVec.toNat_setWidth, toNat_ushiftRight_div]; omega)
    case vc2 =>
      refine ⟨?_, by var_step⟩
      unfold q10b HB Cm Bs
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, h12,
        BitVec.setWidth_32_64_32]
      refine ⟨c, f, ⟨⟨hC, ⟨?_, ?_, hf, hP, hbl, h08, hid⟩, hm⟩, ⟨?_, ?_⟩, ?_, hKp⟩, h0, ?_, hI⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
      all_goals try assumption
      first
        | exact ix_bit1 x.idx _ x.p8 _ _ rfl (by rw [hdn]; exact hix.1) (by rw [hdn]; exact hix.2) hp31
        | (rw [BitVec.add_comm]
           exact ix_bit1 x.idx _ x.p8 _ _ rfl (by rw [hdn]; exact hix.1) (by rw [hdn]; exact hix.2) hp31)

end Kraken.Examples.Sbr.Ps
