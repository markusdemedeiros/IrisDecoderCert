import Kraken.X64.Examples.Sbr.Parse.PsBlkHLib

/-!
# `ff_ps_read_data`: the entry index and the first bit
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
/-- The entry index stored; `eax` = the index after one bit. -/
theorem blk_L2c (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L2c" := by
  cfg_block
  measure_hb "L2c"
    intro n
    simp only [tab_L2c, var_L2c, tab_L3c, var_L3c]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hsp, hbp, hsi, hbx, ⟨h13, h12⟩, hcx, f, hf, hbl, hm⟩, hn⟩ := hs₀
    have hi : x.idx.toNat ≤ x.p8.toNat := hC.2.2.1
    have hp31 : x.p8.toNat < 2 ^ 31 := hC.2.2.2.1
    have e1 : s₀.regs.get64 .rbp + Int64.toBitVec (-140)
        = t₀.regs.get64 .rsp - 0xa8#64 + BitVec.ofNat 64 0x14 := by
      rw [hbp, show Int64.toBitVec (-140) = BitVec.ofNat 64 (2 ^ 64 - 140) from rfl]
      simp only [rsp0]; bv_omega
    have hS' := Fr_f_store hm hf 0x14 4 (by omega) x.idx.toInt
    have hL0 := Fr_f_load hm hf 0x14 4 (by omega)
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals pnorm at *
    all_goals simp only [e1] at *
    all_goals try simp only [hL0, Option.isSome_some] at *
    all_goals try simp only [hcx, h12, BitVec.setWidth_32_64_32]
    all_goals try subst_vars
    all_goals try simp only [ofInt_toBytes32, ofInt_toBytes64, BitVec.setWidth_32_64_32, AddrIndex.offset64,
      Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, Width.bytes, BitVec.mul_one] at *
    all_goals refine ⟨?_, by var_step⟩
    unfold q3c
    refine ⟨hC, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_, _, ?_, ?_, ?_, hS'⟩
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
    all_goals try assumption
    all_goals try rfl
    · exact ix_bit1 x.idx x.idx x.p8 _ _ rfl (Nat.le_refl _) hi hp31
    · rw [wr_length f 0x14 4 _ (by omega), hf]
    · rw [rd_wr_disj _ _ _ _ _ _ (by omega) (by omega)]; exact hbl
    · rw [rd_wr_same _ _ _ _ (by omega), ofInt_toBytes32]

set_option maxRecDepth 20000 in
/-- The header bit stored (`rbp - 0x88`), `gb_host` stored (`rbp - 0x98`); branch on the bit. -/
theorem blk_L3c (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L3c" := by
  cfg_block
  measure_hb "L3c"
    intro n
    simp only [tab_L3c, var_L3c, tab_L5b, var_L5b, var_Lb6]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hsp, hbp, hsi, hbx, ⟨h13, h12⟩, hcx, hix, f, hf, hbl, hid, hm⟩, hn⟩ := hs₀
    have e1 : s₀.regs.get64 .rbp + Int64.toBitVec (-136)
        = t₀.regs.get64 .rsp - 0xa8#64 + BitVec.ofNat 64 0x18 := by
      rw [hbp]; exact fr_addr _ 136 (by omega) (by omega)
    have e2 : s₀.regs.get64 .rbp + Int64.toBitVec (-152)
        = t₀.regs.get64 .rsp - 0xa8#64 + BitVec.ofNat 64 0x08 := by
      rw [hbp]; exact fr_addr _ 152 (by omega) (by omega)
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals pnorm at *
    all_goals try simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ite_self] at *
    all_goals try simp only [e1, e2] at *
    all_goals try simp only [hcx, BitVec.setWidth_32_64_32] at *
    case vc1 => exact Fr_f_isSome hm hf 0x18 4 (by omega)
    case vc2 =>
      exact Fr_f_isSome (Fr_f_store hm hf 0x18 4 (by omega) _)
        (by rw [wr_length _ _ _ _ (by omega), hf]) 0x08 8 (by omega)
    all_goals rename_i hz
    all_goals simp only [CondCode.interp_z, StatusFlags.zf_from_result] at hz
    case vc3 =>
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.Lb6") ⟨rfl, ?_, Or.inl ?_⟩
      · refine (tab_Lb6 _ _ _ _ _ _).mpr ?_
        unfold qb6 HB Cm Bs
        simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ite_self]
        refine ⟨_, ⟨⟨hC, ⟨hsp, hbp, ?_, hC.1, ?_, ?_, ?_⟩,
          Fr_f_store (Fr_f_store hm hf 0x18 4 (by omega) _)
            (by rw [wr_length _ _ _ _ (by omega), hf]) 0x08 8 (by omega) _⟩,
          ⟨?_, ?_⟩, ?_, ⟨rfl, rfl⟩⟩, ?_, hix⟩
        all_goals try simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ite_self]
        all_goals try assumption
        · rw [wr_length _ _ _ _ (by rw [wr_length _ _ _ _ (by omega), hf]; omega), wr_length _ _ _ _ (by omega), hf]
        · rw [rd_wr_disj _ _ _ _ _ _ (by rw [wr_length _ _ _ _ (by omega), hf]; omega) (by omega), rd_wr_disj _ _ _ _ _ _ (by omega) (by omega)]
          exact hbl
        · rw [rd_wr_same _ _ _ _ (by rw [wr_length _ _ _ _ (by omega), hf]; omega), ofInt_toBytes64]; exact hsi
        · rw [rd_wr_disj _ _ _ _ _ _ (by rw [wr_length _ _ _ _ (by omega), hf]; omega) (by omega), rd_wr_disj _ _ _ _ _ _ (by omega) (by omega)]
          exact hid
        · rw [rd_wr_disj _ _ _ _ _ _ (by rw [wr_length _ _ _ _ (by omega), hf]; omega) (by omega), rd_wr_same _ _ _ _ (by omega), rd_toBytes32]
          simp only [beq_iff_eq] at hz; rw [hz]; rfl
      · rw [var_Lb6]; first | var_step | exact Kraken.lex_cons_lt_of_lt rfl (by decide)
    case vc4 =>
      refine ⟨?_, by var_step⟩
      unfold q5b HB Cm Bs
      simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ite_self]
      refine ⟨_, ⟨⟨hC, ⟨hsp, hbp, ?_, hC.1, ?_, ?_, ?_⟩,
        Fr_f_store (Fr_f_store hm hf 0x18 4 (by omega) _)
          (by rw [wr_length _ _ _ _ (by omega), hf]) 0x08 8 (by omega) _⟩,
        ⟨?_, ?_⟩, ?_, ⟨rfl, rfl⟩⟩, ?_, hix⟩
      all_goals try simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ite_self]
      all_goals try assumption
      · rw [wr_length _ _ _ _ (by rw [wr_length _ _ _ _ (by omega), hf]; omega), wr_length _ _ _ _ (by omega), hf]
      · rw [rd_wr_disj _ _ _ _ _ _ (by rw [wr_length _ _ _ _ (by omega), hf]; omega) (by omega), rd_wr_disj _ _ _ _ _ _ (by omega) (by omega)]
        exact hbl
      · rw [rd_wr_same _ _ _ _ (by rw [wr_length _ _ _ _ (by omega), hf]; omega), ofInt_toBytes64]; exact hsi
      · rw [rd_wr_disj _ _ _ _ _ _ (by rw [wr_length _ _ _ _ (by omega), hf]; omega) (by omega), rd_wr_disj _ _ _ _ _ _ (by omega) (by omega)]
        exact hid
      · rw [rd_wr_disj _ _ _ _ _ _ (by rw [wr_length _ _ _ _ (by omega), hf]; omega) (by omega), rd_wr_same _ _ _ _ (by omega), rd_toBytes32]
        simp only [beq_eq_false_iff_ne, ne_eq] at hz
        intro h; exact hz (BitVec.eq_of_toNat_eq (by simpa using h))

set_option maxRecDepth 20000 in
/-- No header: `rdi` saved at `rbp - 0x40`, on to the common part. -/
theorem blk_Lb6 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.Lb6" := by
  cfg_block
  measure_hb "Lb6"
    intro n
    simp only [tab_Lb6, var_Lb6, var_L197]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨f, ⟨⟨hC, ⟨hsp, hbp, hf, hP, hbl, h08, hid⟩, hm⟩, ⟨h13, h12⟩, hbx, hKp⟩, h0, hix⟩, hn⟩
      := hs₀
    have e1 : s₀.regs.get64 .rbp + Int64.toBitVec (-64)
        = t₀.regs.get64 .rsp - 0xa8#64 + BitVec.ofNat 64 0x60 := by
      rw [hbp]; exact fr_addr _ 64 (by omega) (by omega)
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals pnorm at *
    all_goals try simp only [e1] at *
    case vc1 => exact Fr_f_isSome hm hf 0x60 8 (by omega)
    case vc2 =>
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.L197") ⟨rfl, ?_, Or.inl ?_⟩
      · refine (tab_L197 _ _ _ _ _ _).mpr ?_
        unfold q197 HB Cm Bs
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
        refine ⟨x.c, _, ⟨⟨hC, ⟨?_, ?_, ?_, hP, ?_, ?_, ?_⟩, Fr_f_store hm hf 0x60 8 (by omega) _⟩,
          ⟨?_, ?_⟩, ?_, hKp⟩, ⟨fun _ => rfl, fun h => absurd ?_ h⟩, ?_⟩
        all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
        all_goals try assumption
        · rw [wr_length _ _ _ _ (by omega), hf]
        · rw [rd_wr_disj _ _ _ _ _ _ (by omega) (by omega)]; exact hbl
        · rw [rd_wr_disj _ _ _ _ _ _ (by omega) (by omega)]; exact h08
        · rw [rd_wr_disj _ _ _ _ _ _ (by omega) (by omega)]; exact hid
        · rw [rd_wr_disj _ _ _ _ _ _ (by omega) (by omega)]; exact h0
      · rw [var_L197]; first | var_step | exact Kraken.lex_cons_lt_of_lt rfl (by decide)

set_option maxRecDepth 20000 in
/-- A header: the `enable_iid` bit's byte loaded, `edx` the index after it. -/
theorem blk_L5b (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L5b" := by
  cfg_block
  measure_hb "L5b"
    intro n
    simp only [tab_L5b, var_L5b, tab_L70, var_L70]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨f, hHB, h0, hix⟩, hn⟩ := hs₀
    have hHB' := hHB
    obtain ⟨⟨hC, ⟨hsp, hbp, hf, hP, hbl, h08, hid⟩, hm⟩, ⟨h13, h12⟩, hbx, hKp⟩ := hHB'
    have hp31 : x.p8.toNat < 2 ^ 31 := hC.2.2.2.1
    have hpL : x.p8.toNat / 8 + 4 ≤ x.L := hC.2.2.2.2.1
    have hr32 : (s₀.regs.get64 .rax).toNat < 2 ^ 32 := by omega
    have hlo : x.idx.toNat ≤ (BitVec.setWidth 32 (s₀.regs.get64 .rax)).toNat := by
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hr32]; exact hix.1
    have hhi : (BitVec.setWidth 32 (s₀.regs.get64 .rax)).toNat ≤ x.p8.toNat := by
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hr32]; exact hix.2
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals pnorm at *
    all_goals try simp only [AddrIndex.offset64, Reg64s.get64_set64, reduceCtorEq, ite_true,
      ite_false, Width.bytes, BitVec.mul_one, BitVec.setWidth_32_64_32, h13]
    case vc1 =>
      exact Fr_buf_load hm _ 1 (by
        simp only [BitVec.toNat_setWidth, toNat_ushiftRight_div]
        omega)
    case vc2 =>
      refine ⟨?_, by var_step⟩
      unfold q70 HB Cm Bs
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
      refine ⟨f, ⟨⟨hC, ⟨?_, ?_, hf, hP, hbl, h08, hid⟩, hm⟩, ⟨?_, ?_⟩, ?_, hKp⟩, h0, ?_⟩
      all_goals try assumption
      rw [h12, BitVec.setWidth_32_64_32]
      exact ix_bit1 x.idx _ x.p8 _ _ rfl hlo hhi hp31

set_option maxRecDepth 20000 in
/-- `enable_iid` read and stored; branch on it. -/
theorem blk_L70 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L70" := by
  cfg_block
  measure_hb "L70"
    intro n
    simp only [tab_L70, var_L70, tab_L85, var_L85, var_Lf3]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨f, hHB, h0, hix⟩, hn⟩ := hs₀
    have hHB' := hHB
    obtain ⟨⟨hC, ⟨hsp, hbp, hf, hP, hbl, h08, hid⟩, hm⟩, ⟨h13, h12⟩, hbx, hKp⟩ := hHB'
    have hcl : x.c.length = 764 := hP.1
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals pnorm at *
    all_goals try simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      ite_self] at *
    all_goals try simp only [hbx]
    case vc1 => exact Fr_c_isSome hm hcl 4 4 (by omega)
    case vc2 =>
      rename_i hz
      simp only [CondCode.interp_z, StatusFlags.zf_from_result, beq_iff_eq] at hz
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.Lf3") ⟨rfl, ?_, Or.inl ?_⟩
      · refine (tab_Lf3 _ _ _ _ _ _).mpr ?_
        unfold qf3 HB Cm Bs
        simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ite_self]
        refine ⟨_, f, ⟨⟨hC, ⟨?_, ?_, hf, PsInv_wr4 hP _, hbl, h08, hid⟩, Fr_c_store hm hcl 4 4 (by omega) _⟩,
          ⟨?_, ?_⟩, ?_, Kp_wr hKp 4 4 _ (by omega) (by omega) (by omega)⟩, h0, ?_, fun h => absurd ?_ h⟩
        all_goals try simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ite_self]
        all_goals try assumption
        rw [i32_wr_same _ _ _ (by omega), hz]; rfl
      · rw [var_Lf3]; first | var_step | exact Kraken.lex_cons_lt_of_lt rfl (by decide)
    case vc3 =>
      refine ⟨?_, by var_step⟩
      unfold q85 HB Cm Bs
      simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ite_self]
      refine ⟨_, f, ⟨⟨hC, ⟨?_, ?_, hf, PsInv_wr4 hP _, hbl, h08, hid⟩, Fr_c_store hm hcl 4 4 (by omega) _⟩,
          ⟨?_, ?_⟩, ?_, Kp_wr hKp 4 4 _ (by omega) (by omega) (by omega)⟩, h0, ?_⟩
      all_goals try simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ite_self]
      all_goals try assumption

set_option maxRecDepth 20000 in
/-- `iid_mode` read (three bits); out of range goes to the error path. -/
theorem blk_L85 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L85" := by
  cfg_block
  measure_hb "L85"
    intro n
    simp only [tab_L85, var_L85, tab_Laa, var_Laa, var_Lbf]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hHB, h0, hix⟩, hn⟩ := hs₀
    have hHB' := hHB
    obtain ⟨⟨hC, ⟨hsp, hbp, hf, hP, hbl, h08, hid⟩, hm⟩, ⟨h13, h12⟩, hbx, hKp⟩ := hHB'
    have hp31 : x.p8.toNat < 2 ^ 31 := hC.2.2.2.1
    have hpL : x.p8.toNat / 8 + 4 ≤ x.L := hC.2.2.2.2.1
    have hr32 : (s₀.regs.get64 .rdx).toNat < 2 ^ 32 := by omega
    vcgen [ps_bswap32_havoc, ps_shl_cl32_havoc]
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals pnorm at *
    all_goals try simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      ite_self, AddrIndex.offset64, Width.bytes, BitVec.mul_one, BitVec.setWidth_32_64_32] at *
    all_goals try simp only [h13, h12]
    case vc1 =>
      exact Fr_buf_load hm _ 4 (by
        simp only [BitVec.toNat_setWidth, toNat_ushiftRight_div]; omega)
    case vc2 =>
      rename_i hle
      have hj := jle5 _ (shr29_lt _) hle
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.Lbf") ⟨rfl, ?_, Or.inl ?_⟩
      · refine (tab_Lbf _ _ _ _ _ _).mpr ?_
        unfold qbf HB Cm Bs
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, h12,
          BitVec.setWidth_32_64_32]
        refine ⟨c, f, ⟨⟨hC, ⟨?_, ?_, hf, hP, hbl, h08, hid⟩, hm⟩, ⟨?_, ?_⟩, ?_, hKp⟩, h0, ?_, ?_,
          hj.2⟩
        all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
        all_goals try assumption
        · exact (ix_clampH x _ 3#64 (by decide) hix hp31 hC.2.2.1 _ _).1
        · rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans (shr29_lt _) (by decide))]
          exact hj.1
      · rw [var_Lbf]; first | var_step | exact Kraken.lex_cons_lt_of_lt rfl (by decide)
    case vc3 =>
      refine ⟨?_, by var_step⟩
      unfold qaa AtErr Cm Bs
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
      refine ⟨c, f, ⟨hC, ⟨?_, ?_, hf, hP, hbl, h08, hid⟩, hm⟩, ?_, fun hw => Rng0_of_Kp hP hKp hw⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
      all_goals try assumption

end Kraken.Examples.Sbr.Ps
