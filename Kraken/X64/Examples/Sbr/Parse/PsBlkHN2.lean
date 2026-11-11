import Kraken.X64.Examples.Sbr.Parse.PsBlkHNLib

/-!
# `ff_ps_read_data`: the class-1 borders `1..3` (`0x277`–`0x336`)
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
/-- `border[1]` read (5 bits); it is never below `border[0] = -1`. -/
theorem blk_L277 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L277" := by
  cfg_block
  measure_hb "L277"
    intro n
    simp only [tab_L277, var_L277, tab_L297, var_L297, var_L2b3]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, v, hB, hv1⟩, hn⟩ := hs₀
    have hB' := hB
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, hf, hP, hbl, h08, hid⟩, hm⟩, ⟨h13, h12⟩, hbx, hKp⟩, hH, h38, hv4, hne,
      h58, h10, hb0, hix⟩ := hB'
    have hp31 : x.p8.toNat < 2 ^ 31 := hC.2.2.2.1
    have hpL : x.p8.toNat / 8 + 4 ≤ x.L := hC.2.2.2.2.1
    have hcl : c.length = 764 := hP.1
    have e56 : s₀.regs.get64 .rbx + 56#64 = arg2 t₀ + BitVec.ofNat 64 56 := by rw [hbx]
    have l1 := Fr_c_isSome hm hcl 56 4 (by omega)
    have hst := fun w => Fr_c_store hm hcl 56 4 (by omega) w
    rw [← e56] at l1 hst
    have P := PLift.up hst
    clear hst
    vcgen [ps_bswap32_havoc, ps_shl_cl32_havoc]
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals try pnorm at *
    all_goals try simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      ite_self, AddrIndex.offset64, Width.bytes, BitVec.mul_one, BitVec.setWidth_32_64_32] at *
    all_goals try simp only [h13, h12]
    case vc1 =>
      exact Fr_buf_load hm _ 4 (by
        simp only [BitVec.toNat_setWidth, toNat_ushiftRight_div]; omega)
    case vc2 => exact l1
    case vc3 =>
      rename_i hj
      rw [hn_ge32] at hj
      have hw := of_decide_eq_true hj
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.L2b3") ⟨rfl, ?_, Or.inl ?_⟩
      · refine (tab_L2b3 _ _ _ _ _ _).mpr ?_
        refine ⟨_, f, _, hn_BS_wr hB 56 _ (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ (P.down _), hv1,
          hn_BordTo_wr (j := 0) hcl (hn_BordTo0 hb0 rfl) (by omega) _ ?_ ?_, ?_⟩
        all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
        all_goals try exact hix
        all_goals try trivial
        · exact hn_shr27_ge _ _ hb0
        · exact hn_shr27_le _
        · rw [hn_shr27_nat, show 56 = 52 + 4 * (0 + 1) from rfl, hn_bord_wr_same c 0 hcl (by omega)]
      · rw [var_L2b3]; first | var_step | exact Kraken.lex_cons_lt_of_lt rfl (by decide)
    case vc4 =>
      refine ⟨?_, by var_step⟩
      exact hn_err_wr hB 56 _ (by omega) (by omega) (by simp) (by simp) (by simp) (P.down _)

set_option maxRecDepth 20000 in
/-- `rax = num_env + 1`, the index advanced; `num_env = 1` is done. -/
theorem blk_L2b3 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L2b3" := by
  cfg_block
  measure_hb "L2b3"
    intro n
    simp only [tab_L2b3, var_L2b3, tab_L2cd, var_L2cd]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, v, hB, hv1, hbt, hdx⟩, hn⟩ := hs₀
    have hB' := hB
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, hf, hP, hbl, h08, hid⟩, hm⟩, ⟨h13, h12⟩, hbx, hKp⟩, hH, h38, hv4, hne,
      h58, h10, hb0, hix⟩ := hB'
    have hp31 : x.p8.toNat < 2 ^ 31 := hC.2.2.2.1
    have e1 : s₀.regs.get64 .rbp + Int64.toBitVec (-72)
        = t₀.regs.get64 .rsp - 0xa8#64 + BitVec.ofNat 64 0x58 := by
      rw [hbp]; exact fr_addr _ 72 (by omega) (by omega)
    have hL := Fr_f_load hm hf 0x58 8 (by omega)
    rw [← e1] at hL
    have hbt' : (s₀.regs.get64 .r10).toNat = 1 → BordTo c (s₀.regs.get64 .r10).toNat :=
      fun h => h ▸ hbt
    have hinc := hn_inc_v _ hv4
    rw [← h58] at hinc
    vcgen [hn_inc32_spec]
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals try pnorm at *
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      AddrIndex.offset64, Width.bytes, BitVec.mul_one] at *
    all_goals try simp only [h12, BitVec.setWidth_32_64_32] at *
    case vc1 => rw [hL]; rfl
    case vc2 =>
      rename_i hld hj
      rw [hL, Option.some.injEq] at hld
      subst hld
      rw [h58, hn_z32 _ 2 (by omega)] at hj
      have hv := of_decide_eq_true hj
      rw [hn_inc_v32 _ hv4] at hv
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.L715") ⟨rfl, ?_, Or.inl ?_⟩
      · refine (tab_L715 _ _ _ _ _ _).mpr ?_
        refine toHdr (hn_BS_mv hB ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl) (hbt' (by omega))
        all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
        all_goals try simp only [h12, BitVec.setWidth_32_64_32]
        exact (ix_clampH x _ 5#64 (by decide) hix hp31 hC.2.2.1 _ _).1
      · rw [var_L715]; first | var_step | exact Kraken.lex_cons_lt_of_lt rfl (by decide)
    case vc3 =>
      rename_i hld hj
      rw [hL, Option.some.injEq] at hld
      subst hld
      rw [h58, hn_z32 _ 2 (by omega)] at hj
      have hv := of_decide_eq_false hj
      rw [hn_inc_v32 _ hv4] at hv
      refine ⟨⟨c, f, _, hn_BS_mv hB ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl, ?_, ?_, hbt, ?_⟩, by var_step⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
      all_goals try simp only [h12, BitVec.setWidth_32_64_32]
      · exact (ix_clampH x _ 5#64 (by decide) hix hp31 hC.2.2.1 _ _).1
      · omega
      · exact hinc
      · exact hdx

set_option maxRecDepth 20000 in
/-- `border[2]` read (5 bits) into `rsi`; below `border[1]` goes to the error path. -/
theorem blk_L2cd (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L2cd" := by
  cfg_block
  measure_hb "L2cd"
    intro n
    simp only [tab_L2cd, var_L2cd, tab_L297, var_L297, tab_L2ec, var_L2ec]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, v, hB, hv2, hax, hbt, hr⟩, hn⟩ := hs₀
    have hB' := hB
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, hf, hP, hbl, h08, hid⟩, hm⟩, ⟨h13, h12⟩, hbx, hKp⟩, hH, h38, hv4, hne,
      h58, h10, hb0, hix⟩ := hB'
    have hp31 : x.p8.toNat < 2 ^ 31 := hC.2.2.2.1
    have hpL : x.p8.toNat / 8 + 4 ≤ x.L := hC.2.2.2.2.1
    have hcl : c.length = 764 := hP.1
    have e0 : s₀.regs.get64 .rbx + 60#64 = arg2 t₀ + BitVec.ofNat 64 60 := by rw [hbx]
    have l1 := Fr_c_isSome hm hcl 60 4 (by omega)
    have hst := fun w => Fr_c_store hm hcl 60 4 (by omega) w
    rw [← e0] at l1 hst
    have P := PLift.up hst
    clear hst
    have hrd := fun w hge => hn_rd_bord (j := 1) hcl hbt (by omega) 60 rfl _ hr w hge
    vcgen [ps_bswap32_havoc, ps_shl_cl32_havoc]
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals try pnorm at *
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      AddrIndex.offset64, Width.bytes, BitVec.mul_one, BitVec.setWidth_32_64_32] at *
    all_goals try simp only [h13, h12]
    case vc1 =>
      exact Fr_buf_load hm _ 4 (by
        simp only [BitVec.toNat_setWidth, toNat_ushiftRight_div]; omega)
    case vc2 => exact l1
    case vc3 =>
      rename_i hj
      rw [hn_l32] at hj
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.L297") ⟨rfl, ?_, Or.inl ?_⟩
      · refine (tab_L297 _ _ _ _ _ _).mpr ?_
        exact hn_err_wr hB 60 _ (by omega) (by omega) (by simp) (by simp) (by simp) (P.down _)
      · rw [var_L297]; first | var_step | exact Kraken.lex_cons_lt_of_lt rfl (by decide)
    case vc4 =>
      rename_i hj
      rw [hn_l32] at hj
      have hw := hrd _ (of_decide_eq_false hj)
      refine ⟨⟨_, f, _, hn_BS_wr hB 60 _ (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ (P.down _), ?_, ?_,
        hw.1, ?_⟩, by var_step⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
      all_goals try exact hix
      all_goals try trivial
      all_goals try omega
      exact hw.2

set_option maxRecDepth 20000 in
/-- The index advanced; `num_env = 2` is done. -/
theorem blk_L2ec (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L2ec" := by
  cfg_block
  measure_hb "L2ec"
    intro n
    simp only [tab_L2ec, var_L2ec, tab_L300, var_L300]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, v, hB, hv2, hax, hbt, hr⟩, hn⟩ := hs₀
    have hB' := hB
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, hf, hP, hbl, h08, hid⟩, hm⟩, ⟨h13, h12⟩, hbx, hKp⟩, hH, h38, hv4, hne,
      h58, h10, hb0, hix⟩ := hB'
    have hp31 : x.p8.toNat < 2 ^ 31 := hC.2.2.2.1
    have hz := hn_z32 (BitVec.setWidth 32 (s₀.regs.get64 .rax)) 3 (by omega)
    rw [hn_eax _ _ hax (by omega)] at hz
    have hbt' : v + 1 = 3 → BordTo c v := fun h => by
      have : v = 2 := by omega
      rw [this]; exact hbt
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals try pnorm at *
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      AddrIndex.offset64, Width.bytes, BitVec.mul_one, BitVec.setWidth_32_64_32] at *
    all_goals try simp only [h12, BitVec.setWidth_32_64_32] at *
    case vc1 =>
      rename_i hj
      rw [hz] at hj
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.L715") ⟨rfl, ?_, Or.inl ?_⟩
      · refine (tab_L715 _ _ _ _ _ _).mpr ?_
        refine toHdr (hn_BS_mv hB ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl) (hbt' (of_decide_eq_true hj))
        all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
        all_goals try simp only [h12, BitVec.setWidth_32_64_32]
        exact (ix_clampH x _ 5#64 (by decide) hix hp31 hC.2.2.1 _ _).1
      · rw [var_L715]; first | var_step | exact Kraken.lex_cons_lt_of_lt rfl (by decide)
    case vc2 =>
      rename_i hj
      rw [hz] at hj
      have hv := of_decide_eq_false hj
      refine ⟨⟨c, f, _, hn_BS_mv hB ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl, ?_, ?_, hbt, hr⟩, by var_step⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
      all_goals try simp only [h12, BitVec.setWidth_32_64_32]
      · exact (ix_clampH x _ 5#64 (by decide) hix hp31 hC.2.2.1 _ _).1
      all_goals try omega
      all_goals try assumption

set_option maxRecDepth 20000 in
/-- `border[3]` read (5 bits) into `rdx`; below `border[2]` goes to the error path. -/
theorem blk_L300 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L300" := by
  cfg_block
  measure_hb "L300"
    intro n
    simp only [tab_L300, var_L300, tab_L297, var_L297, tab_L323, var_L323]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, v, hB, hv2, hax, hbt, hr⟩, hn⟩ := hs₀
    have hB' := hB
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, hf, hP, hbl, h08, hid⟩, hm⟩, ⟨h13, h12⟩, hbx, hKp⟩, hH, h38, hv4, hne,
      h58, h10, hb0, hix⟩ := hB'
    have hp31 : x.p8.toNat < 2 ^ 31 := hC.2.2.2.1
    have hpL : x.p8.toNat / 8 + 4 ≤ x.L := hC.2.2.2.2.1
    have hcl : c.length = 764 := hP.1
    have e0 : s₀.regs.get64 .rbx + 64#64 = arg2 t₀ + BitVec.ofNat 64 64 := by rw [hbx]
    have l1 := Fr_c_isSome hm hcl 64 4 (by omega)
    have hst := fun w => Fr_c_store hm hcl 64 4 (by omega) w
    rw [← e0] at l1 hst
    have P := PLift.up hst
    clear hst
    have hrd := fun w hge => hn_rd_bord (j := 2) hcl hbt (by omega) 64 rfl _ hr w hge
    vcgen [ps_bswap32_havoc, ps_shl_cl32_havoc]
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals try pnorm at *
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      AddrIndex.offset64, Width.bytes, BitVec.mul_one, BitVec.setWidth_32_64_32] at *
    all_goals try simp only [h13, h12]
    case vc1 =>
      exact Fr_buf_load hm _ 4 (by
        simp only [BitVec.toNat_setWidth, toNat_ushiftRight_div]; omega)
    case vc2 => exact l1
    case vc3 =>
      rename_i hj
      rw [hn_l32] at hj
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.L297") ⟨rfl, ?_, Or.inl ?_⟩
      · refine (tab_L297 _ _ _ _ _ _).mpr ?_
        exact hn_err_wr hB 64 _ (by omega) (by omega) (by simp) (by simp) (by simp) (P.down _)
      · rw [var_L297]; first | var_step | exact Kraken.lex_cons_lt_of_lt rfl (by decide)
    case vc4 =>
      rename_i hj
      rw [hn_l32] at hj
      have hw := hrd _ (of_decide_eq_false hj)
      refine ⟨⟨_, f, _, hn_BS_wr hB 64 _ (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ (P.down _), ?_, ?_,
        hw.1, ?_⟩, by var_step⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
      all_goals try exact hix
      all_goals try trivial
      all_goals try omega
      exact hw.2

set_option maxRecDepth 20000 in
/-- The index advanced; `num_env = 3` is done. -/
theorem blk_L323 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L323" := by
  cfg_block
  measure_hb "L323"
    intro n
    simp only [tab_L323, var_L323, tab_L337, var_L337]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, v, hB, hv2, hax, hbt, hr⟩, hn⟩ := hs₀
    have hB' := hB
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, hf, hP, hbl, h08, hid⟩, hm⟩, ⟨h13, h12⟩, hbx, hKp⟩, hH, h38, hv4, hne,
      h58, h10, hb0, hix⟩ := hB'
    have hp31 : x.p8.toNat < 2 ^ 31 := hC.2.2.2.1
    have hz := hn_z32 (BitVec.setWidth 32 (s₀.regs.get64 .rax)) 4 (by omega)
    rw [hn_eax _ _ hax (by omega)] at hz
    have hbt' : v + 1 = 4 → BordTo c v := fun h => by
      have : v = 3 := by omega
      rw [this]; exact hbt
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals try pnorm at *
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      AddrIndex.offset64, Width.bytes, BitVec.mul_one, BitVec.setWidth_32_64_32] at *
    all_goals try simp only [h12, BitVec.setWidth_32_64_32] at *
    case vc1 =>
      rename_i hj
      rw [hz] at hj
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.L715") ⟨rfl, ?_, Or.inl ?_⟩
      · refine (tab_L715 _ _ _ _ _ _).mpr ?_
        refine toHdr (hn_BS_mv hB ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl) (hbt' (of_decide_eq_true hj))
        all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
        all_goals try simp only [h12, BitVec.setWidth_32_64_32]
        exact (ix_clampH x _ 5#64 (by decide) hix hp31 hC.2.2.1 _ _).1
      · rw [var_L715]; first | var_step | exact Kraken.lex_cons_lt_of_lt rfl (by decide)
    case vc2 =>
      rename_i hj
      rw [hz] at hj
      have hv := of_decide_eq_false hj
      refine ⟨⟨c, f, _, hn_BS_mv hB ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl, ?_, ?_, hbt, hr⟩, by var_step⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
      all_goals try simp only [h12, BitVec.setWidth_32_64_32]
      · exact (ix_clampH x _ 5#64 (by decide) hix hp31 hC.2.2.1 _ _).1
      all_goals try omega
      all_goals try assumption

end Kraken.Examples.Sbr.Ps
