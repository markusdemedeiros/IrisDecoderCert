import Kraken.X64.Examples.Sbr.Parse.PsBlkHNLib

/-!
# `ff_ps_read_data`: the class-1 border `4` (`0x337`–`0x36d`), the decreasing-border message (`0x297`)
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
/-- `border[4]` read (5 bits) into `rsi`; below `border[3]` goes to the error path. -/
theorem blk_L337 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L337" := by
  cfg_block
  measure_hb "L337"
    intro n
    simp only [tab_L337, var_L337, tab_L297, var_L297, tab_L35a, var_L35a]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, v, hB, hv2, hax, hbt, hr⟩, hn⟩ := hs₀
    have hB' := hB
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, hf, hP, hbl, h08, hid⟩, hm⟩, ⟨h13, h12⟩, hbx, hKp⟩, hH, h38, hv4, hne,
      h58, h10, hb0, hix⟩ := hB'
    have hp31 : x.p8.toNat < 2 ^ 31 := hC.2.2.2.1
    have hpL : x.p8.toNat / 8 + 4 ≤ x.L := hC.2.2.2.2.1
    have hcl : c.length = 764 := hP.1
    have e0 : s₀.regs.get64 .rbx + 68#64 = arg2 t₀ + BitVec.ofNat 64 68 := by rw [hbx]
    have l1 := Fr_c_isSome hm hcl 68 4 (by omega)
    have hst := fun w => Fr_c_store hm hcl 68 4 (by omega) w
    rw [← e0] at l1 hst
    have P := PLift.up hst
    clear hst
    have hrd := fun w hge => hn_rd_bord (j := 3) hcl hbt (by omega) 68 rfl _ hr w hge
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
        exact hn_err_wr hB 68 _ (by omega) (by omega) (by simp) (by simp) (by simp) (P.down _)
      · rw [var_L297]; first | var_step | exact Kraken.lex_cons_lt_of_lt rfl (by decide)
    case vc4 =>
      rename_i hj
      rw [hn_l32] at hj
      have hw := hrd _ (of_decide_eq_false hj)
      refine ⟨⟨_, f, _, hn_BS_wr hB 68 _ (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ (P.down _), ?_, ?_,
        hw.1⟩, by var_step⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
      all_goals try exact hix
      all_goals try trivial
      all_goals try omega

set_option maxRecDepth 20000 in
/-- The index advanced; `num_env = 4` is done. -/
theorem blk_L35a (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L35a" := by
  cfg_block
  measure_hb "L35a"
    intro n
    simp only [tab_L35a, var_L35a, tab_L36e, var_L36e]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, v, hB, hv2, hax, hbt⟩, hn⟩ := hs₀
    have hB' := hB
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, hf, hP, hbl, h08, hid⟩, hm⟩, ⟨h13, h12⟩, hbx, hKp⟩, hH, h38, hv4, hne,
      h58, h10, hb0, hix⟩ := hB'
    have hp31 : x.p8.toNat < 2 ^ 31 := hC.2.2.2.1
    have hz := hn_z32 (BitVec.setWidth 32 (s₀.regs.get64 .rax)) 5 (by omega)
    rw [hn_eax _ _ hax (by omega)] at hz
    have hbt' : v + 1 = 5 → BordTo c v := fun h => by
      have : v = 4 := by omega
      rw [this]; exact hbt
    have h5 : (s₀.regs.get64 .r10).toNat + 1 = 5 := by omega
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
      exact absurd h5 (of_decide_eq_false hj)


set_option maxRecDepth 20000 in
/-- A border decreases: `av_log(avctx, AV_LOG_ERROR, …)`, to the error path. -/
theorem blk_L297 (k : Nat) (Ext : Mem 64 → Prop) (hAv : AvLogSpec Ext k) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L297" := by
  cfg_block
  measure_hb "L297"
    intro n
    simp only [tab_L297, var_L297]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, ⟨hC, ⟨hsp, hbp, hf, hP, hbl, h08, hid⟩, hm⟩, hbx, hR⟩, hn⟩ := hs₀
    have e1 : s₀.regs.get64 .rbp + Int64.toBitVec (-64)
        = t₀.regs.get64 .rsp - 0xa8#64 + BitVec.ofNat 64 0x60 := by
      rw [hbp]; exact fr_addr _ 64 (by omega) (by omega)
    obtain ⟨F, hF⟩ := hn_Fr_ext k Ext x ra t₀ f c x.idx
    have hm2 := hm
    rw [hF] at hm2
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rsp - 8#64) 8).isSome = true := by
      rw [hsp, BitVec.sub_sub_ofNat]
      exact Block.loadInt_isSome hm2 (by simp)
    have hpush := fun v => Block.storeInt_val hm2 (Split.here _ _) v
    have e48 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 0xb0#64 := by
      rw [hsp]; show _ - 168#64 - 8#64 = _; rw [BitVec.sub_sub_ofNat]
    clear hm2
    vcgen [MachineWP.call_proc_spec_at F "av_log" hAv]
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    pnorm at e1
    case vc1 =>
      pnorm
      simp only [e1]
      exact Fr_f_isSome hm hf 0x60 8 (by omega)
    case vc2 =>
      refine ⟨fun ra' => ⟨⟨?_, trivial⟩, fun s' hpost => ?_⟩, hld⟩
      · rw [e48]; exact hpush _
      · rw [e48] at hpost
        obtain ⟨hsp', hbp', ⟨hbx', -, -, -, -⟩, hm'⟩ := hpost
        have hm'' : s'.dmem =⋆ Fr k Ext x ra t₀ f c x.idx := (congrFun hF s'.dmem).mpr hm'
        vcgen
        all_goals try call_simp
        all_goals try dsimp only at *
        left
        refine Table.ofLabels_at (l := "ff_ps_read_data.L1475") ⟨rfl, ?_, Or.inl ?_⟩
        · refine (tab_L1475 _ _ _ _ _ _).mpr ?_
          refine ⟨c, f, ⟨hC, ⟨?_, ?_, hf, hP, hbl, h08, hid⟩, hm''⟩, ?_, hR⟩
          · rw [hsp', show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl,
              BitVec.sub_add_ofNat_cancel _ _ _ (by omega) (by omega)]
          · rw [hbp', hbp]
          · rw [hbx', hbx]
        · rw [var_L1475]; first | var_step | exact Kraken.lex_cons_lt_of_lt rfl (by decide)

end Kraken.Examples.Sbr.Ps
