import Kraken.X64.Examples.Sbr.Parse.PsBlkHLib

/-!
# `ff_ps_read_data`: the `icc` header fields
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
/-- `enable_icc` stored; branch on it. -/
theorem blk_L10b (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L10b" := by
  cfg_block
  measure_hb "L10b"
    intro n
    simp only [tab_L10b, var_L10b, tab_L11d, var_L11d, tab_L16a, var_L16a]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hHB, h0, hix, hI⟩, hn⟩ := hs₀
    have hHB' := hHB
    obtain ⟨⟨hC, ⟨hsp, hbp, hf, hP, hbl, h08, hid⟩, hm⟩, ⟨h13, h12⟩, hbx, hKp⟩ := hHB'
    have hcl : c.length = 764 := hP.1
    vcgen [ps_bswap32_havoc, ps_shl_cl32_havoc]
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals pnorm at *
    all_goals try simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      ite_self, AddrIndex.offset64, Width.bytes, BitVec.mul_one, BitVec.setWidth_32_64_32] at *
    all_goals try simp only [hbx]
    case vc1 => exact Fr_c_isSome hm hcl 20 4 (by omega)
    case vc2 =>
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.L16a") ⟨rfl, ?_, Or.inl ?_⟩
      · refine (tab_L16a _ _ _ _ _ _).mpr ?_
        unfold q16a HB Cm Bs
        simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ite_self]
        refine ⟨_, f, ⟨⟨hC, ⟨?_, ?_, hf, PsInv_wr_field hP 20 _ (by omega) (by omega) (by omega),
            hbl, h08, hid⟩, Fr_c_store hm hcl 20 4 (by omega) _⟩,
          ⟨?_, ?_⟩, ?_, Kp_wr hKp 20 4 _ (by omega) (by omega) (by omega)⟩, h0, ?_,
          IidH_wr hI 20 _ (by omega) (by omega)⟩
        all_goals try simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ite_self]
        all_goals try assumption
      · rw [var_L16a]; first | var_step | exact Kraken.lex_cons_lt_of_lt rfl (by decide)
    case vc3 =>
      refine ⟨?_, by var_step⟩
      unfold q11d HB Cm Bs
      simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ite_self]
      refine ⟨_, f, ⟨⟨hC, ⟨?_, ?_, hf, PsInv_wr_field hP 20 _ (by omega) (by omega) (by omega),
          hbl, h08, hid⟩, Fr_c_store hm hcl 20 4 (by omega) _⟩,
        ⟨?_, ?_⟩, ?_, Kp_wr hKp 20 4 _ (by omega) (by omega) (by omega)⟩, h0, ?_,
        IidH_wr hI 20 _ (by omega) (by omega)⟩
      all_goals try simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ite_self]
      all_goals try assumption

set_option maxRecDepth 20000 in
/-- `icc_mode`: three bits, byte-swapped load. -/
theorem blk_L11d (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L11d" := by
  cfg_block
  measure_hb "L11d"
    intro n
    simp only [tab_L11d, var_L11d, tab_L135, var_L135]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hHB, h0, hix, hI⟩, hn⟩ := hs₀
    have hHB' := hHB
    obtain ⟨⟨hC, ⟨hsp, hbp, hf, hP, hbl, h08, hid⟩, hm⟩, ⟨h13, h12⟩, hbx, hKp⟩ := hHB'
    have hp31 : x.p8.toNat < 2 ^ 31 := hC.2.2.2.1
    have hpL : x.p8.toNat / 8 + 4 ≤ x.L := hC.2.2.2.2.1
    have hr32 : (s₀.regs.get64 .r8).toNat < 2 ^ 32 := by omega
    vcgen [ps_bswap32_havoc, ps_shl_cl32_havoc]
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals pnorm at *
    all_goals try simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      ite_self, AddrIndex.offset64, Width.bytes, BitVec.mul_one, BitVec.setWidth_32_64_32] at *
    all_goals try simp only [h13]
    case vc1 =>
      exact Fr_buf_load hm _ 4 (by
        simp only [BitVec.toNat_setWidth, toNat_ushiftRight_div]; omega)
    case vc2 =>
      refine ⟨?_, by var_step⟩
      unfold q135 HB Cm Bs
      simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ite_self]
      refine ⟨c, f, ⟨⟨hC, ⟨?_, ?_, hf, hP, hbl, h08, hid⟩, hm⟩, ⟨?_, ?_⟩, ?_, hKp⟩, h0, ?_, hI, ?_⟩
      all_goals try simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ite_self]
      all_goals try assumption
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans (shr29_lt _) (by decide))]
      exact shr29_lt _

set_option maxRecDepth 20000 in
/-- `icc_mode` stored, the index clamped; `icc_mode < 6` to the table load. -/
theorem blk_L135 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L135" := by
  cfg_block
  measure_hb "L135"
    intro n
    simp only [tab_L135, var_L135, tab_L148, var_L148, tab_L154, var_L154]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hHB, h0, hix, hI, ha8⟩, hn⟩ := hs₀
    have hHB' := hHB
    obtain ⟨⟨hC, ⟨hsp, hbp, hf, hP, hbl, h08, hid⟩, hm⟩, ⟨h13, h12⟩, hbx, hKp⟩ := hHB'
    have hcl : c.length = 764 := hP.1
    have hp31 : x.p8.toNat < 2 ^ 31 := hC.2.2.2.1
    have hA : (BitVec.setWidth 32 (s₀.regs.get64 .rax)).toNat = (s₀.regs.get64 .rax).toNat := by
      rw [BitVec.toNat_setWidth]; omega
    have hA8 : (BitVec.setWidth 32 (s₀.regs.get64 .rax)).toNat < 8 := by omega
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals pnorm at *
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      AddrIndex.offset64, Width.bytes, BitVec.mul_one, BitVec.setWidth_32_64_32] at *
    all_goals try simp only [hbx, h12, BitVec.setWidth_32_64_32]
    case vc1 => exact Fr_c_isSome hm hcl 24 4 (by omega)
    case vc2 =>
      rename_i hl
      have hj := jl6 _ hA8 hl
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.L154") ⟨rfl, ?_, Or.inl ?_⟩
      · refine (tab_L154 _ _ _ _ _ _).mpr ?_
        unfold q154 HB Cm Bs
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, h12,
          BitVec.setWidth_32_64_32]
        refine ⟨_, f, ⟨⟨hC, ⟨?_, ?_, hf, PsInv_wr_field hP 24 _ (by omega) (by omega) (by omega),
            hbl, h08, hid⟩, Fr_c_store hm hcl 24 4 (by omega) _⟩,
          ⟨?_, ?_⟩, ?_, Kp_wr hKp 24 4 _ (by omega) (by omega) (by omega)⟩, h0,
          (ix_clampH x _ 3#64 (by decide) hix hp31 hC.2.2.1 _ _).1,
          IidH_wr hI 24 _ (by omega) (by omega), by omega, hj.2⟩
        all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
        all_goals try assumption
      · rw [var_L154]; first | var_step | exact Kraken.lex_cons_lt_of_lt rfl (by decide)
    case vc3 =>
      refine ⟨?_, by var_step⟩
      unfold q148 AtErr Cm Bs
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
      refine ⟨_, f, ⟨hC, ⟨?_, ?_, hf, PsInv_wr_field hP 24 _ (by omega) (by omega) (by omega),
          hbl, h08, hid⟩, Fr_c_store hm hcl 24 4 (by omega) _⟩, ?_,
        fun hw => Rng0_of_Kp (PsInv_wr_field hP 24 _ (by omega) (by omega) (by omega))
          (Kp_wr hKp 24 4 _ (by omega) (by omega) (by omega)) hw⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
      all_goals try assumption

set_option maxRecDepth 20000 in
/-- `nr_icc_par` from the table. -/
theorem blk_L154 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L154" := by
  cfg_block
  measure_hb "L154"
    intro n
    simp only [tab_L154, var_L154, tab_L16a, var_L16a]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hHB, h0, hix, hI, ha6, hcf⟩, hn⟩ := hs₀
    have hHB' := hHB
    obtain ⟨⟨hC, ⟨hsp, hbp, hf, hP, hbl, h08, hid⟩, hm⟩, ⟨h13, h12⟩, hbx, hKp⟩ := hHB'
    have hcl : c.length = 764 := hP.1
    have eidx : BitVec.setWidth 64 (BitVec.setWidth 32 (s₀.regs.get64 .rax))
        + lab "nr_iidicc_par_tab"
        = lab "nr_iidicc_par_tab" + BitVec.ofNat 64 (s₀.regs.get64 .rax).toNat := by
      rw [BitVec.add_comm]; congr 1; apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
    have hL := Fr_iidicc hm _ ha6
    have hv := iidicc_val _ ha6
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
      simp only [CondCode.interp_nc, hcf] at ha
      exact absurd ha (by decide)
    case vc2 => rw [eidx, hL]; rfl
    case vc3 => exact Fr_c_isSome hm hcl 28 4 (by omega)
    case vc4 =>
      rename_i hld
      rw [eidx, hL, Option.some.injEq] at hld
      subst hld
      refine ⟨?_, by var_step⟩
      unfold q16a HB Cm Bs
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
      refine ⟨_, f, ⟨⟨hC, ⟨?_, ?_, hf, PsInv_wr_field hP 28 _ (by omega) (by omega)
          (fun _ => by rcases hv with h | h | h <;> omega),
          hbl, h08, hid⟩, Fr_c_store hm hcl 28 4 (by omega) _⟩,
        ⟨?_, ?_⟩, ?_, Kp_wr hKp 28 4 _ (by omega) (by omega) (by omega)⟩, h0, ?_,
        IidH_wr hI 28 _ (by omega) (by omega)⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
      all_goals try assumption

set_option maxRecDepth 20000 in
/-- `rdi` saved at `rbp - 0x40`; the `enable_ipdopd` bit's byte loaded. -/
theorem blk_L16a (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L16a" := by
  cfg_block
  measure_hb "L16a"
    intro n
    simp only [tab_L16a, var_L16a, tab_L185, var_L185]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hHB, h0, hix, hI⟩, hn⟩ := hs₀
    have hHB' := hHB
    obtain ⟨⟨hC, ⟨hsp, hbp, hf, hP, hbl, h08, hid⟩, hm⟩, ⟨h13, h12⟩, hbx, hKp⟩ := hHB'
    have hp31 : x.p8.toNat < 2 ^ 31 := hC.2.2.2.1
    have hpL : x.p8.toNat / 8 + 4 ≤ x.L := hC.2.2.2.2.1
    have hr32 : (s₀.regs.get64 .r8).toNat < 2 ^ 32 := by omega
    have hdn : (BitVec.setWidth 32 (s₀.regs.get64 .r8)).toNat = (s₀.regs.get64 .r8).toNat := by
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hr32]
    have e1 : s₀.regs.get64 .rbp + Int64.toBitVec (-64)
        = t₀.regs.get64 .rsp - 0xa8#64 + BitVec.ofNat 64 0x60 := by
      rw [hbp]; exact fr_addr _ 64 (by omega) (by omega)
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals pnorm at *
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      AddrIndex.offset64, Width.bytes, BitVec.mul_one, BitVec.setWidth_32_64_32] at *
    all_goals try simp only [e1] at *
    all_goals try simp only [h13, h12, BitVec.setWidth_32_64_32]
    case vc1 => exact Fr_f_isSome hm hf 0x60 8 (by omega)
    case vc2 =>
      exact Fr_buf_load (Fr_f_store hm hf 0x60 8 (by omega) _) _ 1 (by
        simp only [BitVec.toNat_setWidth, toNat_ushiftRight_div]; omega)
    case vc3 =>
      refine ⟨?_, by var_step⟩
      unfold q185 HB Cm Bs
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, h12,
        BitVec.setWidth_32_64_32]
      refine ⟨c, _, ⟨⟨hC, ⟨?_, ?_, ?_, hP, ?_, ?_, ?_⟩, Fr_f_store hm hf 0x60 8 (by omega) _⟩,
        ⟨?_, ?_⟩, ?_, hKp⟩, ?_, ?_, hI⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
      all_goals try assumption
      · rw [wr_length _ _ _ _ (by omega), hf]
      · rw [rd_wr_disj _ _ _ _ _ _ (by omega) (by omega)]; exact hbl
      · rw [rd_wr_disj _ _ _ _ _ _ (by omega) (by omega)]; exact h08
      · rw [rd_wr_disj _ _ _ _ _ _ (by omega) (by omega)]; exact hid
      · rw [rd_wr_disj _ _ _ _ _ _ (by omega) (by omega)]; exact h0
      · first
          | exact ix_bit1 x.idx _ x.p8 _ _ rfl (by rw [hdn]; exact hix.1) (by rw [hdn]; exact hix.2) hp31
          | (rw [BitVec.add_comm]
             exact ix_bit1 x.idx _ x.p8 _ _ rfl (by rw [hdn]; exact hix.1) (by rw [hdn]; exact hix.2) hp31)

set_option maxRecDepth 20000 in
/-- `enable_ipdopd` stored; on to the common part. -/
theorem blk_L185 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L185" := by
  cfg_block
  measure_hb "L185"
    intro n
    simp only [tab_L185, var_L185, tab_L197, var_L197]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hHB, h0, hix, hI⟩, hn⟩ := hs₀
    have hHB' := hHB
    obtain ⟨⟨hC, ⟨hsp, hbp, hf, hP, hbl, h08, hid⟩, hm⟩, ⟨h13, h12⟩, hbx, hKp⟩ := hHB'
    have hcl : c.length = 764 := hP.1
    vcgen [ps_bswap32_havoc, ps_shl_cl32_havoc]
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals pnorm at *
    all_goals try simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      ite_self, AddrIndex.offset64, Width.bytes, BitVec.mul_one, BitVec.setWidth_32_64_32] at *
    all_goals try simp only [hbx]
    case vc1 => exact Fr_c_isSome hm hcl 32 4 (by omega)
    case vc2 =>
      refine ⟨?_, by var_step⟩
      unfold q197 HB Cm Bs
      simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ite_self]
      refine ⟨_, f, ⟨⟨hC, ⟨?_, ?_, hf, PsInv_wr_field hP 32 _ (by omega) (by omega) (by omega),
          hbl, h08, hid⟩, Fr_c_store hm hcl 32 4 (by omega) _⟩,
        ⟨?_, ?_⟩, ?_, Kp_wr hKp 32 4 _ (by omega) (by omega) (by omega)⟩,
        ⟨fun h => absurd h h0, fun _ => IidH_wr hI 32 _ (by omega) (by omega)⟩, ?_⟩
      all_goals try simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ite_self]
      all_goals try assumption

end Kraken.Examples.Sbr.Ps
