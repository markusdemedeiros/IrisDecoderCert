import Kraken.X64.Examples.Sbr.Parse.PsBlkHLib

/-!
# `ff_ps_read_data`: the frame class, `num_env`
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
/-- The `frame_class` bit: its byte loaded, the index past it in `edx`. -/
theorem blk_L197 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L197" := by
  cfg_block
  measure_hb "L197"
    intro n
    simp only [tab_L197, var_L197, tab_L1b0, var_L1b0]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hHB, hH, hix⟩, hn⟩ := hs₀
    have hHB' := hHB
    obtain ⟨⟨hC, ⟨hsp, hbp, hf, hP, hbl, h08, hid⟩, hm⟩, ⟨h13, h12⟩, hbx, hKp⟩ := hHB'
    have hp31 : x.p8.toNat < 2 ^ 31 := hC.2.2.2.1
    have hpL : x.p8.toNat / 8 + 4 ≤ x.L := hC.2.2.2.2.1
    have hr32 : (s₀.regs.get64 .rax).toNat < 2 ^ 32 := by omega
    have hdn : (BitVec.setWidth 32 (s₀.regs.get64 .rax)).toNat = (s₀.regs.get64 .rax).toNat := by
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hr32]
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals pnorm at *
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      AddrIndex.offset64, Width.bytes, BitVec.mul_one, BitVec.setWidth_32_64_32] at *
    all_goals try simp only [h13, h12, BitVec.setWidth_32_64_32]
    case vc1 =>
      exact Fr_buf_load hm _ 1 (by
        simp only [BitVec.toNat_setWidth, toNat_ushiftRight_div]; omega)
    case vc2 =>
      refine ⟨?_, by var_step⟩
      unfold q1b0 HB Cm Bs
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, h12,
        BitVec.setWidth_32_64_32]
      refine ⟨c, f, ⟨⟨hC, ⟨?_, ?_, hf, hP, hbl, h08, hid⟩, hm⟩, ⟨?_, ?_⟩, ?_, hKp⟩, hH, ?_, ?_, ?_, ?_⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
      all_goals try assumption
      · exact (ix_lea1 _ _ _ _ rfl hix.2 hp31).1
      · exact ⟨Nat.le_trans hix.1 (ix_lea1 _ _ _ _ rfl hix.2 hp31).2.2.2,
          (ix_lea1 _ _ _ _ rfl hix.2 hp31).2.2.1⟩
      · exact (ix_lea1 _ _ _ _ rfl hix.2 hp31).2.1

set_option maxRecDepth 20000 in
/-- `frame_class` stored. -/
theorem blk_L1b0 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L1b0" := by
  cfg_block
  measure_hb "L1b0"
    intro n
    simp only [tab_L1b0, var_L1b0, tab_L1be, var_L1be]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hHB, hH, hix, hdi, hdx, hdxe⟩, hn⟩ := hs₀
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
    case vc1 => exact Fr_c_isSome hm hcl 36 4 (by omega)
    case vc2 =>
      refine ⟨?_, by var_step⟩
      unfold q1be HB Cm Bs
      simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ite_self]
      refine ⟨_, f, ⟨⟨hC, ⟨?_, ?_, hf, PsInv_wr_field hP 36 _ (by omega) (by omega) (by omega),
          hbl, h08, hid⟩, Fr_c_store hm hcl 36 4 (by omega) _⟩,
        ⟨?_, ?_⟩, ?_, Kp_wr hKp 36 4 _ (by omega) (by omega) (by omega)⟩,
        HdrOk_wr hH 36 _ (by omega) (by omega), ?_, ?_, ?_, ?_, ?_⟩
      all_goals try simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ite_self]
      all_goals try assumption
      exact and1_le _

set_option maxRecDepth 20000 in
/-- `num_env_old = num_env`, also kept at `rbp - 0x68`. -/
theorem blk_L1be (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L1be" := by
  cfg_block
  measure_hb "L1be"
    intro n
    simp only [tab_L1be, var_L1be, tab_L1c8, var_L1c8]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hHB, hH, hix, hdi, hdx, hdxe, hsi⟩, hn⟩ := hs₀
    have hHB' := hHB
    obtain ⟨⟨hC, ⟨hsp, hbp, hf, hP, hbl, h08, hid⟩, hm⟩, ⟨h13, h12⟩, hbx, hKp⟩ := hHB'
    have hcl : c.length = 764 := hP.1
    have hL := Fr_c_load hm hcl 44 4 (by omega)
    have e1 : s₀.regs.get64 .rbp + Int64.toBitVec (-104)
        = t₀.regs.get64 .rsp - 0xa8#64 + BitVec.ofNat 64 0x38 := by
      rw [hbp]; exact fr_addr _ 104 (by omega) (by omega)
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals pnorm at *
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      AddrIndex.offset64, Width.bytes, BitVec.mul_one, BitVec.setWidth_32_64_32] at *
    all_goals try simp only [e1] at *
    all_goals try simp only [hbx]
    case vc1 => exact Fr_c_isSome hm hcl 44 4 (by omega)
    case vc2 => exact Fr_f_isSome hm hf 0x38 8 (by omega)
    case vc3 => exact Fr_c_isSome (Fr_f_store hm hf 0x38 8 (by omega) _) hcl 40 4 (by omega)
    case vc4 =>
      rename_i hld
      rw [hbx, hL, Option.some.injEq] at hld
      subst hld
      have hW0 : 0 ≤ (BitVec.ofInt 32 (rd c 44 4)).toInt := by
        rw [ofInt_rd_i32]; exact hP.2.2.2.2.2.1.1
      have hW5 : (BitVec.ofInt 32 (rd c 44 4)).toInt ≤ 5 := by
        rw [ofInt_rd_i32]; exact hP.2.2.2.2.2.1.2
      refine ⟨?_, by var_step⟩
      unfold q1c8 HB Cm Bs
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
      refine ⟨_, _, ⟨⟨hC, ⟨?_, ?_, ?_, PsInv_wr40 hP _ hW0 hW5, ?_, ?_, ?_⟩,
          Fr_c_store (Fr_f_store hm hf 0x38 8 (by omega) _) hcl 40 4 (by omega) _⟩,
        ⟨?_, ?_⟩, ?_, Kp_wr hKp 40 4 _ (by omega) (by omega) (by omega)⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
      all_goals try assumption
      · rw [wr_length _ _ _ _ (by omega), hf]
      · rw [rd_wr_disj _ _ _ _ _ _ (by omega) (by omega)]; exact hbl
      · rw [rd_wr_disj _ _ _ _ _ _ (by omega) (by omega)]; exact h08
      · rw [rd_wr_disj _ _ _ _ _ _ (by omega) (by omega)]; exact hid
      · have h' := HdrOk_wr hH 40 (BitVec.ofInt 32 (rd c 44 4)).toInt (by omega) (by omega)
        unfold HdrOk at h' ⊢
        rw [rd_wr_disj _ _ _ _ _ _ (by omega) (by omega)]; exact h'
      · unfold S38
        rw [rd_wr_same _ _ _ _ (by omega), i32_wr_same _ _ _ (by omega)]; exact s38_lem _ hW0


set_option maxRecDepth 20000 in
/-- `num_env_idx`: two bits, byte-swapped load. -/
theorem blk_L1c8 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L1c8" := by
  cfg_block
  measure_hb "L1c8"
    intro n
    simp only [tab_L1c8, var_L1c8, tab_L1e1, var_L1e1]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hHB, hH, hS, hix, hdi, hdx, hdxe, hsi⟩, hn⟩ := hs₀
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
    all_goals try simp only [h13]
    case vc1 =>
      exact Fr_buf_load hm _ 4 (by
        simp only [BitVec.toNat_setWidth, toNat_ushiftRight_div]; omega)
    case vc2 =>
      refine ⟨?_, by var_step⟩
      unfold q1e1 HB Cm Bs
      simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ite_self]
      refine ⟨c, f, ⟨⟨hC, ⟨?_, ?_, hf, hP, hbl, h08, hid⟩, hm⟩, ⟨?_, ?_⟩, ?_, hKp⟩, hH, hS, ?_,
        ?_, ?_, ?_, shr30_lt64 _⟩
      all_goals try simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ite_self]
      all_goals try assumption
      omega

set_option maxRecDepth 20000 in
/-- The index past the two bits, clamped; `num_env_idx < 4`. -/
theorem blk_L1e1 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L1e1" := by
  cfg_block
  measure_hb "L1e1"
    intro n
    simp only [tab_L1e1, var_L1e1, tab_L1fa, var_L1fa]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hHB, hH, hS, hix, hdi, hsum, hsi, h9⟩, hn⟩ := hs₀
    have hHB' := hHB
    obtain ⟨⟨hC, ⟨hsp, hbp, hf, hP, hbl, h08, hid⟩, hm⟩, ⟨h13, h12⟩, hbx, hKp⟩ := hHB'
    have hp31 : x.p8.toNat < 2 ^ 31 := hC.2.2.2.1
    have hra : (s₀.regs.get64 .rax + s₀.regs.get64 .rdi).toNat
        = (s₀.regs.get64 .rax).toNat + (s₀.regs.get64 .rdi).toNat := by
      rw [BitVec.toNat_add]; omega
    have hr : Ix x (s₀.regs.get64 .rax + s₀.regs.get64 .rdi) := by
      unfold Ix; rw [hra]; omega
    have h94 : (BitVec.setWidth 32 (s₀.regs.get64 .r9)).toNat < 4 := by
      rw [BitVec.toNat_setWidth]; omega
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals pnorm at *
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      AddrIndex.offset64, Width.bytes, BitVec.mul_one, BitVec.setWidth_32_64_32] at *
    all_goals try simp only [h12, BitVec.setWidth_32_64_32]
    case vc1 =>
      exfalso; rename_i hj
      exact absurd ((nc_cmp4 _ h94).symm.trans hj) (by decide)
    case vc2 =>
      refine ⟨?_, by var_step⟩
      unfold q1fa HB Cm Bs
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
      refine ⟨c, f, ⟨⟨hC, ⟨?_, ?_, hf, hP, hbl, h08, hid⟩, hm⟩, ⟨?_, ?_⟩, ?_, hKp⟩, hH, hS,
        (ix_clampH x _ 2#64 (by decide) hr hp31 hC.2.2.1 _ _).1, ?_, ?_⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
      all_goals try assumption


end Kraken.Examples.Sbr.Ps
