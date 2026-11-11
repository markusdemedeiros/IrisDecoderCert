import Kraken.X64.Examples.Sbr.Parse.PsBlkXLib

/-!
# `ff_ps_read_data`, the extension: the band-loop heads `0xe60`/`0xf70`/`0xee0`/`0x1000` (the `0x22` traps are unreachable)
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
theorem blk_e60 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.Le60" := by
  cfg_block
  measure_hb "Le60"
    simp only [tab_Le60, var_Le60, tab_Le80, var_Le80]
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hXB, hL, hN, hJ, hP, hT, hBd⟩, hn⟩ := hs₀
    have hC := hXB.1.1
    have hm := hXB.1.2.2
    have hbp : s₀.regs.get64 .rbp = rsp0 t₀ - 8#64 := hXB.1.2.1.2.1
    have hr13 : s₀.regs.get64 .r13 = x.buf := hXB.2.1.1
    have hI2 := hJ.2.1.2
    have hoff := xrd_off ((s₀.regs.get64 .rsi).setWidth 32) x.p8 x.L
      (by rw [BitVec.toNat_setWidth]; omega) hC.2.2.2.2.1
    have hbl := Fr_buf_load hm (BitVec.setWidth 64 ((BitVec.setWidth 32 (s₀.regs.get64 .rsi)).ushiftRight 3)) 4 (by omega)
    vcgen [bswap32_havoc, shl_cl32_havoc]
    all_goals subst_vars
    all_goals try xsimp
    · simp only [hr13]; exact hbl
    · exfalso
      obtain hc := ‹CondCode.z.interp _ = true›
      dsimp only at hc
      exact trap34 hBd _ hc
    · refine ⟨⟨c, f, XB_regs hXB rfl ?_ ?_ ?_ ?_, hL, hN, XJ_regs hJ ?_, XP_regs hP ?_ ?_ ?_ ?_, ?_, ?_, ?_⟩, Nat.le_of_eq ?_⟩
      all_goals try (xsimp; done)
      · xsimp; exact hT
      · simp only [XBd]; xsimp; exact hBd
      · xsimp; exact Nat.lt_of_lt_of_le (zx_shr_lt _ 27 (by omega)) (by decide)
      · exact lex6_eq (vq1 hbp rfl (by xsimp)) (vq2 hbp rfl (by xsimp)) (by xsimp)


set_option maxRecDepth 20000 in
theorem blk_f70 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.Lf70" := by
  cfg_block
  measure_hb "Lf70"
    simp only [tab_Lf70, var_Lf70, tab_Lf90, var_Lf90]
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hXB, hL, hN, hJ, hP, hT, hBd⟩, hn⟩ := hs₀
    have hC := hXB.1.1
    have hm := hXB.1.2.2
    have hbp : s₀.regs.get64 .rbp = rsp0 t₀ - 8#64 := hXB.1.2.1.2.1
    have hr13 : s₀.regs.get64 .r13 = x.buf := hXB.2.1.1
    have hI2 := hJ.2.1.2
    have hoff := xrd_off ((s₀.regs.get64 .rdx).setWidth 32) x.p8 x.L
      (by rw [BitVec.toNat_setWidth]; omega) hC.2.2.2.2.1
    have hbl := Fr_buf_load hm (BitVec.setWidth 64 ((BitVec.setWidth 32 (s₀.regs.get64 .rdx)).ushiftRight 3)) 4 (by omega)
    vcgen [bswap32_havoc, shl_cl32_havoc]
    all_goals subst_vars
    all_goals try xsimp
    · simp only [hr13]; exact hbl
    · exfalso
      obtain hc := ‹CondCode.z.interp _ = true›
      dsimp only at hc
      exact trap34 hBd _ hc
    · refine ⟨⟨c, f, XB_regs hXB rfl ?_ ?_ ?_ ?_, hL, hN, XJ_regs hJ ?_, XP_regs hP ?_ ?_ ?_ ?_, ?_, ?_, ?_⟩, Nat.le_of_eq ?_⟩
      all_goals try (xsimp; done)
      · xsimp; exact hT
      · simp only [XBd]; xsimp; exact hBd
      · xsimp; exact Nat.lt_of_lt_of_le (zx_shr_lt _ 27 (by omega)) (by decide)
      · exact lex6_eq (vq1 hbp rfl (by xsimp)) (vq2 hbp rfl (by xsimp)) (by xsimp)



set_option maxRecDepth 20000 in
theorem blk_ee0 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.Lee0" := by
  cfg_block
  measure_hb "Lee0"
    simp only [tab_Lee0, var_Lee0, tab_Lf06, var_Lf06]
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hXB, hL, hN, hJ, hP, hT, hBd, hQ⟩, hn⟩ := hs₀
    have hC := hXB.1.1
    have hm := hXB.1.2.2
    have hbp : s₀.regs.get64 .rbp = rsp0 t₀ - 8#64 := hXB.1.2.1.2.1
    have hcl : c.length = 764 := hXB.1.2.1.2.2.2.1.1
    have hr13 : s₀.regs.get64 .r13 = x.buf := hXB.2.1.1
    have hI2 := hJ.2.1.2
    have hoff := xrd_off ((s₀.regs.get64 .rdi).setWidth 32) x.p8 x.L
      (by rw [BitVec.toNat_setWidth]; omega) hC.2.2.2.2.1
    have hbl := Fr_buf_load hm (BitVec.setWidth 64 ((BitVec.setWidth 32 (s₀.regs.get64 .rdi)).ushiftRight 3)) 4 (by omega)
    vcgen [bswap32_havoc, shl_cl32_havoc]
    all_goals subst_vars
    all_goals try xsimp
    · exfalso
      obtain hc := ‹CondCode.z.interp _ = true›
      dsimp only at hc
      exact trap34 hBd _ hc
    · obtain ⟨j, hj1, hj5, hr14⟩ := hQ
      rw [prev_load hm hcl hr14 hj1 hj5 (by omega) (by have := hBd.1; have := hBd.2; omega)]; rfl
    · simp only [hr13]; exact hbl
    · refine ⟨⟨c, f, XB_regs hXB rfl ?_ ?_ ?_ ?_, hL, hN, XJ_regs hJ ?_, XP_regs hP ?_ ?_ ?_ ?_, ?_, ?_, ?_, ?_⟩, Nat.le_of_eq ?_⟩
      all_goals try (xsimp; done)
      · xsimp; exact hT
      · simp only [XBd]; xsimp; exact hBd
      · simp only [XQ]; xsimp; exact hQ
      · xsimp; exact Nat.lt_of_lt_of_le (zx_shr_lt _ 27 (by omega)) (by decide)
      · exact lex6_eq (vq1 hbp rfl (by xsimp)) (vq2 hbp rfl (by xsimp)) (by xsimp)
set_option maxRecDepth 20000 in
theorem blk_1000 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.L1000" := by
  cfg_block
  measure_hb "L1000"
    simp only [tab_L1000, var_L1000, tab_L1026, var_L1026]
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hXB, hL, hN, hJ, hP, hT, hBd, hQ⟩, hn⟩ := hs₀
    have hC := hXB.1.1
    have hm := hXB.1.2.2
    have hbp : s₀.regs.get64 .rbp = rsp0 t₀ - 8#64 := hXB.1.2.1.2.1
    have hcl : c.length = 764 := hXB.1.2.1.2.2.2.1.1
    have hr13 : s₀.regs.get64 .r13 = x.buf := hXB.2.1.1
    have hI2 := hJ.2.1.2
    have hoff := xrd_off ((s₀.regs.get64 .rdi).setWidth 32) x.p8 x.L
      (by rw [BitVec.toNat_setWidth]; omega) hC.2.2.2.2.1
    have hbl := Fr_buf_load hm (BitVec.setWidth 64 ((BitVec.setWidth 32 (s₀.regs.get64 .rdi)).ushiftRight 3)) 4 (by omega)
    vcgen [bswap32_havoc, shl_cl32_havoc]
    all_goals subst_vars
    all_goals try xsimp
    · exfalso
      obtain hc := ‹CondCode.z.interp _ = true›
      dsimp only at hc
      exact trap34 hBd _ hc
    · obtain ⟨j, hj1, hj5, hr14⟩ := hQ
      rw [prev_load hm hcl hr14 hj1 hj5 (by omega) (by have := hBd.1; have := hBd.2; omega)]; rfl
    · simp only [hr13]; exact hbl
    · refine ⟨⟨c, f, XB_regs hXB rfl ?_ ?_ ?_ ?_, hL, hN, XJ_regs hJ ?_, XP_regs hP ?_ ?_ ?_ ?_, ?_, ?_, ?_, ?_⟩, Nat.le_of_eq ?_⟩
      all_goals try (xsimp; done)
      · xsimp; exact hT
      · simp only [XBd]; xsimp; exact hBd
      · simp only [XQ]; xsimp; exact hQ
      · xsimp; exact Nat.lt_of_lt_of_le (zx_shr_lt _ 27 (by omega)) (by decide)
      · exact lex6_eq (vq1 hbp rfl (by xsimp)) (vq2 hbp rfl (by xsimp)) (by xsimp)

end Kraken.Examples.Sbr.Ps
