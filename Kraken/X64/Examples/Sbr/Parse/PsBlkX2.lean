import Kraken.X64.Examples.Sbr.Parse.PsBlkXLib

/-!
# `ff_ps_read_data`, the extension: the count (`0xce0`–`0xd3b`)
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
theorem blk_ce0 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.Lce0" := by
  cfg_block
  measure_hb "Lce0"
    simp only [tab_Lce0, tab_Lcf0, var_Lce0, var_Lcf0]
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hXB, ⟨hI, h10, hbx⟩, hdx⟩, hn⟩ := hs₀
    have hr12 : s₀.regs.get64 .r12 = x.p8.setWidth 64 := hXB.2.1.2
    have hp : x.p8.toNat < 2 ^ 31 := hXB.1.1.2.2.2.1
    have hi : x.idx.toNat ≤ x.p8.toNat := hXB.1.1.2.2.1
    vcgen
    case vc1 =>
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.Ld16")
        ⟨rfl, (tab_Ld16 _ _ _ _ _ _).mpr ?_, Or.inl ?_⟩
      · subst_vars
        xsimp
        refine ⟨c, f, XB_regs hXB rfl ?_ ?_ ?_ ?_, ⟨?_, ?_, ?_⟩, ?_⟩
        all_goals xsimp
        all_goals first | rfl | assumption | omega | (simp only [hr12, BitVec.setWidth_32_64_32]; exact (ix_clamp x _ _ (by decide) hI hp hi _ _).1)
      · rw [var_Ld16]; subst hn; exact Kraken.lex_cons_lt_of_lt rfl (by decide)
    case vc2 =>
      subst_vars
      xsimp
      refine ⟨⟨c, f, XB_regs hXB rfl ?_ ?_ ?_ ?_, ⟨?_, ?_, ?_⟩⟩,
        Kraken.lex_cons_le_of_lt rfl (by decide)⟩
      all_goals xsimp
      all_goals first | rfl | assumption | omega | (simp only [hr12, BitVec.setWidth_32_64_32]; exact (ix_clamp x _ _ (by decide) hI hp hi _ _).1)

set_option maxRecDepth 20000 in
theorem blk_cf0 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.Lcf0" := by
  cfg_block
  measure_hb "Lcf0"
    simp only [tab_Lcf0, tab_Ld08, var_Lcf0, var_Ld08]
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, ⟨⟨hC, hB, hm⟩, ⟨hr13, hr12⟩, hXI⟩, hI, h10, hbx⟩, hn⟩ := hs₀
    have hoff := xrd_off ((s₀.regs.get64 .r8).setWidth 32) x.p8 x.L
      (by rw [BitVec.toNat_setWidth]; omega) hC.2.2.2.2.1
    have hbl := Fr_buf_load hm _ 4 hoff
    have hXB : XB k Ext x ra t₀ s₀ c f := ⟨⟨hC, hB, hm⟩, ⟨hr13, hr12⟩, hXI⟩
    clear hm
    vcgen [bswap32_havoc, shl_cl32_havoc]
    all_goals subst_vars
    all_goals xsimp
    · simp only [hr13]; exact hbl
    · refine ⟨⟨c, f, XB_regs hXB rfl ?_ ?_ ?_ ?_, ⟨?_, ?_, ?_⟩, ?_⟩,
        Kraken.lex_cons_le_of_lt rfl (by decide)⟩
      all_goals xsimp
      all_goals first | rfl | assumption | exact zx_shr_lt _ 24 (by omega)

set_option maxRecDepth 20000 in
theorem blk_d08 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.Ld08" := by
  cfg_block
  measure_hb "Ld08"
    simp only [tab_Ld08, tab_Ld16, var_Ld08, var_Ld16]
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hXB, ⟨hI, h10, hbx⟩, hdx⟩, hn⟩ := hs₀
    have hr12 : s₀.regs.get64 .r12 = x.p8.setWidth 64 := hXB.2.1.2
    have hp : x.p8.toNat < 2 ^ 31 := hXB.1.1.2.2.2.1
    have hi : x.idx.toNat ≤ x.p8.toNat := hXB.1.1.2.2.1
    vcgen
    all_goals subst_vars
    all_goals xsimp
    refine ⟨⟨c, f, XB_regs hXB rfl ?_ ?_ ?_ ?_, ⟨?_, ?_, ?_⟩, ?_⟩,
      Kraken.lex_cons_le_of_lt rfl (by decide)⟩
    all_goals xsimp
    all_goals first | rfl | assumption | omega | (simp only [hr12, BitVec.setWidth_32_64_32]; exact (ix_clamp x _ _ (by decide) hI hp hi _ _).1) | (simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]; omega)

set_option maxRecDepth 20000 in
theorem blk_d16 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.Ld16" := by
  cfg_block
  measure_hb "Ld16"
    simp only [tab_Ld16, tab_Ld25, var_Ld16, var_Ld25]
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hXB, ⟨hI, h10, hbx⟩, hdx⟩, hn⟩ := hs₀
    vcgen
    case vc1 =>
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.L104e")
        ⟨rfl, (tab_L104e _ _ _ _ _ _).mpr ?_, Or.inl ?_⟩
      · subst_vars
        rename_i _ h
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true] at h
        rw [test_le_small _ (by omega), decide_eq_true_eq] at h
        xsimp
        refine ⟨c, f, XB_regs hXB rfl ?_ ?_ ?_ ?_, ⟨?_, ?_, ?_⟩, ?_⟩
        all_goals try xsimp
        all_goals first | rfl | assumption | (rw [AddrIndex.offset64_scale8, toInt_x8 _ hdx]; omega)
      · rw [var_L104e]; subst hn; exact Kraken.lex_cons_lt_of_lt rfl (by decide)
    case vc2 =>
      subst_vars
      xsimp
      rename_i _ h
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true] at h
      rw [test_le_small _ (by omega), decide_eq_false_iff_not] at h
      refine ⟨⟨c, f, XB_regs hXB rfl ?_ ?_ ?_ ?_, ⟨?_, ?_, ?_⟩, ?_⟩,
        Kraken.lex_cons_le_of_lt rfl (by decide)⟩
      all_goals try xsimp
      all_goals first | rfl | assumption | (rw [AddrIndex.offset64_scale8, toInt_x8 _ hdx]; omega)

set_option maxRecDepth 20000 in
theorem blk_d25 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.Ld25" := by
  cfg_block
  measure_hb "Ld25"
    simp only [tab_Ld25, tab_Ld3b, var_Ld25, var_Ld3b]
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hXB, ⟨hI, h10, hbx⟩, hax⟩, hn⟩ := hs₀
    have hm := hXB.1.2.2
    have hbp : s₀.regs.get64 .rbp = rsp0 t₀ - 8#64 := hXB.1.2.1.2.1
    have hfl : f.length = 0x78 := hXB.1.2.1.2.2.1
    have e1 : s₀.regs.get64 .rbp + BitVec.ofNat 64 (18446744073709551616 - 80)
        = rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 0x50 := by rw [hbp]; bv_omega
    have e2 : s₀.regs.get64 .rbp + BitVec.ofNat 64 (18446744073709551616 - 120)
        = rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 0x28 := by rw [hbp]; bv_omega
    vcgen
    all_goals subst_vars
    all_goals try xsimp
    · rw [e1, Fr_f_load hm hfl 0x50 8 (by omega)]; rfl
    · rw [e1, e2, Fr_f_load (Fr_f_store hm hfl 0x50 8 (by omega) _)
        (by rw [wr_length _ _ _ _ (by omega)]; exact hfl) 0x28 8 (by omega)]; rfl
    · rw [e1, e2]
      rename_i s₀
      have hX1 := XB_wrf (s' := ({ s₀ with dmem := storeInt s₀.dmem (rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 0x50) 8 (s₀.regs.get64 Reg64.rbx + 416#64).toInt } : MachineData))
        hXB 0x50 8 _ (by omega) (by decide) rfl rfl rfl rfl rfl
      refine ⟨⟨c, _, XB_wrf hX1 0x28 8 _ (by omega) (by decide) rfl ?_ ?_ ?_ ?_, ⟨?_, ?_, ?_⟩,
        ⟨?_, ?_⟩, ?_⟩, Kraken.lex_cons_le_of_lt rfl (by decide)⟩
      all_goals try xsimp
      · exact hI
      · exact h10
      · exact hbx
      · rw [rd_wr _ 40 8 80 8 _ (by rw [wr_length _ _ _ _ (by omega)]; omega) (by omega),
          xrd_wr_self _ 80 8 64 _ (by omega) rfl, BitVec.ofInt_toInt, hbx]
      · rw [xrd_wr_self _ 40 8 64 _ (by rw [wr_length _ _ _ _ (by omega)]; omega) rfl,
          BitVec.ofInt_toInt, hbx]
      · exact hax

set_option maxRecDepth 20000 in
theorem blk_d3b (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.Ld3b" := by
  cfg_block
  measure_hb "Ld3b"
    simp only [tab_Ld3b, var_Ld3b, var_Ld7b]
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hXB, ⟨hI, h10, hbx⟩, hL2, hax⟩, hn⟩ := hs₀
    have hm := hXB.1.2.2
    have hbp : s₀.regs.get64 .rbp = rsp0 t₀ - 8#64 := hXB.1.2.1.2.1
    have hfl : f.length = 0x78 := hXB.1.2.1.2.2.1
    have hH := hXB.2.2.1.1
    have e1 : s₀.regs.get64 .rbp + BitVec.ofNat 64 (18446744073709551616 - 72)
        = rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 0x58 := by rw [hbp]; bv_omega
    have e2 : s₀.regs.get64 .rbp + BitVec.ofNat 64 (18446744073709551616 - 88)
        = rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 0x48 := by rw [hbp]; bv_omega
    have e1' : s₀.regs.get64 .rbp + (-72 : Int64).toBitVec
        = rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 0x58 := by
      rw [hbp, Int64.toBitVec_neg_ofNat_norm]; bv_omega
    have := hH.2.1
    have l0 := Fr_f_load hm hfl 0x58 4 (by omega)
    rw [rd_lo4 f 0x58 _ (by omega) hH.2.2.1 (by omega)] at l0
    have l1 := l0
    have l1' := l0
    rw [← e1] at l1
    rw [← e1'] at l1'
    clear l0
    vcgen
    case vc3 =>
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.Ld7b")
        ⟨rfl, (tab_Ld7b _ _ _ _ _ _).mpr ?_, Or.inl ?_⟩
      · rename_i v hv
        subst_vars
        rw [l1', Option.some.injEq] at hv
        subst hv
        xsimp
        refine ⟨c, wr f 0x48 8 (BitVec.setWidth 64 (BitVec.ofInt 32 (ne c))).toInt,
          XB_wrf hXB 0x48 8 _ (by omega) (by decide) ?_ ?_ ?_ ?_ ?_, ⟨?_, ?_, ?_⟩,
          ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
        all_goals try xsimp
        · rw [e2]
        all_goals try rfl
        · exact hI
        · exact h10
        · exact hbx
        · rw [rd_wr _ 0x48 8 0x50 8 _ (by omega) (by omega)]; exact hL2.1
        · rw [rd_wr _ 0x48 8 0x28 8 _ (by omega) (by omega)]; exact hL2.2
        · rw [xrd_wr_self _ 0x48 8 64 _ (by omega) rfl, BitVec.ofInt_toInt]
          exact zx_ofInt_small _ hH.1 hH.2.1
        · exact hax
      · rw [var_Ld7b]; subst hn; exact Kraken.lex_cons_lt_of_lt rfl (by decide)
    all_goals subst_vars
    all_goals try xsimp
    · rw [l1]; rfl
    · rename_i v hv
      rw [l1', Option.some.injEq] at hv
      subst hv
      rw [e2, Fr_f_load hm hfl 0x48 8 (by omega)]; rfl

end Kraken.Examples.Sbr.Ps
