import Kraken.X64.Examples.Sbr.Parse.PsBlkXLib

/-!
# `ff_ps_read_data`, the extension: the `while (cnt > 7)` loop head (`0xd50`–`0xdd8`, `0x104e`)
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
theorem blk_d70 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.Ld70" := by
  cfg_block
  measure_hb "Ld70"
    simp only [tab_Ld70, tab_Ld7b, var_Ld70, var_Ld7b]
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hXB, ⟨hI, h10, hbx⟩, hL⟩, hn⟩ := hs₀
    have h7 : (BitVec.setWidth 32 (Int64.toBitVec 7)).toInt = 7 := by decide
    vcgen
    case vc1 =>
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.L104e")
        ⟨rfl, (tab_L104e _ _ _ _ _ _).mpr ?_, Or.inl ?_⟩
      · subst_vars
        rename_i h
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true] at h
        rw [CondCode.interp_le_cmp_toInt32, h7] at h
        simp only [BitVec.setWidth_32_64_32, decide_eq_true_eq] at h
        xsimp
        refine ⟨c, f, XB_regs hXB rfl ?_ ?_ ?_ ?_, ⟨?_, ?_, ?_⟩, ?_⟩
        all_goals try xsimp
        · exact hI
        · exact h10
        · exact hbx
        · exact h
      · rw [var_L104e]; subst hn; exact Kraken.lex_cons_lt_of_lt rfl (by decide)
    case vc2 =>
      subst_vars
      rename_i h
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true] at h
      rw [CondCode.interp_le_cmp_toInt32, h7] at h
      simp only [BitVec.setWidth_32_64_32, decide_eq_false_iff_not] at h
      xsimp
      refine ⟨⟨c, f, XB_regs hXB rfl ?_ ?_ ?_ ?_, ⟨?_, ?_, ?_⟩, hL, ?_⟩,
        Nat.le_of_lt (lex3_lt rfl (toInt_toNat_lt _) (by omega) (Or.inl ?_))⟩
      all_goals try xsimp
      · exact hI
      · exact h10
      · exact hbx
      · omega
      · rw [BitVec.add_comm]; omega

set_option maxRecDepth 20000 in
theorem blk_104e (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.L104e" := by
  cfg_block
  measure_hb "L104e"
    simp only [tab_L104e, tab_L1063, var_L104e, var_L1063]
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hXB, ⟨hI, h10, hbx⟩, hax⟩, hn⟩ := hs₀
    have hp : x.p8.toNat < 2 ^ 31 := hXB.1.1.2.2.2.1
    have hi : x.idx.toNat ≤ x.p8.toNat := hXB.1.1.2.2.1
    have hr12 : s₀.regs.get64 .r12 = x.p8.setWidth 64 := hXB.2.1.2
    vcgen
    case vc1 =>
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.L1459")
        ⟨rfl, (tab_L1459 _ _ _ _ _ _).mpr ?_, Or.inl ?_⟩
      · subst_vars
        try xsimp
        exact ⟨c, f, (XB_regs hXB rfl rfl rfl rfl rfl).1, hbx,
          fun hw => ⟨(hXB.2.2.2.2 hw).1.1, (hXB.2.2.2.2 hw).1.2.1⟩⟩
      · rw [var_L1459]; subst hn; exact Kraken.lex_cons_lt_of_lt rfl (by decide)
    case vc2 =>
      subst_vars
      rename_i s₀ _ h
      dsimp only at h
      rw [test_s32] at h
      have hd : (BitVec.setWidth 32 (s₀.regs.get64 .rax)).toNat ≤ 256 := by
        rw [BitVec.toInt_eq_toNat_of_msb h] at hax; omega
      try xsimp
      refine ⟨⟨c, f, (XB_regs hXB rfl ?_ ?_ ?_ ?_).1, ?_, ?_, hXB.2.2.1, hXB.2.2.2.1, ?_,
        hXB.2.2.2.2⟩, Kraken.lex_cons_le_of_lt rfl (by decide)⟩
      all_goals try xsimp
      all_goals try rfl
      · exact hbx
      · simp only [hr12, BitVec.setWidth_32_64_32]; exact x_ix_clamp2 x _ _ hd hI hp hi _ _
      · exact h10

set_option maxRecDepth 20000 in
theorem blk_d7b (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.Ld7b" := by
  cfg_block
  measure_hb "Ld7b"
    simp only [tab_Ld7b, tab_Ld93, var_Ld7b, var_Ld93]
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, ⟨⟨hC, hB, hm⟩, ⟨hr13, hr12⟩, hXI⟩, ⟨hI, h10, hbx⟩, hL, hax⟩, hn⟩ := hs₀
    have hoff := xrd_off ((s₀.regs.get64 .r8).setWidth 32) x.p8 x.L
      (by rw [BitVec.toNat_setWidth]; omega) hC.2.2.2.2.1
    have hbl := Fr_buf_load hm _ 4 hoff
    have hXB : XB k Ext x ra t₀ s₀ c f := ⟨⟨hC, hB, hm⟩, ⟨hr13, hr12⟩, hXI⟩
    clear hm
    vcgen [bswap32_havoc, shl_cl32_havoc]
    all_goals subst_vars
    all_goals try xsimp
    · simp only [hr13]; exact hbl
    · refine ⟨⟨c, f, XB_regs hXB rfl ?_ ?_ ?_ ?_, ⟨?_, ?_, ?_⟩, hL, ?_⟩,
        Nat.le_of_lt (lex3_lt rfl (toInt_toNat_lt' _) (by decide) (Or.inr ⟨rfl, by decide⟩))⟩
      all_goals try xsimp
      all_goals first | rfl | exact hI | exact h10 | exact hbx | exact hax

set_option maxRecDepth 20000 in
theorem blk_d93 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.Ld93" := by
  cfg_block
  measure_hb "Ld93"
    simp only [tab_Ld93, tab_Lda7, var_Ld93, var_Lda7]
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hXB, ⟨hI, h10, hbx⟩, hL, hax⟩, hn⟩ := hs₀
    have hr12 : s₀.regs.get64 .r12 = x.p8.setWidth 64 := hXB.2.1.2
    have hp : x.p8.toNat < 2 ^ 31 := hXB.1.1.2.2.2.1
    have hi : x.idx.toNat ≤ x.p8.toNat := hXB.1.1.2.2.1
    vcgen
    case vc1 =>
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.Ld70")
        ⟨rfl, (tab_Ld70 _ _ _ _ _ _).mpr ?_, Or.inl ?_⟩
      · subst_vars
        try xsimp
        refine ⟨c, f, XB_regs hXB rfl ?_ ?_ ?_ ?_, ⟨?_, ?_, ?_⟩, hL⟩
        all_goals try xsimp
        all_goals first | rfl | exact h10 | exact hbx | (simp only [hr12, BitVec.setWidth_32_64_32]; exact (ix_clamp x _ _ (by decide) hI hp hi _ _).1)
      · rw [var_Ld70]; subst_vars
        try xsimp
        exact lex3_lt rfl (toInt_toNat_lt' _) (by decide) (Or.inl (sub2_lt _ hax))
    case vc2 =>
      subst_vars
      try xsimp
      refine ⟨⟨c, f, XB_regs hXB rfl ?_ ?_ ?_ ?_, ⟨?_, ?_, ?_⟩, hL, ?_⟩,
        Nat.le_of_lt (lex3_lt rfl (toInt_toNat_lt' _) (by decide) (Or.inr ⟨rfl, by decide⟩))⟩
      all_goals try xsimp
      all_goals first | rfl | exact h10 | exact hbx | exact hax | (simp only [hr12, BitVec.setWidth_32_64_32]; exact (ix_clamp x _ _ (by decide) hI hp hi _ _).1)

set_option maxRecDepth 20000 in
theorem blk_da7 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.Lda7" := by
  cfg_block
  measure_hb "Lda7"
    simp only [tab_Lda7, tab_Ldc6, var_Lda7, var_Ldc6]
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hXB, ⟨hI, h10, hbx⟩, hL, hax⟩, hn⟩ := hs₀
    have hC := hXB.1.1
    have hm := hXB.1.2.2
    have hr13 : s₀.regs.get64 .r13 = x.buf := hXB.2.1.1
    have hr12 : s₀.regs.get64 .r12 = x.p8.setWidth 64 := hXB.2.1.2
    have hp : x.p8.toNat < 2 ^ 31 := hC.2.2.2.1
    have hi : x.idx.toNat ≤ x.p8.toNat := hC.2.2.1
    have hI2 := hI.2
    have hoff := xrd_off ((s₀.regs.get64 .r8).setWidth 32) x.p8 x.L
      (by rw [BitVec.toNat_setWidth]; omega) hC.2.2.2.2.1
    have hbl := Fr_buf_load hm (BitVec.setWidth 64 ((BitVec.setWidth 32 (s₀.regs.get64 .r8)).ushiftRight 3)) 1 (by omega)
    vcgen [bswap32_havoc, shl_cl32_havoc]
    all_goals subst_vars
    all_goals try xsimp
    · simp only [hr13]; exact hbl
    · refine ⟨⟨c, f, XB_regs hXB rfl ?_ ?_ ?_ ?_, ⟨?_, ?_, ?_⟩, hL, ?_, ⟨?_, ?_, ?_⟩⟩,
        Nat.le_of_lt (lex3_lt rfl (toInt_toNat_lt' _) (by decide) (Or.inr ⟨rfl, by decide⟩))⟩
      all_goals try xsimp
      all_goals try first | rfl | exact hI | exact h10 | exact hbx | exact hax
      · simp only [hr12, BitVec.setWidth_32_64_32]; exact (ix_setl x _ _ hI hp _ _).1
      · simp only [hr12, BitVec.setWidth_32_64_32]; exact (ix_setl x _ _ hI hp _ _).2

set_option maxRecDepth 20000 in
theorem blk_dc6 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.Ldc6" := by
  cfg_block
  measure_hb "Ldc6"
    simp only [tab_Ldc6, tab_Ldd8, var_Ldc6, var_Ldd8]
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hXB, ⟨hI, h10, hbx⟩, hL, hax, hJ⟩, hn⟩ := hs₀
    have hm := hXB.1.2.2
    have hbp : s₀.regs.get64 .rbp = rsp0 t₀ - 8#64 := hXB.1.2.1.2.1
    have hfl : f.length = 0x78 := hXB.1.2.1.2.2.1
    have hcl : c.length = 764 := hXB.1.2.1.2.2.2.1.1
    have e1 : s₀.regs.get64 .rbp + BitVec.ofNat 64 (18446744073709551616 - 128)
        = rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 0x20 := by rw [hbp]; bv_omega
    have hb48 : s₀.regs.get64 .rbx + 48#64 = arg2 t₀ + BitVec.ofNat 64 48 := by rw [hbx]
    have hne : ∀ v, ne (wr c 48 4 v) = ne c := fun v => i32_wr c 48 4 44 v (by omega) (Or.inl (by omega))
    vcgen
    case vc3 =>
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.Ld50")
        ⟨rfl, (tab_Ld50 _ _ _ _ _ _).mpr ?_, Or.inl ?_⟩
      · subst_vars
        rename_i s₀ _ _ _ _ _
        try xsimp
        refine dc6_d50 hXB hL ((BitVec.setWidth 32 (s₀.regs.get64 .rsi)).ushiftRight 7 &&& BitVec.setWidth 32 1#64).toInt _ hax ?_ ?_ ?_ ?_ ?_ ⟨?_, ?_, ?_⟩
        all_goals try xsimp
        all_goals first | (rw [hb48, e1]) | rfl | exact hJ.1 | exact hJ.2.1 | exact hJ.2.2
      · rw [var_Ld50]; subst_vars
        rename_i s₀ _ _ _ _ _
        try xsimp
        refine lex3_lt rfl (toInt_toNat_lt' _) (by decide)
          (Or.inr ⟨dc6_slot hXB hL ((BitVec.setWidth 32 (s₀.regs.get64 .rsi)).ushiftRight 7 &&& BitVec.setWidth 32 1#64).toInt _ hax ?_ ?_ ?_ ?_ ?_, by decide⟩)
        all_goals try xsimp
        all_goals first | (rw [hb48, e1]) | rfl
    all_goals subst_vars
    all_goals try xsimp
    · rw [hb48, Fr_c_load hm hcl 48 4 (by omega)] <;> rfl
    · rw [hb48, e1, Fr_f_load (Fr_c_store hm hcl 48 4 (by omega) _) hfl 0x20 4 (by omega)] <;> rfl
    · rename_i s₀ _ _ _ _ _
      refine ⟨dc6_dd8 hXB hL ((BitVec.setWidth 32 (s₀.regs.get64 .rsi)).ushiftRight 7 &&& BitVec.setWidth 32 1#64).toInt _ hax ?_ ?_ ?_ ?_ ?_ ⟨?_, ?_, ?_⟩ ⟨?_, ?_, ?_⟩,
        Nat.le_of_lt (lex3_lt rfl (toInt_toNat_lt' _) (by decide)
          (Or.inr ⟨dc6_slot hXB hL ((BitVec.setWidth 32 (s₀.regs.get64 .rsi)).ushiftRight 7 &&& BitVec.setWidth 32 1#64).toInt _ hax ?_ ?_ ?_ ?_ ?_, by decide⟩))⟩
      all_goals try xsimp
      all_goals first | (rw [hb48, e1]) | rfl | exact hJ.1 | exact hJ.2.1 | exact hJ.2.2 | exact hI | exact hbx | exact h10

end Kraken.Examples.Sbr.Ps
