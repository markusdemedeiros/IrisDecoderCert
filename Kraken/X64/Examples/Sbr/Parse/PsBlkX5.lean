import Kraken.X64.Examples.Sbr.Parse.PsBlkXLib

/-!
# `ff_ps_read_data`, the extension: the envelope loop latch `0xe00` and the `ipd`/`opd` heads
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
theorem blk_e00 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.Le00" := by
  cfg_block
  measure_hb "Le00"
    simp only [tab_Le00, var_Le00, tab_Le15, var_Le15]
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hXB, hL, hN, hJ, hP⟩, hn⟩ := hs₀
    have hm := hXB.1.2.2
    have hbp : s₀.regs.get64 .rbp = rsp0 t₀ - 8#64 := hXB.1.2.1.2.1
    have hfl : f.length = 0x78 := hXB.1.2.1.2.2.1
    have hcl : c.length = 764 := hXB.1.2.1.2.2.2.1.1
    have hPI := hXB.1.2.1.2.2.2.1
    have hne := hPI.2.2.2.2.2.1
    have ea : ∀ o : Nat, o ≤ 0xa0 → s₀.regs.get64 .rbp + BitVec.ofNat 64 (18446744073709551616 - (0xa0 - o))
        = rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 o := by
      intro o ho; rw [hbp]; apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have l1 := Fr_f_load hm hfl 0x48 8 (by omega)
    rw [← ea 0x48 (by omega)] at l1
    have hs64 : slot64 s₀ 0x58 = _ := slot64_Fr hm hfl hbp 0x48 (by omega)
    have hr15 := hP.2.2.1
    have hN64 := hL.2
    vcgen
    all_goals subst_vars
    all_goals try xsimp
    · rw [l1]; rfl
    · rename_i v hv hc
      xsimp_at hv
      rw [l1, Option.some.injEq] at hv
      subst hv
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.Ld50")
        ⟨rfl, (tab_Ld50 _ _ _ _ _ _).mpr ⟨c, f, XB_regs hXB rfl ?_ ?_ ?_ ?_, hL, hN, ?_⟩, Or.inl ?_⟩
      all_goals try (xsimp; done)
      · simp only [XJ]; xsimp; exact hJ
      · rw [var_Ld50]
        refine lex3_lt rfl (toInt_toNat_lt' _) (by decide) (Or.inr ⟨?_, by decide⟩)
        exact congrArg (fun z => z.toInt.toNat) (slot32_regs rfl (by xsimp) _)
    · rename_i s₀ v hv hc
      xsimp_at hv
      rw [l1, Option.some.injEq] at hv
      subst hv
      xsimp_at hc
      rw [z_sub] at hc
      have hc' := of_decide_eq_false hc
      rw [hN64] at hc'
      have hlt : (s₀.regs.get64 .r15 + 1#64).toNat < (ne c).toNat := by
        have : (s₀.regs.get64 .r15 + 1#64).toNat ≠ (BitVec.ofNat 64 (ne c).toNat).toNat :=
          fun h => hc' (BitVec.eq_of_toNat_eq h)
        rw [BitVec.toNat_ofNat] at this
        rw [BitVec.toNat_add, BitVec.toNat_ofNat] at this ⊢
        simp only [ne, i32] at this hr15 ⊢
        omega
      refine ⟨⟨c, f, XB_regs hXB rfl ?_ ?_ ?_ ?_, hL, hN, ?_, ?_, ?_, ?_, ?_, ?_⟩, Nat.le_of_lt ?_⟩
      all_goals try (xsimp; done)
      · simp only [XJ]; xsimp; exact hJ
      · xsimp; exact hP.1
      · xsimp; exact hP.2.1
      · xsimp; exact hlt
      · xsimp; exact x_row_step _ _ _ 416 (by omega) hP.2.2.2.1
      · xsimp; exact x_row_step _ _ _ 586 (by omega) hP.2.2.2.2
      · refine lex4_lt rfl (congrArg (fun z => z.toInt.toNat) (slot32_regs rfl (by xsimp) _)) (BitVec.isLt _)
          (e00_dec _ _ _ (slot64_regs rfl (by xsimp) _) ?_)
        rw [hs64, hN64, BitVec.toNat_ofNat]; first | omega | (simp only [ne, i32]; omega)

set_option maxRecDepth 20000 in
theorem blk_e15 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.Le15" := by
  cfg_block
  measure_hb "Le15"
    simp only [tab_Le15, var_Le15, tab_Le32, var_Le32]
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hXB, hL, hN, hJ, hP⟩, hn⟩ := hs₀
    have hC := hXB.1.1
    have hm := hXB.1.2.2
    have hbp : s₀.regs.get64 .rbp = rsp0 t₀ - 8#64 := hXB.1.2.1.2.1
    have hr13 : s₀.regs.get64 .r13 = x.buf := hXB.2.1.1
    have hr12 : s₀.regs.get64 .r12 = x.p8.setWidth 64 := hXB.2.1.2
    have hp : x.p8.toNat < 2 ^ 31 := hC.2.2.2.1
    have hI2 := hJ.2.1.2
    have hoff := xrd_off ((s₀.regs.get64 .rdx).setWidth 32) x.p8 x.L
      (by rw [BitVec.toNat_setWidth]; omega) hC.2.2.2.2.1
    have hbl := Fr_buf_load hm (BitVec.setWidth 64 ((BitVec.setWidth 32 (s₀.regs.get64 .rdx)).ushiftRight 3)) 1 (by omega)
    vcgen [bswap32_havoc, shl_cl32_havoc]
    all_goals subst_vars
    all_goals try xsimp
    · simp only [hr13]; exact hbl
    · refine ⟨⟨c, f, XB_regs hXB rfl ?_ ?_ ?_ ?_, hL, hN, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩⟩, Nat.le_of_lt ?_⟩
      all_goals try (xsimp; done)
      all_goals try xsimp
      all_goals try first | exact hJ.1 | exact hP.1 | exact hP.2.1 | exact hP.2.2.1 | exact hP.2.2.2.1 | exact hP.2.2.2.2
      · simp only [hr12, BitVec.setWidth_32_64_32]; exact (ix_setl x _ _ hJ.2.1 hp _ _).1
      · simp only [hr12, BitVec.setWidth_32_64_32]; exact Nat.le_trans hJ.2.2 (ix_setl x _ _ hJ.2.1 hp _ _).2
      · exact lex5_lt rfl (vq1 hbp rfl (by xsimp)) (vq2 hbp rfl (by xsimp)) (by decide) (by decide)



set_option maxRecDepth 20000 in
theorem blk_e32 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.Le32" := by
  cfg_block
  measure_hb "Le32"
    simp only [tab_Le32, var_Le32, tab_Le4c, var_Le4c]
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hXB, hL, hN, hJ, hP⟩, hn⟩ := hs₀
    have hC := hXB.1.1
    have hm := hXB.1.2.2
    have hbp : s₀.regs.get64 .rbp = rsp0 t₀ - 8#64 := hXB.1.2.1.2.1
    obtain ⟨j, hj, he⟩ := vsel (BitVec.setWidth 32 (s₀.regs.get64 .rdi)) 48
    have lv := Fr_vptr_load hm (6 + j) (by omega)
    rw [show 8 * (6 + j) = 48 + 8 * j by omega, ← he] at lv
    have hpv : BitVec.ofInt 64 (Int.ofBytes (Int.toBytes 8 (x.v (6 + j)).p.toInt)) = (x.v (6 + j)).p :=
      BitVec.ofInt_ofBytes_toBytes 64 8 rfl _
    vcgen
    all_goals subst_vars
    all_goals try xsimp
    · rw [lv]; rfl
    · rename_i v hv _ hc
      xsimp_at hv
      rw [lv, Option.some.injEq] at hv
      subst hv
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.Leb0")
        ⟨rfl, (tab_Leb0 _ _ _ _ _ _).mpr ⟨c, f, XB_regs hXB rfl ?_ ?_ ?_ ?_, hL, hN, XJ_regs hJ ?_, XP_regs hP ?_ ?_ ?_ ?_, 6 + j, by omega, by omega, ?_⟩, Or.inl ?_⟩
      all_goals try (xsimp; done)
      · xsimp; exact hpv
      · rw [var_Leb0]
        exact lex5_lt rfl (vq1 hbp rfl (by xsimp)) (vq2 hbp rfl (by xsimp)) (by decide) (by decide)
    · rename_i v hv _ hc
      xsimp_at hv
      rw [lv, Option.some.injEq] at hv
      subst hv
      refine ⟨⟨c, f, XB_regs hXB rfl ?_ ?_ ?_ ?_, hL, hN, XJ_regs hJ ?_, XP_regs hP ?_ ?_ ?_ ?_, 6 + j, by omega, by omega, ?_⟩, Nat.le_of_lt ?_⟩
      all_goals try (xsimp; done)
      · xsimp; exact hpv
      · exact lex5_lt rfl (vq1 hbp rfl (by xsimp)) (vq2 hbp rfl (by xsimp)) (by decide) (by decide)

end Kraken.Examples.Sbr.Ps
