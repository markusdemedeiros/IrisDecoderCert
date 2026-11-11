import Kraken.X64.Examples.Sbr.Parse.PsBlkXLib

/-!
# `ff_ps_read_data`, the extension: the loop latch `0xd50` and the envelope loop entry `0xdd8`
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
theorem blk_d50 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.Ld50" := by
  cfg_block
  measure_hb "Ld50"
    simp only [tab_Ld50, tab_Ld70, var_Ld50, var_Ld70]
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hXB, hL, hN, hJ⟩, hn⟩ := hs₀
    have hm := hXB.1.2.2
    have hbp : s₀.regs.get64 .rbp = rsp0 t₀ - 8#64 := hXB.1.2.1.2.1
    have hfl : f.length = 0x78 := hXB.1.2.1.2.2.1
    have hLS := hXB.2.2.1
    have hr12 : s₀.regs.get64 .r12 = x.p8.setWidth 64 := hXB.2.1.2
    have hp : x.p8.toNat < 2 ^ 31 := hXB.1.1.2.2.2.1
    have hsl : slot32 s₀ 0x80 = BitVec.ofInt 32 (rd f 0x20 4) := slot32_Fr hm hfl hbp 0x20 (by omega)
    have ea : ∀ o : Nat, o ≤ 0xa0 → s₀.regs.get64 .rbp + BitVec.ofNat 64 (18446744073709551616 - (0xa0 - o))
        = rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 o := by
      intro o ho; rw [hbp]; apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have l1 := Fr_f_load hm hfl 0x68 8 (by omega)
    have l2 := Fr_f_load hm hfl 0x40 8 (by omega)
    have l3 := Fr_f_load hm hfl 0x20 4 (by omega)
    rw [← ea 0x68 (by omega)] at l1
    rw [← ea 0x40 (by omega)] at l2
    rw [← ea 0x20 (by omega)] at l3
    rw [hsl] at hn
    vcgen
    all_goals subst_vars
    all_goals try xsimp
    · rw [l1]; rfl
    · rename_i v1 hv1
      xsimp_at hv1
      rw [l1, Option.some.injEq] at hv1
      subst hv1
      rw [l2]; rfl
    · rename_i v1 hv1 v2 hv2
      xsimp_at hv1
      rw [l1, Option.some.injEq] at hv1
      subst hv1
      xsimp_at hv2
      rw [l2, Option.some.injEq] at hv2
      subst hv2
      rw [l3]; rfl
    · rename_i v1 hv1 v2 hv2 v3 hv3
      xsimp_at hv1
      rw [l1, Option.some.injEq] at hv1
      subst hv1
      xsimp_at hv2
      rw [l2, Option.some.injEq] at hv2
      subst hv2
      xsimp_at hv3
      rw [l3, Option.some.injEq] at hv3
      subst hv3
      refine ⟨⟨c, f, XB_regs hXB rfl ?_ ?_ ?_ ?_, ⟨?_, ?_, ?_⟩, hL⟩,
        Nat.le_of_lt (lex3_le rfl (toInt_toNat_lt' _) (by decide) ?_ (by decide))⟩
      all_goals try xsimp
      all_goals try rfl
      · simp only [hr12, BitVec.setWidth_32_64_32]; exact (ix_inc x _ hJ.2.1 hp _ _).1
      · exact (congrArg (fun z => (BitVec.ofInt 64 z).toNat) hLS.2.2.2).trans
          (ofInt_ne_toNat _ hLS.1.1 hLS.1.2.1)
      · exact hLS.2.2.1
      · simp only [hr12, BitVec.setWidth_32_64_32]; exact d50_le x _ _ _ hN hJ.1 hJ.2.1 hJ.2.2 hp _ _

set_option maxRecDepth 20000 in
theorem blk_dd8 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.Ldd8" := by
  cfg_block
  measure_hb "Ldd8"
    simp only [tab_Ldd8, var_Ldd8]
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hXB, ⟨hI, h10, hbx⟩, hL, hN, hJ⟩, hn⟩ := hs₀
    have hm := hXB.1.2.2
    have hbp : s₀.regs.get64 .rbp = rsp0 t₀ - 8#64 := hXB.1.2.1.2.1
    have hfl : f.length = 0x78 := hXB.1.2.1.2.2.1
    have hcl : c.length = 764 := hXB.1.2.1.2.2.2.1.1
    have hPI := hXB.1.2.1.2.2.2.1
    have ea : ∀ o : Nat, o ≤ 0xa0 → s₀.regs.get64 .rbp + BitVec.ofNat 64 (18446744073709551616 - (0xa0 - o))
        = rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 o := by
      intro o ho; rw [hbp]; apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have l1 := Fr_c_load hm hcl 16 4 (by omega)
    have l2 := Fr_f_load hm hfl 0x28 8 (by omega)
    have l3 := Fr_f_load hm hfl 0x50 8 (by omega)
    rw [← hbx] at l1
    rw [← ea 0x28 (by omega)] at l2
    rw [← ea 0x50 (by omega)] at l3
    have hne := hPI.2.2.2.2.2.1
    vcgen
    case vc1 =>
      subst_vars
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.Ld50")
        ⟨rfl, (tab_Ld50 _ _ _ _ _ _).mpr ⟨c, f, XB_regs hXB rfl rfl rfl rfl rfl, hL, hN, hJ⟩, Or.inl ?_⟩
      rw [var_Ld50]
      exact lex3_lt rfl (toInt_toNat_lt' _) (by decide) (Or.inr ⟨rfl, by decide⟩)
    all_goals subst_vars
    all_goals try xsimp
    · rw [l1]; rfl
    · rw [l2]; rfl
    · rw [l3]; rfl
    · rename_i a0 hle v1 hv1 v2 hv2 v3 hv3 a1
      xsimp_at hv1
      rw [l1, Option.some.injEq] at hv1
      subst hv1
      xsimp_at hv2
      rw [l2, Option.some.injEq] at hv2
      subst hv2
      xsimp_at hv3
      rw [l3, Option.some.injEq] at hv3
      subst hv3
      dsimp only at hle
      rw [test_le8 _ (by omega)] at hle
      have h0 := of_decide_eq_false hle
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.Le15")
        ⟨rfl, (tab_Le15 _ _ _ _ _ _).mpr ⟨c, f, XB_regs hXB rfl ?_ ?_ ?_ ?_, hL, hN, ?_, ?_, ?_, ?_, ?_, ?_⟩, Or.inl ?_⟩
      all_goals try (xsimp; done)
      · simp only [XJ]; xsimp; exact hJ
      · xsimp; have := (BitVec.ofInt 32 (rd c 16 4)).isLt; simp only [BitVec.toNat_setWidth]; omega
      · xsimp; rw [x_rd_i32]; exact hPI.2.2.1
      · xsimp; simp only [BitVec.xor_self]; simp; first | (simp only [ne, i32]; omega) | (unfold ne; omega)
      · xsimp; simp only [BitVec.xor_self]; rw [hL.1.1]; rfl
      · xsimp; simp only [BitVec.xor_self]; rw [hL.1.2]; rfl
      · rw [var_Le15]
        refine lex3_lt rfl (toInt_toNat_lt' _) (by decide) (Or.inr ⟨?_, by decide⟩)
        exact congrArg (fun z => z.toInt.toNat) (slot32_regs rfl (by xsimp) _)

end Kraken.Examples.Sbr.Ps
