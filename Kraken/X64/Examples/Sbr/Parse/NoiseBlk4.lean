import Kraken.X64.Examples.Sbr.Parse.NoiseFrame

/-!
# `read_sbr_noise`: the end of a row, the exit, the traps
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Noise

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

theorem blk_L6640 (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_noise.L6640" := by
  cfg_block
  measure_hb "L6640"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨⟨hC, hR, i, hi, hm⟩, ⟨c, hc12, hcn, hc13⟩⟩, hn⟩ := hs₀
    have hnn : x.nn ≤ 2 := hC.1
    have hL := LcL.of hm hR.2.1
    have hnl := T_ld_nn hm
    have pc12 : PLift _ := ⟨hc12⟩
    have pc13 : PLift _ := ⟨hc13⟩
    have pR : PLift _ := ⟨hR⟩
    vcgen
    all_goals try subst_vars
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals nnorm
    all_goals try (simp only [hL.d, Option.isSome_some]; done)
    all_goals try simp only [hL.d, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt] at *
    all_goals try (simp only [hnl, Option.isSome_some]; done)
    all_goals try simp only [hnl, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt32_ofBytes_toBytes4] at *
    case vc5 =>
      rename_i h1 h2
      rw [pc12.down, succ64 c (by omega)] at h1 h2
      rw [nat32to64 _ (by omega)] at h2
      flg h1
      flg h2
      omega
    case vc3 =>
      rename_i h2
      left
      apply Table.ofLabels_at
      dsimp only [reduceTable, reduceVar]
      refine ⟨by decide, ⟨⟨hC, ?_, i, hi, hm⟩, ?_, ?_⟩, Or.inl (by simp only [Nat.add_eq, Nat.succ_eq_add_one]; omega)⟩ <;>
        try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      · exact pR.down
      · exact nat32to64 _ (by omega)
    case vc4 =>
      rename_i h1 h2
      rw [pc12.down, succ64 c (by omega)] at h1 h2
      rw [nat32to64 _ (by omega)] at h2
      flg h1
      flg h2
      left
      apply Table.ofLabels_at
      dsimp only [reduceTable, reduceVar]
      refine ⟨by decide, ⟨⟨hC, ?_, i, hi, hm⟩, ⟨c + 1, ?_, ?_, ?_⟩, ?_⟩, Or.inl ?_⟩ <;>
        try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      · exact pR.down
      · rw [pc12.down]; exact succ64 c (by omega)
      · omega
      · rw [pc13.down, ← add5 _ c (by omega)]
        simp only [arg3]
        show 5#64 + _ = _
        ac_rfl
      · rw [pc12.down, succ64 c (by omega)]
        simp only [Nat.add_eq, Nat.succ_eq_add_one, BitVec.toNat_ofNat]
        omega

theorem blk_L66cf (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_noise.L66cf" := by
  cfg_block
  intro n
  exact Triple.pin fun _ h => by dsimp only [reduceTable] at h; exact h.1.elim

theorem blk_L66d4 (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_noise.L66d4" := by
  cfg_block
  intro n
  exact Triple.pin fun _ h => by dsimp only [reduceTable] at h; exact h.1.elim

theorem blk_L66d9 (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_noise.L66d9" := by
  cfg_block
  intro n
  exact Triple.pin fun _ h => by dsimp only [reduceTable] at h; exact h.1.elim

theorem blk_L6663 (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_noise.L6663" := by
  cfg_block
  measure_hb "L6663"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hR, hM⟩, hn⟩ := hs₀
    vcgen
    all_goals try subst_vars
    all_goals try dsimp only [reduceTable, reduceVar] at *
    refine ⟨⟨hC, ?_, hM⟩, Nat.le.refl⟩
    try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    exact hR

theorem blk_L66c9 (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_noise.L66c9" := by
  cfg_block
  measure_hb "L66c9"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hR, hM⟩, hn⟩ := hs₀
    vcgen
    all_goals try subst_vars
    all_goals try dsimp only [reduceTable, reduceVar] at *
    left
    apply Table.ofLabels_at
    dsimp only [reduceTable, reduceVar]
    refine ⟨by decide, ⟨hC, ?_, hM⟩, ?_⟩
    · try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      exact hR
    · edge_lt

theorem blk_L66ba (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_noise.L66ba" := by
  cfg_block
  measure_hb "L66ba"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨⟨hC, hsp, hbp, i, hi, hm⟩, hrv⟩, hn⟩ := hs₀
    have hmT : PLift _ := ⟨hm⟩
    rw [T_saved] at hm
    generalize 8 ?@ (t₀.regs.get64 .rsp - 0x60#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x60#64)
      ⋆ (Blank t₀ ⋆ (NoiseF Ext x t₀ i ⋆ Rest x.R ra t₀))) = Q at hm
    have po := pop_offs (t₀.regs.get64 .rsp)
    have l1 : s₀.dmem.loadInt (t₀.regs.get64 .rsp - 48#64) 8
        = some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 .rbx).toInt)) := by grind_cells'
    have l2 : s₀.dmem.loadInt (t₀.regs.get64 .rsp - 40#64) 8
        = some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 .r12).toInt)) := by grind_cells'
    have l3 : s₀.dmem.loadInt (t₀.regs.get64 .rsp - 32#64) 8
        = some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 .r13).toInt)) := by grind_cells'
    have l4 : s₀.dmem.loadInt (t₀.regs.get64 .rsp - 24#64) 8
        = some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 .r14).toInt)) := by grind_cells'
    have l5 : s₀.dmem.loadInt (t₀.regs.get64 .rsp - 16#64) 8
        = some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 .r15).toInt)) := by grind_cells'
    have l6 : s₀.dmem.loadInt (t₀.regs.get64 .rsp - 8#64) 8
        = some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 .rbp).toInt)) := by grind_cells'
    clear hm
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try subst_vars
    all_goals simp only [hsp, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, Reg64s.get64_set64,
      reduceCtorEq, ↓reduceIte, po.1, po.2.1, po.2.2.1, po.2.2.2.1, po.2.2.2.2.1, po.2.2.2.2.2.1,
      po.2.2.2.2.2.2] at *
    all_goals simp only [l1, l2, l3, l4, l5, l6, Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]
    refine ⟨⟨hC, trivial, trivial, ?_, ?_, i, hi, hmT.down⟩, Nat.zero_le _⟩ <;>
      simp only [SavedRegs, RetV, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, and_self]
    exact hrv

theorem blk_done (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_noise.done" := by
  cfg_block
  measure_hb "done"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hsp, hbp, hsv, hrv, i, hi, hm⟩, hn⟩ := hs₀
    rw [T_ret] at hm
    have hpost : s₀.dmem =⋆ 8 ?@ t₀.regs.get64 .rsp ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x60#64)
        ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x60#64) ⋆ (Blank t₀ ⋆ (NoiseF Ext x t₀ i
        ⋆ Saved t₀ x.R)))) :=
      Block.sep_intro (Int.toBytes_length _ _) (by decide) hm
    rw [← Post_mem] at hpost
    generalize 8 ?@ (t₀.regs.get64 .rsp - 0x60#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x60#64)
        ⋆ (Blank t₀ ⋆ (NoiseF Ext x t₀ i ⋆ Saved t₀ x.R))) = Q at hm
    have l0 : s₀.dmem.loadInt (t₀.regs.get64 .rsp) 8
        = some (Int.ofBytes (Int.toBytes 8 ra.toBitVec.toInt)) := by grind_cells'
    have hra : s₀.retAddr = some ra := by
      simp only [MachineData.retAddr, hsp, l0, Option.map_some,
        BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Int64.ofBitVec_toBitVec]
    clear hm l0
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try subst_vars
    all_goals simp only [hra, Option.isSome_some, Option.some.injEq] at *
    subst_vars
    right
    refine ⟨rfl, i, hi, ?_, ?_, ?_, ?_, hpost⟩ <;>
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hsp, hbp, hsv, and_self]
    · exact hrv
    · rfl

theorem blk_L6689 (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_noise.L6689" := by
  cfg_block
  measure_hb "L6689"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨⟨hC, hR, i, hi, hm⟩, h9, h8⟩, hn⟩ := hs₀
    have hnn : x.nn ≤ 2 := hC.1
    have p8 : PLift _ := ⟨h8⟩
    have p9 : PLift _ := ⟨h9⟩
    have pR : PLift _ := ⟨hR⟩
    vcgen
    all_goals try subst_vars
    all_goals try dsimp only [reduceTable, reduceVar] at *
    case vc1 =>
      rename_i h
      rw [p8.down] at h
      flg h
      exfalso; omega
    case vc2 =>
      refine ⟨⟨⟨hC, ?_, ?_, i, hi, T_blank hm⟩, ?_, ?_, ?_⟩, Nat.le.refl⟩ <;>
        try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      · exact pR.down.1
      · exact pR.down.2.1
      · exact p9.down
      · exact p8.down
      · rfl

theorem blk_L64dc (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_noise.L64dc" := by
  cfg_block
  measure_hb "L64dc"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨⟨hC, hR, i, hi, hm⟩, c, ⟨hc12, hcn, hc13⟩, hbx⟩, hn⟩ := hs₀
    have hnq5 : x.nq ≤ 5 := hC.2.1
    have hnq := NqL.of hm hR.2.2.1
    have pc12 : PLift _ := ⟨hc12⟩
    have pc13 : PLift _ := ⟨hc13⟩
    have pR : PLift _ := ⟨hR⟩
    vcgen
    all_goals try subst_vars
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals nnorm
    all_goals try (simp only [hnq.ld, Option.isSome_some]; done)
    all_goals try simp only [hnq.ld, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt32_ofBytes_toBytes4] at *
    case vc2 =>
      left
      apply Table.ofLabels_at
      dsimp only [reduceTable, reduceVar]
      refine ⟨by decide, ⟨⟨hC, pR.down, i, hi, hm⟩, c, pc12.down, hcn, pc13.down⟩, Or.inl ?_⟩
      simp only [Nat.add_eq, Nat.succ_eq_add_one]; omega
    case vc3 =>
      rename_i h
      flg h
      exfalso; omega

end Kraken.Examples.Sbr.Noise
