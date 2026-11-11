import Kraken.X64.Examples.Sbr.Parse.GridMem

/-!
# `read_sbr_grid`: the error paths and the return

The two `av_log` calls (`AvLogSpec`, its frame `Ext` inside the footprint), the return value
`-1`, the five pops and the `ret`.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Grid

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

theorem blk_L4ed3 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4ed3" := by
  cfg_block
  measure_hb "L4ed3"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hE, hn⟩ := hs₀
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    left; apply Table.ofLabels_at
    dsimp only [reduceTable, reduceVar]
    refine ⟨by decide, hE, ?_⟩
    edge_lt

omit [CodeEnv] in
theorem gridOut_err {x : GArgs} {st : GSt} (hS : SInv x st) : GridOut x st 0xffffffff#32 :=
  ⟨hS.1, hS.2.1, Or.inr rfl, fun h => absurd h (by decide), hS.2.2⟩

theorem blk_L5086 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L5086" := by
  cfg_block
  measure_hb "L5086"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hsp, h13, st, hS, hm⟩, hn⟩ := hs₀
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    exact ⟨⟨hC, hsp, h13, st, gridOut_err hS, hm⟩, Nat.le_refl _⟩

theorem blk_L4ec4 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4ec4" := by
  cfg_block
  measure_hb "L4ec4"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, hsp, h13, st, hS, hm⟩, hdi⟩, hn⟩ := hs₀
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    exact ⟨⟨⟨hC, hsp, h13, st, hS, hm⟩, hdi⟩, Nat.le_refl _⟩

omit [CodeEnv] in
theorem pop_offs (t : BitVec 64) : t - 40#64 + 8#64 = t - 32#64 ∧ t - 40#64 + 16#64 = t - 24#64
    ∧ t - 32#64 + 8#64 = t - 24#64 ∧ t - 32#64 + 16#64 = t - 16#64
    ∧ t - 32#64 + 24#64 = t - 8#64 ∧ t - 32#64 + 32#64 = t
    ∧ t - 24#64 + 8#64 = t - 16#64 ∧ t - 16#64 + 8#64 = t - 8#64 ∧ t - 8#64 + 8#64 = t := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_omega

theorem blk_L508b (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L508b" := by
  cfg_block
  measure_hb "L508b"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hsp, h13, st, hO, hm⟩, hn⟩ := hs₀
    have hmT : Hide _ := hm
    rw [T_saved] at hm
    generalize 8 ?@ (t₀.regs.get64 .rsp - 0x30#64)
      ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x30#64) ⋆ (GFB Ext x t₀ st ⋆ Rest x.R ra t₀)) = Q at hm
    have po := pop_offs (t₀.regs.get64 .rsp)
    have l1 : s₀.dmem.loadInt (t₀.regs.get64 .rsp - 40#64) 8
        = some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 .rbx).toInt)) := by grind_cells'
    have l2 : s₀.dmem.loadInt (t₀.regs.get64 .rsp - 32#64) 8
        = some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 .r12).toInt)) := by grind_cells'
    have l3 : s₀.dmem.loadInt (t₀.regs.get64 .rsp - 24#64) 8
        = some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 .r14).toInt)) := by grind_cells'
    have l4 : s₀.dmem.loadInt (t₀.regs.get64 .rsp - 16#64) 8
        = some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 .r15).toInt)) := by grind_cells'
    have l5 : s₀.dmem.loadInt (t₀.regs.get64 .rsp - 8#64) 8
        = some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 .rbp).toInt)) := by grind_cells'
    clear hm
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals simp only [hsp, BitVec.reduceAdd, po.1, po.2.1, po.2.2.1, po.2.2.2.1, po.2.2.2.2.1, po.2.2.2.2.2.1,
      po.2.2.2.2.2.2.1, po.2.2.2.2.2.2.2.1, po.2.2.2.2.2.2.2.2] at *
    all_goals simp only [l1, l2, l3, l4, l5, Option.isSome_some, Option.some.injEq] at *
    subst_vars
    simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]
    refine ⟨⟨hC, ?_, ?_, ⟨?_, ?_, h13, ?_, ?_⟩, st, hO, hmT⟩, Nat.le_refl _⟩ <;>
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]

theorem Post_mem (k : Nat) (Ext : Mem 64 → Prop) (x : GArgs) (t₀ : MachineData) (st : GSt) :
    (8 ?@ (t₀.regs.get64 .rsp - 0x30#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x30#64)
      ⋆ (GFB Ext x t₀ st ⋆ Saved t₀ (8 ?@ t₀.regs.get64 .rsp ⋆ x.R))))
    = 8 ?@ t₀.regs.get64 .rsp ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x30#64)
      ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x30#64) ⋆ (GFB Ext x t₀ st ⋆ Saved t₀ x.R))) := by
  simp only [Saved]; ac_rfl

theorem blk_done (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.done" := by
  cfg_block
  measure_hb "done"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hsp, hbp, hsv, st, hO, hm⟩, hn⟩ := hs₀
    rw [T_ret] at hm
    have hpost : s₀.dmem =⋆ 8 ?@ t₀.regs.get64 .rsp ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x30#64)
        ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x30#64) ⋆ (GFB Ext x t₀ st ⋆ Saved t₀ x.R))) :=
      Block.sep_intro (Int.toBytes_length _ _) (by decide) hm
    rw [← Post_mem] at hpost
    generalize 8 ?@ (t₀.regs.get64 .rsp - 0x30#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x30#64)
        ⋆ (GFB Ext x t₀ st ⋆ Saved t₀ x.R)) = Q at hm
    have l0 : s₀.dmem.loadInt (t₀.regs.get64 .rsp) 8
        = some (Int.ofBytes (Int.toBytes 8 ra.toBitVec.toInt)) := by grind_cells'
    have hra : s₀.retAddr = some ra := by
      simp only [MachineData.retAddr, hsp, l0, Option.map_some,
        BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Int64.ofBitVec_toBitVec]
    clear hm l0
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals simp only [hra, Option.isSome_some, Option.some.injEq] at *
    subst_vars
    right; left
    refine ⟨rfl, st, ?_, ?_, ?_, ?_, hpost⟩
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hsp, hbp, hsv, and_self]
    · exact hO
    · rfl

/-- `av_log(avctx, AV_LOG_ERROR, …)`. -/
theorem blk_L4ecc (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop) (hAv : AvLogSpec Ext k)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4ecc" := by
  cfg_block
  measure_hb "L4ecc"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, hsp, h13, st, hS, hm⟩, hdi⟩, hn⟩ := hs₀
    obtain ⟨F, hF⟩ := T_ext k Ext x ra t₀ (Saved t₀) st
    rw [hF] at hm
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rsp - 8#64) 8).isSome = true := by
      rw [hsp, BitVec.sub_sub_ofNat]
      exact Block.loadInt_isSome hm (by simp)
    have hpush := fun v => Block.storeInt_val hm (Split.here _ _) v
    have e48 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 48#64 := by
      rw [hsp]; show _ - 40#64 - 8#64 = _; bv_omega
    vcgen [MachineWP.call_proc_spec_at F "av_log" hAv]
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    refine ⟨fun ra' => ⟨⟨?_, trivial⟩, fun s' hpost => ?_⟩, hld⟩
    · rw [e48]; exact hpush _
    · rw [e48] at hpost
      obtain ⟨hsp', -, ⟨-, -, h13', -, -⟩, hm'⟩ := hpost
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨⟨hC, ?_, ?_, st, hS, ?_⟩, Nat.le_refl _⟩
      · rw [hsp']; bv_omega
      · rw [h13', h13]
      · show T k Ext x ra t₀ (Saved t₀) st _
        exact (congrFun hF s'.dmem).mpr hm'

/-- `av_log(ac->avctx, AV_LOG_ERROR, …)` for the border check. -/
theorem blk_L506f (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop) (hAv : AvLogSpec Ext k)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L506f" := by
  cfg_block
  measure_hb "L506f"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, hsp, h13, st, hS, hm⟩, hdi⟩, hn⟩ := hs₀
    have hav := T_load_avctx hm
    obtain ⟨F, hF⟩ := T_ext k Ext x ra t₀ (Saved t₀) st
    rw [hF] at hm
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rsp - 8#64) 8).isSome = true := by
      rw [hsp, BitVec.sub_sub_ofNat]
      exact Block.loadInt_isSome hm (by simp)
    have hpush := fun v => Block.storeInt_val hm (Split.here _ _) v
    have e48 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 48#64 := by
      rw [hsp]; show _ - 40#64 - 8#64 = _; bv_omega
    vcgen [MachineWP.call_proc_spec_at F "av_log" hAv]
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [hdi, AddrIndex.offset64_none, BitVec.add_zero, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, Option.isSome_some, Option.some.injEq] at *
    all_goals try simp only [arg0] at hav
    all_goals try simp only [hav, Option.isSome_some, Option.some.injEq] at *
    refine ⟨fun ra' => ⟨⟨?_, trivial⟩, fun s' hpost => ?_⟩, hld⟩
    · rw [e48]; exact hpush _
    · rw [e48] at hpost
      obtain ⟨hsp', -, ⟨-, -, h13', -, -⟩, hm'⟩ := hpost
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨⟨hC, ?_, ?_, st, hS, ?_⟩, Nat.le_refl _⟩
      · rw [hsp']; bv_omega
      · rw [h13', h13]
      · exact (congrFun hF s'.dmem).mpr hm'

end Kraken.Examples.Sbr.Grid
