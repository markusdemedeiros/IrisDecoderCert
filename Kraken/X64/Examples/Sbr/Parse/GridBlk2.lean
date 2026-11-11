import Kraken.X64.Examples.Sbr.Parse.GridBlk1

/-!
# `read_sbr_grid`: the frame-class dispatch and the head of `FIXFIX`
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Grid

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

/-- The dispatch on `bs_frame_class` through the jump table. -/
theorem blk_L4478 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4478" := by
  cfg_block
  measure_hb "L4478"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hR, hax, h8, h15, h9, st, hD, hm⟩, hn⟩ := hs₀
    have hjc : JtC := hC.2.2.2.2.2.2
    obtain ⟨F, hF⟩ := T_jt k Ext x ra t₀ (Saved t₀) (st.withI ((s₀.regs.get64 .r9).setWidth 32))
    have h15' := lt4_cases _ h15
    have hmT : Hide _ := hm
    rw [hF] at hm
    simp only [JtW] at hm
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    · rcases h15' with h | h | h | h <;> (simp only [h, BitVec.add_zero, BitVec.reduceSetWidth, BitVec.reduceMul] at *; grind_cells0)
    · rename_i v hv
      left
      rcases h15' with h | h | h | h
      · rw [jt_target "read_sbr_grid_jt" "read_sbr_grid.L448b" hjc.1 v
          (by simp only [h, BitVec.add_zero, BitVec.reduceSetWidth, BitVec.reduceMul] at hv
              grind_cells0)]
        apply Table.ofLabels_at
        dsimp only [reduceTable, reduceVar]
        refine ⟨by decide, ?_, Or.inr ⟨rfl, by decide +kernel⟩⟩
        show Cls 0 k Ext x ra t₀ _
        simp only [Cls, Regs, Regs0, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        exact ⟨hC, hR, hax, h8, h, h9, st, hD, hmT⟩
      · rw [jt_target "read_sbr_grid_jt" "read_sbr_grid.L4773" hjc.2.1 v
          (by simp only [h, BitVec.add_zero, BitVec.reduceSetWidth, BitVec.reduceMul] at hv
              grind_cells0)]
        apply Table.ofLabels_at
        dsimp only [reduceTable, reduceVar]
        refine ⟨by decide, ?_, Or.inr ⟨rfl, by decide +kernel⟩⟩
        show Cls 1 k Ext x ra t₀ _
        simp only [Cls, Regs, Regs0, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        exact ⟨hC, hR, hax, h8, h, h9, st, hD, hmT⟩
      · rw [jt_target "read_sbr_grid_jt" "read_sbr_grid.L44e3" hjc.2.2.1 v
          (by simp only [h, BitVec.add_zero, BitVec.reduceSetWidth, BitVec.reduceMul] at hv
              grind_cells0)]
        apply Table.ofLabels_at
        dsimp only [reduceTable, reduceVar]
        refine ⟨by decide, ?_, Or.inr ⟨rfl, by decide +kernel⟩⟩
        show Cls 2 k Ext x ra t₀ _
        simp only [Cls, Regs, Regs0, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        exact ⟨hC, hR, hax, h8, h, h9, st, hD, hmT⟩
      · rw [jt_target "read_sbr_grid_jt" "read_sbr_grid.L46a2" hjc.2.2.2 v
          (by simp only [h, BitVec.add_zero, BitVec.reduceSetWidth, BitVec.reduceMul] at hv
              grind_cells0)]
        apply Table.ofLabels_at
        dsimp only [reduceTable, reduceVar]
        refine ⟨by decide, ?_, Or.inr ⟨rfl, by decide +kernel⟩⟩
        show Cls 3 k Ext x ra t₀ _
        simp only [Cls, Regs, Regs0, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        exact ⟨hC, hR, hax, h8, h, h9, st, hD, hmT⟩

/-- FIXFIX: `get_bits(gb, 2)`, `bs_num_env = 1 << tmp`, the check against the maximum. -/
theorem blk_L448b (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L448b" := by
  cfg_block
  measure_hb "L448b"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hR, hax, h8, h15, h9, st, hD, hm⟩, hn⟩ := hs₀
    have hp : x.p8.toNat < 2 ^ 31 := hC.2.2.2.1
    have hoff := rd_off ((s₀.regs.get64 .r9).setWidth 32) x.p8 x.L
      (by rw [BitVec.toNat_setWidth]; omega) hC.2.2.2.2.1
    have h30 := shr30_lt
    have hbl := T_buf_load hm _ 4 hoff
    obtain ⟨F, hg⟩ := T_gb hm
    have hst := T_storeI hm
    have hus := fun v => T_load_usac (hst v)
    have hav := fun v => T_load_avctx (hst v)
    have hrdx : s₀.regs.get64 .rdx = arg2 t₀ := hR.1.2.2.2.1
    have hrsi : s₀.regs.get64 .rsi = arg1 t₀ := hR.1.2.2.2.2.2
    have hrdi : s₀.regs.get64 .rdi = arg0 t₀ := hR.1.2.2.2.2.1
    have hmT : Hide _ := hm
    have pR : PLift (Regs t₀ s₀) := ⟨hR⟩
    clear hm
    vcgen [bswap32_havoc, shl_cl32_havoc, shl_cl64_val]
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero,
      Int64.toBitVec_neg_ofNat_norm, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
      BitVec.setWidth_32_64_32, hrdx, hrsi, hrdi, get64_ite, ite_self] at *
    all_goals try simp only [hus, hav, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt64_ofBytes_toBytes8] at *
    case vc1 => grind_cells'
    case vc2 => grind_cells'
    case vc3 => rfl
    case vc5 => rfl
    · generalize hc : (BitVec.setWidth 32 _).ushiftRight 30 = c at *
      have hc4 : c.toNat < 4 := hc ▸ shr30_lt _
      left
      apply Table.ofLabels_at
      dsimp only [reduceTable, reduceVar]
      refine ⟨by decide, ⟨hC, ?_, ?_, ?_, ?_, _, ?_, hst _⟩, ?_⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h8, hax,
        BitVec.setWidth_32_64_32, GSt.withI, BitVec.toNat_setWidth] at *
      · exact pR.down
      · omega
      · rcases lt4_cases32 c hc4 with rfl | rfl | rfl | rfl <;> rfl
      · have hle := ‹CondCode.le.interp _ = true›
        clear hst hmT hbl hg
        by_cases hu : x.usac = 0#32 <;> simp only [hu, ↓reduceIte, BitVec.ofInt_toInt] at hle ⊢ <;>
          rcases lt4_cases32 c hc4 with rfl | rfl | rfl | rfl <;>
          first | decide | (revert hle; decide)
      · refine ⟨hD.1, hD.2, ?_⟩
        dsimp only
        grind_cells'
      · edge_lt
    · left
      apply Table.ofLabels_at
      dsimp only [reduceTable, reduceVar]
      refine ⟨by decide, ⟨⟨hC, ?_, ?_, _, ?_, hst _⟩, ?_⟩, ?_⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h8, hax,
        BitVec.setWidth_32_64_32, GSt.withI] at *
      · exact pR.down.1.1
      · exact pR.down.1.2.2.1
      · refine ⟨hD.1, hD.2, ?_⟩
        dsimp only
        grind_cells'
      · grind_cells'
      · edge_lt

end Kraken.Examples.Sbr.Grid
