import Kraken.X64.Examples.Sbr.Parse.GridShD9

/-!
# `read_sbr_grid`: VARVAR `get_bits(gb, ceil_log2[bs_num_env])` (shard D, part 10)

VARFIX's `L45cb` (the `ceil_log2` load) and `L45d8` (shard A) in one block.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Grid

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

/-- `get_bits(gb, ceil_log2[n])` (the VARVAR pointer bits, after `movsbl ceil_log2(%rax)`; the count `eax` is havocked). -/
theorem blk_L4c5c (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4c5c" := by
  cfg_block
  measure_hb "L4c5c"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hRB, hdx, hdi, st, ⟨hP, h5, hax, hcx⟩, hm⟩, hn⟩ := hs₀
    obtain ⟨F', hB⟩ := T_blocks hm
    have pax : PLift (s₀.regs.get64 .rax = st.n.setWidth 64) := ⟨hax⟩
    have pcx : PLift (s₀.regs.get64 .rcx = lab "ceil_log2") := ⟨hcx⟩
    have hI : st.i.toNat ≤ x.p8.toNat := hP.1.2.2.2.2.2.2.2.1
    have hoff := rd_off st.i x.p8 x.L hI hC.2.2.2.2.1
    have hbl := T_buf_load hm _ 4 hoff
    obtain ⟨F, hg⟩ := T_gb hm
    have pli : PLift (s₀.dmem.loadInt (s₀.regs.get64 .rdx + 8#64) 4
        = some (Int.ofBytes (Int.toBytes 4 st.i.toInt))) := ⟨by rw [hdx]; exact gb_load_idx hg⟩
    have plp : PLift (s₀.dmem.loadInt (s₀.regs.get64 .rdx + 16#64) 4
        = some (Int.ofBytes (Int.toBytes 4 x.p8.toInt))) := ⟨by rw [hdx]; exact gb_load_p8 hg⟩
    have plb : PLift (s₀.dmem.loadInt (s₀.regs.get64 .rdx) 8
        = some (Int.ofBytes (Int.toBytes 8 x.buf.toInt))) := ⟨by rw [hdx]; exact gb_load_buf hg⟩
    have hst := T_storeI hm
    have hmT : Hide _ := hm
    have pRB : PLift (RB t₀ s₀) := ⟨hRB⟩
    clear hm hRB hg
    vcgen [bswap32_havoc, shl_cl32_havoc, shr_cl32_havoc]
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [AddrIndex.offset64_scale1, AddrIndex.offset64_none, Reg64s.get64_set64,
      Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, reduceCtorEq,
      ↓reduceIte, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
      BitVec.ushiftRight_eq] at *
    all_goals have li := pli.down
    all_goals have lp := plp.down
    all_goals have lb := plb.down
    all_goals try simp only [li, lp, lb, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt64_ofBytes_toBytes8,
      BitVec.ofInt_toInt, BitVec.setWidth_32_64_32] at *
    · rw [pax.down, pcx.down]
      refine Blocks.loadInt_isSome hB (Or.inr (Or.inl ?_))
      rw [BitVec.add_sub_cancel, BitVec.toNat_setWidth]; omega
    · exact hbl
    · obtain ⟨hsp, hbp, h13, hbx⟩ := pRB.down
      rw [hdx]
      refine ⟨⟨hC, ?_, rfl, hdi, _, shA_frPre_withI hP (gb_clamp _ _ _ _), hst _⟩,
        Nat.le_refl _⟩
      simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      exact ⟨hsp, hbp, h13, hbx⟩

end Kraken.Examples.Sbr.Grid
