import Kraken.X64.Examples.Sbr.Parse.GridShA5

/-!
# `read_sbr_grid`: FIXVAR (class 1) tail, `bs_pointer` and the `bs_freq_res` fill from the top
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Grid

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

/-- `cmp $0x6,%ecx; jae`: `bs_num_env ≤ 5`, not taken. -/
theorem blk_L486a (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L486a" := by
  cfg_block
  measure_hb "L486a"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hRB, hdx, hdi, st, ⟨hP, h5, hcx⟩, hm⟩, hn⟩ := hs₀
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, hcx] at *
    · exfalso
      have hf := ‹CondCode.nc.interp _ = true›
      have : st.n = 0#32 ∨ st.n = 1#32 ∨ st.n = 2#32 ∨ st.n = 3#32 ∨ st.n = 4#32 ∨ st.n = 5#32 := by
        bv_omega
      rcases this with h | h | h | h | h | h <;> simp only [h] at hf <;> revert hf <;> decide
    · exact ⟨⟨hC, hRB, hdx, hdi, st, ⟨hP, h5, rfl⟩, hmT⟩, Nat.le_refl _⟩

/-- `ceil_log2[bs_num_env]` (FIXVAR). -/
theorem blk_L4873 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4873" := by
  cfg_block
  measure_hb "L4873"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hRB, hdx, hdi, st, ⟨hP, h5, hcx⟩, hm⟩, hn⟩ := hs₀
    obtain ⟨F, hB⟩ := T_blocks hm
    have hmT : Hide _ := hm
    have pRB : PLift (RB t₀ s₀) := ⟨hRB⟩
    clear hm hRB
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    · simp only [AddrIndex.offset64_scale1, Reg64s.get64_set64, Int64.toBitVec_ofNat_norm,
        BitVec.add_zero, hcx, BitVec.setWidth_32_64_32, ↓reduceIte]
      refine Blocks.loadInt_isSome hB (Or.inr (Or.inl ?_))
      rw [BitVec.add_sub_cancel, BitVec.toNat_setWidth]; omega
    · obtain ⟨hsp, hbp, h13, hbx⟩ := pRB.down
      refine ⟨⟨hC, ?_, hdx, hdi, st, ⟨hP, h5⟩, hmT⟩, Nat.le_refl _⟩
      simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      exact ⟨hsp, hbp, h13, hbx⟩

/-- `get_bits(gb, ceil_log2[n])` (the VARFIX pointer bits; the count `eax` is havocked). -/
theorem blk_L4880 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4880" := by
  cfg_block
  measure_hb "L4880"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hRB, hdx, hdi, st, ⟨hP, h5⟩, hm⟩, hn⟩ := hs₀
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
      ↓reduceIte, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, get64_ite, ite_self,
      BitVec.ushiftRight_eq] at *
    all_goals have li := pli.down
    all_goals have lp := plp.down
    all_goals have lb := plb.down
    all_goals try simp only [li, lp, lb, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt64_ofBytes_toBytes8,
      BitVec.ofInt_toInt, BitVec.setWidth_32_64_32] at *
    · exact hbl
    · obtain ⟨hsp, hbp, h13, hbx⟩ := pRB.down
      rw [hdx]
      refine ⟨⟨hC, ?_, rfl, hdi, _, shA_frPre_withI hP (gb_clamp _ _ _ _), hst _⟩,
        Nat.le_refl _⟩
      simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      exact ⟨hsp, hbp, h13, hbx⟩

/-- `cmpl $0x0,0x8(%rbx); je L4ea2` (not taken: `1 ≤ n`), `eax = esi = 0`. -/
theorem blk_L48b3 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L48b3" := by
  cfg_block
  measure_hb "L48b3"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hRB, hdx, hdi, st, hP, hm⟩, hn⟩ := hs₀
    have hrbx : s₀.regs.get64 .rbx = arg3 t₀ := hRB.2.2.2
    have hld := T_loadN hm
    have hmT : Hide _ := hm
    have pRB : PLift (RB t₀ s₀) := ⟨hRB⟩
    clear hm hRB
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbx] at *
    all_goals try simp only [hld, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt_toInt,
      BitVec.setWidth_32_64_32] at *
    · exfalso
      have hf := ‹CondCode.z.interp _ = true›
      have h1 := hP.2.1
      have h8 := hP.1.2.2.2.1
      have : st.n = 1#32 ∨ st.n = 2#32 ∨ st.n = 3#32 ∨ st.n = 4#32 ∨ st.n = 5#32 ∨ st.n = 6#32
          ∨ st.n = 7#32 ∨ st.n = 8#32 := by bv_omega
      rcases this with h | h | h | h | h | h | h | h <;> simp only [h] at hf <;> revert hf <;> decide
    · obtain ⟨hsp, hbp, h13, hbx⟩ := pRB.down
      simp only [BitVec.xor_self]
      refine ⟨⟨hC, ?_, hdx, hdi, st, ⟨hP, 0, hP.2.1, rfl, rfl, ?_, trivial⟩, hmT⟩, ?_⟩
      · simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        exact ⟨hsp, hbp, h13, hbx⟩
      · intro e h1 h2; omega
      · simp only [BitVec.toNat_zero, Nat.add_eq]; omega

end Kraken.Examples.Sbr.Grid
