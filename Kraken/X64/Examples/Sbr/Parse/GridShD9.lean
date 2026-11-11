import Kraken.X64.Examples.Sbr.Parse.GridShD8

/-!
# `read_sbr_grid`: VARVAR `bs_num_env < 6`, `get_bits(ceil_log2)`, the cases on `bs_num_env`
(shard D, part 9)

The same code as VARFIX's `L45bf` … `L460b` (shard A), at the VARVAR addresses.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Grid

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

/-- `cmp $0x6,%ecx; jae`: the check `bs_num_env < 6` (passes, `bs_num_env ≤ 5`). -/
theorem blk_L4c4a (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4c4a" := by
  cfg_block
  measure_hb "L4c4a"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hRB, hdx, hdi, st, ⟨hP, h5, hcx⟩, hm⟩, hn⟩ := hs₀
    have hmT : Hide _ := hm
    have pRB : PLift (RB t₀ s₀) := ⟨hRB⟩
    have pcx : PLift ((s₀.regs.get64 .rcx).setWidth 32 = st.n) := ⟨hcx⟩
    clear hm hRB
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, pcx.down] at *
    · exfalso
      have hf := ‹CondCode.nc.interp _ = true›
      have h1 : 1 ≤ st.n.toNat := hP.2.1
      have : st.n = 1#32 ∨ st.n = 2#32 ∨ st.n = 3#32 ∨ st.n = 4#32 ∨ st.n = 5#32 := by bv_omega
      rcases this with h | h | h | h | h <;> simp only [h] at hf <;> revert hf <;> decide
    · exact ⟨⟨hC, pRB.down, hdx, hdi, st, ⟨hP, h5, rfl⟩, hmT⟩, Nat.le_refl _⟩

/-- `mov %ecx,%eax; lea ceil_log2(%rip),%rcx`. -/
theorem blk_L4c53 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4c53" := by
  cfg_block
  measure_hb "L4c53"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hRB, hdx, hdi, st, ⟨hP, h5, hcx⟩, hm⟩, hn⟩ := hs₀
    have hmT : Hide _ := hm
    have pRB : PLift (RB t₀ s₀) := ⟨hRB⟩
    have pcx : PLift ((s₀.regs.get64 .rcx).setWidth 32 = st.n) := ⟨hcx⟩
    clear hm hRB
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [pcx.down] at *
    obtain ⟨hsp, hbp, h13, hbx⟩ := pRB.down
    refine ⟨⟨hC, ?_, hdx, hdi, st, ⟨hP, h5, rfl, trivial⟩, hmT⟩, Nat.le_refl _⟩
    simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    exact ⟨hsp, hbp, h13, hbx⟩

/-- `cmp $0x1,%esi` after `movslq 0x8(%rbx),%rsi`: `n = 1` (falls to `L4ca9`) or `n ≥ 2`. -/
theorem blk_L4c93 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4c93" := by
  cfg_block
  measure_hb "L4c93"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hRB, hdx, hdi, st, hP, hm⟩, hn⟩ := hs₀
    have hld := T_loadN hm
    have hrbx : s₀.regs.get64 .rbx = arg3 t₀ := hRB.2.2.2
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
    all_goals have hRB := pRB.down
    all_goals try simp only [hld, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt_toInt] at *
    all_goals have hn8 : st.n.toNat ≤ 8 := hP.1.2.2.2.1
    all_goals have h1 : 1 ≤ st.n.toNat := hP.2.1
    all_goals simp only [shA_sext _ hn8] at *
    · exfalso
      have hle := ‹CondCode.le.interp _ = true›
      rw [shA_le_pos _ h1 hn8] at hle; exact absurd hle (by decide)
    · have hz := ‹CondCode.nz.interp _ = true›
      rw [shA_nz] at hz
      have hz' : st.n.toNat ≠ 1 := by
        intro h; apply hz; simp only [BitVec.setWidth_32_64_32]; bv_omega
      obtain ⟨hsp, hbp, h13, hbx⟩ := hRB
      left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
      refine ⟨by decide, ⟨hC, ?_, ?_, ?_, st, ⟨hP, by omega, ?_⟩, hmT⟩, by edge_lt⟩
      all_goals try simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      all_goals first | exact ⟨hsp, hbp, h13, hbx⟩ | exact hdx | exact hdi
    · have hz := ‹CondCode.nz.interp _ = false›
      rw [shA_nz_f] at hz
      simp only [BitVec.setWidth_32_64_32] at hz
      obtain ⟨hsp, hbp, h13, hbx⟩ := hRB
      refine ⟨⟨hC, ?_, ?_, ?_, st, ⟨hP, by bv_omega⟩, hmT⟩, by decide⟩
      all_goals try simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      all_goals first | exact ⟨hsp, hbp, h13, hbx⟩ | exact hdx | exact hdi

end Kraken.Examples.Sbr.Grid
