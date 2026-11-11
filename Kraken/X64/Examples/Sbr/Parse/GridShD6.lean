import Kraken.X64.Examples.Sbr.Parse.GridShD5

/-!
# `read_sbr_grid`: the tail (shard D, part 6)

The last border-chain step `t_env[7] < t_env[8]` (`L5058`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Grid

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

/-- `t_env[7] < t_env[8]`; `bs_num_env == 8` ends the chain (`bs_num_env ≤ 8`, so the `ud1`
fallthrough is dead). -/
theorem blk_L5058 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L5058" := by
  cfg_block
  measure_hb "L5058"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h13, hbx⟩, st, ⟨hS, hj, hM, hTR, hdx, hr⟩, hm⟩, hdi⟩, hn⟩ := hs₀
    have hn8 : st.n.toNat ≤ 8 := hS.1.2.2.2.2.1
    have hb19 := hS.2.1
    have ld := T_loadTe hm 8 (by omega)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at ld
    have ld' : (s₀.dmem.loadInt (arg3 t₀ + 88740#64) 1).isSome = true := by rw [ld]; rfl
    have pTR : PLift (TR s₀ st) := ⟨hTR⟩
    have pbx : PLift (s₀.regs.get64 .rbx = arg3 t₀) := ⟨hbx⟩
    have pdi : PLift (s₀.regs.get64 .rdi = arg0 t₀) := ⟨hdi⟩
    have pdx : PLift (s₀.regs.get64 .rdx = (bv st.te 0).setWidth 64) := ⟨hdx⟩
    have pr : PLift (s₀.regs.get64 .rsi = (bv st.te 7).setWidth 64) := ⟨hr⟩
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, hbx,
      AddrIndex.offset64_none, BitVec.add_zero] at *
    all_goals try with_reducible exact ld'
    all_goals try simp only [ld, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt8_ofBytes_toBytes1, BitVec.ofInt_toInt,
      pTR.down.2.1, pr.down, shD_sw8_64, shD_sw32_64, BitVec.reduceSetWidth, shD_ae_subw,
      shD_z_subE, decide_eq_true_eq, decide_eq_false_iff_not] at *
    · left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
      refine ⟨by decide, ⟨⟨hC, ?_, ?_, st, hS, hmT⟩, ?_⟩, by edge_lt⟩
      all_goals first | exact hsp | exact h13 | exact pdi.down
    · have hlt : ¬ (st.te.getD 8 0).toBitVec.toNat ≤ (st.te.getD 7 0).toBitVec.toNat := by
        assumption
      have hnv : st.n.toNat = 8 := by
        have : st.n + 1#32 - 9#32 = 0#32 := by assumption
        bv_omega
      have hM' : Mono st st.n.toNat := by rw [hnv]; exact shD_monoS (j := 7) hM hlt
      left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
      refine ⟨by decide, ⟨hC, ?_, st, ⟨hS, shD_live_of (by omega) hM' hb19, ⟨?_, ?_, ?_⟩, ?_⟩,
        hmT⟩, by edge_lt⟩
      all_goals first
        | exact ⟨hsp, hbp, h13, pbx.down⟩
        | exact pTR.down.1
        | exact pTR.down.2.1
        | exact pTR.down.2.2
        | exact pdx.down
        | exact pdi.down
    · exfalso
      have : ¬ st.n + 1#32 - 9#32 = 0#32 := by assumption
      apply this; bv_omega

end Kraken.Examples.Sbr.Grid
