import Kraken.X64.Examples.Sbr.Parse.EnvBlk4

/-!
# `read_sbr_envelope`: the per-envelope loop head
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Vlc
open Kraken.Examples.Sbr.Parse (Hide eq_r eq_l eq_h)

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Env

variable [CodeEnv]

/-- Loop head: test `bs_df_env[i]`, spill `i`. -/
theorem blk_L58fd (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L58fd" := by
  cfg_block
  measure_hb "L58fd"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, gi, i, ⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hFC, hLI, h9, h15, h13, h12⟩, hn⟩ := hs₀
    have hi8 : i ≤ 8 := by have := hC.1.2.2.2.2.1; have := hLI.1; omega
    have hdf := T_ld_df hm i hi8
    have hld := T_ld_f68 hm
    have hst := T_st_f68 hm
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [hbp, h9, h15, AddrIndex.offset64_scale1] at ⊢
    · exact hdf
    · simp only [hld, Option.isSome_some]
    · left
      apply Table.ofLabels_at
      refine ⟨by decide, ?_⟩
      refine ⟨⟨{ fv with f68 := BitVec.ofNat 64 i }, gi, i, ⟨⟨⟨hC, hsp, hbp, hgi, hst _⟩, hdx⟩,
        hFC, hLI, rfl, h13⟩, h12, h9, h15⟩, ?_⟩
      refine Or.inr ⟨?_, by decide⟩
      rw [var_L5a60, var_L58fd, fi_eq' _ _ _ _ hbp (hst _), h9]
      all_goals simp only [BitVec.toNat_ofNat]
      all_goals omega
    · refine ⟨⟨{ fv with f68 := BitVec.ofNat 64 i }, gi, i, ⟨⟨⟨hC, hsp, hbp, hgi, hst _⟩, hdx⟩,
        hFC, hLI, rfl, h13⟩, h12, h9, h15⟩, ?_⟩
      show var "read_sbr_envelope.L590d" _ ≤ var "read_sbr_envelope.L58fd" _
      rw [var_L590d, var_L58fd, fi_eq' _ _ _ _ hbp (hst _), h9]
      all_goals simp only [BitVec.toNat_ofNat]
      all_goals omega

end Kraken.Examples.Sbr.Env
