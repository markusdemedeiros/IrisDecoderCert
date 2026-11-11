import Kraken.X64.Examples.Sbr.Parse.EnvBlk1

/-!
# `read_sbr_envelope`: the table selection
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Vlc
open Kraken.Examples.Sbr.Parse (Hide)

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Env

theorem sw32_64 (v : BitVec 32) : (v.setWidth 64).setWidth 32 = v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  have := v.isLt
  omega

variable [CodeEnv]

theorem blk_L57c9 (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L57c9" := by
  cfg_block
  measure_hb "L57c9"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, ⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hdi, hsi, h15, h8⟩, hn⟩ := hs₀
    vcgen [inc32_havoc]
    all_goals try dsimp only at *
    all_goals try subst_vars
    · rw [hsi, show Int64.toBitVec 60 = 0x3c#64 from rfl, T_ld_cpl hm]; rfl
    · rsimp
      rw [hsi, show Int64.toBitVec 311780 = 0x4c1e4#64 from rfl, T_ld_n1 hm]; rfl
    all_goals
      rename_i c hc af r11 st v hv b1 b2 hz
      rw [hsi, show Int64.toBitVec 60 = 0x3c#64 from rfl, T_ld_cpl hm] at hc
      cases hc
      rsimp at hv
      rw [hsi, show Int64.toBitVec 311780 = 0x4c1e4#64 from rfl, T_ld_n1 hm] at hv
      cases hv
      rsimp at hz
      rw [cell4_val, sw32_64] at hz
    · rw [z_and_iff] at hz
      left
      apply Table.ofLabels_at
      refine ⟨by decide, ⟨fv, ⟨⟨hC, ?_, ?_, hgi, hm⟩, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩,
        Or.inr ⟨?_, by decide⟩⟩
      all_goals try rsimp
      · exact hsp
      · exact hbp
      · exact hdx
      · exact hdi
      · exact hsi
      · exact h15
      · exact fun h => h.2 hz
      · show (_ : BitVec 64) = _; rsimp; rw [hsi]; rfl
      · rw [c4_val]; exact odd_bit x.n1
      · rw [var_L584c, var_L57c9]
    · have hz' : x.coupling ≠ 0#32 := fun h0 => by
        rw [(z_and_iff _ _).2 h0] at hz; exact absurd hz (by decide)
      refine ⟨⟨fv, ⟨⟨hC, ?_, ?_, hgi, hm⟩, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      all_goals try rsimp
      · exact hsp
      · exact hbp
      · exact hdx
      · exact hdi
      · exact hsi
      · exact h15
      · exact ⟨h8, hz'⟩
      · show (_ : BitVec 64) = _; rsimp; rw [hsi]; rfl
      · rw [c4_val]; exact odd_bit x.n1
      · rw [var_L57ef, var_L57c9]; exact Nat.le_refl _

end Kraken.Examples.Sbr.Env
