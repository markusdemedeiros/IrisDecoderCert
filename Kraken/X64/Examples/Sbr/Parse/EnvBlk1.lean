import Kraken.X64.Examples.Sbr.Parse.EnvMem

/-!
# `read_sbr_envelope`: the setup blocks

The table pointers (`t_huff`, `f_huff` from `ff_aac_sbr_vlc`), the frame slots, and the head of
the envelope loop.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Vlc
open Kraken.Examples.Sbr.Parse (Hide)

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Env

variable [CodeEnv]

omit [CodeEnv] in
theorem bv_add_zero' (a : BitVec 64) : a + 0 = a := BitVec.add_zero a

/-- Register reads over register writes. -/
syntax "rsimp" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| rsimp) => `(tactic| simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte,
      AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2,
      AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.add_zero, bv_add_zero'])
  | `(tactic| rsimp $loc:location) =>
    `(tactic| simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte,
      AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2,
      AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.add_zero, bv_add_zero']
      $loc:location)

omit [CodeEnv] in
/-- `n & 1` as the code computes it (`and r14d, 1` after a 32-bit load). -/
theorem odd_bit (n : Nat) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.ofNat 32 n))
      &&& BitVec.setWidth 32 (Int64.toBitVec 1)) = BitVec.ofNat 64 (n % 2) := by
  rw [show BitVec.setWidth 32 (Int64.toBitVec 1) = 1#32 from rfl]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.reducePow,
    Nat.reduceMod, Nat.and_one_is_mod]
  omega

theorem blk_L57c1 (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L57c1" := by
  cfg_block
  measure_hb "L57c1"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, ⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hdi, hsi, hcx, h8⟩, hn⟩ := hs₀
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    · rename_i hz
      rw [z_and_iff] at hz
      left
      apply Table.ofLabels_at
      refine ⟨by decide, ⟨fv, ⟨⟨hC, ?_, ?_, hgi, hm⟩, ?_⟩, ?_, ?_, ?_, ?_⟩, Or.inr ⟨?_, by decide⟩⟩
      all_goals try rsimp
      all_goals try rsimp at hz
      all_goals first | assumption | (rw [h8] at hz; exact hz) | rfl
    · rename_i hz
      rsimp at hz
      rw [h8] at hz
      refine ⟨⟨fv, ⟨⟨hC, ?_, ?_, hgi, hm⟩, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_⟩
      all_goals try rsimp
      · exact hsp
      · exact hbp
      · exact hdx
      · exact hdi
      · exact hsi
      · exact hcx
      · intro h0
        change BitVec.setWidth 32 (t₀.regs.get64 .r8) = 0#32 at h0
        rw [(z_and_iff _ _).2 h0] at hz; exact absurd hz (by decide)
      · rw [var_L57c9, var_L57c1]; exact Nat.le_refl _

theorem blk_L5834 (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L5834" := by
  cfg_block
  measure_hb "L5834"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, ⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hdi, hsi, h15, h8⟩, hn⟩ := hs₀
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    · rsimp
      rw [hsi, show Int64.toBitVec 311780 = 0x4c1e4#64 from rfl, T_ld_n1 hm]; rfl
    · rename_i v hv _
      rsimp at hv
      rw [hsi, show Int64.toBitVec 311780 = 0x4c1e4#64 from rfl, T_ld_n1 hm] at hv
      cases hv
      refine ⟨⟨fv, ⟨⟨hC, ?_, ?_, hgi, hm⟩, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      all_goals try rsimp
      · exact hsp
      · exact hbp
      · exact hdx
      · exact hdi
      · exact hsi
      · exact h15
      · exact fun h => h.1 h8
      · show (_ : BitVec 64) = _; rsimp; rw [hsi]; rfl
      · rw [c4_val]; exact odd_bit x.n1
      · rw [var_L584c, var_L5834]; exact Nat.le_refl _

end Kraken.Examples.Sbr.Env
