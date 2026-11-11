import Kraken.X64.Examples.Sbr.Parse.GridShD2

/-!
# `read_sbr_grid`: the tail (shard D, part 3)

The index of `t_q[1]` for `bs_num_noise = 2`, by frame class and `bs_pointer`.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Grid

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

/-- `incl %r` (the rule `IntMisc.lean` has for `dec`, with `a + 1`). -/
theorem shD_inc_reg_w32_spec {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}
    {p : Program} (asz : Width) (r : Reg64) :
    ⦃ fun s =>
        let a := (s.regs.get64 r).setWidth 32
        let v := a + 1
        WP.wp p Q E
          { s with
              regs := s.regs.set64 r ((v).setWidth 64),
              status := StatusFlags.from_result v
                  { cf := s.status.cf,
                    af := (v.take 4).unsigned != (a.take 4).unsigned + 1,
                    of := v.signed != a.signed + 1 } } ⦄
      (Directive.instr (.regular asz .W32 (.inc (.reg (.low r .W32)))) :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by
    simp only [Directive.interp, Instr.interp,
      Operation.interp, RegOrMem.interp,
      
      MachineData.set, MachineData.setReg, 
      
      Effects.All]
    (try simp only [Reg64s.get_low32, Reg64s.set_low32
      ])
    exact hP)

/-- The dispatch on `bs_frame_class` and `bs_pointer`. -/
theorem blk_L4f27 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4f27" := by
  cfg_block
  measure_hb "L4f27"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hRB, st, ⟨hQ, hTR⟩, hm⟩, hn⟩ := hs₀
    have pTR : PLift (TR s₀ st) := ⟨hTR⟩
    have pRB : PLift (RB t₀ s₀) := ⟨hRB⟩
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat,
      BitVec.reduceSetWidth, shD_nz_sub, shD_z_test, BitVec.and_self, beq_iff_eq,
      Bool.not_eq_true', Bool.not_eq_false', beq_eq_false_iff_ne, ne_eq] at *
    all_goals try (left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar])
    · exact ⟨by decide, ⟨hC, pRB.down, st, ⟨hQ, pTR.down⟩, hmT⟩, by edge_lt⟩
    · exact ⟨by decide, ⟨hC, pRB.down, st, ⟨hQ, pTR.down⟩, hmT⟩, by edge_lt⟩
    · exact ⟨by decide, ⟨hC, pRB.down, st, hQ, hmT⟩, by edge_lt⟩
    · have key : ∀ a : BitVec 32, ¬ a = 0#32 → ¬ a = 1#32 → 2 ≤ a.toNat := by
        intro a h0 h1; bv_omega
      exact ⟨by decide, ⟨hC, pRB.down, st, ⟨hQ, pTR.down.2.2,
        key _ (by assumption) (by assumption)⟩, hmT⟩, by edge_lt⟩
    · refine ⟨by decide, ⟨hC, ?_, st, ⟨hQ, ?_⟩, hmT⟩, by edge_lt⟩
      · obtain ⟨a, b, c, d⟩ := pRB.down
        refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] <;>
          assumption
      · simp only [Reg64s.get64_set64, ↓reduceIte, pTR.down.1, shD_sw32_64]
        have := hQ.2.2.2
        bv_omega

theorem blk_L5094 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L5094" := by
  cfg_block
  measure_hb "L5094"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hRB, st, hQ, hm⟩, hn⟩ := hs₀
    have pRB : PLift (RB t₀ s₀) := ⟨hRB⟩
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceEqDiff, ↓reduceIte
      ] at *
    left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
    refine ⟨by decide, ⟨hC, ?_, st, ⟨hQ.1, ?_⟩, hmT⟩, by edge_lt⟩
    · obtain ⟨a, b, c, d⟩ := pRB.down
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] <;>
        assumption
    · simp only [Reg64s.get64_set64, ↓reduceIte, hQ.2.1, shD_sw32_64]
      rw [BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega

theorem blk_L509b (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L509b" := by
  cfg_block
  measure_hb "L509b"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hRB, st, hQ, hm⟩, hn⟩ := hs₀
    have pRB : PLift (RB t₀ s₀) := ⟨hRB⟩
    have hmT : Hide _ := hm
    clear hm
    vcgen [shD_inc_reg_w32_spec]
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat,
      BitVec.reduceSetWidth, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, 
      shD_ae_sub] at *
    left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
    refine ⟨by decide, ⟨hC, ?_, st, ⟨hQ.1, ?_⟩, hmT⟩, by edge_lt⟩
    · obtain ⟨a, b, c, d⟩ := pRB.down
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] <;>
        assumption
    · simp only [Reg64s.get64_set64, ↓reduceIte, hQ.2.1, shD_sw32_64]
      have hr := hQ.2.2.2
      have h2 := hQ.1.2.2.2
      have h8 : st.n.toNat ≤ 8 := hQ.1.1.1.2.2.2.2.1
      split
      · rename_i h
        simp only [decide_eq_true_eq] at h
        bv_omega
      · bv_omega

theorem blk_L50bc (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L50bc" := by
  cfg_block
  measure_hb "L50bc"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hRB, st, hQ, hm⟩, hn⟩ := hs₀
    have pRB : PLift (RB t₀ s₀) := ⟨hRB⟩
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat,
      BitVec.reduceSetWidth, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, 
      shD_c_sub] at *
    · left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
      exact ⟨by decide, ⟨hC, pRB.down, st, hQ, hmT⟩, by edge_lt⟩
    · have := hQ.1.1.1.2.2.2.2.1
      simp only [GSt.dv] at this
      simp only [decide_eq_false_iff_not] at *
      omega

/-- `t_q[1]` index `1` (`bs_pointer = 0`). -/
theorem blk_L50ae (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L50ae" := by
  cfg_block
  measure_hb "L50ae"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hRB, st, hQ, hm⟩, hn⟩ := hs₀
    have pRB : PLift (RB t₀ s₀) := ⟨hRB⟩
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat] at *
    left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
    refine ⟨by decide, ⟨hC, ?_, st, ⟨hQ, ?_⟩, hmT⟩, by edge_lt⟩
    · obtain ⟨a, b, c, d⟩ := pRB.down
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] <;>
        assumption
    · simp only [Reg64s.get64_set64, ↓reduceIte]
      have := hQ.2.2.2
      bv_omega
/-- `t_q[1]` index `bs_pointer - 1`. -/
theorem blk_L50b8 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L50b8" := by
  cfg_block
  measure_hb "L50b8"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hRB, st, hQ, hm⟩, hn⟩ := hs₀
    have pRB : PLift (RB t₀ s₀) := ⟨hRB⟩
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat] at *
    refine ⟨⟨hC, ?_, st, ⟨hQ.1, ?_⟩, hmT⟩, Nat.le_refl _⟩
    · obtain ⟨a, b, c, d⟩ := pRB.down
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] <;>
        assumption
    · have := hQ.2.1
      have := hQ.2.2
      try simp only [Reg64s.get64_set64, ↓reduceIte]
      simp only [AddrIndex.offset64_none, shD_sw32_64]
      have e : (-1 : Int64).toBitVec = 0xffffffffffffffff#64 := by decide
      rw [e]
      bv_omega

end Kraken.Examples.Sbr.Grid
