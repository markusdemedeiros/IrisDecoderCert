import Kraken.X64.Examples.Sbr.Parse.ResetNoiseLib

/-!
# `sbr_reset`: the unrolled `goal_sb` search of `sbr_hf_calc_npatches` (shard B, noise)

Blocks `L2cc2` … `L30c9`, entries `AtSrch j` (`spec/BS.py`): each block compares `goal_sb` with
`f_master[j]`, `f_master[j+1]`, `f_master[j+2]` and leaves for gB's `L30df` with `k` at the first
entry `≥ goal_sb` (`rsN_exit`), else goes on (`rsN_next`). `L30c9` (`f_master[48]`) cannot reach
the trap `L32dc` (`rsN_end`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Reset

variable [CodeEnv]

theorem rsN_of {j k : Nat} {e : REnv} {a : RArgs} {ra : Int64} {t₀ s : MachineData}
    (h : AtSrch j k e a ra t₀ s) : ∃ st fr c, SQ j k e a ra t₀ s st fr c :=
  let ⟨h1, h2, st, fr, c, h⟩ := h
  ⟨st, fr, c, h1, h2, h⟩

set_option maxRecDepth 100000 in
/-- `goal_sb` against `f_master[0]` … `f_master[2]`. -/
theorem blk_L2cc2 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2cc2" ⟨"sbr_reset.L2cc2", B.L2cc2, some "sbr_reset.L2d03"⟩ := by
  info_off
  measure_hb "L2cc2"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨st, fr, c, hQ⟩ := rsN_of (T.L2cc2.mp hs)
    clear hs
    obtain ⟨F0, e0, b0, ld0⟩ := rsN_ldF hQ (i := 0) (by omega)
    obtain ⟨F1, e1, b1, ld1⟩ := rsN_ldF hQ (i := 1) (by omega)
    obtain ⟨F2, e2, b2, ld2⟩ := rsN_ldF hQ (i := 2) (by omega)
    obtain ⟨h12, hax⟩ := rsN_regs hQ
    obtain ⟨g0, g1, -⟩ := rsN_num hQ
    have gt : (goalSb a.x.sampleRate.toInt).toNat < 2 ^ 16 := by omega
    simp only [arg1, Nat.reduceMul, Nat.reduceAdd] at ld0 ld1 ld2 h12
    have PQ := PLift.up hQ
    have PL := PLift.up (And.intro ld0 (And.intro ld1 ld2))
    have PE := PLift.up (And.intro e0 (And.intro e1 e2))
    have PR := PLift.up (And.intro h12 hax)
    have z0 : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    clear hQ ld0 ld1 ld2 e0 e1 e2 h12 hax
    simp only [B.L2cc2]
    vcgen
    all_goals try subst_vars
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
      Int64.toBitVec_ofNat_norm, Option.isSome_some, PR.down.1, PR.down.2, z0, BitVec.add_zero, PL.down.1, PL.down.2.1, PL.down.2.2,
      Option.some.injEq, cc_be_sub, cc_a_sub, decide_eq_true_eq, decide_eq_false_iff_not] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt_natCast, rsN_sw _ b0, rsN_sw _ b1, rsN_sw _ b2, rsN_sg _ (by omega : (goalSb a.x.sampleRate.toInt).toNat < 2 ^ 32),
      rsN_cc_le _ _ gt b0, decide_eq_true_eq, decide_eq_false_iff_not] at *
    all_goals try simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at *
    · left; apply Table.ofLabels_at
      refine ⟨by decide, T.L30df.mpr (rsN_exit PQ.down _ rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 0
        (by simp)
        (fun i h1 h2 => absurd h2 (by omega))
        ⟨F0, PE.down.1, by omega⟩), ?_⟩
      edge_step
    · left; apply Table.ofLabels_at
      refine ⟨by decide, T.L30df.mpr (rsN_exit PQ.down _ rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 1
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; rfl)
        (by
          intro i h1 h2
          have : i = 0 := by omega
          subst this; exact ⟨F0, PE.down.1, by omega⟩)
        ⟨F1, PE.down.2.1, by omega⟩), ?_⟩
      edge_step
    · left; apply Table.ofLabels_at
      refine ⟨by decide, T.L30df.mpr (rsN_exit PQ.down _ rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 2
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; rfl)
        (by
          intro i h1 h2
          rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
          · exact ⟨F0, PE.down.1, by omega⟩
          · exact ⟨F1, PE.down.2.1, by omega⟩)
        ⟨F2, PE.down.2.2, by omega⟩), ?_⟩
      edge_step
    · refine ⟨T.L2d03.mpr ?_, ?_⟩
      · simp only [E.L2d03, AtSrch]
        refine rsN_next PQ.down _ ?_ (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 3 ?_
        · rfl
        exact
          (by
          intro i h1 h2
          rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
          · exact ⟨F0, PE.down.1, by omega⟩
          · exact ⟨F1, PE.down.2.1, by omega⟩
          · exact ⟨F2, PE.down.2.2, by omega⟩)
      · var_step

set_option maxRecDepth 100000 in
/-- `goal_sb` against `f_master[3]` … `f_master[5]`. -/
theorem blk_L2d03 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2d03" ⟨"sbr_reset.L2d03", B.L2d03, some "sbr_reset.L2d45"⟩ := by
  info_off
  measure_hb "L2d03"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨st, fr, c, hQ⟩ := rsN_of (T.L2d03.mp hs)
    clear hs
    obtain ⟨F0, e0, b0, ld0⟩ := rsN_ldF hQ (i := 3) (by omega)
    obtain ⟨F1, e1, b1, ld1⟩ := rsN_ldF hQ (i := 4) (by omega)
    obtain ⟨F2, e2, b2, ld2⟩ := rsN_ldF hQ (i := 5) (by omega)
    obtain ⟨h12, hax⟩ := rsN_regs hQ
    obtain ⟨g0, g1, -⟩ := rsN_num hQ
    have gt : (goalSb a.x.sampleRate.toInt).toNat < 2 ^ 16 := by omega
    simp only [arg1, Nat.reduceMul, Nat.reduceAdd] at ld0 ld1 ld2 h12
    have PQ := PLift.up hQ
    have PL := PLift.up (And.intro ld0 (And.intro ld1 ld2))
    have PE := PLift.up (And.intro e0 (And.intro e1 e2))
    have PR := PLift.up (And.intro h12 hax)
    have z0 : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    clear hQ ld0 ld1 ld2 e0 e1 e2 h12 hax
    simp only [B.L2d03]
    vcgen
    all_goals try subst_vars
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
      Int64.toBitVec_ofNat_norm, Option.isSome_some, PR.down.1, PR.down.2, z0, BitVec.add_zero, PL.down.1, PL.down.2.1, PL.down.2.2,
      Option.some.injEq, cc_be_sub, cc_a_sub, decide_eq_true_eq, decide_eq_false_iff_not] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt_natCast, rsN_sw _ b0, rsN_sw _ b1, rsN_sw _ b2, rsN_sg _ (by omega : (goalSb a.x.sampleRate.toInt).toNat < 2 ^ 32),
      rsN_cc_le _ _ gt b0, decide_eq_true_eq, decide_eq_false_iff_not] at *
    all_goals try simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at *
    · left; apply Table.ofLabels_at
      refine ⟨by decide, T.L30df.mpr (rsN_exit PQ.down _ rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 3
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; rfl)
        (fun i h1 h2 => absurd h2 (by omega))
        ⟨F0, PE.down.1, by omega⟩), ?_⟩
      edge_step
    · left; apply Table.ofLabels_at
      refine ⟨by decide, T.L30df.mpr (rsN_exit PQ.down _ rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 4
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; rfl)
        (by
          intro i h1 h2
          have : i = 3 := by omega
          subst this; exact ⟨F0, PE.down.1, by omega⟩)
        ⟨F1, PE.down.2.1, by omega⟩), ?_⟩
      edge_step
    · left; apply Table.ofLabels_at
      refine ⟨by decide, T.L30df.mpr (rsN_exit PQ.down _ rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 5
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; rfl)
        (by
          intro i h1 h2
          rcases (show i = 3 ∨ i = 4 by omega) with rfl | rfl
          · exact ⟨F0, PE.down.1, by omega⟩
          · exact ⟨F1, PE.down.2.1, by omega⟩)
        ⟨F2, PE.down.2.2, by omega⟩), ?_⟩
      edge_step
    · refine ⟨T.L2d45.mpr ?_, ?_⟩
      · simp only [E.L2d45, AtSrch]
        refine rsN_next PQ.down _ ?_ (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 6 ?_
        · rfl
        exact
          (by
          intro i h1 h2
          rcases (show i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl
          · exact ⟨F0, PE.down.1, by omega⟩
          · exact ⟨F1, PE.down.2.1, by omega⟩
          · exact ⟨F2, PE.down.2.2, by omega⟩)
      · var_step

set_option maxRecDepth 100000 in
/-- `goal_sb` against `f_master[6]` … `f_master[8]`. -/
theorem blk_L2d45 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2d45" ⟨"sbr_reset.L2d45", B.L2d45, some "sbr_reset.L2d87"⟩ := by
  info_off
  measure_hb "L2d45"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨st, fr, c, hQ⟩ := rsN_of (T.L2d45.mp hs)
    clear hs
    obtain ⟨F0, e0, b0, ld0⟩ := rsN_ldF hQ (i := 6) (by omega)
    obtain ⟨F1, e1, b1, ld1⟩ := rsN_ldF hQ (i := 7) (by omega)
    obtain ⟨F2, e2, b2, ld2⟩ := rsN_ldF hQ (i := 8) (by omega)
    obtain ⟨h12, hax⟩ := rsN_regs hQ
    obtain ⟨g0, g1, -⟩ := rsN_num hQ
    have gt : (goalSb a.x.sampleRate.toInt).toNat < 2 ^ 16 := by omega
    simp only [arg1, Nat.reduceMul, Nat.reduceAdd] at ld0 ld1 ld2 h12
    have PQ := PLift.up hQ
    have PL := PLift.up (And.intro ld0 (And.intro ld1 ld2))
    have PE := PLift.up (And.intro e0 (And.intro e1 e2))
    have PR := PLift.up (And.intro h12 hax)
    have z0 : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    clear hQ ld0 ld1 ld2 e0 e1 e2 h12 hax
    simp only [B.L2d45]
    vcgen
    all_goals try subst_vars
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
      Int64.toBitVec_ofNat_norm, Option.isSome_some, PR.down.1, PR.down.2, z0, BitVec.add_zero, PL.down.1, PL.down.2.1, PL.down.2.2,
      Option.some.injEq, cc_be_sub, cc_a_sub, decide_eq_true_eq, decide_eq_false_iff_not] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt_natCast, rsN_sw _ b0, rsN_sw _ b1, rsN_sw _ b2, rsN_sg _ (by omega : (goalSb a.x.sampleRate.toInt).toNat < 2 ^ 32),
      rsN_cc_le _ _ gt b0, decide_eq_true_eq, decide_eq_false_iff_not] at *
    all_goals try simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at *
    · left; apply Table.ofLabels_at
      refine ⟨by decide, T.L30df.mpr (rsN_exit PQ.down _ rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 6
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; rfl)
        (fun i h1 h2 => absurd h2 (by omega))
        ⟨F0, PE.down.1, by omega⟩), ?_⟩
      edge_step
    · left; apply Table.ofLabels_at
      refine ⟨by decide, T.L30df.mpr (rsN_exit PQ.down _ rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 7
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; rfl)
        (by
          intro i h1 h2
          have : i = 6 := by omega
          subst this; exact ⟨F0, PE.down.1, by omega⟩)
        ⟨F1, PE.down.2.1, by omega⟩), ?_⟩
      edge_step
    · left; apply Table.ofLabels_at
      refine ⟨by decide, T.L30df.mpr (rsN_exit PQ.down _ rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 8
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; rfl)
        (by
          intro i h1 h2
          rcases (show i = 6 ∨ i = 7 by omega) with rfl | rfl
          · exact ⟨F0, PE.down.1, by omega⟩
          · exact ⟨F1, PE.down.2.1, by omega⟩)
        ⟨F2, PE.down.2.2, by omega⟩), ?_⟩
      edge_step
    · refine ⟨T.L2d87.mpr ?_, ?_⟩
      · simp only [E.L2d87, AtSrch]
        refine rsN_next PQ.down _ ?_ (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 9 ?_
        · rfl
        exact
          (by
          intro i h1 h2
          rcases (show i = 6 ∨ i = 7 ∨ i = 8 by omega) with rfl | rfl | rfl
          · exact ⟨F0, PE.down.1, by omega⟩
          · exact ⟨F1, PE.down.2.1, by omega⟩
          · exact ⟨F2, PE.down.2.2, by omega⟩)
      · var_step

set_option maxRecDepth 100000 in
/-- `goal_sb` against `f_master[9]` … `f_master[11]`. -/
theorem blk_L2d87 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2d87" ⟨"sbr_reset.L2d87", B.L2d87, some "sbr_reset.L2dc9"⟩ := by
  info_off
  measure_hb "L2d87"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨st, fr, c, hQ⟩ := rsN_of (T.L2d87.mp hs)
    clear hs
    obtain ⟨F0, e0, b0, ld0⟩ := rsN_ldF hQ (i := 9) (by omega)
    obtain ⟨F1, e1, b1, ld1⟩ := rsN_ldF hQ (i := 10) (by omega)
    obtain ⟨F2, e2, b2, ld2⟩ := rsN_ldF hQ (i := 11) (by omega)
    obtain ⟨h12, hax⟩ := rsN_regs hQ
    obtain ⟨g0, g1, -⟩ := rsN_num hQ
    have gt : (goalSb a.x.sampleRate.toInt).toNat < 2 ^ 16 := by omega
    simp only [arg1, Nat.reduceMul, Nat.reduceAdd] at ld0 ld1 ld2 h12
    have PQ := PLift.up hQ
    have PL := PLift.up (And.intro ld0 (And.intro ld1 ld2))
    have PE := PLift.up (And.intro e0 (And.intro e1 e2))
    have PR := PLift.up (And.intro h12 hax)
    have z0 : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    clear hQ ld0 ld1 ld2 e0 e1 e2 h12 hax
    simp only [B.L2d87]
    vcgen
    all_goals try subst_vars
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
      Int64.toBitVec_ofNat_norm, Option.isSome_some, PR.down.1, PR.down.2, z0, BitVec.add_zero, PL.down.1, PL.down.2.1, PL.down.2.2,
      Option.some.injEq, cc_be_sub, cc_a_sub, decide_eq_true_eq, decide_eq_false_iff_not] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt_natCast, rsN_sw _ b0, rsN_sw _ b1, rsN_sw _ b2, rsN_sg _ (by omega : (goalSb a.x.sampleRate.toInt).toNat < 2 ^ 32),
      rsN_cc_le _ _ gt b0, decide_eq_true_eq, decide_eq_false_iff_not] at *
    all_goals try simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at *
    · left; apply Table.ofLabels_at
      refine ⟨by decide, T.L30df.mpr (rsN_exit PQ.down _ rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 9
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; rfl)
        (fun i h1 h2 => absurd h2 (by omega))
        ⟨F0, PE.down.1, by omega⟩), ?_⟩
      edge_step
    · left; apply Table.ofLabels_at
      refine ⟨by decide, T.L30df.mpr (rsN_exit PQ.down _ rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 10
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; rfl)
        (by
          intro i h1 h2
          have : i = 9 := by omega
          subst this; exact ⟨F0, PE.down.1, by omega⟩)
        ⟨F1, PE.down.2.1, by omega⟩), ?_⟩
      edge_step
    · left; apply Table.ofLabels_at
      refine ⟨by decide, T.L30df.mpr (rsN_exit PQ.down _ rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 11
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; rfl)
        (by
          intro i h1 h2
          rcases (show i = 9 ∨ i = 10 by omega) with rfl | rfl
          · exact ⟨F0, PE.down.1, by omega⟩
          · exact ⟨F1, PE.down.2.1, by omega⟩)
        ⟨F2, PE.down.2.2, by omega⟩), ?_⟩
      edge_step
    · refine ⟨T.L2dc9.mpr ?_, ?_⟩
      · simp only [E.L2dc9, AtSrch]
        refine rsN_next PQ.down _ ?_ (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 12 ?_
        · rfl
        exact
          (by
          intro i h1 h2
          rcases (show i = 9 ∨ i = 10 ∨ i = 11 by omega) with rfl | rfl | rfl
          · exact ⟨F0, PE.down.1, by omega⟩
          · exact ⟨F1, PE.down.2.1, by omega⟩
          · exact ⟨F2, PE.down.2.2, by omega⟩)
      · var_step

set_option maxRecDepth 100000 in
/-- `goal_sb` against `f_master[12]` … `f_master[14]`. -/
theorem blk_L2dc9 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2dc9" ⟨"sbr_reset.L2dc9", B.L2dc9, some "sbr_reset.L2e0b"⟩ := by
  info_off
  measure_hb "L2dc9"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨st, fr, c, hQ⟩ := rsN_of (T.L2dc9.mp hs)
    clear hs
    obtain ⟨F0, e0, b0, ld0⟩ := rsN_ldF hQ (i := 12) (by omega)
    obtain ⟨F1, e1, b1, ld1⟩ := rsN_ldF hQ (i := 13) (by omega)
    obtain ⟨F2, e2, b2, ld2⟩ := rsN_ldF hQ (i := 14) (by omega)
    obtain ⟨h12, hax⟩ := rsN_regs hQ
    obtain ⟨g0, g1, -⟩ := rsN_num hQ
    have gt : (goalSb a.x.sampleRate.toInt).toNat < 2 ^ 16 := by omega
    simp only [arg1, Nat.reduceMul, Nat.reduceAdd] at ld0 ld1 ld2 h12
    have PQ := PLift.up hQ
    have PL := PLift.up (And.intro ld0 (And.intro ld1 ld2))
    have PE := PLift.up (And.intro e0 (And.intro e1 e2))
    have PR := PLift.up (And.intro h12 hax)
    have z0 : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    clear hQ ld0 ld1 ld2 e0 e1 e2 h12 hax
    simp only [B.L2dc9]
    vcgen
    all_goals try subst_vars
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
      Int64.toBitVec_ofNat_norm, Option.isSome_some, PR.down.1, PR.down.2, z0, BitVec.add_zero, PL.down.1, PL.down.2.1, PL.down.2.2,
      Option.some.injEq, cc_be_sub, cc_a_sub, decide_eq_true_eq, decide_eq_false_iff_not] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt_natCast, rsN_sw _ b0, rsN_sw _ b1, rsN_sw _ b2, rsN_sg _ (by omega : (goalSb a.x.sampleRate.toInt).toNat < 2 ^ 32),
      rsN_cc_le _ _ gt b0, decide_eq_true_eq, decide_eq_false_iff_not] at *
    all_goals try simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at *
    · left; apply Table.ofLabels_at
      refine ⟨by decide, T.L30df.mpr (rsN_exit PQ.down _ rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 12
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; rfl)
        (fun i h1 h2 => absurd h2 (by omega))
        ⟨F0, PE.down.1, by omega⟩), ?_⟩
      edge_step
    · left; apply Table.ofLabels_at
      refine ⟨by decide, T.L30df.mpr (rsN_exit PQ.down _ rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 13
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; rfl)
        (by
          intro i h1 h2
          have : i = 12 := by omega
          subst this; exact ⟨F0, PE.down.1, by omega⟩)
        ⟨F1, PE.down.2.1, by omega⟩), ?_⟩
      edge_step
    · left; apply Table.ofLabels_at
      refine ⟨by decide, T.L30df.mpr (rsN_exit PQ.down _ rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 14
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; rfl)
        (by
          intro i h1 h2
          rcases (show i = 12 ∨ i = 13 by omega) with rfl | rfl
          · exact ⟨F0, PE.down.1, by omega⟩
          · exact ⟨F1, PE.down.2.1, by omega⟩)
        ⟨F2, PE.down.2.2, by omega⟩), ?_⟩
      edge_step
    · refine ⟨T.L2e0b.mpr ?_, ?_⟩
      · simp only [E.L2e0b, AtSrch]
        refine rsN_next PQ.down _ ?_ (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 15 ?_
        · rfl
        exact
          (by
          intro i h1 h2
          rcases (show i = 12 ∨ i = 13 ∨ i = 14 by omega) with rfl | rfl | rfl
          · exact ⟨F0, PE.down.1, by omega⟩
          · exact ⟨F1, PE.down.2.1, by omega⟩
          · exact ⟨F2, PE.down.2.2, by omega⟩)
      · var_step

set_option maxRecDepth 100000 in
/-- `goal_sb` against `f_master[15]` … `f_master[17]`. -/
theorem blk_L2e0b (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2e0b" ⟨"sbr_reset.L2e0b", B.L2e0b, some "sbr_reset.L2e4d"⟩ := by
  info_off
  measure_hb "L2e0b"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨st, fr, c, hQ⟩ := rsN_of (T.L2e0b.mp hs)
    clear hs
    obtain ⟨F0, e0, b0, ld0⟩ := rsN_ldF hQ (i := 15) (by omega)
    obtain ⟨F1, e1, b1, ld1⟩ := rsN_ldF hQ (i := 16) (by omega)
    obtain ⟨F2, e2, b2, ld2⟩ := rsN_ldF hQ (i := 17) (by omega)
    obtain ⟨h12, hax⟩ := rsN_regs hQ
    obtain ⟨g0, g1, -⟩ := rsN_num hQ
    have gt : (goalSb a.x.sampleRate.toInt).toNat < 2 ^ 16 := by omega
    simp only [arg1, Nat.reduceMul, Nat.reduceAdd] at ld0 ld1 ld2 h12
    have PQ := PLift.up hQ
    have PL := PLift.up (And.intro ld0 (And.intro ld1 ld2))
    have PE := PLift.up (And.intro e0 (And.intro e1 e2))
    have PR := PLift.up (And.intro h12 hax)
    have z0 : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    clear hQ ld0 ld1 ld2 e0 e1 e2 h12 hax
    simp only [B.L2e0b]
    vcgen
    all_goals try subst_vars
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
      Int64.toBitVec_ofNat_norm, Option.isSome_some, PR.down.1, PR.down.2, z0, BitVec.add_zero, PL.down.1, PL.down.2.1, PL.down.2.2,
      Option.some.injEq, cc_be_sub, cc_a_sub, decide_eq_true_eq, decide_eq_false_iff_not] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt_natCast, rsN_sw _ b0, rsN_sw _ b1, rsN_sw _ b2, rsN_sg _ (by omega : (goalSb a.x.sampleRate.toInt).toNat < 2 ^ 32),
      rsN_cc_le _ _ gt b0, decide_eq_true_eq, decide_eq_false_iff_not] at *
    all_goals try simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at *
    · left; apply Table.ofLabels_at
      refine ⟨by decide, T.L30df.mpr (rsN_exit PQ.down _ rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 15
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; rfl)
        (fun i h1 h2 => absurd h2 (by omega))
        ⟨F0, PE.down.1, by omega⟩), ?_⟩
      edge_step
    · left; apply Table.ofLabels_at
      refine ⟨by decide, T.L30df.mpr (rsN_exit PQ.down _ rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 16
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; rfl)
        (by
          intro i h1 h2
          have : i = 15 := by omega
          subst this; exact ⟨F0, PE.down.1, by omega⟩)
        ⟨F1, PE.down.2.1, by omega⟩), ?_⟩
      edge_step
    · left; apply Table.ofLabels_at
      refine ⟨by decide, T.L30df.mpr (rsN_exit PQ.down _ rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 17
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; rfl)
        (by
          intro i h1 h2
          rcases (show i = 15 ∨ i = 16 by omega) with rfl | rfl
          · exact ⟨F0, PE.down.1, by omega⟩
          · exact ⟨F1, PE.down.2.1, by omega⟩)
        ⟨F2, PE.down.2.2, by omega⟩), ?_⟩
      edge_step
    · refine ⟨T.L2e4d.mpr ?_, ?_⟩
      · simp only [E.L2e4d, AtSrch]
        refine rsN_next PQ.down _ ?_ (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 18 ?_
        · rfl
        exact
          (by
          intro i h1 h2
          rcases (show i = 15 ∨ i = 16 ∨ i = 17 by omega) with rfl | rfl | rfl
          · exact ⟨F0, PE.down.1, by omega⟩
          · exact ⟨F1, PE.down.2.1, by omega⟩
          · exact ⟨F2, PE.down.2.2, by omega⟩)
      · var_step

set_option maxRecDepth 100000 in
/-- `goal_sb` against `f_master[18]` … `f_master[20]`. -/
theorem blk_L2e4d (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2e4d" ⟨"sbr_reset.L2e4d", B.L2e4d, some "sbr_reset.L2e8f"⟩ := by
  info_off
  measure_hb "L2e4d"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨st, fr, c, hQ⟩ := rsN_of (T.L2e4d.mp hs)
    clear hs
    obtain ⟨F0, e0, b0, ld0⟩ := rsN_ldF hQ (i := 18) (by omega)
    obtain ⟨F1, e1, b1, ld1⟩ := rsN_ldF hQ (i := 19) (by omega)
    obtain ⟨F2, e2, b2, ld2⟩ := rsN_ldF hQ (i := 20) (by omega)
    obtain ⟨h12, hax⟩ := rsN_regs hQ
    obtain ⟨g0, g1, -⟩ := rsN_num hQ
    have gt : (goalSb a.x.sampleRate.toInt).toNat < 2 ^ 16 := by omega
    simp only [arg1, Nat.reduceMul, Nat.reduceAdd] at ld0 ld1 ld2 h12
    have PQ := PLift.up hQ
    have PL := PLift.up (And.intro ld0 (And.intro ld1 ld2))
    have PE := PLift.up (And.intro e0 (And.intro e1 e2))
    have PR := PLift.up (And.intro h12 hax)
    have z0 : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    clear hQ ld0 ld1 ld2 e0 e1 e2 h12 hax
    simp only [B.L2e4d]
    vcgen
    all_goals try subst_vars
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
      Int64.toBitVec_ofNat_norm, Option.isSome_some, PR.down.1, PR.down.2, z0, BitVec.add_zero, PL.down.1, PL.down.2.1, PL.down.2.2,
      Option.some.injEq, cc_be_sub, cc_a_sub, decide_eq_true_eq, decide_eq_false_iff_not] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt_natCast, rsN_sw _ b0, rsN_sw _ b1, rsN_sw _ b2, rsN_sg _ (by omega : (goalSb a.x.sampleRate.toInt).toNat < 2 ^ 32),
      rsN_cc_le _ _ gt b0, decide_eq_true_eq, decide_eq_false_iff_not] at *
    all_goals try simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at *
    · left; apply Table.ofLabels_at
      refine ⟨by decide, T.L30df.mpr (rsN_exit PQ.down _ rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 18
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; rfl)
        (fun i h1 h2 => absurd h2 (by omega))
        ⟨F0, PE.down.1, by omega⟩), ?_⟩
      edge_step
    · left; apply Table.ofLabels_at
      refine ⟨by decide, T.L30df.mpr (rsN_exit PQ.down _ rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 19
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; rfl)
        (by
          intro i h1 h2
          have : i = 18 := by omega
          subst this; exact ⟨F0, PE.down.1, by omega⟩)
        ⟨F1, PE.down.2.1, by omega⟩), ?_⟩
      edge_step
    · left; apply Table.ofLabels_at
      refine ⟨by decide, T.L30df.mpr (rsN_exit PQ.down _ rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 20
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; rfl)
        (by
          intro i h1 h2
          rcases (show i = 18 ∨ i = 19 by omega) with rfl | rfl
          · exact ⟨F0, PE.down.1, by omega⟩
          · exact ⟨F1, PE.down.2.1, by omega⟩)
        ⟨F2, PE.down.2.2, by omega⟩), ?_⟩
      edge_step
    · refine ⟨T.L2e8f.mpr ?_, ?_⟩
      · simp only [E.L2e8f, AtSrch]
        refine rsN_next PQ.down _ ?_ (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 21 ?_
        · rfl
        exact
          (by
          intro i h1 h2
          rcases (show i = 18 ∨ i = 19 ∨ i = 20 by omega) with rfl | rfl | rfl
          · exact ⟨F0, PE.down.1, by omega⟩
          · exact ⟨F1, PE.down.2.1, by omega⟩
          · exact ⟨F2, PE.down.2.2, by omega⟩)
      · var_step

set_option maxRecDepth 100000 in
/-- `goal_sb` against `f_master[21]` … `f_master[23]`. -/
theorem blk_L2e8f (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2e8f" ⟨"sbr_reset.L2e8f", B.L2e8f, some "sbr_reset.L2ed1"⟩ := by
  info_off
  measure_hb "L2e8f"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨st, fr, c, hQ⟩ := rsN_of (T.L2e8f.mp hs)
    clear hs
    obtain ⟨F0, e0, b0, ld0⟩ := rsN_ldF hQ (i := 21) (by omega)
    obtain ⟨F1, e1, b1, ld1⟩ := rsN_ldF hQ (i := 22) (by omega)
    obtain ⟨F2, e2, b2, ld2⟩ := rsN_ldF hQ (i := 23) (by omega)
    obtain ⟨h12, hax⟩ := rsN_regs hQ
    obtain ⟨g0, g1, -⟩ := rsN_num hQ
    have gt : (goalSb a.x.sampleRate.toInt).toNat < 2 ^ 16 := by omega
    simp only [arg1, Nat.reduceMul, Nat.reduceAdd] at ld0 ld1 ld2 h12
    have PQ := PLift.up hQ
    have PL := PLift.up (And.intro ld0 (And.intro ld1 ld2))
    have PE := PLift.up (And.intro e0 (And.intro e1 e2))
    have PR := PLift.up (And.intro h12 hax)
    have z0 : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    clear hQ ld0 ld1 ld2 e0 e1 e2 h12 hax
    simp only [B.L2e8f]
    vcgen
    all_goals try subst_vars
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
      Int64.toBitVec_ofNat_norm, Option.isSome_some, PR.down.1, PR.down.2, z0, BitVec.add_zero, PL.down.1, PL.down.2.1, PL.down.2.2,
      Option.some.injEq, cc_be_sub, cc_a_sub, decide_eq_true_eq, decide_eq_false_iff_not] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt_natCast, rsN_sw _ b0, rsN_sw _ b1, rsN_sw _ b2, rsN_sg _ (by omega : (goalSb a.x.sampleRate.toInt).toNat < 2 ^ 32),
      rsN_cc_le _ _ gt b0, decide_eq_true_eq, decide_eq_false_iff_not] at *
    all_goals try simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at *
    · left; apply Table.ofLabels_at
      refine ⟨by decide, T.L30df.mpr (rsN_exit PQ.down _ rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 21
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; rfl)
        (fun i h1 h2 => absurd h2 (by omega))
        ⟨F0, PE.down.1, by omega⟩), ?_⟩
      edge_step
    · left; apply Table.ofLabels_at
      refine ⟨by decide, T.L30df.mpr (rsN_exit PQ.down _ rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 22
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; rfl)
        (by
          intro i h1 h2
          have : i = 21 := by omega
          subst this; exact ⟨F0, PE.down.1, by omega⟩)
        ⟨F1, PE.down.2.1, by omega⟩), ?_⟩
      edge_step
    · left; apply Table.ofLabels_at
      refine ⟨by decide, T.L30df.mpr (rsN_exit PQ.down _ rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 23
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; rfl)
        (by
          intro i h1 h2
          rcases (show i = 21 ∨ i = 22 by omega) with rfl | rfl
          · exact ⟨F0, PE.down.1, by omega⟩
          · exact ⟨F1, PE.down.2.1, by omega⟩)
        ⟨F2, PE.down.2.2, by omega⟩), ?_⟩
      edge_step
    · refine ⟨T.L2ed1.mpr ?_, ?_⟩
      · simp only [E.L2ed1, AtSrch]
        refine rsN_next PQ.down _ ?_ (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 24 ?_
        · rfl
        exact
          (by
          intro i h1 h2
          rcases (show i = 21 ∨ i = 22 ∨ i = 23 by omega) with rfl | rfl | rfl
          · exact ⟨F0, PE.down.1, by omega⟩
          · exact ⟨F1, PE.down.2.1, by omega⟩
          · exact ⟨F2, PE.down.2.2, by omega⟩)
      · var_step

set_option maxRecDepth 100000 in
/-- `goal_sb` against `f_master[24]` … `f_master[26]`. -/
theorem blk_L2ed1 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2ed1" ⟨"sbr_reset.L2ed1", B.L2ed1, some "sbr_reset.L2f13"⟩ := by
  info_off
  measure_hb "L2ed1"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨st, fr, c, hQ⟩ := rsN_of (T.L2ed1.mp hs)
    clear hs
    obtain ⟨F0, e0, b0, ld0⟩ := rsN_ldF hQ (i := 24) (by omega)
    obtain ⟨F1, e1, b1, ld1⟩ := rsN_ldF hQ (i := 25) (by omega)
    obtain ⟨F2, e2, b2, ld2⟩ := rsN_ldF hQ (i := 26) (by omega)
    obtain ⟨h12, hax⟩ := rsN_regs hQ
    obtain ⟨g0, g1, -⟩ := rsN_num hQ
    have gt : (goalSb a.x.sampleRate.toInt).toNat < 2 ^ 16 := by omega
    simp only [arg1, Nat.reduceMul, Nat.reduceAdd] at ld0 ld1 ld2 h12
    have PQ := PLift.up hQ
    have PL := PLift.up (And.intro ld0 (And.intro ld1 ld2))
    have PE := PLift.up (And.intro e0 (And.intro e1 e2))
    have PR := PLift.up (And.intro h12 hax)
    have z0 : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    clear hQ ld0 ld1 ld2 e0 e1 e2 h12 hax
    simp only [B.L2ed1]
    vcgen
    all_goals try subst_vars
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
      Int64.toBitVec_ofNat_norm, Option.isSome_some, PR.down.1, PR.down.2, z0, BitVec.add_zero, PL.down.1, PL.down.2.1, PL.down.2.2,
      Option.some.injEq, cc_be_sub, cc_a_sub, decide_eq_true_eq, decide_eq_false_iff_not] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt_natCast, rsN_sw _ b0, rsN_sw _ b1, rsN_sw _ b2, rsN_sg _ (by omega : (goalSb a.x.sampleRate.toInt).toNat < 2 ^ 32),
      rsN_cc_le _ _ gt b0, decide_eq_true_eq, decide_eq_false_iff_not] at *
    all_goals try simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at *
    · left; apply Table.ofLabels_at
      refine ⟨by decide, T.L30df.mpr (rsN_exit PQ.down _ rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 24
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; rfl)
        (fun i h1 h2 => absurd h2 (by omega))
        ⟨F0, PE.down.1, by omega⟩), ?_⟩
      edge_step
    · left; apply Table.ofLabels_at
      refine ⟨by decide, T.L30df.mpr (rsN_exit PQ.down _ rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 25
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; rfl)
        (by
          intro i h1 h2
          have : i = 24 := by omega
          subst this; exact ⟨F0, PE.down.1, by omega⟩)
        ⟨F1, PE.down.2.1, by omega⟩), ?_⟩
      edge_step
    · left; apply Table.ofLabels_at
      refine ⟨by decide, T.L30df.mpr (rsN_exit PQ.down _ rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 26
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; rfl)
        (by
          intro i h1 h2
          rcases (show i = 24 ∨ i = 25 by omega) with rfl | rfl
          · exact ⟨F0, PE.down.1, by omega⟩
          · exact ⟨F1, PE.down.2.1, by omega⟩)
        ⟨F2, PE.down.2.2, by omega⟩), ?_⟩
      edge_step
    · refine ⟨T.L2f13.mpr ?_, ?_⟩
      · simp only [E.L2f13, AtSrch]
        refine rsN_next PQ.down _ ?_ (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 27 ?_
        · rfl
        exact
          (by
          intro i h1 h2
          rcases (show i = 24 ∨ i = 25 ∨ i = 26 by omega) with rfl | rfl | rfl
          · exact ⟨F0, PE.down.1, by omega⟩
          · exact ⟨F1, PE.down.2.1, by omega⟩
          · exact ⟨F2, PE.down.2.2, by omega⟩)
      · var_step

set_option maxRecDepth 100000 in
/-- `goal_sb` against `f_master[27]` … `f_master[29]`. -/
theorem blk_L2f13 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2f13" ⟨"sbr_reset.L2f13", B.L2f13, some "sbr_reset.L2f55"⟩ := by
  info_off
  measure_hb "L2f13"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨st, fr, c, hQ⟩ := rsN_of (T.L2f13.mp hs)
    clear hs
    obtain ⟨F0, e0, b0, ld0⟩ := rsN_ldF hQ (i := 27) (by omega)
    obtain ⟨F1, e1, b1, ld1⟩ := rsN_ldF hQ (i := 28) (by omega)
    obtain ⟨F2, e2, b2, ld2⟩ := rsN_ldF hQ (i := 29) (by omega)
    obtain ⟨h12, hax⟩ := rsN_regs hQ
    obtain ⟨g0, g1, -⟩ := rsN_num hQ
    have gt : (goalSb a.x.sampleRate.toInt).toNat < 2 ^ 16 := by omega
    simp only [arg1, Nat.reduceMul, Nat.reduceAdd] at ld0 ld1 ld2 h12
    have PQ := PLift.up hQ
    have PL := PLift.up (And.intro ld0 (And.intro ld1 ld2))
    have PE := PLift.up (And.intro e0 (And.intro e1 e2))
    have PR := PLift.up (And.intro h12 hax)
    have z0 : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    clear hQ ld0 ld1 ld2 e0 e1 e2 h12 hax
    simp only [B.L2f13]
    vcgen
    all_goals try subst_vars
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
      Int64.toBitVec_ofNat_norm, Option.isSome_some, PR.down.1, PR.down.2, z0, BitVec.add_zero, PL.down.1, PL.down.2.1, PL.down.2.2,
      Option.some.injEq, cc_be_sub, cc_a_sub, decide_eq_true_eq, decide_eq_false_iff_not] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt_natCast, rsN_sw _ b0, rsN_sw _ b1, rsN_sw _ b2, rsN_sg _ (by omega : (goalSb a.x.sampleRate.toInt).toNat < 2 ^ 32),
      rsN_cc_le _ _ gt b0, decide_eq_true_eq, decide_eq_false_iff_not] at *
    all_goals try simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at *
    · left; apply Table.ofLabels_at
      refine ⟨by decide, T.L30df.mpr (rsN_exit PQ.down _ rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 27
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; rfl)
        (fun i h1 h2 => absurd h2 (by omega))
        ⟨F0, PE.down.1, by omega⟩), ?_⟩
      edge_step
    · left; apply Table.ofLabels_at
      refine ⟨by decide, T.L30df.mpr (rsN_exit PQ.down _ rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 28
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; rfl)
        (by
          intro i h1 h2
          have : i = 27 := by omega
          subst this; exact ⟨F0, PE.down.1, by omega⟩)
        ⟨F1, PE.down.2.1, by omega⟩), ?_⟩
      edge_step
    · left; apply Table.ofLabels_at
      refine ⟨by decide, T.L30df.mpr (rsN_exit PQ.down _ rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 29
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; rfl)
        (by
          intro i h1 h2
          rcases (show i = 27 ∨ i = 28 by omega) with rfl | rfl
          · exact ⟨F0, PE.down.1, by omega⟩
          · exact ⟨F1, PE.down.2.1, by omega⟩)
        ⟨F2, PE.down.2.2, by omega⟩), ?_⟩
      edge_step
    · refine ⟨T.L2f55.mpr ?_, ?_⟩
      · simp only [E.L2f55, AtSrch]
        refine rsN_next PQ.down _ ?_ (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 30 ?_
        · rfl
        exact
          (by
          intro i h1 h2
          rcases (show i = 27 ∨ i = 28 ∨ i = 29 by omega) with rfl | rfl | rfl
          · exact ⟨F0, PE.down.1, by omega⟩
          · exact ⟨F1, PE.down.2.1, by omega⟩
          · exact ⟨F2, PE.down.2.2, by omega⟩)
      · var_step

set_option maxRecDepth 100000 in
/-- `goal_sb` against `f_master[30]` … `f_master[32]`. -/
theorem blk_L2f55 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2f55" ⟨"sbr_reset.L2f55", B.L2f55, some "sbr_reset.L2f97"⟩ := by
  info_off
  measure_hb "L2f55"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨st, fr, c, hQ⟩ := rsN_of (T.L2f55.mp hs)
    clear hs
    obtain ⟨F0, e0, b0, ld0⟩ := rsN_ldF hQ (i := 30) (by omega)
    obtain ⟨F1, e1, b1, ld1⟩ := rsN_ldF hQ (i := 31) (by omega)
    obtain ⟨F2, e2, b2, ld2⟩ := rsN_ldF hQ (i := 32) (by omega)
    obtain ⟨h12, hax⟩ := rsN_regs hQ
    obtain ⟨g0, g1, -⟩ := rsN_num hQ
    have gt : (goalSb a.x.sampleRate.toInt).toNat < 2 ^ 16 := by omega
    simp only [arg1, Nat.reduceMul, Nat.reduceAdd] at ld0 ld1 ld2 h12
    have PQ := PLift.up hQ
    have PL := PLift.up (And.intro ld0 (And.intro ld1 ld2))
    have PE := PLift.up (And.intro e0 (And.intro e1 e2))
    have PR := PLift.up (And.intro h12 hax)
    have z0 : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    clear hQ ld0 ld1 ld2 e0 e1 e2 h12 hax
    simp only [B.L2f55]
    vcgen
    all_goals try subst_vars
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
      Int64.toBitVec_ofNat_norm, Option.isSome_some, PR.down.1, PR.down.2, z0, BitVec.add_zero, PL.down.1, PL.down.2.1, PL.down.2.2,
      Option.some.injEq, cc_be_sub, cc_a_sub, decide_eq_true_eq, decide_eq_false_iff_not] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt_natCast, rsN_sw _ b0, rsN_sw _ b1, rsN_sw _ b2, rsN_sg _ (by omega : (goalSb a.x.sampleRate.toInt).toNat < 2 ^ 32),
      rsN_cc_le _ _ gt b0, decide_eq_true_eq, decide_eq_false_iff_not] at *
    all_goals try simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at *
    · left; apply Table.ofLabels_at
      refine ⟨by decide, T.L30df.mpr (rsN_exit PQ.down _ rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 30
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; rfl)
        (fun i h1 h2 => absurd h2 (by omega))
        ⟨F0, PE.down.1, by omega⟩), ?_⟩
      edge_step
    · left; apply Table.ofLabels_at
      refine ⟨by decide, T.L30df.mpr (rsN_exit PQ.down _ rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 31
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; rfl)
        (by
          intro i h1 h2
          have : i = 30 := by omega
          subst this; exact ⟨F0, PE.down.1, by omega⟩)
        ⟨F1, PE.down.2.1, by omega⟩), ?_⟩
      edge_step
    · left; apply Table.ofLabels_at
      refine ⟨by decide, T.L30df.mpr (rsN_exit PQ.down _ rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 32
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; rfl)
        (by
          intro i h1 h2
          rcases (show i = 30 ∨ i = 31 by omega) with rfl | rfl
          · exact ⟨F0, PE.down.1, by omega⟩
          · exact ⟨F1, PE.down.2.1, by omega⟩)
        ⟨F2, PE.down.2.2, by omega⟩), ?_⟩
      edge_step
    · refine ⟨T.L2f97.mpr ?_, ?_⟩
      · simp only [E.L2f97, AtSrch]
        refine rsN_next PQ.down _ ?_ (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 33 ?_
        · rfl
        exact
          (by
          intro i h1 h2
          rcases (show i = 30 ∨ i = 31 ∨ i = 32 by omega) with rfl | rfl | rfl
          · exact ⟨F0, PE.down.1, by omega⟩
          · exact ⟨F1, PE.down.2.1, by omega⟩
          · exact ⟨F2, PE.down.2.2, by omega⟩)
      · var_step

set_option maxRecDepth 100000 in
/-- `goal_sb` against `f_master[33]` … `f_master[35]`. -/
theorem blk_L2f97 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2f97" ⟨"sbr_reset.L2f97", B.L2f97, some "sbr_reset.L2fd9"⟩ := by
  info_off
  measure_hb "L2f97"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨st, fr, c, hQ⟩ := rsN_of (T.L2f97.mp hs)
    clear hs
    obtain ⟨F0, e0, b0, ld0⟩ := rsN_ldF hQ (i := 33) (by omega)
    obtain ⟨F1, e1, b1, ld1⟩ := rsN_ldF hQ (i := 34) (by omega)
    obtain ⟨F2, e2, b2, ld2⟩ := rsN_ldF hQ (i := 35) (by omega)
    obtain ⟨h12, hax⟩ := rsN_regs hQ
    obtain ⟨g0, g1, -⟩ := rsN_num hQ
    have gt : (goalSb a.x.sampleRate.toInt).toNat < 2 ^ 16 := by omega
    simp only [arg1, Nat.reduceMul, Nat.reduceAdd] at ld0 ld1 ld2 h12
    have PQ := PLift.up hQ
    have PL := PLift.up (And.intro ld0 (And.intro ld1 ld2))
    have PE := PLift.up (And.intro e0 (And.intro e1 e2))
    have PR := PLift.up (And.intro h12 hax)
    have z0 : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    clear hQ ld0 ld1 ld2 e0 e1 e2 h12 hax
    simp only [B.L2f97]
    vcgen
    all_goals try subst_vars
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
      Int64.toBitVec_ofNat_norm, Option.isSome_some, PR.down.1, PR.down.2, z0, BitVec.add_zero, PL.down.1, PL.down.2.1, PL.down.2.2,
      Option.some.injEq, cc_be_sub, cc_a_sub, decide_eq_true_eq, decide_eq_false_iff_not] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt_natCast, rsN_sw _ b0, rsN_sw _ b1, rsN_sw _ b2, rsN_sg _ (by omega : (goalSb a.x.sampleRate.toInt).toNat < 2 ^ 32),
      rsN_cc_le _ _ gt b0, decide_eq_true_eq, decide_eq_false_iff_not] at *
    all_goals try simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at *
    · left; apply Table.ofLabels_at
      refine ⟨by decide, T.L30df.mpr (rsN_exit PQ.down _ rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 33
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; rfl)
        (fun i h1 h2 => absurd h2 (by omega))
        ⟨F0, PE.down.1, by omega⟩), ?_⟩
      edge_step
    · left; apply Table.ofLabels_at
      refine ⟨by decide, T.L30df.mpr (rsN_exit PQ.down _ rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 34
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; rfl)
        (by
          intro i h1 h2
          have : i = 33 := by omega
          subst this; exact ⟨F0, PE.down.1, by omega⟩)
        ⟨F1, PE.down.2.1, by omega⟩), ?_⟩
      edge_step
    · left; apply Table.ofLabels_at
      refine ⟨by decide, T.L30df.mpr (rsN_exit PQ.down _ rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 35
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; rfl)
        (by
          intro i h1 h2
          rcases (show i = 33 ∨ i = 34 by omega) with rfl | rfl
          · exact ⟨F0, PE.down.1, by omega⟩
          · exact ⟨F1, PE.down.2.1, by omega⟩)
        ⟨F2, PE.down.2.2, by omega⟩), ?_⟩
      edge_step
    · refine ⟨T.L2fd9.mpr ?_, ?_⟩
      · simp only [E.L2fd9, AtSrch]
        refine rsN_next PQ.down _ ?_ (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 36 ?_
        · rfl
        exact
          (by
          intro i h1 h2
          rcases (show i = 33 ∨ i = 34 ∨ i = 35 by omega) with rfl | rfl | rfl
          · exact ⟨F0, PE.down.1, by omega⟩
          · exact ⟨F1, PE.down.2.1, by omega⟩
          · exact ⟨F2, PE.down.2.2, by omega⟩)
      · var_step

set_option maxRecDepth 100000 in
/-- `goal_sb` against `f_master[36]` … `f_master[38]`. -/
theorem blk_L2fd9 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2fd9" ⟨"sbr_reset.L2fd9", B.L2fd9, some "sbr_reset.L301b"⟩ := by
  info_off
  measure_hb "L2fd9"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨st, fr, c, hQ⟩ := rsN_of (T.L2fd9.mp hs)
    clear hs
    obtain ⟨F0, e0, b0, ld0⟩ := rsN_ldF hQ (i := 36) (by omega)
    obtain ⟨F1, e1, b1, ld1⟩ := rsN_ldF hQ (i := 37) (by omega)
    obtain ⟨F2, e2, b2, ld2⟩ := rsN_ldF hQ (i := 38) (by omega)
    obtain ⟨h12, hax⟩ := rsN_regs hQ
    obtain ⟨g0, g1, -⟩ := rsN_num hQ
    have gt : (goalSb a.x.sampleRate.toInt).toNat < 2 ^ 16 := by omega
    simp only [arg1, Nat.reduceMul, Nat.reduceAdd] at ld0 ld1 ld2 h12
    have PQ := PLift.up hQ
    have PL := PLift.up (And.intro ld0 (And.intro ld1 ld2))
    have PE := PLift.up (And.intro e0 (And.intro e1 e2))
    have PR := PLift.up (And.intro h12 hax)
    have z0 : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    clear hQ ld0 ld1 ld2 e0 e1 e2 h12 hax
    simp only [B.L2fd9]
    vcgen
    all_goals try subst_vars
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
      Int64.toBitVec_ofNat_norm, Option.isSome_some, PR.down.1, PR.down.2, z0, BitVec.add_zero, PL.down.1, PL.down.2.1, PL.down.2.2,
      Option.some.injEq, cc_be_sub, cc_a_sub, decide_eq_true_eq, decide_eq_false_iff_not] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt_natCast, rsN_sw _ b0, rsN_sw _ b1, rsN_sw _ b2, rsN_sg _ (by omega : (goalSb a.x.sampleRate.toInt).toNat < 2 ^ 32),
      rsN_cc_le _ _ gt b0, decide_eq_true_eq, decide_eq_false_iff_not] at *
    all_goals try simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at *
    · left; apply Table.ofLabels_at
      refine ⟨by decide, T.L30df.mpr (rsN_exit PQ.down _ rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 36
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; rfl)
        (fun i h1 h2 => absurd h2 (by omega))
        ⟨F0, PE.down.1, by omega⟩), ?_⟩
      edge_step
    · left; apply Table.ofLabels_at
      refine ⟨by decide, T.L30df.mpr (rsN_exit PQ.down _ rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 37
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; rfl)
        (by
          intro i h1 h2
          have : i = 36 := by omega
          subst this; exact ⟨F0, PE.down.1, by omega⟩)
        ⟨F1, PE.down.2.1, by omega⟩), ?_⟩
      edge_step
    · left; apply Table.ofLabels_at
      refine ⟨by decide, T.L30df.mpr (rsN_exit PQ.down _ rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 38
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; rfl)
        (by
          intro i h1 h2
          rcases (show i = 36 ∨ i = 37 by omega) with rfl | rfl
          · exact ⟨F0, PE.down.1, by omega⟩
          · exact ⟨F1, PE.down.2.1, by omega⟩)
        ⟨F2, PE.down.2.2, by omega⟩), ?_⟩
      edge_step
    · refine ⟨T.L301b.mpr ?_, ?_⟩
      · simp only [E.L301b, AtSrch]
        refine rsN_next PQ.down _ ?_ (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 39 ?_
        · rfl
        exact
          (by
          intro i h1 h2
          rcases (show i = 36 ∨ i = 37 ∨ i = 38 by omega) with rfl | rfl | rfl
          · exact ⟨F0, PE.down.1, by omega⟩
          · exact ⟨F1, PE.down.2.1, by omega⟩
          · exact ⟨F2, PE.down.2.2, by omega⟩)
      · var_step

set_option maxRecDepth 100000 in
/-- `goal_sb` against `f_master[39]` … `f_master[41]`. -/
theorem blk_L301b (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L301b" ⟨"sbr_reset.L301b", B.L301b, some "sbr_reset.L305d"⟩ := by
  info_off
  measure_hb "L301b"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨st, fr, c, hQ⟩ := rsN_of (T.L301b.mp hs)
    clear hs
    obtain ⟨F0, e0, b0, ld0⟩ := rsN_ldF hQ (i := 39) (by omega)
    obtain ⟨F1, e1, b1, ld1⟩ := rsN_ldF hQ (i := 40) (by omega)
    obtain ⟨F2, e2, b2, ld2⟩ := rsN_ldF hQ (i := 41) (by omega)
    obtain ⟨h12, hax⟩ := rsN_regs hQ
    obtain ⟨g0, g1, -⟩ := rsN_num hQ
    have gt : (goalSb a.x.sampleRate.toInt).toNat < 2 ^ 16 := by omega
    simp only [arg1, Nat.reduceMul, Nat.reduceAdd] at ld0 ld1 ld2 h12
    have PQ := PLift.up hQ
    have PL := PLift.up (And.intro ld0 (And.intro ld1 ld2))
    have PE := PLift.up (And.intro e0 (And.intro e1 e2))
    have PR := PLift.up (And.intro h12 hax)
    have z0 : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    clear hQ ld0 ld1 ld2 e0 e1 e2 h12 hax
    simp only [B.L301b]
    vcgen
    all_goals try subst_vars
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
      Int64.toBitVec_ofNat_norm, Option.isSome_some, PR.down.1, PR.down.2, z0, BitVec.add_zero, PL.down.1, PL.down.2.1, PL.down.2.2,
      Option.some.injEq, cc_be_sub, cc_a_sub, decide_eq_true_eq, decide_eq_false_iff_not] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt_natCast, rsN_sw _ b0, rsN_sw _ b1, rsN_sw _ b2, rsN_sg _ (by omega : (goalSb a.x.sampleRate.toInt).toNat < 2 ^ 32),
      rsN_cc_le _ _ gt b0, decide_eq_true_eq, decide_eq_false_iff_not] at *
    all_goals try simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at *
    · left; apply Table.ofLabels_at
      refine ⟨by decide, T.L30df.mpr (rsN_exit PQ.down _ rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 39
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; rfl)
        (fun i h1 h2 => absurd h2 (by omega))
        ⟨F0, PE.down.1, by omega⟩), ?_⟩
      edge_step
    · left; apply Table.ofLabels_at
      refine ⟨by decide, T.L30df.mpr (rsN_exit PQ.down _ rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 40
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; rfl)
        (by
          intro i h1 h2
          have : i = 39 := by omega
          subst this; exact ⟨F0, PE.down.1, by omega⟩)
        ⟨F1, PE.down.2.1, by omega⟩), ?_⟩
      edge_step
    · left; apply Table.ofLabels_at
      refine ⟨by decide, T.L30df.mpr (rsN_exit PQ.down _ rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 41
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; rfl)
        (by
          intro i h1 h2
          rcases (show i = 39 ∨ i = 40 by omega) with rfl | rfl
          · exact ⟨F0, PE.down.1, by omega⟩
          · exact ⟨F1, PE.down.2.1, by omega⟩)
        ⟨F2, PE.down.2.2, by omega⟩), ?_⟩
      edge_step
    · refine ⟨T.L305d.mpr ?_, ?_⟩
      · simp only [E.L305d, AtSrch]
        refine rsN_next PQ.down _ ?_ (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 42 ?_
        · rfl
        exact
          (by
          intro i h1 h2
          rcases (show i = 39 ∨ i = 40 ∨ i = 41 by omega) with rfl | rfl | rfl
          · exact ⟨F0, PE.down.1, by omega⟩
          · exact ⟨F1, PE.down.2.1, by omega⟩
          · exact ⟨F2, PE.down.2.2, by omega⟩)
      · var_step

set_option maxRecDepth 100000 in
/-- `goal_sb` against `f_master[42]` … `f_master[44]`. -/
theorem blk_L305d (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L305d" ⟨"sbr_reset.L305d", B.L305d, some "sbr_reset.L3093"⟩ := by
  info_off
  measure_hb "L305d"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨st, fr, c, hQ⟩ := rsN_of (T.L305d.mp hs)
    clear hs
    obtain ⟨F0, e0, b0, ld0⟩ := rsN_ldF hQ (i := 42) (by omega)
    obtain ⟨F1, e1, b1, ld1⟩ := rsN_ldF hQ (i := 43) (by omega)
    obtain ⟨F2, e2, b2, ld2⟩ := rsN_ldF hQ (i := 44) (by omega)
    obtain ⟨h12, hax⟩ := rsN_regs hQ
    obtain ⟨g0, g1, -⟩ := rsN_num hQ
    have gt : (goalSb a.x.sampleRate.toInt).toNat < 2 ^ 16 := by omega
    simp only [arg1, Nat.reduceMul, Nat.reduceAdd] at ld0 ld1 ld2 h12
    have PQ := PLift.up hQ
    have PL := PLift.up (And.intro ld0 (And.intro ld1 ld2))
    have PE := PLift.up (And.intro e0 (And.intro e1 e2))
    have PR := PLift.up (And.intro h12 hax)
    have z0 : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    clear hQ ld0 ld1 ld2 e0 e1 e2 h12 hax
    simp only [B.L305d]
    vcgen
    all_goals try subst_vars
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
      Int64.toBitVec_ofNat_norm, Option.isSome_some, PR.down.1, PR.down.2, z0, BitVec.add_zero, PL.down.1, PL.down.2.1, PL.down.2.2,
      Option.some.injEq, cc_be_sub, cc_a_sub, decide_eq_true_eq, decide_eq_false_iff_not] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt_natCast, rsN_sw _ b0, rsN_sw _ b1, rsN_sw _ b2, rsN_sg _ (by omega : (goalSb a.x.sampleRate.toInt).toNat < 2 ^ 32),
      rsN_cc_le _ _ gt b0, decide_eq_true_eq, decide_eq_false_iff_not] at *
    all_goals try simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at *
    · left; apply Table.ofLabels_at
      refine ⟨by decide, T.L30df.mpr (rsN_exit PQ.down _ rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 42
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; rfl)
        (fun i h1 h2 => absurd h2 (by omega))
        ⟨F0, PE.down.1, by omega⟩), ?_⟩
      edge_step
    · left; apply Table.ofLabels_at
      refine ⟨by decide, T.L30df.mpr (rsN_exit PQ.down _ rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 43
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; rfl)
        (by
          intro i h1 h2
          have : i = 42 := by omega
          subst this; exact ⟨F0, PE.down.1, by omega⟩)
        ⟨F1, PE.down.2.1, by omega⟩), ?_⟩
      edge_step
    · left; apply Table.ofLabels_at
      refine ⟨by decide, T.L30df.mpr (rsN_exit PQ.down _ rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 44
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; rfl)
        (by
          intro i h1 h2
          rcases (show i = 42 ∨ i = 43 by omega) with rfl | rfl
          · exact ⟨F0, PE.down.1, by omega⟩
          · exact ⟨F1, PE.down.2.1, by omega⟩)
        ⟨F2, PE.down.2.2, by omega⟩), ?_⟩
      edge_step
    · refine ⟨T.L3093.mpr ?_, ?_⟩
      · simp only [E.L3093, AtSrch]
        refine rsN_next PQ.down _ ?_ (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 45 ?_
        · rfl
        exact
          (by
          intro i h1 h2
          rcases (show i = 42 ∨ i = 43 ∨ i = 44 by omega) with rfl | rfl | rfl
          · exact ⟨F0, PE.down.1, by omega⟩
          · exact ⟨F1, PE.down.2.1, by omega⟩
          · exact ⟨F2, PE.down.2.2, by omega⟩)
      · var_step

set_option maxRecDepth 100000 in
/-- `goal_sb` against `f_master[45]` … `f_master[47]`. -/
theorem blk_L3093 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L3093" ⟨"sbr_reset.L3093", B.L3093, some "sbr_reset.L30c9"⟩ := by
  info_off
  measure_hb "L3093"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨st, fr, c, hQ⟩ := rsN_of (T.L3093.mp hs)
    clear hs
    obtain ⟨F0, e0, b0, ld0⟩ := rsN_ldF hQ (i := 45) (by omega)
    obtain ⟨F1, e1, b1, ld1⟩ := rsN_ldF hQ (i := 46) (by omega)
    obtain ⟨F2, e2, b2, ld2⟩ := rsN_ldF hQ (i := 47) (by omega)
    obtain ⟨h12, hax⟩ := rsN_regs hQ
    obtain ⟨g0, g1, -⟩ := rsN_num hQ
    have gt : (goalSb a.x.sampleRate.toInt).toNat < 2 ^ 16 := by omega
    simp only [arg1, Nat.reduceMul, Nat.reduceAdd] at ld0 ld1 ld2 h12
    have PQ := PLift.up hQ
    have PL := PLift.up (And.intro ld0 (And.intro ld1 ld2))
    have PE := PLift.up (And.intro e0 (And.intro e1 e2))
    have PR := PLift.up (And.intro h12 hax)
    have z0 : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    clear hQ ld0 ld1 ld2 e0 e1 e2 h12 hax
    simp only [B.L3093]
    vcgen
    all_goals try subst_vars
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
      Int64.toBitVec_ofNat_norm, Option.isSome_some, PR.down.1, PR.down.2, z0, BitVec.add_zero, PL.down.1, PL.down.2.1, PL.down.2.2,
      Option.some.injEq, cc_be_sub, cc_a_sub, decide_eq_true_eq, decide_eq_false_iff_not] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt_natCast, rsN_sw _ b0, rsN_sw _ b1, rsN_sw _ b2, rsN_sg _ (by omega : (goalSb a.x.sampleRate.toInt).toNat < 2 ^ 32),
      rsN_cc_le _ _ gt b0, decide_eq_true_eq, decide_eq_false_iff_not] at *
    all_goals try simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at *
    · left; apply Table.ofLabels_at
      refine ⟨by decide, T.L30df.mpr (rsN_exit PQ.down _ rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 45
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; rfl)
        (fun i h1 h2 => absurd h2 (by omega))
        ⟨F0, PE.down.1, by omega⟩), ?_⟩
      edge_step
    · left; apply Table.ofLabels_at
      refine ⟨by decide, T.L30df.mpr (rsN_exit PQ.down _ rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 46
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; rfl)
        (by
          intro i h1 h2
          have : i = 45 := by omega
          subst this; exact ⟨F0, PE.down.1, by omega⟩)
        ⟨F1, PE.down.2.1, by omega⟩), ?_⟩
      edge_step
    · left; apply Table.ofLabels_at
      refine ⟨by decide, T.L30df.mpr (rsN_exit PQ.down _ rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 47
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; rfl)
        (by
          intro i h1 h2
          rcases (show i = 45 ∨ i = 46 by omega) with rfl | rfl
          · exact ⟨F0, PE.down.1, by omega⟩
          · exact ⟨F1, PE.down.2.1, by omega⟩)
        ⟨F2, PE.down.2.2, by omega⟩), ?_⟩
      edge_step
    · refine ⟨T.L30c9.mpr ?_, ?_⟩
      · simp only [E.L30c9, AtSrch]
        refine rsN_next PQ.down _ ?_ (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 48 ?_
        · rfl
        exact
          (by
          intro i h1 h2
          rcases (show i = 45 ∨ i = 46 ∨ i = 47 by omega) with rfl | rfl | rfl
          · exact ⟨F0, PE.down.1, by omega⟩
          · exact ⟨F1, PE.down.2.1, by omega⟩
          · exact ⟨F2, PE.down.2.2, by omega⟩)
      · var_step

set_option maxRecDepth 100000 in
/-- `goal_sb` against `f_master[48]`. -/
theorem blk_L30c9 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L30c9" ⟨"sbr_reset.L30c9", B.L30c9, some "sbr_reset.L30df"⟩ := by
  info_off
  measure_hb "L30c9"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨st, fr, c, hQ⟩ := rsN_of (T.L30c9.mp hs)
    clear hs
    obtain ⟨F0, e0, b0, ld0⟩ := rsN_ldF hQ (i := 48) (by omega)
    obtain ⟨h12, hax⟩ := rsN_regs hQ
    obtain ⟨g0, g1, -⟩ := rsN_num hQ
    have gt : (goalSb a.x.sampleRate.toInt).toNat < 2 ^ 16 := by omega
    simp only [arg1, Nat.reduceMul, Nat.reduceAdd] at ld0 h12
    have PQ := PLift.up hQ
    have PL := PLift.up ld0
    have PE := PLift.up e0
    have PR := PLift.up (And.intro h12 hax)
    have z0 : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    clear hQ ld0 e0 h12 hax
    simp only [B.L30c9]
    vcgen
    all_goals try subst_vars
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
      Int64.toBitVec_ofNat_norm, Option.isSome_some, PR.down.1, PR.down.2, z0, BitVec.add_zero, PL.down,
      Option.some.injEq, cc_be_sub, cc_a_sub, decide_eq_true_eq, decide_eq_false_iff_not] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt_natCast, rsN_sw _ b0, rsN_sg _ (by omega : (goalSb a.x.sampleRate.toInt).toNat < 2 ^ 32),
      rsN_cc_le _ _ gt b0, decide_eq_true_eq, decide_eq_false_iff_not] at *
    all_goals try simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at *
    · exfalso
      exact rsN_end PQ.down (by
          intro i h1 h2
          have : i = 48 := by omega
          subst this; exact ⟨F0, PE.down, by omega⟩)
    · exact ⟨T.L30df.mpr (rsN_exit PQ.down _ rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) 48 (by
        simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; rfl)
        (fun i h1 h2 => absurd h2 (by omega)) ⟨F0, PE.down, by omega⟩), by var_step⟩

end Kraken.Examples.Sbr.Reset
