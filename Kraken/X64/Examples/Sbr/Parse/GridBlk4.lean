import Kraken.X64.Examples.Sbr.Parse.GridMem

/-!
# `read_sbr_grid`: the start of the FIXFIX body

`bs_num_env = 1 << tmp` is written and `t_env[0] = 0`; from here to the `bs_freq_res` fill the
state satisfies `SInvF` (the `DWF` clauses that do not mention `bs_freq_res[1..bs_num_env]`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Grid

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

/-- Storing `t_env[0]`. -/
theorem T_storeTe0 {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : GArgs} {ra : Int64}
    {t₀ : MachineData} {FR : (Mem 64 → Prop) → Mem 64 → Prop} {st : GSt}
    (h : m =⋆ T k Ext x ra t₀ FR st) (hl : st.te.length = 10) (v : BitVec 8) :
    m.storeInt (arg3 t₀ + 0x15a9c#64) 1 v.toInt =⋆ T k Ext x ra t₀ FR (st.setTe 0 v) := by
  rw [T_te] at h ⊢
  have := TeB_storeInt h hl 0 (by omega) v
  simp only [BitVec.add_zero] at this
  exact this

omit [CodeEnv] in
theorem sinvF_n {x : GArgs} {st : GSt} (h : SInv x st) (n : BitVec 32) (hn : n.toNat ≤ 8) :
    SInvF x (st.withN n) := by
  obtain ⟨⟨hfl, -, htl, hql, -, hfr, hnn, -, -, hte9, htq, -⟩, -, hi⟩ := h
  simp only [GSt.dv] at hfl htl hql hnn hte9 htq hfr
  exact ⟨hfl, htl, hql, hn, by omega, hte9, fun q hq => htq q (by omega), hi,
    hfr 0 (Nat.zero_le _)⟩

omit [CodeEnv] in
theorem sinvF_te0 {x : GArgs} {st : GSt} (h : SInvF x st) (v : BitVec 8) :
    SInvF x (st.setTe 0 v) := by
  obtain ⟨hfl, htl, hql, hn, hnn, hte9, htq, hi, hf0⟩ := h
  refine ⟨hfl, ?_, hql, hn, hnn, ?_, htq, hi, hf0⟩
  · simp only [List.length_set]; exact htl
  · simp only [u8]; rw [getD_set_ne _ _ _ _ (by omega)]; exact hte9

theorem blk_L4cb0 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4cb0" := by
  cfg_block
  measure_hb "L4cb0"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hR, hax, h8, hb, st, hS, hm⟩, hn⟩ := hs₀
    have htl : st.te.length = 10 := hS.1.2.2.1
    have hsN := fun v => T_storeN hm v
    have hsT := fun v w => T_storeTe0 (T_storeN hm v) htl w
    have hrbx : s₀.regs.get64 .rbx = arg3 t₀ := hR.2
    have ldN : (s₀.dmem.loadInt (arg3 t₀ + 8#64) 4).isSome = true := by
      have h' := hm
      rw [T_n] at h'
      rw [loadInt_sep _ _ 4 _ _ h' (Int.toBytes_length 4 _) (by omega)]; rfl
    have ldT : ∀ v : BitVec 32, ((s₀.dmem.storeInt (arg3 t₀ + 8#64) 4 v.toInt).loadInt
        (arg3 t₀ + 0x15a9c#64) 1).isSome = true := by
      intro v
      have h' := hsN v
      rw [T_te] at h'
      have := TeB_loadInt h' 0 (by omega)
      simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at this
      rw [this]; rfl
    have hmT : Hide _ := hm
    have pR : PLift (Regs t₀ s₀) := ⟨hR⟩
    clear hm hR
    rcases lt4_cases _ hax with h | h | h | h <;> rw [h] at h8 hb <;>
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
      hrbx] at *
    all_goals try (have hf := ‹CondCode.c.interp _ = false›; simp only [h] at hf; revert hf; decide)
    all_goals try (have hf := ‹CondCode.z.interp _ = true›; simp only [h, CondCode.interp, StatusFlags.from_result, BitVec.reduceSetWidth, BitVec.reduceAnd, BitVec.zero_eq, BitVec.reduceBEq, Bool.true_eq_false, Bool.false_eq_true] at hf; done)
    all_goals try (have hf := ‹CondCode.z.interp _ = false›; simp only [h, CondCode.interp, StatusFlags.from_result, BitVec.reduceSetWidth, BitVec.reduceAnd, BitVec.zero_eq, BitVec.reduceBEq, Bool.true_eq_false, Bool.false_eq_true] at hf; done)
    all_goals try with_reducible exact ldN
    all_goals try with_reducible exact ldT _
    all_goals left; apply Table.ofLabels_at
    all_goals dsimp only [reduceTable, reduceVar]
    · -- L4cc9 (tmp = 0)
      refine ⟨by decide, ⟨hC, pR.down, h, ?_, _, sinvF_n hS _ ?_, ?_, hsN _⟩, ?_⟩
      · rw [h8]; rfl
      · rw [h8]; decide
      · rw [h8]; rfl
      · edge_lt
    all_goals
      refine ⟨by decide, ⟨hC, pR.down, ?_, ?_, ?_, _, sinvF_te0 (sinvF_n hS _ ?_) _, ?_, ?_, hsT _ _⟩, ?_⟩
      · rw [h]; decide
      · rw [h8, h]
      · rw [h]; exact hb
      · rw [h8]; decide
      · dsimp only [GSt.setTe, GSt.withN]
        rw [h8, h]; rfl
      · simp only [u8, GSt.setTe, GSt.withN]
        rw [getD_set_eq _ _ _ (by simp only [htl]; omega)]; rfl
      · edge_lt

/-- FIXFIX with `tmp = 0`: `bs_amp_res = 0`, `t_env[0] = 0`. -/
theorem blk_L4cc9 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4cc9" := by
  cfg_block
  measure_hb "L4cc9"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hR, hax, h8, st, hS, hn1, hm⟩, hn⟩ := hs₀
    have htl : st.te.length = 10 := hS.2.1
    have hs1 := fun v => T_store_x64 hm v
    have hs2 := fun v w => T_storeTe0 (hs1 v) htl w
    have ld64 : (s₀.dmem.loadInt (arg3 t₀ + 0x64#64) 4).isSome = true := by
      obtain ⟨F, hF⟩ := T_x64 k Ext x ra t₀ (Saved t₀) st
      have h1 := hm
      rw [hF] at h1
      exact Block.loadInt_isSome h1 (by rw [BitVec.sub_self, BitVec.toNat_zero]; omega)
    have ldT : ∀ v : Int, ((s₀.dmem.storeInt (arg3 t₀ + 0x64#64) 4 v).loadInt
        (arg3 t₀ + 0x15a9c#64) 1).isSome = true := by
      intro v
      have h' := hs1 v
      rw [T_te] at h'
      have := TeB_loadInt h' 0 (by omega)
      simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at this
      rw [this]; rfl
    have hrbx : s₀.regs.get64 .rbx = arg3 t₀ := hR.2
    have hmT : Hide _ := hm
    have pR : PLift (Regs t₀ s₀) := ⟨hR⟩
    clear hm hR
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
      hrbx] at *
    all_goals try with_reducible exact ld64
    all_goals try with_reducible exact ldT _
    refine ⟨⟨hC, ⟨pR.down.1, pR.down.2⟩, ?_, ?_, ?_, _, sinvF_te0 hS _, ?_, ?_, hs2 _ _⟩, Nat.le_refl _⟩
    · rw [hax]; decide
    · rw [h8, hax]; rfl
    · rw [hax]; split <;> decide
    · dsimp only [GSt.setTe]
      rw [hn1, hax]; rfl
    · simp only [u8, GSt.setTe]
      rw [getD_set_eq _ _ _ (by omega)]; rfl

end Kraken.Examples.Sbr.Grid
