import Kraken.X64.Examples.Sbr.Parse.GridShA1
import Kraken.X64.Examples.Sbr.Parse.GridBlk4

/-!
# `read_sbr_grid`: VARFIX (class 2), `bs_num_env`, `t_env[bs_num_env]`, `ceil_log2`
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Grid

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

omit [CodeEnv] in
theorem shA_inc (a : BitVec 64) (h : a.toNat < 4) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (a + 1#64)) = a + 1#64
      ∧ (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (a + 1#64)))).toNat
        = a.toNat + 1
      ∧ (a + 1#64).toNat = a.toNat + 1 := by
  rcases lt4_cases a h with rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl, rfl⟩

omit [CodeEnv] in
/-- `FrPre` after `t_env[n] = v`, `v ≤ 19`. -/
theorem shA_frPre_te {x : GArgs} {st : GSt} (hS : SInvF x st) (h1 : 1 ≤ st.n.toNat)
    (v : BitVec 8) (hv : v.toNat ≤ 19) : FrPre x (st.setTe st.n.toNat v) := by
  obtain ⟨hfl, htl, hql, hn, hnn, hte9, htq, hi, hf0⟩ := hS
  refine ⟨⟨hfl, by simp only [List.length_set]; exact htl, hql, hn, hnn, ?_, htq, hi, hf0⟩, h1, ?_⟩
  · simp only [u8]; rw [getD_set_ne _ _ _ _ (by omega)]; exact hte9
  · simp only [u8]; rw [getD_set_eq _ _ _ (by omega)]
    simpa using hv

omit [CodeEnv] in
/-- `test %eax,%eax; jle` on a small `eax`. -/
theorem shA_le_ax (a : BitVec 64) (h : a.toNat < 4) (b : Bool) :
    CondCode.le.interp (StatusFlags.from_result (BitVec.setWidth 32 a &&& BitVec.setWidth 32 a)
      { cf := false, af := b, of := false }) = decide (a.toNat = 0) := by
  rcases lt4_cases a h with rfl | rfl | rfl | rfl <;> rfl

/-- `bs_num_env = bs_num_rel + 1`, the check `< 9`. -/
theorem blk_L4539 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4539" := by
  cfg_block
  measure_hb "L4539"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hRB, hdx, hdi, st, ⟨hS, hax⟩, hm⟩, hn⟩ := hs₀
    have hsN := fun v => T_storeN hm v
    have ldN : (s₀.dmem.loadInt (arg3 t₀ + 8#64) 4).isSome = true := by
      rw [T_loadN hm]; rfl
    have hrbx : s₀.regs.get64 .rbx = arg3 t₀ := hRB.2.2.2
    have hmT : Hide _ := hm
    have pRB : PLift (RB t₀ s₀) := ⟨hRB⟩
    have hi := shA_inc _ hax
    clear hm hRB
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbx] at *
    · exact ldN
    · exfalso
      have hf := ‹CondCode.nc.interp _ = true›
      rcases lt4_cases _ hax with h | h | h | h <;> simp only [h] at hf <;> revert hf <;> decide
    · obtain ⟨hsp, hbp, h13, hbx⟩ := pRB.down
      refine ⟨⟨hC, ?_, hdx, hdi, _, ⟨sinvF_n hS _ (Nat.le_trans (Nat.le_of_eq hi.2.1) (by omega)), hax, hi.2.1, hi.1⟩, hsN _⟩,
        Nat.le_refl _⟩
      simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      exact ⟨hsp, hbp, h13, hbx⟩

/-- `t_env[bs_num_env] = 16`; `bs_num_rel = 0` skips the `t_env` loop. -/
theorem blk_L4548 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4548" := by
  cfg_block
  measure_hb "L4548"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hRB, hdx, hdi, st, ⟨hS, hax, hn1, hcx⟩, hm⟩, hn⟩ := hs₀
    have hrbx : s₀.regs.get64 .rbx = arg3 t₀ := hRB.2.2.2
    have htl : st.te.length = 10 := hS.2.1
    have hi := shA_inc _ hax
    have ea : BitVec.setWidth 64 (BitVec.setWidth 32 (s₀.regs.get64 .rcx))
        = BitVec.ofNat 64 st.n.toNat := by
      rw [hcx, hi.1]; apply BitVec.eq_of_toNat_eq; rw [hi.2.2, hn1, BitVec.toNat_ofNat]; omega
    have hst := T_storeTe hm htl st.n.toNat (by omega) (BitVec.setWidth 8 16#64)
    have hld := T_loadTe hm st.n.toNat (by omega)
    have hmT : Hide _ := hm
    have pRB : PLift (RB t₀ s₀) := ⟨hRB⟩
    clear hm hRB
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [AddrIndex.offset64_scale1, Reg64s.get64_set64, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, hrbx, ea, ↓reduceIte] at *
    · rw [hld]; rfl
    all_goals have hP := shA_frPre_te hS (by omega) (BitVec.setWidth 8 16#64) (by decide)
    · have hf := ‹CondCode.le.interp _ = true›
      rw [shA_le_ax _ hax] at hf
      have h0 := of_decide_eq_true hf
      obtain ⟨hsp, hbp, h13, hbx⟩ := pRB.down
      left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
      refine ⟨by decide, ⟨hC, ?_, hdx, hdi, _, ⟨hP, show st.n.toNat ≤ 4 by omega, ?_⟩, hst⟩, by edge_lt⟩
      · simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        exact ⟨hsp, hbp, h13, hbx⟩
      · simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hcx]
        apply BitVec.eq_of_toNat_eq; rw [hi.2.2, BitVec.toNat_setWidth]; omega
    · have hf := ‹CondCode.le.interp _ = false›
      rw [shA_le_ax _ hax] at hf
      have h0 := of_decide_eq_false hf
      obtain ⟨hsp, hbp, h13, hbx⟩ := pRB.down
      refine ⟨⟨hC, ?_, hdx, hdi, _, ⟨hP, by omega, hax, hn1⟩, hst⟩, Nat.le_refl _⟩
      simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      exact ⟨hsp, hbp, h13, hbx⟩

/-- `movzbl t_env[0],%esi`, `r8 = 0`. -/
theorem blk_L4556 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4556" := by
  cfg_block
  measure_hb "L4556"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hRB, hdx, hdi, st, ⟨hP, hax1, hax, hn1⟩, hm⟩, hn⟩ := hs₀
    have hrbx : s₀.regs.get64 .rbx = arg3 t₀ := hRB.2.2.2
    have hld := T_loadTe hm 0 (by omega)
    simp only [BitVec.add_zero] at hld
    have hmT : Hide _ := hm
    have pRB : PLift (RB t₀ s₀) := ⟨hRB⟩
    have e : (BitVec.setWidth 64 (BitVec.setWidth 32 (s₀.regs.get64 .rax))) = s₀.regs.get64 .rax := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth]; omega
    clear hm hRB
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbx] at *
    · rw [hld]; rfl
    · obtain ⟨hsp, hbp, h13, hbx⟩ := pRB.down
      simp only [e, BitVec.xor_self, BitVec.setWidth_zero, BitVec.toNat_zero]
      refine ⟨⟨hC, ?_, hdx, hdi, st, ⟨hP, hax1, hax, hn1, by omega⟩, hmT⟩, by simp only [Nat.add_eq]; omega⟩
      simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      exact ⟨hsp, hbp, h13, hbx⟩

/-- `mov 0x8(%rbx),%ecx`, the check `bs_num_env < 6`. -/
theorem blk_L45bf (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L45bf" := by
  cfg_block
  measure_hb "L45bf"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hRB, hdx, hdi, st, ⟨hP, h2, h4⟩, hm⟩, hn⟩ := hs₀
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
      have hf := ‹CondCode.nc.interp _ = true›
      have : st.n = 2#32 ∨ st.n = 3#32 ∨ st.n = 4#32 := by bv_omega
      rcases this with h | h | h <;> simp only [h] at hf <;> revert hf <;> decide
    · obtain ⟨hsp, hbp, h13, hbx⟩ := pRB.down
      refine ⟨⟨hC, ?_, hdx, hdi, st, ⟨hP, h4, ?_⟩, hmT⟩, Nat.le_refl _⟩
      · simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        exact ⟨hsp, hbp, h13, hbx⟩
      · rfl

/-- `ceil_log2[bs_num_env]`. -/
theorem blk_L45cb (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L45cb" := by
  cfg_block
  measure_hb "L45cb"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hRB, hdx, hdi, st, ⟨hP, h4, hcx⟩, hm⟩, hn⟩ := hs₀
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
      refine ⟨⟨hC, ?_, hdx, hdi, st, ⟨hP, h4⟩, hmT⟩, Nat.le_refl _⟩
      simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      exact ⟨hsp, hbp, h13, hbx⟩

end Kraken.Examples.Sbr.Grid
