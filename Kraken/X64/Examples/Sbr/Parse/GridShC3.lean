import Kraken.X64.Examples.Sbr.Parse.GridShC1
import Kraken.X64.Examples.Sbr.Parse.GridShA3

/-!
# `read_sbr_grid`: the `FIXVAR` body up to the `t_env` loop (class 1)

`bs_var_bord_1`, `bs_num_rel_1` (two `get_bits(gb, 2)`), `bs_num_env = bs_num_rel_1 + 1`,
`t_env[0] = 0`, `t_env[bs_num_env] = 16 + bs_var_bord_1`, and the loop's entry.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Grid

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

/-- FIXVAR: `get_bits(gb, 2)` for `bs_var_bord_1`. -/
theorem blk_L4773 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4773" := by
  cfg_block
  measure_hb "L4773"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hR, hax, h8, h15, h9, st, hD, hm⟩, hn⟩ := hs₀
    have hoff := rd_off ((s₀.regs.get64 .r9).setWidth 32) x.p8 x.L
      (by rw [BitVec.toNat_setWidth]; omega) hC.2.2.2.2.1
    have hbl := T_buf_load hm _ 4 hoff
    have hst := fun i => T_storeI hm i
    have hrdx : s₀.regs.get64 .rdx = arg2 t₀ := hR.1.2.2.2.1
    have hrbx : s₀.regs.get64 .rbx = arg3 t₀ := hR.2
    have ldI := T_loadI hm
    have hmT : Hide _ := hm
    have pR : PLift (Regs t₀ s₀) := ⟨hR⟩
    clear hm hR
    vcgen [bswap32_havoc, shl_cl32_havoc]
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [AddrIndex.offset64_scale1, AddrIndex.offset64_none, Reg64s.get64_set64,
      Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, reduceCtorEq,
      ↓reduceIte, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
      BitVec.ushiftRight_eq, hax, h8, hrdx, hrbx, BitVec.setWidth_32_64_32] at *
    · exact hbl
    · rw [ldI]; rfl
    · obtain ⟨⟨hsp, hbp, h13, -, hdi, -⟩, hbx⟩ := pR.down
      refine ⟨⟨hC, ?_, trivial, hdi, trivial, trivial, gb_clamp64 _ _ _ _, shA_lt4' _, _, hD,
        hst _⟩, Nat.le_refl _⟩
      simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      exact ⟨hsp, hbp, h13, hbx⟩

/-- FIXVAR: `get_bits(gb, 2)` for `bs_num_rel_1`. -/
theorem blk_L4798 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4798" := by
  cfg_block
  measure_hb "L4798"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hRB, hrdx, hdi, hax, h8, h9, hsi, st, hD, hm⟩, hn⟩ := hs₀
    have hoff := rd_off ((s₀.regs.get64 .r9).setWidth 32) x.p8 x.L
      (by rw [BitVec.toNat_setWidth]; omega) hC.2.2.2.2.1
    have hbl := T_buf_load hm _ 4 hoff
    have hst := fun i => T_storeI hm i
    have ldI := T_loadI hm
    have hmT : Hide _ := hm
    have pRB : PLift (RB t₀ s₀) := ⟨hRB⟩
    have psi : PLift ((s₀.regs.get64 .rsi).toNat < 4) := ⟨hsi⟩
    have pdi : PLift (s₀.regs.get64 .rdi = arg0 t₀) := ⟨hdi⟩
    clear hm hRB
    vcgen [bswap32_havoc, shl_cl32_havoc]
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [AddrIndex.offset64_scale1, AddrIndex.offset64_none, Reg64s.get64_set64,
      Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, reduceCtorEq,
      ↓reduceIte, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
      BitVec.ushiftRight_eq, hax, h8, hrdx, BitVec.setWidth_32_64_32] at *
    · exact hbl
    · rw [ldI]; rfl
    · obtain ⟨hsp, hbp, h13, hbx⟩ := pRB.down
      refine ⟨⟨hC, ?_, trivial, pdi.down, _, ⟨shA_sinv_withI hD (gb_clamp _ _ _ _), shA_lt4' _,
        psi.down⟩, hst _⟩, Nat.le_refl _⟩
      simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      exact ⟨hsp, hbp, h13, hbx⟩

/-- FIXVAR: `bs_num_env = bs_num_rel_1 + 1`, `t_env[0] = 0`, the check `< 9`. -/
theorem blk_L47bd (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L47bd" := by
  cfg_block
  measure_hb "L47bd"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hRB, hdx, hdi, st, ⟨hS, hax, hsi⟩, hm⟩, hn⟩ := hs₀
    have htl : st.te.length = 10 := hS.1.2.2.1
    have hsT := fun v w => shC_T_storeTeJ (T_storeN hm v) htl 0 (by omega) 0x15a9c#64 (by decide) w
    have ldN : (s₀.dmem.loadInt (arg3 t₀ + 8#64) 4).isSome = true := by
      rw [T_loadN hm]; rfl
    have ldT := fun v => shC_T_loadTeJ (T_storeN hm v) 0x15a9c#64 (by decide)
    have hrbx : s₀.regs.get64 .rbx = arg3 t₀ := hRB.2.2.2
    have hmT : Hide _ := hm
    have pRB : PLift (RB t₀ s₀) := ⟨hRB⟩
    have hi := shA_inc _ hax
    have hsT' := hsT (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32
      (s₀.regs.get64 .rax + 1#64))))
    clear hm hRB
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbx] at *
    · exact ldN
    · exact ldT _
    · exfalso
      have hf := ‹CondCode.nc.interp _ = true›
      rcases lt4_cases _ hax with h | h | h | h <;> simp only [h] at hf <;> revert hf <;> decide
    · obtain ⟨hsp, hbp, h13, hbx⟩ := pRB.down
      refine ⟨⟨hC, ?_, hdx, hdi, _, ⟨shC_sinvF_setTe (sinvF_n hS _ ?_) 0
        (by omega) _, hax, hsi, hi.2.1, hi.1⟩, hsT' _⟩, Nat.le_refl _⟩
      · simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        exact ⟨hsp, hbp, h13, hbx⟩
      · exact Nat.le_trans (Nat.le_of_eq hi.2.1) (by omega)

omit [CodeEnv] in
theorem shC_v19 (r : BitVec 64) (h : r.toNat < 4) :
    (BitVec.setWidth 8 16#64 + BitVec.setWidth 8 r).toNat ≤ 19 := by
  rcases lt4_cases r h with rfl | rfl | rfl | rfl <;> decide

/-- FIXVAR: `t_env[bs_num_env] = 16 + bs_var_bord_1`; `bs_num_rel_1 = 0` skips the `t_env` loop. -/
theorem blk_L47d3 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L47d3" := by
  cfg_block
  measure_hb "L47d3"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hRB, hdx, hdi, st, ⟨hS, hax, hsi, hn1, hcx⟩, hm⟩, hn⟩ := hs₀
    have hrbx : s₀.regs.get64 .rbx = arg3 t₀ := hRB.2.2.2
    have htl : st.te.length = 10 := hS.2.1
    have hi := shA_inc _ hax
    have ea : BitVec.setWidth 64 (BitVec.setWidth 32 (s₀.regs.get64 .rcx))
        = BitVec.ofNat 64 st.n.toNat := by
      rw [hcx, hi.1]; apply BitVec.eq_of_toNat_eq; rw [hi.2.2, hn1, BitVec.toNat_ofNat]; omega
    have hst := fun v => T_storeTe hm htl st.n.toNat (by omega) v
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
      BitVec.ofNat_eq_ofNat, hrbx, ea, reduceCtorEq, ↓reduceIte, shC_rl8] at *
    · rw [hld]; rfl
    all_goals have hP := shA_frPre_te hS (by omega) _ (shC_v19 _ hsi)
    · have hf := ‹CondCode.le.interp _ = true›
      rw [shA_le_ax _ hax] at hf
      have h0 := of_decide_eq_true hf
      obtain ⟨hsp, hbp, h13, hbx⟩ := pRB.down
      left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
      refine ⟨by decide, ⟨hC, ?_, hdx, hdi, _, ⟨hP, show st.n.toNat ≤ 5 by omega, ?_⟩, hst _⟩,
        by edge_lt⟩
      · simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        exact ⟨hsp, hbp, h13, hbx⟩
      · simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hcx]
        apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_setWidth, hi.2.2]; omega
    · have hf := ‹CondCode.le.interp _ = false›
      rw [shA_le_ax _ hax] at hf
      have h0 := of_decide_eq_false hf
      obtain ⟨hsp, hbp, h13, hbx⟩ := pRB.down
      refine ⟨⟨hC, ?_, hdx, hdi, _, ⟨hP, by omega, hax, hn1, ?_⟩, hst _⟩, Nat.le_refl _⟩
      · simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        exact ⟨hsp, hbp, h13, hbx⟩
      · simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hcx]
        apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_setWidth, hi.2.2]; omega

/-- FIXVAR: `eax = -bs_num_rel_1`, `esi = 0`: the `t_env` loop at step `0`. -/
theorem blk_L47ea (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L47ea" := by
  cfg_block
  measure_hb "L47ea"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hRB, hdx, hdi, st, ⟨hP, hax1, hax, hn1, hcx⟩, hm⟩, hn⟩ := hs₀
    have pm := PLift.up hm
    have pRB : PLift (RB t₀ s₀) := ⟨hRB⟩
    have hmT : Hide _ := hm
    clear hm hRB
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] at *
    obtain ⟨hsp, hbp, h13, hbx⟩ := pRB.down
    refine ⟨⟨hC, ?_, hdx, hdi, st, ⟨hP, _, 0, hax1, hax, by omega, by omega, ?_, ?_, by omega,
      ?_⟩, pm.down⟩, ?_⟩
    · simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      exact ⟨hsp, hbp, h13, hbx⟩
    · rcases lt4_cases _ hax with h | h | h | h <;> rw [h] <;> decide
    · simp only [BitVec.xor_self, BitVec.setWidth_zero]; rfl
    · rw [hcx]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth]
      have := st.n.isLt; omega
    · simp only [BitVec.xor_self, BitVec.setWidth_zero]
      rcases lt4_cases _ hax with h | h | h | h <;> rw [h] <;> decide

end Kraken.Examples.Sbr.Grid
