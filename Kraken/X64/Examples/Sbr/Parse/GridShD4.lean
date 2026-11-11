import Kraken.X64.Examples.Sbr.Parse.GridShD3

/-!
# `read_sbr_grid`: the tail (shard D, part 4)

The `bs_pointer` check and the start of the border check (`L4ea2`, `L4ed8`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Grid

/-- `cmp b, a` then `jb` (any width, unsigned). -/
theorem shD_c_subw {w : Nat} (a b : BitVec w) (af of : Bool) :
    CondCode.c.interp (StatusFlags.from_result (a - b)
      { cf := (a - b).unsigned != a.unsigned - b.unsigned, af := af, of := of })
      = decide (a.toNat < b.toNat) := by
  simp only [CondCode.interp, StatusFlags.from_result, BitVec.unsigned]
  by_cases h : a.toNat < b.toNat
  · simp only [h, decide_true, bne_iff_ne, ne_eq]
    rw [BitVec.toNat_sub]; have := a.isLt; have := b.isLt; omega
  · simp only [h, decide_false, bne_eq_false_iff_eq]
    rw [BitVec.toNat_sub]; have := a.isLt; have := b.isLt
    have e : (2 ^ w - b.toNat + a.toNat) % 2 ^ w = a.toNat - b.toNat := by
      rw [show 2 ^ w - b.toNat + a.toNat = (a.toNat - b.toNat) + 2 ^ w by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [e]; omega

/-- `cmp b, a` then `jae` (any width, unsigned). -/
theorem shD_ae_subw {w : Nat} (a b : BitVec w) (af of : Bool) :
    CondCode.ae.interp (StatusFlags.from_result (a - b)
      { cf := (a - b).unsigned != a.unsigned - b.unsigned, af := af, of := of })
      = decide (b.toNat ≤ a.toNat) := by
  have := shD_c_subw a b af of
  simp only [CondCode.interp] at this ⊢
  rw [this]; by_cases h : a.toNat < b.toNat <;> simp [h] <;> omega

/-- `cmp b, a` then `jbe` (any width, unsigned). -/
theorem shD_be_subw {w : Nat} (a b : BitVec w) (af of : Bool) :
    CondCode.be.interp (StatusFlags.from_result (a - b)
      { cf := (a - b).unsigned != a.unsigned - b.unsigned, af := af, of := of })
      = decide (a.toNat ≤ b.toNat) := by
  have := shD_c_subw a b af of
  simp only [CondCode.interp] at this ⊢
  rw [this]
  simp only [StatusFlags.from_result]
  by_cases h : a = b
  · subst h; simp [BitVec.zero_eq]
  · have h' : a - b ≠ BitVec.zero w := by
      intro hc; apply h; rw [BitVec.zero_eq] at hc
      have := congrArg (· + b) hc; simpa [BitVec.sub_add_cancel] using this
    have h'' : a.toNat ≠ b.toNat := fun e => h (BitVec.eq_of_toNat_eq e)
    rw [beq_eq_false_iff_ne.mpr h']
    by_cases h3 : a.toNat < b.toNat <;> simp [h3] <;> omega

theorem shD_lea1 (n : BitVec 32) : (n.setWidth 64 + 1#64).setWidth 32 = n + 1#32 := by
  bv_omega

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

/-- `bs_frame_class` stored; `bs_pointer` checked against `bs_num_env + 1`. -/
theorem blk_L4ea2 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4ea2" := by
  cfg_block
  measure_hb "L4ea2"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h13, hbx⟩, st, ⟨hS, h1⟩, hm⟩, hdi⟩, hn⟩ := hs₀
    have hs := fun v => T_store_cls hm v
    have ldC := T_load_cls hm 4 (Nat.le_refl _)
    have ldN := fun v => T_loadN (T_store_cls hm v)
    have ldA := fun v => T_load_avctx (T_store_cls hm v)
    have ldN' : ∀ v, ((s₀.dmem.storeInt (arg3 t₀) 4 v).loadInt (arg3 t₀ + 8#64) 4).isSome = true :=
      fun v => by rw [ldN]; rfl
    have ldA' : ∀ v, ((s₀.dmem.storeInt (arg3 t₀) 4 v).loadInt (arg0 t₀ + 8#64) 8).isSome = true :=
      fun v => by rw [ldA]; rfl
    have hn8 : st.n.toNat ≤ 8 := hS.1.2.2.2.2.1
    have pbx : PLift (s₀.regs.get64 .rbx = arg3 t₀) := ⟨hbx⟩
    have pdi : PLift (s₀.regs.get64 .rdi = arg0 t₀) := ⟨hdi⟩
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, hbx, hdi,
      AddrIndex.offset64_none, BitVec.add_zero] at *
    all_goals try with_reducible exact ldC
    all_goals try with_reducible exact ldN' _
    all_goals try with_reducible exact ldA' _
    all_goals try simp only [ldN, ldA, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt64_ofBytes_toBytes8,
      BitVec.ofInt_toInt, shD_lea1, shD_sw32_64, shD_be_subw, decide_eq_true_eq] at *
    · left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
      exact ⟨by decide, ⟨hC, hsp, h13, st, hS, hs _⟩, by edge_lt⟩
    · left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
      refine ⟨by decide, ⟨⟨hC, ?_, st, ⟨hS, h1, ?_, ?_, ?_⟩, hs _⟩, ?_⟩, by edge_lt⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      all_goals first
        | exact ⟨hsp, hbp, h13, pbx.down⟩
        | exact pdi.down
        | (have h' : (st.n + 1#32).toNat = st.n.toNat + 1 := by bv_omega
           rw [← h']; assumption)
    · refine ⟨⟨⟨hC, ?_, ?_, st, hS, hs _⟩, ?_⟩, Nat.zero_le _⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      · exact hsp
      · exact h13

omit [CodeEnv] in
theorem shD_mono1 {st : GSt}
    (h : ¬ (st.te.getD 1 0).toBitVec.toNat ≤ (st.te.getD 0 0).toBitVec.toNat) : Mono st 1 := by
  intro e he
  have : e = 0 := by omega
  subst this
  show (st.te.getD 0 0).toBitVec.toNat < (st.te.getD 1 0).toBitVec.toNat
  omega

/-- `bs_num_env ≠ 0`; `t_env[0] < t_env[1]`; `bs_num_env == 1` ends the chain. -/
theorem blk_L4ed8 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4ed8" := by
  cfg_block
  measure_hb "L4ed8"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h13, hbx⟩, st, ⟨hS, h1, hTR⟩, hm⟩, hdi⟩, hn⟩ := hs₀
    have hn8 : st.n.toNat ≤ 8 := hS.1.2.2.2.2.1
    have ld0 := T_loadTe hm 0 (by omega)
    have ld1 := T_loadTe hm 1 (by omega)
    simp only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.zero_add] at ld0 ld1
    have ld0' : (s₀.dmem.loadInt (arg3 t₀ + 88732#64) 1).isSome = true := by rw [ld0]; rfl
    have ld1' : (s₀.dmem.loadInt (arg3 t₀ + 88733#64) 1).isSome = true := by rw [ld1]; rfl
    have pTR : PLift (TR s₀ st) := ⟨hTR⟩
    have pbx : PLift (s₀.regs.get64 .rbx = arg3 t₀) := ⟨hbx⟩
    have pdi : PLift (s₀.regs.get64 .rdi = arg0 t₀) := ⟨hdi⟩
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, hbx,
      AddrIndex.offset64_none, BitVec.add_zero] at *
    all_goals try with_reducible exact ld0'
    all_goals try with_reducible exact ld1'
    all_goals try simp only [ld0, ld1, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt8_ofBytes_toBytes1, BitVec.ofInt_toInt, zx8, sw8,
      pTR.down.1, pTR.down.2.1, shD_sw32_64, shD_z_test, shD_nz_sub, shD_ae_subw,
      BitVec.reduceSetWidth, BitVec.and_self, Bool.not_eq_true', decide_eq_true_eq,
      decide_eq_false_iff_not, beq_iff_eq, beq_eq_false_iff_ne, ne_eq] at *
    · exfalso
      have h0 : st.n = 0#32 := by assumption
      have := congrArg BitVec.toNat h0; simp only [BitVec.toNat_ofNat] at this; omega
    · left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
      refine ⟨by decide, ⟨⟨hC, hsp, h13, st, hS, hmT⟩, ?_⟩, by edge_lt⟩
      try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      exact pdi.down
    · left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
      have h2 : 2 ≤ st.n.toNat := by
        have : ¬ st.n + 1#32 = 2#32 := by assumption
        bv_omega
      have hlt : ¬ (st.te.getD 1 0).toBitVec.toNat ≤ (st.te.getD 0 0).toBitVec.toNat := by
        assumption
      refine ⟨by decide, ⟨⟨hC, ?_, st, ⟨hS, h2, shD_mono1 hlt, ⟨?_, ?_, ?_⟩, ?_, ?_⟩,
        hmT⟩, ?_⟩, by edge_lt⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      all_goals first
        | exact ⟨hsp, hbp, h13, pbx.down⟩
        | exact pTR.down.1
        | exact pTR.down.2.1
        | exact pTR.down.2.2
        | exact pdi.down
        | rfl
    · have hn1 : st.n.toNat = 1 := by
        have h' : (!st.n + 1#32 == 2#32) = false := by assumption
        have : st.n + 1#32 = 2#32 := by simpa using h'
        bv_omega
      have hm1 := shD_mono1 (st := st) (by assumption)
      refine ⟨⟨hC, ?_, st, ⟨hS, shD_live_of h1 (by rw [hn1]; exact hm1) hS.2.1, ⟨?_, ?_, ?_⟩, ?_⟩,
        hmT⟩, ?_⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      all_goals first
        | exact ⟨hsp, hbp, h13, pbx.down⟩
        | exact pTR.down.1
        | exact pTR.down.2.1
        | exact pTR.down.2.2
        | rfl
        | decide
        | omega
        | (simp only [reduceVar] at *; omega)

end Kraken.Examples.Sbr.Grid
