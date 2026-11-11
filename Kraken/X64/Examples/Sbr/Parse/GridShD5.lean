import Kraken.X64.Examples.Sbr.Parse.GridShD4

/-!
# `read_sbr_grid`: the tail (shard D, part 5)

The border chain `t_env[j] < t_env[j+1]` (`L4fd3` … `L5058`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Grid

theorem shD_monoS {st : GSt} {j : Nat} (h : Mono st j)
    (h' : ¬ (st.te.getD (j + 1) 0).toBitVec.toNat ≤ (st.te.getD j 0).toBitVec.toNat) :
    Mono st (j + 1) :=
  shD_mono_step h (by simp only [u8]; exact Nat.lt_of_not_le h')

theorem shD_sw8_64 (b : BitVec 8) : (b.setWidth 64).setWidth 8 = b := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth]
  have := b.isLt; omega

theorem shD_z_subE {w : Nat} (r : BitVec w) (cf af of : Bool) :
    CondCode.z.interp (StatusFlags.from_result r { cf := cf, af := af, of := of })
      = decide (r = 0#w) := by
  simp only [CondCode.interp, StatusFlags.from_result, BitVec.zero_eq]
  by_cases h : r = 0#w <;> simp [h]

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm



/-- `t_env[1] < t_env[2]`; `bs_num_env == 2` ends the chain. -/
theorem blk_L4fd3 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4fd3" := by
  cfg_block
  measure_hb "L4fd3"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h13, hbx⟩, st, ⟨hS, hj, hM, hTR, hdx, hr⟩, hm⟩, hdi⟩, hn⟩ := hs₀
    have hn8 : st.n.toNat ≤ 8 := hS.1.2.2.2.2.1
    have hb19 := hS.2.1
    have ld := T_loadTe hm 2 (by omega)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at ld
    have ld' : (s₀.dmem.loadInt (arg3 t₀ + 88734#64) 1).isSome = true := by rw [ld]; rfl
    have pTR : PLift (TR s₀ st) := ⟨hTR⟩
    have pbx : PLift (s₀.regs.get64 .rbx = arg3 t₀) := ⟨hbx⟩
    have pdi : PLift (s₀.regs.get64 .rdi = arg0 t₀) := ⟨hdi⟩
    have pdx : PLift (s₀.regs.get64 .rdx = (bv st.te 0).setWidth 64) := ⟨hdx⟩
    have pr : PLift (s₀.regs.get64 .rsi = (bv st.te 1).setWidth 64) := ⟨hr⟩
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
    all_goals try simp only [BitVec.ofInt8_ofBytes_toBytes1, BitVec.ofInt_toInt, zx8,
      pTR.down.2.1, pr.down, shD_sw8_64, shD_sw32_64, BitVec.reduceSetWidth, shD_ae_subw, shD_z_subE, 
      decide_eq_true_eq, decide_eq_false_iff_not] at *
    · left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
      refine ⟨by decide, ⟨⟨hC, ?_, ?_, st, hS, hmT⟩, ?_⟩, by edge_lt⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      all_goals first | exact hsp | exact h13 | exact pdi.down
    · have hlt : ¬ (st.te.getD 2 0).toBitVec.toNat ≤ (st.te.getD 1 0).toBitVec.toNat := by
        assumption
      have hnv : st.n.toNat = 2 := by
        have : st.n + 1#32 - 3#32 = 0#32 := by assumption
        bv_omega
      have hM' : Mono st st.n.toNat := by rw [hnv]; exact shD_monoS (j := 1) hM hlt
      left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
      refine ⟨by decide, ⟨hC, ?_, st, ⟨hS, shD_live_of (by omega) hM' hb19, ⟨?_, ?_, ?_⟩, ?_⟩,
        hmT⟩, by edge_lt⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      all_goals first
        | exact ⟨hsp, hbp, h13, pbx.down⟩
        | exact pTR.down.1
        | exact pTR.down.2.1
        | exact pTR.down.2.2
        | exact pdx.down
        | exact pdi.down
    · have hlt : ¬ (st.te.getD 2 0).toBitVec.toNat ≤ (st.te.getD 1 0).toBitVec.toNat := by
        assumption
      have hj' : 2 + 1 ≤ st.n.toNat := by
        have : ¬ st.n + 1#32 - 3#32 = 0#32 := by assumption
        bv_omega
      refine ⟨⟨⟨hC, ?_, st, ⟨hS, hj', shD_monoS (j := 1) hM hlt, ⟨?_, ?_, ?_⟩, ?_, ?_⟩, hmT⟩, ?_⟩,
        Nat.le_refl _⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      all_goals first
        | exact ⟨hsp, hbp, h13, pbx.down⟩
        | exact pTR.down.1
        | exact pTR.down.2.1
        | exact pTR.down.2.2
        | exact pdx.down
        | exact pdi.down
        | rfl

/-- `t_env[2] < t_env[3]`; `bs_num_env == 3` ends the chain. -/
theorem blk_L4fed (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4fed" := by
  cfg_block
  measure_hb "L4fed"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h13, hbx⟩, st, ⟨hS, hj, hM, hTR, hdx, hr⟩, hm⟩, hdi⟩, hn⟩ := hs₀
    have hn8 : st.n.toNat ≤ 8 := hS.1.2.2.2.2.1
    have hb19 := hS.2.1
    have ld := T_loadTe hm 3 (by omega)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at ld
    have ld' : (s₀.dmem.loadInt (arg3 t₀ + 88735#64) 1).isSome = true := by rw [ld]; rfl
    have pTR : PLift (TR s₀ st) := ⟨hTR⟩
    have pbx : PLift (s₀.regs.get64 .rbx = arg3 t₀) := ⟨hbx⟩
    have pdi : PLift (s₀.regs.get64 .rdi = arg0 t₀) := ⟨hdi⟩
    have pdx : PLift (s₀.regs.get64 .rdx = (bv st.te 0).setWidth 64) := ⟨hdx⟩
    have pr : PLift (s₀.regs.get64 .r9 = (bv st.te 2).setWidth 64) := ⟨hr⟩
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
    all_goals try simp only [BitVec.ofInt8_ofBytes_toBytes1, BitVec.ofInt_toInt, zx8,
      pTR.down.2.1, pr.down, shD_sw8_64, shD_sw32_64, BitVec.reduceSetWidth, shD_ae_subw, shD_z_subE, 
      decide_eq_true_eq, decide_eq_false_iff_not] at *
    · left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
      refine ⟨by decide, ⟨⟨hC, ?_, ?_, st, hS, hmT⟩, ?_⟩, by edge_lt⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      all_goals first | exact hsp | exact h13 | exact pdi.down
    · have hlt : ¬ (st.te.getD 3 0).toBitVec.toNat ≤ (st.te.getD 2 0).toBitVec.toNat := by
        assumption
      have hnv : st.n.toNat = 3 := by
        have : st.n + 1#32 - 4#32 = 0#32 := by assumption
        bv_omega
      have hM' : Mono st st.n.toNat := by rw [hnv]; exact shD_monoS (j := 2) hM hlt
      left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
      refine ⟨by decide, ⟨hC, ?_, st, ⟨hS, shD_live_of (by omega) hM' hb19, ⟨?_, ?_, ?_⟩, ?_⟩,
        hmT⟩, by edge_lt⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      all_goals first
        | exact ⟨hsp, hbp, h13, pbx.down⟩
        | exact pTR.down.1
        | exact pTR.down.2.1
        | exact pTR.down.2.2
        | exact pdx.down
        | exact pdi.down
    · have hlt : ¬ (st.te.getD 3 0).toBitVec.toNat ≤ (st.te.getD 2 0).toBitVec.toNat := by
        assumption
      have hj' : 3 + 1 ≤ st.n.toNat := by
        have : ¬ st.n + 1#32 - 4#32 = 0#32 := by assumption
        bv_omega
      refine ⟨⟨⟨hC, ?_, st, ⟨hS, hj', shD_monoS (j := 2) hM hlt, ⟨?_, ?_, ?_⟩, ?_, ?_⟩, hmT⟩, ?_⟩,
        Nat.le_refl _⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      all_goals first
        | exact ⟨hsp, hbp, h13, pbx.down⟩
        | exact pTR.down.1
        | exact pTR.down.2.1
        | exact pTR.down.2.2
        | exact pdx.down
        | exact pdi.down
        | rfl

/-- `t_env[3] < t_env[4]`; `bs_num_env == 4` ends the chain. -/
theorem blk_L5002 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L5002" := by
  cfg_block
  measure_hb "L5002"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h13, hbx⟩, st, ⟨hS, hj, hM, hTR, hdx, hr⟩, hm⟩, hdi⟩, hn⟩ := hs₀
    have hn8 : st.n.toNat ≤ 8 := hS.1.2.2.2.2.1
    have hb19 := hS.2.1
    have ld := T_loadTe hm 4 (by omega)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at ld
    have ld' : (s₀.dmem.loadInt (arg3 t₀ + 88736#64) 1).isSome = true := by rw [ld]; rfl
    have pTR : PLift (TR s₀ st) := ⟨hTR⟩
    have pbx : PLift (s₀.regs.get64 .rbx = arg3 t₀) := ⟨hbx⟩
    have pdi : PLift (s₀.regs.get64 .rdi = arg0 t₀) := ⟨hdi⟩
    have pdx : PLift (s₀.regs.get64 .rdx = (bv st.te 0).setWidth 64) := ⟨hdx⟩
    have pr : PLift (s₀.regs.get64 .rsi = (bv st.te 3).setWidth 64) := ⟨hr⟩
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
    all_goals try simp only [BitVec.ofInt8_ofBytes_toBytes1, BitVec.ofInt_toInt, zx8,
      pTR.down.2.1, pr.down, shD_sw8_64, shD_sw32_64, BitVec.reduceSetWidth, shD_ae_subw, shD_z_subE, 
      decide_eq_true_eq, decide_eq_false_iff_not] at *
    · left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
      refine ⟨by decide, ⟨⟨hC, ?_, ?_, st, hS, hmT⟩, ?_⟩, by edge_lt⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      all_goals first | exact hsp | exact h13 | exact pdi.down
    · have hlt : ¬ (st.te.getD 4 0).toBitVec.toNat ≤ (st.te.getD 3 0).toBitVec.toNat := by
        assumption
      have hnv : st.n.toNat = 4 := by
        have : st.n + 1#32 - 5#32 = 0#32 := by assumption
        bv_omega
      have hM' : Mono st st.n.toNat := by rw [hnv]; exact shD_monoS (j := 3) hM hlt
      left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
      refine ⟨by decide, ⟨hC, ?_, st, ⟨hS, shD_live_of (by omega) hM' hb19, ⟨?_, ?_, ?_⟩, ?_⟩,
        hmT⟩, by edge_lt⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      all_goals first
        | exact ⟨hsp, hbp, h13, pbx.down⟩
        | exact pTR.down.1
        | exact pTR.down.2.1
        | exact pTR.down.2.2
        | exact pdx.down
        | exact pdi.down
    · have hlt : ¬ (st.te.getD 4 0).toBitVec.toNat ≤ (st.te.getD 3 0).toBitVec.toNat := by
        assumption
      have hj' : 4 + 1 ≤ st.n.toNat := by
        have : ¬ st.n + 1#32 - 5#32 = 0#32 := by assumption
        bv_omega
      refine ⟨⟨⟨hC, ?_, st, ⟨hS, hj', shD_monoS (j := 3) hM hlt, ⟨?_, ?_, ?_⟩, ?_, ?_⟩, hmT⟩, ?_⟩,
        Nat.le_refl _⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      all_goals first
        | exact ⟨hsp, hbp, h13, pbx.down⟩
        | exact pTR.down.1
        | exact pTR.down.2.1
        | exact pTR.down.2.2
        | exact pdx.down
        | exact pdi.down
        | rfl

/-- `t_env[4] < t_env[5]`; `bs_num_env == 5` ends the chain. -/
theorem blk_L5018 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L5018" := by
  cfg_block
  measure_hb "L5018"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h13, hbx⟩, st, ⟨hS, hj, hM, hTR, hdx, hr⟩, hm⟩, hdi⟩, hn⟩ := hs₀
    have hn8 : st.n.toNat ≤ 8 := hS.1.2.2.2.2.1
    have hb19 := hS.2.1
    have ld := T_loadTe hm 5 (by omega)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at ld
    have ld' : (s₀.dmem.loadInt (arg3 t₀ + 88737#64) 1).isSome = true := by rw [ld]; rfl
    have pTR : PLift (TR s₀ st) := ⟨hTR⟩
    have pbx : PLift (s₀.regs.get64 .rbx = arg3 t₀) := ⟨hbx⟩
    have pdi : PLift (s₀.regs.get64 .rdi = arg0 t₀) := ⟨hdi⟩
    have pdx : PLift (s₀.regs.get64 .rdx = (bv st.te 0).setWidth 64) := ⟨hdx⟩
    have pr : PLift (s₀.regs.get64 .r9 = (bv st.te 4).setWidth 64) := ⟨hr⟩
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
    all_goals try simp only [BitVec.ofInt8_ofBytes_toBytes1, BitVec.ofInt_toInt, zx8,
      pTR.down.2.1, pr.down, shD_sw8_64, shD_sw32_64, BitVec.reduceSetWidth, shD_ae_subw, shD_z_subE, 
      decide_eq_true_eq, decide_eq_false_iff_not] at *
    · left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
      refine ⟨by decide, ⟨⟨hC, ?_, ?_, st, hS, hmT⟩, ?_⟩, by edge_lt⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      all_goals first | exact hsp | exact h13 | exact pdi.down
    · have hlt : ¬ (st.te.getD 5 0).toBitVec.toNat ≤ (st.te.getD 4 0).toBitVec.toNat := by
        assumption
      have hnv : st.n.toNat = 5 := by
        have : st.n + 1#32 - 6#32 = 0#32 := by assumption
        bv_omega
      have hM' : Mono st st.n.toNat := by rw [hnv]; exact shD_monoS (j := 4) hM hlt
      left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
      refine ⟨by decide, ⟨hC, ?_, st, ⟨hS, shD_live_of (by omega) hM' hb19, ⟨?_, ?_, ?_⟩, ?_⟩,
        hmT⟩, by edge_lt⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      all_goals first
        | exact ⟨hsp, hbp, h13, pbx.down⟩
        | exact pTR.down.1
        | exact pTR.down.2.1
        | exact pTR.down.2.2
        | exact pdx.down
        | exact pdi.down
    · have hlt : ¬ (st.te.getD 5 0).toBitVec.toNat ≤ (st.te.getD 4 0).toBitVec.toNat := by
        assumption
      have hj' : 5 + 1 ≤ st.n.toNat := by
        have : ¬ st.n + 1#32 - 6#32 = 0#32 := by assumption
        bv_omega
      refine ⟨⟨⟨hC, ?_, st, ⟨hS, hj', shD_monoS (j := 4) hM hlt, ⟨?_, ?_, ?_⟩, ?_, ?_⟩, hmT⟩, ?_⟩,
        Nat.le_refl _⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      all_goals first
        | exact ⟨hsp, hbp, h13, pbx.down⟩
        | exact pTR.down.1
        | exact pTR.down.2.1
        | exact pTR.down.2.2
        | exact pdx.down
        | exact pdi.down
        | rfl

/-- `t_env[5] < t_env[6]`; `bs_num_env == 6` ends the chain. -/
theorem blk_L502d (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L502d" := by
  cfg_block
  measure_hb "L502d"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h13, hbx⟩, st, ⟨hS, hj, hM, hTR, hdx, hr⟩, hm⟩, hdi⟩, hn⟩ := hs₀
    have hn8 : st.n.toNat ≤ 8 := hS.1.2.2.2.2.1
    have hb19 := hS.2.1
    have ld := T_loadTe hm 6 (by omega)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at ld
    have ld' : (s₀.dmem.loadInt (arg3 t₀ + 88738#64) 1).isSome = true := by rw [ld]; rfl
    have pTR : PLift (TR s₀ st) := ⟨hTR⟩
    have pbx : PLift (s₀.regs.get64 .rbx = arg3 t₀) := ⟨hbx⟩
    have pdi : PLift (s₀.regs.get64 .rdi = arg0 t₀) := ⟨hdi⟩
    have pdx : PLift (s₀.regs.get64 .rdx = (bv st.te 0).setWidth 64) := ⟨hdx⟩
    have pr : PLift (s₀.regs.get64 .rsi = (bv st.te 5).setWidth 64) := ⟨hr⟩
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
    all_goals try simp only [BitVec.ofInt8_ofBytes_toBytes1, BitVec.ofInt_toInt, zx8,
      pTR.down.2.1, pr.down, shD_sw8_64, shD_sw32_64, BitVec.reduceSetWidth, shD_ae_subw, shD_z_subE, 
      decide_eq_true_eq, decide_eq_false_iff_not] at *
    · left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
      refine ⟨by decide, ⟨⟨hC, ?_, ?_, st, hS, hmT⟩, ?_⟩, by edge_lt⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      all_goals first | exact hsp | exact h13 | exact pdi.down
    · have hlt : ¬ (st.te.getD 6 0).toBitVec.toNat ≤ (st.te.getD 5 0).toBitVec.toNat := by
        assumption
      have hnv : st.n.toNat = 6 := by
        have : st.n + 1#32 - 7#32 = 0#32 := by assumption
        bv_omega
      have hM' : Mono st st.n.toNat := by rw [hnv]; exact shD_monoS (j := 5) hM hlt
      left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
      refine ⟨by decide, ⟨hC, ?_, st, ⟨hS, shD_live_of (by omega) hM' hb19, ⟨?_, ?_, ?_⟩, ?_⟩,
        hmT⟩, by edge_lt⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      all_goals first
        | exact ⟨hsp, hbp, h13, pbx.down⟩
        | exact pTR.down.1
        | exact pTR.down.2.1
        | exact pTR.down.2.2
        | exact pdx.down
        | exact pdi.down
    · have hlt : ¬ (st.te.getD 6 0).toBitVec.toNat ≤ (st.te.getD 5 0).toBitVec.toNat := by
        assumption
      have hj' : 6 + 1 ≤ st.n.toNat := by
        have : ¬ st.n + 1#32 - 7#32 = 0#32 := by assumption
        bv_omega
      refine ⟨⟨⟨hC, ?_, st, ⟨hS, hj', shD_monoS (j := 5) hM hlt, ⟨?_, ?_, ?_⟩, ?_, ?_⟩, hmT⟩, ?_⟩,
        Nat.le_refl _⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      all_goals first
        | exact ⟨hsp, hbp, h13, pbx.down⟩
        | exact pTR.down.1
        | exact pTR.down.2.1
        | exact pTR.down.2.2
        | exact pdx.down
        | exact pdi.down
        | rfl

/-- `t_env[6] < t_env[7]`; `bs_num_env == 7` ends the chain. -/
theorem blk_L5043 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L5043" := by
  cfg_block
  measure_hb "L5043"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h13, hbx⟩, st, ⟨hS, hj, hM, hTR, hdx, hr⟩, hm⟩, hdi⟩, hn⟩ := hs₀
    have hn8 : st.n.toNat ≤ 8 := hS.1.2.2.2.2.1
    have hb19 := hS.2.1
    have ld := T_loadTe hm 7 (by omega)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at ld
    have ld' : (s₀.dmem.loadInt (arg3 t₀ + 88739#64) 1).isSome = true := by rw [ld]; rfl
    have pTR : PLift (TR s₀ st) := ⟨hTR⟩
    have pbx : PLift (s₀.regs.get64 .rbx = arg3 t₀) := ⟨hbx⟩
    have pdi : PLift (s₀.regs.get64 .rdi = arg0 t₀) := ⟨hdi⟩
    have pdx : PLift (s₀.regs.get64 .rdx = (bv st.te 0).setWidth 64) := ⟨hdx⟩
    have pr : PLift (s₀.regs.get64 .r9 = (bv st.te 6).setWidth 64) := ⟨hr⟩
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
    all_goals try simp only [BitVec.ofInt8_ofBytes_toBytes1, BitVec.ofInt_toInt, zx8,
      pTR.down.2.1, pr.down, shD_sw8_64, shD_sw32_64, BitVec.reduceSetWidth, shD_ae_subw, shD_z_subE, 
      decide_eq_true_eq, decide_eq_false_iff_not] at *
    · left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
      refine ⟨by decide, ⟨⟨hC, ?_, ?_, st, hS, hmT⟩, ?_⟩, by edge_lt⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      all_goals first | exact hsp | exact h13 | exact pdi.down
    · have hlt : ¬ (st.te.getD 7 0).toBitVec.toNat ≤ (st.te.getD 6 0).toBitVec.toNat := by
        assumption
      have hnv : st.n.toNat = 7 := by
        have : st.n + 1#32 - 8#32 = 0#32 := by assumption
        bv_omega
      have hM' : Mono st st.n.toNat := by rw [hnv]; exact shD_monoS (j := 6) hM hlt
      left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
      refine ⟨by decide, ⟨hC, ?_, st, ⟨hS, shD_live_of (by omega) hM' hb19, ⟨?_, ?_, ?_⟩, ?_⟩,
        hmT⟩, by edge_lt⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      all_goals first
        | exact ⟨hsp, hbp, h13, pbx.down⟩
        | exact pTR.down.1
        | exact pTR.down.2.1
        | exact pTR.down.2.2
        | exact pdx.down
        | exact pdi.down
    · have hlt : ¬ (st.te.getD 7 0).toBitVec.toNat ≤ (st.te.getD 6 0).toBitVec.toNat := by
        assumption
      have hj' : 7 + 1 ≤ st.n.toNat := by
        have : ¬ st.n + 1#32 - 8#32 = 0#32 := by assumption
        bv_omega
      refine ⟨⟨⟨hC, ?_, st, ⟨hS, hj', shD_monoS (j := 6) hM hlt, ⟨?_, ?_, ?_⟩, ?_, ?_⟩, hmT⟩, ?_⟩,
        Nat.le_refl _⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      all_goals first
        | exact ⟨hsp, hbp, h13, pbx.down⟩
        | exact pTR.down.1
        | exact pTR.down.2.1
        | exact pTR.down.2.2
        | exact pdx.down
        | exact pdi.down
        | rfl


end Kraken.Examples.Sbr.Grid
