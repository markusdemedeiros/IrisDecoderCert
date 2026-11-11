import Kraken.X64.Examples.Sbr.Parse.GridMem
import Kraken.X64.Examples.Sbr.Parse.GridShD0

/-!
# `read_sbr_grid`: the tail (shard D, part 1)

The `e_a` reset before the return (`L4f75`) and the `av_assert0` message before `abort`
(`L50e8`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Grid

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

/-- `e_a[0] = -(e_a[1] != num_env_old)`, `e_a[1] = -1`. -/
theorem blk_L4f75 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4f75" := by
  cfg_block
  measure_hb "L4f75"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨hsp, hbp, h13, hbx⟩, st, hP, hm⟩, hn⟩ := hs₀
    have hs := fun v w => T_store_ea1 (T_store_ea0 hm v) w
    have ld := T_load_ea1 hm 4 (Nat.le_refl _)
    have ld0 := T_load_ea0 hm 4 (Nat.le_refl _)
    have ld1 := fun v => T_load_ea1 (T_store_ea0 hm v) 4 (Nat.le_refl _)
    have hmT : Hide _ := hm
    have pbx : PLift (s₀.regs.get64 .rbx = arg3 t₀) := ⟨hbx⟩
    clear hm
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, hbx,
      AddrIndex.offset64_none, BitVec.add_zero] at *
    all_goals try with_reducible exact ld
    all_goals try with_reducible exact ld0
    all_goals try with_reducible exact ld1 _
    exact ⟨⟨hC, ⟨hsp, hbp, h13, pbx.down⟩, st, hP, hs _ _⟩, Nat.le_refl _⟩

/-- `av_log(NULL, AV_LOG_PANIC, "Assertion …")` of `av_assert0`, then `abort`. -/
theorem blk_L50e8 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop) (hAv : AvLogSpec Ext k)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L50e8" := by
  cfg_block
  measure_hb "L50e8"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hsp, h13, st, hS, hm⟩, hn⟩ := hs₀
    obtain ⟨F, hF⟩ := T_ext k Ext x ra t₀ (Saved t₀) st
    rw [hF] at hm
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rsp - 8#64) 8).isSome = true := by
      rw [hsp, BitVec.sub_sub_ofNat]
      exact Block.loadInt_isSome hm (by simp)
    have hpush := fun v => Block.storeInt_val hm (Split.here _ _) v
    have e48 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 48#64 := by
      rw [hsp]; show _ - 40#64 - 8#64 = _; bv_omega
    vcgen [MachineWP.call_proc_spec_at F "av_log" hAv]
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    refine ⟨fun ra' => ⟨⟨?_, trivial⟩, fun s' hpost => ?_⟩, hld⟩
    · rw [e48]; exact hpush _
    · rw [e48] at hpost
      obtain ⟨hsp', -, -, hm'⟩ := hpost
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨⟨hC, ?_, st, ?_⟩, Nat.le_refl _⟩
      · rw [hsp']; bv_omega
      · show T k Ext x ra t₀ (Saved t₀) st _
        exact (congrFun hF s'.dmem).mpr hm'

/-- Storing `t_q[0]`. -/
theorem shD_T_storeTq0 {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : GArgs} {ra : Int64}
    {t₀ : MachineData} {FR : (Mem 64 → Prop) → Mem 64 → Prop} {st : GSt}
    (h : m =⋆ T k Ext x ra t₀ FR st) (hl : st.tq.length = 3) (v : BitVec 8) :
    m.storeInt (arg3 t₀ + 0x15aa6#64) 1 v.toInt =⋆ T k Ext x ra t₀ FR (st.setTq 0 v) := by
  rw [T_tq] at h ⊢
  have := TqB_storeInt h hl 0 (by omega) v
  simp only [BitVec.add_zero] at this
  exact this

/-- `bs_num_noise = 1 + (n > 1)`, `t_q[0] = t_env[0]`. -/
theorem blk_L4efc (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4efc" := by
  cfg_block
  measure_hb "L4efc"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨hsp, hbp, h13, hbx⟩, st, ⟨hS, hL, hTR, hdx⟩, hm⟩, hn⟩ := hs₀
    have hql : st.tq.length = 3 := hS.1.2.2.2.1
    have hs := fun v w => shD_T_storeTq0 (T_storeNn hm v) hql w
    have ldN : (s₀.dmem.loadInt (arg3 t₀ + 0x18#64) 4).isSome = true := by
      rw [T_loadNn hm]; rfl
    have ldQ : ∀ v : BitVec 32, ((s₀.dmem.storeInt (arg3 t₀ + 0x18#64) 4 v.toInt).loadInt
        (arg3 t₀ + 0x15aa6#64) 1).isSome = true := by
      intro v; have := T_loadTq (T_storeNn hm v) 0 (by omega)
      simp only [BitVec.add_zero] at this
      rw [this]; rfl
    have pTR : PLift (TR s₀ st) := ⟨hTR⟩
    have pbx : PLift (s₀.regs.get64 .rbx = arg3 t₀) := ⟨hbx⟩
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, hbx,
      AddrIndex.offset64_none, BitVec.add_zero] at *
    all_goals try simp only [pTR.down.1, hdx, shD_nz_sub, BitVec.xor_self, BitVec.setWidth_zero, shD_rl0,
      shD_sw32_64, BitVec.reduceSetWidth, sw8]
    all_goals try with_reducible exact ldN
    all_goals try with_reducible exact ldQ _
    refine ⟨⟨hC, ⟨?_, ?_, ?_, ?_⟩, _, ⟨shD_tinv_nq hS hL _, ?_, ?_, ?_⟩, hs _ (bv st.te 0)⟩,
      Nat.le_refl _⟩
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    · exact hsp
    · exact hbp
    · exact h13
    · exact pbx.down
    · exact pTR.down
    all_goals by_cases h1 : st.n = 1#32 <;> simp [h1]

end Kraken.Examples.Sbr.Grid
