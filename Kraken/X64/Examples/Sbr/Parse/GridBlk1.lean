import Kraken.X64.Examples.Sbr.Parse.GridMem

/-!
# `read_sbr_grid`: the blocks between the prologue and the frame-class dispatch
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Grid

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

/-- `bs_freq_res[0] = bs_freq_res[bs_num_env]`; the word at offset `0x64` gets
`sbr->bs_amp_res_header`. -/
theorem blk_L4422 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4422" := by
  cfg_block
  measure_hb "L4422"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hR, hcx, h14, hax, hm⟩, hn⟩ := hs₀
    have hfl : x.v.freqRes.length = 9 := hC.1.1
    have hs1 : s₀.dmem.storeInt (arg3 t₀ + 12#64) 1 (bv x.v.freqRes x.v.nenv).toInt
        =⋆ T k Ext x ra t₀ (Saved t₀) (st1a x) := by
      rw [T_fr] at hm ⊢
      have := FrB_storeInt hm hfl 0 (by omega) (bv x.v.freqRes x.v.nenv)
      simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, UInt8.ofBitVec_toBitVec] at this
      exact this
    have ld12 : (s₀.dmem.loadInt (arg3 t₀ + 12#64) 1).isSome = true := by
      have hf := hm
      rw [T_fr] at hf
      have := FrB_loadInt hf 0 (by omega)
      simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at this
      simp only [this, Option.isSome_some]
    have ld100 : ((s₀.dmem.storeInt (arg3 t₀ + 12#64) 1 (bv x.v.freqRes x.v.nenv).toInt).loadInt
        (arg3 t₀ + 100#64) 4).isSome = true := by
      obtain ⟨F, hF⟩ := T_x64 k Ext x ra t₀ (Saved t₀) (st1a x)
      have h1 := hs1
      rw [hF] at h1
      exact Block.loadInt_isSome h1 (by rw [BitVec.sub_self, BitVec.toNat_zero]; omega)
    have hamp := T_load_amp hs1
    have hs2 := T_store_x64 hs1
    clear hm hs1
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals simp only [hcx, hax, sw8, Int64.toBitVec_ofNat_norm, BitVec.setWidth_32_64_32]
    · exact ld12
    · rw [hR.1.2.2.2.2.2, hamp]; rfl
    · exact ld100
    · exact ⟨⟨hC, hR, trivial, h14, hs2 _⟩, Nat.le_refl _⟩

/-- `movzbl 0x15a9c(%rcx,%r14,1),%eax`: `t_env[bs_num_env]`, from `TeB_loadInt`. -/
theorem blk_L442b (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L442b" := by
  cfg_block
  measure_hb "L442b"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hR, hcx, h14, hm⟩, hn⟩ := hs₀
    have hn8 : x.v.nenv ≤ 8 := hC.1.2.2.2.2.1
    have hm' := hm
    rw [T_te] at hm'
    have hld := TeB_loadInt hm' x.v.nenv (by omega)
    clear hm'
    simp only [st1a, GArgs.st, bv] at hld
    have hz := zx8
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals grind_cells'

/-- `t_env_num_env_old = t_env[bs_num_env]`. -/
theorem blk_L4434 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4434" := by
  cfg_block
  measure_hb "L4434"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hR, hcx, hax, hm⟩, hn⟩ := hs₀
    have hS := sinv_st1 x hC
    have htl : x.v.te.length = 10 := hC.1.2.2.1
    rw [T_te] at hm
    have hld := TeB_loadInt hm 9 (by omega)
    have hst := TeB_storeInt hm htl 9 (by omega) (x.v.te.getD x.v.nenv 0).toBitVec
    simp only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat,
      UInt8.ofBitVec_toBitVec] at hld hst
    clear hm
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    · simp only [hcx, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, hld, Option.isSome_some]
    · rename_i s
      refine ⟨⟨hC, hR, st1 x, hS, ?_⟩, Nat.le_refl _⟩
      have e8 : BitVec.setWidth 8 (s.regs.get64 Reg64.rax) = (x.v.te.getD x.v.nenv 0).toBitVec := by
        rw [hax]; apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_setWidth]
        have := (x.v.te.getD x.v.nenv 0).toBitVec.isLt
        omega
      simp only [hcx, Int64.toBitVec_ofNat_norm, e8]
      show T k Ext x ra t₀ (Saved t₀) (st1 x) _
      rw [T_te]; exact hst

/-- `get_bits(gb, 2)` for `bs_frame_class` and the check against the jump table's size. -/
theorem blk_L443a (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L443a" := by
  cfg_block
  measure_hb "L443a"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hR, st, ⟨hD, hT, hI⟩, hm⟩, hn⟩ := hs₀
    have hp : x.p8.toNat < 2 ^ 31 := hC.2.2.2.1
    have hoff := rd_off st.i x.p8 x.L hI hC.2.2.2.2.1
    have h30 := shr30_lt
    have hbl := T_buf_load hm _ 4 hoff
    obtain ⟨F, hg⟩ := T_gb hm
    have hst := T_storeI hm
    have hrdx : s₀.regs.get64 .rdx = arg2 t₀ := hR.1.2.2.2.1
    generalize T k Ext x ra t₀ (Saved t₀) st = P at hm
    vcgen [bswap32_havoc, shl_cl32_havoc]
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try refine ⟨⟨hC, ?_, ?_, ?_, ?_, ?_, st, ⟨hD, hT⟩, ?_⟩, ?_⟩
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      AddrIndex.offset64_scale1, AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero,
      Int64.toBitVec_neg_ofNat_norm, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
      BitVec.setWidth_32_64_32] at *
    all_goals try (rw [hrdx]; exact hst _)
    -- the trap edge (`bs_frame_class ≥ 4`) is closed by contradiction
    all_goals try ((first | show Table.ofLabels _ _ _ | show Table.ofLabels _ _ _ ∨ _); exfalso)
    all_goals grind_cells'

end Kraken.Examples.Sbr.Grid
