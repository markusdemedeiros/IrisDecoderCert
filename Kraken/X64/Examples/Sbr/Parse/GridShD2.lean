import Kraken.X64.Examples.Sbr.Parse.GridShD1

/-!
# `read_sbr_grid`: the tail (shard D, part 2)

`bs_num_noise`, `t_q`.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Grid

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

/-- `t_q[bs_num_noise] = t_env[bs_num_env]`. -/
theorem blk_L4f11 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4f11" := by
  cfg_block
  measure_hb "L4f11"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨hsp, hbp, h13, hbx⟩, st, ⟨hT, hTR, hnn, hsi⟩, hm⟩, hn⟩ := hs₀
    have hn8 : st.n.toNat ≤ 8 := hT.1.2.2.2.2.1
    have hql : st.tq.length = 3 := hT.1.2.2.2.1
    have e : st.n.setWidth 64 = BitVec.ofNat 64 st.n.toNat := by
      apply BitVec.eq_of_toNat_eq; simp
    have ldT := T_loadTe hm st.n.toNat (by omega)
    rw [← e] at ldT
    have hnn0 : st.nn.toNat ≠ 0 := by
      rw [hnn]; split <;> decide
    have hnn3 : st.nn.toNat < 3 := by
      rw [hnn]; split <;> decide
    have ea : s₀.regs.get64 .rsi + arg3 t₀ + 88743#64
        = arg3 t₀ + BitVec.ofNat 64 st.nn.toNat + 0x15aa6#64 := by
      rw [hsi, hnn]; split <;> bv_omega
    have hs := fun v => T_storeTq hm hql st.nn.toNat hnn3 v
    rw [← ea] at hs
    have ldQ := T_loadTq hm st.nn.toNat hnn3
    rw [← ea] at ldQ
    have ldQ' : (s₀.dmem.loadInt (s₀.regs.get64 .rsi + arg3 t₀ + 88743#64) 1).isSome = true := by
      rw [ldQ]; rfl
    have ldT' : (s₀.dmem.loadInt (arg3 t₀ + st.n.setWidth 64 + 88732#64) 1).isSome = true := by
      rw [ldT]; rfl
    have pTR : PLift (TR s₀ st) := ⟨hTR⟩
    have pbx : PLift (s₀.regs.get64 .rbx = arg3 t₀) := ⟨hbx⟩
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [Int64.toBitVec_ofNat_norm, hbx
      ] at *
    all_goals try simp only [pTR.down.1, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte,
      AddrIndex.offset64_scale1, shD_sw32_64, pbx.down] at *
    all_goals try with_reducible exact ldT'
    all_goals try with_reducible exact ldQ'
    all_goals try simp only [ldT, Option.some.injEq] at *
    all_goals try subst_vars
    simp only [BitVec.ofInt8_ofBytes_toBytes1, BitVec.ofInt_toInt, zx8, sw8]
    refine ⟨⟨hC, ⟨?_, ?_, ?_, ?_⟩, _, ⟨shD_tinv_setTq hT _ hnn0 _, ?_, hnn, ?_⟩, hs _⟩, Nat.le_refl _⟩
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    · exact hsp
    · exact hbp
    · exact h13
    · exact pbx.down
    · exact pTR.down
    · show ((st.tq.set st.nn.toNat _).getD st.nn.toNat 0).toNat ≤ 19
      rw [getD_set_eq _ _ _ (by omega)]
      exact hT.2.1.2.1 _ (Nat.le_refl _)

/-- `bs_num_env == 1`: to the `e_a` reset; else to the `t_q[1]` cases. -/
theorem blk_L4f22 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4f22" := by
  cfg_block
  measure_hb "L4f22"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hRB, st, ⟨hT, hTR, hnn, hq⟩, hm⟩, hn⟩ := hs₀
    have pTR : PLift (TR s₀ st) := ⟨hTR⟩
    have pRB : PLift (RB t₀ s₀) := ⟨hRB⟩
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [pTR.down.1, shD_sw32_64, shD_z_sub] at *
    all_goals try simp only [Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.reduceSetWidth,
      beq_iff_eq, beq_eq_false_iff_ne, ne_eq] at *
    all_goals try (left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar])
    · have h1 : st.n = 1#32 := by assumption
      have hn1 : st.nn = 1#32 := by simp [hnn, h1]
      rw [hn1] at hq
      refine ⟨by decide, ⟨hC, pRB.down, st, ⟨shD_dwf_nq hT (by rw [hn1]; decide) hq
        (fun h => by rw [hn1] at h; exact absurd h (by decide)), hT.2.1, hT.2.2⟩, hmT⟩, by edge_lt⟩
    · have h1 : ¬ st.n = 1#32 := by assumption
      have hn2 : st.nn = 2#32 := by simp [hnn, h1]
      rw [hn2] at hq
      have h2 : 2 ≤ st.n.toNat := by
        have := hT.2.1.1
        have : st.n.toNat ≠ 1 := fun h => h1 (BitVec.eq_of_toNat_eq h)
        omega
      exact ⟨⟨hC, pRB.down, st, ⟨⟨hT, hn2, hq, h2⟩, pTR.down⟩, hmT⟩, Nat.le_refl _⟩

/-- Storing `t_q[1]`. -/
theorem shD_T_storeTq1 {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : GArgs} {ra : Int64}
    {t₀ : MachineData} {FR : (Mem 64 → Prop) → Mem 64 → Prop} {st : GSt}
    (h : m =⋆ T k Ext x ra t₀ FR st) (hl : st.tq.length = 3) (v : BitVec 8) :
    m.storeInt (arg3 t₀ + 0x15aa7#64) 1 v.toInt =⋆ T k Ext x ra t₀ FR (st.setTq 1 v) := by
  have := T_storeTq h hl 1 (by omega) v
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at this
  exact this

/-- `t_q[1] = t_env[c]`. -/
theorem blk_L4f65 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4f65" := by
  cfg_block
  measure_hb "L4f65"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨hsp, hbp, h13, hbx⟩, st, ⟨hQ, hc⟩, hm⟩, hn⟩ := hs₀
    have hn8 : st.n.toNat ≤ 8 := hQ.1.1.2.2.2.2.1
    have hql : st.tq.length = 3 := hQ.1.1.2.2.2.1
    have ldT := T_loadTe hm _ (by omega : ((s₀.regs.get64 .rcx).setWidth 32).toNat < 10)
    rw [← shD_sw64_ofNat] at ldT
    have ldT' : (s₀.dmem.loadInt (arg3 t₀ + ((s₀.regs.get64 .rcx).setWidth 32).setWidth 64
        + 88732#64) 1).isSome = true := by rw [ldT]; rfl
    have hs := fun v => shD_T_storeTq1 hm hql v
    have ldQ : (s₀.dmem.loadInt (arg3 t₀ + 0x15aa7#64) 1).isSome = true := by
      have := T_loadTq hm 1 (by omega)
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at this
      rw [this]; rfl
    have pbx : PLift (s₀.regs.get64 .rbx = arg3 t₀) := ⟨hbx⟩
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [Int64.toBitVec_ofNat_norm, Reg64s.get64_set64, 
      ↓reduceIte, AddrIndex.offset64_scale1, 
      pbx.down] at *
    all_goals try with_reducible exact ldT'
    all_goals try with_reducible exact ldQ
    all_goals try simp only [ldT, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt8_ofBytes_toBytes1, BitVec.ofInt_toInt, zx8, sw8]
    refine ⟨⟨hC, ⟨?_, ?_, ?_, ?_⟩, _, shD_tq2_fin hQ _ hc, hs _⟩, Nat.le_refl _⟩
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    · exact hsp
    · exact hbp
    · exact h13
    · exact pbx.down

end Kraken.Examples.Sbr.Grid
