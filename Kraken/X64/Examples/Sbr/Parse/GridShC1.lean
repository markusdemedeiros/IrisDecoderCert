import Kraken.X64.Examples.Sbr.Parse.GridMem

/-!
# `read_sbr_grid`: the `FIXFIX` body (class 0)

`t_env[e] = e * (16 / n)` for `n ∈ {2, 4, 8}` (unrolled stores), `t_env[n] = 16`.
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
theorem shC_n248 {n : BitVec 32} (h : n.toNat = 2 ∨ n.toNat = 4 ∨ n.toNat = 8) :
    n = 2#32 ∨ n = 4#32 ∨ n = 8#32 := by
  rcases h with h | h | h
  · exact Or.inl (BitVec.eq_of_toNat_eq h)
  · exact Or.inr (Or.inl (BitVec.eq_of_toNat_eq h))
  · exact Or.inr (Or.inr (BitVec.eq_of_toNat_eq h))

theorem blk_L4cfb (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4cfb" := by
  cfg_block
  measure_hb "L4cfb"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hRB, hdx, hdi, st, hFX, hm⟩, hn⟩ := hs₀
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals rename_i hs hc; simp only [hs] at hc ⊢
    all_goals try simp only [RB, reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
    · exfalso
      obtain ⟨-, hn3, -, h8, -⟩ := hFX
      rw [h8] at hc
      rcases shC_n248 hn3 with h | h | h <;> rw [h] at hc <;>
        simp only [AddrIndex.offset64_none, BitVec.add_zero, Int64.toBitVec_ofNat_norm,
          Int64.toBitVec_neg_ofNat_norm, BitVec.ofNat_eq_ofNat,
          BitVec.reduceSetWidth] at hc <;> revert hc <;> decide
    · refine ⟨⟨hC, ?_, ?_, ?_, st, ?_, ?_⟩, ?_⟩
      · exact hRB
      · exact hdx
      · exact hdi
      · exact hFX
      · exact hmT
      · omega

omit [CodeEnv] in
theorem shC_fx_step {x : GArgs} {st : GSt} {r8 r9 rsi : BitVec 64} {j : Nat}
    (h : FX x st r8 r9 rsi j) (hj1 : 1 ≤ j) (hjn : j < st.n.toNat) (v : BitVec 8)
    (hv : v.toNat = j * (16 / st.n.toNat)) : FX x (st.setTe j v) r8 r9 rsi (j + 1) := by
  obtain ⟨⟨hfl, htl, hql, hn8, hnn, hte9, htq, hi, hf0⟩, hn3, -, h8, h9, hsi, ht0, htn, hmid⟩ := h
  have hj9 : j < 10 := by omega
  refine ⟨⟨hfl, by simp only [List.length_set]; exact htl, hql, hn8, hnn, ?_, htq, hi, hf0⟩,
    hn3, (by show j + 1 ≤ st.n.toNat; omega), h8, h9, hsi, ?_, ?_, ?_⟩
  · simp only [u8]; rw [getD_set_ne _ _ _ _ (by omega)]; exact hte9
  · simp only [u8]; rw [getD_set_ne _ _ _ _ (by omega)]; exact ht0
  · simp only [u8]; rw [getD_set_ne _ _ _ _ (by omega)]; exact htn
  · intro e he1 he
    simp only [u8]
    by_cases hej : e = j
    · subst hej
      rw [getD_set_eq _ _ _ (by omega)]
      simp only [UInt8.toNat_ofBitVec]; omega
    · rw [getD_set_ne _ _ _ _ hej]; exact hmid e he1 (by omega)

omit [CodeEnv] in
theorem shC_fx_live {x : GArgs} {st : GSt} {r8 r9 rsi : BitVec 64} {j : Nat}
    (h : FX x st r8 r9 rsi j) (hj : st.n.toNat ≤ j) :
    SInvF x st ∧ 1 ≤ st.n.toNat ∧ (∀ e, e ≤ st.n.toNat → u8 st.te e ≤ 19)
      ∧ (∀ e, e < st.n.toNat → u8 st.te e < u8 st.te (e + 1)) := by
  obtain ⟨hF, hn3, hjn, -, -, -, ht0, htn, hmid⟩ := h
  refine ⟨hF, by omega, ?_, ?_⟩
  · intro e he
    by_cases e0 : e = 0
    · subst e0; omega
    by_cases en : e = st.n.toNat
    · subst en; omega
    have := hmid e (by omega) (by omega)
    rcases hn3 with h | h | h <;> rw [h] at this he <;> omega
  · intro e he
    by_cases en : e + 1 = st.n.toNat
    · rw [en, htn]
      by_cases e0 : e = 0
      · subst e0; omega
      have := hmid e (by omega) (by omega)
      rcases hn3 with h | h | h <;> rw [h] at this en <;> omega
    have h1 := hmid (e + 1) (by omega) (by omega)
    by_cases e0 : e = 0
    · subst e0; rw [ht0]; rcases hn3 with h | h | h <;> rw [h] at h1 <;> omega
    have := hmid e (by omega) (by omega)
    rcases hn3 with h | h | h <;> rw [h] at this h1 <;> omega

theorem shC_T_storeTeJ {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : GArgs} {ra : Int64}
    {t₀ : MachineData} {FR : (Mem 64 → Prop) → Mem 64 → Prop} {st : GSt}
    (h : m =⋆ T k Ext x ra t₀ FR st) (hl : st.te.length = 10) (j : Nat) (hj : j < 10)
    (o : BitVec 64) (ho : o.toNat = 0x15a9c + j) (v : BitVec 8) :
    m.storeInt (arg3 t₀ + o) 1 v.toInt =⋆ T k Ext x ra t₀ FR (st.setTe j v) := by
  have := T_storeTeO (o := o) ⟨by omega, by omega⟩ h hl v
  rwa [show o.toNat - 0x15a9c = j by omega] at this

theorem shC_T_loadTeJ {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : GArgs} {ra : Int64}
    {t₀ : MachineData} {FR : (Mem 64 → Prop) → Mem 64 → Prop} {st : GSt}
    (h : m =⋆ T k Ext x ra t₀ FR st) (o : BitVec 64) (ho : 0x15a9c ≤ o.toNat ∧ o.toNat < 0x15aa6) :
    (m.loadInt (arg3 t₀ + o) 1).isSome = true := by
  rw [T_loadTeO ho h]; rfl

theorem blk_L4d08 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4d08" := by
  cfg_block
  measure_hb "L4d08"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hRB, hdx, hdi, st, hFX, hm⟩, hn⟩ := hs₀
    subst hn
    have htl : st.te.length = 10 := hFX.1.2.1
    have hsT := fun v => shC_T_storeTeJ hm htl 1 (by omega) 0x15a9d#64 (by decide) v
    have ldT := shC_T_loadTeJ hm 0x15a9d#64 (by decide)
    have hbx : s₀.regs.get64 .rbx = arg3 t₀ := hRB.2.2.2
    obtain ⟨-, hn3, -, h8, h9, hsi, -⟩ := id hFX
    have hv : (BitVec.setWidth 8 (s₀.regs.get64 .rsi)).toNat = 1 * (16 / st.n.toNat) := by
      rw [BitVec.toNat_setWidth, hsi]; have := Nat.div_le_self 16 st.n.toNat; omega
    have hF2 := shC_fx_step hFX (by omega) (by rcases hn3 with h | h | h <;> omega) _ hv
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    case vc1 =>
      rename_i hs; simp only [hs, hbx, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat]
      exact ldT
    all_goals rename_i hs hc; simp only [hs] at hc ⊢
    all_goals simp only [hbx, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat]
    all_goals rw [h9] at hc
    · left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
      rcases shC_n248 hn3 with h | h | h <;> rw [h] at hc
      · refine ⟨by decide, ⟨hC, ?_, ?_, ?_, _, shC_fx_live hF2 ?_, hsT _⟩, by edge_lt⟩
        all_goals try simp only [RB, reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
        · exact hRB
        · exact hdx
        · exact hdi
        · show st.n.toNat ≤ 2; rw [h]; decide
      all_goals (exfalso; revert hc; decide)
    · rcases shC_n248 hn3 with h | h | h <;> rw [h] at hc
      · exfalso; revert hc; decide
      all_goals refine ⟨⟨hC, ?_, ?_, ?_, _, ⟨hF2, ?_⟩, hsT _⟩, Nat.le_refl _⟩
      all_goals try simp only [RB, reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
      all_goals first | exact hRB | exact hdx | exact hdi | (show 4 ≤ st.n.toNat; rw [h]; decide)

theorem blk_L4d15 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4d15" := by
  cfg_block
  measure_hb "L4d15"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hRB, hdx, hdi, st, ⟨hFX, hx⟩, hm⟩, hn⟩ := hs₀
    subst hn
    have htl : st.te.length = 10 := hFX.1.2.1
    have hsT := fun v => shC_T_storeTeJ hm htl 2 (by omega) 0x15a9e#64 (by decide) v
    have ldT := shC_T_loadTeJ hm 0x15a9e#64 (by decide)
    have hbx : s₀.regs.get64 .rbx = arg3 t₀ := hRB.2.2.2
    obtain ⟨-, hn3, -, h8, h9, hsi, -⟩ := id hFX
    have hn' : st.n = 4#32 ∨ st.n = 8#32 := by
      rcases shC_n248 hn3 with h | h | h
      · exact absurd hx (by rw [h]; decide)
      · exact Or.inl h
      · exact Or.inr h
    have hrx : True := trivial
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    case vc1 =>
      rename_i hs; simp only [hs, hbx, Int64.toBitVec_ofNat_norm]
      exact ldT
    all_goals rename_i hs hc; simp only [hs] at hc ⊢
    all_goals simp only [hbx, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat]
    all_goals rw [h9] at hc
    all_goals rcases hn' with h | h
    all_goals have hrsi : s₀.regs.get64 .rsi = BitVec.ofNat 64 (16 / st.n.toNat) :=
      BitVec.eq_of_toNat_eq (by rw [hsi, BitVec.toNat_ofNat]; rw [h]; rfl)
    all_goals rw [h] at hc hrsi
    all_goals first
      | (exfalso; revert hc; decide)
      | (left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
         refine ⟨by decide, ⟨hC, ?_, ?_, ?_, _,
           shC_fx_live (shC_fx_step hFX (by omega) (by rw [h]; decide) _ ?_)
             (by show st.n.toNat ≤ 3; rw [h]; decide), hsT _⟩, by edge_lt⟩)
      | (refine ⟨⟨hC, ?_, ?_, ?_, _, ⟨shC_fx_step hFX (by omega) (by rw [h]; decide) _ ?_, ?_⟩,
           hsT _⟩, Nat.le_refl _⟩)
    all_goals try simp only [RB, reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
    all_goals first
      | exact hRB | exact hdx | exact hdi
      | (show 4 ≤ st.n.toNat; rw [h]; decide)
      | (refine ⟨by show st.n.toNat = 8; rw [h]; rfl, ?_⟩; first | (rw [hrx]; rfl) | (rw [hrsi]; rfl))
      | (simp only [AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrsi, h]; decide)
      | skip

theorem blk_L4d24 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4d24" := by
  cfg_block
  measure_hb "L4d24"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hRB, hdx, hdi, st, ⟨hFX, hx⟩, hm⟩, hn⟩ := hs₀
    subst hn
    have htl : st.te.length = 10 := hFX.1.2.1
    have hsT := fun v => shC_T_storeTeJ hm htl 3 (by omega) 0x15a9f#64 (by decide) v
    have ldT := shC_T_loadTeJ hm 0x15a9f#64 (by decide)
    have hbx : s₀.regs.get64 .rbx = arg3 t₀ := hRB.2.2.2
    obtain ⟨-, hn3, -, h8, h9, hsi, -⟩ := id hFX
    have hn' : st.n = 4#32 ∨ st.n = 8#32 := by
      rcases shC_n248 hn3 with h | h | h
      · exact absurd hx (by rw [h]; decide)
      · exact Or.inl h
      · exact Or.inr h
    have hrx : True := trivial
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    case vc1 =>
      rename_i hs; simp only [hs, hbx, Int64.toBitVec_ofNat_norm]
      exact ldT
    all_goals rename_i hs hc; simp only [hs] at hc ⊢
    all_goals simp only [hbx, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat]
    all_goals rw [h9] at hc
    all_goals rcases hn' with h | h
    all_goals have hrsi : s₀.regs.get64 .rsi = BitVec.ofNat 64 (16 / st.n.toNat) :=
      BitVec.eq_of_toNat_eq (by rw [hsi, BitVec.toNat_ofNat]; rw [h]; rfl)
    all_goals rw [h] at hc hrsi
    all_goals first
      | (exfalso; revert hc; decide)
      | (left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
         refine ⟨by decide, ⟨hC, ?_, ?_, ?_, _,
           shC_fx_live (shC_fx_step hFX (by omega) (by rw [h]; decide) _ ?_)
             (by show st.n.toNat ≤ 4; rw [h]; decide), hsT _⟩, by edge_lt⟩)
      | (refine ⟨⟨hC, ?_, ?_, ?_, _, ⟨shC_fx_step hFX (by omega) (by rw [h]; decide) _ ?_, ?_⟩,
           hsT _⟩, Nat.le_refl _⟩)
    all_goals try simp only [RB, reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
    all_goals first
      | exact hRB | exact hdx | exact hdi
      | (show 4 ≤ st.n.toNat; rw [h]; decide)
      | (refine ⟨by show st.n.toNat = 8; rw [h]; rfl, ?_⟩; first | (rw [hrx]; rfl) | (rw [hrsi]; rfl))
      | (simp only [AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrsi, h]; decide)
      | skip

theorem blk_L4d37 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4d37" := by
  cfg_block
  measure_hb "L4d37"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hRB, hdx, hdi, st, ⟨hFX, hx⟩, hm⟩, hn⟩ := hs₀
    subst hn
    have htl : st.te.length = 10 := hFX.1.2.1
    have hsT := fun v => shC_T_storeTeJ hm htl 4 (by omega) 0x15aa0#64 (by decide) v
    have ldT := shC_T_loadTeJ hm 0x15aa0#64 (by decide)
    have hbx : s₀.regs.get64 .rbx = arg3 t₀ := hRB.2.2.2
    obtain ⟨-, hn3, -, h8, h9, hsi, -⟩ := id hFX
    have hn' : st.n = 8#32 := BitVec.eq_of_toNat_eq hx.1
    have hrx : s₀.regs.get64 .rax = 2#64 := BitVec.eq_of_toNat_eq hx.2
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    case vc1 =>
      rename_i hs; simp only [hs, hbx, Int64.toBitVec_ofNat_norm]
      exact ldT
    all_goals rename_i hs hc; simp only [hs] at hc ⊢
    all_goals simp only [hbx, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat]
    all_goals rw [h9] at hc
    all_goals have h := hn'
    all_goals have hrsi : s₀.regs.get64 .rsi = BitVec.ofNat 64 (16 / st.n.toNat) :=
      BitVec.eq_of_toNat_eq (by rw [hsi, BitVec.toNat_ofNat]; rw [h]; rfl)
    all_goals rw [h] at hc hrsi
    all_goals first
      | (exfalso; revert hc; decide)
      | (left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
         refine ⟨by decide, ⟨hC, ?_, ?_, ?_, _,
           shC_fx_live (shC_fx_step hFX (by omega) (by rw [h]; decide) _ ?_)
             (by show st.n.toNat ≤ 5; rw [h]; decide), hsT _⟩, by edge_lt⟩)
      | (refine ⟨⟨hC, ?_, ?_, ?_, _, ⟨shC_fx_step hFX (by omega) (by rw [h]; decide) _ ?_, ?_⟩,
           hsT _⟩, Nat.le_refl _⟩)
    all_goals try simp only [RB, reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
    all_goals first
      | exact hRB | exact hdx | exact hdi
      | (show 4 ≤ st.n.toNat; rw [h]; decide)
      | (refine ⟨by show st.n.toNat = 8; rw [h]; rfl, ?_⟩; first | (rw [hrx]; rfl) | (rw [hrsi]; rfl))
      | (simp only [AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrsi, hrx, h]; decide)
      | skip

theorem blk_L4d4a (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4d4a" := by
  cfg_block
  measure_hb "L4d4a"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hRB, hdx, hdi, st, ⟨hFX, hx⟩, hm⟩, hn⟩ := hs₀
    subst hn
    have htl : st.te.length = 10 := hFX.1.2.1
    have hsT := fun v => shC_T_storeTeJ hm htl 5 (by omega) 0x15aa1#64 (by decide) v
    have ldT := shC_T_loadTeJ hm 0x15aa1#64 (by decide)
    have hbx : s₀.regs.get64 .rbx = arg3 t₀ := hRB.2.2.2
    obtain ⟨-, hn3, -, h8, h9, hsi, -⟩ := id hFX
    have hn' : st.n = 8#32 := BitVec.eq_of_toNat_eq hx.1
    have hrx : s₀.regs.get64 .rax = 2#64 := BitVec.eq_of_toNat_eq hx.2
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    case vc1 =>
      rename_i hs; simp only [hs, hbx, Int64.toBitVec_ofNat_norm]
      exact ldT
    all_goals rename_i hs hc; simp only [hs] at hc ⊢
    all_goals simp only [hbx, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat]
    all_goals rw [h9] at hc
    all_goals have h := hn'
    all_goals have hrsi : s₀.regs.get64 .rsi = BitVec.ofNat 64 (16 / st.n.toNat) :=
      BitVec.eq_of_toNat_eq (by rw [hsi, BitVec.toNat_ofNat]; rw [h]; rfl)
    all_goals rw [h] at hc hrsi
    all_goals first
      | (exfalso; revert hc; decide)
      | (left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
         refine ⟨by decide, ⟨hC, ?_, ?_, ?_, _,
           shC_fx_live (shC_fx_step hFX (by omega) (by rw [h]; decide) _ ?_)
             (by show st.n.toNat ≤ 6; rw [h]; decide), hsT _⟩, by edge_lt⟩)
      | (refine ⟨⟨hC, ?_, ?_, ?_, _, ⟨shC_fx_step hFX (by omega) (by rw [h]; decide) _ ?_, ?_⟩,
           hsT _⟩, Nat.le_refl _⟩)
    all_goals try simp only [RB, reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
    all_goals first
      | exact hRB | exact hdx | exact hdi
      | (show 4 ≤ st.n.toNat; rw [h]; decide)
      | (refine ⟨by show st.n.toNat = 8; rw [h]; rfl, ?_⟩; first | (rw [hrx]; rfl) | (rw [hrsi]; rfl))
      | (simp only [AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrsi, hrx, h]; decide)
      | skip

theorem blk_L4d59 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4d59" := by
  cfg_block
  measure_hb "L4d59"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hRB, hdx, hdi, st, ⟨hFX, hx⟩, hm⟩, hn⟩ := hs₀
    subst hn
    have htl : st.te.length = 10 := hFX.1.2.1
    have hsT := fun v => shC_T_storeTeJ hm htl 6 (by omega) 0x15aa2#64 (by decide) v
    have ldT := shC_T_loadTeJ hm 0x15aa2#64 (by decide)
    have hbx : s₀.regs.get64 .rbx = arg3 t₀ := hRB.2.2.2
    obtain ⟨-, hn3, -, h8, h9, hsi, -⟩ := id hFX
    have hn' : st.n = 8#32 := BitVec.eq_of_toNat_eq hx.1
    have hrx : s₀.regs.get64 .rax = 2#64 := BitVec.eq_of_toNat_eq hx.2
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    case vc1 =>
      rename_i hs; simp only [hs, hbx, Int64.toBitVec_ofNat_norm]
      exact ldT
    all_goals rename_i hs hc; simp only [hs] at hc ⊢
    all_goals simp only [hbx, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat]
    all_goals rw [h9] at hc
    all_goals have h := hn'
    all_goals have hrsi : s₀.regs.get64 .rsi = BitVec.ofNat 64 (16 / st.n.toNat) :=
      BitVec.eq_of_toNat_eq (by rw [hsi, BitVec.toNat_ofNat]; rw [h]; rfl)
    all_goals rw [h] at hc hrsi
    all_goals first
      | (exfalso; revert hc; decide)
      | (left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
         refine ⟨by decide, ⟨hC, ?_, ?_, ?_, _,
           shC_fx_live (shC_fx_step hFX (by omega) (by rw [h]; decide) _ ?_)
             (by show st.n.toNat ≤ 7; rw [h]; decide), hsT _⟩, by edge_lt⟩)
      | (refine ⟨⟨hC, ?_, ?_, ?_, _, ⟨shC_fx_step hFX (by omega) (by rw [h]; decide) _ ?_, ?_⟩,
           hsT _⟩, Nat.le_refl _⟩)
    all_goals try simp only [RB, reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
    all_goals first
      | exact hRB | exact hdx | exact hdi
      | (show 4 ≤ st.n.toNat; rw [h]; decide)
      | (refine ⟨by show st.n.toNat = 8; rw [h]; rfl, ?_⟩; first | (rw [hrx]; rfl) | (rw [hrsi]; rfl))
      | (simp only [AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrsi, hrx, h]; decide)
      | skip

theorem blk_L4d6b (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4d6b" := by
  cfg_block
  measure_hb "L4d6b"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hRB, hdx, hdi, st, ⟨hFX, hx⟩, hm⟩, hn⟩ := hs₀
    subst hn
    have htl : st.te.length = 10 := hFX.1.2.1
    have hsT := fun v => shC_T_storeTeJ hm htl 7 (by omega) 0x15aa3#64 (by decide) v
    have ldT := shC_T_loadTeJ hm 0x15aa3#64 (by decide)
    have hbx : s₀.regs.get64 .rbx = arg3 t₀ := hRB.2.2.2
    obtain ⟨-, hn3, -, h8, h9, hsi, -⟩ := id hFX
    have hn' : st.n = 8#32 := BitVec.eq_of_toNat_eq hx.1
    have hrx : s₀.regs.get64 .rax = 2#64 := BitVec.eq_of_toNat_eq hx.2
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    case vc1 =>
      rename_i hs; simp only [hs, hbx, Int64.toBitVec_ofNat_norm]
      exact ldT
    all_goals rename_i hs hc; simp only [hs] at hc ⊢
    all_goals simp only [hbx, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat]
    all_goals rw [h9] at hc
    all_goals have h := hn'
    all_goals have hrsi : s₀.regs.get64 .rsi = BitVec.ofNat 64 (16 / st.n.toNat) :=
      BitVec.eq_of_toNat_eq (by rw [hsi, BitVec.toNat_ofNat]; rw [h]; rfl)
    all_goals rw [h] at hc hrsi
    all_goals first
      | (exfalso; revert hc; decide)
      | (left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
         refine ⟨by decide, ⟨hC, ?_, ?_, ?_, _,
           shC_fx_live (shC_fx_step hFX (by omega) (by rw [h]; decide) _ ?_)
             (by show st.n.toNat ≤ 8; rw [h]; decide), hsT _⟩, by edge_lt⟩)
      | (refine ⟨⟨hC, ?_, ?_, ?_, _, ⟨shC_fx_step hFX (by omega) (by rw [h]; decide) _ ?_, ?_⟩,
           hsT _⟩, Nat.le_refl _⟩)
    all_goals try simp only [RB, reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
    all_goals first
      | exact hRB | exact hdx | exact hdi
      | (show 4 ≤ st.n.toNat; rw [h]; decide)
      | (refine ⟨by show st.n.toNat = 8; rw [h]; rfl, ?_⟩; first | (rw [hrx]; rfl) | (rw [hrsi]; rfl))
      | (simp only [AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrsi, hrx, h]; decide)
      | skip

omit [CodeEnv] in
theorem shC_sinvF_setTe {x : GArgs} {st : GSt} (h : SInvF x st) (j : Nat) (hj : j < 9)
    (v : BitVec 8) : SInvF x (st.setTe j v) := by
  obtain ⟨hfl, htl, hql, hn, hnn, hte9, htq, hi, hf0⟩ := h
  refine ⟨hfl, ?_, hql, hn, hnn, ?_, htq, hi, hf0⟩
  · simp only [List.length_set]; exact htl
  · simp only [u8]; rw [getD_set_ne _ _ _ _ (by omega)]; exact hte9

omit [CodeEnv] in
theorem shC_fx_setn {x : GArgs} {st : GSt} {r8 r9 rsi : BitVec 64} {j : Nat}
    (h : FX x st r8 r9 rsi j) (j' : Nat) (hj' : st.n.toNat = j') (v : BitVec 8)
    (hv : v.toNat = 16) : FX x (st.setTe j' v) r8 r9 rsi j := by
  subst hj'
  have hF := h.1
  obtain ⟨-, hn3, hjn, h8, h9, hsi, ht0, -, hmid⟩ := h
  have htl := hF.2.1
  refine ⟨shC_sinvF_setTe hF _ (by omega) v, hn3, hjn, h8, h9, hsi, ?_, ?_, ?_⟩
  · simp only [u8]; rw [getD_set_ne _ _ _ _ (by omega)]; exact ht0
  · simp only [u8]; rw [getD_set_eq _ _ _ (by omega)]; simp only [UInt8.toNat_ofBitVec]; omega
  · intro e he1 he
    simp only [u8]; rw [getD_set_ne _ _ _ _ (by omega)]; exact hmid e he1 he

omit [CodeEnv] in
theorem shC_fx_init {x : GArgs} {st : GSt} {r8 r9 rsi : BitVec 64} (j : Nat) (hj : st.n.toNat = j)
    (hF : SInvF x st)
    (hn3 : st.n.toNat = 2 ∨ st.n.toNat = 4 ∨ st.n.toNat = 8) (ht0 : u8 st.te 0 = 0)
    (v : BitVec 8) (hv : v.toNat = 16) (h8 : r8 = st.n.setWidth 64)
    (h9 : r9 = (st.n - 1#32).setWidth 64) (hsi : rsi.toNat = 16 / st.n.toNat) :
    FX x (st.setTe j v) r8 r9 rsi 1 := by
  subst hj
  have htl := hF.2.1
  refine ⟨shC_sinvF_setTe hF _ (by omega) v, hn3, (by show 1 ≤ st.n.toNat; omega), h8, h9, hsi,
    ?_, ?_, fun e he1 he => by omega⟩
  · simp only [u8]; rw [getD_set_ne _ _ _ _ (by omega)]; exact ht0
  · simp only [u8]; rw [getD_set_eq _ _ _ (by omega)]; simp only [UInt8.toNat_ofBitVec]; omega

omit [CodeEnv] in
theorem shC_n1_live {x : GArgs} {st : GSt} (hF : SInvF x st) (hn : st.n = 1#32)
    (ht0 : u8 st.te 0 = 0) (v : BitVec 8) (hv : v.toNat = 16) :
    SInvF x (st.setTe 1 v) ∧ 1 ≤ (st.setTe 1 v).n.toNat
      ∧ (∀ e, e ≤ (st.setTe 1 v).n.toNat → u8 (st.setTe 1 v).te e ≤ 19)
      ∧ (∀ e, e < (st.setTe 1 v).n.toNat → u8 (st.setTe 1 v).te e < u8 (st.setTe 1 v).te (e + 1)) := by
  have htl := hF.2.1
  have hn1 : (st.setTe 1 v).n.toNat = 1 := by show st.n.toNat = 1; rw [hn]; rfl
  have e0 : u8 (st.setTe 1 v).te 0 = 0 := by
    simp only [u8]; rw [getD_set_ne _ _ _ _ (by omega)]; exact ht0
  have e1 : u8 (st.setTe 1 v).te 1 = 16 := by
    simp only [u8]; rw [getD_set_eq _ _ _ (by omega)]; simp only [UInt8.toNat_ofBitVec]; omega
  refine ⟨shC_sinvF_setTe hF 1 (by omega) v, by omega, ?_, ?_⟩
  · intro e he; rw [hn1] at he
    rcases (by omega : e = 0 ∨ e = 1) with rfl | rfl <;> omega
  · intro e he; rw [hn1] at he
    rcases (by omega : e = 0) with rfl; rw [Nat.zero_add, e0, e1]; decide

theorem blk_L4cd7 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4cd7" := by
  cfg_block
  measure_hb "L4cd7"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hR, hax, h8, hb, st, hF, hn, ht0, hm⟩, hnv⟩ := hs₀
    subst hnv
    have htl : st.te.length = 10 := hF.2.1
    have hsJ := fun j hj o ho v => shC_T_storeTeJ hm htl j hj o ho v
    have ldJ := fun o ho => shC_T_loadTeJ hm o ho
    have hbx : s₀.regs.get64 .rbx = arg3 t₀ := hR.2
    have hmT : Hide _ := hm
    have pR : PLift (Regs t₀ s₀) := ⟨hR⟩
    clear hm hR
    rcases lt4_cases _ hax with h | h | h | h <;> rw [h] at h8 hb hn <;>
      simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, BitVec.ofNat_eq_ofNat] at h8 hb hn <;>
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals (have hs : _ = s₀ := ‹_ = s₀›; simp only [hs] at *)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, h, h8, hbx, AddrIndex.offset64_none, AddrIndex.offset64_scale1, Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceSub, BitVec.reduceAdd, BitVec.add_assoc, BitVec.reduceSetWidth, BitVec.reduceUShiftRight, BitVec.reduceToNat]
    all_goals try with_reducible exact ldJ _ (by decide)
    all_goals try (exfalso; have hc := ‹CondCode.z.interp _ = _›
                   simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, h, h8, hbx, AddrIndex.offset64_none, AddrIndex.offset64_scale1, Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceSub, BitVec.reduceAdd, BitVec.add_assoc, BitVec.reduceSetWidth, BitVec.reduceUShiftRight, BitVec.reduceToNat, CondCode.interp, StatusFlags.from_result, BitVec.reduceAnd, BitVec.reduceBEq, BitVec.zero_eq, Bool.true_eq_false, Bool.false_eq_true, beq_self_eq_true, reduceCtorEq] at hc; done)
    · left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
      refine ⟨by decide, ⟨hC, ?_, ?_, ?_, _, shC_n1_live hF hn ht0 _ (by decide),
        hsJ 1 (by decide) _ (by decide) _⟩, by edge_lt⟩
      all_goals try simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      · exact ⟨pR.down.1.1, pR.down.1.2.1, pR.down.1.2.2.1, pR.down.2⟩
      · exact pR.down.1.2.2.2.1
      · exact pR.down.1.2.2.2.2.1
    all_goals
      first
        | refine ⟨⟨hC, ?_, ?_, ?_, _, shC_fx_init 2 ?_ hF ?_ ht0 _ (by decide) ?_ ?_ ?_,
            hsJ 2 (by decide) _ (by decide) _⟩, Nat.le_refl _⟩
        | refine ⟨⟨hC, ?_, ?_, ?_, _, shC_fx_init 4 ?_ hF ?_ ht0 _ (by decide) ?_ ?_ ?_,
            hsJ 4 (by decide) _ (by decide) _⟩, Nat.le_refl _⟩
        | refine ⟨⟨hC, ?_, ?_, ?_, _, shC_fx_init 8 ?_ hF ?_ ht0 _ (by decide) ?_ ?_ ?_,
            hsJ 8 (by decide) _ (by decide) _⟩, Nat.le_refl _⟩
      all_goals try simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      all_goals first
        | exact ⟨pR.down.1.1, pR.down.1.2.1, pR.down.1.2.2.1, pR.down.2⟩
        | exact pR.down.1.2.2.2.1
        | exact pR.down.1.2.2.2.2.1
        | (rw [hn]; decide)
        | (rw [hn]; rfl)

theorem blk_L4d80 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4d80" := by
  cfg_block
  measure_hb "L4d80"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hRB, hdx, hdi, st, ⟨hFX, hx⟩, hm⟩, hn⟩ := hs₀
    subst hn
    have htl : st.te.length = 10 := hFX.1.2.1
    have hsT := fun v => shC_T_storeTeJ hm htl 8 (by omega) 0x15aa4#64 (by decide) v
    have ldT := shC_T_loadTeJ hm 0x15aa4#64 (by decide)
    have hbx : s₀.regs.get64 .rbx = arg3 t₀ := hRB.2.2.2
    obtain ⟨-, hn3, -, h8, h9, hsi, -⟩ := id hFX
    have hn' : st.n = 8#32 := BitVec.eq_of_toNat_eq hx.1
    have hrsi : s₀.regs.get64 .rsi = 2#64 :=
      BitVec.eq_of_toNat_eq (by rw [hsi, hx.1]; rfl)
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals (have hs : _ = s₀ := ‹_ = s₀›; simp only [hs] at *)
    all_goals try simp only [hbx, hrsi, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat,
      Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, BitVec.reduceSetWidth, BitVec.reduceShiftLeft,
      BitVec.reduceToNat, Nat.reduceMod, BitVec.reduceShiftLeftShiftLeft]
    all_goals try with_reducible exact ldT
    refine ⟨⟨hC, ?_, hdx, hdi, _, shC_fx_live (shC_fx_setn hFX 8 hx.1 _ (by decide))
      (by show st.n.toNat ≤ 8; omega), hsT _⟩, Nat.le_refl _⟩
    simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    exact hRB

theorem shC_rl0 (b : BitVec 8) : ((0#64).replaceLow b).setWidth 32 = b.setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.replaceLow, BitVec.toNat_setWidth, BitVec.drop]
  rw [BitVec.toNat_append]; simp

theorem shC_rl8 (v : BitVec 64) (b : BitVec 8) : (v.replaceLow b).setWidth 8 = b := by
  simp only [BitVec.replaceLow]
  ext i hi
  simp only [BitVec.getElem_setWidth, BitVec.getLsbD_setWidth]
  rw [show (v.drop 8).append b = v.drop 8 ++ b from rfl, BitVec.getLsbD_append]
  simp [hi, BitVec.getLsbD_eq_getElem]
  omega

theorem shC_gb1_idx (i p : BitVec 32) (r : BitVec 64) (af : Bool) (hi : i.toNat ≤ p.toNat)
    (hp : p.toNat < 2 ^ 31) :
    (i + BitVec.setWidth 32 ((BitVec.setWidth 64 (BitVec.setWidth 32 r ^^^ BitVec.setWidth 32 r)).replaceLow
      (BitVec.ofNat 8 (CondCode.l.interp (StatusFlags.from_result (i - p)
        { cf := (i - p).unsigned != i.unsigned - p.unsigned, af := af,
          of := (i - p).signed != i.signed - p.signed })).toNat))).toNat ≤ p.toNat :=
  gb1_idx i p (BitVec.setWidth 32 r) _ af hi hp

theorem shC_T_loadFrJ {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : GArgs} {ra : Int64}
    {t₀ : MachineData} {FR : (Mem 64 → Prop) → Mem 64 → Prop} {st : GSt}
    (h : m =⋆ T k Ext x ra t₀ FR st) (o : BitVec 64) (ho : 0xc ≤ o.toNat ∧ o.toNat < 0x15) :
    (m.loadInt (arg3 t₀ + o) 1).isSome = true := by
  rw [T_loadFrO ho h]; rfl

theorem shC_T_storeFrJ {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : GArgs} {ra : Int64}
    {t₀ : MachineData} {FR : (Mem 64 → Prop) → Mem 64 → Prop} {st : GSt}
    (h : m =⋆ T k Ext x ra t₀ FR st) (hl : st.fr.length = 9) (j : Nat) (hj : j < 9)
    (o : BitVec 64) (ho : o.toNat = 0xc + j) (v : BitVec 8) :
    m.storeInt (arg3 t₀ + o) 1 v.toInt =⋆ T k Ext x ra t₀ FR (st.setFr j v) := by
  have := T_storeFrO (o := o) ⟨by omega, by omega⟩ h hl v
  rwa [show o.toNat - 0xc = j by omega] at this

omit [CodeEnv] in
theorem shC_fr1 {x : GArgs} {st : GSt} (hF : SInvF x st) (hL : Live st) (ni : BitVec 32)
    (hni : ni.toNat ≤ x.p8.toNat) (b : BitVec 8) (hb : b.toNat ≤ 1) :
    SInvF x ((st.withI ni).setFr 1 b) ∧ Live ((st.withI ni).setFr 1 b)
      ∧ u8 ((st.withI ni).setFr 1 b).fr 1 ≤ 1 := by
  obtain ⟨hfl, htl, hql, hn, hnn, hte9, htq, hi, hf0⟩ := hF
  refine ⟨⟨by simp only [List.length_set]; exact hfl, htl, hql, hn, hnn, hte9, htq, hni, ?_⟩, hL, ?_⟩
  · simp only [u8]; rw [getD_set_ne _ _ _ _ (by omega)]; exact hf0
  · simp only [u8]; rw [getD_set_eq _ _ _ (by omega)]; simp only [UInt8.toNat_ofBitVec]; omega

theorem blk_L4d8b (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4d8b" := by
  cfg_block
  measure_hb "L4d8b"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hRB, hdx, hdi, st, hL, hm⟩, hn⟩ := hs₀
    subst hn
    have hI : st.i.toNat ≤ x.p8.toNat := hL.1.2.2.2.2.2.2.2.1
    have hoff := rd_off1 st.i x.p8 x.L hI hC.2.2.2.2.1
    have hbl := T_buf_load hm _ 1 hoff
    obtain ⟨F, hg⟩ := T_gb hm
    have pli : PLift (s₀.dmem.loadInt (s₀.regs.get64 .rdx + 8#64) 4
        = some (Int.ofBytes (Int.toBytes 4 st.i.toInt))) := ⟨by rw [hdx]; exact gb_load_idx hg⟩
    have plp : PLift (s₀.dmem.loadInt (s₀.regs.get64 .rdx + 16#64) 4
        = some (Int.ofBytes (Int.toBytes 4 x.p8.toInt))) := ⟨by rw [hdx]; exact gb_load_p8 hg⟩
    have plb : PLift (s₀.dmem.loadInt (s₀.regs.get64 .rdx) 8
        = some (Int.ofBytes (Int.toBytes 8 x.buf.toInt))) := ⟨by rw [hdx]; exact gb_load_buf hg⟩
    have pbx : PLift (s₀.regs.get64 .rbx = arg3 t₀) := ⟨hRB.2.2.2⟩
    have pdx : PLift (s₀.regs.get64 .rdx = arg2 t₀) := ⟨hdx⟩
    have hst := fun v => T_storeI hm v
    have hM := fun ni b => shC_T_storeFrJ (hst ni) hL.1.1 1 (by omega) 13#64 (by decide) b
    have hbx : s₀.regs.get64 .rbx = arg3 t₀ := hRB.2.2.2
    have hmT : Hide _ := hm
    clear hm hg
    vcgen [shl_cl32_havoc]
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals (have hs : _ = s₀ := ‹_ = s₀›; simp only [hs] at *)
    all_goals try simp only [AddrIndex.offset64_scale1, AddrIndex.offset64_none, Reg64s.get64_set64,
      Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, reduceCtorEq,
      ↓reduceIte, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, BitVec.ushiftRight_eq] at *
    all_goals have li := pli.down
    all_goals have lp := plp.down
    all_goals have lb := plb.down
    all_goals try simp only [li, lp, lb, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt64_ofBytes_toBytes8,
      BitVec.ofInt_toInt, BitVec.setWidth_32_64_32] at *
    · exact hbl
    · rw [pdx.down, pbx.down]
      exact shC_T_loadFrJ (hst _) 13#64 (by decide)
    · simp only [Tl, RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, shC_rl8]
      rw [pdx.down, pbx.down]
      dsimp only [At]
      refine ⟨⟨⟨hC, ⟨hRB.1, hRB.2.1, hRB.2.2.1, rfl⟩, _, ?P, hM _ _⟩, hdi, ?R⟩, Nat.le_refl _⟩
      case P =>
        exact shC_fr1 hL.1 ⟨hL.2.1, hL.2.2.1, hL.2.2.2⟩ _
          (shC_gb1_idx st.i x.p8 (s₀.regs.get64 .r8) _ hI hC.2.2.2.1) _
          (by have := shr7_lt (BitVec.setWidth 8 ‹BitVec 64›); omega)
      case R => have := shr7_lt (BitVec.setWidth 8 ‹BitVec 64›); omega

theorem shC_sinv1 {x : GArgs} {st : GSt} (hC : GridC x) (hF : SInvF x st) (hL : Live st)
    (h1 : u8 st.fr 1 ≤ 1) (hn : st.n.toNat < 2) : SInv x st := by
  obtain ⟨⟨-, hil, -, -, -, -, -, hinv, hy, -, -, hidx1, hidx2, hv1, hv2, -⟩, -⟩ := hC
  obtain ⟨hfl, htl, hql, hn8, hnn, hte9, htq, hi, hf0⟩ := hF
  obtain ⟨hn1, hte, -⟩ := hL
  refine ⟨⟨hfl, hil, htl, hql, hn8, ?_, hnn, hinv, hy, hte9, htq, hidx1, hidx2, hv1, hv2,
    fun h => h.elim⟩, hte _ (Nat.le_refl _), hi⟩
  intro e he
  show u8 st.fr e ≤ 1
  rcases (show e = 0 ∨ e = 1 by simp only [GSt.dv] at he; omega) with rfl | rfl
  · exact hf0
  · exact h1

theorem shC_cfb {w : Nat} (a b : BitVec w) (af of : Bool) :
    CondCode.c.interp (StatusFlags.from_result (a - b)
      { cf := (a - b).unsigned != a.unsigned - b.unsigned, af := af, of := of })
      = decide (a.toNat < b.toNat) := by
  simp only [CondCode.interp, StatusFlags.from_result, BitVec.unsigned]
  rw [BitVec.toNat_sub]
  have := a.isLt; have := b.isLt
  by_cases h : a.toNat < b.toNat
  · simp only [h, decide_true, bne_iff_ne, ne_eq]
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  · simp only [h, decide_false, bne_eq_false_iff_eq]
    rw [show 2 ^ w - b.toNat + a.toNat = (a.toNat - b.toNat) + 2 ^ w by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]; omega

theorem blk_L4db6 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4db6" := by
  cfg_block
  measure_hb "L4db6"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨⟨hC, hRB, st, ⟨hF, hL, h1⟩, hm⟩, hdi, hal⟩, hn⟩ := hs₀
    subst hn
    have hbx : s₀.regs.get64 .rbx = arg3 t₀ := hRB.2.2.2
    have pln : PLift (s₀.dmem.loadInt (s₀.regs.get64 .rbx + 8#64) 4
        = some (Int.ofBytes (Int.toBytes 4 st.n.toInt))) := ⟨by rw [hbx]; exact T_loadN hm⟩
    have pm := PLift.up hm
    have pR := PLift.up hRB
    have hn8 : st.n.toNat ≤ 8 := hF.2.2.2.1
    have hn1 : 1 ≤ st.n.toNat := hL.1
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals (have hs : _ = s₀ := ‹_ = s₀›; simp only [hs] at *)
    all_goals try simp only [AddrIndex.offset64_none, Reg64s.get64_set64,
      Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, reduceCtorEq, ↓reduceIte] at *
    all_goals have ln := pln.down
    all_goals try simp only [ln, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt_toInt, shC_cfb,
      BitVec.toNat_setWidth, BitVec.reduceSetWidth, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
      decide_eq_true_eq, decide_eq_false_iff_not, Nat.not_lt] at *
    · have hlt : st.n.toNat < 2 := by have := ‹st.n.toNat % _ < 2›; omega
      left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
      refine ⟨by decide, ⟨⟨hC, ?_, st, ⟨shC_sinv1 hC hF hL h1 hlt, hL⟩, pm.down⟩, hdi⟩, by edge_lt⟩
      simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      exact pR.down
    · have hge : 2 ≤ st.n.toNat := by have := ‹2 ≤ st.n.toNat % _›; omega
      refine ⟨⟨⟨hC, ?_, st, ⟨hF, hL, h1, hge, ?_⟩, pm.down⟩, hdi, hal⟩, Nat.le_refl _⟩
      · simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        exact pR.down
      · simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]

theorem blk_L4dbf (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4dbf" := by
  cfg_block
  measure_hb "L4dbf"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨⟨hC, hRB, st, ⟨hF, hL, h1, h2, hdx⟩, hm⟩, hdi, hal⟩, hn⟩ := hs₀
    subst hn
    have pm := PLift.up hm
    have pR := PLift.up hRB
    have pdx := PLift.up hdx
    have hn8 : st.n.toNat ≤ 8 := hF.2.2.2.1
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals (rename_i hs0 hc; simp only [hs0] at *)
    all_goals try simp only [AddrIndex.offset64_none, Reg64s.get64_set64,
      Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.ofNat_eq_ofNat,
      reduceCtorEq, ↓reduceIte, shC_cfb] at *
    · exfalso
      have hn' : st.n = 2#32 ∨ st.n = 3#32 ∨ st.n = 4#32 ∨ st.n = 5#32 ∨ st.n = 6#32 ∨
          st.n = 7#32 ∨ st.n = 8#32 := by bv_omega
      rw [pdx.down] at hc
      rcases hn' with h | h | h | h | h | h | h <;> rw [h] at hc <;> revert hc <;> decide
    · refine ⟨⟨⟨hC, ?_, st, ⟨hF, hL, h1, h2, ?_⟩, pm.down⟩, hdi, hal⟩, Nat.le_refl _⟩
      · simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        exact pR.down
      · exact pdx.down

theorem blk_L4ddd (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4ddd" := by
  cfg_block
  measure_hb "L4ddd"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨⟨hC, hRB, st, hP, hm⟩, h12⟩, hn⟩ := hs₀
    subst hn
    have pm := PLift.up hm
    have pR := PLift.up hRB
    have p12 := PLift.up h12
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals (have hs : _ = s₀ := ‹_ = s₀›; simp only [hs] at *)
    refine ⟨⟨⟨hC, ?_, st, hP, pm.down⟩, p12.down⟩, Nat.le_refl _⟩
    simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    exact pR.down

theorem blk_L4de0 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4de0" := by
  cfg_block
  measure_hb "L4de0"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨⟨hC, hRB, st, ⟨hS, hL⟩, hm⟩, hdi⟩, hn⟩ := hs₀
    subst hn
    have hbx : s₀.regs.get64 .rbx = arg3 t₀ := hRB.2.2.2
    have pln : PLift (s₀.dmem.loadInt (s₀.regs.get64 .rbx + 8#64) 4
        = some (Int.ofBytes (Int.toBytes 4 st.n.toInt))) := ⟨by rw [hbx]; exact T_loadN hm⟩
    have hsc := fun v => T_store_cls hm v
    have pR := PLift.up hRB
    have hlc : (s₀.dmem.loadInt (arg3 t₀) 4).isSome = true := T_load_cls hm 4 (by omega)
    have pbx := PLift.up hbx
    have hn8 : st.n.toNat ≤ 8 := hS.1.2.2.2.2.1
    have hn1 : 1 ≤ st.n.toNat := hL.1
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals (have hs : _ = s₀ := ‹_ = s₀›; simp only [hs] at *)
    all_goals try simp only [Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
      pbx.down] at *
    · exact hlc
    · rw [T_loadN (hsc _)]; rfl
    have ln := T_loadN (hsc (BitVec.setWidth 32 (s₀.regs.get64 Reg64.r15)).toInt)
    simp only [ln, Option.some.injEq] at *
    subst_vars
    simp only [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt_toInt]
    left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
    refine ⟨by decide, ⟨⟨hC, ?_, st, ⟨hS, hn1, ?_, ?_, ?_⟩, hsc _⟩, ?_⟩, by edge_lt⟩
    all_goals try simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    · exact ⟨pR.down.1, pR.down.2.1, pR.down.2.2.1, pbx.down⟩
    · simp only [AddrIndex.offset64_none, BitVec.add_zero]
      bv_omega
    · simp only [BitVec.xor_self, BitVec.setWidth_zero, BitVec.toNat_zero]
      omega
    · exact hdi

end Kraken.Examples.Sbr.Grid
