import Kraken.X64.Examples.Sbr.Parse.GridShA2

/-!
# `read_sbr_grid`: VARFIX (class 2), the `t_env` loop (`get_bits(gb, 2)` per relative border)
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
/-- `FrPre` after a store to `t_env[j]`, `j < n`. -/
theorem shA_frPre_te_lt {x : GArgs} {st : GSt} (hP : FrPre x st) (j : Nat) (hj : j < st.n.toNat)
    (v : BitVec 8) : FrPre x (st.setTe j v) := by
  obtain ⟨⟨hfl, htl, hql, hn, hnn, hte9, htq, hi, hf0⟩, h1, hten⟩ := hP
  refine ⟨⟨hfl, by simp only [List.length_set]; exact htl, hql, hn, hnn, ?_, htq, hi, hf0⟩, h1, ?_⟩
  · simp only [u8]; rw [getD_set_ne _ _ _ _ (by omega)]; exact hte9
  · simp only [u8]; rw [getD_set_ne _ _ _ _ (by omega)]; exact hten

omit [CodeEnv] in
theorem shA_ne_succ (a b : BitVec 64) (e : (b + 1#64).toNat = b.toNat + 1)
    (h : a - (b + 1#64) ≠ 0#64) : a.toNat ≠ b.toNat + 1 := by
  intro h'; apply h; rw [← e] at h'; rw [BitVec.eq_of_toNat_eq h', BitVec.sub_self]

omit [CodeEnv] in
theorem shA_eq_succ (a b : BitVec 64) (e : (b + 1#64).toNat = b.toNat + 1)
    (h : a - (b + 1#64) = 0#64) : a.toNat = b.toNat + 1 := by
  rw [← e]; have : a = b + 1#64 := by bv_omega
  rw [this]

omit [CodeEnv] in
theorem shA_frPre_withI {x : GArgs} {st : GSt} (hP : FrPre x st) {i : BitVec 32}
    (hi : i.toNat ≤ x.p8.toNat) : FrPre x (st.withI i) := by
  obtain ⟨⟨hfl, htl, hql, hn, hnn, hte9, htq, -, hf0⟩, h1, hten⟩ := hP
  exact ⟨⟨hfl, htl, hql, hn, hnn, hte9, htq, hi, hf0⟩, h1, hten⟩

/-- `t_env[i+1] = t_env[i] + 2 * tmp + 2`; the loop's back edge. -/
theorem blk_L45a5 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L45a5" := by
  cfg_block
  measure_hb "L45a5"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hRB, hdx, hdi, st, ⟨hP, hax1, hax, hn1, h8⟩, hm⟩, hn⟩ := hs₀
    have hrbx : s₀.regs.get64 .rbx = arg3 t₀ := hRB.2.2.2
    have htl : st.te.length = 10 := hP.1.2.1
    have hst := fun v => T_storeTe hm htl ((s₀.regs.get64 .r8).toNat + 1) (by omega) v
    have hld := T_loadTe hm ((s₀.regs.get64 .r8).toNat + 1) (by omega)
    have ea : arg3 t₀ + s₀.regs.get64 .r8 + 0x15a9d#64
        = arg3 t₀ + BitVec.ofNat 64 ((s₀.regs.get64 .r8).toNat + 1) + 0x15a9c#64 := by
      bv_omega
    have e1 : (s₀.regs.get64 .r8 + 1#64).toNat = (s₀.regs.get64 .r8).toNat + 1 := by
      rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
    have hmT : Hide _ := hm
    have pRB : PLift (RB t₀ s₀) := ⟨hRB⟩
    clear hm hRB
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [AddrIndex.offset64_scale1, Reg64s.get64_set64, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, hrbx, reduceCtorEq, ↓reduceIte] at *
    all_goals try rw [ea]
    · rw [hld]; rfl
    · have hne := (shA_nz _ _).mp ‹_›
      have hne' := shA_ne_succ _ _ e1 hne
      obtain ⟨hsp, hbp, h13, hbx⟩ := pRB.down
      left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      refine ⟨by decide, ⟨hC, ⟨hsp, hbp, h13, hbx⟩, hdx, hdi, _,
        ⟨shA_frPre_te_lt hP _ (by omega) _, hax1, hax, hn1, by rw [e1]; omega⟩, hst _⟩, Or.inl ?_⟩
      simp only [Nat.add_eq]; rw [e1]; omega
    · have heq := (shA_nz_f _ _).mp ‹_›
      have heq' := shA_eq_succ _ _ e1 heq
      obtain ⟨hsp, hbp, h13, hbx⟩ := pRB.down
      refine ⟨⟨hC, ?_, hdx, hdi, _, ⟨shA_frPre_te_lt hP _ (by omega) _,
        show 2 ≤ st.n.toNat by omega, show st.n.toNat ≤ 4 by omega⟩, hst _⟩, by simp only [Nat.add_eq]; omega⟩
      simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      exact ⟨hsp, hbp, h13, hbx⟩

/-- `get_bits(gb, 2)` of a relative border. -/
theorem blk_L4570 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4570" := by
  cfg_block
  measure_hb "L4570"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hRB, hdx, hdi, st, ⟨hP, hax1, hax, hn1, h8⟩, hm⟩, hn⟩ := hs₀
    have hI : st.i.toNat ≤ x.p8.toNat := hP.1.2.2.2.2.2.2.2.1
    have hoff := rd_off st.i x.p8 x.L hI hC.2.2.2.2.1
    have hbl := T_buf_load hm _ 4 hoff
    obtain ⟨F, hg⟩ := T_gb hm
    have pli : PLift (s₀.dmem.loadInt (s₀.regs.get64 .rdx + 8#64) 4
        = some (Int.ofBytes (Int.toBytes 4 st.i.toInt))) := ⟨by rw [hdx]; exact gb_load_idx hg⟩
    have plp : PLift (s₀.dmem.loadInt (s₀.regs.get64 .rdx + 16#64) 4
        = some (Int.ofBytes (Int.toBytes 4 x.p8.toInt))) := ⟨by rw [hdx]; exact gb_load_p8 hg⟩
    have plb : PLift (s₀.dmem.loadInt (s₀.regs.get64 .rdx) 8
        = some (Int.ofBytes (Int.toBytes 8 x.buf.toInt))) := ⟨by rw [hdx]; exact gb_load_buf hg⟩
    have hst := T_storeI hm
    have hmT : Hide _ := hm
    have pRB : PLift (RB t₀ s₀) := ⟨hRB⟩
    clear hm hRB hg
    vcgen [bswap32_havoc, shl_cl32_havoc]
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [AddrIndex.offset64_scale1, AddrIndex.offset64_none, Reg64s.get64_set64,
      Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, reduceCtorEq,
      ↓reduceIte, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, get64_ite, ite_self,
      BitVec.ushiftRight_eq] at *
    all_goals have li := pli.down
    all_goals have lp := plp.down
    all_goals have lb := plb.down
    all_goals try simp only [li, lp, lb, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt64_ofBytes_toBytes8,
      BitVec.ofInt_toInt, BitVec.setWidth_32_64_32] at *
    · exact hbl
    · obtain ⟨hsp, hbp, h13, hbx⟩ := pRB.down
      rw [hdx]
      refine ⟨⟨hC, ?_, rfl, hdi, _, ⟨shA_frPre_withI hP (gb_clamp _ _ _ _), hax1, hax, hn1, h8⟩, hst _⟩,
        Nat.le_refl _⟩
      simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      exact ⟨hsp, hbp, h13, hbx⟩


omit [CodeEnv] in
theorem shA_lt4' (w : BitVec 32) : (BitVec.setWidth 64 (w >>> 30)).toNat < 4 := by
  have := shr30_lt w
  simp only [BitVec.toNat_setWidth]; omega

omit [CodeEnv] in
theorem shA_lt4 (w : BitVec 32) : (BitVec.setWidth 8 (BitVec.setWidth 64 (w >>> 30))).toNat < 4 := by
  have := shr30_lt w
  simp only [BitVec.toNat_setWidth]; omega

omit [CodeEnv] in
theorem shA_sinv_withI {x : GArgs} {st : GSt} (hS : SInvD x st) {i : BitVec 32}
    (hi : i.toNat ≤ x.p8.toNat) : SInv x (st.withI i) := ⟨hS.1, hS.2, hi⟩

omit [CodeEnv] in
/-- `t_env[0] = v` (`v < 4`) and a new reader index keep `SInv`. -/
theorem shA_sinv_te0 {x : GArgs} {st : GSt} (hS : SInvD x st) {i : BitVec 32}
    (hi : i.toNat ≤ x.p8.toNat) (v : BitVec 8) (hv : v.toNat < 4) :
    SInv x ((st.withI i).setTe 0 v) := by
  obtain ⟨⟨hfl, hil, htl, hql, hn8, hfr, hnn, hinv, hy, hte9, htq, hidx1, hidx2, hv1, hv2, -⟩,
    hten⟩ := hS
  simp only [GSt.dv] at hfl htl hql hn8 hfr hnn hte9 htq
  refine ⟨⟨hfl, hil, ?_, hql, hn8, hfr, hnn, hinv, hy, ?_, htq, hidx1, hidx2, hv1, hv2,
    fun h => h.elim⟩, ?_, hi⟩
  · simp only [GSt.dv, List.length_set]; exact htl
  · simp only [GSt.dv, u8]; rw [getD_set_ne _ _ _ _ (by omega)]; exact hte9
  · simp only [u8]
    rw [getD_set_if _ _ _ _ (by omega)]
    split
    · simp; omega
    · exact hten

/-- VARFIX: `get_bits(gb, 2)` for `t_env[0]`. -/
theorem blk_L44e3 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L44e3" := by
  cfg_block
  measure_hb "L44e3"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hR, hax, h8, h15, h9, st, hD, hm⟩, hn⟩ := hs₀
    have hoff := rd_off ((s₀.regs.get64 .r9).setWidth 32) x.p8 x.L
      (by rw [BitVec.toNat_setWidth]; omega) hC.2.2.2.2.1
    have hbl := T_buf_load hm _ 4 hoff
    have htl : st.te.length = 10 := hD.1.2.2.1
    have hst := fun i v => T_storeTe (T_storeI hm i) htl 0 (by omega) v
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at hst
    have hrdx : s₀.regs.get64 .rdx = arg2 t₀ := hR.1.2.2.2.1
    have hrbx : s₀.regs.get64 .rbx = arg3 t₀ := hR.2
    have ldI := T_loadI hm
    have ldT := fun i => T_loadTe (T_storeI hm i) 0 (by omega)
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at ldT
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
    · rw [ldT]; rfl
    · obtain ⟨⟨hsp, hbp, h13, -, hdi, -⟩, hbx⟩ := pR.down
      refine ⟨⟨hC, ?_, trivial, ?_, _, shA_sinv_te0 hD (gb_clamp _ _ _ _) _ (shA_lt4 _), hst _ _⟩,
        Nat.le_refl _⟩
      · simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        exact ⟨hsp, hbp, h13, hbx⟩
      · exact hdi

/-- VARFIX: `get_bits(gb, 2)` for `bs_num_rel_0`. -/
theorem blk_L450e (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L450e" := by
  cfg_block
  measure_hb "L450e"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hRB, hdx, hdi, st, hS, hm⟩, hn⟩ := hs₀
    have hI : st.i.toNat ≤ x.p8.toNat := hS.2.2
    have hoff := rd_off st.i x.p8 x.L hI hC.2.2.2.2.1
    have hbl := T_buf_load hm _ 4 hoff
    obtain ⟨F, hg⟩ := T_gb hm
    have pli : PLift (s₀.dmem.loadInt (s₀.regs.get64 .rdx + 8#64) 4
        = some (Int.ofBytes (Int.toBytes 4 st.i.toInt))) := ⟨by rw [hdx]; exact gb_load_idx hg⟩
    have plp : PLift (s₀.dmem.loadInt (s₀.regs.get64 .rdx + 16#64) 4
        = some (Int.ofBytes (Int.toBytes 4 x.p8.toInt))) := ⟨by rw [hdx]; exact gb_load_p8 hg⟩
    have plb : PLift (s₀.dmem.loadInt (s₀.regs.get64 .rdx) 8
        = some (Int.ofBytes (Int.toBytes 8 x.buf.toInt))) := ⟨by rw [hdx]; exact gb_load_buf hg⟩
    have hst := T_storeI hm
    have hmT : Hide _ := hm
    have pRB : PLift (RB t₀ s₀) := ⟨hRB⟩
    clear hm hRB hg
    vcgen [bswap32_havoc, shl_cl32_havoc]
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [AddrIndex.offset64_scale1, AddrIndex.offset64_none, Reg64s.get64_set64,
      Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, reduceCtorEq,
      ↓reduceIte, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, get64_ite, ite_self,
      BitVec.ushiftRight_eq] at *
    all_goals have li := pli.down
    all_goals have lp := plp.down
    all_goals have lb := plb.down
    all_goals try simp only [li, lp, lb, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt64_ofBytes_toBytes8,
      BitVec.ofInt_toInt, BitVec.setWidth_32_64_32] at *
    · exact hbl
    · obtain ⟨hsp, hbp, h13, hbx⟩ := pRB.down
      rw [hdx]
      refine ⟨⟨hC, ?_, rfl, hdi, _, ⟨shA_sinv_withI ⟨hS.1, hS.2.1⟩ (gb_clamp _ _ _ _), shA_lt4' _⟩, hst _⟩,
        Nat.le_refl _⟩
      simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      exact ⟨hsp, hbp, h13, hbx⟩


end Kraken.Examples.Sbr.Grid
