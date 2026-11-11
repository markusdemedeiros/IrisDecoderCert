import Kraken.X64.Examples.Sbr.Parse.GridShB2

/-!
# `read_sbr_grid`: `VARVAR` (class 3), the first `t_env` loop

The unrolled `t_env[i + 1] = t_env[i] + 2 * get_bits(gb, 2) + 2` for `i < bs_num_rel_0`
(`bs_num_rel_0 ≤ 3`; the steps past `3` are not reached).
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
/-- The zero flag of a result. -/
theorem shB_z {w : Nat} (v : BitVec w) (f : StatusFlags.from_result.Remaining) :
    CondCode.z.interp (StatusFlags.from_result v f) = (v == BitVec.zero w) := by
  simp only [CondCode.interp, StatusFlags.from_result]

omit [CodeEnv] in
/-- The carry flag of `cmp`: unsigned below. -/
theorem shB_c_sub {w : Nat} (a c : BitVec w) (af of : Bool) :
    CondCode.c.interp (StatusFlags.from_result (a - c)
      { cf := (a - c).unsigned != a.unsigned - c.unsigned, af := af, of := of })
      = decide (a.toNat < c.toNat) := by
  simp only [CondCode.interp, StatusFlags.from_result, BitVec.unsigned]
  have := a.isLt; have := c.isLt
  by_cases h : a.toNat < c.toNat
  · simp only [h, decide_true, bne_iff_ne, ne_eq]; omega
  · rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)]
    simp only [h, decide_false, bne_eq_false_iff_eq]; omega

omit [CodeEnv] in
theorem shB_nc_sub {w : Nat} (a c : BitVec w) (af of : Bool) :
    CondCode.nc.interp (StatusFlags.from_result (a - c)
      { cf := (a - c).unsigned != a.unsigned - c.unsigned, af := af, of := of })
      = decide (c.toNat ≤ a.toNat) := by
  have := shB_c_sub a c af of
  simp only [CondCode.interp] at this ⊢
  rw [this]; by_cases h : a.toNat < c.toNat <;> simp [h] <;> omega

omit [CodeEnv] in
/-- `FrPre` after a `t_env[j]` store below `bs_num_env` (`j ≠ 9`). -/
theorem shB_frpre_te {x : GArgs} {st : GSt} {j : Nat} {w : BitVec 8} (h : FrPre x st)
    (hj : j ≠ st.n.toNat) (hj9 : j < 9) : FrPre x (st.setTe j w) := by
  obtain ⟨⟨hfl, htl, hql, hn8, hnn, hte9, htq, hi, hf0⟩, h1, hten⟩ := h
  refine ⟨⟨hfl, ?_, hql, hn8, hnn, ?_, htq, hi, hf0⟩, h1, ?_⟩
  · simp only [List.length_set]; exact htl
  · simp only [u8] at *; rw [getD_set_ne _ _ _ _ (by omega)]; exact hte9
  · simp only [u8] at *; rw [getD_set_ne _ _ _ _ (by omega)]; exact hten

omit [CodeEnv] in
theorem shB_frpre_i {x : GArgs} {st : GSt} {i : BitVec 32} (h : FrPre x st)
    (hi : i.toNat ≤ x.p8.toNat) : FrPre x (st.withI i) :=
  ⟨⟨h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2.1, h.1.2.2.2.2.1, h.1.2.2.2.2.2.1, h.1.2.2.2.2.2.2.1, hi,
    h.1.2.2.2.2.2.2.2.2⟩, h.2⟩

omit [CodeEnv] in
/-- `cmp $K, %r32` sets the zero flag iff the register (small) is `K`. -/
theorem shB_eqK (v : BitVec 64) (K : Nat) (hv : v.toNat < 2 ^ 31) (hK : K < 2 ^ 31) :
    (BitVec.setWidth 32 v - BitVec.setWidth 32 (BitVec.ofNat 64 K) = BitVec.zero 32) ↔ v.toNat = K := by
  change _ = 0#32 ↔ _
  have : (BitVec.ofNat 64 K).toNat = K := by rw [BitVec.toNat_ofNat]; omega
  constructor <;> intro h <;> bv_omega

/-- `get_bits(gb, 2)` for `t_env[1]` (the index store is in the next block). -/
theorem blk_L4948 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4948" := by
  cfg_block
  measure_hb "L4948"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hR, hdx, hdi, st, ⟨hF, h5, hs1, hsi, hax, hn⟩, hm⟩, hv⟩ := hs₀
    have hI : st.i.toNat ≤ x.p8.toNat := hF.1.2.2.2.2.2.2.2.1
    have hoff := rd_off st.i x.p8 x.L hI hC.2.2.2.2.1
    have hbl := T_buf_load hm _ 4 hoff
    have hli := T_loadI hm
    have hgl := T_gbl hm
    have pR : PLift (RB t₀ s₀) := ⟨hR⟩
    have pdi : PLift (s₀.regs.get64 .rdi = arg0 t₀) := ⟨hdi⟩
    have pdx : PLift (s₀.regs.get64 .rdx = arg2 t₀) := ⟨hdx⟩
    have hmT : Hide _ := hm
    clear hm
    vcgen [bswap32_havoc, shl_cl32_havoc]
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      AddrIndex.offset64_scale1, AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
      hdx, BitVec.setWidth_32_64_32] at *
    all_goals try simp only [hli, hgl.1, hgl.2, Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt64_ofBytes_toBytes8,
      BitVec.ofInt_toInt, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] at *
    all_goals try exact hbl
    refine ⟨⟨hC, ?_, ?_, ?_, st, ⟨hF, h5, ?_, ?_, ?_, ?_, gb_clamp64 _ _ _ _⟩, hmT⟩, Nat.le_refl _⟩
    all_goals try simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    all_goals first | done | trivial | exact pR.down | exact pdx.down | exact pdi.down | exact hs1 | exact hsi | exact hax | exact hn

/-- `t_env[1] = t_env[0] + 2 * bits + 2`, the index store, `bs_num_rel_0 == 1`. -/
theorem blk_L4979 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4979" := by
  cfg_block
  measure_hb "L4979"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hR, hdx, hdi, st, ⟨hF, h5, hs1, hsi, hax, hn, h9⟩, hm⟩, hv⟩ := hs₀
    have htl : st.te.length = 10 := hF.1.2.1
    have pst : PLift (∀ (v : BitVec 32) (w : BitVec 8),
        ((s₀.dmem.storeInt (arg2 t₀ + 8#64) 4 v.toInt).storeInt (arg3 t₀ + 0x15a9d#64) 1 w.toInt)
          =⋆ T k Ext x ra t₀ (Saved t₀) ((st.withI v).setTe 1 w)) := ⟨fun v w => by
      have := T_storeTeO (o := 0x15a9d#64) (by decide) (T_storeI hm v) (st := st.withI v) htl w
      exact this⟩
    have hl0 := T_loadTeO (o := 0x15a9c#64) (by decide) hm
    have hli := T_loadI hm
    have hl1 : ∀ v : BitVec 32, ((s₀.dmem.storeInt (arg2 t₀ + 8#64) 4 v.toInt).loadInt
        (arg3 t₀ + 0x15a9d#64) 1).isSome := fun v => by
      rw [T_loadTeO (o := 0x15a9d#64) (by decide) (T_storeI hm v)]; rfl
    have pF : PLift (∀ v : BitVec 32, v.toNat ≤ x.p8.toNat → ∀ w : BitVec 8,
        FrPre x ((st.withI v).setTe 1 w)) :=
      ⟨fun v hv w => shB_frpre_te (shB_frpre_i hF hv) (by show 1 ≠ st.n.toNat; omega) (by omega)⟩
    have pR : PLift (RB t₀ s₀) := ⟨hR⟩
    have pdi : PLift (s₀.regs.get64 .rdi = arg0 t₀) := ⟨hdi⟩
    have pdx : PLift (s₀.regs.get64 .rdx = arg2 t₀) := ⟨hdx⟩
    have hrbx : s₀.regs.get64 .rbx = arg3 t₀ := hR.2.2.2
    have hsi31 : (s₀.regs.get64 .rsi).toNat < 2 ^ 31 := by omega
    clear hm
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      AddrIndex.offset64_scale1, AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
      hdx, hrbx] at *
    all_goals try simp only [hl0, hli, Option.isSome_some] at *
    all_goals try exact hl1 _
    all_goals try simp only [shB_z, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, shB_eqK _ 1 hsi31 (by decide)] at *
    · left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
      refine ⟨by decide, ⟨hC, ?_, ?_, ?_, _, ⟨pF.down _ ?_ _, ?_, ?_, ?_⟩, pst.down _ _⟩, by edge_lt⟩
      all_goals try simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      all_goals first | done | trivial | exact pR.down | exact pdx.down | exact pdi.down | exact hax | (simp only [BitVec.toNat_setWidth]; omega) | (change st.n.toNat ≤ 5; exact h5) | (change _ ≤ st.n.toNat; omega)
    · refine ⟨⟨hC, ?_, ?_, ?_, _, ⟨pF.down _ ?_ _, ?_, ?_, hsi, hax, ?_⟩, pst.down _ _⟩, Nat.le_refl _⟩
      all_goals try simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      all_goals first | done | trivial | exact pR.down | exact pdx.down | exact pdi.down | exact hax | exact hn | (simp only [BitVec.toNat_setWidth]; omega) | (change st.n.toNat ≤ 5; exact h5) | omega

/-- `get_bits(gb, 2)` for `t_env[2]`. -/
theorem blk_L499b (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L499b" := by
  cfg_block
  measure_hb "L499b"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hR, hdx, hdi, st, ⟨hF, h5, hs2, hsi, hax, hn⟩, hm⟩, hv⟩ := hs₀
    have hI : st.i.toNat ≤ x.p8.toNat := hF.1.2.2.2.2.2.2.2.1
    have hoff := rd_off st.i x.p8 x.L hI hC.2.2.2.2.1
    have hbl := T_buf_load hm _ 4 hoff
    have hli := T_loadI hm
    have hgl := T_gbl hm
    have pst : PLift (∀ v : BitVec 32, s₀.dmem.storeInt (arg2 t₀ + 8#64) 4 v.toInt
        =⋆ T k Ext x ra t₀ (Saved t₀) (st.withI v)) := ⟨fun v => T_storeI hm v⟩
    have pR : PLift (RB t₀ s₀) := ⟨hR⟩
    have pdi : PLift (s₀.regs.get64 .rdi = arg0 t₀) := ⟨hdi⟩
    have pdx : PLift (s₀.regs.get64 .rdx = arg2 t₀) := ⟨hdx⟩
    clear hm
    vcgen [bswap32_havoc, shl_cl32_havoc]
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      AddrIndex.offset64_scale1, AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
      hdx, BitVec.setWidth_32_64_32] at *
    all_goals try simp only [hli, hgl.1, hgl.2, Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt64_ofBytes_toBytes8,
      BitVec.ofInt_toInt, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] at *
    all_goals try exact hbl
    refine ⟨⟨hC, ?_, ?_, ?_, ?_⟩, Nat.le_refl _⟩
    · simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      exact pR.down
    · trivial
    · exact pdi.down
    · refine ⟨st.withI _, ?_, pst.down _⟩
      exact ⟨shB_frpre_i hF (gb_clamp _ _ _ _), h5, hs2, hsi, hax, hn⟩

/-- `get_bits(gb, 2)` for `t_env[3]`. -/
theorem blk_L49e9 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L49e9" := by
  cfg_block
  measure_hb "L49e9"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hR, hdx, hdi, st, ⟨hF, h5, hs3, hax, hn⟩, hm⟩, hv⟩ := hs₀
    have hI : st.i.toNat ≤ x.p8.toNat := hF.1.2.2.2.2.2.2.2.1
    have hoff := rd_off st.i x.p8 x.L hI hC.2.2.2.2.1
    have hbl := T_buf_load hm _ 4 hoff
    have hli := T_loadI hm
    have hgl := T_gbl hm
    have pst : PLift (∀ v : BitVec 32, s₀.dmem.storeInt (arg2 t₀ + 8#64) 4 v.toInt
        =⋆ T k Ext x ra t₀ (Saved t₀) (st.withI v)) := ⟨fun v => T_storeI hm v⟩
    have pR : PLift (RB t₀ s₀) := ⟨hR⟩
    have pdi : PLift (s₀.regs.get64 .rdi = arg0 t₀) := ⟨hdi⟩
    have pdx : PLift (s₀.regs.get64 .rdx = arg2 t₀) := ⟨hdx⟩
    clear hm
    vcgen [bswap32_havoc, shl_cl32_havoc]
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      AddrIndex.offset64_scale1, AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
      hdx, BitVec.setWidth_32_64_32] at *
    all_goals try simp only [hli, hgl.1, hgl.2, Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt64_ofBytes_toBytes8,
      BitVec.ofInt_toInt, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] at *
    all_goals try exact hbl
    refine ⟨⟨hC, ?_, ?_, ?_, ?_⟩, Nat.le_refl _⟩
    · simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      exact pR.down
    · trivial
    · exact pdi.down
    · refine ⟨st.withI _, ?_, pst.down _⟩
      exact ⟨shB_frpre_i hF (gb_clamp _ _ _ _), h5, hs3, hax, hn⟩


/-- `t_env[2] = …` store; `cmp $2,%esi; je L4bb9`. -/
theorem blk_L49cf (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L49cf" := by
  cfg_block
  measure_hb "L49cf"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hR, hdx, hdi, st, ⟨hF, h5, hs2, hsi, hax, hn⟩, hm⟩, hv⟩ := hs₀
    have htl : st.te.length = 10 := hF.1.2.1
    have pst : PLift (∀ (w : BitVec 8),
        s₀.dmem.storeInt (arg3 t₀ + 0x15a9e#64) 1 w.toInt
          =⋆ T k Ext x ra t₀ (Saved t₀) (st.setTe 2 w)) := ⟨fun w => by
      have := T_storeTeO (o := 0x15a9e#64) (by decide) hm htl w
      exact this⟩
    have hl1 : (s₀.dmem.loadInt (arg3 t₀ + 0x15a9e#64) 1).isSome := by
      rw [T_loadTeO (o := 0x15a9e#64) (by decide) hm]; rfl
    have pF : PLift (∀ w : BitVec 8, FrPre x (st.setTe 2 w)) :=
      ⟨fun w => shB_frpre_te hF (by show 2 ≠ st.n.toNat; omega) (by omega)⟩
    have pR : PLift (RB t₀ s₀) := ⟨hR⟩
    have pdi : PLift (s₀.regs.get64 .rdi = arg0 t₀) := ⟨hdi⟩
    have pdx : PLift (s₀.regs.get64 .rdx = arg2 t₀) := ⟨hdx⟩
    have hrbx : s₀.regs.get64 .rbx = arg3 t₀ := hR.2.2.2
    have hsi31 : (s₀.regs.get64 .rsi).toNat < 2 ^ 31 := by omega
    clear hm
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      AddrIndex.offset64_scale1, AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
      hdx, hrbx] at *
    all_goals try exact hl1
    all_goals try simp only [shB_z, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, shB_eqK _ 2 hsi31 (by decide)] at *
    · left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
      refine ⟨by decide, ⟨hC, ?_, ?_, ?_, _, ⟨pF.down _, ?_, ?_, ?_⟩, pst.down _⟩, by edge_lt⟩
      all_goals try simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      all_goals first | done | trivial | exact pR.down | exact pdx.down | exact pdi.down | exact hax | (change st.n.toNat ≤ 5; exact h5) | (change _ ≤ st.n.toNat; omega)
    · refine ⟨⟨hC, ?_, ?_, ?_, _, ⟨pF.down _, ?_, ?_, hax, ?_⟩, pst.down _⟩, Nat.le_refl _⟩
      all_goals try simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      all_goals first | done | trivial | exact pR.down | exact pdx.down | exact pdi.down | exact hax | (change st.n.toNat ≤ 5; exact h5) | omega | (change _ = _; omega)

/-- `t_env[3] = …` store; `cmp $3,%esi; je L4bb9`. -/
theorem blk_L4a1d (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4a1d" := by
  cfg_block
  measure_hb "L4a1d"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hR, hdx, hdi, st, ⟨hF, h5, hs3, hax, hn⟩, hm⟩, hv⟩ := hs₀
    have htl : st.te.length = 10 := hF.1.2.1
    have pst : PLift (∀ (w : BitVec 8),
        s₀.dmem.storeInt (arg3 t₀ + 0x15a9f#64) 1 w.toInt
          =⋆ T k Ext x ra t₀ (Saved t₀) (st.setTe 3 w)) := ⟨fun w => by
      have := T_storeTeO (o := 0x15a9f#64) (by decide) hm htl w
      exact this⟩
    have hl1 : (s₀.dmem.loadInt (arg3 t₀ + 0x15a9f#64) 1).isSome := by
      rw [T_loadTeO (o := 0x15a9f#64) (by decide) hm]; rfl
    have pF : PLift (∀ w : BitVec 8, FrPre x (st.setTe 3 w)) :=
      ⟨fun w => shB_frpre_te hF (by show 3 ≠ st.n.toNat; omega) (by omega)⟩
    have pR : PLift (RB t₀ s₀) := ⟨hR⟩
    have pdi : PLift (s₀.regs.get64 .rdi = arg0 t₀) := ⟨hdi⟩
    have pdx : PLift (s₀.regs.get64 .rdx = arg2 t₀) := ⟨hdx⟩
    have hrbx : s₀.regs.get64 .rbx = arg3 t₀ := hR.2.2.2
    have hsi31 : (s₀.regs.get64 .rsi).toNat < 2 ^ 31 := by omega
    clear hm
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      AddrIndex.offset64_scale1, AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
      hdx, hrbx] at *
    all_goals try exact hl1
    all_goals try simp only [shB_z, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, shB_eqK _ 3 hsi31 (by decide)] at *
    · left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
      refine ⟨by decide, ⟨hC, ?_, ?_, ?_, _, ⟨pF.down _, ?_, ?_, ?_⟩, pst.down _⟩, by edge_lt⟩
      all_goals try simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      all_goals first | done | trivial | exact pR.down | exact pdx.down | exact pdi.down | exact hax | (change st.n.toNat ≤ 5; exact h5) | (change _ ≤ st.n.toNat; omega)
    all_goals try (exfalso; omega)

end Kraken.Examples.Sbr.Grid
