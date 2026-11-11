import Kraken.X64.Examples.Sbr.Parse.GridMem

/-!
# `read_sbr_grid`: `VARVAR` (class 3), the head

`bs_var_bord_0` (stored to `t_env[0]`), `bs_var_bord_1`, `bs_num_rel_0`, `bs_num_rel_1`, the
check `bs_num_env ≤ 5`, `bs_num_env` and `t_env[bs_num_env]`.
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
/-- `t_env[0] = bs_var_bord_0 < 4` keeps the invariant. -/
theorem sinv_te0 {x : GArgs} {st : GSt} {i : BitVec 32} {w : BitVec 8} (hS : SInvD x st)
    (hw : w.toNat < 20) (hi : i.toNat ≤ x.p8.toNat) : SInv x ((st.withI i).setTe 0 w) := by
  obtain ⟨⟨hfl, hil, htl, hql, hn8, hfr, hnn, hinv, hy, hte9, htq, hidx1, hidx2, hv1, hv2, -⟩,
    hten⟩ := hS
  refine ⟨⟨hfl, hil, ?_, hql, hn8, hfr, hnn, hinv, hy, ?_, htq, hidx1, hidx2, hv1, hv2,
    fun h => h.elim⟩, ?_, hi⟩
  all_goals simp only [GSt.dv, List.length_set, u8] at *
  · exact htl
  · rw [getD_set_ne _ _ _ _ (by omega)]; exact hte9
  · rw [getD_set_if _ _ _ _ (by omega)]
    split
    · simp only [UInt8.toNat_ofBitVec]; omega
    · exact hten

omit [CodeEnv] in
/-- The low byte of `get_bits(gb, 2)`. -/
theorem gb2_byte (y : BitVec 32) :
    (BitVec.setWidth 8 (BitVec.setWidth 64 (y.ushiftRight 30))).toNat < 20 := by
  have := shr30_lt y
  simp only [BitVec.toNat_setWidth]
  have h : (y.ushiftRight 30).toNat = (y >>> 30).toNat := rfl
  omega

omit [CodeEnv] in
theorem gb2_lt4 (y : BitVec 32) : (BitVec.setWidth 64 (y.ushiftRight 30)).toNat < 4 := by
  have := shr30_lt y
  simp only [BitVec.toNat_setWidth]
  have h : (y.ushiftRight 30).toNat = (y >>> 30).toNat := rfl
  omega

/-- `VARVAR`: `bs_var_bord_0 = get_bits(gb, 2)`, stored to `t_env[0]`. -/
theorem blk_L46a2 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L46a2" := by
  cfg_block
  measure_hb "L46a2"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hR, hax, h8, h15, h9, st, hD, hm⟩, hn⟩ := hs₀
    have hp : x.p8.toNat < 2 ^ 31 := hC.2.2.2.1
    have hoff := rd_off ((s₀.regs.get64 .r9).setWidth 32) x.p8 x.L
      (by rw [BitVec.toNat_setWidth]; omega) hC.2.2.2.2.1
    have hbl := T_buf_load hm _ 4 hoff
    have htl : st.te.length = 10 := hD.1.2.2.1
    have hst : ∀ (v : BitVec 32) (w : BitVec 8),
        ((s₀.dmem.storeInt (arg2 t₀ + 8#64) 4 v.toInt).storeInt (arg3 t₀ + 0x15a9c#64) 1 w.toInt)
          =⋆ T k Ext x ra t₀ (Saved t₀) ((st.withI v).setTe 0 w) := fun v w => by
      have := T_storeTeO (o := 0x15a9c#64) (by decide) (T_storeI hm v) htl w
      exact this
    have hli := T_loadI hm
    have hlt : ∀ v : BitVec 32, ((s₀.dmem.storeInt (arg2 t₀ + 8#64) 4 v.toInt).loadInt
        (arg3 t₀ + 0x15a9c#64) 1).isSome := fun v => by
      rw [T_loadTeO (o := 0x15a9c#64) (by decide) (T_storeI hm v)]; rfl
    have hrdx : s₀.regs.get64 .rdx = arg2 t₀ := hR.1.2.2.2.1
    have hrbx : s₀.regs.get64 .rbx = arg3 t₀ := hR.2
    have pR : PLift (Regs t₀ s₀) := ⟨hR⟩
    clear hm
    vcgen [bswap32_havoc, shl_cl32_havoc]
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      AddrIndex.offset64_scale1, AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrdx, hrbx, h8, hax,
      Int64.toBitVec_neg_ofNat_norm, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
      BitVec.setWidth_32_64_32]
    · exact hbl
    · simp only [hli, Option.isSome_some]
    · exact hlt _
    · refine ⟨⟨hC, ?_, ?_, ?_, _, ?_, hst _ _⟩, ?_⟩
      · simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        exact ⟨pR.down.1.1, pR.down.1.2.1, pR.down.1.2.2.1, pR.down.2⟩
      · first | done | trivial | exact pR.down.1.2.2.2.1
      · first | done | trivial | exact pR.down.1.2.2.2.2.1
      · exact sinv_te0 hD (gb2_byte _) (gb_clamp _ _ _ _)
      · exact Nat.le_refl _

/-- The loads of `gb->buffer` and `gb->size_in_bits_plus8`. -/
theorem T_gbl {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : GArgs} {ra : Int64}
    {t₀ : MachineData} {FR : (Mem 64 → Prop) → Mem 64 → Prop} {st : GSt}
    (h : m =⋆ T k Ext x ra t₀ FR st) :
    m.loadInt (arg2 t₀) 8 = some (Int.ofBytes (Int.toBytes 8 x.buf.toInt))
    ∧ m.loadInt (arg2 t₀ + 16#64) 4 = some (Int.ofBytes (Int.toBytes 4 x.p8.toInt)) := by
  obtain ⟨F, hg⟩ := T_gb h
  exact ⟨Parse.gb_load_buf (g := arg2 t₀) (i := st.i) hg, Parse.gb_load_p8 (g := arg2 t₀) (buf := x.buf) (i := st.i) hg⟩

/-- `bs_var_bord_1 = get_bits(gb, 2)` (the reader reloaded). -/
theorem blk_L46cd (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L46cd" := by
  cfg_block
  measure_hb "L46cd"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hR, hdx, hdi, st, ⟨hD, hT, hI⟩, hm⟩, hn⟩ := hs₀
    have hp : x.p8.toNat < 2 ^ 31 := hC.2.2.2.1
    have hoff := rd_off st.i x.p8 x.L hI hC.2.2.2.2.1
    have hbl := T_buf_load hm _ 4 hoff
    have hli := T_loadI hm
    have hgl := T_gbl hm
    have hst := T_storeI hm
    have pR : PLift (RB t₀ s₀) := ⟨hR⟩
    have pdi : PLift (s₀.regs.get64 .rdi = arg0 t₀) := ⟨hdi⟩
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
    · exact hbl
    · refine ⟨⟨hC, ?_, ?_, ?_, ?_, ?_, gb_clamp64 _ _ _ _, gb2_lt4 _, st, ⟨hD, hT⟩, ?_⟩,
        Nat.le_refl _⟩
      · simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        exact pR.down
      all_goals first | done | trivial | rfl | exact pdi.down | (dsimp only [At]; exact hst _)

/-- `bs_num_rel_0 = get_bits(gb, 2)` (the reader in registers). -/
theorem blk_L4701 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4701" := by
  cfg_block
  measure_hb "L4701"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hR, hdx, hdi, hax, h10, h9, h8, st, hD, hm⟩, hn⟩ := hs₀
    have hp : x.p8.toNat < 2 ^ 31 := hC.2.2.2.1
    have hoff := rd_off ((s₀.regs.get64 .r9).setWidth 32) x.p8 x.L
      (by rw [BitVec.toNat_setWidth]; omega) hC.2.2.2.2.1
    have hbl := T_buf_load hm _ 4 hoff
    have hli := T_loadI hm
    have hst := T_storeI hm
    have pR : PLift (RB t₀ s₀) := ⟨hR⟩
    have pdi : PLift (s₀.regs.get64 .rdi = arg0 t₀) := ⟨hdi⟩
    clear hm
    vcgen [bswap32_havoc, shl_cl32_havoc]
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      AddrIndex.offset64_scale1, AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
      hdx, hax, h10, BitVec.setWidth_32_64_32] at *
    all_goals try simp only [hli, Option.isSome_some] at *
    · exact hbl
    · refine ⟨⟨hC, ?_, ?_, ?_, ?_, ?_, gb_clamp64 _ _ _ _, ?_, gb2_lt4 _, st, hD, ?_⟩,
        Nat.le_refl _⟩
      · simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        exact pR.down
      all_goals first | done | trivial | rfl | exact pdi.down | exact h8 | (dsimp only [At]; exact hst _)

/-- `bs_num_rel_1 = get_bits(gb, 2)`. -/
theorem blk_L4726 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4726" := by
  cfg_block
  measure_hb "L4726"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hR, hdx, hdi, hax, h10, h9, h8, hsi, st, hD, hm⟩, hn⟩ := hs₀
    have hp : x.p8.toNat < 2 ^ 31 := hC.2.2.2.1
    have hoff := rd_off ((s₀.regs.get64 .r9).setWidth 32) x.p8 x.L
      (by rw [BitVec.toNat_setWidth]; omega) hC.2.2.2.2.1
    have hbl := T_buf_load hm _ 4 hoff
    have hli := T_loadI hm
    have hst : ∀ v : BitVec 32, s₀.dmem.storeInt (arg2 t₀ + 8#64) 4 v.toInt
        =⋆ T k Ext x ra t₀ (Saved t₀) (st.withI v) := fun v => T_storeI hm v
    have pR : PLift (RB t₀ s₀) := ⟨hR⟩
    have pdi : PLift (s₀.regs.get64 .rdi = arg0 t₀) := ⟨hdi⟩
    clear hm
    vcgen [bswap32_havoc, shl_cl32_havoc]
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      AddrIndex.offset64_scale1, AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
      hdx, hax, h10, BitVec.setWidth_32_64_32] at *
    all_goals try simp only [hli, Option.isSome_some] at *
    · exact hbl
    all_goals try exact hbl
    · refine ⟨⟨hC, ?_, trivial, pdi.down, ?_⟩, Nat.le_refl _⟩
      · simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        exact pR.down
      · refine ⟨st.withI _, ⟨?_, gb2_lt4 _, hsi, h8⟩, hst _⟩
        exact ⟨hD.1, hD.2, gb_clamp _ _ _ _⟩

end Kraken.Examples.Sbr.Grid
