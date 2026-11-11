import Kraken.X64.Examples.Sbr.Parse.GridShB3

/-!
# `read_sbr_grid`: `VARVAR` (class 3), the second `t_env` loop

`t_env[n - 1 - j] = t_env[n - j] - 2 * get_bits(gb, 2) - 2` for `j < bs_num_rel_1`, with
`eax = -bs_num_rel_1` and `esi = -j` (`RelL`).
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
theorem shB_neg (r : BitVec 64) (h : r.toNat < 4) :
    BitVec.setWidth 32 (BitVec.setWidth 64 (-BitVec.setWidth 32 r)) = 0#32 - BitVec.ofNat 32 r.toNat := by
  bv_omega

omit [CodeEnv] in
/-- The zero flag, negated (`jne`). -/
theorem shB_nz {w : Nat} (v : BitVec w) (f : StatusFlags.from_result.Remaining) :
    CondCode.nz.interp (StatusFlags.from_result v f) = !(v == BitVec.zero w) := by
  simp only [CondCode.interp, StatusFlags.from_result]

omit [CodeEnv] in
/-- `RelL` step: `dec %esi`. -/
theorem shB_rel_es1 (e : BitVec 32) (j : Nat) (h : e = 0#32 - BitVec.ofNat 32 j) (hj : j < 4) :
    e - 1#32 = 0#32 - BitVec.ofNat 32 (j + 1) := by
  subst h; bv_omega

omit [CodeEnv] in
/-- `RelL` step: `cmp %esi,%eax` after `dec %esi` is zero iff the last step. -/
theorem shB_rel_z (a e : BitVec 32) (v j : Nat) (ha : a = 0#32 - BitVec.ofNat 32 v)
    (he : e = 0#32 - BitVec.ofNat 32 j) (hv : v < 4) (hj : j < 4) :
    (a - (e - 1#32) = BitVec.zero 32) ↔ v = j + 1 := by
  subst ha he; change _ = 0#32 ↔ _; constructor <;> intro h <;> bv_omega

omit [CodeEnv] in
/-- `RelL` variant after the step. -/
theorem shB_rel_var1 (a : BitVec 32) (v j : Nat) (ha : a = 0#32 - BitVec.ofNat 32 v)
    (hjv : j < v) (hv : v < 4) :
    (0#32 - BitVec.ofNat 32 (j + 1) - a).toNat = v - (j + 1) := by
  subst ha; bv_omega

omit [CodeEnv] in
/-- `RelL` variant: `esi - eax = v - j`. -/
theorem shB_rel_var0 (e a : BitVec 32) (v j : Nat) (ha : a = 0#32 - BitVec.ofNat 32 v)
    (he : e = 0#32 - BitVec.ofNat 32 j) (hjv : j < v) (hv : v < 4) :
    (e - a).toNat = v - j := by
  subst ha he; bv_omega

/-- `bs_num_env` into `ecx`. -/
theorem blk_L4bb9 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4bb9" := by
  cfg_block
  measure_hb "L4bb9"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hR, hdx, hdi, st, ⟨hF, h5, hax, hn⟩, hm⟩, hv⟩ := hs₀
    have hln := T_loadN hm
    have pst : PLift (s₀.dmem =⋆ T k Ext x ra t₀ (Saved t₀) st) := ⟨hm⟩
    have pR : PLift (RB t₀ s₀) := ⟨hR⟩
    have pdi : PLift (s₀.regs.get64 .rdi = arg0 t₀) := ⟨hdi⟩
    have pdx : PLift (s₀.regs.get64 .rdx = arg2 t₀) := ⟨hdx⟩
    have hrbx : s₀.regs.get64 .rbx = arg3 t₀ := hR.2.2.2
    clear hm
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      AddrIndex.offset64_scale1, AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
      hrbx] at *
    all_goals try simp only [hln, Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt64_ofBytes_toBytes8,
      BitVec.ofInt_toInt, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, BitVec.setWidth_32_64_32] at *
    refine ⟨⟨hC, ?_, pdx.down, pdi.down, st, ⟨hF, h5, hax, hn, rfl⟩, pst.down⟩, Nat.le_refl _⟩
    simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact pR.down

/-- `test %eax,%eax; jle` (no relative borders), else `eax = -v`, `esi = 0`. -/
theorem blk_L4bbc (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4bbc" := by
  cfg_block
  measure_hb "L4bbc"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hR, hdx, hdi, st, ⟨hF, h5, hax, hn, hcx⟩, hm⟩, hv⟩ := hs₀
    have pst : PLift (s₀.dmem =⋆ T k Ext x ra t₀ (Saved t₀) st) := ⟨hm⟩
    have pR : PLift (RB t₀ s₀) := ⟨hR⟩
    have pdi : PLift (s₀.regs.get64 .rdi = arg0 t₀) := ⟨hdi⟩
    have pdx : PLift (s₀.regs.get64 .rdx = arg2 t₀) := ⟨hdx⟩
    have pcx : PLift ((s₀.regs.get64 .rcx).setWidth 32 = st.n) := ⟨hcx⟩
    have pF : PLift (FrPre x st) := ⟨hF⟩
    clear hm
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      AddrIndex.offset64_scale1, AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow] at *
    all_goals try simp only [shB_le_test _ hax, decide_eq_true_eq, decide_eq_false_iff_not] at *
    · left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
      refine ⟨by decide, ⟨hC, ?_, pdx.down, pdi.down, st, ⟨pF.down, h5, pcx.down⟩, pst.down⟩, by edge_lt⟩
      simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact pR.down
    · refine ⟨⟨hC, ?_, pdx.down, pdi.down, st, ⟨pF.down, _, 0, by omega, hax, by omega, hn, shB_neg _ hax, ?_, h5, pcx.down⟩, pst.down⟩, ?_⟩
      · simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact pR.down
      · simp only [BitVec.xor_self]; rfl
      · show 22 + _ ≤ 32
        simp only [BitVec.xor_self, BitVec.setWidth_32_64_32]
        bv_omega


/-- `ecx = n - j`; `cmp $9,%ecx; jae` (trap). -/
theorem blk_L4bd0 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4bd0" := by
  cfg_block
  measure_hb "L4bd0"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hR, hdx, hdi, st, ⟨hF, v, j, hv1, hv4, hjv, hvn, hea, hes, h5, hcx⟩, hm⟩, hv⟩ := hs₀
    have hsum : BitVec.setWidth 32 (s₀.regs.get64 .rsi) + BitVec.setWidth 32 (s₀.regs.get64 .rcx)
        = BitVec.ofNat 32 (st.n.toNat - j) := by rw [hcx, hes]; bv_omega
    have pst : PLift (s₀.dmem =⋆ T k Ext x ra t₀ (Saved t₀) st) := ⟨hm⟩
    have pR : PLift (RB t₀ s₀) := ⟨hR⟩
    have pdi : PLift (s₀.regs.get64 .rdi = arg0 t₀) := ⟨hdi⟩
    have pdx : PLift (s₀.regs.get64 .rdx = arg2 t₀) := ⟨hdx⟩
    have pea : PLift (BitVec.setWidth 32 (s₀.regs.get64 .rax) = 0#32 - BitVec.ofNat 32 v) := ⟨hea⟩
    have pes : PLift (BitVec.setWidth 32 (s₀.regs.get64 .rsi) = 0#32 - BitVec.ofNat 32 j) := ⟨hes⟩
    have pF : PLift (FrPre x st) := ⟨hF⟩
    clear hm
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      AddrIndex.offset64_scale1, AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
      BitVec.setWidth_32_64_32, hsum] at *
    all_goals try simp only [shB_nc_sub, decide_eq_true_eq, decide_eq_false_iff_not,
      BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.not_le] at *
    · exfalso; omega
    · refine ⟨⟨hC, ?_, pdx.down, pdi.down, st, ⟨pF.down, v, j, hv1, hv4, hjv, hvn, pea.down, pes.down,
        h5, rfl⟩, pst.down⟩, Nat.le_refl _⟩
      simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact pR.down


/-- `r8 = t_env[n - j]`. -/
theorem blk_L4bdb (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4bdb" := by
  cfg_block
  measure_hb "L4bdb"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hR, hdx, hdi, st, ⟨hF, v, j, hv1, hv4, hjv, hvn, hea, hes, h5, hcx⟩, hm⟩, hv⟩ := hs₀
    have hc64 : BitVec.setWidth 64 (BitVec.setWidth 32 (s₀.regs.get64 .rcx))
        = BitVec.ofNat 64 (st.n.toNat - j) := by rw [hcx]; bv_omega
    have hl := T_loadTe hm (st.n.toNat - j) (by omega)
    have pst : PLift (s₀.dmem =⋆ T k Ext x ra t₀ (Saved t₀) st) := ⟨hm⟩
    have pR : PLift (RB t₀ s₀) := ⟨hR⟩
    have pdi : PLift (s₀.regs.get64 .rdi = arg0 t₀) := ⟨hdi⟩
    have pdx : PLift (s₀.regs.get64 .rdx = arg2 t₀) := ⟨hdx⟩
    have pea : PLift (BitVec.setWidth 32 (s₀.regs.get64 .rax) = 0#32 - BitVec.ofNat 32 v) := ⟨hea⟩
    have pes : PLift (BitVec.setWidth 32 (s₀.regs.get64 .rsi) = 0#32 - BitVec.ofNat 32 j) := ⟨hes⟩
    have pF : PLift (FrPre x st) := ⟨hF⟩
    have hrbx : s₀.regs.get64 .rbx = arg3 t₀ := hR.2.2.2
    clear hm
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      AddrIndex.offset64_scale1, AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
      hrbx, hc64] at *
    all_goals try simp only [hl, Option.isSome_some] at *
    refine ⟨⟨hC, ?_, pdx.down, pdi.down, st, ⟨pF.down, v, j, hv1, hv4, hjv, hvn, pea.down, pes.down,
      h5⟩, pst.down⟩, Nat.le_refl _⟩
    simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact pR.down


/-- `r9 = get_bits(gb, 2)`. -/
theorem blk_L4be6 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4be6" := by
  cfg_block
  measure_hb "L4be6"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hR, hdx, hdi, st, ⟨hF, v, j, hv1, hv4, hjv, hvn, hea, hes, h5⟩, hm⟩, hv⟩ := hs₀
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
    have pea : PLift (BitVec.setWidth 32 (s₀.regs.get64 .rax) = 0#32 - BitVec.ofNat 32 v) := ⟨hea⟩
    have pes : PLift (BitVec.setWidth 32 (s₀.regs.get64 .rsi) = 0#32 - BitVec.ofNat 32 j) := ⟨hes⟩
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
      exact ⟨shB_frpre_i hF (gb_clamp _ _ _ _), v, j, hv1, hv4, hjv, hvn, pea.down, pes.down, h5⟩


/-- `ecx = n`, `r10d = n - 1 - j`; `cmp $9,%r10d; jae` (trap). -/
theorem blk_L4c1b (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4c1b" := by
  cfg_block
  measure_hb "L4c1b"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hR, hdx, hdi, st, ⟨hF, v, j, hv1, hv4, hjv, hvn, hea, hes, h5⟩, hm⟩, hv⟩ := hs₀
    have hln := T_loadN hm
    have hr10 : BitVec.setWidth 32 (s₀.regs.get64 .rsi + BitVec.setWidth 64 st.n) - 1#32
        = BitVec.ofNat 32 (st.n.toNat - 1 - j) := by bv_omega
    have pst : PLift (s₀.dmem =⋆ T k Ext x ra t₀ (Saved t₀) st) := ⟨hm⟩
    have pR : PLift (RB t₀ s₀) := ⟨hR⟩
    have pdi : PLift (s₀.regs.get64 .rdi = arg0 t₀) := ⟨hdi⟩
    have pdx : PLift (s₀.regs.get64 .rdx = arg2 t₀) := ⟨hdx⟩
    have pea : PLift (BitVec.setWidth 32 (s₀.regs.get64 .rax) = 0#32 - BitVec.ofNat 32 v) := ⟨hea⟩
    have pes : PLift (BitVec.setWidth 32 (s₀.regs.get64 .rsi) = 0#32 - BitVec.ofNat 32 j) := ⟨hes⟩
    have pF : PLift (FrPre x st) := ⟨hF⟩
    have hrbx : s₀.regs.get64 .rbx = arg3 t₀ := hR.2.2.2
    clear hm
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      AddrIndex.offset64_scale1, AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
      hrbx] at *
    all_goals try simp only [hln, Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt64_ofBytes_toBytes8,
      BitVec.ofInt_toInt, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, BitVec.setWidth_32_64_32] at *
    all_goals try simp only [hr10] at *
    all_goals try simp only [shB_nc_sub, decide_eq_true_eq, decide_eq_false_iff_not,
      BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.not_le] at *
    · exfalso; omega
    · refine ⟨⟨hC, ?_, pdx.down, pdi.down, st, ⟨pF.down, v, j, hv1, hv4, hjv, hvn, pea.down, pes.down,
        h5, rfl, rfl⟩, pst.down⟩, Nat.le_refl _⟩
      simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact pR.down


/-- `t_env[n - 1 - j] = t_env[n - j] - 2 * r9 - 2`; `dec %esi; cmp %esi,%eax; jne L4bd0`. -/
theorem blk_L4c2f (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4c2f" := by
  cfg_block
  measure_hb "L4c2f"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hR, hdx, hdi, st, ⟨hF, v, j, hv1, hv4, hjv, hvn, hea, hes, h5, h10, hcx⟩, hm⟩, hv⟩ := hs₀
    have htl : st.te.length = 10 := hF.1.2.1
    have h64 : BitVec.setWidth 64 (BitVec.setWidth 32 (s₀.regs.get64 .r10))
        = BitVec.ofNat 64 (st.n.toNat - 1 - j) := by rw [h10]; bv_omega
    have hes1 := shB_rel_es1 _ _ hes (by omega)
    have hvar1 := shB_rel_var1 _ _ _ hea hjv hv4
    have hvar0 := shB_rel_var0 _ _ _ _ hea hes hjv hv4
    have hz0 := shB_rel_z _ _ _ _ hea hes hv4 (by omega)
    have pst : PLift (∀ w : BitVec 8,
        s₀.dmem.storeInt (arg3 t₀ + BitVec.ofNat 64 (st.n.toNat - 1 - j) + 0x15a9c#64) 1 w.toInt
          =⋆ T k Ext x ra t₀ (Saved t₀) (st.setTe (st.n.toNat - 1 - j) w)) :=
      ⟨fun w => T_storeTe hm htl _ (by omega) w⟩
    have hl1 := T_loadTe hm (st.n.toNat - 1 - j) (by omega)
    have pF : PLift (∀ w : BitVec 8, FrPre x (st.setTe (st.n.toNat - 1 - j) w)) :=
      ⟨fun w => shB_frpre_te hF (by omega) (by omega)⟩
    have pR : PLift (RB t₀ s₀) := ⟨hR⟩
    have pdi : PLift (s₀.regs.get64 .rdi = arg0 t₀) := ⟨hdi⟩
    have pdx : PLift (s₀.regs.get64 .rdx = arg2 t₀) := ⟨hdx⟩
    have pea : PLift (BitVec.setWidth 32 (s₀.regs.get64 .rax) = 0#32 - BitVec.ofNat 32 v) := ⟨hea⟩
    have pes : PLift (BitVec.setWidth 32 (s₀.regs.get64 .rsi) = 0#32 - BitVec.ofNat 32 j) := ⟨hes⟩
    have pcx : PLift (BitVec.setWidth 32 (s₀.regs.get64 .rcx) = st.n) := ⟨hcx⟩
    have hrbx : s₀.regs.get64 .rbx = arg3 t₀ := hR.2.2.2
    have pes1 := PLift.up hes1
    have pvar0 := PLift.up hvar0
    have pvar1 := PLift.up hvar1
    have pz := PLift.up hz0
    clear hm hes1 hvar0 hvar1 hz0 hea hes h10 hcx hdx hdi hF
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      AddrIndex.offset64_scale1, AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
      hrbx, h64] at *
    all_goals try simp only [hl1, Option.isSome_some] at *
    all_goals try simp only [shB_nz, Bool.not_eq_true', Bool.not_eq_false',
      beq_iff_eq, beq_eq_false_iff_ne, ne_eq, BitVec.setWidth_32_64_32, pz.down] at *
    · left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, BitVec.setWidth_32_64_32, pes1.down,
        pvar0.down, pvar1.down]
      refine ⟨by decide, ⟨hC, ?_, pdx.down, pdi.down, st.setTe _ _, ?_, pst.down _⟩, ?_⟩
      · simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact pR.down
      · exact ⟨pF.down _, v, j + 1, hv1, hv4, by omega, hvn, pea.down, rfl, h5, pcx.down⟩
      · exact Or.inl (by show 22 + _ < 22 + (v - j); omega)
    · refine ⟨⟨hC, ?_, pdx.down, pdi.down, st.setTe _ _, ?_, pst.down _⟩, ?_⟩
      · simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact pR.down
      · exact ⟨pF.down _, h5, pcx.down⟩
      · show 12 ≤ 22 + _; omega

end Kraken.Examples.Sbr.Grid
