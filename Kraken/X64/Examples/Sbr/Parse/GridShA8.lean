import Kraken.X64.Examples.Sbr.Parse.GridShA7

/-!
# `read_sbr_grid`: FIXVAR (class 1), the `t_env` fill from the top (`RelL`)
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
theorem shA_nc_sub32 (a b : BitVec 32) (f : StatusFlags.from_result.Remaining)
    (hf : f.cf = ((a - b).unsigned != a.unsigned - b.unsigned)) :
    CondCode.nc.interp (StatusFlags.from_result (a - b) f) = decide (b.toNat ≤ a.toNat) := by
  rw [CondCode.interp_nc, StatusFlags.cf_from_result, hf]
  grind [BitVec.unsigned_eq]

/-- `ecx = n - j`, the check `n - j < 9` (holds). -/
theorem blk_L47f0 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L47f0" := by
  cfg_block
  measure_hb "L47f0"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hRB, hdx, hdi, st, ⟨hP, v, j, hv1, hv4, hjv, hvn, hax, hsi, h5, hcx⟩, hm⟩, hn⟩ := hs₀
    have hrbx : s₀.regs.get64 .rbx = arg3 t₀ := hRB.2.2.2
    have h8 : st.n.toNat ≤ 8 := hP.1.2.2.2.1
    have key : BitVec.setWidth 32 (s₀.regs.get64 .rsi) + BitVec.setWidth 32 (s₀.regs.get64 .rcx)
        = BitVec.ofNat 32 (st.n.toNat - j) := by rw [hcx, hsi]; bv_omega
    have hmT : Hide _ := hm
    have pRB : PLift (RB t₀ s₀) := ⟨hRB⟩
    clear hm hRB
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [AddrIndex.offset64_none, AddrIndex.offset64_scale1, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbx, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, get64_ite, ite_self, BitVec.ushiftRight_eq] at *
    all_goals try rw [ea]
    all_goals try have li := pli.down
    all_goals try have lp := plp.down
    all_goals try have lb := plb.down
    all_goals try simp only [hld, Option.some.injEq, Option.isSome_some] at *
    all_goals try simp only [li, lp, lb, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt64_ofBytes_toBytes8,
      BitVec.ofInt_toInt, BitVec.setWidth_32_64_32] at *
    · exfalso
      have hf := ‹CondCode.nc.interp _ = true›
      rw [shA_nc_sub32 _ _ _ rfl, key] at hf
      simp only [decide_eq_true_eq] at hf
      bv_omega
    · obtain ⟨hsp, hbp, h13, hbx⟩ := pRB.down
      try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, BitVec.setWidth_32_64_32]
      refine ⟨⟨hC, ⟨hsp, hbp, h13, hbx⟩, hdx, hdi, st, ⟨hP, v, j, hv1, hv4, hjv, hvn, hax, hsi, h5, key⟩,
        hmT⟩, Nat.le_refl _⟩

/-- `r8 = t_env[n - j]`. -/
theorem blk_L47fb (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L47fb" := by
  cfg_block
  measure_hb "L47fb"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hRB, hdx, hdi, st, ⟨hP, v, j, hv1, hv4, hjv, hvn, hax, hsi, h5, hcx⟩, hm⟩, hn⟩ := hs₀
    have hrbx : s₀.regs.get64 .rbx = arg3 t₀ := hRB.2.2.2
    have h8 : st.n.toNat ≤ 8 := hP.1.2.2.2.1
    have htl : st.te.length = 10 := hP.1.2.1
    have hld := T_loadTe hm (st.n.toNat - j) (by omega)
    have ea : arg3 t₀ + BitVec.setWidth 64 (BitVec.setWidth 32 (s₀.regs.get64 .rcx)) + 0x15a9c#64
        = arg3 t₀ + BitVec.ofNat 64 (st.n.toNat - j) + 0x15a9c#64 := by rw [hcx]; bv_omega
    have hmT : Hide _ := hm
    have pRB : PLift (RB t₀ s₀) := ⟨hRB⟩
    clear hm hRB
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [AddrIndex.offset64_none, AddrIndex.offset64_scale1, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbx, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, get64_ite, ite_self, BitVec.ushiftRight_eq] at *
    all_goals try rw [ea]
    all_goals try have li := pli.down
    all_goals try have lp := plp.down
    all_goals try have lb := plb.down
    all_goals try simp only [hld, Option.some.injEq, Option.isSome_some] at *
    all_goals try simp only [li, lp, lb, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt64_ofBytes_toBytes8,
      BitVec.ofInt_toInt, BitVec.setWidth_32_64_32] at *
    obtain ⟨hsp, hbp, h13, hbx⟩ := pRB.down
    try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    exact ⟨⟨hC, ⟨hsp, hbp, h13, hbx⟩, hdx, hdi, st, ⟨hP, v, j, hv1, hv4, hjv, hvn, hax, hsi, h5⟩,
      hmT⟩, Nat.le_refl _⟩

/-- `get_bits(gb, 2)` of a relative border (FIXVAR). -/
theorem blk_L4806 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4806" := by
  cfg_block
  measure_hb "L4806"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hRB, hdx, hdi, st, ⟨hP, v, j, hv1, hv4, hjv, hvn, hax, hsi, h5⟩, hm⟩, hn⟩ := hs₀
    have hrbx : s₀.regs.get64 .rbx = arg3 t₀ := hRB.2.2.2
    have h8 : st.n.toNat ≤ 8 := hP.1.2.2.2.1
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
    clear hg
    have hmT : Hide _ := hm
    have pRB : PLift (RB t₀ s₀) := ⟨hRB⟩
    clear hm hRB
    vcgen [bswap32_havoc, shl_cl32_havoc]
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [AddrIndex.offset64_none, AddrIndex.offset64_scale1, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbx, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, get64_ite, ite_self, BitVec.ushiftRight_eq] at *
    all_goals try rw [ea]
    all_goals try have li := pli.down
    all_goals try have lp := plp.down
    all_goals try have lb := plb.down
    all_goals try simp only [hld, Option.some.injEq, Option.isSome_some] at *
    all_goals try simp only [li, lp, lb, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt64_ofBytes_toBytes8,
      BitVec.ofInt_toInt, BitVec.setWidth_32_64_32] at *
    · exact hbl
    · obtain ⟨hsp, hbp, h13, hbx⟩ := pRB.down
      rw [hdx]
      refine ⟨⟨hC, ?_, rfl, hdi, _,
        ⟨shA_frPre_withI hP (gb_clamp _ _ _ _), v, j, hv1, hv4, hjv, hvn, hax, hsi, h5⟩, hst _⟩,
        Nat.le_refl _⟩
      simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      exact ⟨hsp, hbp, h13, hbx⟩

/-- `ecx = n`, `r10d = n - 1 - j`, the check `< 9` (holds). -/
theorem blk_L483b (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L483b" := by
  cfg_block
  measure_hb "L483b"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hRB, hdx, hdi, st, ⟨hP, v, j, hv1, hv4, hjv, hvn, hax, hsi, h5⟩, hm⟩, hn⟩ := hs₀
    have hrbx : s₀.regs.get64 .rbx = arg3 t₀ := hRB.2.2.2
    have h8 : st.n.toNat ≤ 8 := hP.1.2.2.2.1
    have hld := T_loadN hm
    have key : BitVec.setWidth 32 (s₀.regs.get64 .rsi + BitVec.setWidth 64 st.n) - 1#32
        = BitVec.ofNat 32 (st.n.toNat - 1 - j) := by bv_omega
    have hmT : Hide _ := hm
    have pRB : PLift (RB t₀ s₀) := ⟨hRB⟩
    clear hm hRB
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [AddrIndex.offset64_none, AddrIndex.offset64_scale1, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbx, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, get64_ite, ite_self, BitVec.ushiftRight_eq] at *
    all_goals try rw [ea]
    all_goals try have li := pli.down
    all_goals try have lp := plp.down
    all_goals try have lb := plb.down
    all_goals try simp only [hld, Option.some.injEq, Option.isSome_some] at *
    all_goals try simp only [li, lp, lb, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt64_ofBytes_toBytes8,
      BitVec.ofInt_toInt, BitVec.setWidth_32_64_32] at *
    · exfalso
      have hf := ‹CondCode.nc.interp _ = true›
      rw [shA_nc_sub32 _ _ _ rfl, key] at hf
      simp only [decide_eq_true_eq] at hf
      bv_omega
    · obtain ⟨hsp, hbp, h13, hbx⟩ := pRB.down
      try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, BitVec.setWidth_32_64_32]
      refine ⟨⟨hC, ⟨hsp, hbp, h13, hbx⟩, hdx, hdi, st,
        ⟨hP, v, j, hv1, hv4, hjv, hvn, hax, hsi, h5, key, rfl⟩, hmT⟩, Nat.le_refl _⟩

/-- `t_env[n - 1 - j] = r8 - 2 * tmp - 2`; `j + 1`, the back edge or the exit to `L486a`. -/
theorem blk_L484f (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L484f" := by
  cfg_block
  measure_hb "L484f"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hRB, hdx, hdi, st, ⟨hP, v, j, hv1, hv4, hjv, hvn, hax, hsi, h5, h10, hcx⟩, hm⟩, hn⟩ := hs₀
    have hrbx : s₀.regs.get64 .rbx = arg3 t₀ := hRB.2.2.2
    have h8 : st.n.toNat ≤ 8 := hP.1.2.2.2.1
    have htl : st.te.length = 10 := hP.1.2.1
    have hst := T_storeTe hm htl (st.n.toNat - 1 - j) (by omega)
    have hld := T_loadTe hm (st.n.toNat - 1 - j) (by omega)
    have ea : arg3 t₀ + BitVec.setWidth 64 (BitVec.setWidth 32 (s₀.regs.get64 .r10)) + 0x15a9c#64
        = arg3 t₀ + BitVec.ofNat 64 (st.n.toNat - 1 - j) + 0x15a9c#64 := by rw [h10]; bv_omega
    have hmT : Hide _ := hm
    have pRB : PLift (RB t₀ s₀) := ⟨hRB⟩
    clear hm hRB
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [AddrIndex.offset64_none, AddrIndex.offset64_scale1, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbx, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, get64_ite, ite_self, BitVec.ushiftRight_eq] at *
    all_goals try rw [ea]
    all_goals try have li := pli.down
    all_goals try have lp := plp.down
    all_goals try have lb := plb.down
    all_goals try simp only [hld, Option.some.injEq, Option.isSome_some] at *
    all_goals try simp only [li, lp, lb, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt64_ofBytes_toBytes8,
      BitVec.ofInt_toInt, BitVec.setWidth_32_64_32] at *
    · have hne := (shA_nz _ _).mp ‹_›
      have hj1 : j + 1 < v := by
        have : j + 1 ≠ v := by
          intro h; apply hne; subst h; rw [hax, hsi]; bv_omega
        omega
      obtain ⟨hsp, hbp, h13, hbx⟩ := pRB.down
      left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
      try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, BitVec.setWidth_32_64_32]
      refine ⟨by decide, ⟨hC, ?_, hdx, hdi, ?_⟩, Or.inl ?_⟩
      · simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        exact ⟨hsp, hbp, h13, hbx⟩
      · refine ⟨_, ?_, hst _⟩
        refine ⟨shA_frPre_te_lt hP _ (by omega) _, v, j + 1, hv1, hv4, hj1, hvn, hax, ?_, h5, hcx⟩
        rw [hsi]; bv_omega
      · simp only [Nat.add_eq]; rw [hax, hsi]; bv_omega
    · have heq := (shA_nz_f _ _).mp ‹_›
      have hj1 : j + 1 = v := by
        rw [hax, hsi] at heq; bv_omega
      obtain ⟨hsp, hbp, h13, hbx⟩ := pRB.down
      try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, BitVec.setWidth_32_64_32]
      refine ⟨⟨hC, ?_, hdx, hdi, ?_⟩, ?_⟩
      · simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        exact ⟨hsp, hbp, h13, hbx⟩
      · refine ⟨_, ?_, hst _⟩
        exact ⟨shA_frPre_te_lt hP _ (by omega) _, h5, hcx⟩
      · simp only [Nat.add_eq]; omega

end Kraken.Examples.Sbr.Grid
