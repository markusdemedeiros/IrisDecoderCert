import Kraken.X64.Examples.Sbr.Parse.PsBlkLLib

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Ps

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

set_option maxRecDepth 20000 in
theorem blk_a90 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.La90" := by
  cfg_block
  simp only [tab_La90, var_La90, tab_Laa5, var_Laa5]
  measure_hb "La90"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, e, ⟨hLB, h1c, h48, h50, he, h9, hbx, hsi⟩, hW⟩, hn⟩ := hs₀
    subst hn
    have hm := hLB.1.2.2
    have hfl := LB_fl hLB
    have hbp := hLB.1.2.1.2.1
    have hne4 : ne c ≤ 4 := hLB.2.2.2.1.2.1
    have hne0 : 0 ≤ ne c := hLB.2.2.2.1.1
    have h40 : rd f 0x40 8 = ne c := hLB.2.2.2.2.2.2
    have e1 : s₀.regs.get64 .rbp + 0 + (-88 : Int64).toBitVec
        = rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 0x48 :=
      slot_addr (by rw [hbp]; exact BitVec.add_zero _) 88 0x48 rfl
    have e2 : s₀.regs.get64 .rbp + 0 + (-96 : Int64).toBitVec
        = rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 0x40 :=
      slot_addr (by rw [hbp]; exact BitVec.add_zero _) 96 0x40 rfl
    have e3 : s₀.regs.get64 .rbp - BitVec.ofNat 64 0x58
        = rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 0x48 := slot_addr_sub hbp 0x58 0x48 rfl
    have l1 := Fr_f_load hm hfl 0x48 8 (by omega)
    have l3 := l1
    rw [← e1] at l1
    rw [← e3] at l3
    have l2 := Fr_f_load hm hfl 0x40 8 (by omega)
    rw [← e2] at l2
    vcgen
    case vc1 =>
      subst_vars; try dsimp only
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, AddrIndex.offset64_none, l1,
        Option.isSome_some]
    case vc2 =>
      rename_i v1 hv1
      subst_vars; try dsimp only at hv1 ⊢
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, AddrIndex.offset64_none, l1,
        Option.some.injEq] at hv1
      subst hv1
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, AddrIndex.offset64_none, l2,
        Option.isSome_some]
    all_goals rename_i v1 hv1 v2 hv2 hz
    all_goals subst_vars
    all_goals try dsimp only at hv1 hv2 hz ⊢
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, AddrIndex.offset64_none, l1, l2,
        Option.some.injEq] at hv1 hv2
    all_goals subst hv1 hv2
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, CondCode.interp_z,
      StatusFlags.zf_from_result] at hz
    all_goals simp only [h9, h48] at hz
    all_goals rw [cnt_beq _ _ he hne4] at hz
    case vc3 =>
      simp only [decide_eq_true_eq] at hz
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.Lcba") ⟨rfl, ?_, Or.inl ?_⟩
      · refine (tab_Lcba _ _ _ _ _ _).mpr ?_
        obtain ⟨hC, hR, hI, hS⟩ := LB_mv hLB rfl rfl hLB.2.1 hLB.2.2.1 hm
        refine ⟨c, f, hC, hR, hI, hS, h1c, ?_, hW⟩
        simp only [Reg64s.get64_set64, ite_true, reduceCtorEq, ite_false, h40]
        exact toNat_ofInt64_small _ hne0 (by omega)
      · rw [var_Lcba]
        exact Kraken.lex_cons_lt_of_lt rfl (by decide)
    case vc4 =>
      simp only [decide_eq_false_iff_not] at hz
      have hz' : ¬ (e : Int) + 1 = ne c := hz
      have he' : (e : Int) < ne c := he
      have h4' : ne c ≤ 4 := hne4
      have h0' : 0 ≤ ne c := hne0
      refine ⟨(tab_Laa5 _ _ _ _ _ _).mpr ⟨c, f, e + 1, ⟨LB_mv hLB (by rs) (by rs) (by rs; exact hLB.2.1)
        (by rs; exact hLB.2.2.1) hm, h1c, h48, h50, by omega, ?_, ?_, by rs; exact hsi⟩, hW⟩, ?_⟩
      · simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, h9]
        exact ofNat64_add e 1
      · simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, hbx]
        exact row_step _ 246 e
      · simp only [slot64, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, l3, Option.getD_some,
          h48, h9]
        rw [show BitVec.ofNat 64 e + 1 = BitVec.ofNat 64 (e + 1) from ofNat64_add e 1]
        refine Kraken.lex_cons_le_cons (by rfl) (Kraken.lex_cons_le_of_lt (by rfl) ?_)
        rw [meas_sub _ _ (show ((e + 1 : Nat) : Int) ≤ ne c by omega) (show ne c < 2 ^ 63 by omega),
          meas_sub _ _ (show (e : Int) ≤ ne c by omega) (show ne c < 2 ^ 63 by omega)]
        omega

set_option maxRecDepth 20000 in
theorem blk_aa5 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.Laa5" := by
  cfg_block
  simp only [tab_Laa5, var_Laa5, tab_Lac5, var_Lac5]
  measure_hb "Laa5"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, e, ⟨hLB, h1c, h48, h50, he, h9, hbx, hsi⟩, hW⟩, hn⟩ := hs₀
    subst hn
    have hm := hLB.1.2.2
    have hC := hLB.1.1
    have hR := hLB.2.1
    have hI := hLB.2.2.1
    have hsx := shr3_le (s₀.regs.get64 .r8) x.p8 hI.2
    vcgen [shr_cl32_havoc]
    all_goals try subst_vars
    all_goals try dsimp only
    all_goals lsimp
    refine ⟨⟨c, f, e, ⟨LB_mv hLB (by rs) (by rs) (by rs; exact hR) ?_ hm, h1c, h48, h50, he,
      by rs; exact h9, by rs; exact hbx, by rs; exact hsi⟩, hW, ?_⟩, ?_⟩
    · rs; rw [hR.2, BitVec.setWidth_32_64_32]
      exact (lix_setl x _ _ hI hC.2.2.2.1 _ _).1
    · rs; exact hsx
    · simp only [slot64, Reg64s.get64_set64, reduceCtorEq, ite_false]
      exact Kraken.lex_cons_le_cons (by rfl) (Kraken.lex_cons_le_cons (by rfl)
        (Kraken.lex_cons_le_of_lt (by rfl) (by decide)))

set_option maxRecDepth 20000 in
theorem blk_ac5 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.Lac5" := by
  cfg_block
  simp only [tab_Lac5, var_Lac5, tab_Laec, var_Laec]
  measure_hb "Lac5"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, e, ⟨hLB, h1c, h48, h50, he, h9, hbx, hsi⟩, hW, hax⟩, hn⟩ := hs₀
    subst hn
    have hm := hLB.1.2.2
    have hC := hLB.1.1
    have hR := hLB.2.1
    have hB := Fr_buf_load hm (s₀.regs.get64 .rax) 1 (by have := hC.2.2.2.2.1; omega)
    have l5 := Fr_vptr_load hm 5 (by omega)
    rw [show 8 * 5 = 40 from rfl] at l5
    have l4 := Fr_vptr_load hm 4 (by omega)
    rw [show 8 * 4 = 32 from rfl] at l4
    have hv28 : (BitVec.setWidth 32 (s₀.regs.get64 .rsi)).toInt = i32 c 28 := by
      rw [hsi, BitVec.setWidth_32_64_32, BitVec.ofInt_toInt]
    vcgen
    case vc1 =>
      subst_vars; try dsimp only
      simp only [AddrIndex.offset64_scale1, add_i64z, hR.1]
      exact hB
    case vc2 =>
      rename_i v1 hv1 f1 f2 f3
      subst_vars; dsimp only
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, AddrIndex.offset64_scale8,
        add_i64z]
      rw [vidx]
      split
      · simp only [l4, Option.isSome_some]
      · simp only [l5, Option.isSome_some]
    case vc3 =>
      rename_i v1 hv1 f1 f2 f3 v2 hv2 af hz
      subst_vars
      dsimp only at hv2 hz ⊢
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, AddrIndex.offset64_scale8,
        add_i64z] at hv2 hz
      rw [vidx] at hv2
      simp only [CondCode.interp_z, StatusFlags.zf_from_result] at hz
      have hv2' : v2 = Int.ofBytes (Int.toBytes 8 (x.v 4).p.toInt) := by
        split at hv2
        · simp only [l4, Option.some.injEq] at hv2; exact hv2.symm
        · rename_i h; simp only [CondCode.interp_z, StatusFlags.zf_from_result, hz, not_true_eq_false, Bool.false_eq_true] at h
      subst hv2'
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.Lbc3") ⟨rfl, ?_, Or.inl ?_⟩
      · refine (tab_Lbc3 _ _ _ _ _ _).mpr ?_
        refine ⟨c, f, e, 4, ⟨LB_mv hLB (by rs) (by rs) (by rs; exact hLB.2.1) (by rs; exact hLB.2.2.1) hm,
          h1c, h48, h50, he, by rs; exact h9, by rs; exact hbx, by rs; exact hsi⟩, hW, ?_, Or.inl rfl⟩
        rs
        rw [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]
      · rw [var_Lbc3]
        simp only [slot64, Reg64s.get64_set64, reduceCtorEq, ite_false]
        exact Kraken.lex_cons_lt_cons (by rfl) (Kraken.lex_cons_lt_cons (by rfl)
          (Kraken.lex_cons_lt_of_lt (by rfl) (by decide)))
    case vc4 =>
      rename_i v1 hv1 f1 f2 f3 v2 hv2 af hz af2 hc
      subst_vars
      dsimp only at hc ⊢
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true] at hc
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.La90") ⟨rfl, ?_, Or.inl ?_⟩
      · refine (tab_La90 _ _ _ _ _ _).mpr ?_
        exact ⟨c, f, e, ⟨LB_mv hLB (by rs) (by rs) (by rs; exact hLB.2.1) (by rs; exact hLB.2.2.1) hm,
          h1c, h48, h50, he, by rs; exact h9, by rs; exact hbx, by rs; exact hsi⟩, hW⟩
      · rw [var_La90]
        simp only [slot64, Reg64s.get64_set64, reduceCtorEq, ite_false]
        exact Kraken.lex_cons_lt_cons (by rfl) (Kraken.lex_cons_lt_cons (by rfl)
          (Kraken.lex_cons_lt_of_lt (by rfl) (by decide)))
    case vc5 =>
      rename_i v1 hv1 f1 f2 f3 v2 hv2 af hz af2 hc
      subst_vars
      dsimp only at hv2 hz hc ⊢
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, AddrIndex.offset64_scale8,
        add_i64z] at hv2 hz hc
      rw [le_test32, hv28, decide_eq_false_iff_not] at hc
      have hpos : 0 < i32 c 28 := Int.not_le.mp hc
      rw [vidx] at hv2
      simp only [CondCode.interp_z, StatusFlags.zf_from_result] at hz
      have hv2' : v2 = Int.ofBytes (Int.toBytes 8 (x.v 5).p.toInt) := by
        split at hv2
        · rename_i h; simp only [CondCode.interp_z, StatusFlags.zf_from_result, hz, not_true_eq_false, Bool.false_eq_true] at h
        · simp only [l5, Option.some.injEq] at hv2; exact hv2.symm
      subst hv2'
      refine ⟨⟨c, f, e, 5, ⟨LB_mv hLB (by rs) (by rs) (by rs; exact hLB.2.1) (by rs; exact hLB.2.2.1) hm,
          h1c, h48, h50, he, by rs; exact h9, by rs; exact hbx, by rs; exact hsi⟩, hW, hpos, ?_,
          Or.inr rfl⟩, ?_⟩
      · rs
        rw [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]
      · simp only [slot64, Reg64s.get64_set64, reduceCtorEq, ite_false]
        exact Kraken.lex_cons_le_cons (by rfl) (Kraken.lex_cons_le_cons (by rfl)
          (Kraken.lex_cons_le_of_lt (by rfl) (by decide)))

set_option maxRecDepth 20000 in
theorem blk_aec (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.Laec" := by
  cfg_block
  simp only [tab_Laec, var_Laec, tab_Lb01, var_Lb01]
  measure_hb "Laec"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, e, j, ⟨hLB, h1c, h48, h50, he, h9, hbx, hsi⟩, hW, hpos, hTb, hj⟩, hn⟩ := hs₀
    subst hn
    have hP := hLB.1.2.1.2.2.2.1
    have hm := hLB.1.2.2
    have hfl := LB_fl hLB
    have hbp := hLB.1.2.1.2.1
    have e1 : s₀.regs.get64 .rbp + 0 + (-104 : Int64).toBitVec
        = rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 0x38 :=
      slot_addr (by rw [hbp]; exact BitVec.add_zero _) 104 0x38 rfl
    have l1 := Fr_f_load hm hfl 0x38 4 (by omega)
    rw [← e1] at l1
    have h38 : BitVec.ofInt 64 (rd f 0x38 8) = BitVec.ofInt 64 (i32 c 40) := hLB.2.2.2.1.2.2.2
    have h40 : 0 ≤ i32 c 40 ∧ i32 c 40 ≤ 5 := hP.2.2.2.2.1
    have h44 : i32 c 44 ≤ 5 := hP.2.2.2.2.2.1.2
    have he' : (e : Int) < i32 c 44 := he
    have he4 : e ≤ 4 := by omega
    obtain ⟨n40, hV0, hn40⟩ : ∃ n : Nat, BitVec.ofInt 32 (rd f 0x38 4) = BitVec.ofNat 32 n ∧ n ≤ 5 :=
      ⟨_, by rw [rd48, ofInt32_of_64 _ _ h38, ofInt32_nn _ h40.1], by omega⟩
    vcgen
    case vc1 =>
      subst_vars
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, l1,
        Option.isSome_some]
    case vc2 =>
      rename_i af2 v1 hv1
      subst_vars
      dsimp only at hv1 ⊢
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, l1,
        Option.some.injEq] at hv1
      subst hv1
      refine ⟨⟨c, f, e, j, max (if e = 0 then n40 else e) 1,
        ⟨LB_mv hLB (by rs) (by rs) (by rs; exact hLB.2.1) (by rs; exact hLB.2.2.1) hm,
        h1c, h48, h50, he, by rs; exact h9, by rs; exact hbx, by rs; exact hsi⟩, hW, hpos,
        by rs; exact hTb, hj, by omega, by split <;> omega, ?_⟩, ?_⟩
      · rs
        rw [h9, z_small e he4]
        by_cases h0 : e = 0
        · subst h0
          simp only [decide_true, ite_true, ↓reduceIte, hV0]
          rcases (show n40 = 0 ∨ n40 = 1 ∨ n40 = 2 ∨ n40 = 3 ∨ n40 = 4 ∨ n40 = 5 by omega) with
            rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
        · simp only [h0, decide_false, Bool.false_eq_true, ite_false, ↓reduceIte, zx3_ofNat e (by omega)]
          rcases (show e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 by omega) with
            rfl | rfl | rfl | rfl <;> rfl
      · simp only [slot64, Reg64s.get64_set64, reduceCtorEq, ite_false]
        exact Kraken.lex_cons_le_cons (by rfl) (Kraken.lex_cons_le_cons (by rfl)
          (Kraken.lex_cons_le_of_lt (by rfl) (by decide)))

set_option maxRecDepth 20000 in
theorem blk_b01 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.Lb01" := by
  cfg_block
  simp only [tab_Lb01, var_Lb01, tab_Lb20, var_Lb20]
  measure_hb "Lb01"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, e, j, ep, ⟨hLB, h1c, h48, h50, he, h9, hbx, hsi⟩, hW, hpos, hTb, hj, hep1, hep5,
      hax⟩, hn⟩ := hs₀
    subst hn
    have hm := hLB.1.2.2
    have hfl := LB_fl hLB
    have hbp := hLB.1.2.1.2.1
    have e1 : s₀.regs.get64 .rbp + 0 + (-80 : Int64).toBitVec
        = rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 0x50 :=
      slot_addr (by rw [hbp]; exact BitVec.add_zero _) 80 0x50 rfl
    have l1 := Fr_f_load hm hfl 0x50 8 (by omega)
    rw [← e1] at l1
    have i5 : (Int64.toBitVec 5).toNat % 256 % 64 = 5 := by decide
    have hrow := row246 (arg2 t₀) ep hep5
    vcgen
    case vc1 =>
      subst_vars
      try dsimp only
      simp only [i5, ↓reduceIte, Reg64s.get64_set64, reduceCtorEq, ite_true,
        ite_false, AddrIndex.offset64_none, l1, Option.isSome_some]
    case vc2 =>
      rename_i a1 a2 a3 v hv a4
      subst_vars
      dsimp only at hv ⊢
      simp only [i5, Nat.reduceEqDiff, ↓reduceIte, AddrIndex.offset64_none, ite_false, reduceCtorEq,
        ite_true, Reg64s.get64_set64, l1, Option.some.injEq] at hv
      subst hv
      simp only [i5, Nat.reduceEqDiff, ↓reduceIte, AddrIndex.offset64_none, ite_false, reduceCtorEq,
        ite_true, Reg64s.get64_set64, AddrIndex.offset64_scale2, h50, hax]
      refine ⟨⟨c, f, e, 0, j, ep, ⟨⟨⟨LB_mv hLB (by rs) (by rs) (by rs; exact hLB.2.1)
        (by rs; exact hLB.2.2.1) hm, h1c, h48, h50, he, h9, hbx, hsi⟩, hpos, ?_,
        by simpa using hpos, hTb, hj⟩, hep1, hep5, by rs; exact hrow⟩, hW⟩, ?_⟩
      · simp only [BitVec.xor_self]; rfl
      · simp only [slot64, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]
        exact Kraken.lex_cons_le_cons (by rfl) (Kraken.lex_cons_le_cons (by rfl)
          (Kraken.lex_cons_le_of_lt (by rfl) (by decide)))

end Kraken.Examples.Sbr.Ps
