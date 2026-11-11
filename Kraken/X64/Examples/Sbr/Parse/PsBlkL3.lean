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
theorem blk_8d0 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.L8d0" := by
  cfg_block
  simp only [tab_L8d0, var_L8d0, tab_L8ed, var_L8ed]
  measure_hb "L8d0"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, e, j, hIE, hW, h11, hTb, hj⟩, hn⟩ := hs₀
    subst hn
    have hLB := hIE.1
    have hP := hLB.1.2.1.2.2.2.1
    have h4 : i32 c 4 ≠ 0 := hIE.2.1.1
    have hm := hLB.1.2.2
    have hfl := LB_fl hLB
    have hbp := hLB.1.2.1.2.1
    have h12 : i32 c 12 ≤ 34 := hP.2.1
    have hv : (BitVec.setWidth 32 (s₀.regs.get64 .r11)).toInt = i32 c 12 := by
      rw [h11, BitVec.setWidth_32_64_32, BitVec.ofInt_toInt]
    have e1 : s₀.regs.get64 .rbp + 0 + (-104 : Int64).toBitVec
        = rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 0x38 :=
      slot_addr (by rw [hbp]; exact BitVec.add_zero _) 104 0x38 rfl
    have l1 := Fr_f_load hm hfl 0x38 4 (by omega)
    rw [← e1] at l1
    obtain ⟨-, hIS, h9, he, hbx, h14⟩ := hIE
    have h38 : BitVec.ofInt 64 (rd f 0x38 8) = BitVec.ofInt 64 (i32 c 40) := hLB.2.2.2.1.2.2.2
    have h40 : 0 ≤ i32 c 40 ∧ i32 c 40 ≤ 5 := hP.2.2.2.2.1
    have h44 : i32 c 44 ≤ 5 := hP.2.2.2.2.2.1.2
    have he' : (e : Int) < i32 c 44 := he
    have he4 : e ≤ 4 := by omega
    obtain ⟨n40, hV0, hn40⟩ : ∃ n : Nat, BitVec.ofInt 32 (rd f 0x38 4) = BitVec.ofNat 32 n ∧ n ≤ 5 :=
      ⟨_, by rw [rd48, ofInt32_of_64 _ _ h38, ofInt32_nn _ h40.1], by omega⟩
    vcgen
    case vc1 =>
      rename_i af hc
      subst_vars
      dsimp only at hc
      rw [le_test32, hv, decide_eq_true_iff] at hc
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.L760") ⟨rfl, ?_, Or.inl ?_⟩
      · refine (tab_L760 _ _ _ _ _ _).mpr ?_
        exact ⟨c, f, e, ⟨hLB, hIS, h9, he, hbx, h14⟩,
          fun hw => WI_step c f e 0 (hW hw) (by simpa using hc) h4⟩
      · rw [var_L760]
        exact Kraken.lex_cons_lt_cons (by rfl) (Kraken.lex_cons_lt_cons (by rfl)
          (Kraken.lex_cons_lt_of_lt (by rfl) (by decide)))
    case vc2 =>
      subst_vars
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, l1,
        Option.isSome_some]
    case vc3 =>
      rename_i af1 hc af2 v1 hv1
      subst_vars
      dsimp only at hc hv1 ⊢
      rw [le_test32, hv, decide_eq_false_iff_not] at hc
      have hpos : 0 < i32 c 12 := Int.not_le.mp hc
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, l1,
        Option.some.injEq] at hv1
      subst hv1
      refine ⟨⟨c, f, e, j, max (if e = 0 then n40 else e) 1,
        ⟨LB_mv hLB (by rs) (by rs) (by rs; exact hLB.2.1) (by rs; exact hLB.2.2.1) hm,
        hIS, by rs; exact h9, he, by rs; exact hbx, by rs; exact h14⟩, hW, ?_, hpos,
        by rs; exact hTb, hj, by omega, by split <;> omega, ?_⟩, ?_⟩
      · rs; rw [h11]; exact sx_pos _ hpos (by omega)
      · rs
        rw [hbx, z_small e he4]
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
theorem blk_8ed (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.L8ed" := by
  cfg_block
  simp only [tab_L8ed, var_L8ed, tab_L910, var_L910]
  measure_hb "L8ed"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, e, j, ep, hIE, hW, h11, hpos, hTb, hj, hep1, hep5, hax⟩, hn⟩ := hs₀
    subst hn
    have hLB := hIE.1
    have hm := hLB.1.2.2
    have hfl := LB_fl hLB
    have hbp := hLB.1.2.1.2.1
    obtain ⟨-, hIS, h9, he, hbx, h14⟩ := hIE
    have h20 : BitVec.ofInt 64 (rd f 0x20 8) = arg2 t₀ + 0x4c#64 := hIS.2.2.1
    have e1 : s₀.regs.get64 .rbp + 0 + (-128 : Int64).toBitVec
        = rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 0x20 :=
      slot_addr (by rw [hbp]; exact BitVec.add_zero _) 128 0x20 rfl
    have l1 := Fr_f_load hm hfl 0x20 8 (by omega)
    rw [← e1] at l1
    have e2 : s₀.regs.get64 .rbp + (-88 : Int64).toBitVec
        = rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 0x48 := slot_addr hbp 88 0x48 rfl
    have s1 := fun v => Fr_f_store hm hfl 0x48 8 (by omega) v
    rw [← e2] at s1
    have i5 : (Int64.toBitVec 5).toNat % 256 % 64 = 5 := by decide
    have l2 := Fr_f_load hm hfl 0x48 8 (by omega)
    rw [← e2] at l2
    have e3 : s₀.regs.get64 .rbp - BitVec.ofNat 64 0x78
        = rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 0x28 := slot_addr_sub hbp 0x78 0x28 rfl
    have l3 := Fr_f_load hm hfl 0x28 8 (by omega)
    rw [← e3] at l3
    have hfl' : (wr f 0x48 8 (s₀.regs.get64 .r14).toInt).length = 0x78 := by fsimp; exact hfl
    have l3' := Fr_f_load (s1 (s₀.regs.get64 .r14).toInt) hfl' 0x28 8 (by omega)
    rw [← e3] at l3'
    have r28 : rd (wr f 0x48 8 (s₀.regs.get64 .r14).toInt) 0x28 8 = rd f 0x28 8 := by fsimp
    rw [r28] at l3'
    have hrow := row34 (arg2 t₀) ep hep5
    vcgen
    case vc1 =>
      subst_vars
      dsimp only
      simp only [i5, Nat.reduceEqDiff, ↓reduceIte, Reg64s.get64_set64, reduceCtorEq, ite_true,
        ite_false, AddrIndex.offset64_none, l1, Option.isSome_some]
    case vc2 =>
      subst_vars
      dsimp only
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, i5, Nat.reduceEqDiff, ↓reduceIte, l2,
        Option.isSome_some]
    case vc3 =>
      rename_i a1 a2 a3 v hv a4
      subst_vars
      dsimp only at hv ⊢
      simp only [i5, Nat.reduceEqDiff, ↓reduceIte, AddrIndex.offset64_none, ite_false, reduceCtorEq, ite_true, Reg64s.get64_set64, l1,
        Option.some.injEq] at hv
      subst hv
      simp only [i5, Nat.reduceEqDiff, ↓reduceIte, AddrIndex.offset64_none, ite_false, reduceCtorEq, ite_true, Reg64s.get64_set64,
        AddrIndex.offset64_scale2, h20, hax]
      refine ⟨⟨c, _, e, 0, j, ep, ⟨⟨⟨LB_wrf hLB (by rs) (by rs) (by rs; exact hLB.2.1)
        (by rs; exact hLB.2.2.1) (s1 _) (by omega), ?_, h9, he, hbx, h14⟩, h11, hpos, ?_,
        by simpa using hpos, hTb, hj, fun hw => by have hw2 := hW hw; simp only [WI] at hw2 ⊢; fsimp; exact hw2⟩, hep1, hep5, hrow, ?_⟩⟩, ?_⟩
      · simp only [IS] at hIS ⊢; fsimp; exact hIS
      · simp only [BitVec.xor_self]; rfl
      · rw [rd_wr_self f 0x48 8 64 _ (by omega) rfl, BitVec.ofInt_toInt, h14]
      · simp only [slot64, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, l3, l3']
        exact Kraken.lex_cons_le_cons (by rfl) (Kraken.lex_cons_le_cons (by rfl)
          (Kraken.lex_cons_le_of_lt (by rfl) (by decide)))

set_option maxRecDepth 20000 in
theorem blk_c7a (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.Lc7a" := by
  cfg_block
  simp only [tab_Lc7a, var_Lc7a]
  measure_hb "Lc7a"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, ⟨hC, ⟨hsp, hbp, hB⟩, hm⟩, h68, hW⟩, hn⟩ := hs₀
    subst hn
    vcgen
    all_goals try subst_vars
    all_goals try dsimp only
    left
    refine Table.ofLabels_at (l := "ff_ps_read_data.L10d6") ⟨rfl, ?_, Or.inl ?_⟩
    · refine (tab_L10d6 _ _ _ _ _ _).mpr ?_
      exact ⟨c, f, ⟨hC, ⟨by rs; exact hsp, by rs; exact hbp, hB⟩, hm⟩, h68, hW⟩
    · rw [var_L10d6]
      exact Kraken.lex_cons_lt_of_lt rfl (by decide)

set_option maxRecDepth 20000 in
theorem blk_a4c (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.La4c" := by
  cfg_block
  simp only [tab_La4c, var_La4c, tab_La6a, var_La6a]
  measure_hb "La4c"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hCm, hR, hI, hS, h10, hW⟩, hn⟩ := hs₀
    subst hn
    have hLB : LB k Ext x ra t₀ s₀ c f := ⟨hCm, hR, hI, hS⟩
    have hm := hCm.2.2
    have hfl := LB_fl hLB
    have hcl := LB_cl hLB
    have hbp := hCm.2.1.2.1
    have h68 : BitVec.ofInt 64 (rd f 0x68 8) = arg2 t₀ := hS.2.2.1
    have hne4 : ne c ≤ 4 := hS.1.2.1
    have hne0 : 0 ≤ ne c := hS.1.1
    have e1 : s₀.regs.get64 .rbp + 0 + (-56 : Int64).toBitVec
        = rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 0x68 :=
      slot_addr (by rw [hbp]; exact BitVec.add_zero _) 56 0x68 rfl
    have l1 := Fr_f_load hm hfl 0x68 8 (by omega)
    rw [← e1] at l1
    have l2 := Fr_c_load hm hcl 20 4 (by omega)
    have e2 : arg2 t₀ + (20 : Int64).toBitVec = arg2 t₀ + BitVec.ofNat 64 20 := rfl
    rw [← e2] at l2
    have e3 : s₀.regs.get64 .rbp + (-132 : Int64).toBitVec
        = rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 0x1c := slot_addr hbp 132 0x1c rfl
    have s1 := fun v => Fr_f_store hm hfl 0x1c 4 (by omega) v
    rw [← e3] at s1
    have l3 := Fr_f_load hm hfl 0x1c 4 (by omega)
    rw [← e3] at l3
    have hw20 : ∀ v : BitVec 64, BitVec.ofInt 32 (rd (wr f 0x1c 4
        (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.ofInt 32 (rd c 20 4)))).toInt) 0x1c 4)
        = BitVec.ofInt 32 (i32 c 20) := fun _ => by
      rw [rd_wr_self f 0x1c 4 32 _ (by omega) rfl, BitVec.ofInt_toInt, BitVec.setWidth_32_64_32,
        rd_i32]
    vcgen
    case vc1 =>
      subst_vars; try dsimp only
      simp only [AddrIndex.offset64_none, l1, Option.isSome_some]
    case vc2 =>
      rename_i v1 hv1
      subst_vars; dsimp only at hv1 ⊢
      simp only [AddrIndex.offset64_none, l1, Option.some.injEq] at hv1
      subst hv1
      simp only [Reg64s.get64_set64, ite_true, h68, l2, Option.isSome_some]
    case vc3 =>
      rename_i v1 hv1 v2 hv2
      subst_vars; try dsimp only at hv1 hv2 ⊢
      simp only [AddrIndex.offset64_none, l1, Option.some.injEq] at hv1
      subst hv1
      simp only [Reg64s.get64_set64, ite_true, h68, l2, Option.some.injEq] at hv2
      subst hv2
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, l3, Option.isSome_some]
    case vc4 =>
      rename_i v1 hv1 v2 hv2 af hz
      subst_vars; try dsimp only at hv1 hv2 ⊢
      simp only [AddrIndex.offset64_none, l1, Option.some.injEq] at hv1
      subst hv1
      simp only [Reg64s.get64_set64, ite_true, h68, l2, Option.some.injEq] at hv2
      subst hv2
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.Lc86") ⟨rfl, ?_, Or.inl ?_⟩
      · refine (tab_Lc86 _ _ _ _ _ _).mpr ?_
        refine ⟨c, _, ⟨LB_wrf (o := 0x1c) (n := 4) hLB (by rs) (by rs) (by rs; exact hR) (by rs; exact hI) (s1 _)
          (by omega), by rs; exact h10, hw20 0, by rs; exact h68⟩, ?_⟩
        intro hw
        obtain ⟨a1, a2, a3, a4, a5⟩ := hW hw
        exact ⟨a1, a2, by fsimp; exact a3, a4, a5⟩
      · rw [var_Lc86]
        exact Kraken.lex_cons_lt_of_lt rfl (by decide)
    case vc5 =>
      rename_i v1 hv1 v2 hv2 af hz af2 hle
      subst_vars; try dsimp only at hv1 hv2 ⊢
      simp only [AddrIndex.offset64_none, l1, Option.some.injEq] at hv1
      subst hv1
      simp only [Reg64s.get64_set64, ite_true, h68, l2, Option.some.injEq] at hv2
      subst hv2
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.Lcba") ⟨rfl, ?_, Or.inl ?_⟩
      · refine (tab_Lcba _ _ _ _ _ _).mpr ?_
        refine ⟨c, _, ?C, ?R, ?I, ?S, hw20 0, by rs; exact h10, ?W⟩
        case C => exact (LB_wrf (o := 0x1c) (n := 4) hLB (by rs) (by rs) (by rs; exact hR)
          (by rs; exact hI) (s1 _) (by omega)).1
        case R => rs; exact hR
        case I => rs; exact hI
        case S => simp only [LSlots, HSlots] at hS ⊢; fsimp; exact hS
        intro hw
        obtain ⟨a1, a2, a3, a4, a5⟩ := hW hw
        exact ⟨a1, a2, by fsimp; exact a3, a4, a5⟩
      · rw [var_Lcba]
        exact Kraken.lex_cons_lt_of_lt rfl (by decide)
    case vc6 =>
      rename_i v1 hv1 v2 hv2 af hz af2 hle
      subst_vars; try dsimp only at hv1 hv2 hle ⊢
      simp only [AddrIndex.offset64_none, l1, Option.some.injEq] at hv1
      subst hv1
      simp only [Reg64s.get64_set64, ite_true, h68, l2, Option.some.injEq] at hv2
      subst hv2
      try simp only [Reg64s.get64_set64, reduceCtorEq, ite_false] at hle
      rw [le8_nat _ _ h10 (by omega), decide_eq_false_iff_not] at hle
      refine ⟨⟨c, _, ⟨LB_wrf (o := 0x1c) (n := 4) hLB (by rs) (by rs) (by rs; exact hR) (by rs; exact hI) (s1 _)
          (by omega), by rs; exact h10, hw20 0, by rs; exact h68⟩, by have h' : ¬ (ne c).toNat = 0 := hle; omega, ?_⟩,
        Kraken.lex_cons_le_of_lt rfl (by decide)⟩
      intro hw
      obtain ⟨a1, a2, a3, a4, a5⟩ := hW hw
      exact ⟨a1, a2, by fsimp; exact a3, a4, a5⟩

set_option maxRecDepth 20000 in
theorem blk_a6a (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.La6a" := by
  cfg_block
  simp only [tab_La6a, var_La6a]
  measure_hb "La6a"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, ⟨hLB, h10, h1c, hax⟩, hne, hW⟩, hn⟩ := hs₀
    subst hn
    have hm := hLB.1.2.2
    have hfl := LB_fl hLB
    have hcl := LB_cl hLB
    have hbp := hLB.1.2.1.2.1
    have h58 : rd f 0x58 8 = ne c := hLB.2.2.2.1.2.2.1
    have hne4 : ne c ≤ 4 := hLB.2.2.2.1.2.1
    have e1 : s₀.regs.get64 .rbp + (-72 : Int64).toBitVec
        = rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 0x58 := slot_addr hbp 72 0x58 rfl
    have l1 := Fr_f_load hm hfl 0x58 4 (by omega)
    rw [← e1] at l1
    have l2 := Fr_c_load hm hcl 28 4 (by omega)
    have e2 : arg2 t₀ + (28 : Int64).toBitVec = arg2 t₀ + BitVec.ofNat 64 28 := rfl
    rw [← e2, ← hax] at l2
    have e3 : s₀.regs.get64 .rbp + (-88 : Int64).toBitVec
        = rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 0x48 := slot_addr hbp 88 0x48 rfl
    have e4 : s₀.regs.get64 .rbp + (-80 : Int64).toBitVec
        = rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 0x50 := slot_addr hbp 80 0x50 rfl
    have s1 := fun v => Fr_f_store hm hfl 0x48 8 (by omega) v
    have s2 := fun v w => Fr_f_store (s1 v) (by fsimp; exact hfl) 0x50 8 (by omega) w
    rw [← e3] at s1 s2
    rw [← e4] at s2
    have l3 := Fr_f_load hm hfl 0x48 8 (by omega)
    rw [← e3] at l3
    have l4 := fun v => Fr_f_load (s1 v) (by fsimp; exact hfl) 0x50 8 (by omega)
    rw [← e4] at l4
    have hv : BitVec.setWidth 64 (BitVec.ofInt 32 (rd f 0x58 4))
        = BitVec.ofNat 64 (ne c).toNat := by
      rw [rd48, h58]; exact sx_pos _ hne (by omega)
    vcgen
    case vc1 =>
      subst_vars; try dsimp only
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, l2, Option.isSome_some]
    case vc2 =>
      rename_i v1 hv1
      subst_vars; try dsimp only at hv1 ⊢
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, l2, Option.some.injEq] at hv1
      subst hv1
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, AddrIndex.offset64_none, l1,
        Option.isSome_some]
    case vc3 =>
      rename_i v1 hv1 v2 hv2
      subst_vars
      try dsimp only at hv1 hv2 ⊢
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, l2, Option.some.injEq] at hv1
      subst hv1
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, AddrIndex.offset64_none, l1,
        Option.some.injEq] at hv2
      subst hv2
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, l3, Option.isSome_some]
    all_goals rename_i v1 hv1 v2 hv2 _
    all_goals subst_vars
    all_goals try dsimp only at hv1 hv2 ⊢
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, l2, Option.some.injEq] at hv1
    all_goals subst hv1
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, AddrIndex.offset64_none, l1,
        Option.some.injEq] at hv2
    all_goals subst hv2
    case vc4 =>
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, l4, Option.isSome_some]
    case vc5 =>
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.Laa5") ⟨rfl, ?_, Or.inl ?_⟩
      · refine (tab_Laa5 _ _ _ _ _ _).mpr ?_
        refine ⟨c, _, 0, ⟨LB_wrf (o := 0x50) (n := 8) (LB_wrf_m (o := 0x48) (n := 8) hLB _ (s1 _)
          (by omega)) (by rs) (by rs) (by rs; exact hLB.2.1) (by rs; exact hLB.2.2.1) (s2 _ _) (by omega),
          ?_, ?_, ?_, by simpa using hne, ?_, ?_, ?_⟩, ?_⟩
        · fsimp; exact h1c
        · rs; fsimp; rw [hv, rd_wr_nat f 0x48 _ (by omega) (by omega)]; exact Int.toNat_of_nonneg (Int.le_of_lt hne)
        · rw [rd_wr_self _ 0x50 8 64 _ (by fsimp; omega) rfl, BitVec.ofInt_toInt]
          rs; rw [hax]; rfl
        · rs; simp only [BitVec.xor_self]; rfl
        · rs; rw [hax]; rfl
        · rs; rw [rd_i32]
        · intro hw
          obtain ⟨a1, a2, a3, a4, a5⟩ := hW hw
          exact ⟨a1, a2, by fsimp; exact a3, a4, a5⟩
      · rw [var_Laa5]
        exact Kraken.lex_cons_lt_of_lt rfl (by decide)

end Kraken.Examples.Sbr.Ps
