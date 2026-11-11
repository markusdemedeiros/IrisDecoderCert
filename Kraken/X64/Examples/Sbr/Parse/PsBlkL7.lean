import Kraken.X64.Examples.Sbr.Parse.PsBlkL6

/-! # `ff_ps_read_data`, shard L: the `iid` band loop with `dt = 1` (`0x910`–`0x9f5`) -/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Ps

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

/-! ## Level 1 of the walk (`0x938`) -/


theorem sw16_64_32 (w : BitVec 16) : BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32 w)) = w := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth]; have := w.isLt; omega

set_option maxRecDepth 20000 in
theorem blk_938 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.L938" := by
  cfg_block
  simp only [tab_L938, var_L938, tab_L94d, var_L94d]
  measure_hb "L938"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, e, b, j, ep, ⟨⟨⟨hLB, hIS, h9, he, hbx, h14⟩, h11, hnr, h10, hb, hTb, hj, hW⟩, hep1, hep5, hdx, h48⟩, hax⟩, hn⟩ := hs₀
    subst hn
    have hm := hLB.1.2.2
    have hC := hLB.1.1
    have hv := vlc3 hC.2.1 hj hax
    have l2 := Fr_vtab_load hm j (by omega) hv.2.1 (4 * (s₀.regs.get64 .rax).toNat + 2) 2 (by omega)
    have l0 := Fr_vtab_load hm j (by omega) hv.2.1 (4 * (s₀.regs.get64 .rax).toNat) 2 (by omega)
    have h30 : (s₀.regs.get64 .rax).toNat < 2 ^ 30 := by omega
    have i2 : Int64.toBitVec 2 = 2#64 := rfl
    vcgen
    case vc1 =>
      rename_i s hs; subst hs
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, offs4', add_i64z, hTb,
        tab_addr0' _ _ h30, l0]; rfl
    case vc2 =>
      rename_i s hs _ _; subst hs
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, offs4', i2, hTb,
        tab_addr2' _ _ h30, l2]; rfl
    case vc3 =>
      rename_i s hs v0 hv0 v1 hv1 _ hc; subst hs
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, offs4', i2, hTb,
        tab_addr2' _ _ h30, l2, Option.some.injEq] at hv1 hc
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, offs4', add_i64z, hTb,
        tab_addr0' _ _ h30, l0, Option.some.injEq] at hv0
      subst hv0 hv1
      rw [ns_sx16, Bool.not_eq_true'] at hc
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.L9da") ⟨rfl, ?_, Or.inl ?_⟩
      · refine (tab_L9da _ _ _ _ _ _).mpr ?_
        exact ⟨c, f, e, b, j, ep, ⟨⟨⟨LB_mv hLB (by rs) (by rs) (by rs; exact hLB.2.1)
          (by rs; exact hLB.2.2.1) hm, hIS, by rs; exact h9, he, by rs; exact hbx, by rs; exact h14⟩,
          by rs; exact h11, hnr, by rs; exact h10, hb, by rs; exact hTb, hj, hW⟩, hep1, hep5, by rs; exact hdx, h48⟩,
          ⟨_, hc, by rs; exact BitVec.setWidth_32_64_32 _⟩⟩
      · rw [var_L9da]
        simp only [slot64, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]
        exact Kraken.lex_cons_lt_cons (by rfl) (Kraken.lex_cons_lt_cons (by rfl)
          (Kraken.lex_cons_lt_cons (by rfl) (Kraken.lex_cons_lt_cons (by rfl)
            (Kraken.lex_cons_lt_of_lt (by rfl) (by decide)))))
    case vc4 =>
      rename_i s hs v0 hv0 v1 hv1 _ hc; subst hs
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, offs4', i2, hTb,
        tab_addr2' _ _ h30, l2, Option.some.injEq] at hv1 hc
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, offs4', add_i64z, hTb,
        tab_addr0' _ _ h30, l0, Option.some.injEq] at hv0
      subst hv0 hv1
      rw [ns_sx16, Bool.not_eq_false'] at hc
      refine ⟨⟨c, f, e, b, j, ep, _, ⟨⟨⟨LB_mv hLB (by rs) (by rs) (by rs; exact hLB.2.1)
          (by rs; exact hLB.2.2.1) hm, hIS, by rs; exact h9, he, by rs; exact hbx, by rs; exact h14⟩,
          by rs; exact h11, hnr, by rs; exact h10, hb, by rs; exact hTb, hj, hW⟩, hep1, hep5, by rs; exact hdx, h48⟩,
          hv.2.2, hc, by rs; exact BitVec.setWidth_32_64_32 _, ?_⟩, ?_⟩
      · rs
        exact sw16_64_32 _
      · simp only [slot64, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]
        exact Kraken.lex_cons_le_cons (by rfl) (Kraken.lex_cons_le_cons (by rfl)
          (Kraken.lex_cons_le_cons (by rfl) (Kraken.lex_cons_le_cons (by rfl)
            (Kraken.lex_cons_le_of_lt (by rfl) (by decide)))))

/-! ## The walk's end: the registers restored (`0x9cd`) -/

set_option maxRecDepth 20000 in
theorem blk_9cd (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.L9cd" := by
  cfg_block
  simp only [tab_L9cd, var_L9cd, tab_L9da, var_L9da]
  measure_hb "L9cd"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, e, b, j, ep, ⟨hLB, hIS, h11, he, hbx, hdi, hnr, h10, hb, hTb, hj, hep1, hep5, h14, h48, hW⟩,
      hlen⟩, hn⟩ := hs₀
    subst hn
    have hm := hLB.1.2.2
    have hfl := LB_fl hLB
    have hbp := hLB.1.2.1.2.1
    have e3 : s₀.regs.get64 .rbp + 0 + (-88 : Int64).toBitVec
        = rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 0x48 :=
      slot_addr (by rw [hbp]; exact BitVec.add_zero _) 88 0x48 rfl
    have e7 : s₀.regs.get64 .rbp - BitVec.ofNat 64 0x78
        = rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 0x28 := slot_addr_sub hbp 0x78 0x28 rfl
    have l7 := Fr_f_load hm hfl 0x28 8 (by omega)
    rw [← e7] at l7
    have l3 := Fr_f_load hm hfl 0x48 8 (by omega)
    rw [← e3] at l3
    vcgen
    case vc1 =>
      subst_vars
      dsimp only
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, l3,
        Option.isSome_some]
    case vc2 =>
      rename_i v hv
      subst_vars
      dsimp only at hv ⊢
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, l3,
        Option.some.injEq] at hv
      subst hv
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
      refine ⟨⟨c, f, e, b, j, ep, ⟨⟨⟨LB_mv hLB (by rs) (by rs) (by rs; exact hLB.2.1)
          (by rs; exact hLB.2.2.1) hm, hIS, ?_, he, hbx, ?_⟩, hdi, hnr, h10, hb, hTb, hj, hW⟩,
          hep1, hep5, h14, h48⟩, hlen⟩, ?_⟩
      · rs; rw [BitVec.setWidth_32_64_32]; exact h11
      · rs; exact h48
      · simp only [slot64, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, l7]
        exact Kraken.lex_cons_le_cons (by rfl) (Kraken.lex_cons_le_cons (by rfl)
          (Kraken.lex_cons_le_cons (by rfl) (Kraken.lex_cons_le_cons (by rfl)
            (Kraken.lex_cons_le_of_lt (by rfl) (by decide)))))

/-! ## The band store (`0x9da`) -/

set_option maxRecDepth 20000 in
theorem blk_9da (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.L9da" := by
  cfg_block
  simp only [tab_L9da, var_L9da, tab_L9f5, var_L9f5]
  measure_hb "L9da"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, e, b, j, ep, ⟨⟨⟨hLB, hIS, h9, he, hbx, h14⟩, h11, hnr, h10, hb, hTb, hj, hW⟩, hep1, hep5, hdx, h48⟩, hlen⟩, hn⟩ := hs₀
    subst hn
    have hm := hLB.1.2.2
    have hcl := LB_cl hLB
    have hP := hLB.1.2.1.2.2.2.1
    have h12 : i32 c 12 ≤ 34 := hP.2.1
    have hne4 : ne c ≤ 4 := hLB.2.2.2.1.2.1
    have hb' : (b : Int) < i32 c 12 := hb
    have he' : (e : Int) < ne c := he
    have hb34 : b < 34 := by omega
    have he5 : e < 5 := by omega
    have he4 : e ≤ 3 := by omega
    have hC := hLB.1.1
    have hp31 : x.p8.toNat < 2 ^ 31 := hC.2.2.2.1
    have hR12 : s₀.regs.get64 .r12 = x.p8.setWidth 64 := hLB.2.1.2
    have hfl := LB_fl hLB
    have hbp := hLB.1.2.1.2.1
    have e32 : ∀ (v : Int) o', o' + 4 ≤ 76 → i32 (wr c (76 + 34 * e + b) 1 v) o' = i32 c o' :=
      fun v o' h' => i32_wr c _ 1 o' v (by omega) (by omega)
    have e3 : s₀.regs.get64 .rbp - BitVec.ofNat 64 0x78
        = rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 0x28 := slot_addr_sub hbp 0x78 0x28 rfl
    have l3 := Fr_f_load hm hfl 0x28 8 (by omega)
    rw [← e3] at l3
    have l3' := fun v => Fr_f_load (Fr_c_store hm hcl (76 + 34 * e + b) 1 (by omega) v) hfl 0x28 8 (by omega)
    simp only [← e3] at l3'
    vcgen
    case vc2 =>
      rename_i hc
      subst_vars
      dsimp only at hc
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, hbx] at hc
      rw [nc_sub5 e he5] at hc
      exact absurd hc Bool.false_ne_true
    case vc1 =>
      subst_vars
      dsimp only
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, AddrIndex.offset64_scale1,
        add_i64z, h14, h10, addr3]
      rw [Fr_c_load hm hcl _ 1 (by omega)]; rfl
    case vc3 =>
      rename_i hc
      subst_vars
      dsimp only
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, AddrIndex.offset64_scale1,
        add_i64z, h14, h10, addr3, hR12, BitVec.setWidth_32_64_32]
      refine ⟨⟨_, f, e, b, j, ep, ⟨⟨⟨LB_wrc _ (o := 76 + 34 * e + b) (n := 1) hLB (by omega) (by omega)
        (by rs) (by rs) (by rs; exact hLB.2.1) ?ix rfl, IS_wr _ hIS hcl (by omega) (by omega), ?r9, ?he,
        by rs; exact hbx, by rs; exact h14⟩, ?r11, ?nr, by rs; exact h10, ?hb, by rs; exact hTb, hj,
        fun hw => WI_wr _ (hW hw) hcl he4 hb34⟩, hep1, hep5, by rs; exact hdx, h48⟩, i8_wr1 _ _ _ (by omega)⟩, ?lex⟩
      case ix =>
        rs
        exact (lix_clampW x _ _ (lenP_lt _ hlen) hLB.2.2.1 hp31 hC.2.2.1 _ _).1
      case r9 => rs; rw [show i32 (wr c (76 + 34 * e + b) 1 _) 8 = i32 c 8 from e32 _ 8 (by omega)]; exact h9
      case he => rw [show ne (wr c (76 + 34 * e + b) 1 _) = ne c from e32 _ 44 (by omega)]; exact he
      case r11 => rs; rw [show i32 (wr c (76 + 34 * e + b) 1 _) 12 = i32 c 12 from e32 _ 12 (by omega)]; exact h11
      case nr => rw [show i32 (wr c (76 + 34 * e + b) 1 _) 12 = i32 c 12 from e32 _ 12 (by omega)]; exact hnr
      case hb => rw [show i32 (wr c (76 + 34 * e + b) 1 _) 12 = i32 c 12 from e32 _ 12 (by omega)]; exact hb
      case lex =>
        simp only [slot64, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, l3, l3']
        exact Kraken.lex_cons_le_cons (by rfl) (Kraken.lex_cons_le_cons (by rfl)
          (Kraken.lex_cons_le_cons (by rfl) (Kraken.lex_cons_le_cons (by rfl)
            (Kraken.lex_cons_le_of_lt (by rfl) (by decide)))))

/-! ## Band `b` checked, the loop step (`0x9f5`) -/

set_option maxRecDepth 20000 in
theorem blk_9f5 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.L9f5" := by
  cfg_block
  simp only [tab_L9f5, var_L9f5]
  measure_hb "L9f5"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, e, b, j, ep, ⟨⟨⟨hLB, hIS, h9, he, hbx, h14⟩, h11, hnr, h10, hb, hTb, hj, hW⟩, hep1, hep5,
      hdx, h48⟩, hi8⟩, hn⟩ := hs₀
    subst hn
    have hm := hLB.1.2.2
    have hP := hLB.1.2.1.2.2.2.1
    have h8 : i32 c 8 = 0 ∨ i32 c 8 = 1 := hP.2.2.2.2.2.2
    have hq := toInt_q _ h8
    have i7 : (Int64.toBitVec 7).toNat % 256 % 32 = 7 := by decide
    have h12 : i32 c 12 ≤ 34 := hP.2.1
    have hbn : b < (i32 c 12).toNat := by have := hb; omega
    have hn63 : (i32 c 12).toNat < 2 ^ 63 := by omega
    vcgen
    case vc1 =>
      rename_i hz
      subst_vars
      dsimp only at hz ⊢
      simp only [i7, Nat.reduceEqDiff, ↓reduceIte, Reg64s.get64_set64, reduceCtorEq, ite_false,
        ite_true, sw8_64_32, BitVec.setWidth_replaceLow8, sw32_64_32_8] at hz
      rw [CondCode.interp_l_cmp_toInt32, abs8, h9, hq] at hz
      try simp only [i7, ↓reduceIte]
      simp only [decide_eq_true_eq] at hz
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.Lc7a") ⟨rfl, ?_, Or.inl ?_⟩
      · refine (tab_Lc7a _ _ _ _ _ _).mpr ?_
        obtain ⟨hC, -, -, hS⟩ := hLB
        obtain ⟨hP0, ⟨hsp, hbp, hB⟩, hM⟩ := hC
        exact ⟨c, f, ⟨hP0, ⟨by rs; exact hsp, by rs; exact hbp, hB⟩, hM⟩, hS.2.2.1,
          fun hw => ⟨(hW hw).1.1, (hW hw).1.2.1⟩⟩
      · rw [var_Lc7a]
        exact Kraken.lex_cons_lt_of_lt rfl (by decide)
    case vc2 =>
      rename_i hz hz2
      subst_vars
      dsimp only at hz hz2 ⊢
      simp only [i7, Nat.reduceEqDiff, ↓reduceIte, Reg64s.get64_set64, reduceCtorEq, ite_false,
        ite_true, sw8_64_32, BitVec.setWidth_replaceLow8, sw32_64_32_8] at hz
      rw [CondCode.interp_l_cmp_toInt32, abs8, h9, hq] at hz
      try simp only [i7, ↓reduceIte]
      simp only [i7, Nat.reduceEqDiff, ↓reduceIte, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, CondCode.interp_nz,
        StatusFlags.zf_from_result, h10, h11] at hz2
      rw [cnt_beq2 _ _ hbn hn63] at hz2
      simp only [decide_eq_false_iff_not] at hz
      have hab := natAbs_le _ _ hz
      have hR : PsWFb x.c → IidR c e (b + 1) := fun hw b' hb' => by
        rcases Nat.lt_or_ge b' b with hl | hl
        · exact (hW hw).2.2.2.2 b' hl
        · have : b' = b := by omega
          subst this
          rw [← hi8] at hab
          exact hab
      simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hz2
      have hz' : b + 1 ≠ (i32 c 12).toNat := hz2
      have hb' : (b : Int) < i32 c 12 := hb
      have hb2 : ((b + 1 : Nat) : Int) < i32 c 12 := by omega
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.L910") ⟨rfl, ?_, Or.inl ?_⟩
      · refine (tab_L910 _ _ _ _ _ _).mpr ?_
        refine ⟨c, f, e, b + 1, j, ep, ⟨⟨LB_mv hLB (by rs) (by rs) (by rs; exact hLB.2.1)
          (by rs; exact hLB.2.2.1) hm, hIS, by rs; exact h9, he, by rs; exact hbx, by rs; exact h14⟩,
          by rs; exact h11, hnr, ?_, hb2, by rs; exact hTb, hj,
          fun hw => ⟨(hW hw).1, (hW hw).2.1, (hW hw).2.2.1, (hW hw).2.2.2.1, hR hw⟩⟩, hep1, hep5,
          by rs; exact hdx, h48⟩
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, h10]
        exact ofNat64_add b 1
      · rw [var_L910]
        simp only [slot64, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, h10, h11]
        refine Kraken.lex_cons_lt_cons (by rfl) (Kraken.lex_cons_lt_cons (by rfl)
          (Kraken.lex_cons_lt_cons (by rfl) (Kraken.lex_cons_lt_of_lt (by rfl) ?_)))
        rw [Nat.mod_eq_of_lt (BitVec.isLt _), Nat.mod_eq_of_lt (BitVec.isLt _)]
        exact meas_b _ _ hbn hn63
    case vc3 =>
      rename_i hz hz2
      subst_vars
      dsimp only at hz hz2 ⊢
      simp only [i7, Nat.reduceEqDiff, ↓reduceIte, Reg64s.get64_set64, reduceCtorEq, ite_false,
        ite_true, sw8_64_32, BitVec.setWidth_replaceLow8, sw32_64_32_8] at hz
      rw [CondCode.interp_l_cmp_toInt32, abs8, h9, hq] at hz
      try simp only [i7, ↓reduceIte]
      simp only [i7, Nat.reduceEqDiff, ↓reduceIte, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, CondCode.interp_nz,
        StatusFlags.zf_from_result, h10, h11] at hz2
      rw [cnt_beq2 _ _ hbn hn63] at hz2
      simp only [decide_eq_false_iff_not] at hz
      have hab := natAbs_le _ _ hz
      have hR : PsWFb x.c → IidR c e (b + 1) := fun hw b' hb' => by
        rcases Nat.lt_or_ge b' b with hl | hl
        · exact (hW hw).2.2.2.2 b' hl
        · have : b' = b := by omega
          subst this
          rw [← hi8] at hab
          exact hab
      simp only [Bool.not_eq_false', decide_eq_true_eq] at hz2
      have hz' : b + 1 = (i32 c 12).toNat := hz2
      have hb' : (b : Int) < i32 c 12 := hb
      have hb2 : i32 c 12 ≤ ((b + 1 : Nat) : Int) := by omega
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.L760") ⟨rfl, ?_, Or.inl ?_⟩
      · refine (tab_L760 _ _ _ _ _ _).mpr ?_
        exact ⟨c, f, e, ⟨LB_mv hLB (by rs) (by rs) (by rs; exact hLB.2.1)
          (by rs; exact hLB.2.2.1) hm, hIS, by rs; exact h9, he, by rs; exact hbx, by rs; exact h14⟩,
          fun hw => WI_step c f e (b + 1) ⟨(hW hw).1, (hW hw).2.1, (hW hw).2.2.1, (hW hw).2.2.2.1, hR hw⟩
            hb2 hIS.1⟩
      · rw [var_L760]
        simp only [slot64, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]
        exact Kraken.lex_cons_lt_cons (by rfl) (Kraken.lex_cons_lt_cons (by rfl)
          (Kraken.lex_cons_lt_of_lt (by rfl) (by decide)))

/-! ## The band loop head, `dt = 1` (`0x910`) -/

theorem addr_prev (A : BitVec 64) (ep b d : Nat) (h1 : 1 ≤ ep) (h5 : ep ≤ 5) (hb : b < 34) (hd : d = 34) :
    A + BitVec.ofNat 64 (76 + 34 * ep) + BitVec.ofNat 64 b + (-(no_index (OfNat.ofNat d : Int64))).toBitVec
      = A + BitVec.ofNat 64 (76 + 34 * (ep - 1) + b) := by
  rw [Int64.toBitVec_neg_ofNat_norm]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  subst hd
  omega

set_option maxRecDepth 20000 in
theorem blk_910 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.L910" := by
  cfg_block
  simp only [tab_L910, var_L910, tab_L938, var_L938]
  measure_hb "L910"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, e, b, j, ep, ⟨⟨⟨hLB, hIS, h9, he, hbx, h14⟩, h11, hnr, h10, hb, hTb, hj, hW⟩, hep1, hep5, hdx, h48⟩⟩, hn⟩ := hs₀
    subst hn
    have hm := hLB.1.2.2
    have hC := hLB.1.1
    have h13 := hLB.2.1.1
    have hI := hLB.2.2.1
    have hp31 : x.p8.toNat < 2 ^ 31 := hC.2.2.2.1
    have hpL : x.p8.toNat / 8 + 4 ≤ x.L := hC.2.2.2.2.1
    have hr32 : (s₀.regs.get64 .r8).toNat < 2 ^ 32 := by omega
    have hcl := LB_cl hLB
    have hP := hLB.1.2.1.2.2.2.1
    have h12 : i32 c 12 ≤ 34 := hP.2.1
    have hb' : (b : Int) < i32 c 12 := hb
    have hb34 : b < 34 := by omega
    have hpa := addr_prev (arg2 t₀) ep b 34 hep1 hep5 hb34 rfl
    have lc := Fr_c_load hm hcl (76 + 34 * (ep - 1) + b) 1 (by omega)
    vcgen [ps_bswap32_havoc, ps_shl_cl32_havoc]
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals pnorm at *
    all_goals try simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      ite_self, AddrIndex.offset64, Width.bytes, BitVec.mul_one, BitVec.setWidth_32_64_32] at *
    all_goals try simp only [h13]
    case vc1 =>
      have hz := ‹CondCode.z.interp _ = true›
      simp only [CondCode.interp_z, StatusFlags.zf_from_result, h10, beq_iff_eq] at hz
      have := congrArg BitVec.toNat hz
      have h0 : (BitVec.zero 64).toNat = 0 := rfl
      simp only [BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat, h0] at this
      omega
    case vc2 =>
      rw [hdx, h10, hpa, lc]; rfl
    case vc3 =>
      exact Fr_buf_load hm _ 4 (by
        simp only [BitVec.toNat_setWidth, toNat_ushiftRight_div]; omega)
    case vc4 =>
      refine ⟨⟨c, f, e, b, j, ep, ⟨⟨⟨LB_mv hLB (by rs) (by rs) (by rs; exact hLB.2.1)
          (by rs; exact hLB.2.2.1) hm, hIS, by rs; exact h9, he, by rs; exact hbx, by rs; exact h14⟩,
          by rs; exact h11, hnr, by rs; exact h10, hb, by rs; exact hTb, hj, hW⟩, hep1, hep5,
          by rs; exact hdx, h48⟩, ?_⟩, ?_⟩
      · simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ite_self]
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans (shr23_lt _) (by decide))]
        exact shr23_lt _
      · first | var_step | (simp only [slot64, get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]
                            exact Kraken.lex_cons_le_cons (by rfl) (Kraken.lex_cons_le_cons (by rfl)
                              (Kraken.lex_cons_le_cons (by rfl) (Kraken.lex_cons_le_cons (by rfl)
                                (Kraken.lex_cons_le_of_lt (by rfl) (by decide))))))

/-! ## Level 2, `dt = 1`: the next window (`0x94d`) -/

set_option maxRecDepth 20000 in
theorem blk_94d (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.L94d" := by
  cfg_block
  simp only [tab_L94d, var_L94d, tab_L96f, var_L96f]
  measure_hb "L94d"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, e, b, j, ep, i, ⟨⟨⟨hLB, hIS, h9, he, hbx, h14⟩, h11, hnr, h10, hb, hTb, hj, hW⟩, hep1, hep5,
      hdx, h48⟩, hV, hmsb, hrl, hrs⟩, hn⟩ := hs₀
    subst hn
    have hm := hLB.1.2.2
    have hC := hLB.1.1
    have h13 := hLB.2.1.1
    have hI := hLB.2.2.1
    have hp31 : x.p8.toNat < 2 ^ 31 := hC.2.2.2.1
    have hpL : x.p8.toNat / 8 + 4 ≤ x.L := hC.2.2.2.2.1
    have hr32 : (s₀.regs.get64 .r8).toNat < 2 ^ 32 := by omega
    have hR12 : s₀.regs.get64 .r12 = x.p8.setWidth 64 := hLB.2.1.2
    have hcw := fun af of => lix_clampW x (s₀.regs.get64 .r8) 9#64 (by decide) hI hp31 hC.2.2.1 af of
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals pnorm at *
    all_goals try simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      ite_self, AddrIndex.offset64, Width.bytes, BitVec.mul_one, BitVec.setWidth_32_64_32] at *
    all_goals try simp only [h13, hR12, BitVec.setWidth_32_64_32]
    case vc1 =>
      exact Fr_buf_load hm _ 4 (buf_ix hpL (hcw _ _).1)
    case vc2 =>
      refine ⟨⟨c, f, e, b, j, ep, i, ⟨LB_mv hLB (by rs) (by rs) (by rs; exact hLB.2.1)
          ?ix hm, hIS, ?r11, he, by rs; exact hbx, by rs; exact h11, hnr, by rs; exact h10, hb,
          by rs; exact hTb, hj, hep1, hep5, by rs; exact hdx, h48, hW⟩, ?wk⟩, ?lex⟩
      case r11 =>
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, BitVec.setWidth_32_64_32]
        exact h9
      case wk =>
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, BitVec.setWidth_32_64_32, hrs]
        exact ⟨hV, hmsb, hrl, BitVec.setWidth_32_64_32 _⟩
      case ix =>
        rs
        exact (hcw _ _).1
      case lex =>
        simp only [slot64, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]
        exact Kraken.lex_cons_le_cons (by rfl) (Kraken.lex_cons_le_cons (by rfl)
          (Kraken.lex_cons_le_cons (by rfl) (Kraken.lex_cons_le_cons (by rfl)
            (Kraken.lex_cons_le_of_lt (by rfl) (by decide)))))

/-! ## Level 2, `dt = 1`: the subtable index (`0x96f`) -/

set_option maxRecDepth 20000 in
theorem blk_96f (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.L96f" := by
  cfg_block
  simp only [tab_L96f, var_L96f, tab_L983, var_L983]
  measure_hb "L96f"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, e, b, j, ep, i, ⟨hLB, hIS, h11, he, hbx, hdi, hnr, h10, hb, hTb, hj, hep1, hep5, h14, h48, hW⟩,
      hV, hmsb, hrl, hrs⟩, hn⟩ := hs₀
    subst hn
    vcgen [ps_bswap32_havoc, ps_shl_cl32_havoc]
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only
    all_goals try simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      ite_self, sw_shr_ite, cnt_sx hrl, hrs, BitVec.setWidth_32_64_32]
    rename_i _ _ _ w _ _ _ _
    have hm32 : (vlen (x.v j).es i).toNat % 32 < 32 := Nat.mod_lt _ (by decide)
    have hI := vwalk_next hV hmsb ((BitVec.setWidth 32 w).ushiftRight
      ((vlen (x.v j).es i).toNat % 32)) (shr_lt _ _ hm32)
    rw [BitVec.add_comm] at hI
    have hm := hLB.1.2.2
    refine ⟨⟨c, f, e, b, j, ep, ⟨LB_mv hLB (by rsw) (by rsw) (by rsw; exact hLB.2.1)
          (by rsw; exact hLB.2.2.1) hm, hIS, by rsw; exact h11, he, by rsw; exact hbx, by rsw; exact hdi, hnr,
          by rsw; exact h10, hb, by rsw; exact hTb, hj, hep1, hep5, by rsw; exact h14, h48, hW⟩, ?_, ?_, ⟨_, hmsb, by rsw; exact hrl⟩⟩, ?_⟩
    · rsw
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans (BitVec.isLt _) (by decide))]
      exact hI
    · rsw
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans (BitVec.isLt _) (by decide))]
      exact BitVec.isLt _
    · simp only [slot64, get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, ite_self]
      exact Kraken.lex_cons_le_cons (by rfl) (Kraken.lex_cons_le_cons (by rfl)
        (Kraken.lex_cons_le_cons (by rfl) (Kraken.lex_cons_le_cons (by rfl)
          (Kraken.lex_cons_le_of_lt (by rfl) (by decide)))))

theorem tab_addrR0 (p r : BitVec 64) (h : r.toNat < 2 ^ 30) :
    p + r * 4#64 = p + BitVec.ofNat 64 (4 * r.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]; omega

theorem tab_addrR2 (p r : BitVec 64) (h : r.toNat < 2 ^ 30) :
    p + r * 4#64 + 2#64 = p + BitVec.ofNat 64 (4 * r.toNat + 2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]; omega

set_option maxRecDepth 20000 in
theorem blk_983 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.L983" := by
  cfg_block
  simp only [tab_L983, var_L983]
  measure_hb "L983"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, e, b, j, ep, ⟨hLB, hIS, h11, he, hbx, hdi, hnr, h10, hb, hTb, hj, hep1, hep5, h14, h48, hW⟩,
      hV, hr9, hLN⟩, hn⟩ := hs₀
    subst hn
    have hm := hLB.1.2.2
    have hC := hLB.1.1
    obtain ⟨h4, hN, -⟩ := hC.2.1 j (by omega)
    simp only [VlcTab.N] at hN
    have hIN := vwalk_lt (d := 1) hV
    have h30 : (s₀.regs.get64 .r9).toNat < 2 ^ 30 := by omega
    have l0 := Fr_vtab_load hm j (by omega) (by omega) (4 * (s₀.regs.get64 .r9).toNat) 2 (by omega)
    have l2 := Fr_vtab_load hm j (by omega) (by omega) (4 * (s₀.regs.get64 .r9).toNat + 2) 2 (by omega)
    have i2 : Int64.toBitVec 2 = 2#64 := rfl
    vcgen
    all_goals subst_vars
    all_goals try dsimp only at *
    case vc1 =>
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, offs4', add_i64z, hTb,
        tab_addrR0 _ _ h30, l0]; rfl
    case vc2 =>
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, offs4', i2, hTb,
        tab_addrR2 _ _ h30, l2]; rfl
    case vc3 =>
      rename_i v0 hv0 v1 hv1 _ hc
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, offs4', i2, hTb,
        tab_addrR2 _ _ h30, l2, Option.some.injEq, BitVec.setWidth_32_64_32] at hv1 hc
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, offs4', add_i64z, hTb,
        tab_addrR0 _ _ h30, l0, Option.some.injEq] at hv0
      subst hv0 hv1
      rw [s_sx16'] at hc
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.L996") ⟨rfl, ?_, Or.inl ?_⟩
      · refine (tab_L996 _ _ _ _ _ _).mpr ?_
        refine ⟨c, f, e, b, j, ep, _, ⟨LB_mv hLB (by rs) (by rs) (by rs; exact hLB.2.1)
          (by rs; exact hLB.2.2.1) hm, hIS, by rs; exact h11, he, by rs; exact hbx, by rs; exact hdi, hnr,
          by rs; exact h10, hb, by rs; exact hTb, hj, hep1, hep5, by rs; exact h14, h48, hW⟩, ⟨hV, hc, ?_, ?_⟩, by rs; exact hLN⟩
        · rs; exact BitVec.setWidth_32_64_32 _
        · rs; exact sw16_64_32 _
      · rw [var_L996]
        simp only [slot64, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]
        exact Kraken.lex_cons_lt_cons (by rfl) (Kraken.lex_cons_lt_cons (by rfl)
          (Kraken.lex_cons_lt_cons (by rfl) (Kraken.lex_cons_lt_cons (by rfl)
            (Kraken.lex_cons_lt_of_lt (by rfl) (by decide)))))
    case vc4 =>
      rename_i v0 hv0 v1 hv1 _ hc
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, offs4', i2, hTb,
        tab_addrR2 _ _ h30, l2, Option.some.injEq, BitVec.setWidth_32_64_32] at hv1 hc
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, offs4', add_i64z, hTb,
        tab_addrR0 _ _ h30, l0, Option.some.injEq] at hv0
      subst hv0 hv1
      rw [s_sx16'] at hc
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.L9cd") ⟨rfl, ?_, Or.inl ?_⟩
      · refine (tab_L9cd _ _ _ _ _ _).mpr ?_
        refine ⟨c, f, e, b, j, ep, ⟨LB_mv hLB (by rs) (by rs) (by rs; exact hLB.2.1)
          (by rs; exact hLB.2.2.1) hm, hIS, by rs; exact h11, he, by rs; exact hbx, by rs; exact hdi, hnr,
          by rs; exact h10, hb, by rs; exact hTb, hj, hep1, hep5, by rs; exact h14, h48, hW⟩, ⟨_, hc, ?_⟩⟩
        rs; simp only [BitVec.setWidth_32_64_32]
      · rw [var_L9cd]
        simp only [slot64, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]
        exact Kraken.lex_cons_lt_cons (by rfl) (Kraken.lex_cons_lt_cons (by rfl)
          (Kraken.lex_cons_lt_cons (by rfl) (Kraken.lex_cons_lt_cons (by rfl)
            (Kraken.lex_cons_lt_of_lt (by rfl) (by decide)))))

set_option maxRecDepth 20000 in
theorem blk_996 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.L996" := by
  cfg_block
  simp only [tab_L996, var_L996, tab_L9b1, var_L9b1]
  measure_hb "L996"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, e, b, j, ep, i, ⟨hLB, hIS, h11, he, hbx, hdi, hnr, h10, hb, hTb, hj, hep1, hep5, h14, h48, hW⟩,
      ⟨hV, hmsb, hrl, hrs⟩, hLN⟩, hn⟩ := hs₀
    subst hn
    have hm := hLB.1.2.2
    have hC := hLB.1.1
    have h13 := hLB.2.1.1
    have hI := hLB.2.2.1
    have hp31 : x.p8.toNat < 2 ^ 31 := hC.2.2.2.1
    have hpL : x.p8.toNat / 8 + 4 ≤ x.L := hC.2.2.2.2.1
    have hr32 : (s₀.regs.get64 .r8).toNat < 2 ^ 32 := by omega
    have hR12 : s₀.regs.get64 .r12 = x.p8.setWidth 64 := hLB.2.1.2
    have hcw := fun af of => lix_clampN x (s₀.regs.get64 .r8) (s₀.regs.get64 .rax) (lenN_ge _ hLN) hI hp31 hC.2.2.1 af of
    vcgen [ps_bswap32_havoc, ps_shl_cl32_havoc]
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals pnorm at *
    all_goals try simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      ite_self, AddrIndex.offset64, Width.bytes, BitVec.mul_one, BitVec.setWidth_32_64_32] at *
    all_goals try simp only [h13, hR12, BitVec.setWidth_32_64_32]
    case vc1 =>
      exact Fr_buf_load hm _ 4 (buf_ix hpL (hcw _ _))
    case vc2 =>
      refine ⟨⟨c, f, e, b, j, ep, i, ⟨LB_mv hLB (by rsw) (by rsw) (by rsw; exact hLB.2.1)
          ?ix hm, hIS, by rsw; exact h11, he, by rsw; exact hbx, by rsw; exact hdi, hnr, by rsw; exact h10, hb,
          by rsw; exact hTb, hj, hep1, hep5, by rsw; exact h14, h48, hW⟩, ?wk⟩, ?lex⟩
      case wk =>
        simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, ite_self,
          BitVec.setWidth_32_64_32, hrs]
        exact ⟨hV, hmsb, hrl, BitVec.setWidth_32_64_32 _⟩
      case ix =>
        rsw
        exact hcw _ _
      case lex =>
        simp only [slot64, get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, ite_self]
        exact Kraken.lex_cons_le_cons (by rfl) (Kraken.lex_cons_le_cons (by rfl)
          (Kraken.lex_cons_le_cons (by rfl) (Kraken.lex_cons_le_cons (by rfl)
            (Kraken.lex_cons_le_of_lt (by rfl) (by decide)))))

set_option maxRecDepth 20000 in
theorem blk_9b1 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.L9b1" := by
  cfg_block
  simp only [tab_L9b1, var_L9b1, tab_L9cd, var_L9cd]
  measure_hb "L9b1"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, e, b, j, ep, i, ⟨hLB, hIS, h11, he, hbx, hdi, hnr, h10, hb, hTb, hj, hep1, hep5, h14, h48, hW⟩,
      hV, hmsb, hrl, hrs⟩, hn⟩ := hs₀
    subst hn
    have hm := hLB.1.2.2
    have hC := hLB.1.1
    obtain ⟨h4, hN, -⟩ := hC.2.1 j (by omega)
    simp only [VlcTab.N] at hN
    have hm32 : (vlen (x.v j).es i).toNat % 32 < 32 := Nat.mod_lt _ (by decide)
    have i2 : Int64.toBitVec 2 = 2#64 := rfl
    have hI : ∀ w : BitVec 64, VWalk (x.v j).es 1 ((vsym (x.v j).es i).signExtend 32 +
        (BitVec.setWidth 32 w).ushiftRight ((vlen (x.v j).es i).toNat % 32)).toNat := fun w => by
      have h := vwalk_next hV hmsb ((BitVec.setWidth 32 w).ushiftRight ((vlen (x.v j).es i).toNat % 32))
        (shr_lt _ _ hm32)
      rw [BitVec.add_comm] at h; exact h
    have h30 : ∀ w : BitVec 64, ((vsym (x.v j).es i).signExtend 32 +
        (BitVec.setWidth 32 w).ushiftRight ((vlen (x.v j).es i).toNat % 32)).toNat < 2 ^ 30 := fun w => by
      have := vwalk_lt (hI w); omega
    have l0 : ∀ w : BitVec 64, _ := fun w => Fr_vtab_load hm j (by omega) (by omega) (4 * ((vsym (x.v j).es i).signExtend 32 +
        (BitVec.setWidth 32 w).ushiftRight ((vlen (x.v j).es i).toNat % 32)).toNat) 2 (by have := vwalk_lt (hI w); omega)
    have l2 : ∀ w : BitVec 64, _ := fun w => Fr_vtab_load hm j (by omega) (by omega) (4 * ((vsym (x.v j).es i).signExtend 32 +
        (BitVec.setWidth 32 w).ushiftRight ((vlen (x.v j).es i).toNat % 32)).toNat + 2) 2 (by have := vwalk_lt (hI w); omega)
    vcgen [ps_shl_cl32_havoc]
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    case vc1 =>
      simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
        ite_self, sw_shr_ite, cnt_sx hrl, hrs, offs4', add_i64z, hTb, BitVec.setWidth_32_64_32]
      rw [tab_addrI0 _ _ (h30 _), l0]; rfl
    case vc2 =>
      simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
        ite_self, sw_shr_ite, cnt_sx hrl, hrs, offs4', i2, hTb, BitVec.setWidth_32_64_32]
      rw [tab_addrI2 _ _ (h30 _), l2]; rfl
    case vc3 =>
      rename_i _ w _ _ _ _ v0 v1 hv0 hv1
      simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
        ite_self, sw_shr_ite, cnt_sx hrl, hrs, offs4', add_i64z, i2, hTb, BitVec.setWidth_32_64_32] at hv0 hv1
      rw [tab_addrI0 _ _ (h30 _), l0, Option.some.injEq] at hv0
      rw [tab_addrI2 _ _ (h30 _), l2, Option.some.injEq] at hv1
      subst hv0 hv1
      simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ite_self]
      refine ⟨⟨c, f, e, b, j, ep, ⟨LB_mv hLB (by rsw) (by rsw) (by rsw; exact hLB.2.1)
          (by rsw; exact hLB.2.2.1) hm, hIS, by rsw; exact h11, he, by rsw; exact hbx, by rsw; exact hdi, hnr,
          by rsw; exact h10, hb, by rsw; exact hTb, hj, hep1, hep5, by rsw; exact h14, h48, hW⟩,
          ⟨_, vwalk1_msb (hI w), ?_⟩⟩, ?_⟩
      · (try rsw) <;> (try simp only [BitVec.setWidth_32_64_32])
      · simp only [slot64, get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, ite_self]
        exact Kraken.lex_cons_le_cons (by rfl) (Kraken.lex_cons_le_cons (by rfl)
          (Kraken.lex_cons_le_cons (by rfl) (Kraken.lex_cons_le_cons (by rfl)
            (Kraken.lex_cons_le_of_lt (by rfl) (by decide)))))

end Kraken.Examples.Sbr.Ps
