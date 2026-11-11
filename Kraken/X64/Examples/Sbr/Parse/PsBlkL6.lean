import Kraken.X64.Examples.Sbr.Parse.PsBlkL5

/-! # `ff_ps_read_data`, shard L: the `iid` band loop with `dt = 0` (`0x7e0`–`0x8bb`) -/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Ps

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

/-! ## Lemmas for `0x880` (the band store) -/

theorem z_sub34 (b : Nat) (hb : b < 34) (fl : StatusFlags.from_result.Remaining) :
    CondCode.z.interp (StatusFlags.from_result (BitVec.ofNat 64 b - BitVec.setWidth 64 (Int64.toBitVec 34)) fl)
      = false := by
  simp only [CondCode.interp_z, StatusFlags.zf_from_result]
  have h34 : (BitVec.setWidth 64 (Int64.toBitVec 34)).toNat = 34 := by decide
  rw [beq_eq_false_iff_ne]
  intro h
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_sub, h34, BitVec.toNat_ofNat] at this
  have h0 : (BitVec.zero 64).toNat = 0 := rfl
  rw [h0] at this
  omega

theorem nc_sub5 (e : Nat) (he : e < 5) (af of : Bool) :
    CondCode.nc.interp (StatusFlags.from_result (BitVec.ofNat 64 e - BitVec.setWidth 64 (Int64.toBitVec 5))
      { cf := (BitVec.ofNat 64 e - BitVec.setWidth 64 (Int64.toBitVec 5)).unsigned !=
          (BitVec.ofNat 64 e).unsigned - (BitVec.setWidth 64 (Int64.toBitVec 5)).unsigned,
        af := af, of := of }) = false := by
  rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 by omega) with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem addr3 (a : BitVec 64) (m n : Nat) :
    a + BitVec.ofNat 64 m + BitVec.ofNat 64 n = a + BitVec.ofNat 64 (m + n) := by
  rw [BitVec.add_assoc, ← ofNat64_add]
omit [CodeEnv] in
theorem lix_clampW (x : PArgs) (r d : BitVec 64) (hd : (BitVec.setWidth 32 d).toNat < 2 ^ 15) (hr : Ix x r)
    (hp : x.p8.toNat < 2 ^ 31) (hi : x.idx.toNat ≤ x.p8.toNat) (af of : Bool) :
    Ix x (BitVec.setWidth 64 (if CondCode.c.interp (StatusFlags.from_result
        (x.p8 - (BitVec.setWidth 32 d + BitVec.setWidth 32 r))
        { cf := (x.p8 - (BitVec.setWidth 32 d + BitVec.setWidth 32 r)).unsigned !=
            x.p8.unsigned - (BitVec.setWidth 32 d + BitVec.setWidth 32 r).unsigned,
          af := af, of := of }) = true
      then x.p8 else BitVec.setWidth 32 d + BitVec.setWidth 32 r))
    ∧ r.toNat ≤ (BitVec.setWidth 64 (if CondCode.c.interp (StatusFlags.from_result
        (x.p8 - (BitVec.setWidth 32 d + BitVec.setWidth 32 r))
        { cf := (x.p8 - (BitVec.setWidth 32 d + BitVec.setWidth 32 r)).unsigned !=
            x.p8.unsigned - (BitVec.setWidth 32 d + BitVec.setWidth 32 r).unsigned,
          af := af, of := of }) = true
      then x.p8 else BitVec.setWidth 32 d + BitVec.setWidth 32 r)).toNat := by
  obtain ⟨h1, h2⟩ := hr
  have e : (BitVec.setWidth 32 d + BitVec.setWidth 32 r).toNat
      = (BitVec.setWidth 32 d).toNat + r.toNat := by
    have : (BitVec.setWidth 32 r).toNat = r.toNat % 2 ^ 32 := by simp [BitVec.toNat_setWidth]
    have := (BitVec.setWidth 32 d).isLt
    rw [BitVec.toNat_add]; omega
  have h64 : ∀ y : BitVec 32, (BitVec.setWidth 64 y).toNat = y.toNat := fun y => by
    rw [BitVec.toNat_setWidth]; have := y.isLt; omega
  simp only [Ix, h64]
  split
  · have := x.p8.isLt
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> omega
  · rename_i h
    simp only [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, bne_iff_ne, ne_eq,
      Decidable.not_not] at h
    rw [BitVec.toNat_sub] at h
    rw [e] at h ⊢
    have := x.p8.isLt
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> omega

theorem i8_byte_aux : ∀ n, n < 256 →
    (BitVec.ofNat 8 ((Int.toBytes 1 (BitVec.ofNat 8 n).toInt).getD 0 0).toNat).toInt
      = (BitVec.ofNat 8 n).toInt := by
  decide +kernel

theorem i8_wr1 (c : List UInt8) (o : Nat) (y : BitVec 8) (h : o + 1 ≤ c.length) :
    i8 (wr c o 1 y.toInt) o = y.toInt := by
  simp only [i8]
  rw [l5_getD_wr c o 1 o _ h]
  simp only [Nat.le_refl, Nat.lt_add_one, and_self, ↓reduceIte, Nat.sub_self]
  have := i8_byte_aux y.toNat y.isLt
  rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this

theorem lenP_lt (v : BitVec 64) (h : LenP v) : (v.setWidth 32).toNat < 2 ^ 15 := by
  obtain ⟨l, hl, he⟩ := h
  rw [he, BitVec.signExtend_eq_setWidth_of_msb_false hl, BitVec.toNat_setWidth]
  have := (BitVec.msb_eq_false_iff_two_mul_lt).mp hl
  omega

theorem IS_wr {t₀ : MachineData} {c f : List UInt8} {o n : Nat} (v : Int) (h : IS t₀ c f)
    (hl : c.length = 764) (ho : 76 ≤ o) (hn : o + n ≤ 764) : IS t₀ (wr c o n v) f := by
  simp (disch := omega) only [IS, ne, i32_wr] at h ⊢
  exact h

theorem WI_wr {c f : List UInt8} {e b : Nat} (v : Int) (h : WI c f e b) (hl : c.length = 764)
    (he : e ≤ 3) (hb : b < 34) : WI (wr c (76 + 34 * e + b) 1 v) f e b := by
  have e32 : ∀ o', o' + 4 ≤ 76 → i32 (wr c (76 + 34 * e + b) 1 v) o' = i32 c o' :=
    fun o' h' => i32_wr c _ 1 o' v (by omega) (by omega)
  obtain ⟨hR, hH, hS, hB, hI⟩ := h
  obtain ⟨r1, r2, r3⟩ := ZW_wr v (o := 76 + 34 * e + b) (n := 1) hl (by omega) (by omega) ⟨hR, hH, hS⟩
  refine ⟨r1, r2, r3, ?_, ?_⟩
  · intro e' he' b' hb' hc
    rw [e32 4 (by omega), e32 12 (by omega)] at hc
    rw [e32 8 (by omega), i8_wr c _ 1 _ v (by omega) (by omega)]
    exact hB e' he' b' hb' hc
  · intro b' hb'
    rw [e32 8 (by omega), i8_wr c _ 1 _ v (by omega) (by omega)]
    exact hI b' hb'


set_option maxRecDepth 20000 in
theorem blk_8bb (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.L8bb" := by
  cfg_block
  simp only [tab_L8bb, var_L8bb]
  measure_hb "L8bb"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, e, b, j, ⟨⟨hLB, hIS, h9, he, hbx, h14⟩, h11, hnr, h10, hb, hTb, hj, hW⟩, hR⟩, hn⟩ := hs₀
    subst hn
    have hm := hLB.1.2.2
    have hP := hLB.1.2.1.2.2.2.1
    have h12 : i32 c 12 ≤ 34 := hP.2.1
    have hbn : b < (i32 c 12).toNat := by have := hb; omega
    have hn63 : (i32 c 12).toNat < 2 ^ 63 := by omega
    vcgen
    all_goals rename_i hz
    all_goals subst_vars
    all_goals try dsimp only at hz ⊢
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, CondCode.interp_nz,
      StatusFlags.zf_from_result, h10, h11] at hz
    all_goals rw [cnt_beq2 _ _ hbn hn63] at hz
    case vc1 =>
      simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hz
      have hz' : b + 1 ≠ (i32 c 12).toNat := hz
      have hb' : (b : Int) < i32 c 12 := hb
      have hb2 : ((b + 1 : Nat) : Int) < i32 c 12 := by omega
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.L7e0") ⟨rfl, ?_, Or.inl ?_⟩
      · refine (tab_L7e0 _ _ _ _ _ _).mpr ?_
        refine ⟨c, f, e, b + 1, j, ⟨⟨LB_mv hLB (by rs) (by rs) (by rs; exact hLB.2.1)
          (by rs; exact hLB.2.2.1) hm, hIS, by rs; exact h9, he, by rs; exact hbx, by rs; exact h14⟩,
          by rs; exact h11, hnr, ?_, hb2, by rs; exact hTb, hj,
          fun hw => ⟨(hW hw).1, (hW hw).2.1, (hW hw).2.2.1, (hW hw).2.2.2.1, hR hw⟩⟩⟩
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, h10]
        exact ofNat64_add b 1
      · rw [var_L7e0]
        simp only [slot64, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, h10, h11]
        refine Kraken.lex_cons_lt_cons (by rfl) (Kraken.lex_cons_lt_cons (by rfl)
          (Kraken.lex_cons_lt_cons (by rfl) (Kraken.lex_cons_lt_of_lt (by rfl) ?_)))
        rw [Nat.mod_eq_of_lt (BitVec.isLt _), Nat.mod_eq_of_lt (BitVec.isLt _)]
        exact meas_b _ _ hbn hn63
    case vc2 =>
      simp only [Bool.not_eq_false', decide_eq_true_eq] at hz
      have hz' : b + 1 = (i32 c 12).toNat := hz
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

set_option maxRecDepth 20000 in
theorem blk_7e0 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.L7e0" := by
  cfg_block
  simp only [tab_L7e0, var_L7e0, tab_L7f8, var_L7f8]
  measure_hb "L7e0"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, e, b, j, ⟨⟨hLB, hIS, h9, he, hbx, h14⟩, h11, hnr, h10, hb, hTb, hj, hW⟩⟩, hn⟩ := hs₀
    subst hn
    have hm := hLB.1.2.2
    have hC := hLB.1.1
    have h13 := hLB.2.1.1
    have hI := hLB.2.2.1
    have hp31 : x.p8.toNat < 2 ^ 31 := hC.2.2.2.1
    have hpL : x.p8.toNat / 8 + 4 ≤ x.L := hC.2.2.2.2.1
    have hr32 : (s₀.regs.get64 .r8).toNat < 2 ^ 32 := by omega
    vcgen [ps_bswap32_havoc, ps_shl_cl32_havoc]
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals pnorm at *
    all_goals try simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      ite_self, AddrIndex.offset64, Width.bytes, BitVec.mul_one, BitVec.setWidth_32_64_32] at *
    all_goals try simp only [h13]
    case vc1 =>
      exact Fr_buf_load hm _ 4 (by
        simp only [BitVec.toNat_setWidth, toNat_ushiftRight_div]; omega)
    case vc2 =>
      refine ⟨⟨c, f, e, b, j, ⟨⟨LB_mv hLB (by rs) (by rs) (by rs; exact hLB.2.1)
          (by rs; exact hLB.2.2.1) hm, hIS, by rs; exact h9, he, by rs; exact hbx, by rs; exact h14⟩,
          by rs; exact h11, hnr, by rs; exact h10, hb, by rs; exact hTb, hj, hW⟩, ?_⟩, ?_⟩
      · simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ite_self]
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans (shr23_lt _) (by decide))]
        exact shr23_lt _
      · first | var_step | (simp only [slot64, get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]
                            exact Kraken.lex_cons_le_cons (by rfl) (Kraken.lex_cons_le_cons (by rfl)
                              (Kraken.lex_cons_le_cons (by rfl) (Kraken.lex_cons_le_cons (by rfl)
                                (Kraken.lex_cons_le_of_lt (by rfl) (by decide))))))

set_option maxRecDepth 20000 in
theorem blk_8a4 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.L8a4" := by
  cfg_block
  simp only [tab_L8a4, var_L8a4, tab_L8bb, var_L8bb]
  measure_hb "L8a4"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, e, b, j, ⟨⟨hLB, hIS, h9, he, hbx, h14⟩, h11, hnr, h10, hb, hTb, hj, hW⟩, hi8⟩, hn⟩ := hs₀
    subst hn
    have hm := hLB.1.2.2
    have hP := hLB.1.2.1.2.2.2.1
    have h8 : i32 c 8 = 0 ∨ i32 c 8 = 1 := hP.2.2.2.2.2.2
    have hq := toInt_q _ h8
    have i7 : (Int64.toBitVec 7).toNat % 256 % 32 = 7 := by decide
    vcgen
    all_goals rename_i hz
    all_goals subst_vars
    all_goals try dsimp only at hz ⊢
    all_goals simp only [i7, Nat.reduceEqDiff, ↓reduceIte, Reg64s.get64_set64, reduceCtorEq, ite_false,
      ite_true, sw8_64_32, BitVec.setWidth_replaceLow8, sw32_64_32_8] at hz
    all_goals rw [CondCode.interp_l_cmp_toInt32, abs8, h9, hq] at hz
    all_goals try simp only [i7, ↓reduceIte]
    case vc1 =>
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
      simp only [decide_eq_false_iff_not] at hz
      have hab := natAbs_le _ _ hz
      refine ⟨⟨c, f, e, b, j, ⟨⟨LB_mv hLB (by rs) (by rs) (by rs; exact hLB.2.1)
          (by rs; exact hLB.2.2.1) hm, hIS, by rs; exact h9, he, by rs; exact hbx, by rs; exact h14⟩,
          by rs; exact h11, hnr, by rs; exact h10, hb, by rs; exact hTb, hj, hW⟩, fun hw => ?_⟩, ?_⟩
      · intro b' hb'
        rcases Nat.lt_or_ge b' b with hl | hl
        · exact (hW hw).2.2.2.2 b' hl
        · have : b' = b := by omega
          subst this
          rw [← hi8] at hab
          exact hab
      · simp only [slot64, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]
        exact Kraken.lex_cons_le_cons (by rfl) (Kraken.lex_cons_le_cons (by rfl)
          (Kraken.lex_cons_le_cons (by rfl) (Kraken.lex_cons_le_cons (by rfl)
            (Kraken.lex_cons_le_of_lt (by rfl) (by decide)))))

set_option maxRecDepth 20000 in
theorem blk_880 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.L880" := by
  cfg_block
  simp only [tab_L880, var_L880, tab_L8a4, var_L8a4]
  measure_hb "L880"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, e, b, j, ⟨⟨hLB, hIS, h9, he, hbx, h14⟩, h11, hnr, h10, hb, hTb, hj, hW⟩, hlen⟩, hn⟩ := hs₀
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
    case vc1 =>
      rename_i hz
      subst_vars
      dsimp only at hz
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, h10] at hz
      rw [z_sub34 b hb34] at hz
      exact absurd hz Bool.false_ne_true
    case vc3 =>
      rename_i hz hc
      subst_vars
      dsimp only at hc
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, hbx] at hc
      rw [nc_sub5 e he5] at hc
      exact absurd hc Bool.false_ne_true
    case vc2 =>
      rename_i hz
      subst_vars
      dsimp only
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, AddrIndex.offset64_scale1,
        add_i64z, h14, h10, addr3]
      rw [Fr_c_load hm hcl _ 1 (by omega)]; rfl
    case vc4 =>
      rename_i hz hc
      subst_vars
      dsimp only
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, AddrIndex.offset64_scale1,
        add_i64z, h14, h10, addr3, hR12, BitVec.setWidth_32_64_32]
      refine ⟨⟨_, f, e, b, j, ⟨⟨LB_wrc _ (o := 76 + 34 * e + b) (n := 1) hLB (by omega) (by omega)
        (by rs) (by rs) (by rs; exact hLB.2.1) ?ix rfl, IS_wr _ hIS hcl (by omega) (by omega), ?r9, ?he,
        by rs; exact hbx, by rs; exact h14⟩, ?r11, ?nr, by rs; exact h10, ?hb, by rs; exact hTb, hj,
        fun hw => WI_wr _ (hW hw) hcl he4 hb34⟩, i8_wr1 _ _ _ (by omega)⟩, ?lex⟩
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

/-! ## Level 1 of the walk (`0x7f8`) -/

/-- A depth-3 (`iid`) table: every 9-bit index starts a 3-level walk. -/
theorem vlc3 {v : Nat → VlcTab} (hv : VlcC v) {j : Nat} (hj : j < 4) {i : Nat} (hi : i < 512) :
    4 * i + 4 ≤ (v j).es.length ∧ (v j).es.length < 2 ^ 32 ∧ VWalk (v j).es 3 i := by
  have h := hv j (by omega)
  have hb : vbits j = 9 := by simp only [vbits]; split <;> omega
  have hd : vdepth j = 3 := by simp only [vdepth]; split <;> omega
  rw [hb, hd] at h
  obtain ⟨h4, hN, hw⟩ := h
  have hW := hw i (by omega)
  have hlt : i < (v j).es.length / 4 := by simp only [VWalk] at hW; exact hW.1
  simp only [VlcTab.N] at hN
  exact ⟨by omega, by omega, hW⟩

theorem tab_addr0' (p r : BitVec 64) (h : r.toNat < 2 ^ 30) :
    p + BitVec.setWidth 64 (BitVec.setWidth 32 r) * 4#64 = p + BitVec.ofNat 64 (4 * r.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

theorem tab_addr2' (p r : BitVec 64) (h : r.toNat < 2 ^ 30) :
    p + BitVec.setWidth 64 (BitVec.setWidth 32 r) * 4#64 + 2#64
      = p + BitVec.ofNat 64 (4 * r.toNat + 2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
theorem offs4' (i : Reg64) (r : Reg64s) :
    AddrIndex.offset64 (some { reg := i, scale := Width.W32 }) r = r.get64 i * 4#64 := by
  simp [AddrIndex.offset64]

theorem ns_sx16 (w : BitVec 16) (fl : StatusFlags.from_result.Remaining) :
    CondCode.ns.interp (StatusFlags.from_result
      (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.signExtend 32 w)) &&&
        BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.signExtend 32 w))) fl) = !w.msb := by
  rw [CondCode.interp_ns, StatusFlags.sf_from_result, BitVec.and_self, BitVec.setWidth_32_64_32]
  simp [BitVec.msb_signExtend]

set_option maxRecDepth 20000 in
theorem blk_7f8 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.L7f8" := by
  cfg_block
  simp only [tab_L7f8, var_L7f8, tab_L809, var_L809, tab_L880, var_L880]
  measure_hb "L7f8"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, e, b, j, ⟨⟨hLB, hIS, h9, he, hbx, h14⟩, h11, hnr, h10, hb, hTb, hj, hW⟩, hax⟩, hn⟩ := hs₀
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
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, offs4', i2, add_i64z, hTb,
        tab_addr2' _ _ h30, l2, Option.some.injEq] at hv1 hc
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, offs4', add_i64z, hTb,
        tab_addr0' _ _ h30, l0, Option.some.injEq] at hv0
      subst hv0 hv1
      rw [ns_sx16, Bool.not_eq_true'] at hc
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.L880") ⟨rfl, ?_, Or.inl ?_⟩
      · refine (tab_L880 _ _ _ _ _ _).mpr ?_
        exact ⟨c, f, e, b, j, ⟨⟨LB_mv hLB (by rs) (by rs) (by rs; exact hLB.2.1)
          (by rs; exact hLB.2.2.1) hm, hIS, by rs; exact h9, he, by rs; exact hbx, by rs; exact h14⟩,
          by rs; exact h11, hnr, by rs; exact h10, hb, by rs; exact hTb, hj, hW⟩,
          ⟨_, hc, by rs; exact BitVec.setWidth_32_64_32 _⟩⟩
      · rw [var_L880]
        simp only [slot64, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]
        exact Kraken.lex_cons_lt_cons (by rfl) (Kraken.lex_cons_lt_cons (by rfl)
          (Kraken.lex_cons_lt_cons (by rfl) (Kraken.lex_cons_lt_cons (by rfl)
            (Kraken.lex_cons_lt_of_lt (by rfl) (by decide)))))
    case vc4 =>
      rename_i s hs v0 hv0 v1 hv1 _ hc; subst hs
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, offs4', i2, add_i64z, hTb,
        tab_addr2' _ _ h30, l2, Option.some.injEq] at hv1 hc
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, offs4', add_i64z, hTb,
        tab_addr0' _ _ h30, l0, Option.some.injEq] at hv0
      subst hv0 hv1
      rw [ns_sx16, Bool.not_eq_false'] at hc
      refine ⟨⟨c, f, e, b, j, _, ⟨⟨LB_mv hLB (by rs) (by rs) (by rs; exact hLB.2.1)
          (by rs; exact hLB.2.2.1) hm, hIS, by rs; exact h9, he, by rs; exact hbx, by rs; exact h14⟩,
          by rs; exact h11, hnr, by rs; exact h10, hb, by rs; exact hTb, hj, hW⟩,
          hv.2.2, hc, by rs; exact BitVec.setWidth_32_64_32 _, by rs; exact BitVec.setWidth_32_64_32 _⟩, ?_⟩
      simp only [slot64, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]
      exact Kraken.lex_cons_le_cons (by rfl) (Kraken.lex_cons_le_cons (by rfl)
        (Kraken.lex_cons_le_cons (by rfl) (Kraken.lex_cons_le_cons (by rfl)
          (Kraken.lex_cons_le_of_lt (by rfl) (by decide)))))

/-! ## Level 2 of the walk: the next window (`0x809`) -/

theorem buf_ix {x : PArgs} {X : BitVec 32} (hp : x.p8.toNat / 8 + 4 ≤ x.L)
    (h : Ix x (BitVec.setWidth 64 X)) : (BitVec.setWidth 64 (X >>> 3)).toNat + 4 ≤ x.L := by
  obtain ⟨-, h2⟩ := h
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at h2 ⊢
  omega

set_option maxRecDepth 20000 in
theorem blk_809 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.L809" := by
  cfg_block
  simp only [tab_L809, var_L809, tab_L829, var_L829]
  measure_hb "L809"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, e, b, j, i, ⟨⟨hLB, hIS, h9, he, hbx, h14⟩, h11, hnr, h10, hb, hTb, hj, hW⟩, hWk⟩, hn⟩ := hs₀
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
    vcgen [ps_bswap32_havoc, ps_shl_cl32_havoc]
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
      refine ⟨⟨c, f, e, b, j, i, ⟨⟨LB_mv hLB (by rs) (by rs) (by rs; exact hLB.2.1)
          ?ix hm, hIS, by rs; exact h9, he, by rs; exact hbx, by rs; exact h14⟩,
          by rs; exact h11, hnr, by rs; exact h10, hb, by rs; exact hTb, hj, hW⟩, ?wk⟩, ?lex⟩
      case wk =>
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]
        exact hWk
      case ix =>
        rs
        exact (hcw _ _).1
      case lex =>
        simp only [slot64, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]
        exact Kraken.lex_cons_le_cons (by rfl) (Kraken.lex_cons_le_cons (by rfl)
          (Kraken.lex_cons_le_cons (by rfl) (Kraken.lex_cons_le_cons (by rfl)
            (Kraken.lex_cons_le_of_lt (by rfl) (by decide)))))

/-! ## Level 2 of the walk: the subtable entry (`0x829`) -/

theorem vwalk_lt {es : List UInt8} {d i : Nat} (h : VWalk es (d + 1) i) : i < es.length / 4 := by
  simp only [VWalk] at h; exact h.1

theorem vwalk_next {es : List UInt8} {d i : Nat} (h : VWalk es (d + 1) i) (hm : (vlen es i).msb = true)
    (W : BitVec 32) (hW : W.toNat < 2 ^ (32 - (vlen es i).toNat % 32)) :
    VWalk es d (W + (vsym es i).signExtend 32).toNat := by
  simp only [VWalk] at h
  rcases h.2 with h' | h'
  · rw [hm] at h'; exact absurd h' (by decide)
  · have := h' W.toNat hW
    simp only [vnext, BitVec.ofNat_toNat, BitVec.setWidth_eq] at this
    exact this

theorem shr_lt (X : BitVec 32) (m : Nat) (hm : m < 32) : (X.ushiftRight m).toNat < 2 ^ (32 - m) := by
  rw [BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have h1 := X.isLt
  have h2 : 2 ^ 32 = 2 ^ (32 - m) * 2 ^ m := by rw [← Nat.pow_add]; congr 1; omega
  exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm, ← h2]; exact h1)

theorem cnt_sx {r : BitVec 64} {l : BitVec 16} (h : r.setWidth 32 = l.signExtend 32) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 r)).toNat % 256 % 32 = l.toNat % 32 := by
  rw [h, BitVec.toNat_setWidth, BitVec.toNat_signExtend]
  have := l.isLt
  split <;> simp only [BitVec.toNat_setWidth] <;> omega

theorem sw_shr_ite (X : BitVec 64) (n : Nat) :
    BitVec.setWidth 32 (if n = 0 then X else BitVec.setWidth 64 ((BitVec.setWidth 32 X).ushiftRight n))
      = (BitVec.setWidth 32 X).ushiftRight n := by
  split
  · rename_i h; subst h; simp
  · exact BitVec.setWidth_32_64_32 _
theorem tab_addrI0 (p : BitVec 64) (I : BitVec 32) (h : I.toNat < 2 ^ 30) :
    p + BitVec.setWidth 64 I * 4#64 = p + BitVec.ofNat 64 (4 * I.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

theorem tab_addrI2 (p : BitVec 64) (I : BitVec 32) (h : I.toNat < 2 ^ 30) :
    p + BitVec.setWidth 64 I * 4#64 + 2#64 = p + BitVec.ofNat 64 (4 * I.toNat + 2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

theorem s_sx16 (w : BitVec 16) (fl : StatusFlags.from_result.Remaining) :
    CondCode.s.interp (StatusFlags.from_result
      (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.signExtend 32 w)) &&&
        BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.signExtend 32 w))) fl) = w.msb := by
  rw [CondCode.interp_s, StatusFlags.sf_from_result, BitVec.and_self, BitVec.setWidth_32_64_32]
  simp [BitVec.msb_signExtend]

theorem s_sx16' (w : BitVec 16) (fl : StatusFlags.from_result.Remaining) :
    CondCode.s.interp (StatusFlags.from_result
      (BitVec.signExtend 32 w &&& BitVec.signExtend 32 w) fl) = w.msb := by
  rw [CondCode.interp_s, StatusFlags.sf_from_result, BitVec.and_self]
  simp [BitVec.msb_signExtend]

/-- `rs` through the `if` a `shr %cl` leaves on the registers. -/
macro "rsw" : tactic => `(tactic| (simp only [Kraken.Examples.Sbr.Ps.Rdr, Kraken.Examples.Sbr.Ps.Ix,
  get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, ite_self]))

set_option maxRecDepth 20000 in
theorem blk_829 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.L829" := by
  cfg_block
  simp only [tab_L829, var_L829, tab_L842, var_L842]
  measure_hb "L829"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, e, b, j, i, ⟨⟨hLB, hIS, h9, he, hbx, h14⟩, h11, hnr, h10, hb, hTb, hj, hW⟩,
      hV, hmsb, hrl, hrs⟩, hn⟩ := hs₀
    subst hn
    have hm := hLB.1.2.2
    have hC := hLB.1.1
    obtain ⟨h4, hN, -⟩ := hC.2.1 j (by omega)
    simp only [VlcTab.N] at hN
    have hm32 : (vlen (x.v j).es i).toNat % 32 < 32 := Nat.mod_lt _ (by decide)
    have hI := vwalk_next hV hmsb ((BitVec.setWidth 32 (s₀.regs.get64 .rdx)).ushiftRight
      ((vlen (x.v j).es i).toNat % 32)) (shr_lt _ _ hm32)
    rw [BitVec.add_comm] at hI
    have hIN := vwalk_lt hI
    have h30 : ((vsym (x.v j).es i).signExtend 32 + (BitVec.setWidth 32 (s₀.regs.get64 .rdx)).ushiftRight
      ((vlen (x.v j).es i).toNat % 32)).toNat < 2 ^ 30 := by omega
    have l0 := Fr_vtab_load hm j (by omega) (by omega) (4 * ((vsym (x.v j).es i).signExtend 32 + (BitVec.setWidth 32 (s₀.regs.get64 .rdx)).ushiftRight
      ((vlen (x.v j).es i).toNat % 32)).toNat) 2 (by omega)
    have l2 := Fr_vtab_load hm j (by omega) (by omega) (4 * ((vsym (x.v j).es i).signExtend 32 + (BitVec.setWidth 32 (s₀.regs.get64 .rdx)).ushiftRight
      ((vlen (x.v j).es i).toNat % 32)).toNat + 2) 2 (by omega)
    have i2 : Int64.toBitVec 2 = 2#64 := rfl
    vcgen
    all_goals subst_vars
    all_goals try dsimp only at *
    case vc1 =>
      simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
        ite_self, sw_shr_ite, cnt_sx hrl, hrs, offs4', add_i64z, hTb, BitVec.setWidth_32_64_32]
      rw [tab_addrI0 _ _ h30, l0]; rfl
    case vc2 =>
      simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
        ite_self, sw_shr_ite, cnt_sx hrl, hrs, offs4', i2, hTb, BitVec.setWidth_32_64_32]
      rw [tab_addrI2 _ _ h30, l2]; rfl
    case vc3 =>
      rename_i v0 hv0 v1 hv1 _ hc
      simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
        ite_self, sw_shr_ite, cnt_sx hrl, hrs, offs4', add_i64z, i2, hTb, BitVec.setWidth_32_64_32] at hv0 hv1 hc
      rw [tab_addrI0 _ _ h30, l0, Option.some.injEq] at hv0
      rw [tab_addrI2 _ _ h30, l2, Option.some.injEq] at hv1
      subst hv0 hv1
      rw [s_sx16'] at hc
      simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ite_self]
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.L842") ⟨rfl, ?_, Or.inl ?_⟩
      · refine (tab_L842 _ _ _ _ _ _).mpr ?_
        refine ⟨c, f, e, b, j, _, ⟨⟨LB_mv hLB (by rsw) (by rsw) (by rsw; exact hLB.2.1)
          (by rsw; exact hLB.2.2.1) hm, hIS, by rsw; exact h9, he, by rsw; exact hbx, by rsw; exact h14⟩,
          by rsw; exact h11, hnr, by rsw; exact h10, hb, by rsw; exact hTb, hj, hW⟩,
          ⟨hI, hc, ?_, ?_⟩, ⟨_, hmsb, ?_⟩⟩
        all_goals (try rsw) <;> (try simp only [BitVec.setWidth_32_64_32]) <;> (try exact hrl)
      · rw [var_L842]
        simp only [slot64, get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, ite_self]
        exact Kraken.lex_cons_lt_cons (by rfl) (Kraken.lex_cons_lt_cons (by rfl)
          (Kraken.lex_cons_lt_cons (by rfl) (Kraken.lex_cons_lt_cons (by rfl)
            (Kraken.lex_cons_lt_of_lt (by rfl) (by decide)))))
    case vc4 =>
      rename_i v0 hv0 v1 hv1 _ hc
      simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
        ite_self, sw_shr_ite, cnt_sx hrl, hrs, offs4', add_i64z, i2, hTb, BitVec.setWidth_32_64_32] at hv0 hv1 hc
      rw [tab_addrI0 _ _ h30, l0, Option.some.injEq] at hv0
      rw [tab_addrI2 _ _ h30, l2, Option.some.injEq] at hv1
      subst hv0 hv1
      rw [s_sx16'] at hc
      simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ite_self]
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.L880") ⟨rfl, ?_, Or.inl ?_⟩
      · refine (tab_L880 _ _ _ _ _ _).mpr ?_
        refine ⟨c, f, e, b, j, ⟨⟨LB_mv hLB (by rsw) (by rsw) (by rsw; exact hLB.2.1)
          (by rsw; exact hLB.2.2.1) hm, hIS, by rsw; exact h9, he, by rsw; exact hbx, by rsw; exact h14⟩,
          by rsw; exact h11, hnr, by rsw; exact h10, hb, by rsw; exact hTb, hj, hW⟩, ⟨_, hc, ?_⟩⟩
        all_goals (try rsw) <;> (try simp only [BitVec.setWidth_32_64_32]) <;> (try exact hrl)
      · rw [var_L880]
        simp only [slot64, get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, ite_self]
        exact Kraken.lex_cons_lt_cons (by rfl) (Kraken.lex_cons_lt_cons (by rfl)
          (Kraken.lex_cons_lt_cons (by rfl) (Kraken.lex_cons_lt_cons (by rfl)
            (Kraken.lex_cons_lt_of_lt (by rfl) (by decide)))))

/-! ## Level 3 of the walk: the next window (`0x842`) -/

theorem lenN_ge (v : BitVec 64) (h : LenN v) : 2 ^ 32 - 2 ^ 15 ≤ (v.setWidth 32).toNat := by
  obtain ⟨l, hl, he⟩ := h
  rw [he, BitVec.toNat_signExtend]
  have := (BitVec.msb_eq_true_iff_two_mul_ge).mp hl
  have := l.isLt
  simp only [hl, ↓reduceIte, BitVec.toNat_setWidth]
  omega

theorem lix_clampN (x : PArgs) (r d : BitVec 64) (hd : 2 ^ 32 - 2 ^ 15 ≤ (BitVec.setWidth 32 d).toNat)
    (hr : Ix x r) (hp : x.p8.toNat < 2 ^ 31) (hi : x.idx.toNat ≤ x.p8.toNat) (af of : Bool) :
    Ix x (BitVec.setWidth 64 (if CondCode.c.interp (StatusFlags.from_result
        (x.p8 - (BitVec.setWidth 32 r - BitVec.setWidth 32 d))
        { cf := (x.p8 - (BitVec.setWidth 32 r - BitVec.setWidth 32 d)).unsigned !=
            x.p8.unsigned - (BitVec.setWidth 32 r - BitVec.setWidth 32 d).unsigned,
          af := af, of := of }) = true
      then x.p8 else BitVec.setWidth 32 r - BitVec.setWidth 32 d)) := by
  obtain ⟨h1, h2⟩ := hr
  have e : (BitVec.setWidth 32 r - BitVec.setWidth 32 d).toNat
      = r.toNat + (2 ^ 32 - (BitVec.setWidth 32 d).toNat) := by
    have : (BitVec.setWidth 32 r).toNat = r.toNat % 2 ^ 32 := by simp [BitVec.toNat_setWidth]
    have := (BitVec.setWidth 32 d).isLt
    have := x.p8.isLt
    rw [BitVec.toNat_sub]; omega
  have h64 : ∀ y : BitVec 32, (BitVec.setWidth 64 y).toNat = y.toNat := fun y => by
    rw [BitVec.toNat_setWidth]; have := y.isLt; omega
  simp only [Ix, h64]
  split
  · have := x.p8.isLt
    refine ⟨?_, ?_⟩ <;> omega
  · rename_i h
    simp only [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, bne_iff_ne, ne_eq,
      Decidable.not_not] at h
    rw [BitVec.toNat_sub] at h
    rw [e] at h ⊢
    have := x.p8.isLt
    have := (BitVec.setWidth 32 d).isLt
    refine ⟨?_, ?_⟩ <;> omega

set_option maxRecDepth 20000 in
theorem blk_842 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.L842" := by
  cfg_block
  simp only [tab_L842, var_L842, tab_L861, var_L861]
  measure_hb "L842"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, e, b, j, i, ⟨⟨hLB, hIS, h9, he, hbx, h14⟩, h11, hnr, h10, hb, hTb, hj, hW⟩, hWk, hLN⟩, hn⟩ := hs₀
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
      refine ⟨⟨c, f, e, b, j, i, ⟨⟨LB_mv hLB (by rs) (by rs) (by rs; exact hLB.2.1)
          ?ix hm, hIS, by rs; exact h9, he, by rs; exact hbx, by rs; exact h14⟩,
          by rs; exact h11, hnr, by rs; exact h10, hb, by rs; exact hTb, hj, hW⟩, ?wk⟩, ?lex⟩
      case wk =>
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]
        exact hWk
      case ix =>
        rs
        exact hcw _ _
      case lex =>
        simp only [slot64, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]
        exact Kraken.lex_cons_le_cons (by rfl) (Kraken.lex_cons_le_cons (by rfl)
          (Kraken.lex_cons_le_cons (by rfl) (Kraken.lex_cons_le_cons (by rfl)
            (Kraken.lex_cons_le_of_lt (by rfl) (by decide)))))

/-! ## Level 3 of the walk: the last entry (`0x861`) -/

theorem vwalk1_msb {es : List UInt8} {i : Nat} (h : VWalk es 1 i) : (vlen es i).msb = false := by
  simp only [VWalk] at h
  rcases h.2 with h' | h'
  · exact h'
  · exact absurd (h' 0 (Nat.two_pow_pos _)) id

set_option maxRecDepth 20000 in
theorem blk_861 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.L861" := by
  cfg_block
  simp only [tab_L861, var_L861, tab_L880, var_L880]
  measure_hb "L861"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, e, b, j, i, ⟨⟨hLB, hIS, h9, he, hbx, h14⟩, h11, hnr, h10, hb, hTb, hj, hW⟩,
      hV, hmsb, hrl, hrs⟩, hn⟩ := hs₀
    subst hn
    have hm := hLB.1.2.2
    have hC := hLB.1.1
    obtain ⟨h4, hN, -⟩ := hC.2.1 j (by omega)
    simp only [VlcTab.N] at hN
    have hm32 : (vlen (x.v j).es i).toNat % 32 < 32 := Nat.mod_lt _ (by decide)
    have hI := vwalk_next hV hmsb ((BitVec.setWidth 32 (s₀.regs.get64 .rax)).ushiftRight
      ((vlen (x.v j).es i).toNat % 32)) (shr_lt _ _ hm32)
    rw [BitVec.add_comm] at hI
    have hIN := vwalk_lt hI
    have h30 : ((vsym (x.v j).es i).signExtend 32 + (BitVec.setWidth 32 (s₀.regs.get64 .rax)).ushiftRight
      ((vlen (x.v j).es i).toNat % 32)).toNat < 2 ^ 30 := by omega
    have l0 := Fr_vtab_load hm j (by omega) (by omega) (4 * ((vsym (x.v j).es i).signExtend 32 + (BitVec.setWidth 32 (s₀.regs.get64 .rax)).ushiftRight
      ((vlen (x.v j).es i).toNat % 32)).toNat) 2 (by omega)
    have l2 := Fr_vtab_load hm j (by omega) (by omega) (4 * ((vsym (x.v j).es i).signExtend 32 + (BitVec.setWidth 32 (s₀.regs.get64 .rax)).ushiftRight
      ((vlen (x.v j).es i).toNat % 32)).toNat + 2) 2 (by omega)
    have i2 : Int64.toBitVec 2 = 2#64 := rfl
    vcgen
    all_goals subst_vars
    all_goals try dsimp only at *
    case vc1 =>
      simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
        ite_self, sw_shr_ite, cnt_sx hrl, hrs, offs4', add_i64z, hTb, BitVec.setWidth_32_64_32]
      rw [tab_addrI0 _ _ h30, l0]; rfl
    case vc2 =>
      simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
        ite_self, sw_shr_ite, cnt_sx hrl, hrs, offs4', i2, hTb, BitVec.setWidth_32_64_32]
      rw [tab_addrI2 _ _ h30, l2]; rfl
    case vc3 =>
      rename_i v0 hv0 v1 hv1
      simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
        ite_self, sw_shr_ite, cnt_sx hrl, hrs, offs4', add_i64z, i2, hTb, BitVec.setWidth_32_64_32] at hv0 hv1
      rw [tab_addrI0 _ _ h30, l0, Option.some.injEq] at hv0
      rw [tab_addrI2 _ _ h30, l2, Option.some.injEq] at hv1
      subst hv0 hv1
      simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ite_self]
      refine ⟨⟨c, f, e, b, j, ⟨⟨LB_mv hLB (by rsw) (by rsw) (by rsw; exact hLB.2.1)
          (by rsw; exact hLB.2.2.1) hm, hIS, by rsw; exact h9, he, by rsw; exact hbx, by rsw; exact h14⟩,
          by rsw; exact h11, hnr, by rsw; exact h10, hb, by rsw; exact hTb, hj, hW⟩,
          ⟨_, vwalk1_msb hI, ?_⟩⟩, ?_⟩
      · (try rsw) <;> (try simp only [BitVec.setWidth_32_64_32])
      · simp only [slot64, get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, ite_self]
        exact Kraken.lex_cons_le_cons (by rfl) (Kraken.lex_cons_le_cons (by rfl)
          (Kraken.lex_cons_le_cons (by rfl) (Kraken.lex_cons_le_cons (by rfl)
            (Kraken.lex_cons_le_of_lt (by rfl) (by decide)))))

end Kraken.Examples.Sbr.Ps
