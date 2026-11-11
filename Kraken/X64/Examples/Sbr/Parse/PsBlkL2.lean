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
theorem blk_760 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.L760" := by
  cfg_block
  simp only [tab_L760, var_L760]
  measure_hb "L760"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, e, ⟨hLB, hIS, h9, he, hbx, h14⟩, hW⟩, hn⟩ := hs₀
    subst hn
    have hcl := LB_cl hLB
    have hfl := LB_fl hLB
    have hm := hLB.1.2.2
    have hbp := hLB.1.2.1.2.1
    have hne4 : ne c ≤ 4 := hLB.2.2.2.1.2.1
    have h40 : rd f 0x40 8 = ne c := hLB.2.2.2.2.2.2
    have h28 : rd f 0x28 8 = ne c := hIS.2.1
    have e1 : s₀.regs.get64 .rbp + 0 + (-120 : Int64).toBitVec
        = rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 0x28 :=
      slot_addr (by rw [hbp]; exact BitVec.add_zero _) 120 0x28 rfl
    have e2 : s₀.regs.get64 .rbp + 0 + (-96 : Int64).toBitVec
        = rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 0x40 :=
      slot_addr (by rw [hbp]; exact BitVec.add_zero _) 96 0x40 rfl
    have e3 : s₀.regs.get64 .rbp - BitVec.ofNat 64 0x78
        = rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 0x28 := slot_addr_sub hbp 0x78 0x28 rfl
    have l1 := Fr_f_load hm hfl 0x28 8 (by omega)
    have l3 := l1
    rw [← e1] at l1
    rw [← e3] at l3
    have l2 := Fr_f_load hm hfl 0x40 8 (by omega)
    rw [← e2] at l2
    vcgen
    all_goals try subst_vars
    all_goals try dsimp only
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]
    case vc1 => simp only [AddrIndex.offset64_none, l1, Option.isSome_some]
    case vc2 =>
      rename_i v1 hv1
      dsimp only at hv1
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, AddrIndex.offset64_none, l1,
        Option.some.injEq] at hv1
      subst hv1
      simp only [AddrIndex.offset64_none, l2, Option.isSome_some]
    all_goals rename_i v1 hv1 v2 hv2 hz
    all_goals dsimp only at hv1 hv2 hz
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, AddrIndex.offset64_none, l1, l2,
        Option.some.injEq] at hv1 hv2
    all_goals subst hv1 hv2
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, CondCode.interp_z,
      StatusFlags.zf_from_result] at hz
    all_goals simp only [hbx, h28] at hz
    all_goals rw [cnt_beq _ _ he hne4] at hz
    all_goals have he' : (e : Int) < ne c := he
    all_goals have h4' : ne c ≤ 4 := hne4
    all_goals have h0 : 0 ≤ ne c := hLB.2.2.2.1.1
    case vc3 =>
      simp only [decide_eq_true_eq] at hz
      have hz' : (e : Int) + 1 = ne c := hz
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.La4c") ⟨rfl, ?_, Or.inl ?_⟩
      · refine (tab_La4c _ _ _ _ _ _).mpr ?_
        obtain ⟨hC, hR, hI, hS⟩ := LB_mv hLB rfl rfl hLB.2.1 hLB.2.2.1 hm
        refine ⟨c, f, hC, hR, hI, hS, ?_, ?_⟩
        · simp only [Reg64s.get64_set64, ite_true, h40]
          exact toNat_ofInt64_small _ h0 (by omega)
        · intro hw
          obtain ⟨hr, hh, hi, hb, -⟩ := hW hw
          refine ⟨hr, hh, hi, by rw [← hz']; exact hb, fun h => absurd h hIS.1⟩
      · rw [var_La4c]
        exact Kraken.lex_cons_lt_of_lt rfl (by decide)
    case vc4 =>
      simp only [decide_eq_false_iff_not] at hz
      have hz' : ¬ (e : Int) + 1 = ne c := hz
      refine ⟨(tab_L775 _ _ _ _ _ _).mpr ⟨c, f, e + 1, ⟨LB_mv hLB rfl rfl hLB.2.1 hLB.2.2.1 hm, hIS, ?_,
        by omega, ?_, ?_⟩, hW⟩, ?_⟩
      · simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact h9
      · simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, hbx]
        exact ofNat64_add e 1
      · simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, h14]
        exact row_step _ 76 e
      · rw [var_L775]
        simp only [slot64, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, l3, Option.getD_some,
          h28, hbx]
        rw [show BitVec.ofNat 64 e + 1 = BitVec.ofNat 64 (e + 1) from ofNat64_add e 1]
        refine Kraken.lex_cons_le_cons (by rfl) (Kraken.lex_cons_le_of_lt (by rfl) ?_)
        rw [meas_sub _ _ (show ((e + 1 : Nat) : Int) ≤ ne c by omega) (show ne c < 2 ^ 63 by omega),
          meas_sub _ _ (show (e : Int) ≤ ne c by omega) (show ne c < 2 ^ 63 by omega)]
        omega

set_option maxRecDepth 20000 in
theorem blk_775 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.L775" := by
  cfg_block
  simp only [tab_L775, var_L775, tab_L798, var_L798]
  measure_hb "L775"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, e, hIE, hW⟩, hn⟩ := hs₀
    subst hn
    have hLB := hIE.1
    have hm := hLB.1.2.2
    have hC := hLB.1.1
    have hR := hLB.2.1
    have hI := hLB.2.2.1
    have hB := Fr_buf_load hm (((s₀.regs.get64 .r8).setWidth 32).ushiftRight 3 |>.setWidth 64) 1
      (lrd_off1 _ x.p8 x.L (by rw [BitVec.toNat_setWidth]; omega) hC.2.2.2.2.1)
    vcgen [shl_cl32_havoc]
    all_goals try subst_vars
    all_goals try dsimp only
    all_goals lsimp
    case vc1 => rw [hR.1]; exact hB
    case vc2 =>
      obtain ⟨_, hIS, h9, he, hbx, h14⟩ := hIE
      refine ⟨⟨c, f, e, ⟨LB_mv hLB rfl rfl ?_ ?_ hm, hIS, ?_, he, ?_, ?_⟩, hW, ?_, ?_, ?_⟩, ?_⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
      all_goals try assumption
      · exact and1_lt _
      · simp only [BitVec.xor_self]; rfl
      · rw [hR.2, BitVec.setWidth_32_64_32]
        exact setl_ix x _ _ hI hC.2.2.2.1 _ _
      · simp only [slot64, Reg64s.get64_set64, reduceCtorEq, ite_false]
        exact Kraken.lex_cons_le_cons (by rfl) (Kraken.lex_cons_le_cons (by rfl)
          (Kraken.lex_cons_le_of_lt (by rfl) (by decide)))

set_option maxRecDepth 20000 in
theorem blk_798 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.L798" := by
  cfg_block
  simp only [tab_L798, var_L798, tab_L7a8, var_L7a8]
  measure_hb "L798"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, e, hIE, hW, hax, hdx, hsi⟩, hn⟩ := hs₀
    subst hn
    have hLB := hIE.1
    have hm := hLB.1.2.2
    have hfl := LB_fl hLB
    have hbp := hLB.1.2.1.2.1
    have h8 : i32 c 8 = 0 ∨ i32 c 8 = 1 := hLB.1.2.1.2.2.2.1.2.2.2.2.2.2
    have h50 : BitVec.ofInt 64 (rd f 0x50 8) = BitVec.ofInt 64 (i32 c 8) := hIE.2.1.2.2.2
    have e1 : s₀.regs.get64 .rbp + 0 + (-80 : Int64).toBitVec
        = rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 0x50 :=
      slot_addr (by rw [hbp]; exact BitVec.add_zero _) 80 0x50 rfl
    have l1 := Fr_f_load hm hfl 0x50 8 (by omega)
    rw [← e1] at l1
    vcgen
    all_goals try subst_vars
    all_goals try dsimp only
    case vc1 => simp only [AddrIndex.offset64_none, l1, Option.isSome_some]
    all_goals rename_i v hv hc
    all_goals simp only [AddrIndex.offset64_none, l1, Option.some.injEq] at hv
    all_goals subst hv
    all_goals dsimp only at hc
    all_goals simp only [h50, reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_scale2,
      Int64.toBitVec_ofNat_norm, BitVec.add_zero, BitVec.setWidth_32_64_32] at hc ⊢
    all_goals have hv := lea_q2 _ _ h8 hax
    case vc2 => exact absurd hc (by rw [Bool.not_eq_true]; exact nc_sub4 _ hv _ _)
    case vc3 =>
      obtain ⟨_, hIS, h9, he, hbx, h14⟩ := hIE
      refine ⟨⟨c, f, e, ⟨LB_mv hLB rfl rfl (by rs; exact hLB.2.1) (by rs; exact hLB.2.2.1) hm, hIS,
        by rs; exact h9, he, by rs; exact hbx, by rs; exact h14⟩, hW, by rs; exact hax,
        by rs; exact hdx, by rs; exact hsi, ?_⟩, ?_⟩
      · rs; rw [BitVec.toNat_setWidth]; omega
      · simp only [slot64, Reg64s.get64_set64, reduceCtorEq, ite_false]
        exact Kraken.lex_cons_le_cons (by rfl) (Kraken.lex_cons_le_cons (by rfl)
          (Kraken.lex_cons_le_of_lt (by rfl) (by decide)))

set_option maxRecDepth 20000 in
theorem blk_7a8 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.L7a8" := by
  cfg_block
  simp only [tab_L7a8, var_L7a8, tab_L7d5, var_L7d5]
  measure_hb "L7a8"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, e, hIE, hW, hax, hdx, hsi, hcx⟩, hn⟩ := hs₀
    subst hn
    have hLB := hIE.1
    have hm := hLB.1.2.2
    have hC := hLB.1.1
    have hfl := LB_fl hLB
    have hcl := LB_cl hLB
    have hbp := hLB.1.2.1.2.1
    have h68 : BitVec.ofInt 64 (rd f 0x68 8) = arg2 t₀ := hLB.2.2.2.2.2.1
    have e1 : s₀.regs.get64 .rbp + 0 + (-56 : Int64).toBitVec
        = rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 0x68 :=
      slot_addr (by rw [hbp]; exact BitVec.add_zero _) 56 0x68 rfl
    have l1 := Fr_f_load hm hfl 0x68 8 (by omega)
    rw [← e1] at l1
    have l2 := Fr_c_load hm hcl 12 4 (by omega)
    have e2 : arg2 t₀ + (12 : Int64).toBitVec = arg2 t₀ + BitVec.ofNat 64 12 := rfl
    rw [← e2] at l2
    have hj := hcx
    have l3 := Fr_huff hm _ hj
    have hh := huff_lt _ hj
    have l4 := Fr_vptr_load hm (rd [2, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0]
      (4 * (s₀.regs.get64 .rcx).toNat) 4).toNat (by omega)
    have hix := ix_addb x _ _ hLB.2.2.1 hsi hC.2.2.2.1
    rw [← hdx] at hix
    obtain ⟨_, hIS, h9, he, hbx, h14⟩ := hIE
    vcgen
    case vc1 =>
      subst_vars; dsimp only; try rs
      simp only [AddrIndex.offset64_none, l1, Option.isSome_some]
    case vc2 =>
      rename_i v1 hv1
      subst_vars; dsimp only at hv1 ⊢; try rs
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, l1,
        Option.some.injEq] at hv1
      subst hv1
      simp only [h68, l2, Option.isSome_some]
    case vc3 =>
      rename_i v1 hv1 v2 hv2
      subst_vars; dsimp only at hv1 hv2 ⊢; try rs
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, l1,
        Option.some.injEq] at hv1
      subst hv1
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, h68, l2, Option.some.injEq] at hv2
      subst hv2
      simp only [AddrIndex.offset64_scale4, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
        idx4_zx _ hj]
      rw [add_i64z, l3]
      rfl
    case vc4 =>
      rename_i v1 hv1 v2 hv2 v3 hv3
      subst_vars; dsimp only at hv1 hv2 hv3 ⊢; try rs
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, l1,
        Option.some.injEq] at hv1
      subst hv1
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, h68, l2, Option.some.injEq] at hv2
      subst hv2
      simp only [AddrIndex.offset64_scale4, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
        idx4_zx _ hj, add_i64z, l3, Option.some.injEq] at hv3
      subst hv3
      simp only [AddrIndex.offset64_scale8, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
        idx8_ofInt _ hh.2 hh.1, add_i64z, l4, Option.isSome_some]
    all_goals rename_i v1 hv1 v2 hv2 v3 hv3 v4 hv4 af hz
    all_goals subst_vars
    all_goals dsimp only at hv1 hv2 hv3 hv4 ⊢
    all_goals try rs
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      l1, Option.some.injEq] at hv1
    all_goals subst hv1
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, h68, l2,
      Option.some.injEq] at hv2
    all_goals subst hv2
    all_goals simp only [AddrIndex.offset64_scale4, Reg64s.get64_set64, reduceCtorEq, ite_true,
      ite_false, idx4_zx _ hj, add_i64z, l3, Option.some.injEq] at hv3
    all_goals subst hv3
    all_goals simp only [AddrIndex.offset64_scale8, Reg64s.get64_set64, reduceCtorEq, ite_true,
      ite_false, idx8_ofInt _ hh.2 hh.1, add_i64z, l4, Option.some.injEq] at hv4
    all_goals subst hv4
    case vc5 =>
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.L8d0") ⟨rfl, ?_, Or.inl ?_⟩
      · refine (tab_L8d0 _ _ _ _ _ _).mpr ?_
        refine ⟨c, f, e, ?j, ⟨LB_mv hLB (by rs) (by rs) (by rs; exact hLB.2.1) (by rs; exact hix) hm, hIS,
          by rs; exact h9, he, by rs; exact hbx, by rs; exact h14⟩, hW, by rs; exact congrArg (BitVec.setWidth 64) (rd_i32 c 12), ?tb, ?lt⟩
        case tb =>
          rs
          rw [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]
        case lt => omega
      · rw [var_L8d0]
        simp only [slot64, Reg64s.get64_set64, reduceCtorEq, ite_false]
        exact Kraken.lex_cons_lt_cons (by rfl) (Kraken.lex_cons_lt_cons (by rfl)
          (Kraken.lex_cons_lt_of_lt (by rfl) (by decide)))
    case vc6 =>
      refine ⟨⟨c, f, e, ?j, ⟨LB_mv hLB (by rs) (by rs) (by rs; exact hLB.2.1) (by rs; exact hix) hm, hIS,
        by rs; exact h9, he, by rs; exact hbx, by rs; exact h14⟩, hW, by rs; exact congrArg (BitVec.setWidth 64) (rd_i32 c 12), ?tb, ?lt⟩, ?lx⟩
      case tb =>
        rs
        rw [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]
      case lt => omega
      case lx =>
        simp only [slot64, Reg64s.get64_set64, reduceCtorEq, ite_false]
        exact Kraken.lex_cons_le_cons (by rfl) (Kraken.lex_cons_le_cons (by rfl)
          (Kraken.lex_cons_le_of_lt (by rfl) (by decide)))

set_option maxRecDepth 20000 in
theorem blk_7d5 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.L7d5" := by
  cfg_block
  simp only [tab_L7d5, var_L7d5, tab_L7e0, var_L7e0]
  measure_hb "L7d5"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, e, j, hIE, hW, h11, hTb, hj⟩, hn⟩ := hs₀
    subst hn
    have hLB := hIE.1
    have hP := hLB.1.2.1.2.2.2.1
    have h4 : i32 c 4 ≠ 0 := hIE.2.1.1
    have hm := hLB.1.2.2
    have h12 : i32 c 12 ≤ 34 := hP.2.1
    have hv : (BitVec.setWidth 32 (s₀.regs.get64 .r11)).toInt = i32 c 12 := by
      rw [h11, BitVec.setWidth_32_64_32, BitVec.ofInt_toInt]
    obtain ⟨-, hIS, h9, he, hbx, h14⟩ := hIE
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
      rename_i af hc _ _
      subst_vars
      dsimp only at hc ⊢
      rw [le_test32, hv, decide_eq_false_iff_not] at hc
      have hpos : 0 < i32 c 12 := Int.not_le.mp hc
      refine ⟨⟨c, f, e, 0, j, ⟨LB_mv hLB (by rs) (by rs) (by rs; exact hLB.2.1) (by rs; exact hLB.2.2.1) hm,
        hIS, by rs; exact h9, he, by rs; exact hbx, by rs; exact h14⟩, ?_, hpos, ?_, by simpa using hpos,
        by rs; exact hTb, hj, hW⟩, ?_⟩
      · rs; rw [h11]; exact sx_pos _ hpos (by omega)
      · rs; simp only [BitVec.xor_self]; rfl
      · simp only [slot64, Reg64s.get64_set64, reduceCtorEq, ite_false]
        exact Kraken.lex_cons_le_cons (by rfl) (Kraken.lex_cons_le_cons (by rfl)
          (Kraken.lex_cons_le_of_lt (by rfl) (by decide)))

end Kraken.Examples.Sbr.Ps
