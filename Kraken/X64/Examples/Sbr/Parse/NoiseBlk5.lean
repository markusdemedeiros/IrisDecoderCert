import Kraken.X64.Examples.Sbr.Parse.NoiseVlc

/-!
# `read_sbr_noise`: elements 1–4 of a `t_huff` row

The same walk as element 0, with the row pointer `rbx` already advanced; the decoded
value is stored at `rbx + 5 + j`.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Vlc
open Kraken.Examples.Sbr.Parse (GbW bswap32_havoc shl_cl32_havoc rd_off gb_clamp gb_clamp64)

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Noise

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

set_option hygiene false in
/-- The closers of the register/variant obligations of a block's exit assertion. -/
macro "ncl" : tactic => `(tactic|
  first
    | exact pR.down
    | exact pLi.down.1
    | exact pLi.down.2.1
    | exact pLi.down.2.2
    | exact pbx.down
    | exact pax.down
    | exact p8.down
    | exact p10.down
    | exact p14.down
    | exact p11.down
    | exact win9 _
    | rfl
    | exact Nat.le.refl
    | (simp only [BitVec.toNat_setWidth]; omega)
    | (simp only [Nat.add_eq, Nat.succ_eq_add_one]; omega))

set_option hygiene false in
/-- Element `j ≥ 1` of a `t_huff` row, head: `n_q > j`, the previous row's value, the window. -/
macro "noise_a1" j:num : tactic => `(tactic| (
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  dsimp only [reduceTable, reduceVar] at hs₀
  obtain ⟨⟨⟨hC, hR, i, hi, hm⟩, c, hLi, hbx⟩, hn⟩ := hs₀
  have hnn : x.nn ≤ 2 := hC.1
  have hc : c < x.nn := hLi.2.1
  have hnq := NqL.of hm hR.2.2.1
  have hG := GbL.of hm hR.2.2.2.1
  have hbs := T_ld_bs hm
  have hoff := rd_off i x.p8 x.L hi hC.2.2.2.2.2.1
  have oq : (arg3 t₀ + 88656#64 + BitVec.ofNat 64 (5 * c) + BitVec.ofNat 64 $j
      - (arg3 t₀ + 0x15a50#64)).toNat = 5 * c + $j := by simp only [arg3]; bv_omega
  have hlq := T_ld_nfq hm (arg3 t₀ + 88656#64 + BitVec.ofNat 64 (5 * c) + BitVec.ofNat 64 $j) 1
    (by rw [oq]; omega)
  have pR : PLift _ := ⟨hR⟩
  have pLi : PLift _ := ⟨hLi⟩
  have pbx : PLift _ := ⟨hbx⟩
  have pm : PLift _ := ⟨hm⟩
  clear hm oq
  vcgen [bswap32_havoc, shl_cl32_havoc]
  all_goals try subst_vars
  all_goals try dsimp only [reduceTable, reduceVar] at *
  all_goals nnorm
  all_goals try (simp only [hnq.ld, hG.ld_i, hG.ld_buf, hG.ld_p8, Option.isSome_some]; done)
  all_goals try simp only [hG.ld_i, hG.ld_buf, hG.ld_p8, Option.some.injEq] at *
  all_goals try subst_vars
  all_goals try simp only [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt64_ofBytes_toBytes8,
    BitVec.ofInt_toInt] at *
  all_goals
    first
      | (rw [pbx.down]; exact hlq)
      | exact hbs _ 4 hoff
      | (left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
         refine ⟨by decide, ⟨⟨hC, ?_, i, hi, pm.down⟩, c, ?_, ?_, ?_⟩, Or.inl ?_⟩ <;>
           (try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) <;> ncl)
      | (refine ⟨⟨⟨⟨hC, ?_, i, hi, pm.down⟩, c, ⟨?_, ?_, ?_⟩, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
           (try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) <;> ncl)
      | fail "noise_a1: unexpected goal"))

theorem blk_L624c (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_noise.L624c" := by
  cfg_block
  measure_hb "L624c"
    noise_a1 1

theorem blk_L627f (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_noise.L627f" := by
  cfg_block
  measure_hb "L627f"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨⟨⟨hC, hR, i, hi, hm⟩, c, hLi, hbx⟩, hax, h8, h10, h9⟩, hn⟩ := hs₀
    have hL := LcL.of hm hR.2.1
    have hw := win_walk hC.2.2.1 (kt x t₀) kt_lt _ h9
    have hld := vlc_at hm hC.2.2.1 (kt x t₀) kt_lt 3 _ hw
    have pR : PLift _ := ⟨hR⟩
    have pLi : PLift _ := ⟨hLi⟩
    have pbx : PLift _ := ⟨hbx⟩
    have pax : PLift _ := ⟨hax⟩
    have p8 : PLift _ := ⟨h8⟩
    have p10 : PLift _ := ⟨h10⟩
    have pm : PLift _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals try subst_vars
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals nnorm
    all_goals try (simp only [hL.th, Option.isSome_some]; done)
    all_goals try simp only [hL.th, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt] at *
    all_goals try (simp only [hld.1, hld.2, Option.isSome_some]; done)
    all_goals try simp only [hld.1, hld.2, Option.some.injEq] at *
    all_goals try subst_vars
    case vc4 =>
      left
      apply Table.ofLabels_at
      dsimp only [reduceTable, reduceVar]
      refine ⟨by decide, ⟨⟨⟨hC, ?_, i, hi, pm.down⟩, c, ⟨?_, pLi.down.2.1, ?_⟩, ?_⟩, ?_⟩, Or.inr ⟨?_, by decide +kernel⟩⟩ <;>
        try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      · exact pR.down
      · exact pLi.down.1
      · exact pLi.down.2.2
      · exact pbx.down
      · exact p8.down
    case vc5 =>
      rename_i hs
      simp only [CondCode.interp_ns, StatusFlags.sf_from_result, BitVec.and_self,
        Bool.not_eq_false', BitVec.msb_signExtend, decide_true,
        Bool.true_and, Nat.reduceLT] at hs
      refine ⟨⟨⟨⟨hC, ?_, i, hi, pm.down⟩, c, ⟨?_, pLi.down.2.1, ?_⟩, ?_⟩, ?_, ?_, ?_, ?_,
        ⟨_, hw, ?_, rfl, rfl⟩⟩, ?_⟩ <;>
        try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      · exact pR.down
      · exact pLi.down.1
      · exact pLi.down.2.2
      · exact pbx.down
      · exact pax.down
      · exact p8.down
      · exact p10.down
      · exact hs
      · simp only [pLi.down.1, Nat.add_eq, Nat.succ_eq_add_one]
        omega

theorem blk_L6296 (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_noise.L6296" := by
  cfg_block
  measure_hb "L6296"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨⟨⟨hC, hR, i, hi, hm⟩, c, hLi, hbx⟩, hax, h8, h10, h14, e, hW, hneg, h9, h11⟩, hn⟩ := hs₀
    have hbs := T_ld_bs hm
    have pR : PLift _ := ⟨hR⟩
    have pLi : PLift _ := ⟨hLi⟩
    have pbx : PLift _ := ⟨hbx⟩
    have p8 : PLift _ := ⟨h8⟩
    have p10 : PLift _ := ⟨h10⟩
    have p14 : PLift _ := ⟨h14⟩
    have p9 : PLift _ := ⟨h9⟩
    have p11 : PLift _ := ⟨h11⟩
    have pm : PLift _ := ⟨hm⟩
    clear hm
    vcgen [bswap32_havoc, shl_cl32_havoc]
    all_goals try subst_vars
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals nnorm
    case vc1 =>
      rw [p10.down, p8.down, BitVec.setWidth_32_64_32]
      exact hbs _ 4 (rd_off _ _ _ (gb_clamp _ _ _ _) hC.2.2.2.2.2.1)
    case vc2 =>
      refine ⟨⟨⟨⟨hC, ?_, i, hi, pm.down⟩, c, ⟨?_, pLi.down.2.1, ?_⟩, ?_⟩, ?_, ?_,
        ⟨e, hW, hneg, ?_, ?_⟩⟩, Nat.le.refl⟩ <;>
        try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      · exact pR.down
      · exact pLi.down.1
      · exact pLi.down.2.2
      · exact pbx.down
      · exact p8.down
      · exact p14.down
      · rw [p9.down, zs16]
      · exact p11.down

theorem blk_L62b8 (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_noise.L62b8" := by
  cfg_block
  measure_hb "L62b8"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨⟨⟨hC, hR, i, hi, hm⟩, c, hLi, hbx⟩, h8, h14, e, hW, hneg, h9, h11⟩, hn⟩ := hs₀
    have hld := fun w => vlc_at hm hC.2.2.1 (kt x t₀) kt_lt 2 _ (vlc_walk_next hW hneg w)
    have pR : PLift _ := ⟨hR⟩
    have pLi : PLift _ := ⟨hLi⟩
    have pbx : PLift _ := ⟨hbx⟩
    have p8 : PLift _ := ⟨h8⟩
    have p14 : PLift _ := ⟨h14⟩
    have p9 : PLift _ := ⟨h9⟩
    have p11 : PLift _ := ⟨h11⟩
    have pm : PLift _ := ⟨hm⟩
    have key : ∀ v : BitVec 64, v.setWidth 32 = ((s₀.regs.get64 .r10).setWidth 32).ushiftRight
        ((BitVec.setWidth 64 (BitVec.setWidth 32 (s₀.regs.get64 .r11))).toNat % 256 % 32) →
        BitVec.setWidth 32 (s₀.regs.get64 .r9) + BitVec.setWidth 32 v
          = ((s₀.regs.get64 .r10).setWidth 32).ushiftRight ((vlen (TH x t₀).es e).toNat % 32)
            + (vsym (TH x t₀).es e).signExtend 32 := by
      intro v hv
      rw [hv, h9, h11, BitVec.setWidth_32_64_32, BitVec.setWidth_32_64_32, vlc_sh, BitVec.add_comm]
    clear hm
    vcgen [shr_cl32_lo]
    all_goals try subst_vars
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals nnorm
    case vc1 =>
      rw [h14, key _ ‹_›]
      simp only [(hld _).1, Option.isSome_some]
    case vc2 =>
      rw [h14, key _ ‹_›]
      simp only [(hld _).2, Option.isSome_some]
    case vc3 =>
      refine ⟨⟨⟨⟨hC, ?_, i, hi, pm.down⟩, c, ⟨?_, pLi.down.2.1, ?_⟩, ?_⟩, ?_⟩, Nat.le.refl⟩ <;>
        try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      · exact pR.down
      · exact pLi.down.1
      · exact pLi.down.2.2
      · exact pbx.down
      · exact p8.down

theorem blk_L62cc (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_noise.L62cc" := by
  cfg_block
  measure_hb "L62cc"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨⟨⟨hC, hR, i, hi, hm⟩, c, hLi, hbx⟩, h8⟩, hn⟩ := hs₀
    have hnn : x.nn ≤ 2 := hC.1
    have hc : c < x.nn := hLi.2.1
    have hL := LcL.of hm hR.2.1
    have oq : (arg3 t₀ + 88656#64 + BitVec.ofNat 64 (5 * c) + 6#64
        - (arg3 t₀ + 0x15a50#64)).toNat = 5 * c + 6 := by simp only [arg3]; bv_omega
    have hsti := fun j : BitVec 32 => T_st_i hm j
    have hstq := fun (j : BitVec 32) (v : Int) => T_st_nfq (hsti j)
      (arg3 t₀ + 88656#64 + BitVec.ofNat 64 (5 * c) + 6#64) 1 (by rw [oq]; omega) v
    have hlq := fun j : BitVec 32 => T_ld_nfq (hsti j)
      (arg3 t₀ + 88656#64 + BitVec.ofNat 64 (5 * c) + 6#64) 1 (by rw [oq]; omega)
    have hldi := T_ld_i hm
    have pR : PLift _ := ⟨hR⟩
    have pLi : PLift _ := ⟨hLi⟩
    have pbx : PLift _ := ⟨hbx⟩
    have p8 : PLift _ := ⟨h8⟩
    have P1 : PLift _ := ⟨hstq⟩
    have P2 : PLift _ := ⟨hlq⟩
    clear hm hstq hsti hlq oq
    vcgen [shl_cl32_havoc]
    all_goals try subst_vars
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals nnorm
    all_goals try (simp only [hL.d15, hL.w, Option.isSome_some]; done)
    all_goals try simp only [hL.d15, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt] at *
    all_goals try simp only [p8.down, pR.down.2.2.2.1, pbx.down, BitVec.setWidth_32_64_32]
    all_goals
      first
        | (simp only [hldi, Option.isSome_some]; done)
        | exact P2.down _
        | (left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
           refine ⟨by decide, ⟨hC, ?_, _, gb_clamp _ _ _ _, P1.down _ _⟩, Or.inl ?_⟩
           · (try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]); exact pR.down
           · simp only [Nat.add_eq, Nat.succ_eq_add_one]; omega)
        | (refine ⟨⟨⟨hC, ?_, _, gb_clamp _ _ _ _, P1.down _ _⟩, c, ⟨?_, pLi.down.2.1, ?_⟩, ?_⟩, ?_⟩ <;>
             try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
           all_goals first | exact pR.down | exact pLi.down.1 | exact pLi.down.2.2 | exact pbx.down | exact Nat.le.refl | (simp only [Nat.add_eq, Nat.succ_eq_add_one]; omega))

theorem blk_L62f0 (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_noise.L62f0" := by
  cfg_block
  measure_hb "L62f0"
    noise_a1 2

theorem blk_L6323 (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_noise.L6323" := by
  cfg_block
  measure_hb "L6323"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨⟨⟨hC, hR, i, hi, hm⟩, c, hLi, hbx⟩, hax, h8, h10, h9⟩, hn⟩ := hs₀
    have hL := LcL.of hm hR.2.1
    have hw := win_walk hC.2.2.1 (kt x t₀) kt_lt _ h9
    have hld := vlc_at hm hC.2.2.1 (kt x t₀) kt_lt 3 _ hw
    have pR : PLift _ := ⟨hR⟩
    have pLi : PLift _ := ⟨hLi⟩
    have pbx : PLift _ := ⟨hbx⟩
    have pax : PLift _ := ⟨hax⟩
    have p8 : PLift _ := ⟨h8⟩
    have p10 : PLift _ := ⟨h10⟩
    have pm : PLift _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals try subst_vars
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals nnorm
    all_goals try (simp only [hL.th, Option.isSome_some]; done)
    all_goals try simp only [hL.th, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt] at *
    all_goals try (simp only [hld.1, hld.2, Option.isSome_some]; done)
    all_goals try simp only [hld.1, hld.2, Option.some.injEq] at *
    all_goals try subst_vars
    case vc4 =>
      left
      apply Table.ofLabels_at
      dsimp only [reduceTable, reduceVar]
      refine ⟨by decide, ⟨⟨⟨hC, ?_, i, hi, pm.down⟩, c, ⟨?_, pLi.down.2.1, ?_⟩, ?_⟩, ?_⟩, Or.inr ⟨?_, by decide +kernel⟩⟩ <;>
        try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      · exact pR.down
      · exact pLi.down.1
      · exact pLi.down.2.2
      · exact pbx.down
      · exact p8.down
    case vc5 =>
      rename_i hs
      simp only [CondCode.interp_ns, StatusFlags.sf_from_result, BitVec.and_self,
        Bool.not_eq_false', BitVec.msb_signExtend, decide_true,
        Bool.true_and, Nat.reduceLT] at hs
      refine ⟨⟨⟨⟨hC, ?_, i, hi, pm.down⟩, c, ⟨?_, pLi.down.2.1, ?_⟩, ?_⟩, ?_, ?_, ?_, ?_,
        ⟨_, hw, ?_, rfl, rfl⟩⟩, ?_⟩ <;>
        try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      · exact pR.down
      · exact pLi.down.1
      · exact pLi.down.2.2
      · exact pbx.down
      · exact pax.down
      · exact p8.down
      · exact p10.down
      · exact hs
      · simp only [pLi.down.1, Nat.add_eq, Nat.succ_eq_add_one]
        omega

theorem blk_L633a (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_noise.L633a" := by
  cfg_block
  measure_hb "L633a"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨⟨⟨hC, hR, i, hi, hm⟩, c, hLi, hbx⟩, hax, h8, h10, h14, e, hW, hneg, h9, h11⟩, hn⟩ := hs₀
    have hbs := T_ld_bs hm
    have pR : PLift _ := ⟨hR⟩
    have pLi : PLift _ := ⟨hLi⟩
    have pbx : PLift _ := ⟨hbx⟩
    have p8 : PLift _ := ⟨h8⟩
    have p10 : PLift _ := ⟨h10⟩
    have p14 : PLift _ := ⟨h14⟩
    have p9 : PLift _ := ⟨h9⟩
    have p11 : PLift _ := ⟨h11⟩
    have pm : PLift _ := ⟨hm⟩
    clear hm
    vcgen [bswap32_havoc, shl_cl32_havoc]
    all_goals try subst_vars
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals nnorm
    case vc1 =>
      rw [p10.down, p8.down, BitVec.setWidth_32_64_32]
      exact hbs _ 4 (rd_off _ _ _ (gb_clamp _ _ _ _) hC.2.2.2.2.2.1)
    case vc2 =>
      refine ⟨⟨⟨⟨hC, ?_, i, hi, pm.down⟩, c, ⟨?_, pLi.down.2.1, ?_⟩, ?_⟩, ?_, ?_,
        ⟨e, hW, hneg, ?_, ?_⟩⟩, Nat.le.refl⟩ <;>
        try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      · exact pR.down
      · exact pLi.down.1
      · exact pLi.down.2.2
      · exact pbx.down
      · exact p8.down
      · exact p14.down
      · rw [p9.down, zs16]
      · exact p11.down

theorem blk_L635c (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_noise.L635c" := by
  cfg_block
  measure_hb "L635c"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨⟨⟨hC, hR, i, hi, hm⟩, c, hLi, hbx⟩, h8, h14, e, hW, hneg, h9, h11⟩, hn⟩ := hs₀
    have hld := fun w => vlc_at hm hC.2.2.1 (kt x t₀) kt_lt 2 _ (vlc_walk_next hW hneg w)
    have pR : PLift _ := ⟨hR⟩
    have pLi : PLift _ := ⟨hLi⟩
    have pbx : PLift _ := ⟨hbx⟩
    have p8 : PLift _ := ⟨h8⟩
    have p14 : PLift _ := ⟨h14⟩
    have p9 : PLift _ := ⟨h9⟩
    have p11 : PLift _ := ⟨h11⟩
    have pm : PLift _ := ⟨hm⟩
    have key : ∀ v : BitVec 64, v.setWidth 32 = ((s₀.regs.get64 .r10).setWidth 32).ushiftRight
        ((BitVec.setWidth 64 (BitVec.setWidth 32 (s₀.regs.get64 .r11))).toNat % 256 % 32) →
        BitVec.setWidth 32 (s₀.regs.get64 .r9) + BitVec.setWidth 32 v
          = ((s₀.regs.get64 .r10).setWidth 32).ushiftRight ((vlen (TH x t₀).es e).toNat % 32)
            + (vsym (TH x t₀).es e).signExtend 32 := by
      intro v hv
      rw [hv, h9, h11, BitVec.setWidth_32_64_32, BitVec.setWidth_32_64_32, vlc_sh, BitVec.add_comm]
    clear hm
    vcgen [shr_cl32_lo]
    all_goals try subst_vars
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals nnorm
    case vc1 =>
      rw [h14, key _ ‹_›]
      simp only [(hld _).1, Option.isSome_some]
    case vc2 =>
      rw [h14, key _ ‹_›]
      simp only [(hld _).2, Option.isSome_some]
    case vc3 =>
      refine ⟨⟨⟨⟨hC, ?_, i, hi, pm.down⟩, c, ⟨?_, pLi.down.2.1, ?_⟩, ?_⟩, ?_⟩, Nat.le.refl⟩ <;>
        try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      · exact pR.down
      · exact pLi.down.1
      · exact pLi.down.2.2
      · exact pbx.down
      · exact p8.down

theorem blk_L6370 (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_noise.L6370" := by
  cfg_block
  measure_hb "L6370"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨⟨⟨hC, hR, i, hi, hm⟩, c, hLi, hbx⟩, h8⟩, hn⟩ := hs₀
    have hnn : x.nn ≤ 2 := hC.1
    have hc : c < x.nn := hLi.2.1
    have hL := LcL.of hm hR.2.1
    have oq : (arg3 t₀ + 88656#64 + BitVec.ofNat 64 (5 * c) + 7#64
        - (arg3 t₀ + 0x15a50#64)).toNat = 5 * c + 7 := by simp only [arg3]; bv_omega
    have hsti := fun j : BitVec 32 => T_st_i hm j
    have hstq := fun (j : BitVec 32) (v : Int) => T_st_nfq (hsti j)
      (arg3 t₀ + 88656#64 + BitVec.ofNat 64 (5 * c) + 7#64) 1 (by rw [oq]; omega) v
    have hlq := fun j : BitVec 32 => T_ld_nfq (hsti j)
      (arg3 t₀ + 88656#64 + BitVec.ofNat 64 (5 * c) + 7#64) 1 (by rw [oq]; omega)
    have hldi := T_ld_i hm
    have pR : PLift _ := ⟨hR⟩
    have pLi : PLift _ := ⟨hLi⟩
    have pbx : PLift _ := ⟨hbx⟩
    have p8 : PLift _ := ⟨h8⟩
    have P1 : PLift _ := ⟨hstq⟩
    have P2 : PLift _ := ⟨hlq⟩
    clear hm hstq hsti hlq oq
    vcgen [shl_cl32_havoc]
    all_goals try subst_vars
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals nnorm
    all_goals try (simp only [hL.d15, hL.w, Option.isSome_some]; done)
    all_goals try simp only [hL.d15, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt] at *
    all_goals try simp only [p8.down, pR.down.2.2.2.1, pbx.down, BitVec.setWidth_32_64_32]
    all_goals
      first
        | (simp only [hldi, Option.isSome_some]; done)
        | exact P2.down _
        | (left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
           refine ⟨by decide, ⟨hC, ?_, _, gb_clamp _ _ _ _, P1.down _ _⟩, Or.inl ?_⟩
           · (try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]); exact pR.down
           · simp only [Nat.add_eq, Nat.succ_eq_add_one]; omega)
        | (refine ⟨⟨⟨hC, ?_, _, gb_clamp _ _ _ _, P1.down _ _⟩, c, ⟨?_, pLi.down.2.1, ?_⟩, ?_⟩, ?_⟩ <;>
             try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
           all_goals first | exact pR.down | exact pLi.down.1 | exact pLi.down.2.2 | exact pbx.down | exact Nat.le.refl | (simp only [Nat.add_eq, Nat.succ_eq_add_one]; omega))

theorem blk_L6394 (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_noise.L6394" := by
  cfg_block
  measure_hb "L6394"
    noise_a1 3

theorem blk_L63c7 (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_noise.L63c7" := by
  cfg_block
  measure_hb "L63c7"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨⟨⟨hC, hR, i, hi, hm⟩, c, hLi, hbx⟩, hax, h8, h10, h9⟩, hn⟩ := hs₀
    have hL := LcL.of hm hR.2.1
    have hw := win_walk hC.2.2.1 (kt x t₀) kt_lt _ h9
    have hld := vlc_at hm hC.2.2.1 (kt x t₀) kt_lt 3 _ hw
    have pR : PLift _ := ⟨hR⟩
    have pLi : PLift _ := ⟨hLi⟩
    have pbx : PLift _ := ⟨hbx⟩
    have pax : PLift _ := ⟨hax⟩
    have p8 : PLift _ := ⟨h8⟩
    have p10 : PLift _ := ⟨h10⟩
    have pm : PLift _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals try subst_vars
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals nnorm
    all_goals try (simp only [hL.th, Option.isSome_some]; done)
    all_goals try simp only [hL.th, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt] at *
    all_goals try (simp only [hld.1, hld.2, Option.isSome_some]; done)
    all_goals try simp only [hld.1, hld.2, Option.some.injEq] at *
    all_goals try subst_vars
    case vc4 =>
      left
      apply Table.ofLabels_at
      dsimp only [reduceTable, reduceVar]
      refine ⟨by decide, ⟨⟨⟨hC, ?_, i, hi, pm.down⟩, c, ⟨?_, pLi.down.2.1, ?_⟩, ?_⟩, ?_⟩, Or.inr ⟨?_, by decide +kernel⟩⟩ <;>
        try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      · exact pR.down
      · exact pLi.down.1
      · exact pLi.down.2.2
      · exact pbx.down
      · exact p8.down
    case vc5 =>
      rename_i hs
      simp only [CondCode.interp_ns, StatusFlags.sf_from_result, BitVec.and_self,
        Bool.not_eq_false', BitVec.msb_signExtend, decide_true,
        Bool.true_and, Nat.reduceLT] at hs
      refine ⟨⟨⟨⟨hC, ?_, i, hi, pm.down⟩, c, ⟨?_, pLi.down.2.1, ?_⟩, ?_⟩, ?_, ?_, ?_, ?_,
        ⟨_, hw, ?_, rfl, rfl⟩⟩, ?_⟩ <;>
        try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      · exact pR.down
      · exact pLi.down.1
      · exact pLi.down.2.2
      · exact pbx.down
      · exact pax.down
      · exact p8.down
      · exact p10.down
      · exact hs
      · simp only [pLi.down.1, Nat.add_eq, Nat.succ_eq_add_one]
        omega

theorem blk_L63de (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_noise.L63de" := by
  cfg_block
  measure_hb "L63de"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨⟨⟨hC, hR, i, hi, hm⟩, c, hLi, hbx⟩, hax, h8, h10, h14, e, hW, hneg, h9, h11⟩, hn⟩ := hs₀
    have hbs := T_ld_bs hm
    have pR : PLift _ := ⟨hR⟩
    have pLi : PLift _ := ⟨hLi⟩
    have pbx : PLift _ := ⟨hbx⟩
    have p8 : PLift _ := ⟨h8⟩
    have p10 : PLift _ := ⟨h10⟩
    have p14 : PLift _ := ⟨h14⟩
    have p9 : PLift _ := ⟨h9⟩
    have p11 : PLift _ := ⟨h11⟩
    have pm : PLift _ := ⟨hm⟩
    clear hm
    vcgen [bswap32_havoc, shl_cl32_havoc]
    all_goals try subst_vars
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals nnorm
    case vc1 =>
      rw [p10.down, p8.down, BitVec.setWidth_32_64_32]
      exact hbs _ 4 (rd_off _ _ _ (gb_clamp _ _ _ _) hC.2.2.2.2.2.1)
    case vc2 =>
      refine ⟨⟨⟨⟨hC, ?_, i, hi, pm.down⟩, c, ⟨?_, pLi.down.2.1, ?_⟩, ?_⟩, ?_, ?_,
        ⟨e, hW, hneg, ?_, ?_⟩⟩, Nat.le.refl⟩ <;>
        try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      · exact pR.down
      · exact pLi.down.1
      · exact pLi.down.2.2
      · exact pbx.down
      · exact p8.down
      · exact p14.down
      · rw [p9.down, zs16]
      · exact p11.down

theorem blk_L6400 (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_noise.L6400" := by
  cfg_block
  measure_hb "L6400"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨⟨⟨hC, hR, i, hi, hm⟩, c, hLi, hbx⟩, h8, h14, e, hW, hneg, h9, h11⟩, hn⟩ := hs₀
    have hld := fun w => vlc_at hm hC.2.2.1 (kt x t₀) kt_lt 2 _ (vlc_walk_next hW hneg w)
    have pR : PLift _ := ⟨hR⟩
    have pLi : PLift _ := ⟨hLi⟩
    have pbx : PLift _ := ⟨hbx⟩
    have p8 : PLift _ := ⟨h8⟩
    have p14 : PLift _ := ⟨h14⟩
    have p9 : PLift _ := ⟨h9⟩
    have p11 : PLift _ := ⟨h11⟩
    have pm : PLift _ := ⟨hm⟩
    have key : ∀ v : BitVec 64, v.setWidth 32 = ((s₀.regs.get64 .r10).setWidth 32).ushiftRight
        ((BitVec.setWidth 64 (BitVec.setWidth 32 (s₀.regs.get64 .r11))).toNat % 256 % 32) →
        BitVec.setWidth 32 (s₀.regs.get64 .r9) + BitVec.setWidth 32 v
          = ((s₀.regs.get64 .r10).setWidth 32).ushiftRight ((vlen (TH x t₀).es e).toNat % 32)
            + (vsym (TH x t₀).es e).signExtend 32 := by
      intro v hv
      rw [hv, h9, h11, BitVec.setWidth_32_64_32, BitVec.setWidth_32_64_32, vlc_sh, BitVec.add_comm]
    clear hm
    vcgen [shr_cl32_lo]
    all_goals try subst_vars
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals nnorm
    case vc1 =>
      rw [h14, key _ ‹_›]
      simp only [(hld _).1, Option.isSome_some]
    case vc2 =>
      rw [h14, key _ ‹_›]
      simp only [(hld _).2, Option.isSome_some]
    case vc3 =>
      refine ⟨⟨⟨⟨hC, ?_, i, hi, pm.down⟩, c, ⟨?_, pLi.down.2.1, ?_⟩, ?_⟩, ?_⟩, Nat.le.refl⟩ <;>
        try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      · exact pR.down
      · exact pLi.down.1
      · exact pLi.down.2.2
      · exact pbx.down
      · exact p8.down

theorem blk_L6414 (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_noise.L6414" := by
  cfg_block
  measure_hb "L6414"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨⟨⟨hC, hR, i, hi, hm⟩, c, hLi, hbx⟩, h8⟩, hn⟩ := hs₀
    have hnn : x.nn ≤ 2 := hC.1
    have hc : c < x.nn := hLi.2.1
    have hL := LcL.of hm hR.2.1
    have oq : (arg3 t₀ + 88656#64 + BitVec.ofNat 64 (5 * c) + 8#64
        - (arg3 t₀ + 0x15a50#64)).toNat = 5 * c + 8 := by simp only [arg3]; bv_omega
    have hsti := fun j : BitVec 32 => T_st_i hm j
    have hstq := fun (j : BitVec 32) (v : Int) => T_st_nfq (hsti j)
      (arg3 t₀ + 88656#64 + BitVec.ofNat 64 (5 * c) + 8#64) 1 (by rw [oq]; omega) v
    have hlq := fun j : BitVec 32 => T_ld_nfq (hsti j)
      (arg3 t₀ + 88656#64 + BitVec.ofNat 64 (5 * c) + 8#64) 1 (by rw [oq]; omega)
    have hldi := T_ld_i hm
    have pR : PLift _ := ⟨hR⟩
    have pLi : PLift _ := ⟨hLi⟩
    have pbx : PLift _ := ⟨hbx⟩
    have p8 : PLift _ := ⟨h8⟩
    have P1 : PLift _ := ⟨hstq⟩
    have P2 : PLift _ := ⟨hlq⟩
    clear hm hstq hsti hlq oq
    vcgen [shl_cl32_havoc]
    all_goals try subst_vars
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals nnorm
    all_goals try (simp only [hL.d15, hL.w, Option.isSome_some]; done)
    all_goals try simp only [hL.d15, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt] at *
    all_goals try simp only [p8.down, pR.down.2.2.2.1, pbx.down, BitVec.setWidth_32_64_32]
    all_goals
      first
        | (simp only [hldi, Option.isSome_some]; done)
        | exact P2.down _
        | (left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
           refine ⟨by decide, ⟨hC, ?_, _, gb_clamp _ _ _ _, P1.down _ _⟩, Or.inl ?_⟩
           · (try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]); exact pR.down
           · simp only [Nat.add_eq, Nat.succ_eq_add_one]; omega)
        | (refine ⟨⟨⟨hC, ?_, _, gb_clamp _ _ _ _, P1.down _ _⟩, c, ⟨?_, pLi.down.2.1, ?_⟩, ?_⟩, ?_⟩ <;>
             try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
           all_goals first | exact pR.down | exact pLi.down.1 | exact pLi.down.2.2 | exact pbx.down | exact Nat.le.refl | (simp only [Nat.add_eq, Nat.succ_eq_add_one]; omega))

theorem blk_L6438 (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_noise.L6438" := by
  cfg_block
  measure_hb "L6438"
    noise_a1 4

theorem blk_L646b (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_noise.L646b" := by
  cfg_block
  measure_hb "L646b"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨⟨⟨hC, hR, i, hi, hm⟩, c, hLi, hbx⟩, hax, h8, h10, h9⟩, hn⟩ := hs₀
    have hL := LcL.of hm hR.2.1
    have hw := win_walk hC.2.2.1 (kt x t₀) kt_lt _ h9
    have hld := vlc_at hm hC.2.2.1 (kt x t₀) kt_lt 3 _ hw
    have pR : PLift _ := ⟨hR⟩
    have pLi : PLift _ := ⟨hLi⟩
    have pbx : PLift _ := ⟨hbx⟩
    have pax : PLift _ := ⟨hax⟩
    have p8 : PLift _ := ⟨h8⟩
    have p10 : PLift _ := ⟨h10⟩
    have pm : PLift _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals try subst_vars
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals nnorm
    all_goals try (simp only [hL.th, Option.isSome_some]; done)
    all_goals try simp only [hL.th, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt] at *
    all_goals try (simp only [hld.1, hld.2, Option.isSome_some]; done)
    all_goals try simp only [hld.1, hld.2, Option.some.injEq] at *
    all_goals try subst_vars
    case vc4 =>
      left
      apply Table.ofLabels_at
      dsimp only [reduceTable, reduceVar]
      refine ⟨by decide, ⟨⟨⟨hC, ?_, i, hi, pm.down⟩, c, ⟨?_, pLi.down.2.1, ?_⟩, ?_⟩, ?_⟩, Or.inr ⟨?_, by decide +kernel⟩⟩ <;>
        try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      · exact pR.down
      · exact pLi.down.1
      · exact pLi.down.2.2
      · exact pbx.down
      · exact p8.down
    case vc5 =>
      rename_i hs
      simp only [CondCode.interp_ns, StatusFlags.sf_from_result, BitVec.and_self,
        Bool.not_eq_false', BitVec.msb_signExtend, decide_true,
        Bool.true_and, Nat.reduceLT] at hs
      refine ⟨⟨⟨⟨hC, ?_, i, hi, pm.down⟩, c, ⟨?_, pLi.down.2.1, ?_⟩, ?_⟩, ?_, ?_, ?_, ?_,
        ⟨_, hw, ?_, rfl, rfl⟩⟩, ?_⟩ <;>
        try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      · exact pR.down
      · exact pLi.down.1
      · exact pLi.down.2.2
      · exact pbx.down
      · exact pax.down
      · exact p8.down
      · exact p10.down
      · exact hs
      · simp only [pLi.down.1, Nat.add_eq, Nat.succ_eq_add_one]
        omega

theorem blk_L6482 (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_noise.L6482" := by
  cfg_block
  measure_hb "L6482"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨⟨⟨hC, hR, i, hi, hm⟩, c, hLi, hbx⟩, hax, h8, h10, h14, e, hW, hneg, h9, h11⟩, hn⟩ := hs₀
    have hbs := T_ld_bs hm
    have pR : PLift _ := ⟨hR⟩
    have pLi : PLift _ := ⟨hLi⟩
    have pbx : PLift _ := ⟨hbx⟩
    have p8 : PLift _ := ⟨h8⟩
    have p10 : PLift _ := ⟨h10⟩
    have p14 : PLift _ := ⟨h14⟩
    have p9 : PLift _ := ⟨h9⟩
    have p11 : PLift _ := ⟨h11⟩
    have pm : PLift _ := ⟨hm⟩
    clear hm
    vcgen [bswap32_havoc, shl_cl32_havoc]
    all_goals try subst_vars
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals nnorm
    case vc1 =>
      rw [p10.down, p8.down, BitVec.setWidth_32_64_32]
      exact hbs _ 4 (rd_off _ _ _ (gb_clamp _ _ _ _) hC.2.2.2.2.2.1)
    case vc2 =>
      refine ⟨⟨⟨⟨hC, ?_, i, hi, pm.down⟩, c, ⟨?_, pLi.down.2.1, ?_⟩, ?_⟩, ?_, ?_,
        ⟨e, hW, hneg, ?_, ?_⟩⟩, Nat.le.refl⟩ <;>
        try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      · exact pR.down
      · exact pLi.down.1
      · exact pLi.down.2.2
      · exact pbx.down
      · exact p8.down
      · exact p14.down
      · rw [p9.down, zs16]
      · exact p11.down

theorem blk_L64a4 (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_noise.L64a4" := by
  cfg_block
  measure_hb "L64a4"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨⟨⟨hC, hR, i, hi, hm⟩, c, hLi, hbx⟩, h8, h14, e, hW, hneg, h9, h11⟩, hn⟩ := hs₀
    have hld := fun w => vlc_at hm hC.2.2.1 (kt x t₀) kt_lt 2 _ (vlc_walk_next hW hneg w)
    have pR : PLift _ := ⟨hR⟩
    have pLi : PLift _ := ⟨hLi⟩
    have pbx : PLift _ := ⟨hbx⟩
    have p8 : PLift _ := ⟨h8⟩
    have p14 : PLift _ := ⟨h14⟩
    have p9 : PLift _ := ⟨h9⟩
    have p11 : PLift _ := ⟨h11⟩
    have pm : PLift _ := ⟨hm⟩
    have key : ∀ v : BitVec 64, v.setWidth 32 = ((s₀.regs.get64 .r10).setWidth 32).ushiftRight
        ((BitVec.setWidth 64 (BitVec.setWidth 32 (s₀.regs.get64 .r11))).toNat % 256 % 32) →
        BitVec.setWidth 32 (s₀.regs.get64 .r9) + BitVec.setWidth 32 v
          = ((s₀.regs.get64 .r10).setWidth 32).ushiftRight ((vlen (TH x t₀).es e).toNat % 32)
            + (vsym (TH x t₀).es e).signExtend 32 := by
      intro v hv
      rw [hv, h9, h11, BitVec.setWidth_32_64_32, BitVec.setWidth_32_64_32, vlc_sh, BitVec.add_comm]
    clear hm
    vcgen [shr_cl32_lo]
    all_goals try subst_vars
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals nnorm
    case vc1 =>
      rw [h14, key _ ‹_›]
      simp only [(hld _).1, Option.isSome_some]
    case vc2 =>
      rw [h14, key _ ‹_›]
      simp only [(hld _).2, Option.isSome_some]
    case vc3 =>
      refine ⟨⟨⟨⟨hC, ?_, i, hi, pm.down⟩, c, ⟨?_, pLi.down.2.1, ?_⟩, ?_⟩, ?_⟩, Nat.le.refl⟩ <;>
        try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      · exact pR.down
      · exact pLi.down.1
      · exact pLi.down.2.2
      · exact pbx.down
      · exact p8.down

theorem blk_L64b8 (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_noise.L64b8" := by
  cfg_block
  measure_hb "L64b8"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨⟨⟨hC, hR, i, hi, hm⟩, c, hLi, hbx⟩, h8⟩, hn⟩ := hs₀
    have hnn : x.nn ≤ 2 := hC.1
    have hc : c < x.nn := hLi.2.1
    have hL := LcL.of hm hR.2.1
    have oq : (arg3 t₀ + 88656#64 + BitVec.ofNat 64 (5 * c) + 9#64
        - (arg3 t₀ + 0x15a50#64)).toNat = 5 * c + 9 := by simp only [arg3]; bv_omega
    have hsti := fun j : BitVec 32 => T_st_i hm j
    have hstq := fun (j : BitVec 32) (v : Int) => T_st_nfq (hsti j)
      (arg3 t₀ + 88656#64 + BitVec.ofNat 64 (5 * c) + 9#64) 1 (by rw [oq]; omega) v
    have hlq := fun j : BitVec 32 => T_ld_nfq (hsti j)
      (arg3 t₀ + 88656#64 + BitVec.ofNat 64 (5 * c) + 9#64) 1 (by rw [oq]; omega)
    have hldi := T_ld_i hm
    have pR : PLift _ := ⟨hR⟩
    have pLi : PLift _ := ⟨hLi⟩
    have pbx : PLift _ := ⟨hbx⟩
    have p8 : PLift _ := ⟨h8⟩
    have P1 : PLift _ := ⟨hstq⟩
    have P2 : PLift _ := ⟨hlq⟩
    clear hm hstq hsti hlq oq
    vcgen [shl_cl32_havoc]
    all_goals try subst_vars
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals nnorm
    all_goals try (simp only [hL.d15, hL.w, Option.isSome_some]; done)
    all_goals try simp only [hL.d15, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt] at *
    all_goals try simp only [p8.down, pR.down.2.2.2.1, pbx.down, BitVec.setWidth_32_64_32]
    all_goals
      first
        | (simp only [hldi, Option.isSome_some]; done)
        | exact P2.down _
        | (left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
           refine ⟨by decide, ⟨hC, ?_, _, gb_clamp _ _ _ _, P1.down _ _⟩, Or.inl ?_⟩
           · (try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]); exact pR.down
           · simp only [Nat.add_eq, Nat.succ_eq_add_one]; omega)
        | (refine ⟨⟨⟨hC, ?_, _, gb_clamp _ _ _ _, P1.down _ _⟩, c, ⟨?_, pLi.down.2.1, ?_⟩, ?_⟩, ?_⟩ <;>
             try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
           all_goals first | exact pR.down | exact pLi.down.1 | exact pLi.down.2.2 | exact pbx.down | exact Nat.le.refl | (simp only [Nat.add_eq, Nat.succ_eq_add_one]; omega))

end Kraken.Examples.Sbr.Noise
