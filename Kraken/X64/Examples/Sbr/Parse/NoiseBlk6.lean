import Kraken.X64.Examples.Sbr.Parse.NoiseVlc

/-!
# `read_sbr_noise`: the `f_huff` path (delta coding in frequency)

The first value of a row (5 raw bits), then elements `1 … n_q - 1` by a walk of the frequency
table.
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

theorem blk_L64f0 (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_noise.L64f0" := by
  cfg_block
  measure_hb "L64f0"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨⟨hC, hR, i, hi, hm⟩, ⟨c, hLi⟩, h9⟩, hn⟩ := hs₀
    have hG := GbL.of hm hR.2.2.2.1
    have hbs := T_ld_bs hm
    have hoff := rd_off i x.p8 x.L hi hC.2.2.2.2.2.1
    have pR : PLift _ := ⟨hR⟩
    have pLi : PLift _ := ⟨hLi⟩
    have p9 : PLift _ := ⟨h9⟩
    have pm : PLift _ := ⟨hm⟩
    clear hm
    vcgen [bswap32_havoc, shl_cl32_havoc]
    all_goals try subst_vars
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals nnorm
    all_goals try (simp only [hG.ld_i, hG.ld_buf, hG.ld_p8, Option.isSome_some]; done)
    all_goals try simp only [hG.ld_i, hG.ld_buf, hG.ld_p8, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt64_ofBytes_toBytes8,
      BitVec.ofInt_toInt] at *
    all_goals
      first
        | exact hbs _ 4 hoff
        | (refine ⟨⟨⟨hC, ?_, i, hi, pm.down⟩, ⟨c, ?_, pLi.down.2.1, ?_⟩, ?_, ?_⟩, Nat.le.refl⟩ <;>
             try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
           all_goals first | exact pR.down | exact pLi.down.1 | exact pLi.down.2.2 | exact p9.down | exact gb_clamp64 _ _ _ _)

theorem blk_L651b (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_noise.L651b" := by
  cfg_block
  measure_hb "L651b"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨⟨hC, hR, i, hi, hm⟩, ⟨c, hc12, hcn, hc13⟩, h9, hax⟩, hn⟩ := hs₀
    have hnn : x.nn ≤ 2 := hC.1
    have hnq5 : x.nq ≤ 5 := hC.2.1
    have h5 := lea5 c (by omega)
    have oq : (arg3 t₀ + BitVec.ofNat 64 (5 * c) + 88661#64
        - (arg3 t₀ + 0x15a50#64)).toNat = 5 * c + 5 := by simp only [arg3]; bv_omega
    have hsti := fun j : BitVec 32 => T_st_i hm j
    have hb : ∀ j : BitVec 32, ((storeInt s₀.dmem (arg2 t₀ + 8#64) 4 j.toInt).loadInt
        (t₀.regs.get64 .rsp - 8#64 + 18446744073709551575#64) 1).isSome = true := by
      intro j
      refine L_ld_blk (hsti j) _ 1 ?_
      have : t₀.regs.get64 .rsp - 8#64 + 18446744073709551575#64 - (t₀.regs.get64 .rsp - 0x38#64)
          = 7#64 := by bv_omega
      rw [this]; decide
    have hstq := fun (j : BitVec 32) (v : Int) => T_st_nfq (hsti j)
      (arg3 t₀ + BitVec.ofNat 64 (5 * c) + 88661#64) 1 (by rw [oq]; omega) v
    have hlq := fun j : BitVec 32 => T_ld_nfq (hsti j)
      (arg3 t₀ + BitVec.ofNat 64 (5 * c) + 88661#64) 1 (by rw [oq]; omega)
    have hldi := T_ld_i hm
    have hnq' := fun (j : BitVec 32) (v : Int) => T_ld_nq (hstq j v)
    have pR : PLift _ := ⟨hR⟩
    have pc12 : PLift _ := ⟨hc12⟩
    have pc13 : PLift _ := ⟨hc13⟩
    have p9 : PLift _ := ⟨h9⟩
    have pax : PLift _ := ⟨hax⟩
    have P1 : PLift _ := ⟨hstq⟩
    have P2 : PLift _ := ⟨hb⟩
    have P3 : PLift _ := ⟨hnq'⟩
    have P4 : PLift _ := ⟨hlq⟩
    clear hm hstq hsti oq hb hnq' hlq
    vcgen [shl_cl32_havoc]
    all_goals try subst_vars
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals nnorm
    all_goals try simp only [pR.down.2.1, pR.down.2.2.1, pR.down.2.2.2.1, pc12.down, p9.down, h5] at *
    all_goals try simp only [P3.down, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt32_ofBytes_toBytes4] at *
    case vc1 => simp only [hldi, Option.isSome_some]
    case vc2 => exact P2.down _
    case vc3 => exact P4.down _
    case vc4 => simp only [P3.down, Option.isSome_some]
    case vc5 =>
      left
      apply Table.ofLabels_at
      dsimp only [reduceTable, reduceVar]
      refine ⟨by decide, ⟨⟨hC, ?_, _, ?_, P1.down _ _⟩, c, ?_, hcn, ?_⟩, Or.inl ?_⟩ <;>
        try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      all_goals first | exact pR.down | exact pc12.down | exact pc13.down | (rw [BitVec.toNat_setWidth]; exact Nat.le_trans (Nat.mod_le _ _) pax.down) | (simp only [pc12.down, Nat.add_eq, Nat.succ_eq_add_one]; omega)
    case vc6 =>
      have h := ‹CondCode.c.interp _ = false›
      flg h
      refine ⟨⟨⟨hC, ?_, _, ?_, P1.down _ _⟩, ⟨c, ?_, hcn, ?_⟩, ⟨0, ?_, ?_⟩⟩, ?_⟩ <;>
        try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      all_goals first | exact pR.down | exact pc12.down | exact pc13.down | (rw [BitVec.toNat_setWidth]; exact Nat.le_trans (Nat.mod_le _ _) pax.down) | (simp only [pc12.down, Nat.add_eq, Nat.succ_eq_add_one]; omega) | (simp only [BitVec.xor_self]; rfl) | omega

theorem blk_L6540 (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_noise.L6540" := by
  cfg_block
  measure_hb "L6540"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨⟨hC, hR, i, hi, hm⟩, ⟨c, hc12, hcn, hc13⟩, ⟨j, hdi, hj⟩⟩, hn⟩ := hs₀
    have hnn : x.nn ≤ 2 := hC.1
    have hnq5 : x.nq ≤ 5 := hC.2.1
    have hG := GbL.of hm hR.2.2.2.1
    have hbs := T_ld_bs hm
    have hoff := rd_off i x.p8 x.L hi hC.2.2.2.2.2.1
    have hpv : (s₀.dmem.loadInt (s₀.regs.get64 .r13 + s₀.regs.get64 .rdi + 18446744073709551615#64)
        1).isSome = true := by
      rw [hc13, hdi]
      refine T_ld_nfq hm _ 1 ?_
      rw [show arg3 t₀ + 0x15a56#64 + BitVec.ofNat 64 (5 * c) + BitVec.ofNat 64 j
          + 18446744073709551615#64 - (arg3 t₀ + 0x15a50#64) = BitVec.ofNat 64 (5 * c + 5 + j) by
        simp only [arg3]; bv_omega, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    have Php : PLift _ := ⟨hpv⟩
    have pR : PLift _ := ⟨hR⟩
    have pc12 : PLift _ := ⟨hc12⟩
    have pc13 : PLift _ := ⟨hc13⟩
    have pdi : PLift _ := ⟨hdi⟩
    have pm : PLift _ := ⟨hm⟩
    clear hm hpv
    vcgen [bswap32_havoc, shl_cl32_havoc]
    all_goals try subst_vars
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals nnorm
    all_goals try (simp only [hG.ld_i, hG.ld_buf, hG.ld_p8, Option.isSome_some]; done)
    all_goals try simp only [hG.ld_i, hG.ld_buf, hG.ld_p8, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt64_ofBytes_toBytes8,
      BitVec.ofInt_toInt] at *
    case vc1 => exact Php.down
    all_goals
      first
        | exact hbs _ 4 hoff
        | (refine ⟨⟨⟨⟨hC, ?_, i, hi, pm.down⟩, ⟨c, ?_, hcn, ?_⟩, ⟨j, ?_, hj⟩⟩, ?_, ?_, ?_, ?_⟩, Nat.le.refl⟩ <;>
             try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
           all_goals first | exact pR.down | exact pc12.down | exact pc13.down | exact pdi.down | exact win9 _ | rfl | (simp only [BitVec.toNat_setWidth]; omega))

theorem blk_L6568 (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_noise.L6568" := by
  cfg_block
  measure_hb "L6568"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨⟨⟨hC, hR, i, hi, hm⟩, ⟨c, hLi⟩, ⟨j, hdi, hj⟩⟩, hax, h8, h14, h10⟩, hn⟩ := hs₀
    have hw := win_walk hC.2.2.1 (kf x t₀) kf_lt _ h10
    have hld := vlc_at hm hC.2.2.1 (kf x t₀) kf_lt 3 _ hw
    have pR : PLift _ := ⟨hR⟩
    have pLi : PLift _ := ⟨hLi⟩
    have pdi : PLift _ := ⟨hdi⟩
    have pax : PLift _ := ⟨hax⟩
    have p8 : PLift _ := ⟨h8⟩
    have p14 : PLift _ := ⟨h14⟩
    have pm : PLift _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals try subst_vars
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals nnorm
    all_goals try simp only [pR.down.2.2.2.2] at *
    all_goals try (simp only [hld.1, hld.2, Option.isSome_some]; done)
    all_goals try simp only [hld.1, hld.2, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals
      first
        | (left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
           refine ⟨by decide, ⟨⟨⟨hC, ?_, i, hi, pm.down⟩, ⟨c, pLi.down⟩, ⟨j, ?_, hj⟩⟩, ?_⟩, Or.inr ⟨?_, by decide +kernel⟩⟩ <;>
             try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
           all_goals first | exact pR.down | exact pdi.down | exact p8.down)
        | (have hs := ‹CondCode.ns.interp _ = false›
           simp only [CondCode.interp_ns, StatusFlags.sf_from_result, BitVec.and_self,
             Bool.not_eq_false', BitVec.msb_signExtend, decide_true, Bool.true_and, Nat.reduceLT] at hs
           refine ⟨⟨⟨⟨hC, ?_, i, hi, pm.down⟩, ⟨c, pLi.down⟩, ⟨j, ?_, hj⟩⟩, ?_, ?_, ?_, ⟨_, hw, hs, rfl, rfl⟩⟩, Nat.le.refl⟩ <;>
             try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
           all_goals first | exact pR.down | exact pdi.down | exact pax.down | exact p8.down | exact p14.down)

theorem blk_L657b (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_noise.L657b" := by
  cfg_block
  measure_hb "L657b"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨⟨⟨hC, hR, i, hi, hm⟩, ⟨c, hLi⟩, ⟨j, hdi, hj⟩⟩, hax, h8, h14, e, hW, hneg, h10, h11⟩, hn⟩ := hs₀
    have hbs := T_ld_bs hm
    have pR : PLift _ := ⟨hR⟩
    have pLi : PLift _ := ⟨hLi⟩
    have pdi : PLift _ := ⟨hdi⟩
    have p8 : PLift _ := ⟨h8⟩
    have p14 : PLift _ := ⟨h14⟩
    have p10 : PLift _ := ⟨h10⟩
    have p11 : PLift _ := ⟨h11⟩
    have pm : PLift _ := ⟨hm⟩
    clear hm
    vcgen [bswap32_havoc, shl_cl32_havoc]
    all_goals try subst_vars
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals nnorm
    case vc1 =>
      rw [p14.down, p8.down, BitVec.setWidth_32_64_32]
      exact hbs _ 4 (rd_off _ _ _ (gb_clamp _ _ _ _) hC.2.2.2.2.2.1)
    case vc2 =>
      refine ⟨⟨⟨⟨hC, ?_, i, hi, pm.down⟩, ⟨c, pLi.down⟩, ⟨j, ?_, hj⟩⟩, ?_, ?_,
        ⟨e, hW, hneg, ?_, ?_⟩⟩, Nat.le.refl⟩ <;>
        try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      all_goals first | exact pR.down | exact pdi.down | exact p8.down | exact p14.down | exact p11.down | rw [p10.down, zs16]

theorem blk_L659b (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_noise.L659b" := by
  cfg_block
  measure_hb "L659b"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨⟨⟨hC, hR, i, hi, hm⟩, ⟨c, hLi⟩, ⟨j, hdi, hj⟩⟩, h8, h14, e, hW, hneg, h10, h11⟩, hn⟩ := hs₀
    have hld := fun w => vlc_at hm hC.2.2.1 (kf x t₀) kf_lt 2 _ (vlc_walk_next hW hneg w)
    have hwk := fun w => vlc_walk_next hW hneg w
    have pR : PLift _ := ⟨hR⟩
    have pLi : PLift _ := ⟨hLi⟩
    have pdi : PLift _ := ⟨hdi⟩
    have p8 : PLift _ := ⟨h8⟩
    have p14 : PLift _ := ⟨h14⟩
    have pm : PLift _ := ⟨hm⟩
    have key : ∀ v : BitVec 64, v.setWidth 32 = ((s₀.regs.get64 .rbx).setWidth 32).ushiftRight
        ((BitVec.setWidth 64 (BitVec.setWidth 32 (s₀.regs.get64 .r11))).toNat % 256 % 32) →
        BitVec.setWidth 32 (s₀.regs.get64 .r10) + BitVec.setWidth 32 v
          = ((s₀.regs.get64 .rbx).setWidth 32).ushiftRight ((vlen (FH x t₀).es e).toNat % 32)
            + (vsym (FH x t₀).es e).signExtend 32 := by
      intro v hv
      rw [hv, h10, h11, BitVec.setWidth_32_64_32, BitVec.setWidth_32_64_32, vlc_sh, BitVec.add_comm]
    clear hm
    vcgen [shr_cl32_lo]
    all_goals try subst_vars
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals nnorm
    all_goals try simp only [pR.down.2.2.2.2] at *
    all_goals try simp only [key _ ‹_›] at *
    all_goals try (simp only [(hld _).1, (hld _).2, Option.isSome_some]; done)
    all_goals try simp only [(hld _).1, (hld _).2, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals
      first
        | (left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
           have hs := ‹CondCode.s.interp _ = true›
           simp only [CondCode.interp_s, StatusFlags.sf_from_result, BitVec.and_self,
             BitVec.msb_signExtend, decide_true, Bool.true_and, Nat.reduceLT, ↓reduceIte] at hs
           refine ⟨by decide, ⟨⟨⟨hC, ?_, i, hi, pm.down⟩, ⟨c, pLi.down⟩, ⟨j, ?_, hj⟩⟩, ?_, ?_, ⟨_, hwk _, hs, rfl, rfl⟩⟩, Or.inr ⟨?_, by decide +kernel⟩⟩ <;>
             try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
           all_goals first | exact pR.down | exact pdi.down | exact p8.down | exact p14.down)
        | (left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
           refine ⟨by decide, ⟨⟨⟨hC, ?_, i, hi, pm.down⟩, ⟨c, pLi.down⟩, ⟨j, ?_, hj⟩⟩, ?_⟩, Or.inr ⟨?_, by decide +kernel⟩⟩ <;>
             try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
           all_goals first | exact pR.down | exact pdi.down | exact p8.down)

theorem blk_L65b7 (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_noise.L65b7" := by
  cfg_block
  measure_hb "L65b7"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨⟨⟨hC, hR, i, hi, hm⟩, ⟨c, hLi⟩, ⟨j, hdi, hj⟩⟩, h8, h14, e, hW, hneg, h10, hbx⟩, hn⟩ := hs₀
    have hbs := T_ld_bs hm
    have pR : PLift _ := ⟨hR⟩
    have pLi : PLift _ := ⟨hLi⟩
    have pdi : PLift _ := ⟨hdi⟩
    have p8 : PLift _ := ⟨h8⟩
    have p14 : PLift _ := ⟨h14⟩
    have p10 : PLift _ := ⟨h10⟩
    have pbx : PLift _ := ⟨hbx⟩
    have pm : PLift _ := ⟨hm⟩
    clear hm
    vcgen [bswap32_havoc, shl_cl32_havoc]
    all_goals try subst_vars
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals nnorm
    case vc1 =>
      rw [p14.down, p8.down, BitVec.setWidth_32_64_32]
      exact hbs _ 4 (rd_off _ _ _ (gb_clamp _ _ _ _) hC.2.2.2.2.2.1)
    case vc2 =>
      refine ⟨⟨⟨⟨hC, ?_, i, hi, pm.down⟩, ⟨c, pLi.down⟩, ⟨j, ?_, hj⟩⟩, ?_,
        ⟨e, hW, hneg, ?_, ?_⟩⟩, Nat.le.refl⟩ <;>
        try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      all_goals first | exact pR.down | exact pdi.down | exact p8.down | exact pbx.down | rw [p10.down, zs16]

theorem blk_L65d9 (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_noise.L65d9" := by
  cfg_block
  measure_hb "L65d9"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨⟨⟨hC, hR, i, hi, hm⟩, ⟨c, hLi⟩, ⟨j, hdi, hj⟩⟩, h8, e, hW, hneg, h10, hbx⟩, hn⟩ := hs₀
    have hld := fun w => vlc_at hm hC.2.2.1 (kf x t₀) kf_lt 1 _ (vlc_walk_next hW hneg w)
    have pR : PLift _ := ⟨hR⟩
    have pLi : PLift _ := ⟨hLi⟩
    have pdi : PLift _ := ⟨hdi⟩
    have p8 : PLift _ := ⟨h8⟩
    have pm : PLift _ := ⟨hm⟩
    have key : ∀ v : BitVec 64, v.setWidth 32 = ((s₀.regs.get64 .r11).setWidth 32).ushiftRight
        ((BitVec.setWidth 64 (BitVec.setWidth 32 (s₀.regs.get64 .rbx))).toNat % 256 % 32) →
        BitVec.setWidth 32 (s₀.regs.get64 .r10) + BitVec.setWidth 32 v
          = ((s₀.regs.get64 .r11).setWidth 32).ushiftRight ((vlen (FH x t₀).es e).toNat % 32)
            + (vsym (FH x t₀).es e).signExtend 32 := by
      intro v hv
      rw [hv, h10, hbx, BitVec.setWidth_32_64_32, BitVec.setWidth_32_64_32, vlc_sh, BitVec.add_comm]
    clear hm
    vcgen [shr_cl32_lo]
    all_goals try subst_vars
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals nnorm
    all_goals try simp only [pR.down.2.2.2.2] at *
    all_goals try simp only [key _ ‹_›] at *
    all_goals try (simp only [(hld _).1, (hld _).2, Option.isSome_some]; done)
    all_goals
      first
        | (refine ⟨⟨⟨⟨hC, ?_, i, hi, pm.down⟩, ⟨c, pLi.down⟩, ⟨j, ?_, hj⟩⟩, ?_⟩, Nat.le.refl⟩ <;>
             try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
           all_goals first | exact pR.down | exact pdi.down | exact p8.down)

theorem blk_L65f0 (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_noise.L65f0" := by
  cfg_block
  measure_hb "L65f0"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨⟨⟨hC, hR, i, hi, hm⟩, ⟨c, hLi⟩, ⟨j, hdi, hj⟩⟩, h8⟩, hn⟩ := hs₀
    have hnq5 : x.nq ≤ 5 := hC.2.1
    have hsti := fun j : BitVec 32 => T_st_i hm j
    have hldi := T_ld_i hm
    have pR : PLift _ := ⟨hR⟩
    have pLi : PLift _ := ⟨hLi⟩
    have pdi : PLift _ := ⟨hdi⟩
    have p8 : PLift _ := ⟨h8⟩
    have P1 : PLift _ := ⟨hsti⟩
    clear hm hsti
    vcgen
    all_goals try subst_vars
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals nnorm
    all_goals try simp only [p8.down, pR.down.2.2.2.1, BitVec.setWidth_32_64_32]
    all_goals
      first
        | (simp only [hldi, Option.isSome_some]; done)
        | (have h := ‹CondCode.z.interp _ = true›
           rw [pdi.down] at h
           flg h
           exfalso; omega)
        | (refine ⟨⟨⟨hC, ?_, _, gb_clamp _ _ _ _, P1.down _⟩, ⟨c, pLi.down⟩, ⟨j, ?_, hj⟩⟩, Nat.le.refl⟩ <;>
             try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
           all_goals first | exact pR.down | exact pdi.down)

theorem blk_L6607 (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_noise.L6607" := by
  cfg_block
  measure_hb "L6607"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨⟨hC, hR, i, hi, hm⟩, ⟨c, hc12, hcn, hc13⟩, ⟨j, hdi, hj⟩⟩, hn⟩ := hs₀
    have hnn : x.nn ≤ 2 := hC.1
    have hnq5 : x.nq ≤ 5 := hC.2.1
    have hL := LcL.of hm hR.2.1
    have oq : (arg3 t₀ + 88662#64 + BitVec.ofNat 64 (5 * c) + BitVec.ofNat 64 j
        - (arg3 t₀ + 0x15a50#64)).toNat = 5 * c + 6 + j := by
      rw [show arg3 t₀ + 88662#64 + BitVec.ofNat 64 (5 * c) + BitVec.ofNat 64 j
          - (arg3 t₀ + 0x15a50#64) = BitVec.ofNat 64 (5 * c + 6 + j) by simp only [arg3]; bv_omega,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hstq := fun (v : Int) => T_st_nfq hm
      (arg3 t₀ + 88662#64 + BitVec.ofNat 64 (5 * c) + BitVec.ofNat 64 j) 1 (by rw [oq]; omega) v
    have hlq := T_ld_nfq hm
      (arg3 t₀ + 88662#64 + BitVec.ofNat 64 (5 * c) + BitVec.ofNat 64 j) 1 (by rw [oq]; omega)
    have hnq' := fun (v : Int) => T_ld_nq (hstq v)
    have pR : PLift _ := ⟨hR⟩
    have pc12 : PLift _ := ⟨hc12⟩
    have pc13 : PLift _ := ⟨hc13⟩
    have pdi : PLift _ := ⟨hdi⟩
    have P1 : PLift _ := ⟨hstq⟩
    have P2 : PLift _ := ⟨hlq⟩
    have P3 : PLift _ := ⟨hnq'⟩
    clear hm hstq oq hlq hnq'
    have e1 : BitVec.ofNat 64 j + 1#64 = BitVec.ofNat 64 (j + 1) := succ64 j (by omega)
    have e2 : BitVec.ofNat 64 j + 2#64 = BitVec.ofNat 64 (j + 2) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have e3 := nat32to64 x.nq (by omega)
    have pe1 : PLift _ := ⟨e1⟩
    have pe2 : PLift _ := ⟨e2⟩
    have pe3 : PLift _ := ⟨e3⟩
    clear e1 e2 e3
    vcgen [shl_cl32_havoc]
    all_goals try subst_vars
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals nnorm
    all_goals try (simp only [hL.w]; done)
    all_goals try simp only [pR.down.2.1, pR.down.2.2.1, pR.down.2.2.2.1, pc12.down, pc13.down, pdi.down] at *
    all_goals try (simp only [P3.down, Option.isSome_some]; done)
    all_goals try simp only [P3.down, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt32_ofBytes_toBytes4] at *
    all_goals try simp only [pe2.down, pe3.down] at *
    all_goals
      first
        | exact P2.down
        | (left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
           refine ⟨by decide, ⟨hC, ?_, i, hi, P1.down _⟩, Or.inl ?_⟩
           · (try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]); exact pR.down
           · simp only [Nat.add_eq, Nat.succ_eq_add_one]; omega)
        | (have h := ‹CondCode.c.interp _ = true›
           flg h
           left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
           refine ⟨by decide, ⟨⟨hC, ?_, i, hi, P1.down _⟩, ⟨c, ?_, hcn, ?_⟩, ⟨j + 1, ?_, ?_⟩⟩, Or.inl ?_⟩ <;>
             try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
           all_goals first | exact pR.down | rfl | omega | (simp only [Nat.add_eq, Nat.succ_eq_add_one, BitVec.toNat_ofNat]; omega) | exact pc12.down | exact pc13.down | exact pe1.down | (rw [pc12.down, pe1.down]; simp only [Nat.add_eq, BitVec.toNat_ofNat]; omega))
        | (refine ⟨⟨⟨hC, ?_, i, hi, P1.down _⟩, ⟨c, ?_, hcn, ?_⟩⟩, ?_⟩ <;>
             try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
           all_goals first | exact pR.down | rfl | (simp only [Nat.add_eq, Nat.succ_eq_add_one, BitVec.toNat_ofNat]; omega) | exact pc12.down | exact pc13.down | exact pe1.down | (rw [pc12.down, pe1.down]; simp only [Nat.add_eq, BitVec.toNat_ofNat]; omega))

end Kraken.Examples.Sbr.Noise
