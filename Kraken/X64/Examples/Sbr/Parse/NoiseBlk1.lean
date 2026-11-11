import Kraken.X64.Examples.Sbr.Parse.NoiseMem

/-!
# `read_sbr_noise`: the outer loop head and the `t_huff` path
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Vlc
open Kraken.Examples.Sbr.Parse (GbW bswap32_havoc shl_cl32_havoc rd_off)

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Noise

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

theorem blk_L6190 (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_noise.L6190" := by
  cfg_block
  measure_hb "L6190"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨⟨hC, hR, i, hi, hm⟩, ⟨c, hc12, hcn, hc13⟩, h9⟩, hn⟩ := hs₀
    have hnn : x.nn ≤ 2 := hC.1
    have hnq := NqL.of hm hR.2.2.1
    have hdf : (s₀.dmem.loadInt (s₀.regs.get64 .r9 + s₀.regs.get64 .r12 + 37#64) 1).isSome := by
      rw [h9, hc12]
      refine T_ld_df hm _ ?_
      rw [show arg3 t₀ + BitVec.ofNat 64 c + 37#64 - (arg3 t₀ + 0x25#64) = BitVec.ofNat 64 c by
        bv_omega, BitVec.toNat_ofNat]
      omega
    vcgen
    all_goals try subst_vars
    all_goals try dsimp only [reduceTable, reduceVar] at *
    case vc2 =>
      left
      apply Table.ofLabels_at
      dsimp only [reduceTable, reduceVar]
      exact ⟨by decide, ⟨⟨hC, hR, i, hi, hm⟩, ⟨c, hc12, hcn, hc13⟩, h9⟩, Or.inr ⟨rfl, by decide +kernel⟩⟩
    case vc4 =>
      left
      apply Table.ofLabels_at
      dsimp only [reduceTable, reduceVar]
      exact ⟨by decide, ⟨⟨hC, hR, i, hi, hm⟩, ⟨c, hc12, hcn, hc13⟩⟩, Or.inl (by simp only [Nat.add_eq, Nat.succ_eq_add_one]; omega)⟩
    case vc5 =>
      exact ⟨⟨⟨hC, hR, i, hi, hm⟩, ⟨c, hc12, hcn, hc13⟩⟩, Nat.le.refl⟩
    all_goals nnorm
    case vc1 => exact hdf
    case vc3 => simp only [hnq.ld, Option.isSome_some]

theorem blk_L61a9 (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_noise.L61a9" := by
  cfg_block
  measure_hb "L61a9"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨⟨hC, hR, i, hi, hm⟩, ⟨c, hc12, hcn, hc13⟩⟩, hn⟩ := hs₀
    have hnn : x.nn ≤ 2 := hC.1
    have hL := LcL.of hm hR.2.1
    have hG := GbL.of hm hR.2.2.2.1
    have hnfq := T_ld_nfq hm
    have hbs := T_ld_bs hm
    have hoff := rd_off i x.p8 x.L hi hC.2.2.2.2.2.1
    have h5 := lea5 c (by omega)
    have hc12' : PLift _ := ⟨hc12⟩
    have hc13' : PLift _ := ⟨hc13⟩
    vcgen [bswap32_havoc, shl_cl32_havoc]
    all_goals try subst_vars
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals nnorm
    all_goals try (simp only [hL.d15, hG.ld_i, hG.ld_buf, hG.ld_p8, Option.isSome_some]; done)
    all_goals try simp only [hL.d15, hG.ld_i, hG.ld_buf, hG.ld_p8, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt64_ofBytes_toBytes8,
      BitVec.ofInt_toInt, hc12, h5] at *
    case vc2 =>
      refine hnfq _ 1 ?_
      rw [show arg3 t₀ + 88656#64 + BitVec.ofNat 64 (5 * c) - (arg3 t₀ + 0x15a50#64)
        = BitVec.ofNat 64 (5 * c) by bv_omega, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show 5 * c < 2 ^ 64 by omega)]
      omega
    case vc6 => exact hbs _ 4 hoff
    case vc7 =>
      refine ⟨⟨⟨hC, ?_, i, hi, hm⟩, ⟨c, ⟨?_, hcn, ?_⟩, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
        try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      all_goals first | exact hR | exact Nat.le.refl | exact hc12'.down | exact hc13'.down | exact win9 _ | exact Nat.le.refl | (simp only [BitVec.toNat_setWidth]; omega)

end Kraken.Examples.Sbr.Noise
