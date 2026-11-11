import Kraken.X64.Examples.Sbr.Parse.DecExtMem

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

/-!
# `ff_aac_sbr_decode_extension`: the exit (the length check, `sbr_turnoff`, the epilogue)
-/

namespace Kraken.Examples.Sbr.DecExt

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

theorem blk_L4ee (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L4ee" := by
  cfg_block
  measure_hb "L4ee"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨hsp, hbp, h14⟩, h12, d, ih, hI, hih, hm⟩, hn⟩ := hs₀
    var_n hn
    simp only [T] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals have hm := p_hm.down; clear p_hm
    dx_run hm [hbp, hsp, h14, h12, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff]
    dx_br hm
    all_goals try (simp only [Int.toBytes_length, Nat.reducePow, BitVec.sub_self, BitVec.toNat_zero]; omega)
    case vc2 =>
      left; apply Table.ofLabels_at
      rw [table.match_1.eq_37]
      refine ⟨by decide, ⟨hC, ⟨?_, ?_, ?_⟩, ?_, d, ih, hI, hih, ?_⟩, ?_⟩
      all_goals first | assumption | sep_close hm | edge_ok var_L57e
    case vc3 =>
      refine ⟨⟨hC, ⟨trivial, trivial, trivial⟩, trivial, d, ih, hI, hih, ?_⟩, Nat.le_of_eq (var_L50b _)⟩
      sep_close hm


omit [CodeEnv] in
theorem lit_add_sub (r : BitVec 64) (a b : Nat) :
    BitVec.ofNat 64 b + (r - BitVec.ofNat 64 a) = r - BitVec.ofNat 64 a + BitVec.ofNat 64 b :=
  BitVec.add_comm _ _

theorem blk_L57e (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L57e" := by
  cfg_block
  measure_hb "L57e"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨hsp, hbp, h14⟩, h12, d, ih, hI, hih, hm⟩, hn⟩ := hs₀
    var_n hn
    simp only [T] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals have hm := p_hm.down; clear p_hm
    dx_run hm [hbp, hsp, h14, h12, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff,
      BitVec.reduceSetWidth, lit_add_sub, BitVec.reduceOfNat]
    dx_br hm
    all_goals simp only [BitVec.reduceOfNat] at *
    dx_br hm
    simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, BitVec.sub_zero]
    refine ⟨⟨hC, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, d, ih, hI, hih, ?_⟩, Nat.le_of_eq (var_done _)⟩
    all_goals first | trivial | rfl | sep_close hm


theorem T_ret (kc : Nat) (Ext : Mem 64 → Prop) (X : XA) (ra : Int64) (t₀ : MachineData)
    (d : DS) (ih : BitVec 32) :
    T kc Ext X ra t₀ (Saved t₀) (LocE t₀) d ih = RetCell ra (t₀.regs.get64 .rsp)
      ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x70#64) ⋆ (Reserve kc (t₀.regs.get64 .rsp - 0x70#64)
        ⋆ (LocE t₀ ⋆ (DecF Ext X t₀ d ih ⋆ Saved t₀ X.R)))) := by
  simp only [T, Saved, Rest]; ac_rfl

theorem blk_done (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.done" := by
  cfg_block
  measure_hb "done"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hsp, hbp, hsv, hax, d, ih, hI, hih, hm⟩, hn⟩ := hs₀
    rw [T_ret] at hm
    have hpost : s₀.dmem =⋆ 8 ?@ t₀.regs.get64 .rsp ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x70#64)
        ⋆ (Reserve kc (t₀.regs.get64 .rsp - 0x70#64)
        ⋆ (LocE t₀ ⋆ (DecF Ext X t₀ d ih ⋆ Saved t₀ X.R)))) :=
      Block.sep_intro (Int.toBytes_length _ _) (by decide) hm
    generalize 8 ?@ (t₀.regs.get64 .rsp - 0x70#64) ⋆ (Reserve kc (t₀.regs.get64 .rsp - 0x70#64)
        ⋆ (LocE t₀ ⋆ (DecF Ext X t₀ d ih ⋆ Saved t₀ X.R))) = Q at hm
    have l0 : s₀.dmem.loadInt (t₀.regs.get64 .rsp) 8
        = some (Int.ofBytes (Int.toBytes 8 ra.toBitVec.toInt)) := by
      grind (ematch := 400) (gen := 400) (instances := 20000) (mbtc := false)
        [-BitVec.toInt_eq_toNat_of_msb, -BitVec.toInt_eq_toNat_bmod]
    have hra : s₀.retAddr = some ra := by
      simp only [MachineData.retAddr, hsp, l0, Option.map_some,
        BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Int64.ofBitVec_toBitVec]
    clear hm l0
    vcgen
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals simp only [hra, Option.isSome_some, Option.some.injEq] at *
    subst_vars
    right; left
    refine ⟨rfl, hC.rsp, d, ih, hI, hih, ?_, ?_, ?_, ?_, hpost⟩
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hsp, hbp, hsv, hax,
      and_self]
    all_goals rfl

end Kraken.Examples.Sbr.DecExt
