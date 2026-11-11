import Kraken.X64.Examples.Sbr.Parse.TlimMem

/-!
# `sbr_make_f_tablelim`: the epilogue (`L43bd`, `done`)
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Tlim

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

omit [CodeEnv] in
theorem pop_offs (t : BitVec 64) : 0x420#64 + (t - 0x448#64) = t - 40#64
    ∧ t - 40#64 + 8#64 = t - 32#64 ∧ t - 40#64 + 16#64 = t - 24#64
    ∧ t - 32#64 + 8#64 = t - 24#64 ∧ t - 32#64 + 16#64 = t - 16#64
    ∧ t - 32#64 + 24#64 = t - 8#64 ∧ t - 32#64 + 32#64 = t
    ∧ t - 24#64 + 8#64 = t - 16#64 ∧ t - 16#64 + 8#64 = t - 8#64 ∧ t - 8#64 + 8#64 = t := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_omega

theorem blk_L43bd (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L43bd" := by
  cfg_block
  measure_hb "L43bd"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨hsp, hbp, h13⟩, y, stk, pb, hT, hy, hL, hm⟩, hn⟩ := hs₀
    rw [var_L43bd] at hn
    subst hn
    have hmT := hm
    have hm' := focus (T_fr k x ra t₀ (Saved t₀) _) hm
    clear hm
    generalize Tfr k x t₀ _ = Q at hm'
    have po := pop_offs (t₀.regs.get64 .rsp)
    have l1 : s₀.dmem.loadInt (t₀.regs.get64 .rsp - 40#64) 8
        = some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 .rbx).toInt)) := by grind_cells'
    have l2 : s₀.dmem.loadInt (t₀.regs.get64 .rsp - 32#64) 8
        = some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 .r12).toInt)) := by grind_cells'
    have l3 : s₀.dmem.loadInt (t₀.regs.get64 .rsp - 24#64) 8
        = some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 .r14).toInt)) := by grind_cells'
    have l4 : s₀.dmem.loadInt (t₀.regs.get64 .rsp - 16#64) 8
        = some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 .r15).toInt)) := by grind_cells'
    have l5 : s₀.dmem.loadInt (t₀.regs.get64 .rsp - 8#64) 8
        = some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 .rbp).toInt)) := by grind_cells'
    clear hm'
    vcgen
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.setWidth_eq] at *
    all_goals simp only [hsp, po.1, po.2.1, po.2.2.1, po.2.2.2.1,
      po.2.2.2.2.1, po.2.2.2.2.2.1, po.2.2.2.2.2.2.1, po.2.2.2.2.2.2.2.1, po.2.2.2.2.2.2.2.2.1,
      po.2.2.2.2.2.2.2.2.2] at *
    all_goals simp only [l1, l2, l3, l4, l5, Option.isSome_some, Option.some.injEq] at *
    subst_vars
    try simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]
    rw [tab_done, var_done]
    refine ⟨⟨hC, ?_, ?_, ?_, y, stk, pb, hT, hy, hL, hmT⟩, Nat.le_refl 0⟩
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, SavedRegs, h13, and_self]

theorem T_ret (k : Nat) (x : TArgs) (ra : Int64) (t₀ : MachineData) (st : TSt) :
    T k x ra t₀ (Saved t₀) st = RetCell ra (rS t₀) ⋆ (Saved t₀ x.R ⋆ Tfr k x t₀ st) := by
  simp only [T, Saved, Rest, Tfr]; ac_rfl

theorem Post_mem (k : Nat) (x : TArgs) (ra : Int64) (t₀ : MachineData) (st : TSt) :
    8 ?@ rS t₀ ⋆ (Saved t₀ x.R ⋆ Tfr k x t₀ st)
      = T k x ra t₀ (fun _ => Saved t₀ (8 ?@ rS t₀ ⋆ x.R)) st := by
  simp only [T, Saved, Tfr]; ac_rfl

theorem blk_done (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.done" := by
  cfg_block
  measure_hb "done"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hsp, hbp, hsv, y, stk, pb, hT, hy, hL, hm⟩, hn⟩ := hs₀
    rw [T_ret] at hm
    have hpost : s₀.dmem =⋆ 8 ?@ rS t₀ ⋆ (Saved t₀ x.R ⋆ Tfr k x t₀ ⟨y.ftLim, y.nlim, stk, pb⟩) :=
      Block.sep_intro (Int.toBytes_length _ _) (by decide) hm
    rw [Post_mem k x ra] at hpost
    generalize Saved t₀ x.R ⋆ Tfr k x t₀ _ = Q at hm
    have l0 : s₀.dmem.loadInt (rS t₀) 8
        = some (Int.ofBytes (Int.toBytes 8 ra.toBitVec.toInt)) := by grind_cells'
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
    right
    refine ⟨rfl, y, stk, pb, hT, hy, hL, ?_, ?_, ?_, hpost⟩
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hsp, hbp, hsv, and_self]
    all_goals try simp only [SavedRegs, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] at hsv ⊢
    all_goals try exact hsv
    all_goals try exact rfl

end Kraken.Examples.Sbr.Tlim
