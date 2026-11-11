import Kraken.X64.Examples.Sbr.Parse.PsBlkT2Lib

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Ps

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

set_option maxRecDepth 20000 in
/-- The epilogue: the result, the locals freed, the six pops. -/
theorem blk_L14b7 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L14b7" := by
  cfg_block
  measure_hb "L14b7"
    intro n
    simp only [tab_L14b7, var_L14b7, tab_done, var_done]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, i, f, hO, hfl, hsp, hbp, hm⟩, hn⟩ := hs₀
    have hm' := hm
    simp only [Fr, Sv] at hm'
    have l1 : s₀.dmem.loadInt (rsp0 t₀ - 0x30#64) 8
        = some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 .rbx).toInt)) :=
      loadInt_sep _ _ 8 _ _ (focus (eq_r (eq_l (eq_r (eq_r (eq_r (eq_r
        (Std.ExtHashMap.sep_comm _ _))))))) hm') (Int.toBytes_length 8 _) (by omega)
    have l2 : s₀.dmem.loadInt (rsp0 t₀ - 0x28#64) 8
        = some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 .r12).toInt)) :=
      loadInt_sep _ _ 8 _ _ (focus (eq_r (eq_l (eq_r (eq_r (eq_r (eq_r eq_h)))))) hm')
        (Int.toBytes_length 8 _) (by omega)
    have l3 : s₀.dmem.loadInt (rsp0 t₀ - 0x20#64) 8
        = some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 .r13).toInt)) :=
      loadInt_sep _ _ 8 _ _ (focus (eq_r (eq_l (eq_r (eq_r (eq_r eq_h))))) hm')
        (Int.toBytes_length 8 _) (by omega)
    have l4 : s₀.dmem.loadInt (rsp0 t₀ - 0x18#64) 8
        = some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 .r14).toInt)) :=
      loadInt_sep _ _ 8 _ _ (focus (eq_r (eq_l (eq_r (eq_r eq_h)))) hm')
        (Int.toBytes_length 8 _) (by omega)
    have l5 : s₀.dmem.loadInt (rsp0 t₀ - 0x10#64) 8
        = some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 .r15).toInt)) :=
      loadInt_sep _ _ 8 _ _ (focus (eq_r (eq_l (eq_r eq_h))) hm')
        (Int.toBytes_length 8 _) (by omega)
    have l6 : s₀.dmem.loadInt (rsp0 t₀ - 8#64) 8
        = some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 .rbp).toInt)) :=
      loadInt_sep _ _ 8 _ _ (focus (eq_r (eq_l eq_h)) hm')
        (Int.toBytes_length 8 _) (by omega)
    clear hm'
    have po : ∀ R : BitVec 64, BitVec.setWidth 64 120#64 + (R - 168#64) = R - 48#64
        ∧ R - 48#64 + 8#64 = R - 40#64 ∧ R - 40#64 + 8#64 = R - 32#64
        ∧ R - 32#64 + 8#64 = R - 24#64 ∧ R - 24#64 + 8#64 = R - 16#64
        ∧ R - 16#64 + 8#64 = R - 8#64 ∧ R - 8#64 + 8#64 = R := fun R => by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_omega
    obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := po (t₀.regs.get64 .rsp)
    simp only [rsp0] at l1 l2 l3 l4 l5 l6
    vcgen
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals t1norm at *
    all_goals simp only [hsp, p1, p2, p3, p4, p5, p6, p7] at *
    all_goals simp only [l1, l2, l3, l4, l5, l6, Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    refine ⟨⟨c, i, f, ?_, hfl, ?_, ?_, ?_, hm⟩, by var_step⟩ <;> try t1r
    · rw [t2_sw3264]; exact hO
    · try simp only [ofInt_toBytes64]
    · simp only [ofInt_toBytes64]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 20000 in
/-- The return. -/
theorem blk_done (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.done" := by
  cfg_block
  measure_hb "done"
    intro n
    simp only [tab_done, var_done]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, i, f, hO, hfl, hsp, hbp, hS, hm⟩, hn⟩ := hs₀
    have hm' := hm
    simp only [Fr, RetCell] at hm'
    have l0 : s₀.dmem.loadInt (rsp0 t₀) 8
        = some (Int.ofBytes (Int.toBytes 8 ra.toBitVec.toInt)) :=
      loadInt_sep _ _ 8 _ _ (focus (eq_r (eq_r (eq_r (eq_r (eq_r eq_h))))) hm')
        (Int.toBytes_length 8 _) (by omega)
    have hra : s₀.retAddr = some ra := by
      simp only [MachineData.retAddr, hsp, l0, Option.map_some,
        BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Int64.ofBitVec_toBitVec]
    clear hm' l0
    vcgen
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals simp only [hra, Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    right
    exact ⟨rfl, c, i, f, hO, hfl, by rw [hsp]; rfl, hbp, hS, hm⟩

end Kraken.Examples.Sbr.Ps
