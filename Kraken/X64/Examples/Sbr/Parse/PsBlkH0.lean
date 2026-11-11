import Kraken.X64.Examples.Sbr.Parse.PsBlkHLib

/-!
# `ff_ps_read_data`: the prologue and the first header bits
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Ps

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

set_option maxRecDepth 20000 in
/-- The prologue: six pushes, `sub $0x78`; the locals' block gets its contents `f`. -/
theorem blk_Entry (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data" := by
  cfg_block
  measure_hb "Entry"
    intro n
    simp only [tab_Entry, var_Entry, tab_L11, var_L11]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨rfl, hC, hm⟩, hn⟩ := hs₀
    obtain ⟨-, f, hf, hm'⟩ := Block.sep_elim hm
    rw [← Val.eq] at hm'
    clear hm
    have PA := push6_a (s₀.regs.get64 .rbp).toInt (s₀.regs.get64 .r15).toInt
      (s₀.regs.get64 .r14).toInt (s₀.regs.get64 .r13).toInt (s₀.regs.get64 .r12).toInt
      (s₀.regs.get64 .rbx).toInt hm'
    have PB := push6_b (s₀.regs.get64 .rbp).toInt (s₀.regs.get64 .r15).toInt
      (s₀.regs.get64 .r14).toInt (s₀.regs.get64 .r13).toInt (s₀.regs.get64 .r12).toInt
      (s₀.regs.get64 .rbx).toInt hm'
    have PM := push6_m (s₀.regs.get64 .rbp).toInt (s₀.regs.get64 .r15).toInt
      (s₀.regs.get64 .r14).toInt (s₀.regs.get64 .r13).toInt (s₀.regs.get64 .r12).toInt
      (s₀.regs.get64 .rbx).toInt hm'
    clear hm'
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals try simp only [BitVec.sub_sub_eight, BitVec.reduceAdd] at *
    case vc1 => exact PA.1
    case vc2 => exact PA.2.1
    case vc3 => exact PA.2.2.1
    case vc4 => exact PA.2.2.2
    case vc5 => exact PB.1
    case vc6 => exact PB.2
    all_goals refine ⟨?_, by var_step⟩
    unfold q11
    refine ⟨hC, ?_, ?_, ?_, ?_, f, hf, ?_⟩
    case refine_5 => exact PM
    all_goals clear PA PB PM hC
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, rsp0, Args, arg0,
      arg1, arg2, arg3, and_self]
    rw [show BitVec.setWidth 64 (Int64.toBitVec 120) = 120#64 from rfl]; bv_omega

end Kraken.Examples.Sbr.Ps
