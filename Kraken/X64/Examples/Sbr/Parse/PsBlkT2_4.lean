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
/-- `num_env = N + 1` (the `icc` row checked). -/
theorem blk_L14f1 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L14f1" := by
  cfg_block
  measure_hb "L14f1"
    intro n
    simp only [tab_L14f1, var_L14f1]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, N, ⟨hB, hW⟩, ⟨hne, h12⟩, hbx⟩, hn⟩ := hs₀
    have hl := t1_B_len hB
    have hN4 : N ≤ 4 := hB.2.2.2.1
    vcgen
    all_goals try subst_vars
    all_goals t1norm at *
    · have L := t1_B_load hB 44 4 (by omega)
      simp only [arg2] at L
      rw [hbx, L]; rfl
    · t1_jump "ff_ps_read_data.L135c"
      show q135c _ _ _ _ _ _
      simp only [hbx, h12]
      rw [t2_inc N (by omega)]
      have e1 : (BitVec.ofNat 32 (N + 1)).toInt = ((N + 1 : Nat) : Int) := t1_toInt_ofNat32 _ (by omega)
      refine ⟨wr c 44 4 (BitVec.ofNat 32 (N + 1)).toInt, f, N,
        ⟨t1_B_st44 hB _ (by omega) (by omega) rfl (by t1r) (by t1r) (by t1r) (by t1r),
          fun hp => t1_W1_wr44 (hW hp) hl hN4 _⟩, ?_, ?_, by t1r; exact hbx⟩
      · simp only [ne]; rw [i32_wr_same _ _ _ (by omega), e1]; push_cast; rfl
      · t1r; exact t2_inc N (by omega)

end Kraken.Examples.Sbr.Ps
