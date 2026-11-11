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
/-- The error path: `r15d = bits_left` reloaded. -/
theorem blk_L1475 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L1475" := by
  cfg_block
  measure_hb "L1475"
    intro n
    simp only [tab_L1475, var_L1475, tab_L1479, var_L1479]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hC, hbx, hR⟩, hn⟩ := hs₀
    have L := t2_fload hC (18446744073709551572#64) 0x2c 4 rfl (by omega) (by omega) (by omega)
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals t1norm at *
    all_goals try simp only [L, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    exact ⟨⟨⟨c, f, t2_C_eq hC rfl (by t1r) (by t1r), by t1r; exact hbx, hR⟩,
      by t1r; rw [t2_sw3264]; exact hC.2.1.2.2.2.2.1⟩, by var_step⟩

set_option maxRecDepth 20000 in
/-- The extension overran: the format, the context. -/
theorem blk_L1459 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L1459" := by
  cfg_block
  measure_hb "L1459"
    intro n
    simp only [tab_L1459, var_L1459, tab_L1464, var_L1464]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hC, hbx, hR⟩, hn⟩ := hs₀
    have L := t2_fload hC (18446744073709551552#64) 0x40 8 rfl (by omega) (by omega) (by omega)
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals t1norm at *
    all_goals try simp only [L, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    exact ⟨⟨c, f, t2_C_eq hC rfl (by t1r) (by t1r), by t1r; exact hbx, hR⟩, by var_step⟩

end Kraken.Examples.Sbr.Ps
