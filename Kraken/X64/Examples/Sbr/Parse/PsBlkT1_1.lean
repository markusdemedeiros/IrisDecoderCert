import Kraken.X64.Examples.Sbr.Parse.PsBlkT1Lib

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Ps

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

set_option maxRecDepth 20000 in
/-- The `iid` check failed: the format string. -/
theorem blk_L10cf (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L10cf" := by
  cfg_block
  measure_hb "L10cf"
    intro n
    simp only [tab_L10cf, var_L10cf, tab_L10d6, var_L10d6]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, ⟨hC, ⟨hsp, hbp, hf, hP, hbl, h08, hid⟩, hm⟩, h68, hR⟩, hn⟩ := hs₀
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    exact ⟨⟨c, f, ⟨hC, ⟨by t1r; exact hsp, by t1r; exact hbp, hf, hP, hbl, h08, hid⟩, hm⟩, h68, hR⟩,
      by var_step⟩

set_option maxRecDepth 20000 in
/-- `icc_par[N][0] ≤ 7` (`0x14ec`), else the error (`0x132a`); trap: `num_env > 4`. -/
theorem blk_L12ff (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L12ff" := by
  cfg_block
  measure_hb "L12ff"
    intro n
    simp only [tab_L12ff, var_L12ff, tab_L132a, var_L132a]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, N, ⟨hB, hW⟩, ⟨hne, h12⟩, hbx, hc0, hcx⟩, hn⟩ := hs₀
    have hl := t1_B_len hB
    have hN4 : N ≤ 4 := hB.2.2.2.1
    have L1 := t1_B_fload hB (18446744073709551520#64) 0x60 1 rfl (by omega) (by omega) (by omega)
    have h40 : rd f 0x40 1 = N := t1_rd1 f 0x40 N (by have := hB.1.2.1.2.2.1; omega) hB.2.2.2.2.1 (by omega)
    have LB := t1_B_load hB (246 + 34 * N) 1 (by omega)
    have hA : BitVec.setWidth 64 246#64 + (s₀.regs.get64 .rbx
        + (BitVec.setWidth 64 (BitVec.setWidth 32 (s₀.regs.get64 .r12)) <<< 5
          + BitVec.setWidth 64 (BitVec.setWidth 32 (s₀.regs.get64 .r12)) * 2#64))
        = arg2 t₀ + BitVec.ofNat 64 (246 + 34 * N) := by
      rw [hbx, h12, t1_sw N (by omega), t1_r34]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
    have hA' : BitVec.setWidth 64 246#64 + (s₀.regs.get64 .rbx
        + (BitVec.setWidth 64 (BitVec.setWidth 32 (s₀.regs.get64 .r12)) <<< 5
          + BitVec.setWidth 64 (BitVec.setWidth 32 (s₀.regs.get64 .r12)) * 2#64))
        = arg2 t₀ + BitVec.ofNat 64 (34 * N + 0xf6) := by rw [hA, Nat.add_comm]
    rw [← hA] at LB
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals t1norm at *
    all_goals try t1cc at *
    all_goals try simp only [L1, LB, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    case vc2 =>
      exfalso; rename_i htr; rw [h40] at htr
      simp only [BitVec.ofInt_natCast, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at htr; omega
    case vc4 =>
      t1_jump "ff_ps_read_data.L14ec"
      exact ⟨c, f, N, ⟨t1_B_eq hB rfl (by t1r) (by t1r) (by t1r) (by t1r), hW⟩, ⟨hne, by t1r; exact h12⟩,
        by t1r; exact hbx, hc0, by t1r; exact hcx, by t1r; exact hA'⟩
    case vc5 =>
      exact ⟨⟨⟨c, f, (t1_B_eq hB rfl (by t1r) (by t1r) (by t1r) (by t1r)).1, by t1r; exact hbx,
        fun hp => ⟨(hW hp).1.1, (hW hp).1.2.1⟩⟩, by t1r; exact hB.2.2.1⟩, by var_step⟩

end Kraken.Examples.Sbr.Ps
