import Kraken.X64.Examples.Sbr.Parse.ResetQsFr

/-!
# `sbr_reset`, `AV_QSORT` copy 1 (`stop_dk`): the pop (`L12d0`)
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse Kraken.Examples.Sbr.Parse.Qsort

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Reset

variable [CodeEnv]

theorem blk_L12d0 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L12d0" ⟨"sbr_reset.L12d0", B.L12d0, some "sbr_reset.L12d8"⟩ := by
  info_off
  measure_hb "L12d0"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, hr, hsp1, hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨h40, h30, hN1, hN2, S, A0, hax, hD, hR, hSR, hQ⟩, hm⟩ := T.L12d0.mp hs
    clear hs
    have hS6 : S.length ≤ 6 := depth_len (m := 6) hD (by omega)
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L12d0]
    vcgen
    all_goals try subst_vars
    all_goals rename_i c
    all_goals rw [hax, cc_z_test32 _ (by omega)] at c
    all_goals simp only [decide_eq_true_eq, decide_eq_false_iff_not] at c
    · left; apply Table.ofLabels_at
      refine ⟨by decide, T.L1523.mpr ⟨row, hr, hsp1, hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm,
        hF, ⟨h40, h30, trivial⟩, hm⟩, ?_⟩
      edge_step
    · refine ⟨T.L12d8.mpr ⟨row, hr, hsp1, hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
        ⟨h40, h30, ⟨hN1, hN2, S, A0, hax, hD, hR, hSR, hQ⟩, ?_⟩, hm⟩, ?_⟩
      · rw [hax]; intro h'
        have := congrArg BitVec.toNat h'
        simp only [BitVec.toNat_ofNat] at this; omega
      · var_step

end Kraken.Examples.Sbr.Reset
