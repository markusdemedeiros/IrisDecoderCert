import Kraken.X64.Examples.Sbr.Parse.ResetQs3Lib

/-!
# `sbr_reset`, `AV_QSORT` copy 3 (`vk1`): the pop (`L2390`)
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse Kraken.Examples.Sbr.Parse.Qsort

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Reset

variable [CodeEnv]

set_option maxRecDepth 100000 in
theorem blk_L2390 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2390" ⟨"sbr_reset.L2390", B.L2390, some "sbr_reset.L2398"⟩ := by
  info_off
  measure_hb "L2390"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, st, fr, hX, ⟨hrsp, hrbp⟩, hRg, hF, hWf, hm, hN1, hN2, S, A0, hax, hD, hR, hSR,
      hQ⟩ :=
      Q3.g_iff.mp (T.L2390.mp hs)
    clear hs
    have hS6 : S.length ≤ 6 := depth_len (m := 6) hD (by omega)
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L2390]
    vcgen
    all_goals try subst_vars
    all_goals rename_i c
    all_goals rw [hax, cc_z_test32 _ (by omega)] at c
    all_goals simp only [decide_eq_true_eq, decide_eq_false_iff_not] at c
    · left; apply Table.ofLabels_at
      have hS0 : S = [] := List.eq_nil_of_length_eq_zero c
      subst hS0
      obtain ⟨hN0, hI, h30, vm, hv1, hv2, hTA⟩ := hWf
      obtain ⟨hr15, hr12, hr13⟩ := hRg
      obtain ⟨hC, hB, hr, hk2, hk0, hq, hu, hx, hsp, hfm, hk2v, hk1v, h110, hN1'⟩ := hX
      refine ⟨by decide, T.L25cf.mpr ⟨row, k2, hr, hk2, hk0, hq, hu, hC, hB, ⟨hrsp, hrbp⟩, st, fr,
        hx, hsp, hfm, hF, ⟨hk2v, hk1v, h110, hI, hN0, hN1', hr15, hr12, hr13, vm, hv1, hv2,
          hTA, h30, arr_of_qw hR hQ⟩, hm⟩, ?_⟩
      edge_step
    · refine ⟨T.L2398.mpr (Q3.g_iff.mpr ⟨row, k2, st, fr, hX, ⟨hrsp, hrbp⟩, (by q3_rg hRg), hF, hWf,
        hm, ⟨hN1, hN2, S, A0, hax, hD, hR, hSR, hQ⟩, ?_⟩), ?_⟩
      · rw [hax]; intro h'
        have := congrArg BitVec.toNat h'
        simp only [BitVec.toNat_ofNat] at this; omega
      · var_step

end Kraken.Examples.Sbr.Reset
