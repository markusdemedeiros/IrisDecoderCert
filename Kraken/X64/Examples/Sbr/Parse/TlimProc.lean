import Kraken.X64.Examples.Sbr.Parse.TlimBlkA
import Kraken.X64.Examples.Sbr.Parse.TlimTrap
import Kraken.X64.Examples.Sbr.Parse.TlimBlkB
import Kraken.X64.Examples.Sbr.Parse.TlimBlkC
import Kraken.X64.Examples.Sbr.Parse.TlimBlkD
import Kraken.X64.Examples.Sbr.Parse.TlimBlkE
import Kraken.X64.Examples.Sbr.Parse.TlimMc
import Kraken.X64.Examples.Sbr.Parse.TlimFin
import Kraken.X64.Examples.Sbr.Parse.TlimCmp
import Kraken.X64.Examples.Sbr.Parse.TlimCmp2
import Kraken.X64.Examples.Sbr.Parse.TlimCmp3
import Kraken.X64.Examples.Sbr.Parse.TlimQsA
import Kraken.X64.Examples.Sbr.Parse.TlimQsB
import Kraken.X64.Examples.Sbr.Parse.TlimQsC
import Kraken.X64.Examples.Sbr.Parse.TlimQsD
import Kraken.X64.Examples.Sbr.Parse.TlimQsG1
import Kraken.X64.Examples.Sbr.Parse.TlimQsG2
import Kraken.X64.Examples.Sbr.Parse.TlimQsG3
import Kraken.X64.Examples.Sbr.Parse.TlimQsG4
import Kraken.X64.Examples.Sbr.Parse.TlimQsG5
import Kraken.X64.Examples.Sbr.Parse.TlimQsE
import Kraken.X64.Examples.Sbr.Parse.TlimQsF
import Kraken.X64.Examples.Sbr.Parse.TlimQsH1
import Kraken.X64.Examples.Sbr.Parse.TlimQsH2
import Kraken.X64.Examples.Sbr.Parse.TlimQsH3
import Kraken.X64.Examples.Sbr.Parse.TlimGlue

/-!
# `sbr_make_f_tablelim`: the procedure

`ProcSpec.of_cfg_post` over the block table (`TlimBase.lean`), the entry glue `pre_glue` and the
exit glue `post_glue` (`TlimGlue.lean`). Blocks not proved are explicit hypotheses of `spec`.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.Tlim

/-- The labels of the text, in order. -/
abbrev labelList : List Label := ["sbr_make_f_tablelim",
  "sbr_make_f_tablelim.L3f22",
  "sbr_make_f_tablelim.L3f31",
  "sbr_make_f_tablelim.L3f3a",
  "sbr_make_f_tablelim.L3f59",
  "sbr_make_f_tablelim.L3f65",
  "sbr_make_f_tablelim.L3f77",
  "sbr_make_f_tablelim.L3f89",
  "sbr_make_f_tablelim.L3f9b",
  "sbr_make_f_tablelim.L3fad",
  "sbr_make_f_tablelim.L3fbf",
  "sbr_make_f_tablelim.L3fcc",
  "sbr_make_f_tablelim.L3ff5",
  "sbr_make_f_tablelim.L4000",
  "sbr_make_f_tablelim.L400a",
  "sbr_make_f_tablelim.L4020",
  "sbr_make_f_tablelim.L4026",
  "sbr_make_f_tablelim.L403f",
  "sbr_make_f_tablelim.L4060",
  "sbr_make_f_tablelim.L4068",
  "sbr_make_f_tablelim.L4090",
  "sbr_make_f_tablelim.L40c3",
  "sbr_make_f_tablelim.L40c9",
  "sbr_make_f_tablelim.L40e0",
  "sbr_make_f_tablelim.L40ec",
  "sbr_make_f_tablelim.L40f0",
  "sbr_make_f_tablelim.L40f7",
  "sbr_make_f_tablelim.L4105",
  "sbr_make_f_tablelim.L4110",
  "sbr_make_f_tablelim.L4120",
  "sbr_make_f_tablelim.L4130",
  "sbr_make_f_tablelim.L4150",
  "sbr_make_f_tablelim.L4164",
  "sbr_make_f_tablelim.L4169",
  "sbr_make_f_tablelim.L4170",
  "sbr_make_f_tablelim.L4190",
  "sbr_make_f_tablelim.L4194",
  "sbr_make_f_tablelim.L4199",
  "sbr_make_f_tablelim.L41b0",
  "sbr_make_f_tablelim.L41b4",
  "sbr_make_f_tablelim.L41ca",
  "sbr_make_f_tablelim.L41d3",
  "sbr_make_f_tablelim.L41e0",
  "sbr_make_f_tablelim.L41f7",
  "sbr_make_f_tablelim.L4200",
  "sbr_make_f_tablelim.L4211",
  "sbr_make_f_tablelim.L421b",
  "sbr_make_f_tablelim.L4250",
  "sbr_make_f_tablelim.L425a",
  "sbr_make_f_tablelim.L4280",
  "sbr_make_f_tablelim.L429d",
  "sbr_make_f_tablelim.L42b6",
  "sbr_make_f_tablelim.L42bc",
  "sbr_make_f_tablelim.L42d0",
  "sbr_make_f_tablelim.L42eb",
  "sbr_make_f_tablelim.L42fa",
  "sbr_make_f_tablelim.L4312",
  "sbr_make_f_tablelim.L4317",
  "sbr_make_f_tablelim.L4323",
  "sbr_make_f_tablelim.L4330",
  "sbr_make_f_tablelim.L4338",
  "sbr_make_f_tablelim.L4340",
  "sbr_make_f_tablelim.L4342",
  "sbr_make_f_tablelim.L4350",
  "sbr_make_f_tablelim.L435b",
  "sbr_make_f_tablelim.L4363",
  "sbr_make_f_tablelim.L4370",
  "sbr_make_f_tablelim.L4385",
  "sbr_make_f_tablelim.L438a",
  "sbr_make_f_tablelim.L4398",
  "sbr_make_f_tablelim.L43a4",
  "sbr_make_f_tablelim.L43bd",
  "sbr_make_f_tablelim.done",
  "sbr_make_f_tablelim.L43cd",
  "sbr_make_f_tablelim.L43d2",
  "sbr_make_f_tablelim.L43d7",
  "sbr_make_f_tablelim.L43dc",
  "sbr_make_f_tablelim.L43e1",
  "sbr_make_f_tablelim.L43e6",
  "sbr_make_f_tablelim.L43eb",
  "sbr_make_f_tablelim.L43f0"]

theorem labels_body : Program.labels body = labelList := by decide

theorem body_wf : Program.WF body := by decide

variable [CodeEnv]

/-- The procedure from all block obligations. -/
theorem spec_of (hpl : Program.PlacedIn body) (k : Nat) (_hk : k ≤ 2 ^ 32)
    (hB : ∀ x ra t₀ l, l ∈ labelList → BlockOb k x ra t₀ l) : TlimSpec k := by
  refine Kraken.Executable.ProcSpec.of_cfg_post_pre (p := body)
    (fun x ra t₀ => table k x ra t₀)
    (fun x ra t₀ s => Post' k x ra t₀ s) var (hblocks := ?_) (hpre := ?_) (hpost := ?_)
    (hwf := body_wf)
  · intro x ra t₀ _ l blk h
    have hs : (Program.blockAt body l).isSome = true := by rw [h]; rfl
    rw [Program.isSome_blockAt, ← Program.labels_eq_view, List.contains_iff_mem,
      labels_body] at hs
    exact hB x ra t₀ l hs blk h
  · rintro x ra t ⟨hc, hC⟩
    obtain ⟨stk, pb, hs, hp, hm⟩ := pre_glue hc
    exact ⟨rfl, hC, stk, pb, ⟨hC.2.2.2.2.2.1, hs, hp⟩, hm⟩
  · intro x ra t₀ s hp h
    exact post_glue hp.1 h

/-- `sbr_make_f_tablelim` meets `TlimSpec k`, with `memcpy` as `MemcpyValSpec k`. -/
theorem spec (hpl : Program.PlacedIn body) (k : Nat) (hk : k ≤ 2 ^ 32)
    (hMc : MemcpyValSpec k) :
    TlimSpec k := by
  refine spec_of hpl k hk fun x ra t₀ l hl => ?_
  simp only [labelList, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl

  · exact blk_entry k hk hMc x ra t₀
  · exact blk_L3f22 k hk hMc x ra t₀
  · exact blk_L3f31 k hk hMc x ra t₀
  · exact blk_L3f3a k hk hMc x ra t₀
  · exact blk_L3f59 k hk hMc x ra t₀
  · exact blk_L3f65 k hk hMc x ra t₀
  · exact blk_L3f77 k hk hMc x ra t₀
  · exact blk_L3f89 k hk hMc x ra t₀
  · exact blk_L3f9b k hk hMc x ra t₀
  · exact blk_L3fad k hk hMc x ra t₀
  · exact blk_L3fbf k hk hMc x ra t₀
  · exact blk_L3fcc k hk hMc x ra t₀
  · exact blk_L3ff5 k hk hMc x ra t₀
  · exact blk_L4000 k hk hMc x ra t₀
  · exact blk_L400a k hk hMc x ra t₀
  · exact blk_L4020 k hk hMc x ra t₀
  · exact blk_L4026 k hk hMc x ra t₀
  · exact blk_L403f k hk hMc x ra t₀
  · exact blk_L4060 k hk hMc x ra t₀
  · exact blk_L4068 k hk hMc x ra t₀
  · exact blk_L4090 k hk hMc x ra t₀
  · exact blk_L40c3 k hk hMc x ra t₀
  · exact blk_L40c9 k hk hMc x ra t₀
  · exact blk_L40e0 k hk hMc x ra t₀
  · exact blk_L40ec k hk hMc x ra t₀
  · exact blk_L40f0 k hk hMc x ra t₀
  · exact blk_L40f7 k hk hMc x ra t₀
  · exact blk_L4105 k hk hMc x ra t₀
  · exact blk_L4110 k hk hMc x ra t₀
  · exact blk_L4120 k hk hMc x ra t₀
  · exact blk_L4130 k hk hMc x ra t₀
  · exact blk_L4150 k hk hMc x ra t₀
  · exact blk_L4164 k hk hMc x ra t₀
  · exact blk_L4169 k hk hMc x ra t₀
  · exact blk_L4170 k hk hMc x ra t₀
  · exact blk_L4190 k hk hMc x ra t₀
  · exact blk_L4194 k hk hMc x ra t₀
  · exact blk_L4199 k hk hMc x ra t₀
  · exact blk_L41b0 k hk hMc x ra t₀
  · exact blk_L41b4 k hk hMc x ra t₀
  · exact blk_L41ca k hk hMc x ra t₀
  · exact blk_L41d3 k hk hMc x ra t₀
  · exact blk_L41e0 k hk hMc x ra t₀
  · exact blk_L41f7 k hk hMc x ra t₀
  · exact blk_L4200 k hk hMc x ra t₀
  · exact blk_L4211 k hk hMc x ra t₀
  · exact blk_L421b k hk hMc x ra t₀
  · exact blk_L4250 k hk hMc x ra t₀
  · exact blk_L425a k hk hMc x ra t₀
  · exact blk_L4280 k hk hMc x ra t₀
  · exact blk_L429d k hk hMc x ra t₀
  · exact blk_L42b6 k hk hMc x ra t₀
  · exact blk_L42bc k hk hMc x ra t₀
  · exact blk_L42d0 k hk hMc x ra t₀
  · exact blk_L42eb k hk hMc x ra t₀
  · exact blk_L42fa k hk hMc x ra t₀
  · exact blk_L4312 k hk hMc x ra t₀
  · exact blk_L4317 k hk hMc x ra t₀
  · exact blk_L4323 k hk hMc x ra t₀
  · exact blk_L4330 k hk hMc x ra t₀
  · exact blk_L4338 k hk hMc x ra t₀
  · exact blk_L4340 k hk hMc x ra t₀
  · exact blk_L4342 k hk hMc x ra t₀
  · exact blk_L4350 k hk hMc x ra t₀
  · exact blk_L435b k hk hMc x ra t₀
  · exact blk_L4363 k hk hMc x ra t₀
  · exact blk_L4370 k hk hMc x ra t₀
  · exact blk_L4385 k hk hMc x ra t₀
  · exact blk_L438a k hk hMc x ra t₀
  · exact blk_L4398 k hk hMc x ra t₀
  · exact blk_L43a4 k hk hMc x ra t₀
  · exact blk_L43bd k hk hMc x ra t₀
  · exact blk_done k hk hMc x ra t₀
  · exact blk_L43cd k hk hMc x ra t₀
  · exact blk_L43d2 k hk hMc x ra t₀
  · exact blk_L43d7 k hk hMc x ra t₀
  · exact blk_L43dc k hk hMc x ra t₀
  · exact blk_L43e1 k hk hMc x ra t₀
  · exact blk_L43e6 k hk hMc x ra t₀
  · exact blk_L43eb k hk hMc x ra t₀
  · exact blk_L43f0 k hk hMc x ra t₀

end Kraken.Examples.Sbr.Tlim
