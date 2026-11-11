import Kraken.X64.Examples.Sbr.Parse.InvfBlk

/-!
# `read_sbr_invf`: the procedure

The block obligations of `InvfBlk` assembled by `ProcSpec.of_cfg_post`. The only hypothesis is
the placement of the text (`Program.PlacedIn body`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply

namespace Kraken.Examples.Sbr.Invf

variable [CodeEnv]

theorem spec (hpl : Program.PlacedIn body) : InvfSpec := by
  refine Kraken.Executable.ProcSpec.of_cfg_post (p := body) table Post' var
    (hblocks := ?_) (hpre := ?_) (hpost := ?_)
  · intro x ra t₀
    refine Program.forall_blockAt ?_
    exact
      (.cons (blk_entry x ra t₀ _ rfl)
      (.cons (blk_L564a x ra t₀ _ rfl)
      (.cons (blk_L5693 x ra t₀ _ rfl)
      (.cons (blk_L56d5 x ra t₀ _ rfl)
      (.cons (blk_L5713 x ra t₀ _ rfl)
      (.cons (blk_L5751 x ra t₀ _ rfl)
      (.cons (blk_L578f x ra t₀ _ rfl)
      (.cons (blk_done x ra t₀ _ rfl)
      (.cons (blk_L5790 x ra t₀ _ rfl)
      (.nil _))))))))))
  · rintro x ra t ⟨hcall, hc⟩
    refine ⟨rfl, hc, ?_⟩
    simp only [T, Rest, InvB, CallPre, IF] at hcall ⊢
    exact Mem.ac hcall
  · rintro x ra t₀ s ⟨vals, i, hi1, hi2, h1, h2, h3, hm⟩
    refine ⟨vals, i, hi1, hi2, h1, h2, h3, ?_⟩
    simp only [InvB, IF] at hm ⊢
    exact Mem.ac hm

end Kraken.Examples.Sbr.Invf
