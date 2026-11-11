import Kraken.X64.Examples.Sbr.Parse.DtdfLoop
import Kraken.X64.Examples.Sbr.Parse.DtdfBlk2

/-!
# `read_sbr_dtdf`: the procedure

`DtdfSpec k`: from `DtdfPre` (the footprint `DtdfF` at the entry index, the reader's bounds,
`bs_num_env ≤ 8`, `bs_num_noise ≤ 2`) the routine returns with `DtdfPost`: the same footprint,
the reader index still `≤ size_in_bits_plus8`. Assembled from the 31 block theorems with
`ProcSpec.of_cfg_post`.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply

namespace Kraken.Examples.Sbr.Dtdf

variable [CodeEnv]

abbrev DtdfSpec (k : Nat) : Prop :=
  cenv.ProcSpec (entry "read_sbr_dtdf") (DtdfPre k) (DtdfPost k)

/-- The block obligation at `l` for the block `blk` (`BlockOb` is `∀ blk, Ob … l blk`). -/
abbrev Ob (k : Nat) (x : DArgs) (ra : Int64) (t₀ : MachineData) (l : Label)
    (blk : Program.Block) : Prop :=
  Program.blockAt body l = some blk → ∀ n : Nat,
    ⦃ fun s => table k x ra t₀ l s ∧ var l s = n ⦄ blk.body
    ⦃ (match blk.next with
       | some l' => fun _ s => table k x ra t₀ l' s ∧ var l' s ≤ n
       | none => fun _ _ => False);
      fun a s => Table.ofLabels (fun l' s => (Program.blockAt body l').isSome
          ∧ table k x ra t₀ l' s ∧ Program.EdgeLt body var l n l' s) a s
        ∨ (a = ra ∧ Post' k x ra t₀ s) ⦄

theorem allBlocks (k : Nat) (x : DArgs) (ra : Int64) (t₀ : MachineData) :
    Program.AllBlocks (Ob k x ra t₀) (Program.view body).2 :=
  .cons (blk_entry k x ra t₀ _) <| .cons (blk_L5185 k x ra t₀ _) <|
  .cons (blk_L51a2 k x ra t₀ _) <| .cons (blk_L51bf k x ra t₀ _) <|
  .cons (blk_L51d0 k x ra t₀ _) <| .cons (blk_L5202 k x ra t₀ _) <|
  .cons (blk_L5243 k x ra t₀ _) <| .cons (blk_L5272 k x ra t₀ _) <|
  .cons (blk_L528f k x ra t₀ _) <| .cons (blk_L52a0 k x ra t₀ _) <|
  .cons (blk_L52d2 k x ra t₀ _) <| .cons (blk_L5317 k x ra t₀ _) <|
  .cons (blk_done k x ra t₀ _) <| .cons (blk_L5347 k x ra t₀ _) <|
  .cons (blk_L5360 k x ra t₀ _) <| .cons (blk_L5392 k x ra t₀ _) <|
  .cons (blk_L53d3 k x ra t₀ _) <| .cons (blk_L5402 k x ra t₀ _) <|
  .cons (blk_L5430 k x ra t₀ _) <| .cons (blk_L5462 k x ra t₀ _) <|
  .cons (blk_L54a2 k x ra t₀ _) <| .cons (blk_L54b0 k x ra t₀ _) <|
  .cons (blk_L54e2 k x ra t₀ _) <| .cons (blk_L5523 k x ra t₀ _) <|
  .cons (blk_L5552 k x ra t₀ _) <| .cons (blk_L5564 k x ra t₀ _) <|
  .cons (blk_L556b k x ra t₀ _) <| .cons (blk_L5580 k x ra t₀ _) <|
  .cons (blk_L55b2 k x ra t₀ _) <| .cons (blk_L55ed k x ra t₀ _) <|
  .cons (blk_L55f3 k x ra t₀ _) <| .cons (blk_L5622 k x ra t₀ _) <| .nil _

/-- `read_sbr_dtdf` meets `DtdfSpec` (memory safety and the `ParseModel` row: only the reader
index changes). -/
theorem dtdf_spec (hpl : Program.PlacedIn body) (k : Nat) : DtdfSpec k := by
  refine Kraken.Executable.ProcSpec.of_cfg_post (p := body) (table k) (Post' k) var
    (hblocks := ?_) (hpre := ?_) (hpost := ?_)
  · intro x ra t₀ l blk hblk
    exact Program.forall_blockAt (allBlocks k x ra t₀) l blk hblk hblk
  · rintro x ra t ⟨hcall, hC⟩
    exact ⟨rfl, hC, hcall⟩
  · intro x ra t₀ s h; exact h

end Kraken.Examples.Sbr.Dtdf
