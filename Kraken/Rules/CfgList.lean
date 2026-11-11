import Kraken.Blocks

/-!
# Splitting the control-flow obligation of a long text block by block

`cfg_cases` computes the block map of a text as a chain of `if`s and splits
it with `split`; on a text of a few hundred directives and a few dozen labels
the `simp` behind `split` runs out of steps, and splitting by hand is slow
(each case carries the whole remaining chain). `Program.forall_blockAt`
states the obligation over the view's list of blocks instead: one conjunct
per block, consumed with `Program.AllBlocks.cons`, each goal naming its block
literally.

For one theorem per block (each with its own heartbeat budget, elaborated in
parallel), state the obligation at a literal label `l` as
`∀ blk, Program.blockAt p l = some blk → …` and open it with `cfg_block`: it
computes the block at `l` and the label questions of the jump exits.
-/

namespace Kraken

/-- `P` holds at every block of the view list, with the next label. -/
def Program.AllBlocks (P : Label → Program.Block → Prop) : List (Label × Program) → Prop
  | [] => True
  | (l, b) :: bs => P l ⟨l, b, bs.head?.map (·.1)⟩ ∧ Program.AllBlocks P bs

theorem Program.AllBlocks.nil (P : Label → Program.Block → Prop) : Program.AllBlocks P [] :=
  trivial

theorem Program.AllBlocks.cons {P : Label → Program.Block → Prop} {l : Label} {b : Program}
    {bs : List (Label × Program)} (h : P l ⟨l, b, bs.head?.map (·.1)⟩)
    (t : Program.AllBlocks P bs) : Program.AllBlocks P ((l, b) :: bs) :=
  ⟨h, t⟩

theorem Program.AllBlocks.blockAtAux {P : Label → Program.Block → Prop} :
    ∀ {bs : List (Label × Program)}, Program.AllBlocks P bs →
      ∀ l blk, Program.blockAtAux bs l = some blk → P l blk
  | [], _, _, _, h => by cases h
  | (l', b) :: bs, ⟨h1, h2⟩, l, blk, h => by
    simp only [Program.blockAtAux] at h
    by_cases hc : l' = l
    · rw [if_pos hc] at h
      cases h
      subst hc
      exact h1
    · rw [if_neg hc] at h
      exact Program.AllBlocks.blockAtAux h2 l blk h

/-- The block obligation from one obligation per block of the view. -/
theorem Program.forall_blockAt {p : Program} {P : Label → Program.Block → Prop}
    (h : Program.AllBlocks P (Program.view p).2) :
    ∀ l blk, Program.blockAt p l = some blk → P l blk :=
  Program.AllBlocks.blockAtAux h

end Kraken

/-- Open a block obligation `∀ blk, Program.blockAt p l = some blk → …` at a
literal label `l` of a closed text `p`: substitute the block at `l`, then
evaluate the jump exits' label questions (`Program.EdgeLt`,
`Program.isSome_blockAt`) on the text's list of labels. -/
macro "cfg_block" : tactic => `(tactic| (
  intro blk hblk
  cfg_view hblk as hview
  have hlabels := congrArg (List.map (·.1)) hview
  simp only [List.map_cons, List.map_nil] at hlabels
  rw [Program.blockAt, hview] at hblk
  clear hview
  simp only [Program.blockAtAux, List.head?_cons, List.head?_nil, Option.map_some,
    Option.map_none, String.reduceEq, ↓reduceIte, Option.some.injEq] at hblk
  subst hblk
  simp only [Program.EdgeLt, Program.isSome_blockAt, Program.blockIdx_eq_view, hlabels]
  clear hlabels))
