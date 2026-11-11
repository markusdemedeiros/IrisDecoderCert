import Kraken.Rules.CfgList

/-!
# Control-flow obligations of texts with hundreds of labels

`cfg_view`, `by decide` on `Program.WF` and a `match` on label strings scale to
a few dozen labels. For a text of several hundred blocks, state the text as
its list of blocks, each body a separate definition:
`body = blocks.flatMap Program.blockCells`. Then

* `Program.view_flatMap` gives the view of the text as that list, with no
  reduction of the bodies (only their label-freeness, checked once);
* `Program.blockIdx_of_getElem?` and `Program.isSome_blockAt_of_getElem?` answer
  the label questions of a jump exit from the label's position in the list of
  labels (one literal index per label, no string comparisons against the
  whole list);
* `Program.LTable` is a table indexed by position: the entry of label `l` is
  the entry at the position of `l` in the list of labels, so a block reads and
  establishes the entry at a literal label by the index alone
  (`Program.LTable.elim`, `Program.LTable.intro`), uniqueness coming from the
  labels being distinct.

Label uniqueness (`Program.WF`) is best shown on natural-number keys of the labels
(`List.pairwise_map` with a key such as the bytes read as a number) by `decide +kernel`:
deciding `Nodup` of the strings themselves exhausts memory at a few hundred labels.

Measured on a text of 434 blocks (2783 instructions): the dispatch over the block list
(`Program.forall_blockAt` and one `Program.AllBlocks.cons` per block) elaborates in
about 2 s, where `cfg_view` with a case split over the labels did not finish in 15
minutes; the per-label lemmas and the key-based uniqueness proof take about a minute.
-/

namespace Kraken

/-- A label-free prefix passes through the view to the entry segment. -/
theorem Program.view_append_free : ∀ (b q : Program), (∀ d ∈ b, d.isLabel = false) →
    Program.view (b ++ q) = (b ++ (Program.view q).1, (Program.view q).2)
  | [], _, _ => rfl
  | d :: b, q, h => by
    have ih := Program.view_append_free b q (fun d' hd' => h d' (List.mem_cons_of_mem d hd'))
    cases d with
    | label l => exact absurd (h _ List.mem_cons_self) (by simp [Directive.isLabel])
    | instr i => simp only [List.cons_append, Program.view, ih]
    | byteArray a => simp only [List.cons_append, Program.view, ih]

/-- The view of a text glued from label-free blocks is that list of blocks. -/
theorem Program.view_flatMap : ∀ (bs : List (Label × Program)),
    (∀ lb ∈ bs, ∀ d ∈ lb.2, d.isLabel = false) →
    Program.view (bs.flatMap Program.blockCells) = ([], bs)
  | [], _ => rfl
  | (l, b) :: bs, h => by
    have ih := Program.view_flatMap bs (fun lb hlb => h lb (List.mem_cons_of_mem _ hlb))
    have hb := Program.view_append_free b (bs.flatMap Program.blockCells) (h _ List.mem_cons_self)
    rw [ih] at hb
    simp only [List.flatMap_cons, Program.blockCells, List.cons_append, Program.view, hb,
      List.append_nil]

theorem Program.idxOf_of_getElem? {α} [BEq α] [LawfulBEq α] : ∀ {xs : List α} {a : α},
    xs.Nodup → ∀ {i : Nat}, xs[i]? = some a → xs.idxOf a = i
  | [], _, _, _, h => by simp at h
  | x :: xs, a, hnd, i, h => by
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp
    | succ j =>
      simp only [List.getElem?_cons_succ] at h
      have hmem : a ∈ xs := List.mem_of_getElem? h
      have hxa : (x == a) = false := by
        have : x ≠ a := fun heq => (List.nodup_cons.mp hnd).1 (heq ▸ hmem)
        simpa using this
      simp only [List.idxOf_cons, hxa, Bool.false_eq_true, ite_false]
      rw [Program.idxOf_of_getElem? (List.nodup_cons.mp hnd).2 h]

/-- The position of a label's block, from its position in the labels. -/
theorem Program.blockIdx_of_getElem? {p : Program} (hwf : Program.WF p) {i : Nat} {l : Label}
    (h : (Program.labels p)[i]? = some l) : Program.blockIdx p l = i :=
  Program.idxOf_of_getElem? hwf.nodup h

/-- A label in the labels has a block. -/
theorem Program.isSome_blockAt_of_getElem? {p : Program} {i : Nat} {l : Label}
    (h : (Program.labels p)[i]? = some l) : (Program.blockAt p l).isSome = true := by
  rw [Program.isSome_blockAt, ← Program.labels_eq_view, List.contains_iff_mem]
  exact List.mem_of_getElem? h

/-- The table indexed by position: the entry of `l` is `ents[i]` for `labs[i] = l`. -/
def Program.LTable {σ : Type} (labs : List Label) (ents : List (σ → Prop)) (l : Label)
    (s : σ) : Prop :=
  ∃ (i : Nat) (e : σ → Prop), labs[i]? = some l ∧ ents[i]? = some e ∧ e s

theorem Program.LTable.intro {σ : Type} {labs : List Label} {ents : List (σ → Prop)}
    {i : Nat} {l : Label} {e : σ → Prop} {s : σ}
    (hl : labs[i]? = some l) (he : ents[i]? = some e) (h : e s) :
    Program.LTable labs ents l s :=
  ⟨i, e, hl, he, h⟩

theorem Program.LTable.elim {σ : Type} {labs : List Label} {ents : List (σ → Prop)}
    (hnd : labs.Nodup) {i : Nat} {l : Label} {e : σ → Prop} {s : σ}
    (hl : labs[i]? = some l) (he : ents[i]? = some e) (h : Program.LTable labs ents l s) :
    e s := by
  obtain ⟨j, e', hj, he', h'⟩ := h
  have hij : j = i := by
    rw [← Program.idxOf_of_getElem? hnd hj, Program.idxOf_of_getElem? hnd hl]
  subst hij
  rw [he] at he'
  cases he'
  exact h'

theorem Program.LTable.iff {σ : Type} {labs : List Label} {ents : List (σ → Prop)}
    (hnd : labs.Nodup) {i : Nat} {l : Label} {e : σ → Prop} {s : σ}
    (hl : labs[i]? = some l) (he : ents[i]? = some e) :
    Program.LTable labs ents l s ↔ e s :=
  ⟨Program.LTable.elim hnd hl he, Program.LTable.intro hl he⟩

end Kraken
