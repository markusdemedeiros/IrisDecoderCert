import Kraken.MachineWP
import Kraken.Rules.CfgTable

/-!
# Placement of the texts of a concatenated image

An image glued from texts that each start at a label (`Program.view t).1 = []`) has as its
block view the concatenation of the texts' block views (`Program.view_flatten`). When the
image is placed and its labels are distinct, each of its texts is placed
(`Program.PlacedIn.of_flatten`): a block of the text is a block of the image, with the same
body and, where the text has one, the same successor. Nothing here evaluates a text.
-/

namespace Kraken

/-- The view of a concatenation whose right part starts at a label. -/
theorem Program.view_append_of_entry_nil : ∀ (a b : Program), (Program.view b).1 = [] →
    Program.view (a ++ b) = ((Program.view a).1, (Program.view a).2 ++ (Program.view b).2)
  | [], b, h => Prod.ext (by simpa [Program.view] using h) (by simp [Program.view])
  | d :: a, b, h => by
    have ih := Program.view_append_of_entry_nil a b h
    cases d with
    | label l => simp only [List.cons_append, Program.view, ih]
    | instr i => simp only [List.cons_append, Program.view, ih]
    | byteArray x => simp only [List.cons_append, Program.view, ih]

/-- The view of texts glued together, each starting at a label. -/
theorem Program.view_flatten : ∀ (ts : List Program), (∀ t ∈ ts, (Program.view t).1 = []) →
    Program.view ts.flatten = ([], ts.flatMap fun t => (Program.view t).2)
  | [], _ => rfl
  | t :: ts, h => by
    have ih := Program.view_flatten ts (fun t' ht' => h t' (List.mem_cons_of_mem _ ht'))
    rw [List.flatten_cons, Program.view_append_of_entry_nil _ _ (by rw [ih]), ih,
      h t List.mem_cons_self, List.flatMap_cons]

/-- The labels of texts glued together. -/
theorem Program.labels_flatten : ∀ (ts : List Program),
    Program.labels ts.flatten = ts.flatMap Program.labels
  | [] => rfl
  | t :: ts => by
    rw [List.flatten_cons, Program.labels_append, Program.labels_flatten ts, List.flatMap_cons]

/-- A text whose block view is a run of a placed text's block view is placed. -/
theorem Program.PlacedIn.of_view [CodeEnv] {p q : Program} (hq : Program.PlacedIn q)
    (hnd : (Program.labels q).Nodup) (pre post : List (Label × Program))
    (hv : (Program.view q).2 = pre ++ ((Program.view p).2 ++ post)) : Program.PlacedIn p := by
  have hnd' : ((Program.view q).2.map (·.1)).Nodup := by rwa [← Program.labels_view]
  have key : ∀ i lb, (Program.view p).2[i]? = some lb →
      (Program.view q).2[pre.length + i]? = some lb := by
    intro i lb h
    have hi : i < (Program.view p).2.length := (List.getElem?_eq_some_iff.mp h).1
    rw [hv, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
      List.getElem?_append_left hi, h]
  have hb : ∀ l blk, Program.blockAt p l = some blk →
      ∃ blk', Program.blockAt q l = some blk' ∧ blk'.body = blk.body
        ∧ ∀ l', blk.next = some l' → blk'.next = some l' := by
    intro l blk h
    obtain ⟨-, i, hi, hn⟩ := Program.blockAtAux_spec h
    refine ⟨_, Program.blockAtAux_of_getElem hnd' (key i _ hi), rfl, ?_⟩
    intro l' hl'
    rw [hn] at hl'
    obtain ⟨lb, hlb, rfl⟩ := Option.map_eq_some_iff.mp hl'
    show ((Program.view q).2[pre.length + i + 1]?).map (·.1) = _
    rw [Nat.add_assoc, key _ _ hlb]
    rfl
  refine ⟨fun l blk h => ?_, fun l blk l' h hn => ?_⟩
  · obtain ⟨blk', h', hbd, -⟩ := hb l blk h
    rw [← hbd]
    exact hq.block l blk' h'
  · obtain ⟨blk', h', hbd, hn'⟩ := hb l blk h
    rw [← hbd]
    exact hq.next l blk' l' h' (hn' l' hn)

/-- Each text of a placed image of texts (each starting at a label, all labels distinct)
is placed. -/
theorem Program.PlacedIn.of_flatten [CodeEnv] {ts : List Program} {p : Program}
    (hq : Program.PlacedIn ts.flatten) (hnd : (Program.labels ts.flatten).Nodup)
    (hts : ∀ t ∈ ts, (Program.view t).1 = []) (hp : p ∈ ts) : Program.PlacedIn p := by
  obtain ⟨s, u, rfl⟩ := List.append_of_mem hp
  refine Program.PlacedIn.of_view hq hnd (s.flatMap fun t => (Program.view t).2)
    (u.flatMap fun t => (Program.view t).2) ?_
  rw [Program.view_flatten _ hts]
  simp only [List.flatMap_append, List.flatMap_cons]

end Kraken
