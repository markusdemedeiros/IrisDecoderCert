/-!
# `AV_QSORT` (`libavutil/qsort.h`): the invariants, at the level of indices

`AV_QSORT(p, num, type, cmp)` is a quicksort with an explicit stack `void *stack[64][2]` of
pending intervals. These definitions describe a run on an array of `N` elements whose values
are `A : Nat → α` (`α` any type with a total preorder `QOrd`: `Nat` for unsigned views of
small values, `Int` for `int16_t` read signed), independent of the element width and of how
the array and the stack sit in memory. Pending intervals are index pairs `[lo, hi1)`
(half-open: `hi1 = end + 1` in elements).

* `Perm N A A0`: `A` is obtained from `A0` by exchanges of positions below `N`. It gives the
  provenance (`Perm.prov`), the frame past `N` (`Perm.frame`), the value bounds
  (`Perm.bounds`) and, for `Int`, the sum (`Perm.sum`).
* `SortedExc N A P`: every pair of positions is in order unless both lie in one pending
  interval of `P`. With `P = []` the array is sorted.
* `QW N A A0 P` (index facts + `Perm`: all a caller needs that does not use sortedness) and
  `QI N A A0 P` (`SortedExc ∧ Disj ∧ QW`).
* `Depth N S`: the stack depth bound. `AV_QSORT` pushes the larger part and continues with the
  smaller, so the interval at stack index `j` has at most `N / 2 ^ j` elements; the code's
  `sp < 64` checks follow (`cur_len`, `depth_len`).
* `phi P`: the termination measure, `2 * size + 1` per pending interval: a partition step
  replaces an interval of `c` elements by two of `c - 1` in total, a drop removes one.
  `wBn w a b`: the same weight read off byte addresses (`start`, `end` pointers, element
  width `w`).

The step lemmas follow the code: `*_init` (the first push), `*_swap` (any `FFSWAP` inside the
current interval), `*_drop` (a finished interval: at most one element, two elements in order,
or the `checksort` scan reached `end`), `*_split` (after the partition, the pivot at `l`),
`*_comm2` (the pushed part and the current part in either order), `depth_*`, `phi_*`.
-/

namespace Kraken.Examples.Sbr.Parse.Qsort

set_option linter.unusedSectionVars false

/-! ## Orders -/

/-- A total preorder (`Nat`, `Int`). -/
class QOrd (α : Type) [LE α] : Prop where
  refl : ∀ a : α, a ≤ a
  trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c
  total : ∀ a b : α, a ≤ b ∨ b ≤ a

instance : QOrd Nat := ⟨Nat.le_refl, fun _ _ _ => Nat.le_trans, Nat.le_total⟩
instance : QOrd Int := ⟨Int.le_refl, fun _ _ _ => Int.le_trans, Int.le_total⟩

/-! ## Definitions -/

/-- A pending interval `[lo, hi1)` of indices. -/
abbrev Iv := Nat × Nat

def InIv (I : Iv) (q : Nat) : Prop := I.1 ≤ q ∧ q < I.2

section Defs
variable {α : Type}

/-- `A` with positions `q1`, `q2` exchanged. -/
def swap (A : Nat → α) (q1 q2 : Nat) : Nat → α :=
  fun q => if q = q1 then A q2 else if q = q2 then A q1 else A q

/-- `A` with position `q` set to `v`. -/
def upd (A : Nat → α) (q : Nat) (v : α) : Nat → α := fun r => if r = q then v else A r

/-- The arrays reachable from `A0` by exchanges below `N`. -/
inductive PermOf (N : Nat) (A0 : Nat → α) : (Nat → α) → Prop
  | refl : PermOf N A0 A0
  | swap {A : Nat → α} : PermOf N A0 A → ∀ i j, i < N → j < N → PermOf N A0 (swap A i j)

/-- `A` is a rearrangement of `A0` (exchanges of positions below `N`). -/
def Perm (N : Nat) (A A0 : Nat → α) : Prop := PermOf N A0 A

def SortedExc [LE α] (N : Nat) (A : Nat → α) (P : List Iv) : Prop :=
  ∀ i j, i < j → j < N → (∀ I ∈ P, ¬ (InIv I i ∧ InIv I j)) → A i ≤ A j

def Disj (P : List Iv) : Prop := P.Pairwise (fun I J => I.2 ≤ J.1 ∨ J.2 ≤ I.1)

def Within (N : Nat) (P : List Iv) : Prop := ∀ I ∈ P, I.1 ≤ I.2 ∧ I.2 ≤ N

def Prov (N : Nat) (A A0 : Nat → α) : Prop := ∀ q, q < N → ∃ t, t < N ∧ A q = A0 t

def Frame (N : Nat) (A A0 : Nat → α) : Prop := ∀ q, N ≤ q → A q = A0 q

/-- The index facts and the rearrangement (no order facts). -/
def QW (N : Nat) (A A0 : Nat → α) (P : List Iv) : Prop := Within N P ∧ Perm N A A0

/-- The invariant with the pending intervals `P` (the stack, and the current interval). -/
def QI [LE α] (N : Nat) (A A0 : Nat → α) (P : List Iv) : Prop :=
  SortedExc N A P ∧ Disj P ∧ QW N A A0 P

end Defs

def Depth (N : Nat) (S : List Iv) : Prop :=
  (∀ j (h : j < S.length), (S[j].2 - S[j].1) * 2 ^ j ≤ N) ∧ 2 ^ S.length ≤ 2 * N

def wt (I : Iv) : Nat := 2 * (I.2 - I.1) + 1

def phi (P : List Iv) : Nat := (P.map wt).sum

/-- The weight of an interval given by byte addresses `a = start`, `b = end` (inclusive) of
elements of `w` bytes. -/
def wBn (w a b : Nat) : Nat := if a ≤ b then b - a + w + 1 else 1

/-- The sum of the first `n` elements. -/
def sumTo (A : Nat → Int) : Nat → Int
  | 0 => 0
  | n + 1 => sumTo A n + A n

/-! ## `swap`, `upd` -/

section Swap
variable {α : Type}

theorem swap_eq (A : Nat → α) (i j q : Nat) :
    swap A i j q = if q = i then A j else if q = j then A i else A q := rfl

/-- The two stores of an exchange. -/
theorem upd_upd_swap (A : Nat → α) (i j : Nat) (q : Nat) :
    upd (upd A j (A i)) i (A j) q = swap A i j q := by
  unfold upd swap; by_cases h1 : q = i <;> by_cases h2 : q = j <;> simp_all

theorem swap_self (A : Nat → α) (i q : Nat) : swap A i i q = A q := by
  unfold swap; by_cases h : q = i <;> simp_all

end Swap

/-! ## `Perm` -/

section PermL
variable {α : Type} {N : Nat}

theorem perm_refl (A : Nat → α) : Perm N A A := PermOf.refl

theorem Perm.swap' {A A0 : Nat → α} (h : Perm N A A0) {i j : Nat} (hi : i < N) (hj : j < N) :
    Perm N (swap A i j) A0 := PermOf.swap h i j hi hj

theorem Perm.congr {A B A0 : Nat → α} (h : Perm N A A0) (e : ∀ q, B q = A q) : Perm N B A0 := by
  have : B = A := funext e
  subst this; exact h

theorem Perm.prov {A A0 : Nat → α} (h : Perm N A A0) : Prov N A A0 := by
  unfold Perm at h
  induction h with
  | refl => intro q hq; exact ⟨q, hq, rfl⟩
  | swap _ i j hi hj ih =>
    intro q hq
    unfold Qsort.swap
    by_cases h1 : q = i
    · simp only [h1, ↓reduceIte]; exact ih j hj
    · by_cases h2 : q = j
      · rw [if_neg h1, if_pos h2]; exact ih i hi
      · simp only [h1, h2, ↓reduceIte]; exact ih q hq

theorem Perm.frame {A A0 : Nat → α} (h : Perm N A A0) : Frame N A A0 := by
  unfold Perm at h
  induction h with
  | refl => intro q _; rfl
  | swap _ i j hi hj ih =>
    intro q hq
    unfold Qsort.swap
    simp only [show q ≠ i by omega, show q ≠ j by omega, ↓reduceIte]; exact ih q hq

theorem Perm.bounds [LE α] {A A0 : Nat → α} (h : Perm N A A0) {P : α → Prop}
    (h0 : ∀ q, q < N → P (A0 q)) : ∀ q, q < N → P (A q) := by
  intro q hq
  obtain ⟨t, ht, e⟩ := h.prov q hq
  rw [e]; exact h0 t ht

theorem sumTo_upd (A : Nat → Int) (p : Nat) (v : Int) :
    ∀ n, sumTo (upd A p v) n = sumTo A n + (if p < n then v - A p else 0)
  | 0 => by simp [sumTo]
  | n + 1 => by
    simp only [sumTo, sumTo_upd A p v n, upd]
    by_cases h : n = p
    · subst h; simp; omega
    · by_cases h2 : p < n
      · simp [h, h2, show p < n + 1 by omega]; omega
      · simp [h, h2, show ¬ p < n + 1 by omega]

theorem sumTo_swap (A : Nat → Int) {i j n : Nat} (hi : i < n) (hj : j < n) :
    sumTo (swap A i j) n = sumTo A n := by
  have e : swap A i j = upd (upd A j (A i)) i (A j) := funext fun q => (upd_upd_swap A i j q).symm
  rw [e, sumTo_upd, sumTo_upd]
  simp only [hi, hj, ↓reduceIte, upd]
  by_cases h : i = j
  · subst h; simp
  · simp [h]; omega

theorem Perm.sum {A A0 : Nat → Int} (h : Perm N A A0) : sumTo A N = sumTo A0 N := by
  unfold Perm at h
  induction h with
  | refl => rfl
  | swap _ i j hi hj ih => rw [sumTo_swap _ hi hj, ih]

end PermL

/-! ## The invariant -/

section QIL
variable {α : Type} [LE α] [QOrd α] {N : Nat} {A A0 : Nat → α}

theorem qw_init (A0 : Nat → α) (N : Nat) : QW N A0 A0 [(0, N)] :=
  ⟨fun I hI => by simp at hI; subst hI; simp, perm_refl A0⟩

theorem qi_init (A0 : Nat → α) (N : Nat) : QI N A0 A0 [(0, N)] := by
  refine ⟨?_, by simp [Disj], qw_init A0 N⟩
  intro i j hij hj hP
  exact absurd ⟨⟨Nat.zero_le _, show i < N by omega⟩, ⟨Nat.zero_le _, hj⟩⟩ (hP (0, N) (by simp))

/-- The current interval (the last one) is inside the array. -/
theorem qw_cur {S : List Iv} {I : Iv} (h : QW N A A0 (S ++ [I])) : I.1 ≤ I.2 ∧ I.2 ≤ N :=
  h.1 I (by simp)

theorem qw_swap {S : List Iv} {I : Iv} (h : QW N A A0 (S ++ [I])) {i j : Nat} (hi : InIv I i)
    (hj : InIv I j) : QW N (swap A i j) A0 (S ++ [I]) := by
  have := qw_cur h
  exact ⟨h.1, h.2.swap' (by unfold InIv at hi; omega) (by unfold InIv at hj; omega)⟩

theorem qw_drop {S : List Iv} {I : Iv} (h : QW N A A0 (S ++ [I])) : QW N A A0 S :=
  ⟨fun J hJ => h.1 J (by simp [hJ]), h.2⟩

theorem mem2 {K I J : Iv} {S : List Iv} : K ∈ S ++ [I, J] ↔ K ∈ S ∨ K = I ∨ K = J := by simp

theorem qw_comm2 {S : List Iv} {I J : Iv} (h : QW N A A0 (S ++ [I, J])) : QW N A A0 (S ++ [J, I]) :=
  ⟨fun K hK => h.1 K (by rw [mem2] at hK ⊢; rcases hK with h | h | h <;> simp [h]), h.2⟩

theorem qw_split {S : List Iv} {lo hi1 l rt : Nat} (h : QW N A A0 (S ++ [(lo, hi1)]))
    (h1 : lo ≤ rt + 1) (h2 : rt < l) (h3 : l + 1 ≤ hi1) :
    QW N A A0 (S ++ [(lo, rt + 1), (l + 1, hi1)]) := by
  have hc := qw_cur h
  refine ⟨fun K hK => ?_, h.2⟩
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hK
  rcases hK with hK | rfl | rfl
  · exact h.1 K (by simp [hK])
  · simp only at hc ⊢; omega
  · simp only at hc ⊢; omega

theorem qi_qw {P : List Iv} (h : QI N A A0 P) : QW N A A0 P := h.2.2

theorem qi_cur {S : List Iv} {I : Iv} (h : QI N A A0 (S ++ [I])) : I.1 ≤ I.2 ∧ I.2 ≤ N :=
  qw_cur h.2.2

/-- Chains of neighbours give all pairs. -/
theorem chain_le {lo e : Nat} (hc : ∀ q, lo ≤ q → q < e → A q ≤ A (q + 1)) :
    ∀ i j, lo ≤ i → i ≤ j → j ≤ e → A i ≤ A j := by
  intro i j hi hij hj
  induction j with
  | zero => obtain rfl : i = 0 := by omega
            exact QOrd.refl _
  | succ j ih =>
    by_cases e1 : i = j + 1
    · subst e1; exact QOrd.refl _
    · exact QOrd.trans _ _ _ (ih (by omega) (by omega)) (hc j (by omega) (by omega))

theorem qi_swap {S : List Iv} {I : Iv} (h : QI N A A0 (S ++ [I])) {i j : Nat} (hi : InIv I i)
    (hj : InIv I j) : QI N (swap A i j) A0 (S ++ [I]) := by
  obtain ⟨hs, hd, hw⟩ := h
  refine ⟨?_, hd, qw_swap hw hi hj⟩
  have hdI : ∀ J ∈ S, J.2 ≤ I.1 ∨ I.2 ≤ J.1 := by
    intro J hJ
    unfold Disj at hd
    have := (List.pairwise_append.mp hd).2.2 J hJ I (by simp)
    exact this
  -- a position moved by the exchange lies in `I`
  have mv : ∀ q, (swap A i j q = A q) ∨ (InIv I q ∧ ∃ q', InIv I q' ∧ swap A i j q = A q') := by
    intro q
    unfold swap
    by_cases e1 : q = i
    · subst e1; exact Or.inr ⟨hi, j, hj, by simp⟩
    · by_cases e2 : q = j
      · subst e2; exact Or.inr ⟨hj, i, hi, by simp [e1]⟩
      · exact Or.inl (by simp [e1, e2])
  intro a b hab hb hP
  have hIn : ¬ (InIv I a ∧ InIv I b) := hP I (by simp)
  -- `I` is not split by anything else: a pair with one side in `I` and the other outside
  have outside : ∀ x y, x < y → y < N → (InIv I x ∨ InIv I y) → ¬ (InIv I x ∧ InIv I y) →
      ∀ J ∈ S ++ [I], ¬ (InIv J x ∧ InIv J y) := by
    intro x y hxy hy hxy1 hxy2 J hJ ⟨hJx, hJy⟩
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hJ
    rcases hJ with hJ | rfl
    · have := hdI J hJ; unfold InIv at hJx hJy hxy1; omega
    · exact hxy2 ⟨hJx, hJy⟩
  rcases mv a with ea | ⟨haI, a', ha'I, ea⟩ <;> rcases mv b with eb | ⟨hbI, b', hb'I, eb⟩
  · rw [ea, eb]; exact hs a b hab hb hP
  · -- `a` outside `I` (else both in `I`), `b` moved inside `I`
    have haO : ¬ InIv I a := fun h => hIn ⟨h, hbI⟩
    rw [ea, eb]
    have hab' : a < b' := by unfold InIv at haO hbI hb'I; omega
    have hc := qw_cur hw
    exact hs a b' hab' (by unfold InIv at hb'I; omega)
      (outside a b' hab' (by unfold InIv at hb'I; omega) (Or.inr hb'I) (fun h => haO h.1))
  · have hbO : ¬ InIv I b := fun h => hIn ⟨haI, h⟩
    rw [ea, eb]
    have hab' : a' < b := by unfold InIv at hbO haI ha'I; omega
    exact hs a' b hab' hb (outside a' b hab' hb (Or.inl ha'I) (fun h => hbO h.2))
  · exact absurd ⟨haI, hbI⟩ hIn

/-- A finished interval: its elements in order (at most one element, two in order, or the
`checksort` scan). -/
theorem qi_drop {S : List Iv} {I : Iv} (h : QI N A A0 (S ++ [I]))
    (hc : ∀ q, I.1 ≤ q → q + 1 < I.2 → A q ≤ A (q + 1)) : QI N A A0 S := by
  obtain ⟨hs, hd, hw⟩ := h
  refine ⟨?_, (List.pairwise_append.mp hd).1, qw_drop hw⟩
  intro a b hab hb hP
  by_cases hI : InIv I a ∧ InIv I b
  · unfold InIv at hI
    exact chain_le (lo := I.1) (e := I.2 - 1) (fun q h1 h2 => hc q h1 (by omega)) a b
      (by omega) (by omega) (by omega)
  · refine hs a b hab hb fun J hJ => ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hJ
    rcases hJ with hJ | rfl
    · exact hP J hJ
    · exact hI

theorem qi_drop_small {S : List Iv} {I : Iv} (h : QI N A A0 (S ++ [I])) (h1 : I.2 ≤ I.1 + 1) :
    QI N A A0 S := qi_drop h fun q h2 h3 => absurd h3 (by omega)

theorem qi_comm2 {S : List Iv} {I J : Iv} (h : QI N A A0 (S ++ [I, J])) :
    QI N A A0 (S ++ [J, I]) := by
  obtain ⟨hs, hd, hw⟩ := h
  refine ⟨fun a b hab hb hP => hs a b hab hb fun K hK => hP K (by rw [mem2] at hK ⊢; rcases hK with h | h | h <;> simp [h]), ?_,
    qw_comm2 hw⟩
  unfold Disj at hd ⊢
  rw [List.pairwise_append] at hd ⊢
  obtain ⟨d1, d2, d3⟩ := hd
  refine ⟨d1, ?_, fun K hK L hL => ?_⟩
  · refine List.Pairwise.cons ?_ (List.Pairwise.cons (by simp) List.Pairwise.nil)
    intro K hK; simp at hK; subst hK
    cases d2 with
    | cons h _ => have := h J (by simp); omega
  · exact d3 K hK L (by simp at hL ⊢; rcases hL with h | h <;> simp [h])

/-- After the partition: the pivot at `l`, everything in `[lo, l]` at most `A l`, everything
in `(rt, e]` (`e = hi1 - 1`) at least `A l`, `rt < l ≤ rt + 2`. The parts `[lo, rt]` and
`[l + 1, e]` stay pending. -/
theorem qi_split {S : List Iv} {lo hi1 l rt : Nat} (h : QI N A A0 (S ++ [(lo, hi1)]))
    (h1 : lo + 1 ≤ l) (h2 : l ≤ rt + 2) (h3 : rt < l) (h4 : l + 1 ≤ hi1)
    (hL : ∀ q, lo ≤ q → q ≤ l → A q ≤ A l) (hR : ∀ q, rt < q → q + 1 ≤ hi1 → A l ≤ A q) :
    QI N A A0 (S ++ [(lo, rt + 1), (l + 1, hi1)]) := by
  obtain ⟨hs, hd, hw⟩ := h
  have hc := qw_cur hw
  simp only at hc
  have hdI : ∀ J ∈ S, J.2 ≤ lo ∨ hi1 ≤ J.1 := fun J hJ =>
    (List.pairwise_append.mp hd).2.2 J hJ (lo, hi1) (by simp)
  refine ⟨?_, ?_, qw_split hw (by omega) h3 h4⟩
  · intro a b hab hb hP
    have hPS : ∀ J ∈ S, ¬ (InIv J a ∧ InIv J b) := fun J hJ => hP J (by simp [hJ])
    by_cases hI : InIv (lo, hi1) a ∧ InIv (lo, hi1) b
    · unfold InIv at hI; simp only at hI
      have hnl : ¬ (a ≤ rt ∧ b ≤ rt) := fun h => hP (lo, rt + 1) (by simp) ⟨⟨by simp; omega,
        by simp; omega⟩, ⟨by simp; omega, by simp; omega⟩⟩
      have hnr : ¬ (l + 1 ≤ a ∧ l + 1 ≤ b) := fun h => hP (l + 1, hi1) (by simp)
        ⟨⟨by simp; omega, by simp; omega⟩, ⟨by simp; omega, by simp; omega⟩⟩
      -- `a ≤ l` and `rt < b`: through the pivot
      exact QOrd.trans _ _ _ (hL a (by omega) (by omega)) (hR b (by omega) (by omega))
    · refine hs a b hab hb fun J hJ => ?_
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hJ
      rcases hJ with hJ | rfl
      · exact hPS J hJ
      · exact hI
  · unfold Disj at hd ⊢
    rw [List.pairwise_append] at hd ⊢
    obtain ⟨d1, -, d3⟩ := hd
    refine ⟨d1, ?_, fun K hK L hL => ?_⟩
    · refine List.Pairwise.cons ?_ (List.Pairwise.cons (by simp) List.Pairwise.nil)
      intro K hK; simp at hK; subst hK; simp only; omega
    · have := hdI K hK
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hL
      rcases hL with rfl | rfl <;> simp only <;> omega

/-- The end: sorted. -/
theorem qi_sorted (h : QI N A A0 []) : ∀ i j, i < j → j < N → A i ≤ A j :=
  fun i j hij hj => h.1 i j hij hj (by simp)

theorem qi_sorted_succ (h : QI N A A0 []) : ∀ q, q + 1 < N → A q ≤ A (q + 1) :=
  fun q hq => qi_sorted h q (q + 1) (by omega) hq

end QIL

/-! ## The stack depth -/

theorem depth_init {N : Nat} (h : 1 ≤ N) : Depth N [(0, N)] := by
  refine ⟨fun j hj => ?_, by simp; omega⟩
  simp at hj; subst hj; simp

theorem depth_pop {N : Nat} {S : List Iv} {I : Iv} (h : Depth N (S ++ [I])) :
    Depth N S ∧ (I.2 - I.1) * 2 ^ S.length ≤ N := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨⟨fun j hj => ?_, ?_⟩, ?_⟩
  · have := h1 j (by simp; omega)
    rwa [List.getElem_append_left hj] at this
  · simp at h2
    have := Nat.pow_le_pow_right (show 0 < 2 by omega) (Nat.le_succ S.length)
    omega
  · have := h1 S.length (by simp)
    simpa using this

theorem depth_push {N : Nat} {S : List Iv} {lo hi1 : Nat} {B : Iv} (hd : Depth N S)
    (hc : (hi1 - lo) * 2 ^ S.length ≤ N) (h2 : 2 ≤ hi1 - lo) (hB : B.2 - B.1 ≤ hi1 - lo)
    {c : Nat} (hs : 2 * c ≤ hi1 - lo) :
    Depth N (S ++ [B]) ∧ c * 2 ^ (S ++ [B]).length ≤ N := by
  obtain ⟨d1, d2⟩ := hd
  have hp : 0 < 2 ^ S.length := Nat.two_pow_pos _
  refine ⟨⟨fun j hj => ?_, ?_⟩, ?_⟩
  · simp only [List.length_append, List.length_cons, List.length_nil] at hj
    by_cases e : j < S.length
    · rw [List.getElem_append_left e]; exact d1 j e
    · obtain rfl : j = S.length := by omega
      simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
        List.getElem_cons_zero]
      exact Nat.le_trans (Nat.mul_le_mul_right _ hB) hc
  · simp only [List.length_append, List.length_cons, List.length_nil, Nat.pow_succ]
    have := Nat.mul_le_mul_right (2 ^ S.length) h2
    rw [Nat.mul_comm] at this
    omega
  · simp only [List.length_append, List.length_cons, List.length_nil, Nat.pow_succ]
    calc c * (2 ^ S.length * 2) = 2 * c * 2 ^ S.length := by
          ac_rfl
      _ ≤ (hi1 - lo) * 2 ^ S.length := Nat.mul_le_mul_right _ hs
      _ ≤ N := hc

/-- The code's check before a push: with a current interval of at least 2 elements at depth
`n`, `2 ^ (n + 1) ≤ N`. -/
theorem cur_len {N n c m : Nat} (hc : c * 2 ^ n ≤ N) (h2 : 2 ≤ c) (hN : N < 2 ^ (m + 1)) :
    n < m := by
  have h : 2 ^ (n + 1) ≤ N := by
    rw [Nat.pow_succ, Nat.mul_comm]
    exact Nat.le_trans (Nat.mul_le_mul_right _ h2) hc
  have : 2 ^ (n + 1) < 2 ^ (m + 1) := by omega
  have := (Nat.pow_lt_pow_iff_right (by omega)).mp this
  omega

/-- The code's check after a pop: `sp ≤ m`. -/
theorem depth_len {N m : Nat} {S : List Iv} (hd : Depth N S) (hN : 2 * N < 2 ^ (m + 1)) :
    S.length ≤ m := by
  have : 2 ^ S.length < 2 ^ (m + 1) := by have := hd.2; omega
  have := (Nat.pow_lt_pow_iff_right (by omega)).mp this
  omega

/-! ## The measure -/

theorem phi_nil : phi [] = 0 := rfl

theorem phi_append (S T : List Iv) : phi (S ++ T) = phi S + phi T := by
  simp [phi, List.map_append, List.sum_append]

theorem phi_one (I : Iv) : phi [I] = wt I := by simp [phi]

theorem phi_pos_one (I : Iv) : 1 ≤ phi [I] := by rw [phi_one]; unfold wt; omega

theorem phi_split {lo hi1 l rt : Nat} (h1 : lo ≤ rt + 1) (h3 : rt < l) (h4 : l + 1 ≤ hi1) :
    phi [(lo, rt + 1), (l + 1, hi1)] < phi [(lo, hi1)] := by
  simp only [phi, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, wt]
  omega

theorem phi_split' {lo hi1 l rt : Nat} (h1 : lo ≤ rt + 1) (h3 : rt < l) (h4 : l + 1 ≤ hi1) :
    phi [(l + 1, hi1), (lo, rt + 1)] < phi [(lo, hi1)] := by
  simp only [phi, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, wt]
  omega

/-- The byte weight of `[p + w lo, p + w (hi1 - 1)]` is `wt (lo, hi1)` scaled by `w`. -/
theorem wBn_iv {w p lo hi1 : Nat} (hw : 1 ≤ w) (hp : w ≤ p + w * hi1) :
    wBn w (p + w * lo) (p + w * hi1 - w) = w * (hi1 - lo) + 1 := by
  unfold wBn
  by_cases h : lo < hi1
  · have e : w * hi1 = w * (hi1 - lo) + w * lo := by
      rw [← Nat.mul_add]; congr 1; omega
    have e2 : w * (hi1 - lo) ≥ w := Nat.le_mul_of_pos_right _ (by omega)
    rw [ite_cond_eq_true _ _ (eq_true (by omega))]; omega
  · have e : w * hi1 ≤ w * lo := Nat.mul_le_mul_left _ (by omega)
    rw [ite_cond_eq_false _ _ (eq_false (by omega)), show hi1 - lo = 0 by omega]; simp

end Kraken.Examples.Sbr.Parse.Qsort
