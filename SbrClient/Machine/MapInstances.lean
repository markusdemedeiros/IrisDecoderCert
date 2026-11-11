import Std.Data.ExtHashMap
import Std.Data.HashMap.Lemmas
import Iris.Std.PartialMap

/-! Iris's finite-map interface for Kraken's extensional hash maps. The
enumeration chooses a finite representative; only its extensional laws are
used. This adds no axiom beyond Lean's standard classical choice. -/
noncomputable section
open Std

namespace SbrClient

variable {K : Type} [BEq K] [Hashable K] [LawfulBEq K]

private def merged {V : Type} (op : K → V → V → V)
    (a b : ExtHashMap K V) : ExtHashMap K V :=
  b.union (a.map fun k v => (b[k]?).elim v (op k v))

instance : Iris.Std.PartialMap (fun V => ExtHashMap K V) K where
  get? m k := m[k]?
  insert m k v := m.insert k v
  delete m k := m.erase k
  empty := ∅
  bindAlter f m := m.filterMap f
  merge := merged

instance : Iris.Std.LawfulPartialMap (fun V => ExtHashMap K V) K where
  get?_empty := by simp [Iris.Std.get?]
  get?_insert_eq := by
    intro V m k k' v heq
    subst k'
    simp [Iris.Std.get?, Iris.Std.insert]
  get?_insert_ne := by
    intro V m k k' v h
    simp [Iris.Std.get?, Iris.Std.insert, ExtHashMap.getElem?_insert, h, Ne.symm h]
  get?_delete_eq := by simp [Iris.Std.get?, Iris.Std.delete]
  get?_delete_ne := by
    intro V m k k' h
    simp [Iris.Std.get?, Iris.Std.delete, ExtHashMap.getElem?_erase, h, Ne.symm h]
  get?_bindAlter := by simp [Iris.Std.get?, Iris.Std.bindAlter]
  get?_merge := by
    intro V op a b k
    simp only [Iris.Std.get?, Iris.Std.merge, merged, ExtHashMap.union_eq,
      ExtHashMap.getElem?_union, ExtHashMap.getElem?_map]
    cases a[k]? <;> cases b[k]? <;> rfl
  equiv_iff_eq := by
    intro V a b
    rw [ExtHashMap.ext_getElem?_iff]
    rfl

private theorem list_exists {V : Type} (m : ExtHashMap K V) :
    ∃ l : List (K × V), (l.map Prod.fst).Nodup ∧
      ∀ k v, (k, v) ∈ l ↔ m[k]? = some v := by
  obtain ⟨m⟩ := m
  induction m using ExtDHashMap.inductionOn with
  | mk m =>
    let h : HashMap K V := ⟨m⟩
    refine ⟨h.toList, ?_, ?_⟩
    · apply List.pairwise_map.mpr
      exact h.distinct_keys_toList.imp (fun hab heq => by simpa [heq] using hab)
    · intro k v
      exact h.mem_toList_iff_getElem?_eq_some

private def enumeration {V : Type} (m : ExtHashMap K V) : List (K × V) :=
  Classical.choose (list_exists m)

private theorem enumeration_spec {V : Type} (m : ExtHashMap K V) :
    ((enumeration m).map Prod.fst).Nodup ∧
      ∀ k v, (k, v) ∈ enumeration m ↔ m[k]? = some v :=
  Classical.choose_spec (list_exists m)

instance : Iris.Std.FiniteMap (fun V => ExtHashMap K V) K where
  toList := enumeration

instance : Iris.Std.LawfulFiniteMap (fun V => ExtHashMap K V) K where
  toList_empty := by
    intro V
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro ⟨k, v⟩ h
    have := (enumeration_spec (∅ : ExtHashMap K _)).2 k v |>.mp h
    simpa using this
  toList_noDupKeys := (enumeration_spec _).1
  toList_get := (enumeration_spec _).2 _ _

end SbrClient
