import Kraken.X64.Examples.Sbr.Parse.GridSpec
import Kraken.X64.Examples.Sbr.Placement

/-!
# Satisfiability of `read_sbr_grid`'s layout hypotheses

`Grid.spec` assumes the placement of its text (`Program.PlacedIn Grid.body`) and, in
`GridC`, the layout fact `JtC`: each entry of the switch's jump table (the 32-bit offset of a
target from the table) sign-extends back to that offset. Both are facts about the ambient
code. Here one ambient code satisfies both: the image `img` is the table's cell (at the label
`read_sbr_grid_jt`) followed by the text of `read_sbr_grid`, laid out by `jLayout` (labels take
no bytes, every other cell 8192, from `0x400000`), as in `Linked.lean`.
-/

open Kraken Kraken.X64.Parser Std.WP MachineWP Kraken.SysV Mem

namespace Kraken.Examples.Sbr.GridJtWit

/-- The jump table's cell. -/
def jtT : Program := [.label "read_sbr_grid_jt", .byteArray ByteArray.empty]

def texts : List Program := [jtT, Grid.body]

/-- The image. -/
def img : Program := texts.flatten

theorem texts_entry : ∀ t ∈ texts, (Program.view t).1 = [] := by
  intro t ht
  simp only [texts, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · rfl
  · decide +kernel

theorem img_wf : Program.WF img := ⟨by decide +kernel⟩

/-- A program at `0x400000`: labels take no bytes, every other cell 8192. -/
@[reducible] def layOf (p : Program) : _root_.Layout where
  start := 0x400000
  size i := if (p[i]?.map Directive.isLabel).getD false then 0 else 8192

/-- The image's layout. -/
@[reducible] def jLayout : _root_.Layout := layOf img

attribute [local instance] jLayout

/-- No cell of the image is an `.align`. -/
def noAlign : Directive → Bool
  | .instr (.regular _ _ (.nopalign _ _)) => false
  | _ => true

theorem img_noAlign : img.all noAlign = true := by decide +kernel

theorem img_length : img.length < 2 ^ 40 := by decide +kernel

theorem sum_snd_le : ∀ (l : List (Directive × Nat)) (c : Nat), (∀ x ∈ l, x.2 ≤ c) →
    (l.map (·.2)).sum ≤ c * l.length
  | [], _, _ => by simp
  | x :: l, c, h => by
    have ih := sum_snd_le l c (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have hx := h x List.mem_cons_self
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_succ]
    omega

theorem jLayout_valid : Executable.ValidLayout (jLayout img) where
  label_size i l z h := by
    simp only [Kraken.Layout.apply, List.getElem?_mapIdx, Option.map_eq_some_iff,
      Prod.mk.injEq] at h
    obtain ⟨d, hd, rfl, rfl⟩ := h
    show (if (img[i]?.map Directive.isLabel).getD false then 0 else 8192) = 0
    simp [hd, Directive.isLabel]
  instr_size i d z h hnl := by
    simp only [Kraken.Layout.apply, List.getElem?_mapIdx, Option.map_eq_some_iff,
      Prod.mk.injEq] at h
    obtain ⟨d', hd, rfl, rfl⟩ := h
    have : d'.isLabel = false := by
      cases d' <;> simp_all [Directive.isLabel]
    show 0 < (if (img[i]?.map Directive.isLabel).getD false then 0 else 8192)
    simp [hd, this]
  no_wrap := by
    have hle : ∀ x ∈ (jLayout img).2, x.2 ≤ 8192 := by
      intro x hx
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hx
      simp only [Kraken.Layout.apply, List.getElem?_mapIdx, Option.map_eq_some_iff] at hi
      obtain ⟨d, -, rfl⟩ := hi
      show (if (img[i]?.map Directive.isLabel).getD false then 0 else 8192) ≤ 8192
      split <;> omega
    have h := sum_snd_le _ 8192 hle
    have hlen : (jLayout img).2.length = img.length := by simp [Kraken.Layout.apply]
    have := img_length
    omega
  align_addr i aw w n pad z h hn := by
    simp only [Kraken.Layout.apply, List.getElem?_mapIdx, Option.map_eq_some_iff,
      Prod.mk.injEq] at h
    obtain ⟨d, hd, hdeq, -⟩ := h
    subst hdeq
    have := List.all_eq_true.mp img_noAlign _ (List.mem_of_getElem? hd)
    simp [noAlign] at this

attribute [local instance] jLayout_valid

/-- The ambient code: the laid-out image. -/
@[instance_reducible] def jCE : CodeEnv := ⟨jLayout img⟩

attribute [local instance] jCE

theorem img_placed : Program.Placed img "read_sbr_grid_jt" :=
  Program.placed_of_layout img_wf rfl (by decide +kernel)

theorem placed_body : Program.PlacedIn Grid.body :=
  Program.PlacedIn.of_flatten img_placed.toPlacedIn img_wf.nodup texts_entry
    (by simp [texts])

/-- `d` is not the label `l`. -/
def notLab (l : Label) : Directive × Nat → Bool
  | (.label l', _) => l' != l
  | _ => true

/-- A cell's size in `jLayout`. -/
def sz (d : Directive) : Nat := if d.isLabel then 0 else 8192

/-- Sizes given by the index are sizes given by the cell. -/
theorem mapIdx_eq_map (p : Program) (f : Nat → Nat) (g : Directive → Nat)
    (h : ∀ i (hi : i < p.length), f i = g p[i]) :
    p.mapIdx (fun i d => (d, f i)) = p.map (fun d => (d, g d)) := by
  apply List.ext_getElem
  · simp only [List.length_mapIdx, List.length_map]
  · intro i h1 h2
    simp only [List.length_mapIdx] at h1
    simp only [List.getElem_mapIdx, List.getElem_map, h i h1]

/-- The laid-out image, cell by cell (a form whose prefixes evaluate in linear time). -/
theorem layout_snd (p : Program) : (layOf p p).2 = p.map fun d => (d, sz d) :=
  mapIdx_eq_map p _ sz fun i hi => by
    show (if (p[i]?.map Directive.isLabel).getD false then 0 else 8192) = sz p[i]
    simp only [List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some, sz]

theorem jLayout_snd : (jLayout img).2 = img.map fun d => (d, sz d) := layout_snd img

/-- A label's address, at its position `n` in the laid-out image. -/
theorem jlab (l : Label) (n : Nat)
    (hn : (img.map fun d => (d, sz d))[n]? = some (.label l, 0))
    (hf : ((img.map fun d => (d, sz d)).take n).all (notLab l) = true) :
    lab l = ((0x400000 : Int64)
      + Int64.ofNat ((((img.map fun d => (d, sz d)).take n).map (·.2)).sum)).toBitVec := by
  have h1 : (jLayout img).2[n]? = some (.label l, 0) := by rw [jLayout_snd]; exact hn
  have h2 : ∀ dz ∈ (jLayout img).2.take n, dz.1 ≠ Directive.label l := by
    rw [jLayout_snd]
    intro dz hdz heq
    have := List.all_eq_true.mp hf dz hdz
    obtain ⟨d, z⟩ := dz
    simp only at heq
    subst heq
    simp [notLab] at this
  unfold lab
  rw [Executable.label_addrOf _ l n h1 h2]
  show ((0x400000 : Int64) + Int64.ofNat ((((jLayout img).2.take n).map (·.2)).sum)).toBitVec = _
  rw [jLayout_snd]

theorem lab_jt : lab "read_sbr_grid_jt" = 0x400000#64 :=
  (jlab _ 0 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem lab_L448b : lab "read_sbr_grid.L448b" = 0x44e000#64 :=
  (jlab _ 48 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem lab_L4773 : lab "read_sbr_grid.L4773" = 0x5f6000#64 :=
  (jlab _ 281 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem lab_L44e3 : lab "read_sbr_grid.L44e3" = 0x480000#64 :=
  (jlab _ 74 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem lab_L46a2 : lab "read_sbr_grid.L46a2" = 0x57c000#64 :=
  (jlab _ 215 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem jtC : Grid.JtC := by
  unfold Grid.JtC Grid.jtOff Grid.JT
  rw [lab_jt, lab_L448b, lab_L4773, lab_L44e3, lab_L46a2]
  decide +kernel

/-- One ambient code places `read_sbr_grid`'s text and satisfies `JtC`. -/
theorem grid_layout_sat : ∃ C : CodeEnv, @Program.PlacedIn C Grid.body ∧ @Grid.JtC C :=
  ⟨jCE, placed_body, jtC⟩

end Kraken.Examples.Sbr.GridJtWit
