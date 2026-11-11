import Kraken.X64.Examples.Sbr.Parse.ResetIface

/-!
# `sbr_reset`: from `ParseModel`'s relations to `ResetOut`

`reset_spec` / `derived_spec` (ParseModel) give the table facts; these lemmas add the frame
facts `ResetOut` states (`R`, `sampleRate`, `avctx` kept) and fix the branch by the value of
`spectrum_params`.
-/

open Kraken Kraken.SysV Mem
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel

namespace Kraken.Examples.Sbr.Reset

/-- The fields `ResetOut` keeps besides `TFrame`. -/
abbrev Keeps (x y : Args) : Prop := y.R = x.R ∧ y.sampleRate = x.sampleRate ∧ y.avctx = x.avctx

theorem tablelim_keeps {lb : Nat} {x y : Args} (h : Tablelim lb x y) : Keeps x y := by
  cases h <;> exact ⟨rfl, rfl, rfl⟩

theorem patches_keeps {f : Nat → Nat} {sr : Int} {k0 kx1 m1 nm : Nat} {x y : Args} {b : Bool}
    (h : Patches f sr k0 kx1 m1 nm x y b) : Keeps x y := by
  cases h; exact ⟨rfl, rfl, rfl⟩

theorem derived_keeps {sr : Int} {lb nm xo : Nat} {f : Nat → Nat} {x y : Args} {b : Bool}
    (h : Derived sr lb nm xo f x y b) : Keeps x y := by
  cases h with
  | badTop _ => exact ⟨rfl, rfl, rfl⟩
  | badKx _ _ => exact ⟨rfl, rfl, rfl⟩
  | badNq _ _ _ _ => exact ⟨rfl, rfl, rfl⟩
  | badPatch _ _ _ _ _ hp =>
    obtain ⟨a1, a2, a3⟩ := patches_keeps hp
    exact ⟨a1, a2, a3⟩
  | ok _ _ _ _ _ hp ht =>
    obtain ⟨a1, a2, a3⟩ := patches_keeps hp
    obtain ⟨b1, b2, b3⟩ := tablelim_keeps ht
    exact ⟨b1.trans a1, b2.trans a2, b3.trans a3⟩

theorem reset_keeps {sp : Spec} {lb : Nat} {x x' : Args} (h : Reset sp lb x x') : Keeps x x' := by
  cases h with
  | badRate _ _ => exact ⟨rfl, rfl, rfl⟩
  | badMaster _ _ => exact ⟨rfl, rfl, rfl⟩
  | badDerived _ _ hd =>
    obtain ⟨a1, a2, a3⟩ := derived_keeps hd
    exact ⟨a1, a2, a3⟩
  | ok _ _ hd =>
    obtain ⟨a1, a2, a3⟩ := derived_keeps hd
    exact ⟨a1, a2, a3⟩

/-! ### The table lengths are kept -/

theorem prun_lens {f : Nat → Nat} {k0 kx1 nm top : Nat} {s r : PL} {b : Bool}
    (h : PRun f k0 kx1 nm top s r b) (hs : s.pn.length = 6 ∧ s.pst.length = 6) :
    r.pn.length = 6 ∧ r.pst.length = 6 := by
  induction h with
  | rep s _ => exact hs
  | many s j _ _ _ => exact hs
  | stop s j _ _ _ _ => exact ⟨mk_length _ _, mk_length _ _⟩
  | cont s j _ _ _ _ _ ih => exact ih ⟨mk_length _ _, mk_length _ _⟩

theorem patches_lens {f : Nat → Nat} {sr : Int} {k0 kx1 m1 nm : Nat} {x y : Args} {b : Bool}
    (h : Patches f sr k0 kx1 m1 nm x y b) (hl : RLens x) : RLens y := by
  obtain ⟨l1, l2, l3, l4, -, -⟩ := hl
  cases h with
  | run k _ hr =>
    obtain ⟨p1, p2⟩ := prun_lens hr ⟨mk_length _ _, mk_length _ _⟩
    exact ⟨l1, l2, l3, l4, p1, p2⟩

theorem tablelim_lens {lb : Nat} {x y : Args} (h : Tablelim lb x y) (hl : RLens x) : RLens y := by
  obtain ⟨l1, l2, l3, -, l5, l6⟩ := hl
  cases h with
  | zero _ => exact ⟨l1, l2, l3, (by simp), l5, l6⟩
  | pos _ _ _ _ => exact ⟨l1, l2, l3, (by simp), l5, l6⟩

/-- `RLens` ignores the channel values (`A`, `B` abstract: no unfolding of `clrNoise`). -/
theorem rlens_upd {z : Args} (A B : DV) (h : RLens z) : RLens { z with d0 := A, d1 := B } := h

theorem derived_lens {sr : Int} {lb nm xo : Nat} {f : Nat → Nat} {x y : Args} {b : Bool}
    (h : Derived sr lb nm xo f x y b) (hl : RLens x) : RLens y := by
  have h1 : RLens (derived1 x nm xo f) := by
    obtain ⟨l1, -, l3, l4, l5, l6⟩ := hl
    exact ⟨l1, by simp [derived1], l3, l4, l5, l6⟩
  have h2 : RLens (derived2 (derived1 x nm xo f) xo f) := by
    obtain ⟨-, l2, l3, l4, l5, l6⟩ := h1
    exact ⟨by simp [derived2], l2, l3, l4, l5, l6⟩
  have h3 : ∀ q, RLens (derived3 (derived2 (derived1 x nm xo f) xo f) q) := fun q => by
    obtain ⟨l1, l2, -, l4, l5, l6⟩ := h2
    exact ⟨l1, l2, by simp [derived3], l4, l5, l6⟩
  cases h with
  | badTop _ => exact h1
  | badKx _ _ => exact h1
  | badNq _ _ _ _ => exact h2
  | badPatch q _ _ _ _ hp => exact patches_lens hp (h3 q)
  | ok q _ _ _ _ hp ht => exact rlens_upd _ _ (tablelim_lens ht (patches_lens hp (h3 q)))

theorem reset_lens {sp : Spec} {lb : Nat} {x x' : Args} (h : Reset sp lb x x') (hl : RLens x) :
    RLens x' := by
  cases h with
  | badRate _ _ => exact hl
  | badMaster _ _ => exact hl
  | badDerived _ _ hd =>
    have := derived_lens hd hl
    exact this
  | ok _ _ hd =>
    have := derived_lens hd hl
    exact this

theorem resetC_lens {a : RArgs} {t : MachineData} [CodeEnv] (h : ResetCI a t) : RLens a.x :=
  ⟨h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.1⟩

theorem turnoff_turnoff (x : Args) : x.turnoff.turnoff = x.turnoff := rfl

/-- The failure exit: the turned-off values with `spectrum_params` all `0xff`, `usac = 0`. -/
theorem resetOut_turnoff {a : RArgs} {x : Args} (hs : Scal a.x) (hl : RLens a.x)
    (h : Reset (⟨u8 a.sp 0, u8 a.sp 2⟩ : Spec) a.lb.toNat a.x x.turnoff) :
    ResetOut a x.turnoff (List.replicate 6 0xff) 0 := by
  obtain ⟨k1, k2, k3⟩ := reset_keeps h
  obtain ⟨hsc, y, hy, hor⟩ := reset_spec h hs
  refine ⟨hsc, reset_lens h hl, ?_⟩
  rcases hor with e | ⟨e, -⟩
  · refine ⟨y, hy, ?_, ?_, ?_, Or.inl ⟨e, rfl, rfl⟩⟩
    · have : y.turnoff.R = a.x.R := e ▸ k1
      exact this
    · have : y.turnoff.sampleRate = a.x.sampleRate := e ▸ k2
      exact this
    · have : y.turnoff.avctx = a.x.avctx := e ▸ k3
      exact this
  · refine ⟨y, hy, e ▸ k1, e ▸ k2, e ▸ k3, Or.inl ⟨?_, rfl, rfl⟩⟩
    rw [← e]

/-- `spectrum_params` after `sbr_turnoff`'s two stores (`movw $0xffff, 4(%rbx)`,
`movl $-1, (%rbx)`). -/
theorem sp_ff {l : List UInt8} (h : l.length = 6) (b2 b4 : List UInt8)
    (h2 : b2 = [0xff, 0xff]) (h4 : b4 = [0xff, 0xff, 0xff, 0xff]) :
    Parse.wr (Parse.wr l 4 b2) 0 b4 = List.replicate 6 0xff := by
  subst h2 h4
  match l, h with
  | [_, _, _, _, _, _], _ => rfl

end Kraken.Examples.Sbr.Reset
