import Kraken.X64.Examples.Sbr.Session
import Kraken.X64.Examples.Sbr.SessionSpec

/-!
# A source-level model of the SBR parser

A functional model of the effect of the SBR parser on the values `Args` (`ApplySpec.lean`),
transcribed from `libavcodec/aacsbr_template.c` (FFmpeg n8.1, cited `l.`) and
`aacps_common.c` (`PC`), with `aac/aacdec_usac.c` (`U`) for the USAC callers. It is a stepping
stone for the parser's proof: nothing imports it and nothing trusts it.
-/

open Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Session

namespace Kraken.Examples.Sbr.ParseModel

/-! ## Byte arrays -/

/-- The byte a C store of the `int` value `z` into a `uint8_t` leaves. -/
def u8i (z : Int) : UInt8 := UInt8.ofNat (z % 256).toNat

/-- The array of `k` bytes whose byte `j` is `f j`. -/
def mk (k : Nat) (f : Nat → UInt8) : List UInt8 := (List.range k).map f

/-- Byte `j` of the old array `bs` (the value a store leaves in place). -/
abbrev old (bs : List UInt8) (j : Nat) : UInt8 := bs.getD j 0

theorem u8_mk (k : Nat) (f : Nat → UInt8) (j : Nat) :
    u8 (mk k f) j = if j < k then (f j).toNat else 0 := by
  unfold u8 mk
  by_cases h : j < k
  · simp [h, List.getD_eq_getElem?_getD]
  · simp [h, List.getD_eq_getElem?_getD]

@[simp] theorem mk_length (k : Nat) (f : Nat → UInt8) : (mk k f).length = k := by simp [mk]

/-- `old bs j` read as a number is `u8 bs j`. -/
theorem old_toNat (bs : List UInt8) (j : Nat) : (old bs j).toNat = u8 bs j := rfl

/-! ## The grid: `read_sbr_grid` (l.638-783), `copy_sbr_grid` (l.785-800)

The bitstream values are inputs: each `get_bits(gb, k)` is a number `< 2 ^ k`, and a loop's
reads are a function `c : Nat → Nat` of the iteration. The loops that fill `t_env` are given by
their net effect (`rsum`): the stores are `uint8_t`, so a border is its `int` value mod 256
(`u8i`). -/

/-- `Σ_{i<k} (2 c_i + 2)`: the sum of the first `k` relative borders. -/
def rsum (c : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => rsum c k + (2 * c k + 2)

/-- The prologue (l.646-651): `bs_freq_res[0] = bs_freq_res[bs_num_env]` and
`t_env_num_env_old = t_env[bs_num_env]` (byte 9 of `te`), for the old `bs_num_env`. -/
def gridPro (v : DV) : DV :=
  { v with freqRes := mk 9 (fun j => if j = 0 then old v.freqRes v.nenv else old v.freqRes j),
           te := mk 10 (fun j => if j = 9 then old v.te v.nenv else old v.te j) }

/-- FIXFIX `t_env` (l.668-674): `t_env[0] = 0`, `t_env[n] = 16`, `t_env[i+1] = t_env[i] + s`
with `s = (16 + n/2) / n` for `i < n - 1`. -/
def fixfixTe (v : DV) (n : Nat) : List UInt8 :=
  mk 10 (fun j => if j = 9 then old v.te 9 else if j < n then UInt8.ofNat (j * ((16 + n / 2) / n))
    else if j = n then 16 else old v.te j)

/-- FIXVAR `t_env` (l.684-689): `t_env[0] = 0`, `t_env[n] = abs_bord_trail`, and
`t_env[n-1-i] = t_env[n-i] - 2 c_i - 2` for `i < n - 1`. -/
def fixvarTe (v : DV) (n abt : Nat) (c : Nat → Nat) : List UInt8 :=
  mk 10 (fun j => if j = 9 then old v.te 9 else if j = 0 then 0
    else if j < n then u8i ((abt : Int) - rsum c (n - j)) else if j = n then UInt8.ofNat abt
    else old v.te j)

/-- VARFIX `t_env` (l.697-703): `t_env[0] = a0`, `t_env[n] = 16`,
`t_env[i+1] = t_env[i] + 2 c_i + 2` for `i < n - 1`. -/
def varfixTe (v : DV) (n a0 : Nat) (c : Nat → Nat) : List UInt8 :=
  mk 10 (fun j => if j = 9 then old v.te 9 else if j < n then UInt8.ofNat (a0 + rsum c j)
    else if j = n then 16 else old v.te j)

/-- VARVAR `t_env` (l.710, 724-730): `t_env[0] = a0`, `t_env[n] = abs_bord_trail`, the leading
borders `1..lead` from `t_env[0]` up, the trailing ones `n-1` down to `lead+1` from `t_env[n]`. -/
def varvarTe (v : DV) (n lead a0 abt : Nat) (c d : Nat → Nat) : List UInt8 :=
  mk 10 (fun j => if j = 9 then old v.te 9 else if j = 0 then UInt8.ofNat a0
    else if j ≤ lead then UInt8.ofNat (a0 + rsum c j)
    else if j < n then u8i ((abt : Int) - rsum d (n - j)) else if j = n then UInt8.ofNat abt
    else old v.te j)

/-- `bs_freq_res[1..n]` from the bits `r` (`r j` stored at `j`). -/
def frSet (v : DV) (n : Nat) (r : Nat → Nat) : List UInt8 :=
  mk 9 (fun j => if 1 ≤ j ∧ j ≤ n then UInt8.ofNat (r j) else old v.freqRes j)

/-- The `switch (bs_frame_class)` of `read_sbr_grid` (l.653-736) from the values `v` after the
prologue: the values it leaves and, unless it returned `-1`, the frame class and `bs_pointer`.
`usac` is `sbr->usac` (l.656).

`bs_pointer` is any value: it is read with `get_bits(gb, ceil_log2[bs_num_env])`, and for
`bs_num_env = 1` the width is `0`, for which the compiled code reads a 32-bit window rather than
`0`. A negative `bs_pointer` stops the decoder at `av_assert0(bs_pointer >= 0)` (before the check
of l.740-745); that run does not return, so it has no outcome here (see `Grid`), and `p : Nat`
covers the values that pass the assertion. -/
inductive GridSw (usac : Bool) (v : DV) : DV → Option (Nat × Nat) → Prop
  /-- FIXFIX with too many envelopes: return before any store (l.655-661). -/
  | fixfixBad (e : Nat) (he : e < 4) (hbad : (if usac then 8 else 5) < 2 ^ e) : GridSw usac v v none
  /-- FIXFIX (l.654-679): one `bs_freq_res` bit `r` for all envelopes. -/
  | fixfix (e r : Nat) (he : e < 4) (hr : r < 2) (hok : 2 ^ e ≤ (if usac then 8 else 5)) :
      GridSw usac v
        { v with nenv := 2 ^ e, te := fixfixTe v (2 ^ e), freqRes := frSet v (2 ^ e) (fun _ => r) }
        (some (0, 0))
  /-- FIXVAR (l.680-695): the `i`-th `bs_freq_res` bit goes to `n - i`. -/
  | fixvar (a b p : Nat) (c r : Nat → Nat) (ha : a < 4) (hb : b < 4) (hc : ∀ i, c i < 4)
      (hr : ∀ i, r i < 2) :
      GridSw usac v
        { v with
          nenv := b + 1
          te := fixvarTe v (b + 1) (16 + a) c
          freqRes := frSet v (b + 1) (fun j => r (b + 1 - j)) } (some (1, p))
  /-- VARFIX (l.696-708). -/
  | varfix (a0 b p : Nat) (c r : Nat → Nat) (ha : a0 < 4) (hb : b < 4) (hc : ∀ i, c i < 4)
      (hr : ∀ i, r i < 2) :
      GridSw usac v
        { v with
          nenv := b + 1
          te := varfixTe v (b + 1) a0 c
          freqRes := frSet v (b + 1) (fun j => r (j - 1)) } (some (2, p))
  /-- VARVAR with too many envelopes: `t_env[0]` is already stored (l.710, 716-721). -/
  | varvarBad (a0 a lead trail : Nat) (ha0 : a0 < 4) (ha : a < 4) (hl : lead < 4)
      (ht : trail < 4) (hbad : 5 < lead + trail + 1) :
      GridSw usac v { v with te := mk 10 (fun j => if j = 0 then UInt8.ofNat a0 else old v.te j) }
        none
  /-- VARVAR (l.709-735). -/
  | varvar (a0 a lead trail p : Nat) (c d r : Nat → Nat) (ha0 : a0 < 4) (ha : a < 4)
      (hl : lead < 4) (ht : trail < 4) (hok : lead + trail + 1 ≤ 5) (hc : ∀ i, c i < 4)
      (hd : ∀ i, d i < 4) (hr : ∀ i, r i < 2) :
      GridSw usac v
        { v with
          nenv := lead + trail + 1
          te := varvarTe v (lead + trail + 1) lead a0 (16 + a) c d
          freqRes := frSet v (lead + trail + 1) (fun j => r (j - 1)) } (some (3, p))

/-- The noise border index (l.760-771). -/
def idxOf (cls n p : Nat) : Nat :=
  if cls = 0 then n / 2
  else if cls % 2 = 1 then n - max (p - 1) 1
  else if p = 0 then 1 else if p = 1 then n - 1 else p - 1

/-- The time borders are strictly monotone (the check of l.747-752). -/
def Mono (v : DV) : Prop := ∀ i, 1 ≤ i → i ≤ v.nenv → u8 v.te (i - 1) < u8 v.te i

/-- After the checks (l.754-773): `bs_num_noise`, `t_q`. -/
def gridTail (v : DV) (cls p : Nat) : DV :=
  { v with
    nnoise := if 1 < v.nenv then 2 else 1
    tq := mk 3 (fun q => if q = 0 then old v.te 0
      else if q = (if 1 < v.nenv then 2 else 1) then old v.te v.nenv
      else if q = 1 ∧ 1 < v.nenv then old v.te (idxOf cls v.nenv p) else old v.tq q) }

/-- `read_sbr_grid(ac, sbr, gb, ch_data)`: the values `v'` of `*ch_data` it leaves and whether it
returned `0` (`true`). Every return `-1` keeps what was stored before it. Only runs that return
are outcomes: a run stopped by `av_assert0(bs_pointer >= 0)` (see `GridSw`) has no next state, so
it is in no `Grid`, `Call` or `ModelStep` (no later call of `ff_aac_sbr_apply` follows it). -/
inductive Grid (usac : Bool) (v : DV) : DV → Bool → Prop
  /-- Rejected in the `switch`. -/
  | swFail {w : DV} : GridSw usac (gridPro v) w none → Grid usac v w false
  /-- `bs_pointer > bs_num_env + 1` (l.740-745). -/
  | ptrFail {w : DV} {cls p : Nat} : GridSw usac (gridPro v) w (some (cls, p)) →
      w.nenv + 1 < p → Grid usac v w false
  /-- Not strictly monotone (l.747-752). -/
  | monoFail {w : DV} {cls p : Nat} : GridSw usac (gridPro v) w (some (cls, p)) →
      p ≤ w.nenv + 1 → ¬ Mono w → Grid usac v w false
  /-- Accepted. -/
  | ok {w : DV} {cls p : Nat} : GridSw usac (gridPro v) w (some (cls, p)) →
      p ≤ w.nenv + 1 → Mono w → Grid usac v (gridTail w cls p) true

/-- `copy_sbr_grid(dst, src)` (l.785-800) on the values `DV` holds: `bs_freq_res[0]` and
`t_env_num_env_old` from `dst`'s own last envelope, `bs_freq_res[1..8]`, `t_env[0..8]`, `t_q`,
`bs_num_env`, `bs_num_noise` from `src`. -/
def copyGrid (dst src : DV) : DV :=
  { dst with
    freqRes := mk 9 (fun j => if j = 0 then old dst.freqRes dst.nenv else old src.freqRes j),
    te := mk 10 (fun j => if j = 9 then old dst.te dst.nenv else old src.te j),
    tq := mk 3 (fun j => old src.tq j), nenv := src.nenv, nnoise := src.nnoise }

/-! ### The grid preserves `DWF` and the border invariant -/

theorem dwf_iff {L : Prop} {v : DV} : DWF L v ↔ DWF False v ∧ (L → Live v) := by
  constructor
  · rintro ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16⟩
    exact ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, False.elim⟩, a16⟩
  · rintro ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, -⟩, a16⟩
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16⟩

/-- Closes the bound goals left by unfolding `mk`. -/
syntax "bnd" : tactic
macro_rules
  | `(tactic| bnd) => `(tactic| first
      | omega
      | assumption
      | (simp only [old_toNat, UInt8.toNat_ofNat', UInt8.toNat_ofNat, Nat.reducePow,
          Classical.not_and_iff_not_or_not, Nat.not_le, Nat.not_lt,
          not_true_eq_false, or_false, false_or, and_true, true_and] at *; omega)
      | (simp only [old_toNat, UInt8.toNat_ofNat', UInt8.toNat_ofNat, Nat.reducePow,
          Classical.not_and_iff_not_or_not, Nat.not_le, Nat.not_lt,
          not_true_eq_false, or_false, false_or, and_true, true_and] at *; assumption)
      | (simp only [old_toNat, UInt8.toNat_ofNat', UInt8.toNat_ofNat, Nat.reducePow,
          Classical.not_and_iff_not_or_not, Nat.not_le, Nat.not_lt,
          not_true_eq_false, or_false, false_or, and_true, true_and] at *; done)
      | decide)

theorem frSet_le {v : DV} {n : Nat} {r : Nat → Nat} (hr : ∀ j, r j < 2)
    (h0 : u8 v.freqRes 0 ≤ 1) {j : Nat} (hj : j ≤ n) : u8 (frSet v n r) j ≤ 1 := by
  unfold frSet; rw [u8_mk]
  by_cases hj9 : j < 9
  · simp only [hj9, ↓reduceIte]
    by_cases hc : 1 ≤ j ∧ j ≤ n
    · simp only [hc, and_self, ↓reduceIte, UInt8.toNat_ofNat']; have := hr j; omega
    · simp only [hc, ↓reduceIte]; obtain rfl : j = 0 := by omega
      exact h0
  · simp only [hj9, ↓reduceIte]; omega

/-- A store that leaves byte `9` (`t_env_num_env_old`). -/
theorem u8_mk9 {f : Nat → UInt8} {bs : List UInt8} (hf : f 9 = old bs 9) :
    u8 (mk 10 f) 9 = u8 bs 9 := by
  rw [u8_mk]; simp only [show 9 < 10 from by decide, ↓reduceIte, hf]

/-- What the `switch` leaves, from the facts of the prologue's values. -/
theorem gridSw_spec {usac : Bool} {v w : DV} {o : Option (Nat × Nat)} (h : GridSw usac v w o)
    (hfl : v.freqRes.length = 9) (htl : v.te.length = 10) (hn : v.nenv ≤ 8)
    (hfr : ∀ e, e ≤ v.nenv → u8 v.freqRes e ≤ 1) (h9 : u8 v.te 9 ≤ 19)
    (hb : u8 v.te v.nenv ≤ 19) :
    w.freqRes.length = 9 ∧ w.te.length = 10 ∧ w.nenv ≤ 8 ∧ (∀ e, e ≤ w.nenv → u8 w.freqRes e ≤ 1)
    ∧ u8 w.te 9 ≤ 19 ∧ u8 w.te w.nenv ≤ 19 ∧ w.nnoise = v.nnoise ∧ w.tq = v.tq
    ∧ w.invf = v.invf ∧ w.vOff = v.vOff ∧ w.ypos = v.ypos ∧ w.idx = v.idx
    ∧ (∀ cls p, o = some (cls, p) → 1 ≤ w.nenv ∧ cls < 4) := by
  have h0 := hfr 0 (Nat.zero_le _)
  cases h with
  | fixfixBad e he hbad =>
    exact ⟨hfl, htl, hn, hfr, h9, hb, rfl, rfl, rfl, rfl, rfl, rfl, by simp⟩
  | fixfix e r he hr hok =>
    have h2 : 2 ^ e ≤ 8 := by split at hok <;> omega
    have h1 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
    refine ⟨mk_length _ _, mk_length _ _, h2, fun j hj => frSet_le (fun _ => hr) h0 hj,
      ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    · dsimp only; simp only [fixfixTe, u8_mk]
      (repeat' split) <;> bnd
    · dsimp only; simp only [fixfixTe, u8_mk]
      (repeat' split) <;> bnd
    · rintro cls p hcp; simp only [Option.some.injEq, Prod.mk.injEq] at hcp
      obtain ⟨rfl, rfl⟩ := hcp; dsimp only; omega
  | fixvar a b p c r ha hb' hc hr =>
    refine ⟨mk_length _ _, mk_length _ _, by dsimp only; omega,
      fun j hj => frSet_le (r := fun j => r (b + 1 - j)) (fun _ => hr _) h0 hj,
      ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    · dsimp only; simp only [fixvarTe, u8_mk]
      (repeat' split) <;> bnd
    · dsimp only; simp only [fixvarTe, u8_mk]
      (repeat' split) <;> bnd
    · rintro cls p' hcp; simp only [Option.some.injEq, Prod.mk.injEq] at hcp
      obtain ⟨rfl, rfl⟩ := hcp; dsimp only; omega
  | varfix a0 b p c r ha hb' hc hr =>
    refine ⟨mk_length _ _, mk_length _ _, by dsimp only; omega,
      fun j hj => frSet_le (r := fun j => r (j - 1)) (fun _ => hr _) h0 hj,
      ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    · dsimp only; simp only [varfixTe, u8_mk]
      (repeat' split) <;> bnd
    · dsimp only; simp only [varfixTe, u8_mk]
      (repeat' split) <;> bnd
    · rintro cls p' hcp; simp only [Option.some.injEq, Prod.mk.injEq] at hcp
      obtain ⟨rfl, rfl⟩ := hcp; dsimp only; omega
  | varvarBad a0 a lead trail ha0 ha hl ht hbad =>
    refine ⟨hfl, mk_length _ _, hn, hfr, ?_, ?_, rfl, rfl,
      rfl, rfl, rfl, rfl, by simp⟩
    · dsimp only; simp only [u8_mk]
      (repeat' split) <;> bnd
    · dsimp only; simp only [u8_mk]
      (repeat' split) <;> bnd
  | varvar a0 a lead trail p c d r ha0 ha hl ht hok hc hd hr =>
    refine ⟨mk_length _ _, mk_length _ _, by dsimp only; omega,
      fun j hj => frSet_le (r := fun j => r (j - 1)) (fun _ => hr _) h0 hj,
      ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    · dsimp only; simp only [varvarTe, u8_mk]
      (repeat' split) <;> bnd
    · dsimp only; simp only [varvarTe, u8_mk]
      (repeat' split) <;> bnd
    · rintro cls p' hcp; simp only [Option.some.injEq, Prod.mk.injEq] at hcp
      obtain ⟨rfl, rfl⟩ := hcp; dsimp only; omega

theorem mono_le {w : DV} (hm : Mono w) :
    ∀ k e, e + k = w.nenv → u8 w.te e ≤ u8 w.te w.nenv
  | 0, e, h => by rw [← h]; exact Nat.le_refl _
  | k + 1, e, h => by
    have h1 := hm (e + 1) (by omega) (by omega)
    have h2 := mono_le hm k (e + 1) (by omega)
    simp only [Nat.add_sub_cancel] at h1
    omega

theorem idxOf_le {cls n p : Nat} (hn : 1 ≤ n) (hp : p ≤ n + 1) : idxOf cls n p ≤ n := by
  unfold idxOf; repeat' split
  all_goals omega

/-- **The grid.** `read_sbr_grid` keeps the unconditional clauses of `DWF` and the border
invariant (`t_env[bs_num_env] ≤ 19`) on every path, including the returns `-1` after the stores,
and an accepted grid is live. It does not touch `bs_invf_mode` or the fields apply writes. -/
theorem grid_wf {usac : Bool} {v w : DV} {ok : Bool} (hd : DWF False v)
    (hb : u8 v.te v.nenv ≤ 19) (h : Grid usac v w ok) :
    DWF False w ∧ u8 w.te w.nenv ≤ 19 ∧ (ok = true → Live w)
    ∧ w.invf = v.invf ∧ w.vOff = v.vOff ∧ w.ypos = v.ypos ∧ w.idx = v.idx := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, -⟩ := hd
  -- the prologue
  have p1 : (gridPro v).freqRes.length = 9 := mk_length _ _
  have p2 : (gridPro v).te.length = 10 := mk_length _ _
  have p3 : (gridPro v).nenv ≤ 8 := a5
  have p4 : ∀ e, e ≤ (gridPro v).nenv → u8 (gridPro v).freqRes e ≤ 1 := by
    intro e he; dsimp only [gridPro] at he ⊢; simp only [u8_mk]
    have := a6 e he; have := a6 v.nenv (Nat.le_refl _)
    (repeat' split) <;> bnd
  have p5 : u8 (gridPro v).te 9 ≤ 19 := by
    dsimp only [gridPro]; simp only [u8_mk]; (repeat' split) <;> bnd
  have p6 : u8 (gridPro v).te (gridPro v).nenv ≤ 19 := by
    dsimp only [gridPro]; simp only [u8_mk]; (repeat' split) <;> bnd
  have sw := fun {w o} (hs : GridSw usac (gridPro v) w o) => gridSw_spec hs p1 p2 p3 p4 p5 p6
  cases h with
  | swFail hs =>
    obtain ⟨b1, b3, b5, b6, b10, bb, b7, b4, b2, b14, b9, b12, -⟩ := sw hs
    refine ⟨⟨b1, b2 ▸ a2, b3, b4 ▸ a4, b5, b6, b7 ▸ a7, b2 ▸ a8, b9 ▸ a9, b10, b7 ▸ b4 ▸ a11,
      b12 ▸ a12, b12 ▸ a13, b14 ▸ a14, b14 ▸ a15, False.elim⟩, bb, by simp, b2, b14, b9, b12⟩
  | ptrFail hs _ =>
    obtain ⟨b1, b3, b5, b6, b10, bb, b7, b4, b2, b14, b9, b12, -⟩ := sw hs
    refine ⟨⟨b1, b2 ▸ a2, b3, b4 ▸ a4, b5, b6, b7 ▸ a7, b2 ▸ a8, b9 ▸ a9, b10, b7 ▸ b4 ▸ a11,
      b12 ▸ a12, b12 ▸ a13, b14 ▸ a14, b14 ▸ a15, False.elim⟩, bb, by simp, b2, b14, b9, b12⟩
  | monoFail hs _ _ =>
    obtain ⟨b1, b3, b5, b6, b10, bb, b7, b4, b2, b14, b9, b12, -⟩ := sw hs
    refine ⟨⟨b1, b2 ▸ a2, b3, b4 ▸ a4, b5, b6, b7 ▸ a7, b2 ▸ a8, b9 ▸ a9, b10, b7 ▸ b4 ▸ a11,
      b12 ▸ a12, b12 ▸ a13, b14 ▸ a14, b14 ▸ a15, False.elim⟩, bb, by simp, b2, b14, b9, b12⟩
  | @ok w cls p hs hp hm =>
    obtain ⟨b1, b3, b5, b6, b10, bb, -, -, b2, b14, b9, b12, bo⟩ := sw hs
    obtain ⟨hn1, -⟩ := bo cls p rfl
    have hle : ∀ e, e ≤ w.nenv → u8 w.te e ≤ 19 := fun e he =>
      Nat.le_trans (mono_le hm (w.nenv - e) e (by omega)) bb
    have hid := idxOf_le (cls := cls) hn1 hp
    have hlive : Live w := ⟨hn1, hle, fun e he => by
      have := hm (e + 1) (by omega) (by omega); simpa using this⟩
    refine ⟨⟨b1, b2 ▸ a2, b3, mk_length _ _, b5, b6, ?_, b2 ▸ a8, b9 ▸ a9, b10, ?_,
      b12 ▸ a12, b12 ▸ a13, b14 ▸ a14, b14 ▸ a15, False.elim⟩, bb, fun _ => hlive, b2, b14, b9,
      b12⟩
    · dsimp only [gridTail]; split <;> omega
    · intro q hq; dsimp only [gridTail] at hq ⊢; simp only [u8_mk]
      have := hle 0 (Nat.zero_le _); have := hle w.nenv (Nat.le_refl _)
      have := hle _ hid
      by_cases hn : 1 < w.nenv <;> simp only [hn, ↓reduceIte] at hq ⊢ <;> (repeat' split) <;> bnd

/-- **The copy.** `copy_sbr_grid(&data[1], &data[0])` keeps `DWF False` and the border invariant
of the destination (its own `t_env[bs_num_env]` goes to `t_env_num_env_old`), and a live source
gives a live destination. -/
theorem copy_wf {d0 d1 : DV} (hd0 : DWF False d0) (hb0 : u8 d0.te d0.nenv ≤ 19)
    (hd1 : DWF False d1) (hb1 : u8 d1.te d1.nenv ≤ 19) :
    DWF False (copyGrid d1 d0) ∧ u8 (copyGrid d1 d0).te (copyGrid d1 d0).nenv ≤ 19
    ∧ (Live d0 → Live (copyGrid d1 d0))
    ∧ (copyGrid d1 d0).invf = d1.invf ∧ (copyGrid d1 d0).vOff = d1.vOff
    ∧ (copyGrid d1 d0).ypos = d1.ypos ∧ (copyGrid d1 d0).idx = d1.idx := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, -⟩ := hd0
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, -⟩ := hd1
  have hte : ∀ e, e ≤ d0.nenv → u8 (copyGrid d1 d0).te e = u8 d0.te e := by
    intro e he; dsimp only [copyGrid]; rw [u8_mk]
    simp only [show e < 10 by omega, show e ≠ 9 by omega, ↓reduceIte]
  refine ⟨⟨mk_length _ _, c2, mk_length _ _, mk_length _ _, a5, ?_, a7, c8, c9, ?_, ?_, c12, c13,
    c14, c15, False.elim⟩, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · intro e he; dsimp only [copyGrid] at he ⊢; simp only [u8_mk]
    have := a6 e he; have := c6 d1.nenv (Nat.le_refl _)
    (repeat' split) <;> bnd
  · dsimp only [copyGrid]; simp only [u8_mk]; (repeat' split) <;> bnd
  · intro q hq; dsimp only [copyGrid] at hq ⊢; simp only [u8_mk]
    have := a11 q hq
    (repeat' split) <;> bnd
  · dsimp only [copyGrid] at hte ⊢; rw [hte _ (Nat.le_refl _)]; exact hb0
  · rintro ⟨l1, l2, l3⟩
    refine ⟨l1, fun e he => ?_, fun e he => ?_⟩
    · dsimp only [copyGrid] at he hte ⊢; rw [hte e he]; exact l2 e he
    · dsimp only [copyGrid] at he hte ⊢; rw [hte e (by omega), hte (e + 1) (by omega)]
      exact l3 e he

/-! ## The frequency tables: `sbr_reset` (l.1113-1124)

`sbr_make_f_master` (l.274-491), `sbr_make_f_derived` (l.552-622), `sbr_hf_calc_npatches`
(l.494-549), `sbr_make_f_tablelim` (l.137-186). The `uint16_t` tables are written through
`mk16`; a store of an `int` into a `uint16_t` keeps it mod 65536. -/

/-- The array of `k` little-endian `uint16_t` whose element `i` is `f i mod 65536`. -/
def mk16 (k : Nat) (f : Nat → Nat) : List UInt8 :=
  mk (2 * k) (fun b => UInt8.ofNat (if b % 2 = 0 then f (b / 2) % 256 else f (b / 2) / 256 % 256))

@[simp] theorem mk16_length (k : Nat) (f : Nat → Nat) : (mk16 k f).length = 2 * k := by
  simp [mk16]

theorem u16_mk16 {k : Nat} {f : Nat → Nat} {i : Nat} (hi : i < k) :
    u16 (mk16 k f) i = f i % 65536 := by
  unfold u16 mk16
  rw [u8_mk, u8_mk]
  simp only [show 2 * i < 2 * k by omega, show 2 * i + 1 < 2 * k by omega,
    show 2 * i % 2 = 0 by omega, show ¬ ((2 * i + 1) % 2 = 0) by omega,
    show 2 * i / 2 = i by omega, show (2 * i + 1) / 2 = i by omega, ↓reduceIte,
    UInt8.toNat_ofNat', Nat.reducePow]
  omega

theorem u16_lt (bs : List UInt8) (i : Nat) : u16 bs i < 65536 := by
  unfold u16 u8
  have := (bs.getD (2 * i) 0).toNat_lt; have := (bs.getD (2 * i + 1) 0).toNat_lt
  omega

/-! ### `sbr_make_f_master` -/

theorem rateRow_mem {sr : Int} {row : Nat} (h : rateRow sr = some row) : sr ∈ rates := by
  apply Classical.byContradiction; intro hn
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hn
  simp [rateRow, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12] at h

/-- The check of `k0Of_range` as a computation. -/
def k0ok (sr : Int) (st : Nat) : Bool :=
  match rateRow sr with
  | some row => decide (1 ≤ k0Of sr row st) && decide (k0Of sr row st ≤ 32)
  | none => true

theorem k0_all : ∀ sr ∈ rates, ∀ st, st < 16 → k0ok sr st = true := by decide

/-- `k[0]` is in `[1, 32]` for every supported rate and every 4-bit `bs_start_freq`. -/
theorem k0Of_range {sr : Int} {row : Nat} (h : rateRow sr = some row) {st : Nat} (hst : st < 16) :
    1 ≤ k0Of sr row st ∧ k0Of sr row st ≤ 32 := by
  have := k0_all sr (rateRow_mem h) st hst
  simp only [k0ok, h, Bool.and_eq_true, decide_eq_true_eq] at this; exact this

/-- The values `sbr_make_f_master` leaves in `Args` (only `k[0]`), and on success `n_master`,
`f_master` and `k[2]`.

Abstraction: the band computation is not transcribed. The model keeps what the code checks and
what holds of its output by construction: `f_master[0] = k[0]` (l.372, 419), strictly increasing
(every step is `dk ≥ 1`, l.356-374, or a `vDk` checked `> 0`, l.421, 467), ending at most at
`k[2]` (the steps of `make_bands` telescope to `stop - start`, the `change` of l.458-460 keeps the
sum), `k[2] ≤ 64` (l.335), `0 ≤ k[2] - k[0] ≤ max_qmf_subbands` (the unsigned compare of l.347),
`bs_xover_band < n_master` (`check_n_master`, l.264). Every failure after the store of `k[0]`
(l.318) is one constructor `fail`: none of them writes `Args`. -/
inductive Master (sr : Int) (start xover : Nat) : Option Int → Option (Nat × (Nat → Nat)) → Prop
  /-- Unsupported rate (l.302-306): `k[0]` not written. -/
  | badRate : rateRow sr = none → Master sr start xover none none
  /-- A rejection after `k[0]` is stored. -/
  | fail {row : Nat} : rateRow sr = some row → Master sr start xover (some (k0Of sr row start)) none
  /-- Success. -/
  | ok {row : Nat} (k2 : Int) (nm : Nat) (f : Nat → Nat) : rateRow sr = some row →
      k2 ≤ 64 → k0Of sr row start ≤ k2 →
      k2 - k0Of sr row start ≤ (if sr ≤ 32000 then 48 else if sr = 44100 then 35 else 32) →
      xover < nm → (f 0 : Int) = k0Of sr row start → (∀ i, i < nm → f i < f (i + 1)) →
      (f nm : Int) ≤ k2 → Master sr start xover (some (k0Of sr row start)) (some (nm, f))

/-! ### `f_tablenoise` (l.606-611) -/

/-- `temp` after iteration `k` of the noise border loop (l.607-611). -/
def ntemp (n0 nq : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => ntemp n0 nq k + (n0 - ntemp n0 nq k) / (nq + 1 - (k + 1))

theorem ntemp_le (n0 nq : Nat) : ∀ k, ntemp n0 nq k ≤ n0
  | 0 => Nat.zero_le _
  | k + 1 => by
    have := ntemp_le n0 nq k
    have := Nat.div_le_self (n0 - ntemp n0 nq k) (nq + 1 - (k + 1))
    simp only [ntemp]; omega

theorem ntemp_mono (n0 nq k : Nat) : ntemp n0 nq k ≤ ntemp n0 nq (k + 1) := by
  simp only [ntemp]; exact Nat.le_add_right _ _

theorem ntemp_last (n0 nq : Nat) (h : 1 ≤ nq) : ntemp n0 nq nq = n0 := by
  obtain ⟨k, rfl⟩ : ∃ k, nq = k + 1 := ⟨nq - 1, by omega⟩
  have := ntemp_le n0 (k + 1) k
  simp only [ntemp, show k + 1 + 1 - (k + 1) = 1 by omega, Nat.div_one]; omega

/-! ### `sbr_hf_calc_npatches` (l.494-549) -/

/-- `Σ_{i<n} patch_num_subbands[i]`, as in `TabWF`. -/
def psum (pn : List UInt8) (n : Nat) : Nat := (List.range n).foldl (fun a i => a + u8 pn i) 0

theorem psum_succ (pn : List UInt8) (n : Nat) : psum pn (n + 1) = psum pn n + u8 pn n := by
  simp [psum, List.range_succ, List.foldl_append]

theorem psum_congr {a b : List UInt8} : ∀ {n : Nat}, (∀ i, i < n → u8 a i = u8 b i) →
    psum a n = psum b n
  | 0, _ => rfl
  | n + 1, h => by
    rw [psum_succ, psum_succ, psum_congr (fun i hi => h i (by omega)), h n (by omega)]

theorem psum_mono (pn : List UInt8) {m n : Nat} (h : m ≤ n) : psum pn m ≤ psum pn n := by
  induction n with
  | zero => obtain rfl : m = 0 := by omega
            exact Nat.le_refl _
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with h' | h'
    · rw [psum_succ]; have := ih (by omega); omega
    · obtain rfl : m = n + 1 := by omega
      exact Nat.le_refl _

/-- The state of the patch loop: `k`, `last_k`, `msb`, `last_msb`, `usb`, `num_patches`,
`patch_num_subbands`, `patch_start_subband`, `sb`. -/
structure PL where
  k : Nat
  lk : Int
  msb : Nat
  lmsb : Int
  usb : Nat
  np : Nat
  pn : List UInt8
  pst : List UInt8
  sb : Nat

/-- `odd = (sb + k[0]) & 1` (l.518). -/
def oddOf (k0 sb : Nat) : Nat := (sb + k0) % 2

/-- The inner loop (l.516-519) from `i = k` down stops at `j`: the first index with
`f_master[j] ≤ k[0] - 1 + msb - odd`; then `sb = f_master[j]`. -/
def Inner (f : Nat → Nat) (k0 msb k j : Nat) : Prop :=
  j ≤ k ∧ (f j : Int) ≤ k0 - 1 + msb - oddOf k0 (f j)
  ∧ ∀ i, j < i → i ≤ k → (k0 - 1 + msb - oddOf k0 (f i) : Int) < f i

/-- One pass of the `do` body after its checks (l.514-541), with `sb = f_master[j]`. The
subtraction `sb - usb` is `FFMAX(sb - usb, 0)` (l.530). -/
def pbody (f : Nat → Nat) (k0 kx1 nm : Nat) (s : PL) (j : Nat) : PL :=
  { k := if (f s.k : Int) - f j < 3 then nm else s.k
    lk := s.k
    msb := if 0 < f j - s.usb then f j else kx1
    lmsb := s.msb
    usb := if 0 < f j - s.usb then f j else s.usb
    np := if 0 < f j - s.usb then s.np + 1 else s.np
    pn := mk 6 (fun i => if i = s.np then UInt8.ofNat (f j - s.usb) else old s.pn i)
    pst := mk 6 (fun i =>
      if i = s.np then u8i ((k0 : Int) - oddOf k0 (f j) - ((f j - s.usb : Nat) : Int))
      else old s.pst i)
    sb := f j }

/-- The `do … while (sb != kx[1] + m[1])` loop (l.508-542) from state `s`: the state it leaves
and whether it ended normally (`true`) or by one of its two `return`s. -/
inductive PRun (f : Nat → Nat) (k0 kx1 nm top : Nat) : PL → PL → Bool → Prop
  /-- `k == last_k && msb == last_msb` (l.510-513). -/
  | rep (s : PL) : (s.k : Int) = s.lk ∧ (s.msb : Int) = s.lmsb → PRun f k0 kx1 nm top s s false
  /-- `num_patches > 5` (l.525-528), after the inner loop. -/
  | many (s : PL) (j : Nat) : ¬ ((s.k : Int) = s.lk ∧ (s.msb : Int) = s.lmsb) →
      Inner f k0 s.msb s.k j → 5 < s.np →
      PRun f k0 kx1 nm top s { s with lk := s.k, lmsb := s.msb, sb := f j } false
  /-- The last pass: `sb == kx[1] + m[1]`. -/
  | stop (s : PL) (j : Nat) : ¬ ((s.k : Int) = s.lk ∧ (s.msb : Int) = s.lmsb) →
      Inner f k0 s.msb s.k j → s.np ≤ 5 → f j = top →
      PRun f k0 kx1 nm top s (pbody f k0 kx1 nm s j) true
  /-- Another pass. -/
  | cont (s : PL) (j : Nat) {r : PL} {b : Bool} : ¬ ((s.k : Int) = s.lk ∧ (s.msb : Int) = s.lmsb) →
      Inner f k0 s.msb s.k j → s.np ≤ 5 → f j ≠ top →
      PRun f k0 kx1 nm top (pbody f k0 kx1 nm s j) r b → PRun f k0 kx1 nm top s r b

/-- `goal_sb` (l.499). -/
def goalSb (sr : Int) : Int := (2048000 + sr / 2) / sr

/-- The start of the loop (l.501-506): `k` is the first index with `f_master[k] ≥ goal_sb` if
`goal_sb < kx[1] + m[1]`, else `n_master`. -/
def KInit (f : Nat → Nat) (nm top : Nat) (goal : Int) (k : Nat) : Prop :=
  if goal < top then k ≤ nm ∧ (∀ i, i < k → (f i : Int) < goal) ∧ goal ≤ f k else k = nm

/-- `sbr_hf_calc_npatches`: the values it leaves (`num_patches`, `patch_num_subbands`,
`patch_start_subband`) and whether it returned `0`. On success the last patch is dropped if it
is narrower than 3 (l.544-546). The byte lists of `Args` stand for the 6-byte arrays, so the
loop starts from them read as 6 bytes (`mk 6`). -/
inductive Patches (f : Nat → Nat) (sr : Int) (k0 kx1 m1 nm : Nat) (x : Args) : Args → Bool → Prop
  | run (k : Nat) {r : PL} {b : Bool} : KInit f nm (kx1 + m1) (goalSb sr) k →
      PRun f k0 kx1 nm (kx1 + m1)
        { k := k, lk := -1, msb := k0, lmsb := -1, usb := kx1, np := 0, pn := mk 6 (old x.pnum),
          pst := mk 6 (old x.pstart), sb := 0 } r b →
      Patches f sr k0 kx1 m1 nm x
        { x with
          npatch := if b ∧ 1 < r.np ∧ u8 r.pn (r.np - 1) < 3 then r.np - 1 else r.np
          pnum := r.pn
          pstart := r.pst } b

/-- The invariant of the patch loop. -/
def PInv (k0 kx1 nm top : Nat) (s : PL) : Prop :=
  s.k ≤ nm ∧ k0 ≤ s.msb ∧ s.msb ≤ s.usb ∧ kx1 ≤ s.usb ∧ s.usb ≤ top ∧ s.np ≤ 6
  ∧ (s.usb = kx1 ∨ 1 ≤ s.np) ∧ s.pn.length = 6 ∧ s.pst.length = 6
  ∧ (∀ i, i < s.np → 1 ≤ u8 s.pn i ∧ u8 s.pn i + u8 s.pst i ≤ k0)
  ∧ psum s.pn s.np = s.usb - kx1

theorem u8i_toNat {z : Int} (h0 : 0 ≤ z) (h1 : z < 256) : (u8i z).toNat = z.toNat := by
  unfold u8i; rw [UInt8.toNat_ofNat', Int.emod_eq_of_lt h0 h1]; omega

theorem pbody_inv {f : Nat → Nat} {k0 kx1 nm top : Nat} (hk0 : k0 ≤ 32) (hkx : k0 ≤ kx1)
    (hf : ∀ i, i ≤ nm → f i ≤ top) {s : PL} {j : Nat} (hs : PInv k0 kx1 nm top s)
    (hj : Inner f k0 s.msb s.k j) (hnp : s.np ≤ 5) :
    PInv k0 kx1 nm top (pbody f k0 kx1 nm s j) := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11⟩ := hs
  obtain ⟨j1, j2, -⟩ := hj
  have hfj := hf j (by omega)
  have hod : oddOf k0 (f j) ≤ 1 := by unfold oddOf; omega
  have hpn : u8 (pbody f k0 kx1 nm s j).pn s.np = f j - s.usb := by
    dsimp only [pbody]; rw [u8_mk]; simp only [show s.np < 6 by omega, ↓reduceIte,
      UInt8.toNat_ofNat', Nat.reducePow]; omega
  have hpe : ∀ i, i < s.np → u8 (pbody f k0 kx1 nm s j).pn i = u8 s.pn i := by
    intro i hi; dsimp only [pbody]; rw [u8_mk]
    simp only [show i < 6 by omega, show i ≠ s.np by omega, ↓reduceIte]
  have hse : ∀ i, i < s.np → u8 (pbody f k0 kx1 nm s j).pst i = u8 s.pst i := by
    intro i hi; dsimp only [pbody]; rw [u8_mk]
    simp only [show i < 6 by omega, show i ≠ s.np by omega, ↓reduceIte]
  have hps : psum (pbody f k0 kx1 nm s j).pn s.np = psum s.pn s.np := psum_congr hpe
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, mk_length _ _, mk_length _ _, ?_, ?_⟩
  · dsimp only [pbody]; split <;> omega
  · dsimp only [pbody]; split <;> omega
  · dsimp only [pbody]; split <;> omega
  · dsimp only [pbody]; split <;> omega
  · dsimp only [pbody]; split <;> omega
  · dsimp only [pbody]; split <;> omega
  · dsimp only [pbody]; split <;> omega
  · intro i hi
    by_cases hc : 0 < f j - s.usb
    · have hi' : i < s.np + 1 := by
        dsimp only [pbody] at hi; simp only [hc, ↓reduceIte] at hi; exact hi
      rcases Nat.lt_or_ge i s.np with hlt | hge
      · rw [hpe i hlt, hse i hlt]; exact i10 i hlt
      · obtain rfl : i = s.np := by omega
        rw [hpn]
        have hst : u8 (pbody f k0 kx1 nm s j).pst s.np =
            ((k0 : Int) - oddOf k0 (f j) - (f j - s.usb : Nat)).toNat := by
          dsimp only [pbody]; rw [u8_mk]
          simp only [show s.np < 6 by omega, ↓reduceIte]
          apply u8i_toNat <;> omega
        rw [hst]; omega
    · have hi' : i < s.np := by dsimp only [pbody] at hi; simp only [hc, ↓reduceIte] at hi; exact hi
      rw [hpe i hi', hse i hi']; exact i10 i hi'
  · by_cases hc : 0 < f j - s.usb
    · dsimp only [pbody] at hps hpn ⊢; simp only [hc, ↓reduceIte]
      rw [psum_succ, hps, hpn, i11]; omega
    · dsimp only [pbody] at hps ⊢; simp only [hc, ↓reduceIte]
      rw [hps, i11]

theorem prun_inv {f : Nat → Nat} {k0 kx1 nm top : Nat} (hk0 : k0 ≤ 32) (hkx : k0 ≤ kx1)
    (hf : ∀ i, i ≤ nm → f i ≤ top) {s r : PL} {b : Bool} (h : PRun f k0 kx1 nm top s r b)
    (hs : PInv k0 kx1 nm top s) : PInv k0 kx1 nm top r ∧ (b = true → r.usb = top) := by
  induction h with
  | rep s _ => exact ⟨hs, by simp⟩
  | many s j _ _ hnp =>
    obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11⟩ := hs
    exact ⟨⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11⟩, by simp⟩
  | stop s j _ hj hnp htop =>
    refine ⟨pbody_inv hk0 hkx hf hs hj hnp, fun _ => ?_⟩
    obtain ⟨-, -, -, -, i5, -⟩ := hs
    dsimp only [pbody]; split <;> omega
  | cont s j _ hj hnp _ _ ih => exact ih (pbody_inv hk0 hkx hf hs hj hnp)

/-- **The patches.** On success: `1 ≤ num_patches ≤ 6`, each patch inside `X_low`
(`patch_start_subband + patch_num_subbands ≤ k[0] ≤ 32`), and the patch widths add up to at most
`m[1]` (F5). On failure `num_patches ≤ 6`. -/
theorem patches_spec {f : Nat → Nat} {sr : Int} {k0 kx1 m1 nm : Nat} {x x' : Args} {b : Bool}
    (hk0 : k0 ≤ 32) (hkx : k0 ≤ kx1) (hm : 1 ≤ m1) (hf : ∀ i, i ≤ nm → f i ≤ kx1 + m1)
    (h : Patches f sr k0 kx1 m1 nm x x' b) :
    x'.npatch ≤ 6 ∧ x'.pnum.length = 6 ∧ x'.pstart.length = 6
    ∧ (b = true → 1 ≤ x'.npatch ∧ (∀ i, i < x'.npatch → u8 x'.pstart i + u8 x'.pnum i ≤ 32)
        ∧ psum x'.pnum x'.npatch ≤ m1)
    ∧ x' = { x with npatch := x'.npatch, pnum := x'.pnum, pstart := x'.pstart } := by
  cases h with
  | @run k r b hk hr =>
    have h0 : PInv k0 kx1 nm (kx1 + m1)
        { k := k, lk := -1, msb := k0, lmsb := -1, usb := kx1, np := 0, pn := mk 6 (old x.pnum),
          pst := mk 6 (old x.pstart), sb := 0 } := by
      refine ⟨?_, Nat.le_refl _, hkx, Nat.le_refl _, show kx1 ≤ kx1 + m1 by omega,
        show 0 ≤ 6 by omega, Or.inl rfl, mk_length _ _, mk_length _ _,
        fun i hi => absurd hi (Nat.not_lt_zero i),
        by simp [psum]⟩
      show k ≤ nm
      unfold KInit at hk; split at hk <;> omega
    obtain ⟨⟨-, -, -, -, i5, i6, i7, i8, i9, i10, i11⟩, hend⟩ := prun_inv hk0 hkx hf hr h0
    refine ⟨?_, i8, i9, fun hb => ?_, rfl⟩
    · dsimp only; split <;> omega
    · subst hb
      have hu := hend rfl
      have hnp1 : 1 ≤ r.np := by rcases i7 with h7 | h7 <;> omega
      dsimp only
      split
      · rename_i hc
        refine ⟨by omega, fun i hi => ?_, ?_⟩
        · have := i10 i (by omega); omega
        · have := psum_mono r.pn (show r.np - 1 ≤ r.np by omega); omega
      · refine ⟨hnp1, fun i hi => ?_, by omega⟩
        have := i10 i hi; omega

/-! ### `sbr_make_f_tablelim` (l.137-186) -/

/-- `f_tablelim` after the two `memcpy` (l.152-156): `f_tablelow[0..n[0]]`, then the patch
borders `patch_borders[1..num_patches-1]`
(`patch_borders[k] = kx[1] + Σ_{i<k} patch_num_subbands[i]`, l.148-150). -/
def limIn (x : Args) (q : Nat) : Nat :=
  if q ≤ x.n0 then u16 x.ftLow q
  else if q < x.n0 + x.npatch then x.kx1 + psum x.pnum (q - x.n0) else u16 x.ftLim q

/-- `AV_QSORT` of the first `M` elements (l.158-160). Abstraction: a sorted array each of whose
first `M` elements is one of the first `M` inputs (a permutation has these properties; the model
does not need more). -/
def Sorted (M : Nat) (a s : Nat → Nat) : Prop :=
  (∀ q, q + 1 < M → s q ≤ s (q + 1)) ∧ (∀ q, q < M → ∃ t, t < M ∧ s q = a t)
  ∧ (∀ q, M ≤ q → s q = a q)

/-- Update an array at one index. -/
def upd (a : Nat → Nat) (p v : Nat) : Nat → Nat := fun q => if q = p then v else a q

/-- The compaction loop (l.163-180) on `(f_tablelim, in, out, n_lim)`, with `in`, `out` as
indices. Abstraction: the branch conditions (a float compare, `in_table_int16`) are not
transcribed: every step may take any of the four branches (`adv` is l.169 and l.178, `drop`
l.172-173, `repl` l.175-176). -/
inductive Compact : (Nat → Nat) → Nat → Nat → Nat → (Nat → Nat) → Nat → Prop
  | done (a : Nat → Nat) (i o L : Nat) : ¬ o < L → Compact a i o L a L
  | adv {a : Nat → Nat} {i o L : Nat} {r : Nat → Nat} {R : Nat} : o < L →
      Compact (upd a (o + 1) (a i)) (i + 1) (o + 1) L r R → Compact a i o L r R
  | drop {a : Nat → Nat} {i o L : Nat} {r : Nat → Nat} {R : Nat} : o < L →
      Compact a (i + 1) o (L - 1) r R → Compact a i o L r R
  | repl {a : Nat → Nat} {i o L : Nat} {r : Nat → Nat} {R : Nat} : o < L →
      Compact (upd a o (a i)) (i + 1) o (L - 1) r R → Compact a i o L r R

/-- `sbr_make_f_tablelim` with `bs_limiter_bands = lb`: the values it leaves (`f_tablelim`,
`n_lim`).

`n_lim = n[0] + num_patches - 1` (l.162) is `-1` if `n[0] = num_patches = 0`: `Args` (whose
`n_lim` is a `Nat`) cannot hold that, and the model has no successor there (`pos` asks
`1 ≤ n[0] + num_patches`). It is reached only from a header that does not reset (l.243-244,
l.1253-1254), and `Inv2` is what excludes it there. -/
inductive Tablelim (lb : Nat) (x : Args) : Args → Prop
  /-- `bs_limiter_bands == 0` (l.181-185). -/
  | zero : lb = 0 → Tablelim lb x
      { x with
        ftLim := mk16 30 (fun q => if q = 0 then u16 x.ftLow 0 else if q = 1 then u16 x.ftLow x.n0
          else u16 x.ftLim q)
        nlim := 1 }
  /-- `bs_limiter_bands > 0` (l.140-180). -/
  | pos {sa r : Nat → Nat} {R : Nat} : 0 < lb → 1 ≤ x.n0 + x.npatch →
      Sorted (x.n0 + x.npatch) (limIn x) sa → Compact sa 1 0 (x.n0 + x.npatch - 1) r R →
      Tablelim lb x { x with ftLim := mk16 30 r, nlim := R }

/-- The invariant of the compaction loop, for a sorted `s` on `[0, N]` with values in
`[lo, hi]`. -/
def CInv (N lo hi : Nat) (s a : Nat → Nat) (i o L : Nat) : Prop :=
  L ≤ N ∧ o ≤ L ∧ i = o + 1 + (N - L) ∧ (∀ q, i ≤ q → q ≤ N → a q = s q)
  ∧ (∀ q, q ≤ o → lo ≤ a q ∧ a q ≤ hi) ∧ (∀ q, q < o → a q ≤ a (q + 1))
  ∧ (i ≤ N → a o ≤ a i)

theorem compact_inv {N lo hi : Nat} {s : Nat → Nat} (hs : ∀ q, q < N → s q ≤ s (q + 1))
    (hr : ∀ q, q ≤ N → lo ≤ s q ∧ s q ≤ hi) {a : Nat → Nat} {i o L : Nat} {r : Nat → Nat}
    {R : Nat} (h : Compact a i o L r R) (hc : CInv N lo hi s a i o L) :
    R ≤ N ∧ (∀ q, q ≤ R → lo ≤ r q ∧ r q ≤ hi) ∧ (∀ q, q < R → r q ≤ r (q + 1)) := by
  induction h with
  | done a i o L hn =>
    obtain ⟨c1, c2, -, -, c5, c6, -⟩ := hc
    obtain rfl : o = L := by omega
    exact ⟨c1, c5, c6⟩
  | @adv a i o L r R hlt _ ih =>
    obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hc
    have hiN : i ≤ N := by omega
    have hai := c4 i (Nat.le_refl _) hiN
    apply ih
    refine ⟨c1, by omega, by omega, fun q hq hqN => ?_, fun q hq => ?_, fun q hq => ?_,
      fun hN => ?_⟩
    · simp only [upd, show q ≠ o + 1 by omega, ↓reduceIte]; exact c4 q (by omega) hqN
    · simp only [upd]; split
      · rw [hai]; exact hr i hiN
      · exact c5 q (by omega)
    · simp only [upd]
      by_cases hq1 : q + 1 = o + 1
      · simp only [hq1, ↓reduceIte, show q ≠ o + 1 by omega]
        obtain rfl : q = o := by omega
        exact c7 hiN
      · simp only [hq1, show q ≠ o + 1 by omega, ↓reduceIte]; exact c6 q (by omega)
    · simp only [upd, ↓reduceIte, show i + 1 ≠ o + 1 by omega]
      rw [hai, c4 (i + 1) (by omega) hN]; exact hs i (by omega)
  | @drop a i o L r R hlt _ ih =>
    obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hc
    have hiN : i ≤ N := by omega
    apply ih
    refine ⟨by omega, by omega, by omega, fun q hq hqN => c4 q (by omega) hqN, c5, c6,
      fun hN => ?_⟩
    rw [c4 (i + 1) (by omega) hN]
    have := c7 hiN; rw [c4 i (Nat.le_refl _) hiN] at this
    exact Nat.le_trans this (hs i (by omega))
  | @repl a i o L r R hlt _ ih =>
    obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hc
    have hiN : i ≤ N := by omega
    have hai := c4 i (Nat.le_refl _) hiN
    apply ih
    refine ⟨by omega, by omega, by omega, fun q hq hqN => ?_, fun q hq => ?_, fun q hq => ?_,
      fun hN => ?_⟩
    · simp only [upd, show q ≠ o by omega, ↓reduceIte]; exact c4 q (by omega) hqN
    · simp only [upd]; split
      · rw [hai]; exact hr i hiN
      · exact c5 q (by omega)
    · simp only [upd]
      by_cases hq1 : q + 1 = o
      · simp only [hq1, ↓reduceIte, show q ≠ o by omega]
        have := c7 hiN; have := c6 q (by omega); rw [hq1] at this; omega
      · simp only [hq1, show q ≠ o by omega, ↓reduceIte]; exact c6 q (by omega)
    · simp only [upd, ↓reduceIte, show i + 1 ≠ o by omega]
      rw [hai, c4 (i + 1) (by omega) hN]; exact hs i (by omega)

theorem chain_le {g : Nat → Nat} {n : Nat} (h : ∀ i, i < n → g i ≤ g (i + 1)) :
    ∀ k i, i + k ≤ n → g i ≤ g (i + k)
  | 0, i, _ => Nat.le_refl _
  | k + 1, i, hk => Nat.le_trans (chain_le h k i (by omega)) (h (i + k) (by omega))

/-- The facts of a table `bs` of `n + 1` entries inside `[lo, hi]`, nondecreasing. -/
def TabIn (bs : List UInt8) (n lo hi : Nat) : Prop :=
  (∀ i, i ≤ n → lo ≤ u16 bs i ∧ u16 bs i ≤ hi) ∧ (∀ i, i < n → u16 bs i ≤ u16 bs (i + 1))

/-- **The limiter table.** From `f_tablelow` inside `[kx[1], kx[1] + m[1]]` and the patch widths
adding up to at most `m[1]`: `n_lim ≤ n[0] + num_patches - 1` (so `≤ 29`), `f_tablelim` inside
`[kx[1], kx[1] + m[1]]` and nondecreasing up to `n_lim`. -/
theorem tablelim_spec {lb : Nat} {x x' : Args} (h : Tablelim lb x x')
    (hlow : TabIn x.ftLow x.n0 x.kx1 (x.kx1 + x.m1)) (hps : psum x.pnum x.npatch ≤ x.m1)
    (hn0 : x.n0 ≤ 24) (hnp : x.npatch ≤ 6) (hkm : x.kx1 + x.m1 ≤ 64) :
    x'.nlim ≤ 29 ∧ x'.ftLim.length = 60 ∧ TabIn x'.ftLim x'.nlim x'.kx1 (x'.kx1 + x'.m1)
    ∧ x' = { x with ftLim := x'.ftLim, nlim := x'.nlim } := by
  cases h with
  | zero _ =>
    refine ⟨by dsimp only; omega, by dsimp only; simp, ⟨fun i hi => ?_, fun i hi => ?_⟩, rfl⟩
    · dsimp only at hi ⊢; rw [u16_mk16 (by omega)]
      have := hlow.1 0 (Nat.zero_le _); have := hlow.1 x.n0 (Nat.le_refl _)
      have := u16_lt x.ftLow 0; have := u16_lt x.ftLow x.n0
      split
      · rename_i h0; subst h0; omega
      · split
        · omega
        · omega
    · dsimp only at hi ⊢
      have h0 : i = 0 := by omega
      subst h0
      rw [u16_mk16 (by omega), u16_mk16 (by omega)]
      simp only [↓reduceIte, Nat.zero_add, show (1 : Nat) ≠ 0 by decide]
      have := hlow.1 0 (Nat.zero_le _); have := hlow.1 x.n0 (Nat.le_refl _)
      have := chain_le hlow.2 x.n0 0 (by omega); simp only [Nat.zero_add] at this
      have := u16_lt x.ftLow 0; have := u16_lt x.ftLow x.n0
      omega
  | @pos sa r R _ h1 hs hc =>
    obtain ⟨s1, s2, -⟩ := hs
    have hrange : ∀ q, q ≤ x.n0 + x.npatch - 1 → x.kx1 ≤ sa q ∧ sa q ≤ x.kx1 + x.m1 := by
      intro q hq
      obtain ⟨t, ht, he⟩ := s2 q (by omega)
      rw [he]; unfold limIn
      split
      · exact hlow.1 t (by assumption)
      · have := psum_mono x.pnum (show t - x.n0 ≤ x.npatch by omega); omega
    have hc0 : CInv (x.n0 + x.npatch - 1) x.kx1 (x.kx1 + x.m1) sa sa 1 0 (x.n0 + x.npatch - 1) :=
      ⟨Nat.le_refl _, Nat.zero_le _, by omega, fun _ _ _ => rfl,
        fun q hq => by obtain rfl : q = 0 := by omega
                       exact hrange 0 (Nat.zero_le _),
        fun q hq => absurd hq (Nat.not_lt_zero _), fun hN => s1 0 (by omega)⟩
    obtain ⟨r1, r2, r3⟩ := compact_inv (fun q hq => s1 q (by omega)) hrange hc hc0
    have hR : R < 30 := by omega
    refine ⟨by dsimp only; omega, by dsimp only; simp, ⟨fun i hi => ?_, fun i hi => ?_⟩, rfl⟩
    · dsimp only at hi ⊢; rw [u16_mk16 (by omega)]
      have := r2 i hi; rw [Nat.mod_eq_of_lt (by omega)]; exact this
    · dsimp only at hi ⊢; rw [u16_mk16 (by omega), u16_mk16 (by omega)]
      have := r2 i (by omega); have := r2 (i + 1) (by omega); have := r3 i hi
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; exact this

/-! ### `sbr_make_f_derived` (l.552-622) and `sbr_reset` -/

/-- Clear `f_indexnoise` (the low 32 bits of `idx`), keep `f_indexsine` (l.618-619). -/
def clrNoise (v : DV) : DV := { v with idx := BitVec.ofNat 64 (v.idx.toNat / 2 ^ 32 * 2 ^ 32) }

/-- The stores of l.559-565: `n[1]`, `n[0]`, `f_tablehigh`, `m[1]`, `kx[1]`. -/
def derived1 (x : Args) (nm xo : Nat) (f : Nat → Nat) : Args :=
  { x with
    n1 := nm - xo
    n0 := (nm - xo + 1) / 2
    ftHigh := mk16 49 (fun i => if i ≤ nm - xo then f (xo + i) else u16 x.ftHigh i)
    m1 := f nm - f xo
    kx1 := f xo }

/-- `f_tablelow` (l.578-581). -/
def derived2 (x : Args) (xo : Nat) (f : Nat → Nat) : Args :=
  { x with
    ftLow := mk16 25 (fun k => if k = 0 then f xo
      else if k ≤ x.n0 then f (xo + (2 * k - x.n1 % 2)) else u16 x.ftLow k) }

/-- `n_q` and `f_tablenoise` (l.596-611). -/
def derived3 (x : Args) (q : Nat) : Args :=
  { x with
    nq := q
    ftNoise := mk16 6 (fun k => if k = 0 then u16 x.ftLow 0
      else if k ≤ q then u16 x.ftLow (ntemp x.n0 q k) else u16 x.ftNoise k) }

/-- `sbr_make_f_derived` after a successful `sbr_make_f_master` (`n_master = nm`,
`f_master = f`, `bs_xover_band = xo`), with `bs_limiter_bands = lb` and `sbr->sample_rate = sr`:
the values it leaves and whether it returned `0`. `m[1] = f_master[n_master] - f_master[xo]` is a
`Nat` subtraction: `f_master` is increasing, so it is the `int` value.

Abstraction: `n_q` is `FFMAX(1, lrintf(bs_noise_bands * log2f(k[2] / kx[1])))` (l.596): any
`q ≥ 1`. -/
inductive Derived (sr : Int) (lb nm xo : Nat) (f : Nat → Nat) (x : Args) : Args → Bool → Prop
  /-- `kx[1] + m[1] > 64` (l.568-572). -/
  | badTop : 64 < (derived1 x nm xo f).kx1 + (derived1 x nm xo f).m1 →
      Derived sr lb nm xo f x (derived1 x nm xo f) false
  /-- `kx[1] > 32` (l.573-576). -/
  | badKx : (derived1 x nm xo f).kx1 + (derived1 x nm xo f).m1 ≤ 64 →
      32 < (derived1 x nm xo f).kx1 → Derived sr lb nm xo f x (derived1 x nm xo f) false
  /-- `n_q > 5`: `n_q = 1`, return (l.600-604). -/
  | badNq (q : Nat) : (derived1 x nm xo f).kx1 + (derived1 x nm xo f).m1 ≤ 64 →
      (derived1 x nm xo f).kx1 ≤ 32 → 5 < q →
      Derived sr lb nm xo f x { derived2 (derived1 x nm xo f) xo f with nq := 1 } false
  /-- `sbr_hf_calc_npatches` failed (l.613-614). -/
  | badPatch (q : Nat) {y : Args} : (derived1 x nm xo f).kx1 + (derived1 x nm xo f).m1 ≤ 64 →
      (derived1 x nm xo f).kx1 ≤ 32 → 1 ≤ q → q ≤ 5 →
      Patches f sr x.k0 (f xo) (f nm - f xo) nm (derived3 (derived2 (derived1 x nm xo f) xo f) q)
        y false →
      Derived sr lb nm xo f x y false
  /-- Success: the patches, `sbr_make_f_tablelim`, `f_indexnoise = 0` (l.613-621). -/
  | ok (q : Nat) {y z : Args} : (derived1 x nm xo f).kx1 + (derived1 x nm xo f).m1 ≤ 64 →
      (derived1 x nm xo f).kx1 ≤ 32 → 1 ≤ q → q ≤ 5 →
      Patches f sr x.k0 (f xo) (f nm - f xo) nm (derived3 (derived2 (derived1 x nm xo f) xo f) q)
        y true →
      Tablelim lb y z →
      Derived sr lb nm xo f x { z with d0 := clrNoise z.d0, d1 := clrNoise z.d1 } true

/-- The hidden spectrum parameters `sbr_reset` reads: `bs_start_freq`, `bs_xover_band` (the
others feed only the abstracted band computations). -/
structure Spec where
  start : Nat
  xover : Nat

/-- `sbr_reset(ac, sbr)` (l.1113-1124), with `bs_limiter_bands = lb`: on any failure
`sbr_turnoff`. It is called only after a header in the same call (`sbr->reset` is cleared at
l.1144 / l.1218 and set only by a header), so `bs_start_freq < 16`. -/
inductive Reset (sp : Spec) (lb : Nat) (x : Args) : Args → Prop
  | badRate : sp.start < 16 → Master x.sampleRate.toInt sp.start sp.xover none none →
      Reset sp lb x x.turnoff
  | badMaster {k0 : Int} : sp.start < 16 →
      Master x.sampleRate.toInt sp.start sp.xover (some k0) none →
      Reset sp lb x { x with k0 := k0.toNat }.turnoff
  | badDerived {k0 : Int} {nm : Nat} {f : Nat → Nat} {y : Args} : sp.start < 16 →
      Master x.sampleRate.toInt sp.start sp.xover (some k0) (some (nm, f)) →
      Derived x.sampleRate.toInt lb nm sp.xover f { x with k0 := k0.toNat } y false →
      Reset sp lb x y.turnoff
  | ok {k0 : Int} {nm : Nat} {f : Nat → Nat} {y : Args} : sp.start < 16 →
      Master x.sampleRate.toInt sp.start sp.xover (some k0) (some (nm, f)) →
      Derived x.sampleRate.toInt lb nm sp.xover f { x with k0 := k0.toNat } y true →
      Reset sp lb x y

/-! ### The tables preserve the invariant -/

/-- The fields the table code leaves alone (up to `f_indexnoise`). -/
def TFrame (x y : Args) : Prop :=
  y.kx0 = x.kx0 ∧ y.m0 = x.m0 ∧ y.limGains = x.limGains ∧ y.start = x.start ∧ y.idAac = x.idAac
  ∧ y.psc = x.psc ∧ y.psh = x.psh ∧ y.anaCtx = x.anaCtx ∧ y.synCtx = x.synCtx ∧ y.fdsp = x.fdsp
  ∧ (y.d0 = x.d0 ∨ y.d0 = clrNoise x.d0) ∧ (y.d1 = x.d1 ∨ y.d1 = clrNoise x.d1)

theorem clrNoise_lo (v : DV) : (clrNoise v).idx.toNat % 2 ^ 32 ≤ 515 := by
  simp only [clrNoise, BitVec.toNat_ofNat]; omega

theorem clrNoise_hi (v : DV) : (clrNoise v).idx.toNat / 2 ^ 32 = v.idx.toNat / 2 ^ 32 := by
  simp only [clrNoise, BitVec.toNat_ofNat]
  have := v.idx.isLt; omega

/-- (`clrNoise` is unfolded first: the kernel must not compare `clrNoise v` with `v`.) -/
theorem dwf_clrNoise {v : DV} (h : DWF False v) : DWF False (clrNoise v) := by
  have e1 := clrNoise_lo v; have e2 := clrNoise_hi v
  unfold clrNoise at e1 e2 ⊢
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, -⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, e1, by rw [e2]; exact a13, a14, a15,
    False.elim⟩

theorem strict_chain {g : Nat → Nat} {n : Nat} (h : ∀ i, i < n → g i < g (i + 1)) :
    ∀ k i, i + k ≤ n → g i + k ≤ g (i + k)
  | 0, i, _ => Nat.le_refl _
  | k + 1, i, hk => by
    have := strict_chain h k i (by omega); have := h (i + k) (by omega)
    show g i + (k + 1) ≤ g (i + k + 1); omega

/-- The index into `f_master` of `f_tablelow[k]` (l.578-581). -/
def lowIx (n1 k : Nat) : Nat := if k = 0 then 0 else 2 * k - n1 % 2

theorem lowIx_le {n1 k : Nat} (hk : k ≤ (n1 + 1) / 2) : lowIx n1 k ≤ n1 := by
  unfold lowIx; split <;> omega

theorem lowIx_mono {n1 k : Nat} : lowIx n1 k ≤ lowIx n1 (k + 1) := by
  unfold lowIx; split <;> split <;> omega

theorem derived1_high {x : Args} {nm xo : Nat} {f : Nat → Nat} {i : Nat} (hi : i ≤ nm - xo)
    (h49 : nm - xo < 49) : u16 (derived1 x nm xo f).ftHigh i = f (xo + i) % 65536 := by
  unfold derived1; rw [u16_mk16 (by omega)]; simp [hi]

theorem derived2_low {x : Args} {nm xo : Nat} {f : Nat → Nat} {k : Nat}
    (hk : k ≤ (nm - xo + 1) / 2) (h49 : nm - xo ≤ 48) :
    u16 (derived2 (derived1 x nm xo f) xo f).ftLow k = f (xo + lowIx (nm - xo) k) % 65536 := by
  unfold derived2 derived1 lowIx; rw [u16_mk16 (by omega)]
  by_cases h0 : k = 0
  · subst h0; simp
  · simp [h0, hk]

theorem derived3_noise {w : Args} {q k : Nat} (hk : k ≤ q) (hq : q ≤ 5) :
    u16 (derived3 w q).ftNoise k = u16 w.ftLow (ntemp w.n0 q k) := by
  unfold derived3; rw [u16_mk16 (by omega)]
  by_cases h0 : k = 0
  · subst h0; simp only [ite_true]; exact Nat.mod_eq_of_lt (u16_lt _ _)
  · simp only [h0, hk, ite_false, ite_true]; exact Nat.mod_eq_of_lt (u16_lt _ _)

/-- **`sbr_make_f_derived`.** From a `f_master` with the properties `Master` gives: every path
keeps the unconditional bounds of the fields it writes, and success establishes `TabWF`, `kx[1]`,
`m[1]` in range and `Inv2` (`1 ≤ n[0]`, `1 ≤ num_patches`). -/
theorem derived_spec {sr : Int} {lb nm xo : Nat} {f : Nat → Nat} {x y : Args} {b : Bool} {k2 : Nat}
    (h : Derived sr lb nm xo f x y b) (hk0 : 1 ≤ x.k0) (hk032 : x.k0 ≤ 32) (hf0 : f 0 = x.k0)
    (hinc : ∀ i, i < nm → f i < f (i + 1)) (htop : f nm ≤ k2) (hk2 : k2 ≤ 64)
    (hq : k2 ≤ x.k0 + 48) (hxo : xo < nm) :
    y.n0 ≤ 24 ∧ y.n1 ≤ 48 ∧ y.nq ≤ max x.nq 5 ∧ y.nlim ≤ max x.nlim 29
    ∧ y.npatch ≤ max x.npatch 6 ∧ y.k0 = x.k0 ∧ TFrame x y
    ∧ (b = true → TabWF y ∧ y.kx1 ≤ 32 ∧ y.kx1 + y.m1 ≤ 64 ∧ y.m1 ≤ 48 ∧ y.nq ≤ 5
        ∧ y.nlim ≤ 29 ∧ y.npatch ≤ 6 ∧ 1 ≤ y.n0 ∧ 1 ≤ y.npatch) := by
  have sc := strict_chain hinc
  have hfle : ∀ i j, i ≤ j → j ≤ nm → f i + (j - i) ≤ f j := fun i j hij hj => by
    have := sc (j - i) i (by omega); rwa [Nat.add_sub_cancel' hij] at this
  have hnm48 : nm ≤ 48 := by have := hfle 0 nm (Nat.zero_le _) (Nat.le_refl _); omega
  have hf64 : ∀ i, i ≤ nm → f i ≤ 64 := fun i hi => by
    have := hfle i nm hi (Nat.le_refl _); omega
  have hfxo : x.k0 + xo ≤ f xo := by have := hfle 0 xo (Nat.zero_le _) (by omega); omega
  have hm1 : nm - xo ≤ f nm - f xo := by have := hfle xo nm (by omega) (Nat.le_refl _); omega
  have hfN : ∀ i, i ≤ nm → f i ≤ f xo + (f nm - f xo) := fun i hi => by
    have := hfle i nm hi (Nat.le_refl _); omega
  cases h with
  | badTop _ =>
    exact ⟨by dsimp only [derived1]; omega, by dsimp only [derived1]; omega,
      by dsimp only [derived1]; omega, by dsimp only [derived1]; omega,
      by dsimp only [derived1]; omega, rfl,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Or.inl rfl, Or.inl rfl⟩, nofun⟩
  | badKx _ _ =>
    exact ⟨by dsimp only [derived1]; omega, by dsimp only [derived1]; omega,
      by dsimp only [derived1]; omega, by dsimp only [derived1]; omega,
      by dsimp only [derived1]; omega, rfl,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Or.inl rfl, Or.inl rfl⟩, nofun⟩
  | badNq q _ _ _ =>
    exact ⟨by dsimp only [derived2, derived1]; omega, by dsimp only [derived2, derived1]; omega,
      by dsimp only; omega, by dsimp only [derived2, derived1]; omega,
      by dsimp only [derived2, derived1]; omega, rfl,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Or.inl rfl, Or.inl rfl⟩, nofun⟩
  | badPatch q _ _ _ h4 hp =>
    obtain ⟨p1, -, -, -, p5⟩ := patches_spec hk032 (by omega) (by omega) hfN hp
    rw [p5]
    exact ⟨by dsimp only [derived3, derived2, derived1]; omega,
      by dsimp only [derived3, derived2, derived1]; omega,
      by dsimp only [derived3]; omega, by dsimp only [derived3, derived2, derived1]; omega,
      by dsimp only; omega, rfl,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Or.inl rfl, Or.inl rfl⟩, nofun⟩
  | @ok q y z h1 h2 h3 h4 hp ht =>
    obtain ⟨p1, p2, p3, p4, p5⟩ := patches_spec hk032 (by omega) (by omega) hfN hp
    obtain ⟨b1, b2, b3⟩ := p4 rfl
    -- the fields of `y`
    have ylow : y.ftLow = (derived2 (derived1 x nm xo f) xo f).ftLow := by rw [p5] <;> rfl
    have yhigh : y.ftHigh = (derived1 x nm xo f).ftHigh := by rw [p5] <;> rfl
    have ynoise : y.ftNoise = (derived3 (derived2 (derived1 x nm xo f) xo f) q).ftNoise := by
      rw [p5] <;> rfl
    have yn0 : y.n0 = (nm - xo + 1) / 2 := by rw [p5] <;> rfl
    have yn1 : y.n1 = nm - xo := by rw [p5] <;> rfl
    have ykx : y.kx1 = f xo := by rw [p5] <;> rfl
    have ym1 : y.m1 = f nm - f xo := by rw [p5] <;> rfl
    have ynq : y.nq = q := by rw [p5] <;> rfl
    -- the derived tables
    have FH : ∀ i, i ≤ nm - xo → u16 y.ftHigh i = f (xo + i) := by
      intro i hi; rw [yhigh, derived1_high hi (by omega)]
      exact Nat.mod_eq_of_lt (by have := hf64 (xo + i) (by omega); omega)
    have FL : ∀ k, k ≤ (nm - xo + 1) / 2 → u16 y.ftLow k = f (xo + lowIx (nm - xo) k) := by
      intro k hk; rw [ylow, derived2_low hk (by omega)]
      have := lowIx_le (n1 := nm - xo) (by omega : k ≤ (nm - xo + 1) / 2)
      exact Nat.mod_eq_of_lt (by have := hf64 (xo + lowIx (nm - xo) k) (by omega); omega)
    have FN : ∀ k, k ≤ q → u16 y.ftNoise k = u16 y.ftLow (ntemp ((nm - xo + 1) / 2) q k) := by
      intro k hk; rw [ynoise, ylow, derived3_noise hk h4]; rfl
    have hlow : TabIn y.ftLow y.n0 y.kx1 (y.kx1 + y.m1) := by
      rw [yn0, ykx, ym1]
      refine ⟨fun i hi => ?_, fun i hi => ?_⟩
      · rw [FL i hi]
        have := lowIx_le (n1 := nm - xo) (by omega : i ≤ (nm - xo + 1) / 2)
        have := hfle xo (xo + lowIx (nm - xo) i) (by omega) (by omega)
        have := hfle (xo + lowIx (nm - xo) i) nm (by omega) (Nat.le_refl _); omega
      · rw [FL i (by omega), FL (i + 1) (by omega)]
        have := lowIx_le (n1 := nm - xo) (by omega : i + 1 ≤ (nm - xo + 1) / 2)
        have := lowIx_mono (n1 := nm - xo) (k := i)
        have := hfle (xo + lowIx (nm - xo) i) (xo + lowIx (nm - xo) (i + 1)) (by omega)
          (by omega); omega
    obtain ⟨t1, t2, t3, t4⟩ := tablelim_spec ht hlow (by rw [ym1]; exact b3) (by omega) p1
      (by omega)
    have yk0 : y.k0 = x.k0 := by rw [p5] <;> rfl
    have zE : z.ftLow = y.ftLow ∧ z.ftHigh = y.ftHigh ∧ z.ftNoise = y.ftNoise ∧ z.n0 = y.n0
        ∧ z.n1 = y.n1 ∧ z.kx1 = y.kx1 ∧ z.m1 = y.m1 ∧ z.nq = y.nq ∧ z.npatch = y.npatch
        ∧ z.pnum = y.pnum ∧ z.pstart = y.pstart ∧ z.k0 = y.k0 := by
      rw [t4]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12⟩ := zE
    have hlow' : TabIn y.ftLow ((nm - xo + 1) / 2) (f xo) (f xo + (f nm - f xo)) := by
      have := hlow; rwa [yn0, ykx, ym1] at this
    have lowMono : ∀ a c, a ≤ c → c ≤ (nm - xo + 1) / 2 → u16 y.ftLow a ≤ u16 y.ftLow c :=
      fun a c hac hc => by
        have := chain_le hlow'.2 (c - a) a (by omega); rwa [Nat.add_sub_cancel' hac] at this
    rw [z6, z7, ykx, ym1] at t3
    have h1' : f xo + (f nm - f xo) ≤ 64 := h1
    have h2' : f xo ≤ 32 := h2
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun _ => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · show z.n0 ≤ 24; rw [z4, yn0]; omega
    · show z.n1 ≤ 48; rw [z5, yn1]; omega
    · show z.nq ≤ max x.nq 5; rw [z8, ynq]; omega
    · show z.nlim ≤ max x.nlim 29; omega
    · show z.npatch ≤ max x.npatch 6; rw [z9]; omega
    · show z.k0 = x.k0; rw [z12, yk0]
    · rw [t4, p5]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Or.inr rfl, Or.inr rfl⟩
    · unfold TabWF; dsimp only
      rw [z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, yn0, yn1, ykx, ym1, ynq]
      refine ⟨by rw [ylow]; simp [derived2], by rw [yhigh]; simp [derived1],
        by rw [ynoise]; simp [derived3], t2, p2, p3, by omega, fun i hi => ?_, hlow'.1,
        fun i hi => ?_, t3.1, fun i hi => ?_, hlow'.2, fun i hi => ?_, t3.2, b2, ?_, ?_, ?_, h3,
        b3⟩
      · rw [FH i hi]
        have := hfle xo (xo + i) (by omega) (by omega)
        have := hfle (xo + i) nm (by omega) (Nat.le_refl _); omega
      · rw [FN i hi]; exact hlow'.1 _ (ntemp_le _ _ _)
      · rw [FH i (by omega), FH (i + 1) (by omega)]; exact hinc (xo + i) (by omega)
      · rw [FN i (by omega), FN (i + 1) hi]
        exact lowMono _ _ (ntemp_mono _ _ _) (ntemp_le _ _ _)
      · have : psum y.pnum y.npatch ≤ f nm - f xo := b3
        unfold psum at this; omega
      · rw [FN 0 (Nat.zero_le _)]
        exact (FL 0 (Nat.zero_le _)).trans (by simp [lowIx])
      · rw [FN q (Nat.le_refl _), ntemp_last _ _ h3, FL _ (Nat.le_refl _)]
        rw [show xo + lowIx (nm - xo) ((nm - xo + 1) / 2) = nm by unfold lowIx; split <;> omega]
        omega
    · show z.kx1 ≤ 32; rw [z6, ykx]; exact h2'
    · show z.kx1 + z.m1 ≤ 64; rw [z6, z7, ykx, ym1]; exact h1'
    · show z.m1 ≤ 48; rw [z7, ym1]; omega
    · show z.nq ≤ 5; rw [z8, ynq]; exact h4
    · exact t1
    · show z.npatch ≤ 6; rw [z9]; exact p1
    · show 1 ≤ z.n0; rw [z4, yn0]; omega
    · show 1 ≤ z.npatch; rw [z9]; exact b1

theorem scal_turnoff {x : Args} (h : Scal x) : Scal x.turnoff := by
  obtain ⟨a1, -, a3, -, -, a6, a7, a8, a9, a10, a11, a12⟩ := h
  exact ⟨a1, (by decide : 32 ≤ 32), a3, (by decide : 32 + 0 ≤ 64), (by decide : 0 ≤ 48), a6, a7,
    a8, a9, a10, a11, a12⟩

theorem tframe_refl (x : Args) : TFrame x x :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Or.inl rfl, Or.inl rfl⟩

/-- The facts of `Master`'s success that `derived_spec` takes, in `Nat`. -/
theorem master_ok {sr : Int} {st xo : Nat} {k0 : Int} {nm : Nat} {f : Nat → Nat} (hst : st < 16)
    (h : Master sr st xo (some k0) (some (nm, f))) :
    ∃ k2 : Nat, 1 ≤ k0.toNat ∧ k0.toNat ≤ 32 ∧ f 0 = k0.toNat ∧ (∀ i, i < nm → f i < f (i + 1))
      ∧ f nm ≤ k2 ∧ k2 ≤ 64 ∧ k2 ≤ k0.toNat + 48 ∧ xo < nm := by
  cases h with
  | @ok row k2 _ _ hr h64 hle hd hxo hf0 hinc htop =>
    have hk := k0Of_range hr hst
    have hd' : k2 - k0Of sr row st ≤ 48 := by
      revert hd; split
      · exact id
      · split <;> intro hd <;> omega
    exact ⟨k2.toNat, by omega, by omega, by omega, hinc, by omega, by omega, by omega, hxo⟩

theorem master_k0 {sr : Int} {st xo : Nat} {k0 : Int} {o : Option (Nat × (Nat → Nat))}
    (hst : st < 16) (h : Master sr st xo (some k0) o) : 1 ≤ k0.toNat ∧ k0.toNat ≤ 32 := by
  cases h with
  | fail hr => have := k0Of_range hr hst; omega
  | ok _ _ _ hr => have := k0Of_range hr hst; omega

/-- **`sbr_reset`.** It keeps the unconditional bounds; it either ends in `sbr_turnoff` or leaves
`TabWF` and `Inv2`'s conclusion; the fields of `TFrame` are kept (up to `f_indexnoise := 0`). -/
theorem reset_spec {sp : Spec} {lb : Nat} {x x' : Args} (h : Reset sp lb x x') (hs : Scal x) :
    Scal x' ∧ ∃ y, TFrame x y
      ∧ (x' = y.turnoff ∨ (x' = y ∧ TabWF y ∧ 1 ≤ y.n0 ∧ 1 ≤ y.npatch)) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := hs
  cases h with
  | badRate _ _ =>
    exact ⟨scal_turnoff ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩, x, tframe_refl x,
      Or.inl rfl⟩
  | @badMaster k0 hst hm =>
    have := master_k0 hst hm
    exact ⟨⟨a1, (by decide : 32 ≤ 32), a3, (by decide : 32 + 0 ≤ 64), (by decide : 0 ≤ 48),
      this.2, a7, a8, a9, a10, a11, a12⟩, { x with k0 := k0.toNat },
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Or.inl rfl, Or.inl rfl⟩, Or.inl rfl⟩
  | @badDerived k0 nm f y hst hm hd =>
    obtain ⟨k2, b1, b2, b3, b4, b5, b6, b7, b8⟩ := master_ok hst hm
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, -⟩ := derived_spec hd b1 b2 b3 b4 b5 b6 b7 b8
    have t1 := c7.1; have t2 := c7.2.1; have t3 := c7.2.2.1
    dsimp only at c3 c4 c5
    rw [Nat.max_eq_right a10] at c3; rw [Nat.max_eq_right a11] at c4
    rw [Nat.max_eq_right a12] at c5
    refine ⟨⟨by rw [t1]; exact a1, (by decide : 32 ≤ 32), by rw [t1, t2]; exact a3,
      (by decide : 32 + 0 ≤ 64), (by decide : 0 ≤ 48), by rw [c6]; exact b2, by rw [t3]; exact a7,
      c1, c2, c3, c4, c5⟩, y, c7, Or.inl rfl⟩
  | @ok k0 nm f y hst hm hd =>
    obtain ⟨k2, b1, b2, b3, b4, b5, b6, b7, b8⟩ := master_ok hst hm
    obtain ⟨c1, c2, -, -, -, c6, c7, c8⟩ := derived_spec hd b1 b2 b3 b4 b5 b6 b7 b8
    obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9⟩ := c8 rfl
    have t1 := c7.1; have t2 := c7.2.1; have t3 := c7.2.2.1
    exact ⟨⟨by rw [t1]; exact a1, d2, by rw [t1, t2]; exact a3, d3, d4, by rw [c6]; exact b2,
      by rw [t3]; exact a7, c1, c2, d5, d6, d7⟩, _, c7, Or.inr ⟨rfl, d1, d8, d9⟩⟩

/-! ## The parser's entry points

The state of the model is `Args` plus `Hid`, the bytes of the decoder state outside `Args` that
decide which paths are taken: `spectrum_params.bs_start_freq`, `bs_xover_band` and
`bs_limiter_bands`. The other fields of `SpectrumParameters` only feed the abstracted band
computation (`Master`) or the change test of the header, which the model makes a free choice. -/

/-- **I2**: a started decoder has `n[0] ≥ 1` and `num_patches ≥ 1`. -/
def Inv2 (x : Args) : Prop := x.start ≠ 0 → 1 ≤ x.n0 ∧ 1 ≤ x.npatch

/-- The `sbr_make_f_tablelim` of a header that did not ask for a reset (l.243-244,
l.1253-1254), with the new and old `bs_limiter_bands`. -/
inductive HdrLim (lb old : Nat) (x : Args) : Args → Prop
  | keep : (lb = old ∨ x.reset ≠ 0) → HdrLim lb old x x
  | lim {y : Args} : lb ≠ old → x.reset = 0 → Tablelim lb x y → HdrLim lb old x y

/-- A header: `read_sbr_header(sbr, gb, usac)` (l.188-247) or, for USAC, also
`copy_usac_default_header` with the change test (l.1241-1254); both are followed by `start = 1`
(l.197, l.1259). `s`, `xo`, `lb`, `lg`: the new `bs_start_freq` (4 bits, l.207; the USAC default
header's comes from the 4-bit field of the configuration), `bs_xover_band` (3 bits, l.211; not
written for USAC), `bs_limiter_bands`, `bs_limiter_gains` (2 bits, l.232-233, l.237-238;
the configuration's for the default header). `rd` is `ready_for_dequant`: `0` (l.198) or kept
(the default header).

Abstraction: `chg` is the result of the `memcmp` of `SpectrumParameters` (l.228, l.1249), a free
choice except that a new `bs_start_freq` forces it. -/
inductive Header (usac : Bool) : St → St → Prop
  | mk {x : Args} {h : Hid} {y : Args} (s xo lb lg : Nat) (rd interp sm : BitVec 32) (chg : Bool) :
      s < 16 → (usac = false → xo < 8) → (usac = true → xo = h.xover) → lb < 4 → lg < 4 →
      (rd = 0 ∨ rd = x.ready) → (s ≠ h.start → chg = true) →
      HdrLim lb h.lb
        { x with start := 1, ready := rd, reset := if chg then 1 else x.reset, limGains := lg,
                 interpol := interp, smooth := sm } y →
      Header usac (x, h) (y, { start := s, xover := xo, lb := lb })

/-- An optional header. -/
def HdrOpt (usac : Bool) (s s' : St) : Prop := s' = s ∨ Header usac s s'

/-- `if (sbr->reset) sbr_reset(ac, sbr)` (l.1165-1166, l.1267-1268). -/
inductive ResetS : St → St → Prop
  | skip {x : Args} {h : Hid} : x.reset = 0 → ResetS (x, h) (x, h)
  | run {x : Args} {h : Hid} {y : Args} : x.reset ≠ 0 → Reset ⟨h.start, h.xover⟩ h.lb x y →
      ResetS (x, h) (y, if y.start = 0 then h.turnoff else h)

/-- `read_sbr_invf` (l.827-835): `bs_invf_mode[1] = bs_invf_mode[0]`, then `n_q` 2-bit values
`vals i % 4` into `bs_invf_mode[0]`. -/
def invfRead (nq : Nat) (v : DV) (vals : Nat → Nat) : DV :=
  { v with invf := mk 10 (fun i => if i < 5 then (if i < nq then UInt8.ofNat (vals i % 4)
      else old v.invf i) else old v.invf (i - 5)) }

/-- The two `memcpy` of a coupled pair (l.1033-1034, l.1302-1305): `bs_invf_mode[1]` of channel 1
from its `bs_invf_mode[0]`, its `bs_invf_mode[0]` from channel 0's. -/
def invfCouple (d0 d1 : DV) : DV :=
  { d1 with invf := mk 10 (fun i => if i < 5 then old d0.invf i else old d1.invf (i - 5)) }

/-- The channel element (`read_sbr_single_channel_element`, l.993-1015;
`read_sbr_channel_pair_element`, l.1017-1067; the USAC ones, l.1272-1350): the values it leaves
and whether it returned `0`. `read_sbr_dtdf`, `read_sbr_envelope`, `read_sbr_noise` and the
harmonics write no field of `Args`; the outcome `b` of the envelope and noise reads is a free
choice (abstraction: their checks, l.874-905, 943-955, are not transcribed). -/
inductive Elem (usac cpe : Bool) (x : Args) : Args → Bool → Prop
  | sceFail {w : DV} : cpe = false → Grid usac x.d0 w false →
      Elem usac cpe x { x with d0 := w } false
  | sce {w : DV} (vals : Nat → Nat) (b : Bool) : cpe = false → Grid usac x.d0 w true →
      Elem usac cpe x { x with d0 := invfRead x.nq w vals } b
  | cplFail {w : DV} : cpe = true → Grid usac x.d0 w false →
      Elem usac cpe x { x with coupling := 1, d0 := w } false
  | cpl {w : DV} (vals : Nat → Nat) (b : Bool) : cpe = true → Grid usac x.d0 w true →
      Elem usac cpe x { x with coupling := 1, d0 := invfRead x.nq w vals,
                               d1 := invfCouple (invfRead x.nq w vals) (copyGrid x.d1 w) } b
  | indFail0 {w : DV} : cpe = true → Grid usac x.d0 w false →
      Elem usac cpe x { x with coupling := 0, d0 := w } false
  | indFail1 {w w1 : DV} : cpe = true → Grid usac x.d0 w true → Grid usac x.d1 w1 false →
      Elem usac cpe x { x with coupling := 0, d0 := w, d1 := w1 } false
  | ind {w w1 : DV} (vals vals1 : Nat → Nat) (b : Bool) : cpe = true → Grid usac x.d0 w true →
      Grid usac x.d1 w1 true →
      Elem usac cpe x { x with coupling := 0, d0 := invfRead x.nq w vals,
                               d1 := invfRead x.nq w1 vals1 } b

/-! ## `ff_ps_read_data` (`PC`:133-289)

The model reads `ps->common` through the fields `PsWF` reads (`PSF`); `View c f` says the 764
bytes `c` hold the fields `f` at the offsets of `PsWF`. The other fields of `PSCommonContext`
(`enable_icc`, `nr_icc_par`, `enable_ipdopd`, `enable_ext`, ...) are free choices of the model at
each call (an over-approximation: the invariant holds for each of their values). -/

/-- The fields of `PSCommonContext` that `PsWF` reads. -/
structure PSF where
  start : Int
  eiid : Int
  quant : Int
  nriid : Int
  neo : Int
  ne : Int
  is34 : Int
  border : Nat → Int
  iid : Nat → Nat → Int
  icc : Nat → Nat → Int
  ipd : Nat → Nat → Int
  opd : Nat → Nat → Int

/-- `c` holds `f`: `start` 0, `enable_iid` 4, `iid_quant` 8, `nr_iid_par` 12, `num_env_old` 40,
`num_env` 44, `border_position[6]` 52, `iid_par`/`icc_par`/`ipd_par`/`opd_par` 76/246/416/586,
`is34bands` 756. -/
def View (c : List UInt8) (f : PSF) : Prop :=
  c.length = 764 ∧ i32 c 0 = f.start ∧ i32 c 4 = f.eiid ∧ i32 c 8 = f.quant ∧ i32 c 12 = f.nriid
  ∧ i32 c 40 = f.neo ∧ i32 c 44 = f.ne ∧ i32 c 756 = f.is34
  ∧ (∀ e, e < 6 → i32 c (52 + 4 * e) = f.border e)
  ∧ (∀ e b, e < 5 → b < 34 → i8 c (76 + 34 * e + b) = f.iid e b
      ∧ i8 c (246 + 34 * e + b) = f.icc e b ∧ i8 c (416 + 34 * e + b) = f.ipd e b
      ∧ i8 c (586 + 34 * e + b) = f.opd e b)

/-- `PsWF`'s clauses on `ps->common`, on the fields. -/
def PsWFf (f : PSF) : Prop :=
  (f.is34 = 0 ∨ f.is34 = 1) ∧ (0 ≤ f.ne ∧ f.ne ≤ 5) ∧ (0 ≤ f.neo ∧ f.neo ≤ 5)
  ∧ (f.quant = 0 ∨ f.quant = 1)
  ∧ (∀ e < 5, ∀ b < 34, 0 ≤ f.icc e b ∧ f.icc e b ≤ 7)
  ∧ (∀ e < 5, ∀ b < 34, 0 ≤ f.ipd e b ∧ f.ipd e b ≤ 7 ∧ 0 ≤ f.opd e b ∧ f.opd e b ≤ 7)
  ∧ (f.start ≠ 0 →
      1 ≤ f.ne ∧ f.border 0 = -1
      ∧ (∀ e : Nat, (e : Int) < f.ne → f.border e ≤ f.border (e + 1))
      ∧ f.border f.ne.toNat = 31
      ∧ (f.eiid ≠ 0 → f.nriid = 10 ∨ f.nriid = 20 ∨ f.nriid = 34)
      ∧ (∀ e : Nat, (e : Int) < f.ne → ∀ b : Nat, b < 34 → (f.eiid = 0 ∨ (b : Int) < f.nriid) →
          -(7 + 8 * f.quant) ≤ f.iid e b ∧ f.iid e b ≤ 7 + 8 * f.quant))

/-- `PsWF`'s clauses on the phase histories. -/
def HistWF (h : List UInt8) : Prop :=
  h.length = 68 ∧ (∀ b < 34, 0 ≤ i8 h b ∧ i8 h b ≤ 63 ∧ 0 ≤ i8 h (34 + b) ∧ i8 h (34 + b) ≤ 63)

theorem psWF_to {c h : List UInt8} {f : PSF} (hv : View c f) (hw : PsWF c h) :
    PsWFf f ∧ HistWF h := by
  obtain ⟨-, v0, v4, v8, v12, v40, v44, v756, vb, va⟩ := hv
  obtain ⟨-, hl, w1, w2, w2', w3, w4, w5, w6, w7⟩ := hw
  rw [v756] at w1; rw [v44] at w2 w7; rw [v40] at w2'; rw [v8] at w3 w7; rw [v0] at w7
  rw [v4, v12] at w7
  refine ⟨⟨w1, w2, w2', w3, fun e he b hb => ?_, fun e he b hb => ?_, fun hs => ?_⟩, hl, w6⟩
  · rw [← (va e b he hb).2.1]; exact w4 e he b hb
  · rw [← (va e b he hb).2.2.1, ← (va e b he hb).2.2.2]; exact w5 e he b hb
  · obtain ⟨x1, x2, x3, x4, x5, x6⟩ := w7 hs
    refine ⟨x1, ?_, fun e he => ?_, ?_, x5, fun e he b hb hc => ?_⟩
    · rw [← vb 0 (by omega)]; exact x2
    · rw [← vb e (by omega), ← vb (e + 1) (by omega)]; exact x3 e he
    · rw [← vb _ (by omega)]; exact x4
    · have := x6 e he b hb hc
      rw [(va e b (by omega) hb).1] at this; exact this

theorem psWF_of {c h : List UInt8} {f : PSF} (hv : View c f) (hw : PsWFf f) (hh : HistWF h) :
    PsWF c h := by
  obtain ⟨vl, v0, v4, v8, v12, v40, v44, v756, vb, va⟩ := hv
  obtain ⟨w1, w2, w2', w3, w4, w5, w7⟩ := hw
  unfold PsWF
  rw [v756, v44, v40, v8, v0, v4, v12]
  refine ⟨vl, hh.1, w1, w2, w2', w3, fun e he b hb => ?_, fun e he b hb => ?_, hh.2,
    fun hs => ?_⟩
  · rw [(va e b he hb).2.1]; exact w4 e he b hb
  · rw [(va e b he hb).2.2.1, (va e b he hb).2.2.2]; exact w5 e he b hb
  · obtain ⟨x1, x2, x3, x4, x5, x6⟩ := w7 hs
    refine ⟨x1, ?_, fun e he => ?_, ?_, x5, fun e he b hb hc => ?_⟩
    · rw [vb 0 (by omega)]; exact x2
    · rw [vb e (by omega), vb (e + 1) (by omega)]; exact x3 e he
    · rw [vb _ (by omega)]; exact x4
    · rw [(va e b (by omega) hb).1]; exact x6 e he b hb hc

/-- `num_env_tab[frame_class][k]` (`PC`:28-31). -/
def numEnvTab (fc : Bool) (k : Nat) : Int :=
  (if fc then [1, 2, 3, 4] else [0, 1, 2, 4]).getD k 0

/-- `nr_iidicc_par_tab[m]` (`PC`:33-35). -/
def nrTab (m : Nat) : Int := [10, 20, 34, 10, 20, 34].getD m 0

/-- `ff_log2_tab[n]` for `n ≤ 4`. -/
def log2Tab (n : Int) : Nat := if n ≤ 1 then 0 else if n ≤ 3 then 1 else 2

/-- The fixed borders `(e * numQMFSlots >> ff_log2_tab[num_env]) - 1` (`PC`:183-184). -/
def fixBorder (ne : Int) (e : Nat) : Int := (e * 32 / 2 ^ log2Tab ne : Nat) - 1

/-- A table read by `read_iid_data`/`read_icc_data` (`PC`:76-105) for envelopes `e < ne` and bands
`b < num`: the entries read satisfy the check `P` (else the parse fails), the others keep their
values. Abstraction: the values (VLC decode, delta sums) are any that pass the check. -/
def TabRead (old new : Nat → Nat → Int) (ne num : Int) (P : Int → Prop) : Prop :=
  ∀ (e b : Nat), ((e : Int) < ne ∧ (b : Int) < num → P (new e b))
    ∧ (¬ ((e : Int) < ne ∧ (b : Int) < num) → new e b = old e b)

/-- Copy row `src` to row `dst` (the `memcpy` of `PC`:230-237). -/
def rowCopy (t : Nat → Nat → Int) (dst src : Nat) : Nat → Nat → Int :=
  fun e b => if e = dst then t src b else t e b

/-- Whether the envelope fix-up runs (`PC`:224). -/
def psFix (ne0 : Int) (bd : Nat → Int) : Bool := decide (ne0 = 0 ∨ bd ne0.toNat < 31)

/-- Its source envelope (`PC`:226). -/
def psSrc (ne0 neOld : Int) : Int := if 0 < ne0 then ne0 - 1 else neOld - 1

/-- Whether it copies (`PC`:228). -/
def psCp (ne0 neOld : Int) (bd : Nat → Int) : Bool :=
  psFix ne0 bd && decide (0 ≤ psSrc ne0 neOld) && decide (psSrc ne0 neOld ≠ ne0)

/-- The table after the fix-up's copy, if enabled. -/
def fixTab (on : Bool) (ne0 neOld : Int) (bd : Nat → Int) (t : Nat → Nat → Int) :
    Nat → Nat → Int :=
  if on && psCp ne0 neOld bd then rowCopy t ne0.toNat (psSrc ne0 neOld).toNat else t

/-- `ff_ps_read_data(logctx, gb, ps, bits_left)`: the fields of `ps->common` it leaves. -/
inductive PsRead (f : PSF) : PSF → Prop
  /-- A path to `err` (`PC`:281-288): `start = 0`, the four tables cleared, and the fields written
  before the failure with any value they can hold there: `enable_iid`, `nr_iid_par`, `iid_quant`
  from a header (`PC`:144-154), `num_env_old`, `num_env` (`PC`:170-171, 256),
  `border_position[]`, `is34bands` (`PC`:263, before the `bits_left` check). -/
  | err (eiid quant nriid neo ne is34 : Int) (bd : Nat → Int) :
      (quant = f.quant ∨ quant = 0 ∨ quant = 1) → (neo = f.neo ∨ neo = f.ne) →
      (0 ≤ ne ∧ ne ≤ 5) → (is34 = f.is34 ∨ is34 = 0 ∨ is34 = 1) →
      PsRead f { start := 0, eiid := eiid, quant := quant, nriid := nriid, neo := neo, ne := ne,
                 is34 := is34, border := bd, iid := fun _ _ => 0, icc := fun _ _ => 0,
                 ipd := fun _ _ => 0, opd := fun _ _ => 0 }
  /-- Success. `hdr`: `enable_ps_header`; `fc`, `k`: `frame_class` and the 2-bit index
  (`num_env = num_env_tab[fc][k]`); `eicc`, `nricc`: `enable_icc`, `nr_icc_par`; `eipd`:
  `enable_ipdopd`. The extension (`PC`:204-219, 111-131) may rewrite `ipd_par`/`opd_par` entries
  with masked (`& 7`) values. -/
  | ok (hdr : Bool) (eiid quant nriid : Int) (fc : Bool) (k : Nat) (bd : Nat → Int)
      (iid1 icc1 ipd1 opd1 : Nat → Nat → Int) (eicc eipd : Bool) (nricc is34 : Int) :
      (hdr = false → eiid = f.eiid ∧ quant = f.quant ∧ nriid = f.nriid) →
      (hdr = true → (eiid = 0 ∧ quant = f.quant ∧ nriid = f.nriid)
        ∨ (eiid = 1 ∧ ∃ m, m ≤ 5 ∧ nriid = nrTab m ∧ quant = if 2 < m then 1 else 0)) →
      k < 4 → bd 0 = -1 →
      (fc = true → ∀ e : Nat, 1 ≤ e → (e : Int) ≤ numEnvTab fc k →
        0 ≤ bd e ∧ bd e ≤ 31 ∧ bd (e - 1) ≤ bd e) →
      (fc = false → ∀ e : Nat, 1 ≤ e → (e : Int) ≤ numEnvTab fc k →
        bd e = fixBorder (numEnvTab fc k) e) →
      (eiid ≠ 0 → TabRead f.iid iid1 (numEnvTab fc k) nriid
        (fun v => -(7 + 8 * quant) ≤ v ∧ v ≤ 7 + 8 * quant)) →
      (eiid = 0 → ∀ e b, iid1 e b = 0) →
      (eicc = true → TabRead f.icc icc1 (numEnvTab fc k) nricc (fun v => 0 ≤ v ∧ v ≤ 7)) →
      (eicc = false → ∀ e b, icc1 e b = 0) →
      (∀ e b, ipd1 e b = f.ipd e b ∨ (0 ≤ ipd1 e b ∧ ipd1 e b ≤ 7)) →
      (∀ e b, opd1 e b = f.opd e b ∨ (0 ≤ opd1 e b ∧ opd1 e b ≤ 7)) →
      -- the `iid_par` check of the fix-up (`PC`:240-247); the `icc_par` check (`PC`:248-255) is
      -- not modelled (more paths succeed in the model)
      (psFix (numEnvTab fc k) bd = true → eiid ≠ 0 → ∀ b : Nat, (b : Int) < nriid → b < 34 →
        -(7 + 8 * quant) ≤ fixTab (decide (eiid ≠ 0)) (numEnvTab fc k) f.ne bd iid1
            (numEnvTab fc k).toNat b
          ∧ fixTab (decide (eiid ≠ 0)) (numEnvTab fc k) f.ne bd iid1 (numEnvTab fc k).toNat b
            ≤ 7 + 8 * quant) →
      -- `is34bands` (`PC`:261-264)
      ((eiid ≠ 0 ∨ eicc = true) →
        is34 = if (eiid ≠ 0 ∧ nriid = 34) ∨ (eicc = true ∧ nricc = 34) then 1 else 0) →
      (¬ (eiid ≠ 0 ∨ eicc = true) → is34 = f.is34) →
      PsRead f
        { start := if hdr then 1 else f.start, eiid := eiid, quant := quant, nriid := nriid,
          neo := f.ne,
          ne := if psFix (numEnvTab fc k) bd then numEnvTab fc k + 1 else numEnvTab fc k,
          is34 := is34,
          border := if psFix (numEnvTab fc k) bd then
              fun e => if e = (numEnvTab fc k).toNat + 1 then 31 else bd e
            else bd,
          iid := fixTab (decide (eiid ≠ 0)) (numEnvTab fc k) f.ne bd iid1,
          icc := fixTab eicc (numEnvTab fc k) f.ne bd icc1,
          ipd := if eipd then fixTab eipd (numEnvTab fc k) f.ne bd ipd1 else fun _ _ => 0,
          opd := if eipd then fixTab eipd (numEnvTab fc k) f.ne bd opd1 else fun _ _ => 0 }

theorem numEnvTab_range (fc : Bool) (k : Nat) : 0 ≤ numEnvTab fc k ∧ numEnvTab fc k ≤ 4 := by
  unfold numEnvTab
  rcases k with _ | _ | _ | _ | k <;> cases fc <;> simp

theorem numEnvTab_false (k : Nat) :
    numEnvTab false k = 0 ∨ numEnvTab false k = 1 ∨ numEnvTab false k = 2
      ∨ numEnvTab false k = 4 := by
  unfold numEnvTab
  rcases k with _ | _ | _ | _ | k <;> simp

theorem fixBorder_le {N : Int} (hN : N = 0 ∨ N = 1 ∨ N = 2 ∨ N = 4) {e : Nat} (he : (e : Int) ≤ N) :
    fixBorder N e ≤ 31 := by
  unfold fixBorder log2Tab
  rcases hN with h | h | h | h <;> subst h <;> simp <;> omega

theorem fixBorder_ge (N : Int) (e : Nat) : -1 ≤ fixBorder N e := by
  show -1 ≤ ((e * 32 / 2 ^ log2Tab N : Nat) : Int) - 1
  generalize (e * 32 / 2 ^ log2Tab N : Nat) = n; omega

theorem fixBorder_mono (N : Int) (e : Nat) : fixBorder N e ≤ fixBorder N (e + 1) := by
  unfold fixBorder
  have : e * 32 / 2 ^ log2Tab N ≤ (e + 1) * 32 / 2 ^ log2Tab N :=
    Nat.div_le_div_right (by omega)
  omega

/-- The borders a successful read leaves before the fix-up. -/
theorem ps_borders {fc : Bool} {k : Nat} {bd : Nat → Int} (hb0 : bd 0 = -1)
    (hbt : fc = true → ∀ e : Nat, 1 ≤ e → (e : Int) ≤ numEnvTab fc k →
        0 ≤ bd e ∧ bd e ≤ 31 ∧ bd (e - 1) ≤ bd e)
    (hbf : fc = false → ∀ e : Nat, 1 ≤ e → (e : Int) ≤ numEnvTab fc k →
        bd e = fixBorder (numEnvTab fc k) e) :
    (∀ e : Nat, (e : Int) ≤ numEnvTab fc k → bd e ≤ 31)
    ∧ (∀ e : Nat, (e : Int) < numEnvTab fc k → bd e ≤ bd (e + 1)) := by
  constructor
  · intro e he
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h; omega
    cases fc
    · rw [hbf rfl e h he]; exact fixBorder_le (numEnvTab_false k) he
    · exact (hbt rfl e h he).2.1
  · intro e he
    cases fc
    · rw [hbf rfl (e + 1) (by omega) (by omega)]
      rcases Nat.eq_zero_or_pos e with h | h
      · subst h; rw [hb0]; exact fixBorder_ge _ _
      · rw [hbf rfl e h (by omega)]; exact fixBorder_mono _ _
    · have := (hbt rfl (e + 1) (by omega) (by omega)).2.2
      simpa using this

theorem fixTab_ne {on : Bool} {N neo : Int} {bd : Nat → Int} {t : Nat → Nat → Int} {e b : Nat}
    (h : e ≠ N.toNat) : fixTab on N neo bd t e b = t e b := by
  unfold fixTab rowCopy; split <;> simp [h]

theorem fixTab_all (P : Int → Prop) (on : Bool) {N neo : Int} (bd : Nat → Int)
    {t : Nat → Nat → Int} (hN : N ≤ 4) (hneo : neo ≤ 5)
    (h : ∀ e < 5, ∀ b < 34, P (t e b)) : ∀ e < 5, ∀ b < 34, P (fixTab on N neo bd t e b) := by
  intro e he b hb
  unfold fixTab
  split
  · rename_i hc
    unfold rowCopy; split
    · apply h _ _ b hb
      simp only [Bool.and_eq_true, psCp, decide_eq_true_eq] at hc
      have := hc.2.1; unfold psSrc at this ⊢; split <;> omega
    · exact h e he b hb
  · exact h e he b hb

theorem tabRead_all {old new : Nat → Nat → Int} {ne num : Int} {P : Int → Prop}
    (hr : TabRead old new ne num P) (ho : ∀ e < 5, ∀ b < 34, P (old e b)) :
    ∀ e < 5, ∀ b < 34, P (new e b) := by
  intro e he b hb
  by_cases hc : (e : Int) < ne ∧ (b : Int) < num
  · exact (hr e b).1 hc
  · rw [(hr e b).2 hc]; exact ho e he b hb

theorem nrTab_mem {m : Nat} (hm : m ≤ 5) : nrTab m = 10 ∨ nrTab m = 20 ∨ nrTab m = 34 := by
  unfold nrTab; rcases m with _ | _ | _ | _ | _ | _ | m <;> simp; omega

/-- `ff_ps_read_data` keeps `PsWF`'s clauses on `ps->common`. -/
theorem psread_wf {f f' : PSF} (hw : PsWFf f) (hr : PsRead f f') : PsWFf f' := by
  obtain ⟨w1, w2, w2', w3, w4, w5, w7⟩ := hw
  cases hr with
  | err eiid quant nriid neo ne is34 bd hq hneo hne his =>
    refine ⟨?_, hne, ?_, ?_, fun _ _ _ _ => by simp, fun _ _ _ _ => by simp, fun h => absurd rfl h⟩
    all_goals dsimp only; omega
  | ok hdr eiid quant nriid fc k bd iid1 icc1 ipd1 opd1 eicc eipd nricc is34 h1 h2 hk hb0 hbt hbf
      hiid hiid0 hicc hicc0 hipd hopd hfix his1 his2 =>
    have hN := numEnvTab_range fc k
    obtain ⟨ba, bm⟩ := ps_borders hb0 hbt hbf
    have hq : quant = 0 ∨ quant = 1 := by
      cases hdr
      · exact (h1 rfl).2.1 ▸ w3
      · rcases h2 rfl with ⟨-, h, -⟩ | ⟨-, m, -, -, h⟩
        · exact h ▸ w3
        · rw [h]; split <;> simp
    refine ⟨?_, ?_, w2, hq, ?_, ?_, fun hs => ⟨?_, ?_, fun e he => ?_, ?_, ?_, ?_⟩⟩
    · by_cases hc : eiid ≠ 0 ∨ eicc = true
      · dsimp only; rw [his1 hc]; split <;> omega
      · exact his2 hc ▸ w1
    · dsimp only; split <;> omega
    · dsimp only
      cases eicc
      · exact fixTab_all (fun v => 0 ≤ v ∧ v ≤ 7) false bd hN.2 w2.2
          (fun e _ b _ => by rw [hicc0 rfl]; simp)
      · exact fixTab_all (fun v => 0 ≤ v ∧ v ≤ 7) true bd hN.2 w2.2
          (tabRead_all (hicc rfl) w4)
    · dsimp only
      have hp : ∀ e < 5, ∀ b < 34, (0 ≤ ipd1 e b ∧ ipd1 e b ≤ 7) ∧ (0 ≤ opd1 e b ∧ opd1 e b ≤ 7) :=
        fun e he b hb => ⟨(hipd e b).elim (fun h => h ▸ ⟨(w5 e he b hb).1, (w5 e he b hb).2.1⟩) id,
          (hopd e b).elim (fun h => h ▸ ⟨(w5 e he b hb).2.2.1, (w5 e he b hb).2.2.2⟩) id⟩
      intro e he b hb
      cases eipd
      · simp
      · have a1 := fixTab_all (fun v => 0 ≤ v ∧ v ≤ 7) true bd hN.2 w2.2
          (fun e he b hb => (hp e he b hb).1) e he b hb
        have a2 := fixTab_all (fun v => 0 ≤ v ∧ v ≤ 7) true bd (t := opd1) hN.2 w2.2
          (fun e he b hb => (hp e he b hb).2) e he b hb
        simp only [ite_true]
        exact ⟨a1.1, a1.2, a2.1, a2.2⟩
    -- under `start ≠ 0`
    · dsimp only; split
      · omega
      · rename_i hc; simp only [psFix, decide_eq_true_eq, not_or] at hc; omega
    · dsimp only; split
      · simp only [show (0 : Nat) ≠ (numEnvTab fc k).toNat + 1 by omega, ite_false]; exact hb0
      · exact hb0
    · dsimp only at he ⊢; split
      · rename_i hc; simp only [hc, ite_true] at he
        have h0 : e ≠ (numEnvTab fc k).toNat + 1 := by omega
        simp only [h0, ite_false]
        by_cases he' : (e : Int) < numEnvTab fc k
        · have : e + 1 ≠ (numEnvTab fc k).toNat + 1 := by omega
          simp only [this, ite_false]; exact bm e he'
        · simp only [show e + 1 = (numEnvTab fc k).toNat + 1 by omega, ite_true]
          exact ba e (by omega)
      · rename_i hc; simp only [hc] at he; exact bm e he
    · dsimp only; split
      · simp only [show (numEnvTab fc k + 1).toNat = (numEnvTab fc k).toNat + 1 by omega, ite_true]
      · rename_i hc
        simp only [psFix, decide_eq_true_eq, not_or] at hc
        have := ba (numEnvTab fc k).toNat (by omega)
        omega
    · dsimp only at hs ⊢; intro he
      cases hdr
      · obtain ⟨a, -, c⟩ := h1 rfl
        try simp only [Bool.false_eq_true, ite_false] at hs
        rw [c]; exact (w7 hs).2.2.2.2.1 (a ▸ he)
      · rcases h2 rfl with ⟨h, -, -⟩ | ⟨-, m, hm, h, -⟩
        · exact absurd h he
        · rw [h]; exact nrTab_mem hm
    · dsimp only; intro e he b hb hc
      by_cases hz : eiid = 0
      · have : decide (eiid ≠ 0) = false := by simp [hz]
        rw [this]; unfold fixTab; simp only [Bool.false_and, Bool.false_eq_true, ite_false]
        rw [hiid0 hz]; omega
      · have hb' : (b : Int) < nriid := hc.resolve_left hz
        by_cases he' : (e : Int) < numEnvTab fc k
        · rw [fixTab_ne (by omega)]
          exact (hiid hz e b).1 ⟨he', hb'⟩
        · split at he
          · rename_i hf
            have : e = (numEnvTab fc k).toNat := by omega
            subst this
            exact hfix hf hz b hb' hb
          · omega

/-- `read_sbr_extension` (l.966-991). -/
inductive ExtS (x : Args) : Args → Prop
  /-- `ff_ps_read_data` (l.977, `PsRead`), which also writes `ac->avctx->profile` (caller memory,
  `R`). -/
  | ps (c : List UInt8) (R : Mem 64 → Prop) (f f' : PSF) : View x.psc f → PsRead f f' →
      View c f' → ExtS x { x with psc := c, R := R }
  /-- The PS extension with `ac->oc[1].m4ac.ps` clear (l.972-975), or another extension
  (l.983-989): the bits are skipped. -/
  | skip : ExtS x x

/-- Reflexive-transitive closure. -/
inductive Star {α : Type} (r : α → α → Prop) : α → α → Prop
  | refl (a : α) : Star r a a
  | step {a b c : α} : r a b → Star r b c → Star r a c

/-- `read_sbr_data(ac, sbr, gb, id_aac)` (l.1069-1111): `id_aac` is `TYPE_SCE = 0`,
`TYPE_CPE = 1`, `TYPE_CCE = 2` or another type (turnoff); a failed element ends in
`sbr_turnoff`; after a successful one, the extensions. -/
inductive Data (id : BitVec 32) : St → St → Prop
  | fail {x : Args} {h : Hid} {y : Args} (cpe : Bool) :
      (cpe = false ∧ (id = 0 ∨ id = 2) ∨ cpe = true ∧ id = 1) →
      Elem false cpe { x with idAac := id, ready := 1 } y false → Data id (x, h) (stOff (y, h))
  | bad {x : Args} {h : Hid} : id ≠ 0 → id ≠ 1 → id ≠ 2 →
      Data id (x, h) (stOff ({ x with idAac := id, ready := 1 }, h))
  | ok {x : Args} {h : Hid} {y z : Args} (cpe : Bool) :
      (cpe = false ∧ (id = 0 ∨ id = 2) ∨ cpe = true ∧ id = 1) →
      Elem false cpe { x with idAac := id, ready := 1 } y true → Star ExtS y z →
      Data id (x, h) (z, h)

/-- The prologue of `ff_aac_sbr_decode_extension` (l.1144-1159): `reset = 0`, `sample_rate`
and `ext_sample_rate` set if `0` (to `sr`, `er`), `kx[0] = kx[1]`, `m[0] = m[1]`,
`kx_and_m_pushed = 1`. -/
def extPro (x : Args) (sr er : BitVec 32) : Args :=
  { x with reset := 0, sampleRate := if x.sampleRate = 0 then sr else x.sampleRate,
           extRate := if x.extRate = 0 then er else x.extRate, kx0 := x.kx1, m0 := x.m1,
           pushed := 1 }

/-- `ff_aac_sbr_decode_extension(ac, che, gb, crc, cnt, id_aac)` (l.1134-1180): the prologue, an
optional header, the reset, `read_sbr_data` if started, and `sbr_turnoff` if more bytes were read
than `cnt` (`long`, a free choice). -/
inductive DecExt (id : BitVec 32) : St → St → Prop
  | mk {x : Args} {h : Hid} {s1 s2 s3 : St} (sr er : BitVec 32) (long : Bool) :
      HdrOpt false (extPro x sr er, h) s1 → ResetS s1 s2 →
      (s2.1.start ≠ 0 → Data id s2 s3) → (s2.1.start = 0 → s3 = s2) →
      DecExt id (x, h) (if long then stOff s3 else s3)

/-- The prologue of `ff_aac_sbr_decode_usac_data` (l.1218-1222): `reset = 0`,
`sample_rate = ext_sample_rate`, `id_aac` from `sbr_ch`. -/
def usacPro (x : Args) (cpe : Bool) : Args :=
  { x with reset := 0, sampleRate := x.extRate, idAac := if cpe then 1 else 0 }

/-- `kx[0] = kx[1]`, `m[0] = m[1]`, `kx_and_m_pushed = 1` (l.1263-1265). -/
def push1 (x : Args) : Args := { x with kx0 := x.kx1, m0 := x.m1, pushed := 1 }

/-- `ff_aac_sbr_decode_usac_data(ac, che, ue, gb, sbr_ch, indep_flag)` (l.1209-1350) with
`sbr_ch = 2` iff `cpe`: the values it leaves and whether it returned `0`. `SbrInfo()` writes
`bs_xover_band` (4 bits, l.1235); a header (optional, l.1240-1260); the push; the reset; the
element. A failure returns without `sbr_turnoff`. -/
inductive Usac (cpe : Bool) : St → St → Bool → Prop
  | mk {x : Args} {h : Hid} {s1 s2 : St} {y : Args} (info : Bool) (xo : Nat) (b : Bool) :
      HdrOpt true (usacPro x cpe, if info then { h with xover := xo } else h) s1 →
      ResetS (push1 s1.1, s1.2) s2 →
      Elem true cpe { s2.1 with ready := 1 } y b → Usac cpe (x, h) (y, s2.2) b

/-- `ff_aac_sbr_config_usac` (l.1201-1207). -/
def Config (s s' : St) : Prop := s' = stOff s

/-- One call of the parser's entry points on this element, with any outcome. -/
def Call (s s' : St) : Prop :=
  (∃ id, DecExt id s s') ∨ (∃ cpe b, Usac cpe s s' b) ∨ Config s s'

/-- A call after which `ff_aac_sbr_apply` may run in the same frame: `ff_aac_sbr_decode_extension`
(any outcome), a successful `ff_aac_sbr_decode_usac_data` (a failed one makes the USAC decoder
return before apply, `U`:1659-1661), `ff_aac_sbr_config_usac`. -/
def Final (s s' : St) : Prop :=
  (∃ id, DecExt id s s') ∨ (∃ cpe, Usac cpe s s' true) ∨ Config s s'

/-- **The parser's step.** `ModelStep x x'`: either no call ran (`x' = x`) or, for some hidden
state satisfying I1, a sequence of calls ended by a `Final` one leads to `x'`. Only calls that
return are steps (a run stopped inside `read_sbr_grid` by its `av_assert0` has no next call of
`ff_aac_sbr_apply`; see `Grid`).

There is no guard on the visible values `x`: every `x` has a hidden state with I1
(`i1_exists`), so every model run from every `x` is a step (`modelStep_of_run`). I2 is carried
by the session instead: it is part of the parser invariant (`Inv := GridInv ∧ Inv2`,
`modelStep_parseStep`), and it survives apply because `ApplyFPost`'s `KeepD` keeps `n[0]`,
`num_patches` and the tables and lets apply only clear `start` (`inv2_stable`). -/
def ModelStep (x x' : Args) : Prop :=
  x' = x ∨ ∃ h m h', I1 x h ∧ Star Call (x, h) m ∧ Final m (x', h')

/-! ## The invariant through the calls -/

theorem clrNoise_te (v : DV) : (clrNoise v).te = v.te := by unfold clrNoise; rfl
theorem clrNoise_nenv (v : DV) : (clrNoise v).nenv = v.nenv := by unfold clrNoise; rfl

theorem mi_turnoff {s : St} (h : AI s.1) : MI (stOff s) ∧ LiveC (stOff s).1 := by
  obtain ⟨a1, -, a3, a4, a5, a6⟩ := h
  refine ⟨⟨⟨scal_turnoff a1, fun h => absurd rfl h, a3, a4, a5, a6⟩, fun _ => rfl⟩,
    fun h => absurd rfl h, fun h => absurd rfl h.1⟩

/-- `TabWF` with a new limiter table. -/
theorem tabwf_lim {x : Args} {l : List UInt8} {n : Nat} (h : TabWF x) (hl : l.length = 60)
    (ht : TabIn l n x.kx1 (x.kx1 + x.m1)) : TabWF { x with ftLim := l, nlim := n } := by
  obtain ⟨c1, c2, c3, -, c5, c6, c7, c8, c9, c10, -, c12, c13, c14, -, c16, c17, c18, c19, c20,
    c21⟩ := h
  exact ⟨c1, c2, c3, hl, c5, c6, c7, c8, c9, c10, ht.1, c12, c13, c14, ht.2, c16, c17, c18, c19,
    c20, c21⟩

/-- The state after the optional header: what `AI` keeps, the tables if no reset is pending,
and a 4-bit `bs_start_freq` if one is. -/
def HI (s : St) : Prop :=
  Scal s.1 ∧ (s.1.reset = 0 → s.1.start ≠ 0 → TabWF s.1 ∧ 1 ≤ s.1.n0 ∧ 1 ≤ s.1.npatch)
  ∧ (s.1.reset ≠ 0 → s.2.start < 16) ∧ DWF False s.1.d0 ∧ DWF False s.1.d1
  ∧ PsWF s.1.psc s.1.psh ∧ GridInv s.1 ∧ I1 s.1 s.2

theorem hi_of_mi {s : St} (h : MI s) (hr : s.1.reset = 0) : HI s := by
  obtain ⟨⟨a1, a2, a3, a4, a5, a6⟩, i1⟩ := h
  exact ⟨a1, fun _ => a2, fun h => absurd hr h, a3, a4, a5, a6, i1⟩

/-- **The header.** From `MI` with `reset = 0` (both callers clear it first). -/
theorem hdr_spec {usac : Bool} {x : Args} {h : Hid} {s1 : St} (hm : MI (x, h)) (hr : x.reset = 0)
    (hh : HdrOpt usac (x, h) s1) : HI s1 ∧ s1.1.idAac = x.idAac := by
  rcases hh with rfl | hh
  · exact ⟨hi_of_mi hm hr, rfl⟩
  obtain ⟨⟨a1, a2, a3, a4, a5, a6⟩, i1⟩ := hm
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩ := a1
  cases hh with
  | @mk _ _ y s xo lb lg rd interp sm chg hs _ _ _ hlg _ hchg hl =>
    -- no change requested: the decoder was started (I1), so its tables are `TabWF`
    have hst : chg = false → x.start ≠ 0 ∧ TabWF x ∧ 1 ≤ x.n0 ∧ 1 ≤ x.npatch := by
      intro hc
      have hs' : s = h.start := by
        apply Classical.byContradiction; intro hne; rw [hchg hne] at hc; exact absurd hc (by decide)
      have hx0 : x.start ≠ 0 := fun h0 => by have h255 : h.start = 255 := i1 h0; omega
      exact ⟨hx0, a2 hx0⟩
    cases hl with
    | keep _ =>
      refine ⟨⟨⟨b1, b2, b3, b4, b5, b6, show lg ≤ 3 by omega, b8, b9, b10, b11, b12⟩,
        fun hr0 _ => ?_, fun _ => hs, a3, a4, a5, a6,
        fun h1 => absurd (show (1 : BitVec 32) = 0 from h1) (by decide)⟩, rfl⟩
      cases chg with
      | true => exact absurd (show (1 : BitVec 32) = 0 from hr0) (by decide)
      | false => exact (hst rfl).2
    | lim _ hr0 ht =>
      cases chg with
      | true => exact absurd (show (1 : BitVec 32) = 0 from hr0) (by decide)
      | false =>
        obtain ⟨-, ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17,
          c18, c19, c20, c21⟩, n1, n2⟩ := hst rfl
        obtain ⟨t1, t2, t3, t4⟩ := tablelim_spec ht ⟨c9, c13⟩ c21 b8 b12 b4
        have t3' : TabIn y.ftLim y.nlim x.kx1 (x.kx1 + x.m1) := by rw [t4] at t3; exact t3
        rw [t4]
        refine ⟨⟨⟨b1, b2, b3, b4, b5, b6, show lg ≤ 3 by omega, b8, b9, b10, t1, b12⟩,
          fun _ _ => ⟨tabwf_lim ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15,
            c16, c17, c18, c19, c20, c21⟩ t2 t3', n1, n2⟩, fun h => absurd hr h, a3, a4, a5, a6,
          fun h1 => absurd (show (1 : BitVec 32) = 0 from h1) (by decide)⟩, rfl⟩

/-- `sbr_reset` keeps the fields of `TFrame`, with no assumption. -/
theorem reset_frame {sp : Spec} {lb : Nat} {x x' : Args} (h : Reset sp lb x x') :
    ∃ y, TFrame x y ∧ (x' = y.turnoff ∨ x' = y) := by
  cases h with
  | badRate _ _ => exact ⟨x, tframe_refl x, Or.inl rfl⟩
  | @badMaster k0 _ _ =>
    exact ⟨{ x with k0 := k0.toNat },
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Or.inl rfl, Or.inl rfl⟩, Or.inl rfl⟩
  | @badDerived k0 nm f y hst hm hd =>
    obtain ⟨k2, b1, b2, b3, b4, b5, b6, b7, b8⟩ := master_ok hst hm
    exact ⟨y, (derived_spec hd b1 b2 b3 b4 b5 b6 b7 b8).2.2.2.2.2.2.1, Or.inl rfl⟩
  | @ok k0 nm f y hst hm hd =>
    obtain ⟨k2, b1, b2, b3, b4, b5, b6, b7, b8⟩ := master_ok hst hm
    exact ⟨_, (derived_spec hd b1 b2 b3 b4 b5 b6 b7 b8).2.2.2.2.2.2.1, Or.inr rfl⟩

theorem gridInv_tframe {x y : Args} (ht : TFrame x y) (hg : GridInv x) : GridInv y := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h0, h1⟩ := ht
  unfold GridInv
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
    simp only [h0, h1, clrNoise_te, clrNoise_nenv] <;> exact hg

theorem dwf_tframe {x y : Args} (ht : TFrame x y) (h0 : DWF False x.d0) (h1 : DWF False x.d1) :
    DWF False y.d0 ∧ DWF False y.d1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, e0, e1⟩ := ht
  constructor
  · rcases e0 with e | e <;> rw [e]
    · exact h0
    · exact dwf_clrNoise h0
  · rcases e1 with e | e <;> rw [e]
    · exact h1
    · exact dwf_clrNoise h1

/-- **The reset step.** -/
theorem reset_step {s1 s2 : St} (hi : HI s1) (hr : ResetS s1 s2) :
    MI s2 ∧ s2.1.idAac = s1.1.idAac := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, i1⟩ := hi
  cases hr with
  | skip h0 => exact ⟨⟨⟨a1, a2 h0, a4, a5, a6, a7⟩, i1⟩, rfl⟩
  | @run x h y hne hR =>
    obtain ⟨sc, -⟩ := reset_spec hR a1
    obtain ⟨z, ht, hz⟩ := reset_spec hR a1 |>.2
    obtain ⟨d0, d1⟩ := dwf_tframe ht a4 a5
    have hg := gridInv_tframe ht a7
    obtain ⟨-, -, -, hzs, hzid, hzpc, hzph, -, -, -, -, -⟩ := ht
    rcases hz with rfl | ⟨rfl, tz, n1, n2⟩
    · refine ⟨⟨⟨sc, fun h => absurd rfl h, d0, d1, ?_, hg⟩, fun _ => ?_⟩, hzid⟩
      · show PsWF z.psc z.psh; rw [hzpc, hzph]; exact a6
      · show (if z.turnoff.start = 0 then h.turnoff else h).start = 255
        simp only [↓reduceIte]; rfl
    · refine ⟨⟨⟨sc, fun _ => ⟨tz, n1, n2⟩, d0, d1, ?_, hg⟩, fun h0 => ?_⟩, hzid⟩
      · rw [hzpc, hzph]; exact a6
      · have h0' : y.start = 0 := h0
        simp only [h0', ↓reduceIte]; rfl

/-! ### The channel elements -/

theorem invfRead_te (nq : Nat) (v : DV) (vals : Nat → Nat) : (invfRead nq v vals).te = v.te := by
  unfold invfRead; rfl
theorem invfRead_nenv (nq : Nat) (v : DV) (vals : Nat → Nat) :
    (invfRead nq v vals).nenv = v.nenv := by unfold invfRead; rfl
theorem invfCouple_te (a b : DV) : (invfCouple a b).te = b.te := by unfold invfCouple; rfl
theorem invfCouple_nenv (a b : DV) : (invfCouple a b).nenv = b.nenv := by unfold invfCouple; rfl

theorem dwf_invfRead {nq : Nat} {v : DV} {vals : Nat → Nat} (h : DWF False v) :
    DWF False (invfRead nq v vals) := by
  unfold invfRead
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, -⟩ := h
  refine ⟨a1, mk_length _ _, a3, a4, a5, a6, a7, fun i hi => ?_, a9, a10, a11, a12, a13, a14, a15,
    False.elim⟩
  rw [u8_mk]; have := a8 i hi; (repeat' split) <;> bnd

theorem dwf_invfCouple {a b : DV} (ha : DWF False a) (hb : DWF False b) :
    DWF False (invfCouple a b) := by
  unfold invfCouple
  obtain ⟨-, -, -, -, -, -, -, a8, -⟩ := ha
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, -⟩ := hb
  refine ⟨b1, mk_length _ _, b3, b4, b5, b6, b7, fun i hi => ?_, b9, b10, b11, b12, b13, b14, b15,
    False.elim⟩
  rw [u8_mk]; have := a8 i hi; (repeat' split) <;> bnd

theorem live_invfRead {nq : Nat} {v : DV} {vals : Nat → Nat} (h : Live v) :
    Live (invfRead nq v vals) := by
  unfold Live; rw [invfRead_te, invfRead_nenv]; exact h

theorem live_invfCouple {a b : DV} (h : Live b) : Live (invfCouple a b) := by
  unfold Live; rw [invfCouple_te, invfCouple_nenv]; exact h

/-- **The channel element** keeps `DWF False` and `GridInv`, writes only the channels and
`bs_coupling`, and a successful one leaves live grids. -/
theorem elem_spec {usac cpe : Bool} {x y : Args} {b : Bool} (hd0 : DWF False x.d0)
    (hd1 : DWF False x.d1) (hg : GridInv x) (h : Elem usac cpe x y b) :
    DWF False y.d0 ∧ DWF False y.d1 ∧ GridInv y ∧ (b = true → Live y.d0 ∧ (cpe = true → Live y.d1))
    ∧ y = { x with d0 := y.d0, d1 := y.d1, coupling := y.coupling } := by
  obtain ⟨g0, g1⟩ := hg
  cases h with
  | sceFail _ hw =>
    obtain ⟨w1, w2, -⟩ := grid_wf hd0 g0 hw
    exact ⟨w1, hd1, ⟨w2, g1⟩, nofun, rfl⟩
  | @sce w vals b hc hw =>
    subst hc
    obtain ⟨w1, w2, w3, -⟩ := grid_wf hd0 g0 hw
    refine ⟨dwf_invfRead w1, hd1, ⟨?_, g1⟩, fun _ => ⟨live_invfRead (w3 rfl), nofun⟩, rfl⟩
    show u8 (invfRead x.nq w vals).te (invfRead x.nq w vals).nenv ≤ 19
    rw [invfRead_te, invfRead_nenv]; exact w2
  | cplFail _ hw =>
    obtain ⟨w1, w2, -⟩ := grid_wf hd0 g0 hw
    exact ⟨w1, hd1, ⟨w2, g1⟩, nofun, rfl⟩
  | @cpl w vals b _ hw =>
    obtain ⟨w1, w2, w3, -⟩ := grid_wf hd0 g0 hw
    obtain ⟨c1, c2, c3, -⟩ := copy_wf w1 w2 hd1 g1
    refine ⟨dwf_invfRead w1, dwf_invfCouple (dwf_invfRead w1) c1, ⟨?_, ?_⟩,
      fun _ => ⟨live_invfRead (w3 rfl), fun _ => live_invfCouple (c3 (w3 rfl))⟩, rfl⟩
    · show u8 (invfRead x.nq w vals).te (invfRead x.nq w vals).nenv ≤ 19
      rw [invfRead_te, invfRead_nenv]; exact w2
    · show u8 (invfCouple _ (copyGrid x.d1 w)).te (invfCouple _ (copyGrid x.d1 w)).nenv ≤ 19
      rw [invfCouple_te, invfCouple_nenv]; exact c2
  | indFail0 _ hw =>
    obtain ⟨w1, w2, -⟩ := grid_wf hd0 g0 hw
    exact ⟨w1, hd1, ⟨w2, g1⟩, nofun, rfl⟩
  | indFail1 _ hw hw1 =>
    obtain ⟨w1, w2, -⟩ := grid_wf hd0 g0 hw
    obtain ⟨v1, v2, -⟩ := grid_wf hd1 g1 hw1
    exact ⟨w1, v1, ⟨w2, v2⟩, nofun, rfl⟩
  | @ind w w' vals vals1 b _ hw hw1 =>
    obtain ⟨w1, w2, w3, -⟩ := grid_wf hd0 g0 hw
    obtain ⟨v1, v2, v3, -⟩ := grid_wf hd1 g1 hw1
    refine ⟨dwf_invfRead w1, dwf_invfRead v1, ⟨?_, ?_⟩,
      fun _ => ⟨live_invfRead (w3 rfl), fun _ => live_invfRead (v3 rfl)⟩, rfl⟩
    · show u8 (invfRead x.nq w vals).te (invfRead x.nq w vals).nenv ≤ 19
      rw [invfRead_te, invfRead_nenv]; exact w2
    · show u8 (invfRead x.nq w' vals1).te (invfRead x.nq w' vals1).nenv ≤ 19
      rw [invfRead_te, invfRead_nenv]; exact v2

/-- `AI` with new channels and `bs_coupling`. -/
theorem ai_elem {x : Args} {d0 d1 : DV} {c : BitVec 32} (h : AI x) (h0 : DWF False d0)
    (h1 : DWF False d1) (hg : GridInv { x with d0 := d0, d1 := d1, coupling := c }) :
    AI { x with d0 := d0, d1 := d1, coupling := c } := by
  obtain ⟨a1, a2, -, -, a5, -⟩ := h
  exact ⟨a1, a2, h0, h1, a5, hg⟩

/-- The extensions keep `AI` and the channels. -/
theorem ext_spec {y z : Args} (h : Star ExtS y z) (hy : AI y) :
    AI z ∧ z.d0 = y.d0 ∧ z.d1 = y.d1 ∧ z.start = y.start ∧ z.idAac = y.idAac := by
  induction h with
  | refl => exact ⟨hy, rfl, rfl, rfl, rfl⟩
  | @step a b c hab _ ih =>
    cases hab with
    | ps c' R f f' hv hr hv' =>
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hy
      obtain ⟨hf, hh⟩ := psWF_to hv a5
      obtain ⟨i1, i2, i3, i4, i5⟩ := ih ⟨a1, a2, a3, a4, psWF_of hv' (psread_wf hf hr) hh, a6⟩
      exact ⟨i1, i2, i3, i4, i5⟩
    | skip => exact ih hy

/-- `AI` does not read `id_aac`, `ready_for_dequant`. -/
theorem ai_id {x : Args} (id : BitVec 32) (h : AI x) : AI { x with idAac := id, ready := 1 } := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6⟩

/-- **`read_sbr_data`.** -/
theorem data_spec {id : BitVec 32} {s s' : St} (hm : MI s) (h : Data id s s') :
    MI s' ∧ LiveC s'.1 := by
  cases h with
  | @fail x hh y cpe _ he =>
    obtain ⟨hai, i1⟩ := hm
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ai_id id hai
    obtain ⟨e1, e2, e3, -, e5⟩ := elem_spec a3 a4 a6 he
    have hy : AI y := by rw [e5]; exact ai_elem ⟨a1, a2, a3, a4, a5, a6⟩ e1 e2 (e5 ▸ e3)
    exact mi_turnoff (s := (y, hh)) hy
  | @bad x hh _ _ _ =>
    obtain ⟨hai, -⟩ := hm
    exact mi_turnoff (s := (_, hh)) (ai_id id hai)
  | @ok x hh y z cpe hc he hx =>
    obtain ⟨hai, i1⟩ := hm
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ai_id id hai
    obtain ⟨e1, e2, e3, e4, e5⟩ := elem_spec a3 a4 a6 he
    have hy : AI y := by rw [e5]; exact ai_elem ⟨a1, a2, a3, a4, a5, a6⟩ e1 e2 (e5 ▸ e3)
    have ys : y.start = x.start := by rw [e5]
    have yid : y.idAac = id := by rw [e5]
    obtain ⟨z1, z2, z3, z4, z5⟩ := ext_spec hx hy
    obtain ⟨l0, l1⟩ := e4 rfl
    refine ⟨⟨z1, fun hz => ?_⟩, fun _ => z2 ▸ l0, fun hz => ?_⟩
    · exact i1 (by rw [← ys, ← z4]; exact hz)
    · rw [z3]; apply l1
      rcases hc with ⟨rfl, hid⟩ | ⟨rfl, -⟩
      · rw [z5, yid] at hz; rcases hid with rfl | rfl <;> exact absurd hz.2 (by decide)
      · rfl

/-! ### The entry points -/

theorem mi_extPro {x : Args} {h : Hid} (sr er : BitVec 32) (hm : MI (x, h)) :
    MI (extPro x sr er, h) := by
  obtain ⟨⟨⟨-, b2, -, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩, a2, a3, a4, a5, a6⟩, i1⟩ := hm
  exact ⟨⟨⟨b2, b2, b4, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩, a2, a3, a4, a5, a6⟩, i1⟩

theorem mi_usacPro {x : Args} {h h' : Hid} (cpe : Bool) (hm : MI (x, h))
    (hs : h'.start = h.start) : MI (usacPro x cpe, h') := by
  obtain ⟨⟨a1, a2, a3, a4, a5, a6⟩, i1⟩ := hm
  exact ⟨⟨a1, a2, a3, a4, a5, a6⟩, fun h0 => hs ▸ i1 h0⟩

theorem hi_push1 {s : St} (hi : HI s) : HI (push1 s.1, s.2) := by
  obtain ⟨⟨-, b2, -, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩, a2, a3, a4, a5, a6, a7, i1⟩ := hi
  exact ⟨⟨b2, b2, b4, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩, a2, a3, a4, a5, a6, a7, i1⟩

/-- **`ff_aac_sbr_decode_extension`.** From `MI`, every outcome gives `MI` and the live
clauses. -/
theorem decext_spec {id : BitVec 32} {s s' : St} (hm : MI s) (h : DecExt id s s') :
    MI s' ∧ LiveC s'.1 := by
  cases h with
  | @mk x hh s1 s2 s3 sr er long hopt hres hd hn =>
    obtain ⟨hi, -⟩ := hdr_spec (mi_extPro sr er hm) rfl hopt
    obtain ⟨m2, -⟩ := reset_step hi hres
    have h3 : MI s3 ∧ LiveC s3.1 := by
      by_cases h0 : s2.1.start = 0
      · rw [hn h0]; exact ⟨m2, fun h => absurd h0 h, fun h => absurd h0 h.1⟩
      · exact data_spec m2 (hd h0)
    cases long with
    | true => exact mi_turnoff h3.1.1
    | false => exact h3

/-- **`ff_aac_sbr_decode_usac_data`.** From `MI`, every outcome gives `MI`; success gives the
live clauses. -/
theorem usac_spec {cpe b : Bool} {s s' : St} (hm : MI s) (h : Usac cpe s s' b) :
    MI s' ∧ (b = true → LiveC s'.1) := by
  cases h with
  | @mk x hh s1 s2 y info xo b hopt hres he =>
    have m0 := mi_usacPro (h' := if info then { hh with xover := xo } else hh) cpe hm
      (by cases info <;> rfl)
    obtain ⟨hi, hid1⟩ := hdr_spec m0 rfl hopt
    obtain ⟨⟨⟨a1, a2, a3, a4, a5, a6⟩, i1⟩, hid2⟩ := reset_step (hi_push1 hi) hres
    have hr : AI { s2.1 with ready := 1 } := ⟨a1, a2, a3, a4, a5, a6⟩
    obtain ⟨r1, r2, r3, r4, r5, r6⟩ := hr
    obtain ⟨e1, e2, e3, e4, e5⟩ := elem_spec r3 r4 r6 he
    have hy : AI y := by
      rw [e5]; exact ai_elem ⟨r1, r2, r3, r4, r5, r6⟩ e1 e2 (e5 ▸ e3)
    have ys : y.start = s2.1.start := by rw [e5]
    have yid : y.idAac = if cpe then 1 else 0 := by
      rw [e5]; exact hid2.trans hid1
    refine ⟨⟨hy, fun h0 => i1 (ys ▸ h0)⟩, fun hb => ?_⟩
    obtain ⟨l0, l1⟩ := e4 hb
    refine ⟨fun _ => l0, fun hz => l1 ?_⟩
    cases cpe with
    | true => rfl
    | false => rw [yid] at hz; exact absurd hz.2 (by decide)

theorem call_spec {s s' : St} (hm : MI s) (h : Call s s') : MI s' := by
  rcases h with ⟨id, h⟩ | ⟨cpe, b, h⟩ | h
  · exact (decext_spec hm h).1
  · exact (usac_spec hm h).1
  · rw [h]; exact (mi_turnoff hm.1).1

theorem final_spec {s s' : St} (hm : MI s) (h : Final s s') : MI s' ∧ LiveC s'.1 := by
  rcases h with ⟨id, h⟩ | ⟨cpe, h⟩ | h
  · exact decext_spec hm h
  · exact ⟨(usac_spec hm h).1, (usac_spec hm h).2 rfl⟩
  · rw [h]; exact mi_turnoff hm.1

theorem star_spec {s s' : St} (h : Star Call s s') (hm : MI s) : MI s' := by
  induction h with
  | refl => exact hm
  | step hab _ ih => exact ih (call_spec hm hab)

/-! ### `SbrWF` and the session -/

theorem mi_of_wf {x : Args} {h : Hid} (hw : SbrWF x) (hg : GridInv x) (h1 : I1 x h)
    (h2 : Inv2 x) : MI (x, h) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, tab, d0, d1, ps⟩ := hw
  exact ⟨⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩, fun hs => ⟨tab hs, h2 hs⟩,
    (dwf_iff.mp d0).1, (dwf_iff.mp d1).1, ps, hg⟩, h1⟩

theorem wf_of_mi {s : St} (h : MI s) (hl : LiveC s.1) : SbrWF s.1 ∧ GridInv s.1 ∧ Inv2 s.1 := by
  obtain ⟨⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩, tab, d0, d1, ps, hg⟩, -⟩ := h
  exact ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, fun hs => (tab hs).1,
    dwf_iff.mpr ⟨d0, hl.1⟩, dwf_iff.mpr ⟨d1, hl.2⟩, ps⟩, hg, fun hs => (tab hs).2⟩

/-- The model's step keeps `SbrWF`, `GridInv` and `Inv2`. -/
theorem modelStep_wf {x x' : Args} (hw : SbrWF x) (hg : GridInv x) (h2 : Inv2 x)
    (h : ModelStep x x') : SbrWF x' ∧ GridInv x' ∧ Inv2 x' := by
  obtain rfl | ⟨hh, m, h', h1, hs, hf⟩ := h
  · exact ⟨hw, hg, h2⟩
  · exact wf_of_mi (final_spec (star_spec hs (mi_of_wf hw hg h1 h2)) hf).1
      (final_spec (star_spec hs (mi_of_wf hw hg h1 h2)) hf).2

/-! ### The pointers apply depends on -/

/-- The `av_tx` contexts and `ac->fdsp` are unchanged. -/
def KP (x y : Args) : Prop := y.anaCtx = x.anaCtx ∧ y.synCtx = x.synCtx ∧ y.fdsp = x.fdsp

theorem KP.trans {x y z : Args} (h1 : KP x y) (h2 : KP y z) : KP x z :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩

theorem kp_hdr {usac : Bool} {s s' : St} (h : HdrOpt usac s s') : KP s.1 s'.1 := by
  rcases h with rfl | h
  · exact ⟨rfl, rfl, rfl⟩
  · cases h with
    | mk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hl =>
      cases hl with
      | keep _ => exact ⟨rfl, rfl, rfl⟩
      | lim _ _ ht => cases ht <;> exact ⟨rfl, rfl, rfl⟩

theorem kp_reset {s s' : St} (h : ResetS s s') : KP s.1 s'.1 := by
  cases h with
  | skip _ => exact ⟨rfl, rfl, rfl⟩
  | run _ hR =>
    obtain ⟨y, ⟨-, -, -, -, -, -, -, h1, h2, h3, -⟩, hy⟩ := reset_frame hR
    rcases hy with rfl | rfl <;> exact ⟨h1, h2, h3⟩

theorem kp_elem {usac cpe : Bool} {x y : Args} {b : Bool} (h : Elem usac cpe x y b) : KP x y := by
  cases h <;> exact ⟨rfl, rfl, rfl⟩

theorem kp_ext {y z : Args} (h : Star ExtS y z) : KP y z := by
  induction h with
  | refl => exact ⟨rfl, rfl, rfl⟩
  | step hab _ ih => cases hab <;> exact KP.trans ⟨rfl, rfl, rfl⟩ ih

theorem kp_data {id : BitVec 32} {s s' : St} (h : Data id s s') : KP s.1 s'.1 := by
  cases h with
  | @fail x hh y cpe _ he =>
    exact KP.trans (KP.trans (y := { x with idAac := id, ready := 1 }) ⟨rfl, rfl, rfl⟩
      (kp_elem he)) (z := (stOff (y, hh)).1) ⟨rfl, rfl, rfl⟩
  | bad _ _ _ => exact ⟨rfl, rfl, rfl⟩
  | @ok x hh y z cpe _ he hx =>
    exact KP.trans (KP.trans (y := { x with idAac := id, ready := 1 }) ⟨rfl, rfl, rfl⟩
      (kp_elem he)) (kp_ext hx)

theorem kp_call {s s' : St} (h : Call s s') : KP s.1 s'.1 := by
  rcases h with ⟨id, h⟩ | ⟨cpe, b, h⟩ | h
  · cases h with
    | @mk x hh s1 s2 s3 sr er long hopt hres hd hn =>
      have k3 : KP s2.1 s3.1 := by
        by_cases h0 : s2.1.start = 0
        · rw [hn h0]; exact ⟨rfl, rfl, rfl⟩
        · exact kp_data (hd h0)
      have k : KP x s3.1 :=
        KP.trans (KP.trans (KP.trans (y := extPro x sr er) ⟨rfl, rfl, rfl⟩ (kp_hdr hopt))
          (kp_reset hres)) k3
      cases long with
      | true => exact k
      | false => exact k
  · cases h with
    | @mk x hh s1 s2 y info xo b hopt hres he =>
      have a : KP x s1.1 := KP.trans (y := usacPro x cpe) ⟨rfl, rfl, rfl⟩ (kp_hdr hopt)
      have b : KP s1.1 (push1 s1.1) := ⟨rfl, rfl, rfl⟩
      have c : KP (push1 s1.1) s2.1 := kp_reset (s := (push1 s1.1, s1.2)) hres
      have d : KP s2.1 y :=
        KP.trans (y := { s2.1 with ready := 1 }) ⟨rfl, rfl, rfl⟩ (kp_elem he)
      exact a.trans (b.trans (c.trans d))
  · rw [h]; exact ⟨rfl, rfl, rfl⟩

theorem kp_star {s s' : St} (h : Star Call s s') : KP s.1 s'.1 := by
  induction h with
  | refl => exact ⟨rfl, rfl, rfl⟩
  | step hab _ ih => exact KP.trans (kp_call hab) ih

theorem final_call {s s' : St} (h : Final s s') : Call s s' := by
  rcases h with h | ⟨cpe, h⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨cpe, true, h⟩)
  · exact Or.inr (Or.inr h)

/-! ### I1 and I2 -/

/-- The hidden state after init: `bs_limiter_bands = 0` (`av_mallocz`, l.74), `spectrum_params`
all ones (`sbr_turnoff`, l.87). -/
def hInit : Hid := { start := 255, xover := 255, lb := 0 }

theorem i1_init (i : InitIn) : I1 (xInit i) hInit := fun _ => rfl
theorem inv2_init (i : InitIn) : Inv2 (xInit i) := fun h => absurd rfl h

/-- `sbr_turnoff` establishes I1 and I2. -/
theorem i1_turnoff (s : St) : I1 (stOff s).1 (stOff s).2 := fun _ => rfl
theorem inv2_turnoff (x : Args) : Inv2 x.turnoff := fun h => absurd rfl h

/-- I2 survives apply: `KeepD` keeps `n[0]` and `num_patches`, and `start` is kept or
cleared. -/
theorem inv2_stable {x y : Args} (h : x.KeepD y) (hx : Inv2 x) : Inv2 y := by
  obtain ⟨-, -, -, -, -, -, -, -, -, ht⟩ := h
  unfold Args.KeepT at ht
  obtain ⟨-, hn0, -, -, -, hnp, -, -, -, -, -, -, hst⟩ := ht
  intro hs
  rcases hst with ⟨h0, -⟩ | ⟨h0, -⟩
  · exact absurd h0 hs
  · rw [hn0, hnp]; exact hx (h0 ▸ hs)

/-- Every visible state has a hidden state with I1 (`spectrum_params.bs_start_freq = 0xFF`). -/
theorem i1_exists (x : Args) : ∃ h, I1 x h := ⟨hInit, fun _ => rfl⟩

/-- Every model run, from any visible state and any hidden state with I1, is a `ModelStep`. -/
theorem modelStep_of_run {x x' : Args} {h h' : Hid} {m : St} (h1 : I1 x h)
    (hs : Star Call (x, h) m) (hf : Final m (x', h')) : ModelStep x x' :=
  Or.inr ⟨h, m, h', h1, hs, hf⟩

/-- The model preserves I1: after a model step from a state with `SbrWF`, `GridInv`, I1 and I2,
the final hidden state satisfies I1. -/
theorem modelStep_i1 {x x' : Args} {h : Hid} (hw : SbrWF x) (hg : GridInv x) (h1 : I1 x h)
    (h2 : Inv2 x) {m : St} {h' : Hid} (hs : Star Call (x, h) m) (hf : Final m (x', h')) :
    I1 x' h' :=
  (final_spec (star_spec hs (mi_of_wf hw hg h1 h2)) hf).1.2

/-- The model preserves I2. -/
theorem modelStep_inv2 {x x' : Args} (hw : SbrWF x) (hg : GridInv x) (h2 : Inv2 x)
    (h : ModelStep x x') : Inv2 x' := (modelStep_wf hw hg h2 h).2.2

/-! ### The result -/

/-- **`ParseStep` for the model**, with the parser invariant `Inv = GridInv ∧ Inv2`.
`ModelStep` has no guard on the visible values (`modelStep_of_run`, `i1_exists`); it quantifies
only the hidden state, under I1 (see `ModelStep`, `I1`). -/
theorem modelStep_parseStep : ParseStep ModelStep (fun x => GridInv x ∧ Inv2 x) where
  wf := fun _ _ hw hi h =>
    ⟨(modelStep_wf hw hi.1 hi.2 h).1, (modelStep_wf hw hi.1 hi.2 h).2.1,
      (modelStep_wf hw hi.1 hi.2 h).2.2⟩
  stable := fun _ _ h hx => ⟨gridInv_stable h hx.1, inv2_stable h hx.2⟩
  init := fun i => ⟨gridInv_init i, inv2_init i⟩
  keep := fun x x' h => by
    obtain rfl | ⟨hh, m, h', -, hs, hf⟩ := h
    · exact ⟨rfl, rfl, rfl⟩
    · exact KP.trans (kp_star hs) (kp_call (final_call hf))

/-- Every value reachable from init in a session with the model as the parser satisfies
`SbrWF` (`Session.reachable_init_wf` with `modelStep_parseStep`). -/
theorem model_reachable_wf [CodeEnv] (i : InitIn) {x : Args}
    (h : Reachable ModelStep (xInit i) x) : SbrWF x :=
  reachable_init_wf modelStep_parseStep i h

end Kraken.Examples.Sbr.ParseModel
