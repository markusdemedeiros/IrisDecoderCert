import Kraken.X64.Parser
import Kraken.MachineWP
import Kraken.Rules.PackedSse
import Kraken.Rules.IntMisc
import Kraken.X64.Examples.Sbr.Spec
import Kraken.X64.Examples.Sbr.Dsp.HfGenText

/-!
# `ff_sbr_hf_gen_sse` as a `ProcSpec`

`sbr_hf_gen(X_high, X_low, alpha0, alpha1, bw, start, end)`
(`libavcodec/x86/sbrdsp.asm`) computes, for `start ≤ i < end`,
`X_high[i] = X_low[i-2]·alpha1·bw² + X_low[i-1]·alpha0·bw + X_low[i]` on complex
pairs, two complex outputs per iteration, with the counter `r8` running from
`8·(start - end)` up to 0. `spec` proves `HfGenSpec`: a call meeting `HfGenC`, with
`X_high[start..end)`, `X_low[start-2..end)`, `alpha0[2]`, `alpha1[2]` and
`ps_mask` owned, returns with the SysV convention restored and only those bytes
changed.

## Notes

* Footprint, in bytes: `8·(end-start)` at `X_high + 8·start` (written),
  `8·(end-start) + 16` at `X_low + 8·start - 16` (read; the first aligned load
  is `X_low[start-2]`, the last `movaps` ends at `X_low[end]`), 8 at `alpha0`,
  8 at `alpha1` (`movlps`, no alignment), 16 at `ps_mask` (`xorps` memory
  operand, 16-aligned). `start`/`end` are the low 32 bits of `r8`/`r9`,
  sign-extended (`movslq`), so the footprint is stated over the sign-extended
  values and is meaningful for negative `start` too.
* Conditions (`HfGenC`), beyond the footprint:
  - `start < end` as signed 32-bit integers. Needed for termination: with
    `start = end` the loop runs once before testing (writes `X_high[end..end+2)`,
    outside the footprint) and then wraps the counter: about `2^60` iterations
    over memory. The C reference does nothing for `start ≥ end`.
  - `end - start` even. The loop exits on `jne` (`jnz` in the source) when the
    counter reaches exactly 0 in steps of 16 bytes = 2 complex values; an odd
    count steps over 0 and runs off the end. checkasm (`start` even, `end =
    128`) and the call site in `aacsbr_template.c` (`2·t_env[0]`,
    `2·t_env[bs_num_env]`) always pass even values.
  - `X_high + 8·start` and `X_low + 8·start - 16` 16-byte aligned (aligned
    `movaps` load and store). This is weaker than "both arrays aligned and
    `start` even": only the parity of the bases at `start` matters. checkasm
    passes 16-aligned arrays and even `start`; the call site passes `X_high[k] +
    2`, `X_low[p] + 2` (rows of 40 complex values, i.e. 320 bytes, in 16-aligned
    arrays) and even `start`. `ps_mask` 16-aligned (from the layout, at linking).
  So the C caller must guarantee `t_env[0] < t_env[bs_num_env]` (for `SbrWF`).
* No stack, no callee-saved register: the reservation is 0.
* Proof: four blocks (entry, `.pre` before the first load, the loop, `ret`).
  `&X_high[start]`, `&X_low[start-2]` and `8·(end-start)` are opaque `def`s
  (`xh`, `xl`, `nb`) inside the proof, their definitions stated once at the
  entry. Reason: with them unfolded, `grind`'s commutative-ring solver PANICs
  (`mkImpEqExprProof`, assertion `d.p matches .num 0`, presumably on the
  products by `8` in `BitVec 64`) and returns a proof that the kernel rejects
  (`unknown constant '_inhabitedExprDummy'`). The entry block, which must
  connect them to the registers, runs `finish (ring := false)`; it proves
  without the ring solver.
* The loop's step needs two local rules (below): `add $0x10,%r8` leaves
  `16 + r8` (constant first), and `grind` cannot relate `(16 + r8 + N).toNat`
  to `(r8 + N).toNat`, nor show the counter does not wrap, by itself. Without
  them the loop block runs to the heartbeat limit.
* Negative checks (scratch): dropping `N % 16 = 0` (what `end - start` even
  gives) from the loop facts makes the loop block fail; dropping the alignment
  of `X_low + 8·start - 16` makes the `.pre` block and the loop block fail.
* Rule-file `grind` scopes opened (see `Kraken/Rules/*.lean`):
  `Kraken.Rules.GenericMem.Norm`, `Kraken.Rules.IntMisc.SubReg`.
-/

open Kraken.X64.Parser
open Kraken
open Kraken.SysV
open Std.WP
open Mem
open MachineWP
open scoped Kraken.Rules.GenericMem.Norm Kraken.Rules.IntMisc.SubReg

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.HfGen

/-! ## Local rules (general; for the library)

For a counter `r` running up to 0 in steps of 16 with `r + n` the bytes done
(a multiple of 16 below `n`): the step `16 + r` does not wrap and keeps the
bytes done below `n` unless it reached 0. Stated with the constant first, the
form the `add` rule leaves. -/

/-- One loop step on a counter `r` running up to 0 by 16, with `r + n` the
bytes done: `add $16,%r` (constant first, as the rule leaves it) does not wrap
unless it reaches 0. -/
theorem add16_toNat {r n : BitVec 64} (hj16 : (r + n).toNat % 16 = 0)
    (hn16 : n.toNat % 16 = 0) (hne : 16#64 + r ≠ 0#64) :
    (16#64 + r).toNat = r.toNat + 16 := by
  bv_omega

grind_pattern add16_toNat => (16#64 + r).toNat, r + n

/-- One loop step: the bytes done grow by 16 and stay below `n` unless the
counter reached 0. -/
theorem loop_step16 {r n : BitVec 64} (hj : (r + n).toNat < n.toNat)
    (hj16 : (r + n).toNat % 16 = 0) (hn16 : n.toNat % 16 = 0) (hne : 16#64 + r ≠ 0#64) :
    (16#64 + r + n).toNat = (r + n).toNat + 16 ∧ (r + n).toNat + 16 < n.toNat := by
  bv_omega

grind_pattern loop_step16 => (16#64 + r + n).toNat

/-! ## The proof -/

variable [CodeEnv]

/-- The caller's side of memory behind the footprint. -/
def Rest (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) : Mem 64 → Prop :=
  RetCell ra (t₀.regs.get64 .rsp) ⋆ (Reserve 0 (t₀.regs.get64 .rsp) ⋆ R)

/-- `&X_high[start]`, `&X_low[start-2]` and `N = 8 * (end - start)` as opaque
atoms inside the proof: `grind`'s ring solver panics (and emits an ill-typed
proof) on the products by `8` they unfold to, so the loop sees only the atoms. -/
def xh (t : MachineData) : BitVec 64 := HfGenXh t
def xl (t : MachineData) : BitVec 64 := HfGenXl t
def nb (t : MachineData) : BitVec 64 := HfGenN t

/-- The footprint over the atoms (definitionally `HfGenF`). -/
abbrev Foot (t : MachineData) : Mem 64 → Prop :=
  Blocks [(xh t, (nb t).toNat), (xl t, (nb t).toNat + 16),
    (arg2 t, 8), (arg3 t, 8), (lab "ps_mask", 16)]

/-- Arithmetic facts about `N` that the condition implies. -/
abbrev NFacts (t₀ : MachineData) : Prop :=
  0 < (nb t₀).toNat ∧ (nb t₀).toNat % 16 = 0 ∧ (nb t₀).toNat < 2 ^ 40

/-- The alignments the loop uses. -/
abbrev Al (t₀ : MachineData) : Prop :=
  isAligned 16 (xh t₀) = true ∧ isAligned 16 (xl t₀) = true
    ∧ isAligned 16 (lab "ps_mask") = true

/-- The loop invariant at `.loop2`: `rdi = Xh + N`, `rsi = Xl + N`, `j = r8 + N` the bytes done,
a multiple of 16 below `N`, with the offsets of the two access pointers. -/
abbrev Inv (R : Mem 64 → Prop) (ra : Int64) (t₀ s : MachineData) : Prop :=
      let j := (s.regs.get64 .r8 + nb t₀).toNat
      NFacts t₀ ∧ Al t₀
      ∧ s.regs.get64 .rdi = xh t₀ + nb t₀
      ∧ s.regs.get64 .rsi = xl t₀ + nb t₀
      ∧ j < (nb t₀).toNat ∧ j % 16 = 0
      ∧ s.regs.get64 .rdi + s.regs.get64 .r8 - xh t₀ = s.regs.get64 .r8 + nb t₀
      ∧ s.regs.get64 .rsi + s.regs.get64 .r8 - xl t₀ = s.regs.get64 .r8 + nb t₀
      ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp
      ∧ SavedRegs t₀ s
      ∧ (s.dmem =⋆ Foot t₀ ⋆ Rest R ra t₀)

/-- The assertions. At `.pre` and `.loop2`: `rdi = Xh + N`, `rsi = Xl + N`,
`r8 + N` the bytes done (a multiple of 16 below `N`). -/
abbrev table (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) :
    Label → MachineData → Prop
  | "ff_sbr_hf_gen_sse", s => s = t₀ ∧ HfGenC t₀ ∧ NFacts t₀ ∧ Al t₀
      ∧ xh t₀ = HfGenXh t₀ ∧ xl t₀ = HfGenXl t₀ ∧ nb t₀ = HfGenN t₀
      ∧ (t₀.dmem =⋆ Foot t₀ ⋆ Rest R ra t₀)
  | "ff_sbr_hf_gen_sse.pre", s =>
      NFacts t₀ ∧ Al t₀
      ∧ s.regs.get64 .rdi = xh t₀ + nb t₀
      ∧ s.regs.get64 .rsi = xl t₀ + nb t₀
      ∧ s.regs.get64 .r8 + nb t₀ = 0#64
      ∧ s.regs.get64 .rsi + s.regs.get64 .r8 - xl t₀ = 0#64
      ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp
      ∧ SavedRegs t₀ s
      ∧ (s.dmem =⋆ Foot t₀ ⋆ Rest R ra t₀)
  | "ff_sbr_hf_gen_sse.loop2", s => Inv R ra t₀ s
  | "ff_sbr_hf_gen_sse.done", s =>
      s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp
      ∧ SavedRegs t₀ s
      ∧ (s.dmem =⋆ Foot t₀ ⋆ Rest R ra t₀)
  | _, _ => False

/-- The variant: `2^64 - r8` (the bytes left) at the loop; 0 at `.done`. -/
abbrev var : Label → MachineData → Nat
  | "ff_sbr_hf_gen_sse.loop2", s => 2 ^ 64 - (s.regs.get64 .r8).toNat
  | "ff_sbr_hf_gen_sse.done", _ => 0
  | _, _ => 2 ^ 64

abbrev Post' (R : Mem 64 → Prop) (ra : Int64) (t₀ s : MachineData) : Prop :=
  s.regs.get64 .rsp = t₀.regs.get64 .rsp + 8
  ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp ∧ SavedRegs t₀ s
  ∧ (s.dmem =⋆ Foot t₀ ⋆ (8 ?@ (t₀.regs.get64 .rsp)
      ⋆ (Reserve 0 (t₀.regs.get64 .rsp) ⋆ R)))

omit [CodeEnv] in
/-- `8 * (b - a)`, sign-extended, for 32-bit `a < b` with `b - a` even: positive,
a multiple of 16, below `2^40`. -/
theorem n_facts (a b : BitVec 32) (h : a.toInt < b.toInt) (h2 : (b.signExtend 64 - a.signExtend 64).toNat % 2 = 0) :
    0 < ((b.signExtend 64 - a.signExtend 64) * 8#64).toNat ∧ ((b.signExtend 64 - a.signExtend 64) * 8#64).toNat % 16 = 0
    ∧ ((b.signExtend 64 - a.signExtend 64) * 8#64).toNat < 2 ^ 40 := by
  have ha : (a.signExtend 64).toInt = a.toInt := BitVec.toInt_signExtend_of_le (by omega)
  have hb : (b.signExtend 64).toInt = b.toInt := BitVec.toInt_signExtend_of_le (by omega)
  have la := BitVec.toInt_lt (x := a)
  have lb := BitVec.toInt_lt (x := b)
  have ga := BitVec.le_toInt (x := a)
  have gb := BitVec.le_toInt (x := b)
  have p31 : (2:Int) ^ (32 - 1) = 2147483648 := by decide
  rw [p31] at la lb ga gb
  have hd : (b.signExtend 64 - a.signExtend 64).toInt = b.toInt - a.toInt := by
    rw [BitVec.toInt_sub, ha, hb]
    simp only [Int.bmod]; split <;> omega
  have hc := BitVec.toInt_eq_toNat_cond (BitVec.signExtend 64 b - BitVec.signExtend 64 a)
  have hn : (b.signExtend 64 - a.signExtend 64).toNat < 2 ^ 33 ∧ 0 < (b.signExtend 64 - a.signExtend 64).toNat := by
    split at hc <;> omega
  have hm : ((b.signExtend 64 - a.signExtend 64) * 8#64).toNat
      = (b.signExtend 64 - a.signExtend 64).toNat * 8 := by
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat]; omega
  rw [hm]
  omega

theorem nfacts {t : MachineData} (h : HfGenC t) : NFacts t :=
  n_facts _ _ h.1 h.2.1

theorem al {t : MachineData} (h : HfGenC t) : Al t := h.2.2

theorem spec (hpl : Program.PlacedIn body) : HfGenSpec := by
  refine Kraken.Executable.ProcSpec.of_cfg_post (p := body) table Post' var
    (hblocks := ?_) (hpre := ?_) (hpost := ?_)
  · intro R ra t₀
    cfg_cases [body]
    · vcgen with finish (ring := false)
    · vcgen with finish
    · vcgen with finish
    · vcgen
      all_goals simp only [Rest] at *
      all_goals call_simp
      all_goals grind_cells
  · rintro R ra t ⟨hcall, hc⟩
    refine ⟨rfl, hc, nfacts hc, al hc, rfl, rfl, rfl, ?_⟩
    have h := hcall
    simp only [Rest, CallPre] at h ⊢
    rw [Std.ExtHashMap.sep_comm_l (Reserve _ _), Std.ExtHashMap.sep_comm_l (RetCell _ _)] at h
    exact h
  · rintro R ra t₀ s ⟨h1, h2, h3, hm⟩
    refine ⟨h1, h2, h3, ?_⟩
    show (_ ⋆ (_ ⋆ (Foot t₀ ⋆ R))) s.dmem
    rw [Std.ExtHashMap.sep_comm_l (Reserve _ _), Std.ExtHashMap.sep_comm_l (Block _ _)]
    exact hm

end Kraken.Examples.Sbr.HfGen
