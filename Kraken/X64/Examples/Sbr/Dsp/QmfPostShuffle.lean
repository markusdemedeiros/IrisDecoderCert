import Kraken.X64.Parser
import Kraken.MachineWP
import Kraken.Rules.PackedSse
import Kraken.X64.Examples.Sbr.Spec
import Kraken.Rules.LeafLemmas
import Kraken.X64.Examples.Sbr.Dsp.QmfPostShuffleText

/-!
# `ff_sbr_qmf_post_shuffle_sse` as a `ProcSpec`

`sbr_qmf_post_shuffle(W, z)` (`libavcodec/x86/sbrdsp.asm`, slot `qmf_post_shuffle`
of `libavcodec/sbrdsp.h`) interleaves `z[0..31]` with the negated, reversed
`z[32..63]` into `W[32][2]`. `spec` proves `QmfPostShuffleSpec`: a call with
`W` (`rdi`) and `z` (`rsi`) 16-byte aligned, the 256 bytes of `W`, the 256 of
`z` and the 16 of `ff_ps_neg` owned, returns with the SysV convention restored
and only those bytes changed (only `W` is written; `z` and `ff_ps_neg` are read).

## Notes

* Footprint as in `tests/checkasm/sbrdsp.c` (`W[32][2]`, `z[64]`) and the one
  call site in `libavcodec/aacsbr_template.c` (`sbr_qmf_synthesis`:
  `W[buf_idx][32][2]` and `z = mdct_buf[0]`, 64 floats). The loop runs eight
  times: `rsi` walks up `z` from 0, `rdx` down from `z + 240`, 16 bytes each,
  `rdi` up `W` 32 bytes per iteration; it stops when `rsi ≥ rdx` (signed).
* Conditions: `W`, `z` 16-aligned (aligned `movaps` loads and stores), and
  `ff_ps_neg` 16-aligned (the aligned `movaps ff_ps_neg(%rip)`). One condition
  beyond checkasm: `z.toInt + 240 < 2^63`, i.e. `z .. z + 240` does not cross
  the signed boundary. The exit test is `jl`, a signed compare of the two
  pointers; were `z + 112 < 2^63 ≤ z + 128`, the compare after the eighth
  iteration (`rsi = z + 128`, `rdx = z + 112`) would see `rsi < rdx` and run on
  past both arrays. It holds of every user-space pointer (canonical addresses are
  below `2^47`). Dropping it makes the `.cmp` block fail (`qmf_jl_taken` has no
  hypothesis to use); dropping the alignment of `W` makes the loop block fail
  (negative checks, scratch).
* No stack, no callee-saved register touched: the reservation is 0.
* Proof shape: blocks are cut by free labels into the SSE body (`.loop`, closed
  by `vcgen with finish`), the pointer updates (`.step`), the compare and branch
  (`.cmp`) and the `ret` (`.done`). The loop invariant carries the pointers both
  as equations in the offset `o = rsi - z` (`rdx = z + (240 - o)`,
  `rdi = W + (o + o)`) and as the offsets of the accesses into their blocks
  (`(rdx - z).toNat`, `(rdi - W).toNat`), so that the SSE block needs no
  bit-vector ring reasoning. The pointer arithmetic is in the lemmas below,
  proved by `grind`/`bv_omega`/`omega`, and handed to `grind -ring` at `.step` and
  to `grind` at `.cmp`. With the ring solver on, `grind` hit an internal
  assertion (`CommRing.mkImpEqExprProof`) on the `.step` goal and produced a
  proof the kernel rejected (`unknown constant _inhabitedExprDummy`); in the
  uncut loop block, `grind`/`finish` timed out.
* The signed `jl` exit: `qmf_jl_taken` reads `CondCode.l` on the flags of
  `cmp %rdx,%rsi` as `rsi.slt rdx` (`CondCode.interp_l_cmp`, in
  `Kraken/Rules/LeafLemmas.lean`), then as `o < 120` through
  `BitVec.toInt_add_of_not_saddOverflow`.
* Rule-file `grind` scopes opened (see `Kraken/Rules/*.lean`):
  `Kraken.Rules.GenericMem.Norm`.
-/

open Kraken.X64.Parser
open Kraken
open Kraken.SysV
open Std.WP
open Mem
open MachineWP
open scoped Kraken.Rules.GenericMem.Norm

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.QmfPostShuffle

/-! ## Pointer arithmetic of the loop

Local facts about the loop's offsets, proved by `grind`/`bv_omega`/`omega` and
handed to `grind` in the blocks (not general rules). -/

/-- The `jl` back edge: at `.cmp`, with `o = rsi - z` in `[16, 128]` and
`rdx = z + (240 - o)`, the signed compare `cmp %rdx,%rsi; jl` is taken only when
`o < 120`; so `o < 128` again at `.loop`, and the variant `rdx - rsi` drops by
32 from its value at `.cmp`. Needs `z.toInt + 240 < 2^63`. -/
theorem qmf_jl_taken {z r d : BitVec 64} (hz : z.toInt + 240 < 2 ^ 63)
    (h1 : 16 ≤ (r - z).toNat) (h2 : (r - z).toNat ≤ 128) (hd : d = z + (240#64 - (r - z)))
    {cf af : Bool}
    (h : CondCode.l.interp (StatusFlags.from_result (r - d)
      { cf := cf, af := af, of := (r - d).signed != r.signed - d.signed }) = true) :
    (r - z).toNat < 128 ∧ (d - r).toNat < (d - r + 32#64).toNat := by
  generalize ho : r - z = o at h1 h2 hd
  have hr : r = z + o := by rw [← ho]; bv_omega
  subst hr hd
  have hz0 := BitVec.le_toInt z
  have hon : o.toInt = o.toNat := BitVec.toInt_eq_toNat_of_lt (by omega)
  have hrn : (z + o).toInt = z.toInt + o.toNat := by
    rw [BitVec.toInt_add_of_not_saddOverflow] <;> simp [BitVec.saddOverflow] <;> omega
  have hcn : (240#64 - o).toNat = 240 - o.toNat := by
    rw [BitVec.toNat_sub_of_le (by bv_omega)]; simp
  have hci : (240#64 - o).toInt = 240 - o.toNat := by
    rw [BitVec.toInt_eq_toNat_of_lt (by omega), hcn]; omega
  have hdn : (z + (240#64 - o)).toInt = z.toInt + (240 - o.toNat) := by
    rw [BitVec.toInt_add_of_not_saddOverflow, hci]
    simp only [BitVec.saddOverflow, hci, Bool.or_eq_true, decide_eq_true_eq, not_or]; omega
  rw [CondCode.interp_l_cmp, BitVec.slt_eq_decide, decide_eq_true_eq, hrn, hdn] at h
  have h120 : o.toNat < 120 := by omega
  refine ⟨by omega, ?_⟩
  bv_omega

/-- One step of the loop's offset: `rsi` advances 16 bytes within `z`. -/
theorem qmf_step {z r : BitVec 64} (h : (r - z).toNat < 128) :
    (r + 16#64 - z).toNat = (r - z).toNat + 16 := by
  bv_omega

/-- The `rdx` relation of the loop invariant, one step on. -/
theorem qmf_step_rdx {z r d : BitVec 64} (hd : d = z + (240#64 - (r - z))) :
    d - 16#64 = z + (240#64 - (r + 16#64 - z)) := by
  subst hd; grind

/-- The `rdi` relation of the loop invariant, one step on. -/
theorem qmf_step_rdi {W z r i : BitVec 64} (hi : i = W + ((r - z) + (r - z))) :
    i + 32#64 = W + ((r + 16#64 - z) + (r + 16#64 - z)) := by
  subst hi; grind

/-- The variant across the loop body: `rdx - rsi` shrinks by 32, re-added at `.cmp`. -/
theorem qmf_var_step (d r : BitVec 64) : d - 16#64 - (r + 16#64) + 32#64 = d - r := by
  grind

/-- The loop's accesses as offsets into their blocks: the load at `rdx` inside `z`,
the two stores at `rdi` inside `W`, all 16-aligned offsets. -/
theorem qmf_loop_facts {W z r d i : BitVec 64} (hd : d = z + (240#64 - (r - z)))
    (hi : i = W + ((r - z) + (r - z))) (h : (r - z).toNat < 128) (h16 : (r - z).toNat % 16 = 0) :
    (d - z).toNat + 16 ≤ 256 ∧ (d - z).toNat % 16 = 0
    ∧ (i - W).toNat + 32 ≤ 256 ∧ (i - W).toNat % 16 = 0 := by
  generalize r - z = o at hd hi h h16
  subst hd hi
  have e1 : z + (240#64 - o) - z = 240#64 - o := by grind
  have e2 : W + (o + o) - W = o + o := by grind
  rw [e1, e2, BitVec.toNat_sub, BitVec.toNat_add]
  simp only [BitVec.toNat_ofNat]
  omega

variable [CodeEnv]


/-- The caller's side of memory behind the footprint: the return address,
the empty reservation and `R`. A `def`, so that `grind` moves it whole. -/
def Rest (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) : Mem 64 → Prop :=
  RetCell ra (t₀.regs.get64 .rsp) ⋆ (Reserve 0 (t₀.regs.get64 .rsp) ⋆ R)

/-- The assertion at each label: the entry state; at `.loop`/`.step` the
invariant (offset `o = rsi - z < 128`, a multiple of 16, `rdx`, `rdi` as
functions of `o` and as offsets into their blocks); at `.cmp` the same after the
pointer updates (`16 ≤ o ≤ 128`); at `.done` the convention's registers. -/
abbrev table (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) :
    Label → MachineData → Prop
  | "ff_sbr_qmf_post_shuffle_sse", s => s = t₀ ∧ QmfPostShuffleC t₀
      ∧ (t₀.dmem =⋆ QmfPostShuffleF t₀ ⋆ Rest R ra t₀)
  | "ff_sbr_qmf_post_shuffle_sse.loop", s =>
      let W := arg0 t₀
      let z := arg1 t₀
      let o := s.regs.get64 .rsi - z
      QmfPostShuffleC t₀ ∧ o.toNat < 128 ∧ o.toNat % 16 = 0
      ∧ s.regs.get64 .rdx = z + (240#64 - o) ∧ s.regs.get64 .rdi = W + (o + o)
      ∧ (s.regs.get64 .rdx - z).toNat + 16 ≤ 256 ∧ (s.regs.get64 .rdx - z).toNat % 16 = 0
      ∧ (s.regs.get64 .rdi - W).toNat + 32 ≤ 256 ∧ (s.regs.get64 .rdi - W).toNat % 16 = 0
      ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp
      ∧ SavedRegs t₀ s
      ∧ (s.dmem =⋆ QmfPostShuffleF t₀ ⋆ Rest R ra t₀)
  | "ff_sbr_qmf_post_shuffle_sse.step", s =>
      let W := arg0 t₀
      let z := arg1 t₀
      let o := s.regs.get64 .rsi - z
      QmfPostShuffleC t₀ ∧ o.toNat < 128 ∧ o.toNat % 16 = 0
      ∧ s.regs.get64 .rdx = z + (240#64 - o) ∧ s.regs.get64 .rdi = W + (o + o)
      ∧ (s.regs.get64 .rdx - z).toNat + 16 ≤ 256 ∧ (s.regs.get64 .rdx - z).toNat % 16 = 0
      ∧ (s.regs.get64 .rdi - W).toNat + 32 ≤ 256 ∧ (s.regs.get64 .rdi - W).toNat % 16 = 0
      ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp
      ∧ SavedRegs t₀ s
      ∧ (s.dmem =⋆ QmfPostShuffleF t₀ ⋆ Rest R ra t₀)
  | "ff_sbr_qmf_post_shuffle_sse.cmp", s =>
      let W := arg0 t₀
      let z := arg1 t₀
      let o := s.regs.get64 .rsi - z
      QmfPostShuffleC t₀ ∧ 16 ≤ o.toNat ∧ o.toNat ≤ 128 ∧ o.toNat % 16 = 0
      ∧ s.regs.get64 .rdx = z + (240#64 - o) ∧ s.regs.get64 .rdi = W + (o + o)
      ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp
      ∧ SavedRegs t₀ s
      ∧ (s.dmem =⋆ QmfPostShuffleF t₀ ⋆ Rest R ra t₀)
  | "ff_sbr_qmf_post_shuffle_sse.done", s =>
      s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp
      ∧ SavedRegs t₀ s
      ∧ (s.dmem =⋆ QmfPostShuffleF t₀ ⋆ Rest R ra t₀)
  | _, _ => False

/-- The variant: `rdx - rsi` (`240 - 2o`) at `.loop`/`.step`, the same plus 32 at
`.cmp` (so the fall-through edges do not increase it and the back edge drops
it by 32); 0 at `.done`. -/
abbrev var : Label → MachineData → Nat
  | "ff_sbr_qmf_post_shuffle_sse.loop", s => (s.regs.get64 .rdx - s.regs.get64 .rsi).toNat
  | "ff_sbr_qmf_post_shuffle_sse.step", s => (s.regs.get64 .rdx - s.regs.get64 .rsi).toNat
  | "ff_sbr_qmf_post_shuffle_sse.cmp", s => (s.regs.get64 .rdx - s.regs.get64 .rsi + 32#64).toNat
  | "ff_sbr_qmf_post_shuffle_sse.done", _ => 0
  | _, _ => 2 ^ 64

/-- What the exit block leaves: `CallPost` with the footprint in front. -/
abbrev Post' (R : Mem 64 → Prop) (ra : Int64) (t₀ s : MachineData) : Prop :=
  s.regs.get64 .rsp = t₀.regs.get64 .rsp + 8
  ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp ∧ SavedRegs t₀ s
  ∧ (s.dmem =⋆ QmfPostShuffleF t₀ ⋆ (8 ?@ (t₀.regs.get64 .rsp)
      ⋆ (Reserve 0 (t₀.regs.get64 .rsp) ⋆ R)))

set_option maxHeartbeats 1000000 in
theorem spec (hpl : Program.PlacedIn body) : QmfPostShuffleSpec := by
  refine Kraken.Executable.ProcSpec.of_cfg_post (p := body) table Post' var
    (hblocks := ?_) (hpre := ?_) (hpost := ?_)
  · intro R ra t₀
    cfg_cases [body]
    · vcgen with finish
    · vcgen with finish
    · vcgen
      rename_i n _ _ s hT
      dsimp only at hT
      have hs := qmf_step hT.1.2.1
      have hd := qmf_step_rdx hT.1.2.2.2.1
      have hi := qmf_step_rdi hT.1.2.2.2.2.1
      have hv := qmf_var_step (s.regs.get64 .rdx) (s.regs.get64 .rsi)
      grind -ring
    · vcgen
      · rename_i n _ _ _ s hT hc
        dsimp only at hT hc
        have hj := qmf_jl_taken hT.1.1.2.2.2 hT.1.2.1 hT.1.2.2.1 hT.1.2.2.2.2.1 hc
        have hf := qmf_loop_facts hT.1.2.2.2.2.1 hT.1.2.2.2.2.2.1 hj.1 hT.1.2.2.2.1
        grind
      · grind
    · vcgen
      all_goals simp only [Rest] at *
      all_goals call_simp
      all_goals grind_cells
  · rintro R ra t ⟨hcall, hc⟩
    refine ⟨rfl, hc, ?_⟩
    have h := hcall
    simp only [Rest, CallPre] at h ⊢
    rw [Std.ExtHashMap.sep_comm_l (Reserve _ _), Std.ExtHashMap.sep_comm_l (RetCell _ _)] at h
    exact h
  · rintro R ra t₀ s ⟨h1, h2, h3, hm⟩
    refine ⟨h1, h2, h3, ?_⟩
    show (_ ⋆ (_ ⋆ (QmfPostShuffleF t₀ ⋆ R))) s.dmem
    rw [Std.ExtHashMap.sep_comm_l (Reserve _ _), Std.ExtHashMap.sep_comm_l (Block _ _)]
    exact hm

end Kraken.Examples.Sbr.QmfPostShuffle
