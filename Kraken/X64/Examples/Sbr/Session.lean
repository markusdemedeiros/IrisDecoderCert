import Kraken.X64.Examples.Sbr.Link
import Kraken.X64.Examples.Sbr.SessionSpec

/-!
# A decoding session of `ff_aac_sbr_apply`

`ff_aac_sbr_apply_linked` (`Link.lean`) is a statement about one call: given the footprint
`ApplyF e x t`, the layout `LayoutC x t` and the decoder invariant `SbrWF x`, the call is
memory-safe and returns owning the footprint at values `y` with `SbrWF y` again. This file
puts calls in sequence. It is pure Lean: no machine code is proved here, and nothing here is
imported by the linked theorem.

A session of one channel element (`ExtChannelElement`, `aacsbr_template.c`) runs

  `ff_aac_sbr_ctx_alloc_init`, then repeatedly: the parser, the caller's frame changes, and a
  call `ff_aac_sbr_apply`.

Of the precondition `ApplyPre k e x ra t = CallPre … ∧ SbrWF x ∧ LayoutC x t`, the stack and
the footprint (`CallPre`) and the layout are facts about the call state the caller builds
(`CallerFrame`); `SbrWF x` is the one conjunct that depends on the history. It is the
invariant of the session:

* `xInit`: the values `ff_aac_sbr_ctx_alloc_init` leaves; `sbrWF_xInit` proves `SbrWF` of them.
* `Reachable step x₀`: the values reachable from `x₀` by apply steps (`ApplyRel`, the value
  part of the linked theorem's postcondition `ApplyFPost`), parser steps (`step`) and frame
  steps (`FrameStep`).
* `reachable_wf`, `reachable_init_wf`: every reachable value satisfies `SbrWF`, under
  `ParseStep step Inv`.
* `applyFPost_reachable`: the induction step; a call's postcondition owns the footprint at values
  that are reachable again.
* `session_call`: at every reachable value, a call state with the caller's frame satisfies
  `ApplyPre`, the call returns (`ApplyPost`), and it returns owning the footprint at reachable
  values again.

What is assumed, and where:
* the parser: `ParseStep step Inv` (it preserves `SbrWF` together with a parser-side invariant
  `Inv` that reads only the values apply keeps and holds after init, and it does not move the
  `av_tx` contexts and `ac->fdsp`). Not proved; it is the interface the proof of the parser must
  meet. `step` and `Inv` are parameters.
* the caller's frame: `CallerFrame` at each call (the stack, the footprint at the session's
  current values, the layout). What the caller may change between calls is `FrameStep` on the
  values and anything in the call state that `CallerFrame` allows (new `L`/`R` buffers, a new
  stack, `ac` fields).
* init: that the machine code of `ff_aac_sbr_ctx_alloc_init` (with `av_mallocz`) writes the
  values `xInit`. Not proved here; `sbrWF_xInit` proves only that those values satisfy the
  invariant.
* the linked theorem's own hypotheses `SbrPlaced`, `SbrSlots e`, `SbrAssumed k e`.

Citations are to `libavcodec/aacsbr_template.c` (FFmpeg n8.1) unless marked: `PC` is
`aacps_common.c`, `P` is `aacps.c`, `PH` is `aacps.h`, `D` is `aac/aacdec.c`, `U` is
`aac/aacdec_usac.c`.
-/

open Kraken Kraken.X64.Parser Std.WP MachineWP Kraken.SysV Mem

namespace Kraken.Examples.Sbr.Session

open Apply

variable [CodeEnv]

/-! ## The steps of a session -/

/-! ## Building blocks for the parser's proof

Two steps that the parser's paths share, proved to preserve `SbrWF`: `sbr_turnoff`, which ends
every failure path, and the save of `kx[1]`, `m[1]`. -/

omit [CodeEnv] in
/-- `DWF` is antitone in `live`. -/
theorem DWF.mono {L L' : Prop} {v : DV} (hL : L' → L) (h : DWF L v) : DWF L' v := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, fun h => a16 (hL h)⟩

/-- `sbr_turnoff` (l.58-68) preserves `SbrWF`: `start = 0` switches off the guarded clauses,
`kx[1] = 32`, `m[1] = 0` meet the bounds. (Its other writes, `usac`, `e_a[1]`,
`spectrum_params`, are raw in the footprint.) -/
theorem sbrWF_turnoff {x : Args} (h : SbrWF x) : SbrWF x.turnoff := by
  obtain ⟨a1, -, a3, -, -, a6, a7, a8, a9, a10, a11, a12, -, d0, d1, ps⟩ := h
  exact ⟨a1, (by decide : 32 ≤ 32), a3, (by decide : 32 + 0 ≤ 64), (by decide : 0 ≤ 48), a6, a7,
    a8, a9, a10, a11, a12, fun h => absurd rfl h, d0.mono (fun h => absurd rfl h),
    d1.mono (fun h => absurd rfl h.1), ps⟩

omit [CodeEnv] in
/-- Saving `kx[1]`, `m[1]` (l.1157-1159, l.1263-1265, and the prologue of apply, l.1705-1710)
preserves `SbrWF`. -/
theorem sbrWF_save {x : Args} (p : BitVec 32) (h : SbrWF x) :
    SbrWF { x with kx0 := x.kx1, m0 := x.m1, pushed := p } := by
  obtain ⟨-, a2, -, a4, a5, a6, a7, a8, a9, a10, a11, a12, b, d0, d1, ps⟩ := h
  exact ⟨a2, a2, a4, a4, a5, a6, a7, a8, a9, a10, a11, a12, b, d0, d1, ps⟩

/-! ## The values after `ff_aac_sbr_ctx_alloc_init` -/

omit [CodeEnv] in
/-- `PsWF` of a zeroed `PSContext` (W1-W6 hold of zeros; `start = 0`). -/
theorem psWF_zero : PsWF (zs 764) (zs 68) := by
  unfold PsWF
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    fun h => absurd (by decide +kernel) h⟩

/-- **Init.** The values `ff_aac_sbr_ctx_alloc_init` leaves satisfy `SbrWF`, for every element
type, `av_tx` contexts, caller memory and `ac` fields. Proved: the values satisfy the
invariant. Assumed (step (a), not here): that init's machine code (with `av_mallocz`), in a
call that returns 0, writes these values. -/
theorem sbrWF_xInit (i : InitIn) : SbrWF (xInit i) := by
  have hd : DWF False dvInit := by
    unfold DWF
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
      by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
      by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
      by decide +kernel, False.elim⟩
  exact ⟨(by decide : 0 ≤ 32), (by decide : 32 ≤ 32), (by decide : 0 + 0 ≤ 64),
    (by decide : 32 + 0 ≤ 64), (by decide : 0 ≤ 48), (by decide : 0 ≤ 32), (by decide : 0 ≤ 3),
    (by decide : 0 ≤ 24), (by decide : 0 ≤ 48), (by decide : 0 ≤ 5), (by decide : 0 ≤ 29),
    (by decide : 0 ≤ 6), fun h => absurd rfl h,
    hd.mono (fun h => absurd rfl h), hd.mono (fun h => absurd rfl h.1), psWF_zero⟩

/-! ## A parser-side invariant -/

omit [CodeEnv] in
/-- `GridInv` reads only `bs_num_env` and `t_env`, which apply keeps. -/
theorem gridInv_stable {x y : Args} (h : x.KeepD y) (hx : GridInv x) : GridInv y := by
  obtain ⟨h1, h2, h3, h4, -⟩ := h
  unfold GridInv; rw [h1, h2, h3, h4]; exact hx

omit [CodeEnv] in
/-- `GridInv` holds after init (`bs_num_env = 0`, `t_env` zero). -/
theorem gridInv_init (i : InitIn) : GridInv (xInit i) :=
  ⟨(by decide : u8 (zs 10) 0 ≤ 19), (by decide : u8 (zs 10) 0 ≤ 19)⟩

/-- The parser's step, as an assumption about a relation `step` on the values, with a
parser-side invariant `Inv`.

`Inv` is there because `SbrWF` alone is not preserved by the parser: `SbrWF` bounds
`t_env[bs_num_env]` only for a live grid (`DWF`'s `live` clause), but the next `read_sbr_grid`
copies it into `t_env_num_env_old` (l.651; `copy_sbr_grid`, l.788), which `DWF` bounds
unconditionally (`u8 v.te 9 ≤ 19`). A value with `start = 0`, `bs_num_env = 1`,
`t_env[1] = 200` satisfies `SbrWF`, and a header plus a valid grid would take it to one that does
not. The real decoder never holds such a value (every grid stores
`t_env[bs_num_env] = abs_bord_trail ≤ 19` before its checks, l.669/685/700/724), so the parser's
proof needs a stronger invariant; `GridInv` is the candidate for this clause. Likewise for the
tables: `SbrWF`'s `TabWF` does not include `n[0] ≥ 1`, `num_patches ≥ 1`, which a header without
reset needs (`ParseModel.Inv2`). The model uses `Inv := GridInv ∧ Inv2`.
`Inv := fun _ => True` is allowed, but then `wf` is the stronger obligation. `Inv` must read
only the values apply does not write (`stable`; `KeepD` covers the grid, `ps->common`, `k[0]`
and the tables, and lets apply only clear `start`), so that apply and the frame steps preserve
it without assumptions.

`step` is a parameter of the session, not a model of the parser: any relation that meets
`ParseStep` will do, including a vacuous one. The result is about the real decoder only once
`ParseStep` is discharged for the relation induced by the parser's code (step (b)).

`step x x'` relates the values after one call of `ff_aac_sbr_apply` (or after init) to the
values at the next call: in between the decoder ran any number of
`ff_aac_sbr_decode_extension` (l.1134-1180), `ff_aac_sbr_config_usac` (l.1201-1207) and
`ff_aac_sbr_decode_usac_data` (l.1209-) calls on this element, including failed ones. Only the
values at the next call matter, so a transient state that violates `SbrWF` between two calls is
not a counterexample, as long as the parse that precedes the next call repairs it (e.g. a USAC
frame that returns at a rejected `read_sbr_grid` with `start = 1`, l.1294-1295, returns before
apply, `U`:1659-1661).

What the parser may change (all through `step`, constrained only by `wf`):
* `start`, `ready_for_dequant`, `reset` (l.197-198, 229, 1074-1075, 1144, 1218, 1259, 1270,
  `sbr_turnoff` l.58-68 at l.1079/1084/1090/1122/1177/1205);
* `id_aac` (l.1074, 1222) and `sample_rate` (l.1146-1147, 1221);
* `kx[0..1]`, `m[0..1]`, `k[0]`, `kx_and_m_pushed` (l.1157-1159, 1263-1265, `sbr_make_f_master`
  / `sbr_make_f_derived`);
* the header fields `bs_limiter_gains`, `bs_interpol_freq`, `bs_smoothing_mode` (l.230-241),
  `bs_coupling` (l.1026, 1290, 1322);
* the tables `n[]`, `n_q`, `n_lim`, `num_patches`, `patch_*`, `f_table*` (`sbr_reset`,
  l.1113-1124; `sbr_make_f_tablelim` also from the header, l.243);
* each channel's grid and side info: `bs_num_env`, `bs_freq_res`, `t_env`, `t_q`,
  `bs_num_noise`, `bs_invf_mode` (`read_sbr_grid`, `read_sbr_invf`), and `f_indexnoise := 0`
  (l.618-619);
* `ps->common` (`ff_ps_read_data`, l.977; `PC`:133-289);
* the `ac` field `ext_sample_rate` (l.1148-1149), and the caller's memory (`ac->avctx->profile`,
  l.978).

What it does not write (fields of `Args` written only elsewhere): the `av_tx` contexts
`sbr->mdct`, `sbr->mdct_ana` (only `ff_aac_sbr_ctx_alloc_init`, l.95-106) and `ac->fdsp`: these
are `keep`, the only frame condition the session needs. Also not written by the parser, but not
assumed because nothing here needs it: both `synthesis_filterbank_samples_offset` (l.88-89 and
`sbr_qmf_synthesis`), `Ypos` (l.1725), `f_indexsine` (`aacsbr.c` `sbr_hf_assemble`), the PS
phase histories (`P`:607, 625, 649-650). `SbrWF` constrains some of them; `wf` covers them. -/
structure ParseStep (step : Args → Args → Prop) (Inv : Args → Prop) : Prop where
  /-- The parser re-establishes the invariants by the next call. -/
  wf : ∀ x x', SbrWF x → Inv x → step x x' → SbrWF x' ∧ Inv x'
  /-- The parser's invariant reads only the values apply keeps (`KeepD`). -/
  stable : ∀ x y, x.KeepD y → Inv x → Inv y
  /-- It holds after init. -/
  init : ∀ i, Inv (xInit i)
  /-- The parser does not move the `av_tx` contexts and `ac->fdsp`. -/
  keep : ∀ x x', step x x' → x'.anaCtx = x.anaCtx ∧ x'.synCtx = x.synCtx ∧ x'.fdsp = x.fdsp

/-- The values of a session started at `x₀`: closed under apply steps (`ApplyRel`), parser
steps (`step`) and frame steps (`FrameStep`). An over-approximation: `apply` allows every
`y` the linked theorem's postcondition allows, not only those the code produces. -/
inductive Reachable (step : Args → Args → Prop) (x₀ : Args) : Args → Prop
  | init : Reachable step x₀ x₀
  | apply {x y : Args} : Reachable step x₀ x → ApplyRel x y → Reachable step x₀ y
  | parse {x x' : Args} : Reachable step x₀ x → step x x' → Reachable step x₀ x'
  | frame {x x' : Args} : Reachable step x₀ x → FrameStep x x' → Reachable step x₀ x'

/-! ## The invariant -/

omit [CodeEnv] in
/-- `SbrWF` does not read the frame fields. -/
theorem sbrWF_frame {x x' : Args} (h : FrameStep x x') (hx : SbrWF x) : SbrWF x' := by
  rw [h]; exact hx

omit [CodeEnv] in
/-- A frame step keeps the decoder state apply keeps. -/
theorem FrameStep.keepD {x x' : Args} (h : FrameStep x x') : x.KeepD x' := by
  rw [h]
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  unfold Args.KeepT
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Or.inr ⟨rfl, rfl, rfl⟩⟩

omit [CodeEnv] in
/-- **The session invariant.** Under the parser assumption, every value reachable from a
start satisfying `SbrWF` and the parser's invariant satisfies both. -/
theorem reachable_wf {step : Args → Args → Prop} {Inv : Args → Prop} (hP : ParseStep step Inv)
    {x₀ x : Args} (h₀ : SbrWF x₀ ∧ Inv x₀) (h : Reachable step x₀ x) : SbrWF x ∧ Inv x := by
  induction h with
  | init => exact h₀
  | apply _ hr ih => exact ⟨hr.2.2.2.2.2.2.1, hP.stable _ _ hr.2.2.2.2.2.1 ih.2⟩
  | parse _ hs ih => exact hP.wf _ _ ih.1 ih.2 hs
  | frame _ hf ih => exact ⟨sbrWF_frame hf ih.1, hP.stable _ _ hf.keepD ih.2⟩

/-- Every value reachable from init satisfies `SbrWF`. -/
theorem reachable_init_wf {step : Args → Args → Prop} {Inv : Args → Prop}
    (hP : ParseStep step Inv) (i : InitIn) {x : Args} (h : Reachable step (xInit i) x) :
    SbrWF x :=
  (reachable_wf hP ⟨sbrWF_xInit i, hP.init i⟩ h).1

omit [CodeEnv] in
/-- The `av_tx` contexts and `ac->fdsp` of every reachable value are those of the start, so
`FnW`'s cells and `e.Ctx` contexts are the same objects at every call. -/
theorem reachable_ptrs {step : Args → Args → Prop} {Inv : Args → Prop} (hP : ParseStep step Inv)
    {x₀ x : Args} (h : Reachable step x₀ x) :
    x.anaCtx = x₀.anaCtx ∧ x.synCtx = x₀.synCtx ∧ x.fdsp = x₀.fdsp := by
  induction h with
  | init => exact ⟨rfl, rfl, rfl⟩
  | apply _ hr ih => exact ⟨hr.2.2.1.trans ih.1, hr.2.2.2.1.trans ih.2.1, hr.2.1.trans ih.2.2⟩
  | parse _ hs ih =>
    obtain ⟨a, s, f⟩ := hP.keep _ _ hs
    exact ⟨a.trans ih.1, s.trans ih.2.1, f.trans ih.2.2⟩
  | frame _ hf ih =>
    rw [hf]; exact ih

/-! ## The calls of a session -/

/-- `ApplyFPost` is `ApplyRel` with the footprint at the new values. -/
theorem applyFPost_iff {e : Env} {x : Args} {t : MachineData} {m : Mem 64} :
    ApplyFPost e x t m ↔ ∃ y, ApplyRel x y ∧ ApplyF e y t m := by
  constructor
  · rintro ⟨y, h1, h2, h3, h4, h5, h6, h7, h9, h10, h8⟩
    exact ⟨y, ⟨h1, h2, h3, h4, h5, h6, h7, h9, h10⟩, h8⟩
  · rintro ⟨y, ⟨h1, h2, h3, h4, h5, h6, h7, h9, h10⟩, h8⟩
    exact ⟨y, h1, h2, h3, h4, h5, h6, h7, h9, h10, h8⟩

/-- The caller's frame at a call: the call state `t` holds the return address, `applyNeed k`
bytes of stack below it, and owns the footprint at the values `x` with the caller's memory
`x.R` (`CallPre`), and the layout holds (`LayoutC`: `ac`, `che`, `L`, `R` 32-aligned, the stack
16-aligned at the call, the constants' alignment). Between calls the caller may pick a new
stack, new `L`/`R` buffers, change the `ac` fields (`FrameStep`); the SBR state itself is
presented at the session's current values (`Reachable`), i.e. it is changed only by the parser
and by apply. -/
structure CallerFrame (k : Nat) (e : Env) (x : Args) (ra : Int64) (t : MachineData) : Prop where
  own : CallPre (applyNeed k) (ApplyF e x t ⋆ x.R) ra t
  layout : LayoutC x t

/-- The footprint without the output buffers: everything `ApplyF` owns but `OutW`. -/
def ApplyCore (e : Env) (x : Args) (t : MachineData) : Mem 64 → Prop :=
  ScW x t ⋆ (TabW x t ⋆ (DScW x.d0 t 0 ⋆ (DScW x.d1 t 1 ⋆ (DArrW t 0 ⋆ (DArrW t 1
    ⋆ (ArrW t ⋆ (PsW x t ⋆ (DspW e t ⋆ (FnW e x t ⋆ (AcW x t ⋆ CstW))))))))))

/-- The footprint is the core and the output buffers `L`, `R`. -/
theorem applyF_split (e : Env) (x : Args) (t : MachineData) :
    ApplyF e x t = ApplyCore e x t ⋆ OutW x t := by
  simp only [ApplyF, ApplyCore, Std.ExtHashMap.sep_assoc]

/-- The core depends on the call state only through `ac` and `che` (`rdi`, `rsi`): between two
calls on the same element the caller keeps it as it is and supplies new `L`, `R` (`OutW`) and a
new stack. -/
theorem applyCore_congr (e : Env) (x : Args) {t t' : MachineData} (h0 : arg0 t' = arg0 t)
    (h1 : arg1 t' = arg1 t) : ApplyCore e x t' = ApplyCore e x t := by
  simp only [ApplyCore, ScW, TabW, DScW, DArrW, ArrW, PsW, DspW, FnW, AcW, sbrA, dA, h0, h1]

/-- Pull the values out of the postcondition's memory. -/
theorem post_mem {k : Nat} {e : Env} {x : Args} {t : MachineData} {m : Mem 64}
    (h : m =⋆ 8 ?@ (t.regs.get64 .rsp) ⋆ (Reserve (applyNeed k) (t.regs.get64 .rsp)
      ⋆ (ApplyFPost e x t ⋆ x.R))) :
    ∃ y, ApplyRel x y ∧ (m =⋆ 8 ?@ (t.regs.get64 .rsp) ⋆ (Reserve (applyNeed k)
      (t.regs.get64 .rsp) ⋆ (ApplyF e y t ⋆ x.R))) := by
  obtain ⟨a, b, hu, hi, ha, c, d, hu2, hi2, hc, f, g, hu3, hi3, hf, hg⟩ := h
  obtain ⟨y, hy, hfy⟩ := applyFPost_iff.mp hf
  exact ⟨y, hy, a, b, hu, hi, ha, c, d, hu2, hi2, hc, f, g, hu3, hi3, hfy, hg⟩

/-- **The induction step.** A call's postcondition gives back the footprint at values that
satisfy `SbrWF` and are reachable again. -/
theorem applyFPost_reachable {step : Args → Args → Prop} {x₀ x : Args} {e : Env}
    {t : MachineData} {m : Mem 64} (hx : Reachable step x₀ x) (h : ApplyFPost e x t m) :
    ∃ y, SbrWF y ∧ Reachable step x₀ y ∧ ApplyRel x y ∧ ApplyF e y t m := by
  obtain ⟨y, hy, hm⟩ := applyFPost_iff.mp h
  exact ⟨y, hy.2.2.2.2.2.2.1, hx.apply hy, hy, hm⟩

/-- **A call in a session.** Under the linked theorem's hypotheses and the parser assumption,
at every value `x` reachable from init and every call state with the caller's frame:
`ApplyPre` holds (its `SbrWF` conjunct from `reachable_init_wf`), and the run from the entry
returns to `ra` with `ApplyPost` and owning the footprint at values `y` that are reachable
again, with `ApplyRel x y`. -/
theorem session_call (hpl : SbrPlaced) (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env)
    (hslots : SbrSlots e) (hasm : SbrAssumed k e) {step : Args → Args → Prop}
    {Inv : Args → Prop} (hP : ParseStep step Inv) (i : InitIn) {x : Args}
    (hx : Reachable step (xInit i) x)
    {ra : Int64} {t : MachineData} (hfr : CallerFrame k e x ra t) :
    ApplyPre k e x ra t
    ∧ Eventually cenv.instrStep (fun st => st.2 = ra ∧ ApplyPost k e x ra t st.1
        ∧ ∃ y, Reachable step (xInit i) y ∧ ApplyRel x y
          ∧ (st.1.dmem =⋆ 8 ?@ (t.regs.get64 .rsp)
              ⋆ (Reserve (applyNeed k) (t.regs.get64 .rsp) ⋆ (ApplyF e y t ⋆ x.R))))
      (t, entry "ff_aac_sbr_apply") := by
  have hpre : ApplyPre k e x ra t :=
    ⟨hfr.own, reachable_init_wf hP i hx, hfr.layout⟩
  refine ⟨hpre, ?_⟩
  refine eventually_weaken _ _ _ _ (fun st ⟨hra, hpost⟩ => ⟨hra, hpost, ?_⟩)
    (ff_aac_sbr_apply_linked hpl k hk e hslots hasm x ra t hpre)
  obtain ⟨y, hy, hm⟩ := post_mem hpost.2.2.2
  exact ⟨y, hx.apply hy, hy, hm⟩

end Kraken.Examples.Sbr.Session
