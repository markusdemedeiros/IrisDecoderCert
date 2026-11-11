import Iris.ProgramLogic.WeakestPre

/-! A semantic-certificate branch for any Iris language with a local machine
model and a proved resource interpretation. Producers mention only local
execution, never Iris resources or step counts. A certificate may stop at an
intermediate expression; requiring positive progress prevents guarded
zero-step circular proofs. -/
namespace BinaryCert
open Iris Iris.ProgramLogic Iris.ProgramLogic.Language.Notation Iris.Std Iris.BI Iris.ProofMode

variable {Expr State Obs Val : Type} [Language Expr State Obs Val]
variable {hlc : HasLC} {GF : BundledGFunctors} [ι : IrisGS_gen hlc Expr GF]
local bi (IProp GF)

/-- The one-time semantic/resource bridge for a machine model. -/
structure World (Local : Type) where
  step : Expr × Local → Expr × Local → Prop
  owns : Local → IProp GF
  agrees : Local → State → Prop
  change : Local → State → Local → State → Prop
  valid : ∀ p σ ns obs nt,
    owns p ∗ stateInterp σ ns obs nt ==∗ ⌜agrees p σ⌝
  progress : ∀ {e p σ}, agrees p σ → (∃ c, step (e, p) c) →
    PrimStep.Reducible (e, σ)
  simulate : ∀ {e p σ obs e' σ' efs}, agrees p σ →
    (∃ c, step (e, p) c) → (e, σ) -<obs>-> (e', σ', efs) →
    obs = [] ∧ efs = [] ∧ ∃ p', step (e, p) (e', p') ∧ change p σ p' σ'
  update : ∀ {p σ p' σ'}, change p σ p' σ' → ∀ ns obs nt,
    owns p ∗ stateInterp σ ns obs nt ==∗
      owns p' ∗ stateInterp σ' (ns + 1) obs nt
  zero_laters : ∀ ns, ι.numLatersPerStep ns = 0

variable {Local : Type} (w : World (Expr := Expr) (State := State) (Obs := Obs) (Val := Val) (GF := GF) Local)

/-- Safety of every finite prefix until the first Q-cut. -/
def SafeN (Q : Expr → Local → Prop) : Nat → Expr → Local → Prop
  | 0, _, _ => True
  | n + 1, e, p => Q e p ∨ (toVal e = none ∧ (∃ c, w.step (e, p) c) ∧
      ∀ e' p', w.step (e, p) (e', p') → SafeN Q n e' p')

def Certificate (e : Expr) (p : Local) (Q : Expr → Local → Prop) : Prop :=
  ∀ n, SafeN w Q n e p

theorem Certificate.progress {e p Q} (h : Certificate w e p Q) (hq : ¬ Q e p) :
    toVal e = none ∧ ∃ c, w.step (e, p) c := by
  rcases h 1 with h | ⟨hv, hr, _⟩
  · exact (hq h).elim
  · exact ⟨hv, hr⟩

theorem Certificate.step {e p Q e' p'} (h : Certificate w e p Q) (hq : ¬ Q e p)
    (hs : w.step (e, p) (e', p')) : Certificate w e' p' Q := by
  intro n
  rcases h (n + 1) with h | ⟨_, _, hk⟩
  · exact (hq h).elim
  · exact hk e' p' hs

abbrev WPFun := CoPset → Expr → (Val → IProp GF) → IProp GF

/-- A whole-run certificate, plus a guarded continuation at its semantic cut. -/
def externalPre (W : WPFun (Expr := Expr) (Val := Val) (GF := GF))
    (E : CoPset) (e : Expr) (Φ : Val → IProp GF) : IProp GF := iprop%
  ∃ (p : Local) (Q : Expr → Local → Prop),
    ⌜Certificate w e p Q ∧ ¬ Q e p⌝ ∗ w.owns p ∗
    ▷ (∀ e' p', ⌜Q e' p'⌝ -∗ w.owns p' -∗ W E e' Φ)

instance externalPre_contractive : OFE.Contractive (externalPre w) where
  distLater_dist H E e Φ := by
    refine BI.exists_ne fun p => BI.exists_ne fun Q => ?_
    refine BI.sep_ne.ne .rfl (BI.sep_ne.ne .rfl ?_)
    refine OFE.Contractive.distLater_dist fun m hm => ?_
    refine BI.forall_ne fun e' => BI.forall_ne fun p' => ?_
    exact BI.wand_ne.ne .rfl (BI.wand_ne.ne .rfl (H m hm E e' Φ))

def pre (W : WPFun (Expr := Expr) (Val := Val) (GF := GF))
    (E : CoPset) (e : Expr) (Φ : Val → IProp GF) : IProp GF := iprop%
  Iris.wp.pre Stuckness.NotStuck W E e Φ ∨ externalPre w W E e Φ

instance pre_contractive : OFE.Contractive (pre w) where
  distLater_dist H E e Φ :=
    BI.or_ne.ne ((Iris.wp.pre.contractive Stuckness.NotStuck).distLater_dist H E e Φ)
      ((externalPre_contractive w).distLater_dist H E e Φ)

noncomputable def cwp : WPFun (Expr := Expr) (Val := Val) (GF := GF) := fixpoint (pre w)

theorem cwp_unfold {E e Φ} : cwp w E e Φ ⊣⊢ pre w (cwp w) E e Φ :=
  BI.equiv_iff.mp (congrFun (congrFun (congrFun
    (fixpoint_unfold (pre w).toContractiveHom) E) e) Φ)

theorem cwp_certificate {e p Q E Φ} (h : Certificate w e p Q) (hq : ¬ Q e p) :
    w.owns p ∗ ▷ (∀ e' p', ⌜Q e' p'⌝ -∗ w.owns p' -∗ cwp w E e' Φ) ⊢ cwp w E e Φ := by
  iintro H
  iapply (cwp_unfold w).mpr
  unfold pre
  iright
  unfold externalPre
  iexists p, Q
  iframe H
  ipureintro
  exact ⟨h, hq⟩

theorem cwp_value {E v Φ} : cwp w E (ToVal.ofVal v) Φ ⊣⊢ |={E}=> Φ v := by
  rw [(cwp_unfold w).to_eq, pre, Iris.wp.pre, toVal_coe]
  refine ⟨or_elim .rfl ?_, or_intro_l⟩
  unfold externalPre
  iintro ⟨%p, %Q, ⟨%hc, %hq⟩, -⟩
  have hv := (Certificate.progress w hc hq).1
  simp at hv

/-- The external case restores the state interpretation at every physical
step and retains either the residual certificate or its Iris continuation.
This proof does not translate the run into a sequence of client Iris rules. -/
theorem external_adequate {E e Φ}
    (σ : State) (ns : Nat) (obs obs' : List Obs) (nt : Nat) :
    externalPre w (cwp w) E e Φ ⊢ stateInterp σ ns (obs ++ obs') nt ={E,∅}=∗
      ⌜PrimStep.Reducible (e, σ)⌝ ∗
      ∀ e' σ' efs, ⌜(e, σ) -<obs>-> (e', σ', efs)⌝ -∗
        |={∅}▷=>^[ι.numLatersPerStep ns + 1] |={∅,E}=>
        stateInterp σ' (ns + 1) obs' (nt + efs.length) ∗
        cwp w E e' Φ ∗ [∗list] ef ∈ efs, cwp w ⊤ ef ι.forkPost := by
  unfold externalPre
  iintro ⟨%p, %Q, ⟨%hc, %hq⟩, Hp, HK⟩ Hσ
  obtain ⟨hv, hr⟩ := Certificate.progress w hc hq
  ihave %hag : ⌜w.agrees p σ⌝ $$ [Hp Hσ]
  · icases w.valid p σ ns (obs ++ obs') nt $$ [$Hp $Hσ] with >%hag
    itrivial
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  isplit
  · ipureintro
    exact w.progress hag hr
  iintro %e' %σ' %efs %hs
  obtain ⟨rfl, rfl, p', hlocal, hchange⟩ := w.simulate hag hr hs
  have hrest := Certificate.step w hc hq hlocal
  rw [w.zero_laters ns]
  simp only [step_fupdN]
  iapply step_fupd_intro LawfulSet.empty_subset
  iintro !>
  simp only [List.nil_append] at *
  imod w.update hchange ns obs' nt $$ [$Hp $Hσ] with ⟨Hp, Hσ⟩
  imod Hclose
  imodintro
  simp only [List.length_nil, Nat.add_zero, Algebra.BigOpL.bigOpL_nil]
  iframe Hσ
  by_cases hcut : Q e' p'
  · ihave HW := HK $$ %e' %p' %hcut Hp
    iframe HW
  · ihave HW : cwp w E e' Φ $$ [Hp HK]
    · iapply cwp_certificate w hrest hcut
      iframe Hp
      inext
      iexact HK
    iframe HW

/-- Projection to the ordinary one-step functional, for transporting Iris
laws. Direct external adequacy above is proved before this projection. -/
theorem external_stepPre {E e Φ} : externalPre w (cwp w) E e Φ ⊢
    Iris.wp.pre Stuckness.NotStuck (cwp w) E e Φ := by
  iintro H
  ihave %hv : ⌜toVal e = none⌝ $$ [H]
  · unfold externalPre
    icases H with ⟨%p, %Q, ⟨%hc, %hq⟩, -⟩
    ipureintro
    exact (Certificate.progress w hc hq).1
  unfold Iris.wp.pre
  rw [hv]
  iintro %σ %ns %obs %obs' %nt Hσ
  imod external_adequate w σ ns obs obs' nt $$ H Hσ with ⟨%hr, HK⟩
  imodintro
  isplit
  · ipureintro
    exact hr
  iintro %e' %σ' %efs %hs _
  iapply HK $$ %e' %σ' %efs %hs

theorem cwp_unfold_step {E e Φ} : cwp w E e Φ ⊣⊢
    Iris.wp.pre Stuckness.NotStuck (cwp w) E e Φ := by
  rw [(cwp_unfold w).to_eq]
  exact ⟨or_elim .rfl (external_stepPre w), or_intro_l⟩

/-- The extension preserves all ordinary Iris laws, by uniqueness of the
guarded fixed point. Certificate acceptance is built into cwp's definition;
this theorem is the independent soundness check and compatibility bridge. -/
theorem cwp_eq_native : cwp w = (Wp.wp (PROP := IProp GF) Stuckness.NotStuck) := by
  apply fixpoint_unique (f := (Iris.wp.pre Stuckness.NotStuck).toContractiveHom)
  funext E e Φ
  exact (cwp_unfold_step w).to_eq

theorem cwp_native {E e Φ} : cwp w E e Φ ⊣⊢
    WP e @ Stuckness.NotStuck; E {{ Φ }} := by rw [cwp_eq_native w]; exact .rfl

/-- The same certificate interface in the ordinary Iris notation, allowing
clients to reuse locks, invariants, framing and existing proof-mode rules. -/
theorem wp_certificate {e p Q E Φ} (h : Certificate w e p Q) (hq : ¬ Q e p) :
    w.owns p ∗ ▷ (∀ e' p', ⌜Q e' p'⌝ -∗ w.owns p' -∗
      WP e' @ Stuckness.NotStuck; E {{ Φ }}) ⊢ WP e @ Stuckness.NotStuck; E {{ Φ }} := by
  simpa only [cwp_eq_native w] using cwp_certificate w (E := E) (Φ := Φ) h hq

/-- Direct physical-step preservation, with separate native/certificate
cases. It does not use cwp_eq_native or external_stepPre. -/
theorem cwp_step {e σ obs e' σ' efs E Φ}
    (hs : (e, σ) -<obs>-> (e', σ', efs)) (ns : Nat) (obs' : List Obs) (nt : Nat) :
    stateInterp σ ns (obs ++ obs') nt ∗ £ (ι.numLatersPerStep ns + 1) ∗ cwp w E e Φ ⊢
      |={E,∅}=> |={∅}▷=>^[ι.numLatersPerStep ns + 1] |={∅,E}=>
      stateInterp σ' (ns + 1) obs' (nt + efs.length) ∗
      cwp w E e' Φ ∗ [∗list] ef ∈ efs, cwp w ⊤ ef ι.forkPost := by
  rw [(cwp_unfold w (E := E) (e := e) (Φ := Φ)).to_eq, pre]
  iintro ⟨Hσ, Hcred, H⟩
  icases H with (H | H)
  · simp only [Iris.wp.pre, Language.val_stuck hs]
    imod H $$ %σ %ns %obs %obs' %nt Hσ with ⟨%_, HK⟩
    imodintro
    iapply HK $$ %e' %σ' %efs %hs Hcred
  · imod external_adequate w σ ns obs obs' nt $$ H Hσ with ⟨%_, HK⟩
    imodintro
    iapply HK $$ %e' %σ' %efs %hs

end BinaryCert
