import SbrClient.Host.Rules

namespace SbrClient.Host
open Kraken Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Iris.Std
variable {hlc : HasLC} {M : Model} {GF : BundledGFunctors} [MachineGS hlc M GF]
local bi (IProp GF)

theorem wp_fork (child : Expr M) {E : CoPset} {Φ : Value → IProp GF} :
    ▷ (WP child @ Stuckness.NotStuck; ⊤ {{ _v, True }}) ∗ ▷ Φ .unit ⊢
      WP (Expr.fork child) @ Stuckness.NotStuck; E {{ Φ }} := by
  iintro ⟨Hchild, HΦ⟩
  iapply wp_lift_atomic_step rfl
  iintro %σ %ns %obs %obs' %nt Hσ
  imodintro
  isplit
  · ipureintro
    exact ⟨[], _, σ, [child], Step.fork⟩
  inext
  iintro %e' %σ' %efs %hs _
  cases hs
  imodintro
  iframe Hσ
  isplitl [HΦ]
  · iexists Value.unit
    iframe HΦ
    ipureintro
    rfl
  · iapply BI.BigSepL.bigSepL_singleton
    iexact Hchild

end SbrClient.Host
