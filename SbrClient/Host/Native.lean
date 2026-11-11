import SbrClient.Host.Rules

/-! A whole-run external certificate becomes a compositional host call rule.
Every instruction remains a physical step; the return continuation starts
only at the model's empty-code return boundary. -/
namespace SbrClient.Host
open Kraken Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Iris.Std BinaryCert
variable {hlc : HasLC} {M : Model} {GF : BundledGFunctors} [MachineGS hlc M GF]
local bi (IProp GF)

theorem wp_native_run {s : MachineState} {Q : MachineState → Prop}
    (h : Eventually M.code.instrStep (fun st => st.2 = M.halt ∧ Q st) s)
    (hne : s.2 ≠ M.halt) (k : CPU → Expr M)
    {E : CoPset} {Φ : Value → IProp GF} :
    owns s.1.dmem ∗ ▷ (∀ c p, ⌜c.pc = M.halt ∧ Q (c.pack p)⌝ -∗ owns p -∗
      WP (k c) @ Stuckness.NotStuck; E {{ Φ }}) ⊢
      WP (Expr.native (.run (CPU.ofMachine s)) k) @ Stuckness.NotStuck; E {{ Φ }} := by
  iintro ⟨Hp, HK⟩
  iapply wp_native_certificate k (certificate_of_eventually machineWorld rfl h)
    (Q := SbrClient.cut (fun st => st.2 = M.halt ∧ Q st))
  · intro hh
    exact hne hh.1
  iframe Hp
  inext
  iintro %x %p %hq Hp
  cases x with
  | run c =>
      change c.pc = M.halt ∧ Q (c.pack p) at hq
      iapply wp_native_exit c k hq.1
      iapply HK $$ %c %p %hq Hp
  | done c => cases hq
  | fault => cases hq

end SbrClient.Host
