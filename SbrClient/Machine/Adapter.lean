import SbrClient.Machine.Language
import SbrClient.Logic.CertifiedWP

/-! Reuse of Kraken's original operational theorem. No instruction or FFmpeg
function proof is reproduced here. The conversion consumes Eventually over
the original executable and stops at its semantic postcondition. -/
namespace SbrClient
open Kraken Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Iris.Std BinaryCert

def cut {M : Model} (Q : MachineState → Prop) : Expr M → Mem 64 → Prop
  | .run c, m => Q (c.pack m)
  | _, _ => False

variable {M : Model} {hlc : HasLC} {GF : BundledGFunctors}
variable [ι : IrisGS_gen hlc (Expr M) GF]
variable (w : BinaryCert.World (Expr := Expr M) (GF := GF) (Mem 64))
variable (hw : w.step = LocalStep M)
include hw

theorem eventually_safeN {Q : MachineState → Prop} (n : Nat) (s : MachineState)
    (cert : Eventually M.code.instrStep Q s) :
    BinaryCert.SafeN w (cut Q) n (.run (CPU.ofMachine s)) s.1.dmem := by
  induction n generalizing s with
  | zero => trivial
  | succ n ih =>
      cases cert with
      | done s hq =>
          left
          simpa [cut] using hq
      | step s mid hs hk =>
          right
          have hne : s.2 ≠ M.halt := by
            intro heq
            have hn := boundary_no_step M.halt_empty s.1 mid
            apply hn
            simpa only [← heq] using hs
          obtain ⟨t, ht, hp⟩ := instrStep_progress hs
          have safe : (instruction M.code s).All (fun _ => True) := by
            apply (all_iff_outcomes _ _).mpr
            intro r hr
            obtain ⟨u, rfl, _⟩ := instrStep_outcome hs hr
            exact ⟨u, rfl, trivial⟩
          refine ⟨rfl, ?_, ?_⟩
          · refine ⟨(.run (CPU.ofMachine t), t.1.dmem), ?_⟩
            rw [hw]
            apply LocalStep.execute hne
            · simpa using safe
            · simpa using ht
          · intro e' p' hlocal
            rw [hw] at hlocal
            cases hlocal with
            | execute _ _ hout =>
                simp only [CPU.pack_ofMachine] at hout
                obtain ⟨u, heq, hmid⟩ := instrStep_outcome hs hout
                cases heq
                exact ih _ (hk _ hmid)
            | halt heq => exact (hne heq).elim

/-- Every existing Kraken run theorem is a certificate for the intrinsic WP
once the machine's one-time spatial interpretation has been established. -/
theorem certificate_of_eventually {Q : MachineState → Prop} {s : MachineState}
    (cert : Eventually M.code.instrStep Q s) :
    BinaryCert.Certificate w (.run (CPU.ofMachine s)) s.1.dmem (cut Q) :=
  fun n => eventually_safeN w hw n s cert

theorem cwp_of_eventually {Q : MachineState → Prop} {s : MachineState}
    {E : CoPset} {Φ : CPU → IProp GF}
    (cert : Eventually M.code.instrStep Q s) (hprogress : ¬ Q s) :
    w.owns s.1.dmem ∗ ▷ (∀ (e' : Expr M) p', ⌜cut Q e' p'⌝ -∗
      w.owns p' -∗ BinaryCert.cwp w E e' Φ) ⊢
      BinaryCert.cwp w E (.run (CPU.ofMachine s)) Φ := by
  apply BinaryCert.cwp_certificate w (certificate_of_eventually w hw cert)
  simpa [cut] using hprogress

end SbrClient
