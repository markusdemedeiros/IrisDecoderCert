import SbrClient.FFmpeg.Resources
import SbrClient.Machine.Adapter

/-! The independently verified FFmpeg contracts enter the concurrent logic
through the semantic-certificate branch. The statements retain every original
placement, stack, alignment, and environment requirement. -/

noncomputable section
namespace SbrClient.SbrAPI
open Kraken Kraken.SysV Mem Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply
open Kraken.Examples.Sbr.SessionBin
open Iris Iris.BI Iris.Std Iris.ProofMode BinaryCert

/-- The external library interface consists of original Kraken execution
certificates. `SbrAPI.verifiedCalls` discharges both fields with the separately
compiled FFmpeg proofs; clients do not assume a new abstract call semantics. -/
structure Calls (S : Setup) [CodeEnv] : Prop where
  config : ConfigSafe S
  apply : 0x9d0 + S.k ≤ 2 ^ 32 → ApplySafe S

variable {hlc : HasLC} {M : SbrClient.Model} {GF : BundledGFunctors}
variable [MachineGS hlc M GF] [CodeEnv]
local bi (IProp GF)

/-- Reuse the whole optimized `ff_aac_sbr_apply` proof. The continuation
receives the actual endpoint expression and owned bytes, so it may restore
the decoder invariant and transfer the output buffers independently. -/
theorem apply_rule (S : Setup) (C : Calls S) (hcode : cenv = M.code)
    (hk : 0x9d0 + S.k ≤ 2 ^ 32)
    {che ac avctx : BitVec 64} {er ps : BitVec 32}
    {Rc : Mem 64 → Prop} {ra : Int64} {t : MachineData}
    (hc : ApplyCall che ac t)
    (hm : CallPre (applyStack S.k)
      (Ready S che ac ⋆ (AcFields ac avctx er ps ⋆ (OutBufs t ⋆ Rc))) ra t)
    (hne : entry "ff_aac_sbr_apply" ≠ ra)
    {E : CoPset} {Φ : CPU → IProp GF} :
    let Q : MachineState → Prop := fun st => st.2 = ra ∧
      CallPost (applyStack S.k)
        (Ready S che ac ⋆ (AcFields ac avctx er ps ⋆ (OutBufs t ⋆ Rc))) ra t st.1
    owns t.dmem ∗ ▷ (∀ (e' : Expr M) p', ⌜cut Q e' p'⌝ -∗
      owns p' -∗ cwp (machineWorld (M := M)) E e' Φ) ⊢
      cwp (machineWorld (M := M)) E (.run (CPU.ofMachine (t, entry "ff_aac_sbr_apply"))) Φ := by
  dsimp only
  have h := C.apply hk hc hm
  unfold Ends at h
  rw [hcode] at h
  have h' := eventually_weaken _ _ _ _ (fun st h => h.elim id False.elim) h
  exact cwp_of_eventually (machineWorld (M := M) (GF := GF)) rfl h' (fun hq => hne hq.1)

/-- `config_usac` upgrades a live decoder to ready and returns zero, using
the original machine-code theorem rather than a host-side state update. -/
theorem config_rule (S : Setup) (C : Calls S) (hcode : cenv = M.code)
    {che ac avctx : BitVec 64} {er ps : BitVec 32}
    {Rc : Mem 64 → Prop} {ra : Int64} {t : MachineData}
    (hc : ConfigCall che ac t)
    (hm : CallPre 0 (Live S che ac ⋆ (AcFields ac avctx er ps ⋆ Rc)) ra t)
    (hne : entry "ff_aac_sbr_config_usac" ≠ ra)
    {E : CoPset} {Φ : CPU → IProp GF} :
    let Q : MachineState → Prop := fun st => st.2 = ra ∧ ret32 st.1 = 0#32 ∧
      CallPost 0 (Ready S che ac ⋆ (AcFields ac avctx er ps ⋆ Rc)) ra t st.1
    owns t.dmem ∗ ▷ (∀ (e' : Expr M) p', ⌜cut Q e' p'⌝ -∗
      owns p' -∗ cwp (machineWorld (M := M)) E e' Φ) ⊢
      cwp (machineWorld (M := M)) E (.run (CPU.ofMachine (t, entry "ff_aac_sbr_config_usac"))) Φ := by
  dsimp only
  have h := C.config hc hm
  unfold Ends at h
  rw [hcode] at h
  have h' := eventually_weaken _ _ _ _ (fun st h => h.elim id False.elim) h
  exact cwp_of_eventually (machineWorld (M := M) (GF := GF)) rfl h' (fun hq => hne hq.1)

end SbrClient.SbrAPI
