import SbrClient.Client.Application
import SbrClient.FFmpeg.Provider

/-! The application theorem below contains the actual independent linked
FFmpeg proofs. It has no Calls/provider hypothesis. Placement and original
library environment requirements are deliberately retained. -/
namespace SbrClient.SbrAPI
open Kraken Kraken.SysV Mem Kraken.Examples.Sbr Kraken.Examples.Sbr.SessionBin
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Iris.Std
variable {hlc : HasLC} {M : Model} {GF : BundledGFunctors}
variable [MachineGS hlc M GF] [CodeEnv] [TokenG GF]
local bi (IProp GF)

theorem wp_verifiedService (B : SessPlaced) (S : Setup) (hcode : cenv = M.code)
    (hk : 0x9d0 + S.k ≤ 2 ^ 32) (c : CPU)
    {che ac avctx : BitVec 64} {er ps : BitVec 32} {Rc : Mem 64 → Prop}
    (hc : ApplyCall che ac (c.pack ∅).1)
    (hpc : c.pc = entry "ff_aac_sbr_apply")
    (hne : entry "ff_aac_sbr_apply" ≠ M.halt)
    (hcfg : entry "ff_aac_sbr_config_usac" ≠ M.halt)
    (lock slot : BitVec 64) (n : Nat) (Ψ : IProp GF) :
    (bootOwned S che ac avctx er ps Rc c ∗
      pointsTo lock (DFrac.own 1) (0 : UInt8) ∗ pointsTo slot (DFrac.own 1) (0 : UInt8)) ∗ Ψ ⊢
      WP (service (M := M) c lock slot n) @ Stuckness.NotStuck; ⊤ {{ _v, Ψ }} :=
  wp_service_frame S (verifiedCalls B S) hcode hk c hc hpc hne hcfg lock slot n Ψ

/-- The same complete client inhabits the intrinsic certificate-accepting
WP; its external calls were introduced by that WP's certificate branch. -/
theorem cwp_verifiedService (B : SessPlaced) (S : Setup) (hcode : cenv = M.code)
    (hk : 0x9d0 + S.k ≤ 2 ^ 32) (c : CPU)
    {che ac avctx : BitVec 64} {er ps : BitVec 32} {Rc : Mem 64 → Prop}
    (hc : ApplyCall che ac (c.pack ∅).1)
    (hpc : c.pc = entry "ff_aac_sbr_apply")
    (hne : entry "ff_aac_sbr_apply" ≠ M.halt)
    (hcfg : entry "ff_aac_sbr_config_usac" ≠ M.halt)
    (lock slot : BitVec 64) (n : Nat) (Ψ : IProp GF) :
    (bootOwned S che ac avctx er ps Rc c ∗
      pointsTo lock (DFrac.own 1) (0 : UInt8) ∗ pointsTo slot (DFrac.own 1) (0 : UInt8)) ∗ Ψ ⊢
      BinaryCert.cwp (Host.world (M := M)) ⊤ (service c lock slot n) (fun _ => Ψ) := by
  rw [BinaryCert.cwp_eq_native]
  exact wp_verifiedService B S hcode hk c hc hpc hne hcfg lock slot n Ψ

end SbrClient.SbrAPI
