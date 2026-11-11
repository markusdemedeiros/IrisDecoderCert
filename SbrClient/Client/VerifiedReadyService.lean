import SbrClient.Client.ReadyService
import SbrClient.FFmpeg.Provider

/-! Main public theorem: actual linked FFmpeg proof artifacts, a ready
(possibly active) SBR decoder, two request workers, and an exact output
checksum with exclusive resource handoff. No Calls/provider hypothesis and
no config-off startup step occur in this interface. Original placement and
external-code contracts inside Ready remain explicit preconditions. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SbrClient.SbrAPI
open Kraken Kraken.SysV Mem Kraken.Examples.Sbr Kraken.Examples.Sbr.SessionBin
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Iris.Std
variable {hlc : HasLC} {M : Model} {GF : BundledGFunctors}
variable [MachineGS hlc M GF] [CodeEnv] [TokenG GF]
local bi (IProp GF)

theorem wp_verifiedReadyService (B : SessPlaced) (S : Setup) (hcode : cenv = M.code)
    (hk : 0x9d0 + S.k ≤ 2 ^ 32) (c : CPU)
    {che ac avctx : BitVec 64} {er ps : BitVec 32} {Rc : Mem 64 → Prop}
    (hc : ApplyCall che ac (c.pack ∅).1)
    (hpc : c.pc = entry "ff_aac_sbr_apply")
    (hne : entry "ff_aac_sbr_apply" ≠ M.halt)
    (lock slot : BitVec 64) (rounds : Nat) (Ψ : IProp GF) :
    letI := (Host.hostIrisGS (hlc := hlc) (GF := GF) (M := M)).invGS
    (applyOwned S che ac avctx er ps Rc c ∗
      pointsTo lock (DFrac.own 1) (0 : UInt8) ∗ pointsTo slot (DFrac.own 1) (0 : UInt8)) ∗ Ψ ⊢
      WP (readyService (M := M) c lock slot rounds) @ Stuckness.NotStuck; ⊤
        {{ v, Ψ ∗ readyResult S che ac avctx er ps Rc c lock slot v }} := by
  letI := (Host.hostIrisGS (hlc := hlc) (GF := GF) (M := M)).invGS
  iintro ⟨Hpre, HΨ⟩
  iapply Iris.wp_frame_r
  iframe HΨ
  iapply wp_readyService S (verifiedCalls B S) hcode hk c hc hpc hne lock slot rounds $$ Hpre

theorem cwp_verifiedReadyService (B : SessPlaced) (S : Setup) (hcode : cenv = M.code)
    (hk : 0x9d0 + S.k ≤ 2 ^ 32) (c : CPU)
    {che ac avctx : BitVec 64} {er ps : BitVec 32} {Rc : Mem 64 → Prop}
    (hc : ApplyCall che ac (c.pack ∅).1)
    (hpc : c.pc = entry "ff_aac_sbr_apply")
    (hne : entry "ff_aac_sbr_apply" ≠ M.halt)
    (lock slot : BitVec 64) (rounds : Nat) (Ψ : IProp GF) :
    letI := (Host.hostIrisGS (hlc := hlc) (GF := GF) (M := M)).invGS
    (applyOwned S che ac avctx er ps Rc c ∗
      pointsTo lock (DFrac.own 1) (0 : UInt8) ∗ pointsTo slot (DFrac.own 1) (0 : UInt8)) ∗ Ψ ⊢
      BinaryCert.cwp (Host.world (M := M)) ⊤ (readyService c lock slot rounds)
        (fun v => iprop(Ψ ∗ readyResult S che ac avctx er ps Rc c lock slot v)) := by
  letI := (Host.hostIrisGS (hlc := hlc) (GF := GF) (M := M)).invGS
  rw [BinaryCert.cwp_eq_native]
  exact wp_verifiedReadyService B S hcode hk c hc hpc hne lock slot rounds Ψ

end SbrClient.SbrAPI
