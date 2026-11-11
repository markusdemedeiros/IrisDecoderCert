import SbrClient.Client.Service
import SbrClient.FFmpeg.Startup

/-! Full modeled application: configure a live decoder, install a decoder
lock and a one-slot ownership mailbox, then run the native producer and
checksum consumer concurrently. The independent FFmpeg theorem fields are
discharged in VerifiedService.lean. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SbrClient.SbrAPI
open Kraken Kraken.SysV Mem Kraken.Examples.Sbr Kraken.Examples.Sbr.SessionBin
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Iris.Std
variable {hlc : HasLC} {M : Model} {GF : BundledGFunctors}
variable [MachineGS hlc M GF] [CodeEnv] [TokenG GF]
local bi (IProp GF)

def service (c : CPU) (lock slot : BitVec 64) (n : Nat) : Host.Expr M :=
  configOnce c (concurrentTwo c lock slot n)

theorem wp_service (S : Setup) (C : Calls S) (hcode : cenv = M.code)
    (hk : 0x9d0 + S.k ≤ 2 ^ 32) (c : CPU)
    {che ac avctx : BitVec 64} {er ps : BitVec 32} {Rc : Mem 64 → Prop}
    (hc : ApplyCall che ac (c.pack ∅).1)
    (hpc : c.pc = entry "ff_aac_sbr_apply")
    (hne : entry "ff_aac_sbr_apply" ≠ M.halt)
    (hcfg : entry "ff_aac_sbr_config_usac" ≠ M.halt)
    (lock slot : BitVec 64) (n : Nat) :
    bootOwned S che ac avctx er ps Rc c ∗
      pointsTo lock (DFrac.own 1) (0 : UInt8) ∗ pointsTo slot (DFrac.own 1) (0 : UInt8) ⊢
      WP (service (M := M) c lock slot n) @ Stuckness.NotStuck; ⊤ {{ _v, True }} := by
  letI := (Host.hostIrisGS (hlc := hlc) (GF := GF) (M := M)).invGS
  iintro ⟨Hboot, Hl, Hs⟩
  unfold service
  iapply wp_configOnce S C hcode c ⟨hc.args⟩ hcfg
  iframe Hboot
  iintro HA
  icases applyOwned_split S che ac avctx er ps Rc c $$ HA with ⟨HD, HO⟩
  iapply Iris.fupd_wp
  imod Host.Lock.init M lock (decoderOwned S che ac avctx er ps Rc c) $$ [$Hl $HD] with ⟨%γ, #Hlock⟩
  imod Host.Mailbox.init M slot (fun _ => outputs (c.pack ∅).1) $$ [$Hs $HO] with ⟨%δ, #Hslot⟩
  imodintro
  iapply wp_concurrentTwo S C hcode hk c hc hpc hne γ δ lock slot n $$ [$Hlock $Hslot]

/-- Arbitrary unrelated application ownership is preserved while both
threads interleave with the native library. For example Ψ may own the exact
bytes of an authentication record or another independent stream's state. -/
theorem wp_service_frame (S : Setup) (C : Calls S) (hcode : cenv = M.code)
    (hk : 0x9d0 + S.k ≤ 2 ^ 32) (c : CPU)
    {che ac avctx : BitVec 64} {er ps : BitVec 32} {Rc : Mem 64 → Prop}
    (hc : ApplyCall che ac (c.pack ∅).1)
    (hpc : c.pc = entry "ff_aac_sbr_apply")
    (hne : entry "ff_aac_sbr_apply" ≠ M.halt)
    (hcfg : entry "ff_aac_sbr_config_usac" ≠ M.halt)
    (lock slot : BitVec 64) (n : Nat) (Ψ : IProp GF) :
    (bootOwned S che ac avctx er ps Rc c ∗
      pointsTo lock (DFrac.own 1) (0 : UInt8) ∗ pointsTo slot (DFrac.own 1) (0 : UInt8)) ∗ Ψ ⊢
      WP (service (M := M) c lock slot n) @ Stuckness.NotStuck; ⊤ {{ _v, Ψ }} := by
  iintro ⟨Hpre, HΨ⟩
  iapply Iris.wp_wand_r (Φ := fun _ => iprop(Ψ ∗ True))
  isplitl [Hpre HΨ]
  · iapply Iris.wp_frame_r
    iframe HΨ
    iapply wp_service S C hcode hk c hc hpc hne hcfg lock slot n $$ Hpre
  · iintro %_ ⟨HΨ, _⟩
    iexact HΨ

end SbrClient.SbrAPI
