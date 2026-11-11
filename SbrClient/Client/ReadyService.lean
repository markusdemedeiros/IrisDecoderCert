import SbrClient.Client.Service

/-! The main ready-state client does not switch SBR off. Two producers each
perform `rounds + 1` calls on the supplied ready decoder. The consumer
acknowledges every publication except the last, scans the last output while
retaining its mailbox claim, then takes the decoder lock and hands all
resources to its caller. Only partial correctness/safety is claimed: no
fairness or scheduler-termination assumption is introduced. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SbrClient.SbrAPI
open Kraken Kraken.SysV Mem Kraken.Examples.Sbr Kraken.Examples.Sbr.SessionBin
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Iris.Std
variable {hlc : HasLC} {M : Model} {GF : BundledGFunctors}
variable [MachineGS hlc M GF] [CodeEnv] [TokenG GF]
local bi (IProp GF)

section Result
variable [genHeapGS (BitVec 64) UInt8 GF ByteMap] [InvGS_gen hlc GF]

/-- Actual decoder and output-byte ownership is returned, together with the
exclusive protocol tokens and handles needed to continue or release them. -/
def heldResult (S : Setup) (che ac avctx : BitVec 64) (er ps : BitVec 32)
    (Rc : Mem 64 → Prop) (c : CPU) (γ δ : GName) (lock slot : BitVec 64)
    (v : Host.Value) : IProp GF := iprop(
  Host.Lock.isLock γ lock (decoderOwned S che ac avctx er ps Rc c) ∗
  Host.Mailbox.isMailbox δ slot (fun _ => outputs (c.pack ∅).1) ∗
  token γ ∗ token δ ∗ decoderOwned S che ac avctx er ps Rc c ∗
  checksumResult (c.pack ∅).1 v)

def readyResult (S : Setup) (che ac avctx : BitVec 64) (er ps : BitVec 32)
    (Rc : Mem 64 → Prop) (c : CPU) (lock slot : BitVec 64) (v : Host.Value) : IProp GF :=
  iprop% ∃ γ δ, heldResult S che ac avctx er ps Rc c γ δ lock slot v

end Result

/-- Keep the final buffer claim, then acquire the decoder. Returning the
checksum leaves both resources held for the caller of the whole service. -/
def takeFinal (c : CPU) (lock slot : BitVec 64) : Host.Expr M :=
  .claim slot (Host.Mailbox.code (some true))
    (.bind (consumeOutputs (c.pack ∅).1) (fun v => .acquire lock (.ret v)))

theorem wp_takeFinal (S : Setup) (c : CPU)
    {che ac avctx : BitVec 64} {er ps : BitVec 32} {Rc : Mem 64 → Prop}
    (γ δ : GName) (lock slot : BitVec 64) :
    letI := (Host.hostIrisGS (hlc := hlc) (GF := GF) (M := M)).invGS
    Host.Lock.isLock γ lock (decoderOwned S che ac avctx er ps Rc c) ∗
      Host.Mailbox.isMailbox δ slot (fun _ => outputs (c.pack ∅).1) ⊢
      WP (takeFinal (M := M) c lock slot) @ Stuckness.NotStuck; ⊤
        {{ v, heldResult S che ac avctx er ps Rc c γ δ lock slot v }} := by
  letI := (Host.hostIrisGS (hlc := hlc) (GF := GF) (M := M)).invGS
  iintro ⟨#Hlock, #Hslot⟩
  unfold takeFinal
  iapply Host.Mailbox.claim δ slot (fun _ => outputs (c.pack ∅).1) true
  iframe Hslot
  iintro ⟨Hδ, HO⟩
  iapply Host.wp_bind
  iapply Iris.wp_wand_r (Φ := checksumResult (c.pack ∅).1)
  isplitl [HO]
  · iapply wp_consumeOutputs_exact $$ HO
  · iintro %v Hsum
    iapply Host.Lock.acquire γ lock (decoderOwned S che ac avctx er ps Rc c)
    iframe Hlock
    iintro ⟨Hγ, HD⟩
    iapply Iris.wp_value' (v := v)
    unfold heldResult
    iframe Hlock Hslot Hγ Hδ HD Hsum

/-- Each worker makes `rounds + 1` calls. Ordinary consumption acknowledges
`2 * rounds + 1` publications; `takeFinal` retains the remaining publication. -/
def readyService (c : CPU) (lock slot : BitVec 64) (rounds : Nat) : Host.Expr M :=
  .bind (.fork (producer c lock slot (rounds + 1))) (fun _ =>
    .bind (.fork (producer c lock slot (rounds + 1))) (fun _ =>
      .bind (consumer c slot (2 * rounds + 1)) (fun _ => takeFinal c lock slot)))

theorem wp_ready_shared (S : Setup) (C : Calls S) (hcode : cenv = M.code)
    (hk : 0x9d0 + S.k ≤ 2 ^ 32) (c : CPU)
    {che ac avctx : BitVec 64} {er ps : BitVec 32} {Rc : Mem 64 → Prop}
    (hc : ApplyCall che ac (c.pack ∅).1)
    (hpc : c.pc = entry "ff_aac_sbr_apply")
    (hne : entry "ff_aac_sbr_apply" ≠ M.halt)
    (γ δ : GName) (lock slot : BitVec 64) (rounds : Nat) :
    letI := (Host.hostIrisGS (hlc := hlc) (GF := GF) (M := M)).invGS
    Host.Lock.isLock γ lock (decoderOwned S che ac avctx er ps Rc c) ∗
      Host.Mailbox.isMailbox δ slot (fun _ => outputs (c.pack ∅).1) ⊢
      WP (readyService (M := M) c lock slot rounds) @ Stuckness.NotStuck; ⊤
        {{ v, heldResult S che ac avctx er ps Rc c γ δ lock slot v }} := by
  letI := (Host.hostIrisGS (hlc := hlc) (GF := GF) (M := M)).invGS
  iintro ⟨#Hlock, #Hslot⟩
  unfold readyService
  iapply Host.wp_bind
  iapply Host.wp_fork
  isplitl []
  · inext
    iapply wp_producer S C hcode hk c hc hpc hne γ δ lock slot (rounds + 1) $$ [$Hlock $Hslot]
  · inext
    iapply Host.wp_bind
    iapply Host.wp_fork
    isplitl []
    · inext
      iapply wp_producer S C hcode hk c hc hpc hne γ δ lock slot (rounds + 1) $$ [$Hlock $Hslot]
    · inext
      iapply Host.wp_bind
      iapply Iris.wp_wand_r (Φ := fun _ => iprop(True))
      isplitl []
      · iapply wp_consumer c δ slot (2 * rounds + 1) $$ Hslot
      · iintro %_ _
        iapply wp_takeFinal S c γ δ lock slot $$ [$Hlock $Hslot]

theorem wp_readyService (S : Setup) (C : Calls S) (hcode : cenv = M.code)
    (hk : 0x9d0 + S.k ≤ 2 ^ 32) (c : CPU)
    {che ac avctx : BitVec 64} {er ps : BitVec 32} {Rc : Mem 64 → Prop}
    (hc : ApplyCall che ac (c.pack ∅).1)
    (hpc : c.pc = entry "ff_aac_sbr_apply")
    (hne : entry "ff_aac_sbr_apply" ≠ M.halt)
    (lock slot : BitVec 64) (rounds : Nat) :
    letI := (Host.hostIrisGS (hlc := hlc) (GF := GF) (M := M)).invGS
    applyOwned S che ac avctx er ps Rc c ∗
      pointsTo lock (DFrac.own 1) (0 : UInt8) ∗ pointsTo slot (DFrac.own 1) (0 : UInt8) ⊢
      WP (readyService (M := M) c lock slot rounds) @ Stuckness.NotStuck; ⊤
        {{ v, readyResult S che ac avctx er ps Rc c lock slot v }} := by
  letI := (Host.hostIrisGS (hlc := hlc) (GF := GF) (M := M)).invGS
  iintro ⟨HA, Hl, Hs⟩
  icases applyOwned_split S che ac avctx er ps Rc c $$ HA with ⟨HD, HO⟩
  iapply Iris.fupd_wp
  imod Host.Lock.init M lock (decoderOwned S che ac avctx er ps Rc c) $$ [$Hl $HD] with ⟨%γ, #Hlock⟩
  imod Host.Mailbox.init M slot (fun _ => outputs (c.pack ∅).1) $$ [$Hs $HO] with ⟨%δ, #Hslot⟩
  imodintro
  iapply Iris.wp_wand_r (Φ := heldResult S che ac avctx er ps Rc c γ δ lock slot)
  isplitl []
  · iapply wp_ready_shared S C hcode hk c hc hpc hne γ δ lock slot rounds $$ [$Hlock $Hslot]
  · iintro %v HR
    unfold readyResult
    iexists γ
    iexists δ
    iexact HR

end SbrClient.SbrAPI
