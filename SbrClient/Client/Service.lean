import SbrClient.FFmpeg.Reusable
import SbrClient.Client.OutputConsumer
import SbrClient.Host.Mailbox
import SbrClient.Host.Fork

/-! A locked SBR worker and concurrent output consumer. The producer holds
the decoder lock and claims free output buffers, invokes the original native
apply, releases the decoder, and publishes the buffers. The consumer claims
ready output, reads every byte, and acknowledges reuse only after its scan.
No whole native call is atomic; all native instructions and host byte/CAS
operations use the same physical shared heap. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace SbrClient.SbrAPI
open Kraken Kraken.SysV Mem Kraken.Examples.Sbr Kraken.Examples.Sbr.SessionBin
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Iris.Std
variable {hlc : HasLC} {M : Model} {GF : BundledGFunctors} [MachineGS hlc M GF] [CodeEnv]
local bi (IProp GF)

def decoderOwned [genHeapGS (BitVec 64) UInt8 GF ByteMap]
    (S : Setup) (che ac avctx : BitVec 64) (er ps : BitVec 32)
    (Rc : Mem 64 → Prop) (c : CPU) : IProp GF := iprop(
  abiResources (applyStack S.k) (c.pack ∅).1 ∗ ready S che ac ∗
  ownsPred (AcFields ac avctx er ps) ∗ ownsPred Rc)

theorem applyOwned_split (S : Setup) (che ac avctx : BitVec 64) (er ps : BitVec 32)
    (Rc : Mem 64 → Prop) (c : CPU) :
    applyOwned (GF := GF) S che ac avctx er ps Rc c ⊢
      decoderOwned S che ac avctx er ps Rc c ∗ outputs (c.pack ∅).1 := by
  unfold applyOwned decoderOwned
  iintro ⟨Habi, Hready, Hac, Hout, HR⟩
  iframe

theorem applyOwned_join (S : Setup) (che ac avctx : BitVec 64) (er ps : BitVec 32)
    (Rc : Mem 64 → Prop) (c : CPU) :
    decoderOwned (GF := GF) S che ac avctx er ps Rc c ∗ outputs (c.pack ∅).1 ⊢
      applyOwned S che ac avctx er ps Rc c := by
  unfold applyOwned decoderOwned
  iintro ⟨⟨Habi, Hready, Hac, HR⟩, Hout⟩
  iframe

def producerOnce (c : CPU) (lock slot : BitVec 64) (next : Host.Expr M) : Host.Expr M :=
  .acquire lock (.claim slot (Host.Mailbox.code (some false)) (applyOnce c
    (.bind (.store lock 0) (fun _ => .bind (.store slot (Host.Mailbox.code (some true))) (fun _ => next)))))

def consumerOnce (c : CPU) (slot : BitVec 64) (next : UInt8 → Host.Expr M) : Host.Expr M :=
  .claim slot (Host.Mailbox.code (some true)) (.bind (consumeOutputs (c.pack ∅).1)
    (fun v => match v with
      | .byte checksum => .bind (.store slot (Host.Mailbox.code (some false))) (fun _ => next checksum)
      | _ => .fault))

variable [TokenG GF]

theorem wp_producerOnce (S : Setup) (C : Calls S) (hcode : cenv = M.code)
    (hk : 0x9d0 + S.k ≤ 2 ^ 32) (c : CPU)
    {che ac avctx : BitVec 64} {er ps : BitVec 32} {Rc : Mem 64 → Prop}
    (hc : ApplyCall che ac (c.pack ∅).1)
    (hpc : c.pc = entry "ff_aac_sbr_apply")
    (hne : entry "ff_aac_sbr_apply" ≠ M.halt)
    (γ δ : GName) (lock slot : BitVec 64) (next : Host.Expr M)
    {Φ : Host.Value → IProp GF} :
    letI := (Host.hostIrisGS (hlc := hlc) (GF := GF) (M := M)).invGS
    Host.Lock.isLock γ lock (decoderOwned S che ac avctx er ps Rc c) ∗
      Host.Mailbox.isMailbox δ slot (fun _ => outputs (c.pack ∅).1) ∗
      (WP next @ Stuckness.NotStuck; ⊤ {{ Φ }}) ⊢
      WP (producerOnce c lock slot next) @ Stuckness.NotStuck; ⊤ {{ Φ }} := by
  letI := (Host.hostIrisGS (hlc := hlc) (GF := GF) (M := M)).invGS
  iintro ⟨#Hlock, #Hslot, Hnext⟩
  unfold producerOnce
  iapply Host.Lock.acquire γ lock (decoderOwned S che ac avctx er ps Rc c)
  iframe Hlock
  iintro ⟨Hγ, HD⟩
  iapply Host.Mailbox.claim δ slot (fun _ => outputs (c.pack ∅).1) false
  iframe Hslot
  iintro ⟨Hδ, HO⟩
  iapply wp_applyOnce S C hcode hk c hc hpc hne
  isplitl [HD HO]
  · iapply applyOwned_join S che ac avctx er ps Rc c $$ [$HD $HO]
  inext
  iintro HA
  icases applyOwned_split S che ac avctx er ps Rc c $$ HA with ⟨HD, HO⟩
  iapply Host.wp_bind
  iapply Host.Lock.release γ lock (decoderOwned S che ac avctx er ps Rc c)
  iframe Hlock Hγ HD
  iapply Host.wp_bind
  iapply Host.Mailbox.publish δ slot (fun _ => outputs (c.pack ∅).1) true
  iframe Hslot Hδ HO Hnext

theorem wp_consumerOnce (c : CPU) (δ : GName) (slot : BitVec 64)
    (next : UInt8 → Host.Expr M) {Φ : Host.Value → IProp GF} :
    letI := (Host.hostIrisGS (hlc := hlc) (GF := GF) (M := M)).invGS
    Host.Mailbox.isMailbox δ slot (fun _ => outputs (c.pack ∅).1) ∗
      (∀ checksum, WP (next checksum) @ Stuckness.NotStuck; ⊤ {{ Φ }}) ⊢
      WP (consumerOnce c slot next) @ Stuckness.NotStuck; ⊤ {{ Φ }} := by
  letI := (Host.hostIrisGS (hlc := hlc) (GF := GF) (M := M)).invGS
  iintro ⟨#Hslot, Hnext⟩
  unfold consumerOnce
  iapply Host.Mailbox.claim δ slot (fun _ => outputs (c.pack ∅).1) true
  iframe Hslot
  iintro ⟨Hδ, HO⟩
  iapply Host.wp_bind
  iapply wp_consumeOutputs (c.pack ∅).1
  iframe HO
  iintro %checksum HO
  iapply Host.wp_bind
  iapply Host.Mailbox.publish δ slot (fun _ => outputs (c.pack ∅).1) false
  iframe Hslot Hδ HO
  iapply Hnext $$ %checksum

def producer (c : CPU) (lock slot : BitVec 64) : Nat → Host.Expr M
  | 0 => .ret .unit
  | n + 1 => producerOnce c lock slot (producer c lock slot n)

/-- Return the last consumed block's checksum; zero requests return byte0. -/
def consumer (c : CPU) (slot : BitVec 64) : Nat → Host.Expr M
  | 0 => .ret (.byte 0)
  | n + 1 => consumerOnce c slot (fun checksum =>
      if n = 0 then .ret (.byte checksum) else consumer c slot n)

theorem wp_producer (S : Setup) (C : Calls S) (hcode : cenv = M.code)
    (hk : 0x9d0 + S.k ≤ 2 ^ 32) (c : CPU)
    {che ac avctx : BitVec 64} {er ps : BitVec 32} {Rc : Mem 64 → Prop}
    (hc : ApplyCall che ac (c.pack ∅).1)
    (hpc : c.pc = entry "ff_aac_sbr_apply")
    (hne : entry "ff_aac_sbr_apply" ≠ M.halt)
    (γ δ : GName) (lock slot : BitVec 64) (n : Nat) :
    letI := (Host.hostIrisGS (hlc := hlc) (GF := GF) (M := M)).invGS
    Host.Lock.isLock γ lock (decoderOwned S che ac avctx er ps Rc c) ∗
      Host.Mailbox.isMailbox δ slot (fun _ => outputs (c.pack ∅).1) ⊢
      WP (producer (M := M) c lock slot n) @ Stuckness.NotStuck; ⊤ {{ _v, True }} := by
  letI := (Host.hostIrisGS (hlc := hlc) (GF := GF) (M := M)).invGS
  induction n with
  | zero =>
      unfold producer
      iintro _
      iapply Iris.wp_value' (v := Host.Value.unit)
      itrivial
  | succ n ih =>
      unfold producer
      iintro ⟨#Hlock, #Hslot⟩
      iapply wp_producerOnce S C hcode hk c hc hpc hne γ δ lock slot
      iframe Hlock Hslot
      iapply ih $$ [$Hlock $Hslot]

theorem wp_consumer (c : CPU) (δ : GName) (slot : BitVec 64) (n : Nat) :
    letI := (Host.hostIrisGS (hlc := hlc) (GF := GF) (M := M)).invGS
    Host.Mailbox.isMailbox δ slot (fun _ => outputs (c.pack ∅).1) ⊢
      WP (consumer (M := M) c slot n) @ Stuckness.NotStuck; ⊤ {{ _v, True }} := by
  letI := (Host.hostIrisGS (hlc := hlc) (GF := GF) (M := M)).invGS
  induction n with
  | zero =>
      unfold consumer
      iintro _
      iapply Iris.wp_value' (v := Host.Value.byte 0)
      itrivial
  | succ n ih =>
      unfold consumer
      iintro #Hslot
      iapply wp_consumerOnce c δ slot
      iframe Hslot
      iintro %checksum
      by_cases hn : n = 0
      · simp only [hn, ite_true]
        iapply Iris.wp_value' (v := Host.Value.byte checksum)
        itrivial
      · simp only [hn, ite_false]
        iapply ih $$ Hslot

/-- The main thread consumes while the forked worker performs native calls.
The postcondition is safety only: this theorem makes no fairness or scheduler
termination claim. -/
def concurrent (c : CPU) (lock slot : BitVec 64) (n : Nat) : Host.Expr M :=
  .bind (.fork (producer c lock slot n)) (fun _ => consumer c slot n)

theorem wp_concurrent (S : Setup) (C : Calls S) (hcode : cenv = M.code)
    (hk : 0x9d0 + S.k ≤ 2 ^ 32) (c : CPU)
    {che ac avctx : BitVec 64} {er ps : BitVec 32} {Rc : Mem 64 → Prop}
    (hc : ApplyCall che ac (c.pack ∅).1)
    (hpc : c.pc = entry "ff_aac_sbr_apply")
    (hne : entry "ff_aac_sbr_apply" ≠ M.halt)
    (γ δ : GName) (lock slot : BitVec 64) (n : Nat) :
    letI := (Host.hostIrisGS (hlc := hlc) (GF := GF) (M := M)).invGS
    Host.Lock.isLock γ lock (decoderOwned S che ac avctx er ps Rc c) ∗
      Host.Mailbox.isMailbox δ slot (fun _ => outputs (c.pack ∅).1) ⊢
      WP (concurrent (M := M) c lock slot n) @ Stuckness.NotStuck; ⊤ {{ _v, True }} := by
  letI := (Host.hostIrisGS (hlc := hlc) (GF := GF) (M := M)).invGS
  iintro ⟨#Hlock, #Hslot⟩
  unfold concurrent
  iapply Host.wp_bind
  iapply Host.wp_fork
  isplitl []
  · inext
    iapply wp_producer S C hcode hk c hc hpc hne γ δ lock slot n $$ [$Hlock $Hslot]
  · inext
    iapply wp_consumer c δ slot n $$ Hslot

/-- Two request workers share the decoder and mailbox. Each performs `n`
native calls; the consumer acknowledges exactly `2*n` output blocks. -/
def concurrentTwo (c : CPU) (lock slot : BitVec 64) (n : Nat) : Host.Expr M :=
  .bind (.fork (producer c lock slot n)) (fun _ =>
    .bind (.fork (producer c lock slot n)) (fun _ => consumer c slot (2 * n)))

theorem wp_concurrentTwo (S : Setup) (C : Calls S) (hcode : cenv = M.code)
    (hk : 0x9d0 + S.k ≤ 2 ^ 32) (c : CPU)
    {che ac avctx : BitVec 64} {er ps : BitVec 32} {Rc : Mem 64 → Prop}
    (hc : ApplyCall che ac (c.pack ∅).1)
    (hpc : c.pc = entry "ff_aac_sbr_apply")
    (hne : entry "ff_aac_sbr_apply" ≠ M.halt)
    (γ δ : GName) (lock slot : BitVec 64) (n : Nat) :
    letI := (Host.hostIrisGS (hlc := hlc) (GF := GF) (M := M)).invGS
    Host.Lock.isLock γ lock (decoderOwned S che ac avctx er ps Rc c) ∗
      Host.Mailbox.isMailbox δ slot (fun _ => outputs (c.pack ∅).1) ⊢
      WP (concurrentTwo (M := M) c lock slot n) @ Stuckness.NotStuck; ⊤ {{ _v, True }} := by
  letI := (Host.hostIrisGS (hlc := hlc) (GF := GF) (M := M)).invGS
  iintro ⟨#Hlock, #Hslot⟩
  unfold concurrentTwo
  iapply Host.wp_bind
  iapply Host.wp_fork
  isplitl []
  · inext
    iapply wp_producer S C hcode hk c hc hpc hne γ δ lock slot n $$ [$Hlock $Hslot]
  · inext
    iapply Host.wp_bind
    iapply Host.wp_fork
    isplitl []
    · inext
      iapply wp_producer S C hcode hk c hc hpc hne γ δ lock slot n $$ [$Hlock $Hslot]
    · inext
      iapply wp_consumer c δ slot (2 * n) $$ Hslot

end SbrClient.SbrAPI
