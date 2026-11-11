import SbrClient.FFmpeg.Reusable

/-! Configure a live SBR element once, then reuse apply's exact resource
invariant. The apply stack and output buffers are retained across config as
ordinary separated caller resources. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace SbrClient.SbrAPI
open Kraken Kraken.SysV Mem Kraken.Examples.Sbr Kraken.Examples.Sbr.SessionBin
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Iris.Std
variable {hlc : HasLC} {M : Model} {GF : BundledGFunctors} [MachineGS hlc M GF] [CodeEnv]
local bi (IProp GF)

omit [CodeEnv] in
private theorem reserveZero (a : BitVec 64) :
    (⌜True⌝ : IProp GF) ⊢ ownsPred (Reserve 0 a) := by
  unfold ownsPred
  iintro _
  iexists (∅ : Mem 64)
  isplit
  · ipureintro
    unfold Reserve Block
    refine ⟨by omega, by omega, [], rfl, ?_⟩
    simp [List.At]
  · unfold owns
    iapply (BigSepM.bigSepM_empty (M := ByteMap)
      (Φ := fun k v => pointsTo k (DFrac.own 1) v)).2
    itrivial

def configCPU (c : CPU) : CPU := {c with pc := entry "ff_aac_sbr_config_usac"}

def configOnce (c : CPU) (next : Host.Expr M) : Host.Expr M :=
  Host.prepare (configCPU c) (.native (.run (configCPU c)) (fun _ => next))

def bootOwned [genHeapGS (BitVec 64) UInt8 GF ByteMap] (S : Setup) (che ac avctx : BitVec 64) (er ps : BitVec 32)
    (Rc : Mem 64 → Prop) (c : CPU) : IProp GF := iprop(
  abiResources (applyStack S.k) (c.pack ∅).1 ∗ live S che ac ∗
  ownsPred (AcFields ac avctx er ps) ∗ outputs (c.pack ∅).1 ∗ ownsPred Rc)

theorem wp_configOnce (S : Setup) (C : Calls S) (hcode : cenv = M.code) (c : CPU)
    {che ac avctx : BitVec 64} {er ps : BitVec 32} {Rc : Mem 64 → Prop}
    (hc : ConfigCall che ac (c.pack ∅).1)
    (hne : entry "ff_aac_sbr_config_usac" ≠ M.halt)
    (next : Host.Expr M) {E : CoPset} {Φ : Host.Value → IProp GF} :
    bootOwned S che ac avctx er ps Rc c ∗
      (applyOwned S che ac avctx er ps Rc c -∗
        WP next @ Stuckness.NotStuck; E {{ Φ }}) ⊢
      WP (configOnce c next) @ Stuckness.NotStuck; E {{ Φ }} := by
  unfold bootOwned abiResources live outputs
  simp only [CPU.pack]
  iintro ⟨⟨⟨Hret, Hstack⟩, Hlive, Hac, Hout, HR⟩, HK⟩
  unfold configOnce
  let R : Mem 64 → Prop := Reserve (applyStack S.k) (c.regs.get64 .rsp) ⋆
    (OutBufs (c.pack ∅).1 ⋆ Rc)
  iapply Host.wp_prepare (configCPU c) 0 (Live S che ac ⋆ (AcFields ac avctx er ps ⋆ R))
  isplitl [Hret]
  · unfold abiResources
    simp only [configCPU, CPU.pack]
    iframe Hret
    iapply reserveZero
    itrivial
  isplitl [Hlive Hac Hstack Hout HR]
  · iapply ownsPred_sep_intro
    iframe Hlive
    iapply ownsPred_sep_intro
    iframe Hac
    unfold R
    simp only [CPU.pack]
    iapply ownsPred_sep_intro
    iframe Hstack
    iapply ownsPred_sep_intro $$ [$Hout $HR]
  · iintro Hpre
    have hcall : ConfigCall che ac ((configCPU c).pack ∅).1 := ⟨hc.args⟩
    iapply wp_config_owned S C hcode (configCPU c) hcall rfl hne (fun _ => next)
    iframe Hpre
    inext
    iintro %_ ⟨Habi, Hready, Hac, HR⟩
    unfold abiResources
    icases Habi with ⟨Hret, _⟩
    icases ownsPred_sep $$ HR with ⟨Hstack, HR⟩
    icases ownsPred_sep $$ HR with ⟨Hout, HR⟩
    iapply HK
    unfold applyOwned abiResources ready outputs
    simp only [CPU.pack, configCPU]
    iframe

/-- End-to-end sequential initialization and arbitrary finite reuse. The
concurrent service uses the same single-call rules under its lock/mailbox
protocol, so the output resources may leave the decoder lock after a call. -/
def serviceSequential (c : CPU) (n : Nat) : Host.Expr M := configOnce c (applyMany c n)

theorem wp_serviceSequential (S : Setup) (C : Calls S) (hcode : cenv = M.code)
    (hk : 0x9d0 + S.k ≤ 2 ^ 32) (c : CPU)
    {che ac avctx : BitVec 64} {er ps : BitVec 32} {Rc : Mem 64 → Prop}
    (hc : ApplyCall che ac (c.pack ∅).1)
    (hpc : c.pc = entry "ff_aac_sbr_apply")
    (hne : entry "ff_aac_sbr_apply" ≠ M.halt)
    (hcfg : entry "ff_aac_sbr_config_usac" ≠ M.halt)
    (n : Nat) {E : CoPset} :
    bootOwned S che ac avctx er ps Rc c ⊢
      WP (serviceSequential (M := M) c n) @ Stuckness.NotStuck; E
        {{ _v, applyOwned S che ac avctx er ps Rc c }} := by
  iintro Hboot
  unfold serviceSequential
  iapply wp_configOnce S C hcode c ⟨hc.args⟩ hcfg
  iframe Hboot
  iintro HR
  iapply wp_applyMany S C hcode hk c hc hpc hne n $$ HR

end SbrClient.SbrAPI
