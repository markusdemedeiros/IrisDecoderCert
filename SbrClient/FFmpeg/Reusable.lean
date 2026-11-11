import SbrClient.FFmpeg.Calls
import SbrClient.FFmpeg.CallSetup

/-! A reusable FFI operation includes explicit return-slot initialization.
The same resource invariant is returned after every apply, so client code
can release the decoder lock and transfer the output buffers after each call. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace SbrClient.SbrAPI
open Kraken Kraken.SysV Mem Kraken.Examples.Sbr Kraken.Examples.Sbr.SessionBin
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Iris.Std
variable {hlc : HasLC} {M : Model} {GF : BundledGFunctors} [MachineGS hlc M GF] [CodeEnv]
local bi (IProp GF)

def applyOnce (c : CPU) (next : Host.Expr M) : Host.Expr M :=
  Host.prepare c (.native (.run c) (fun _ => next))

def applyOwned [genHeapGS (BitVec 64) UInt8 GF ByteMap] (S : Setup) (che ac avctx : BitVec 64) (er ps : BitVec 32)
    (Rc : Mem 64 → Prop) (c : CPU) : IProp GF := iprop(
  abiResources (applyStack S.k) (c.pack ∅).1 ∗ ready S che ac ∗
  ownsPred (AcFields ac avctx er ps) ∗ outputs (c.pack ∅).1 ∗ ownsPred Rc)

theorem wp_applyOnce (S : Setup) (C : Calls S) (hcode : cenv = M.code)
    (hk : 0x9d0 + S.k ≤ 2 ^ 32) (c : CPU)
    {che ac avctx : BitVec 64} {er ps : BitVec 32} {Rc : Mem 64 → Prop}
    (hc : ApplyCall che ac (c.pack ∅).1)
    (hpc : c.pc = entry "ff_aac_sbr_apply")
    (hne : entry "ff_aac_sbr_apply" ≠ M.halt)
    (next : Host.Expr M) {E : CoPset} {Φ : Host.Value → IProp GF} :
    applyOwned S che ac avctx er ps Rc c ∗
      ▷ (applyOwned S che ac avctx er ps Rc c -∗
        WP next @ Stuckness.NotStuck; E {{ Φ }}) ⊢
      WP (applyOnce c next) @ Stuckness.NotStuck; E {{ Φ }} := by
  unfold applyOwned ready outputs
  iintro ⟨⟨Habi, Hready, Hac, Hout, HR⟩, HK⟩
  unfold applyOnce
  iapply Host.wp_prepare c (applyStack S.k)
    (Ready S che ac ⋆ (AcFields ac avctx er ps ⋆ (OutBufs (c.pack ∅).1 ⋆ Rc)))
  iframe Habi
  isplitl [Hready Hac Hout HR]
  · iapply ownsPred_sep_intro
    iframe Hready
    iapply ownsPred_sep_intro
    iframe Hac
    iapply ownsPred_sep_intro $$ [$Hout $HR]
  · iintro Hpre
    iapply wp_apply_owned S C hcode hk c hc hpc hne (fun _ => next)
    iframe Hpre
    inext
    iintro %_ Hresources
    simp only [ready, outputs]
    iapply HK $$ Hresources

/-- A finite client can reuse exactly the same decoder and buffers for any
number of calls. Every iteration includes the real caller's stack stores
and the original native instruction execution. -/
def applyMany (c : CPU) : Nat → Host.Expr M
  | 0 => .ret .unit
  | n + 1 => applyOnce c (applyMany c n)

theorem wp_applyMany (S : Setup) (C : Calls S) (hcode : cenv = M.code)
    (hk : 0x9d0 + S.k ≤ 2 ^ 32) (c : CPU)
    {che ac avctx : BitVec 64} {er ps : BitVec 32} {Rc : Mem 64 → Prop}
    (hc : ApplyCall che ac (c.pack ∅).1)
    (hpc : c.pc = entry "ff_aac_sbr_apply")
    (hne : entry "ff_aac_sbr_apply" ≠ M.halt) (n : Nat) {E : CoPset} :
    applyOwned S che ac avctx er ps Rc c ⊢
      WP (applyMany (M := M) c n) @ Stuckness.NotStuck; E
        {{ _v, applyOwned S che ac avctx er ps Rc c }} := by
  induction n with
  | zero =>
      unfold applyMany
      iintro H
      iapply Iris.wp_value' (v := Host.Value.unit)
      iexact H
  | succ n ih =>
      unfold applyMany
      iintro HR
      iapply wp_applyOnce S C hcode hk c hc hpc hne
      iframe HR
      inext
      iintro HR
      iapply ih $$ HR

end SbrClient.SbrAPI
