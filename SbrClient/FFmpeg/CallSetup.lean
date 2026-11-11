import SbrClient.Host.Stores
import SbrClient.FFmpeg.Resources

/-! A caller reinstalls its return address using real host stores before
entering the native machine. This closes the stack-resource cycle between
FFmpeg's weaker `CallPost` and the next call's `CallPre`. -/
namespace SbrClient.Host
open Kraken Kraken.SysV Mem Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Iris.Std
variable {hlc : HasLC} {M : Model} {GF : BundledGFunctors} [MachineGS hlc M GF]
local bi (IProp GF)

def prepare (c : CPU) (next : Expr M) : Expr M :=
  .bind (writeBytes (c.regs.get64 .rsp) (Int.toBytes 8 M.halt.toBitVec.toInt)) (fun _ => next)

theorem wp_prepare (c : CPU) (d : Nat) (R : Mem 64 → Prop) (next : Expr M)
    {E : CoPset} {Φ : Value → IProp GF} :
    SbrAPI.abiResources d (c.pack ∅).1 ∗ ownsPred R ∗
      (ownsPred (fun p => CallPre d R M.halt (c.pack p).1) -∗
        WP next @ Stuckness.NotStuck; E {{ Φ }}) ⊢
      WP (prepare c next) @ Stuckness.NotStuck; E {{ Φ }} := by
  unfold SbrAPI.abiResources
  simp only [CPU.pack, CallPre, RetCell, Mem.Val]
  iintro ⟨⟨Hret, Hstack⟩, HR, HK⟩
  unfold prepare
  iapply wp_bind
  iapply wp_initializeBlock (c.regs.get64 .rsp) (Int.toBytes 8 M.halt.toBitVec.toInt)
  simp only [Int.toBytes_length]
  iframe Hret
  iintro Hret
  iapply HK
  iapply ownsPred_sep_intro
  iframe Hret
  iapply ownsPred_sep_intro $$ [$Hstack $HR]

end SbrClient.Host
