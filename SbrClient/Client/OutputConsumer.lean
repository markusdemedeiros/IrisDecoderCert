import SbrClient.Host.Consumer
import SbrClient.FFmpeg.Resources

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SbrClient.SbrAPI
open Kraken Kraken.SysV Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Mem Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Iris.Std
variable {hlc : HasLC} {M : Model} {GF : BundledGFunctors} [MachineGS hlc M GF] [CodeEnv]
local bi (IProp GF)

/-- Read all 16384 output bytes before acknowledging the mailbox. The
checksum calculation is modeled host code, and every read is a separate
physical step on the same shared byte heap as the native FFmpeg call. -/
def consumeOutputs (t : MachineData) : Host.Expr M :=
  .bind (Host.scanBlock (arg3 t) 8192 0) (fun v => match v with
    | .byte b => Host.scanBlock (arg4 t) 8192 b
    | _ => .fault)

theorem wp_consumeOutputs (t : MachineData) {E : CoPset} {Φ : Host.Value → IProp GF} :
    outputs t ∗ (∀ checksum, outputs t -∗ Φ (.byte checksum)) ⊢
      WP (consumeOutputs (M := M) t) @ Stuckness.NotStuck; E {{ Φ }} := by
  iintro ⟨Hout, HK⟩
  icases outputs_split t $$ Hout with ⟨HL, HR⟩
  unfold buffer
  unfold consumeOutputs
  iapply Host.wp_bind
  iapply Host.wp_scanBlock (arg3 t) 8192 0
  iframe HL
  iintro %p %hp Hp
  iapply Host.wp_scanBlock (arg4 t) 8192 (Host.scanValue (Host.addresses (arg3 t) 8192) p 0)
  iframe HR
  iintro %q %hq Hq
  iapply HK
  iapply outputs_join t
  unfold buffer ownsPred
  isplitl [Hp]
  · iexists p
    iframe Hp
    ipureintro
    exact hp
  · iexists q
    iframe Hq
    ipureintro
    exact hq

end SbrClient.SbrAPI
