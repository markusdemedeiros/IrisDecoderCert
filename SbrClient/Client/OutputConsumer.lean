import SbrClient.Host.Consumer
import SbrClient.FFmpeg.Resources

/-! The output consumer and its exact checksum specification. Each byte read
is a physical host step. The ordinary ownership-preserving call rule is a
corollary of the exact result, so both interfaces share one scan proof. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SbrClient.SbrAPI
open Kraken Kraken.SysV Kraken.Examples.Sbr Mem
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Iris.Std
variable {hlc : HasLC} {M : Model} {GF : BundledGFunctors} [MachineGS hlc M GF]
local bi (IProp GF)

/-- Read all 16384 output bytes before acknowledging the mailbox. The
checksum calculation is modeled host code, and every read is a separate
physical step on the same shared byte heap as the native FFmpeg call. -/
def consumeOutputs (t : MachineData) : Host.Expr M :=
  .bind (Host.scanBlock (arg3 t) 8192 0) (fun v => match v with
    | .byte b => Host.scanBlock (arg4 t) 8192 b
    | _ => .fault)

def outputChecksum (t : MachineData) (left right : Mem 64) : UInt8 :=
  Host.scanValue (Host.addresses (arg4 t) 8192) right
    (Host.scanValue (Host.addresses (arg3 t) 8192) left 0)

/-- Two full buffer ownerships and a checksum of those very bytes. -/
def checksumResult [genHeapGS (BitVec 64) UInt8 GF ByteMap]
    (t : MachineData) (v : Host.Value) : IProp GF := iprop%
  ∃ left right, ⌜Block (arg3 t) 8192 left ∧ Block (arg4 t) 8192 right ∧
    v = .byte (outputChecksum t left right)⌝ ∗ owns left ∗ owns right

theorem checksumResult_outputs (t : MachineData) (v : Host.Value) :
    checksumResult (GF := GF) t v ⊢ outputs t := by
  unfold checksumResult
  iintro ⟨%left, %right, %h, HL, HR⟩
  iapply outputs_join t
  unfold buffer ownsPred
  isplitl [HL]
  · iexists left
    iframe HL
    ipureintro
    exact h.1
  · iexists right
    iframe HR
    ipureintro
    exact h.2.1

theorem wp_consumeOutputs_exact (t : MachineData) {E : CoPset} :
    outputs (GF := GF) t ⊢
      WP (consumeOutputs (M := M) t) @ Stuckness.NotStuck; E {{ v, checksumResult t v }} := by
  iintro Hout
  icases outputs_split t $$ Hout with ⟨HL, HR⟩
  unfold buffer consumeOutputs
  iapply Host.wp_bind
  iapply Host.wp_scanBlock (arg3 t) 8192 0
  iframe HL
  iintro %left %hl HL
  iapply Host.wp_scanBlock (arg4 t) 8192 (Host.scanValue (Host.addresses (arg3 t) 8192) left 0)
  iframe HR
  iintro %right %hr HR
  unfold checksumResult
  iexists left
  iexists right
  iframe HL HR
  ipureintro
  exact ⟨hl, hr, rfl⟩

/-- Forget the checksum relation when a caller only needs the buffers back. -/
theorem wp_consumeOutputs (t : MachineData) {E : CoPset} {Φ : Host.Value → IProp GF} :
    outputs t ∗ (∀ checksum, outputs t -∗ Φ (.byte checksum)) ⊢
      WP (consumeOutputs (M := M) t) @ Stuckness.NotStuck; E {{ Φ }} := by
  iintro ⟨Hout, HK⟩
  iapply Iris.wp_wand_r (Φ := checksumResult t)
  isplitl [Hout]
  · iapply wp_consumeOutputs_exact $$ Hout
  · iintro %v Hresult
    ihave %hbyte : ⌜∃ b, v = Host.Value.byte b⌝ $$ [Hresult]
    · unfold checksumResult
      icases Hresult with ⟨%left, %right, %h, _⟩
      ipureintro
      exact ⟨_, h.2.2⟩
    obtain ⟨b, rfl⟩ := hbyte
    iapply HK $$ %b
    iapply checksumResult_outputs $$ Hresult

end SbrClient.SbrAPI
