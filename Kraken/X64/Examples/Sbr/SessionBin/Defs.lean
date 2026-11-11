import Kraken.X64.Examples.Sbr.Session
import Kraken.X64.Examples.Sbr.Parse.DecExtSpec
import Kraken.X64.Examples.Sbr.Parse.UsacSpec
import Kraken.X64.Examples.Sbr.Parse.PsSpec
import Kraken.X64.Examples.Sbr.Parse.ResetSpec
import Kraken.X64.Examples.Sbr.Parse.EnvVlc
import Kraken.X64.Examples.Sbr.Parse.GridSpec
import Kraken.X64.Examples.Sbr.Parse.HdrText
import Kraken.X64.Examples.Sbr.Parse.TlimText
import Kraken.X64.Examples.Sbr.Parse.GridText
import Kraken.X64.Examples.Sbr.Parse.DtdfText
import Kraken.X64.Examples.Sbr.Parse.InvfText
import Kraken.X64.Examples.Sbr.Parse.EnvText
import Kraken.X64.Examples.Sbr.Parse.NoiseText
import Kraken.X64.Examples.Sbr.Parse.PsText
import Kraken.X64.Examples.Sbr.Parse.InitText
import Kraken.X64.Examples.Sbr.SessionSpec

/-!
# A decoding session over the binary: definitions

`Session.session_call` proves one call of `ff_aac_sbr_apply` in a session whose parser is an
abstract relation (`ParseStep`). The session here has the parser's entry points as machine code,
each by its proved specification: `ff_aac_sbr_decode_extension` (`DecExt.DecExtSpec`),
`ff_aac_sbr_decode_usac_data` (`Usac.UsacSpec`), `ff_aac_sbr_config_usac` (`Usac.ConfigSpec`),
and `ff_aac_sbr_apply` (`ff_aac_sbr_apply_linked`), with the caller's frame steps in between.

* Values: one record `SV = Args × HV`. `Args` are apply's values (`spLo`/`spHi` hold the six
  bytes of `spectrum_params`); `HV` holds the raw scalars of `*sbr` only the parser reads. The
  parser's records are views of it (`toDS`, `toUSt`, with the model's `Hid` derived, `hidOf`),
  and a parser result gives the next value (`ofDS`, `ofUSt`).
* Memory: one description of the element between calls, `SessW`: `DecExt.SbrF` (all of `*sbr`
  the parser owns, typed as the parser types it), the groups only apply owns, and the parser's
  read-only data `PStat`. Each entry's footprint is a regrouping of `SessW` and the objects of
  the call (the bit reader, the bitstream, the output buffers, three fields of `*ac`).
* `SReach`: the values reachable from init, closed under what each entry's postcondition allows,
  with a flag `ok`: `ff_aac_sbr_apply` may follow (not after a failed USAC frame, which returns
  before apply, `aac/aacdec_usac.c`:1659-1661).
* `SInv`: the invariant on the values that every call keeps.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Session Kraken.Examples.Sbr.Parse

namespace Kraken.Examples.Sbr.SessionBin

/-! ## Values -/

/-- `ff_aac_sbr_decode_usac_data`'s values, with the reader's index `i`. -/
def toUSt (σ : SV) (i : BitVec 32) : Usac.USt :=
  ⟨σ.1, hidOf σ, i, σ.2.usac, σ.2.amp, spBytes σ.1⟩

/-! ## The invariant -/

/-- What every call keeps: the model invariant `MI` (with I1 on the bytes, `GridInv`, `Inv2`),
`ff_ps_read_data`'s invariant of `ps->common`, the width of `bs_limiter_bands`, the lengths of
the byte arrays. -/
def SInv (σ : SV) : Prop :=
  MI (σ.1, hidOf σ) ∧ Ps.PsInv σ.1.psc ∧ σ.2.lb ≤ 3 ∧ DecExt.Lens σ.1

/-! ## Steps -/

variable [CodeEnv]

/-! ## The memory between calls -/

/-- **The element between calls.** It depends on the call state only through `ac = arg0` and
`che = arg1`. -/
def SessW (e : Env) (vs : Nat → Vlc.VlcTab) (vp : Nat → Ps.VlcTab) (σ : SV) (t : MachineData) :
    Mem 64 → Prop :=
  DecExt.SbrF (toDS σ) (sbrA t) ⋆ (PsRest σ.1 t ⋆ (ArrW t ⋆ (DspW e t ⋆ (FnW e σ.1 t
    ⋆ (AcW σ.1 t ⋆ (CstW ⋆ PStat vs vp))))))

/-! ## Hypotheses -/

/-! ## The caller's frames -/

/-- The element's address facts, shared by the entries: `che` 32-aligned (so is `sbr`,
`sbrA_aligned`), the signed bound of apply's `qmf_post_shuffle` operand, no wrap of `*sbr`. -/
def ElemC (t : MachineData) : Prop :=
  isAligned 32 (arg1 t) = true
  ∧ (sbrA t + 0x5fcc0#64).toInt + 1280 < 2 ^ 63 ∧ (sbrA t).toNat + 0x60000 < 2 ^ 64

/-- `ff_aac_sbr_decode_extension(ac, che, gb, crc, cnt, id_aac)` at the values `σ`: the
convention with the element and the call's objects, the reader's bound, the element's address
facts, and the ABI alignment. -/
structure DecFrame (kc : Nat) (e : Env) (vs : Nat → Vlc.VlcTab) (vp : Nat → Ps.VlcTab) (σ : SV)
    (b : Rdr) (i : BitVec 32) (Rc : Mem 64 → Prop) (ra : Int64) (t : MachineData) : Prop where
  own : CallPre (DecExt.decNeed kc) (SessW e vs vp σ t ⋆ DecObj b σ.1.avctx Rc i t) ra t
  rd : b.r.ok i
  elem : ElemC t
  align : isAligned 16 (t.regs.get64 .rsp + 8#64) = true

/-- `ff_aac_sbr_decode_usac_data(ac, che, ue, gb, sbr_ch, indep_flag)` at the values `σ`
`q.Ext`, `q.Oth` are not used (the element's `PStat` and `e.Ext` serve). -/
structure UsacFrame (k : Nat) (e : Env) (vs : Nat → Vlc.VlcTab) (vp : Nat → Ps.VlcTab) (σ : SV)
    (q : Usac.UQ) (i : BitVec 32) (ra : Int64) (t : MachineData) : Prop where
  own : CallPre (Usac.usacNeed k) (SessW e vs vp σ t ⋆ UsacObj q i) ra t
  args : arg0 t = q.a ∧ arg1 t = q.c ∧ arg2 t = q.ue ∧ arg3 t = q.g
  rd : i.toNat ≤ q.p8.toNat ∧ Usac.GbC q
  /-- `ue->sbr`: twelve bytes, the default header's `start_freq` (4 bits), `limiter_bands`,
  `limiter_gains` (2 bits each), as the configuration parser reads them. -/
  ue : q.uev.length = 12 ∧ u8 q.uev 1 < 16 ∧ u8 q.uev 6 < 4 ∧ u8 q.uev 7 < 4
  /-- `ue->sbr`'s default header `freq_scale` (2 bits, as the configuration parser reads it;
  copied into `spectrum_params` and read by `sbr_reset`). -/
  uev3 : u8 q.uev 3 ≤ 3
  elem : ElemC t
  align : isAligned 16 (t.regs.get64 .rsp + 8#64) = true

/-- `ff_aac_sbr_config_usac(ac, che, ue)` at the values `σ`. -/
structure ConfigFrame (e : Env) (vs : Nat → Vlc.VlcTab) (vp : Nat → Ps.VlcTab) (σ : SV)
    (Rc : Mem 64 → Prop) (ra : Int64) (t : MachineData) : Prop where
  own : CallPre 0 (SessW e vs vp σ t ⋆ Rc) ra t

/-- `ff_aac_sbr_apply(ac, che, id_aac, L, R)` at the values `σ`: the element, the output
buffers, the caller's rest; the element's address facts, the ABI stack alignment, the output
buffers 32-aligned (with `SessPlaced.labs`, apply's `LayoutC`). -/
structure ApplyFrame (k : Nat) (e : Env) (vs : Nat → Vlc.VlcTab) (vp : Nat → Ps.VlcTab) (σ : SV)
    (Rc : Mem 64 → Prop) (ra : Int64) (t : MachineData) : Prop where
  own : CallPre (applyNeed k) (SessW e vs vp σ t ⋆ (OutW σ.1 t ⋆ Rc)) ra t
  elem : ElemC t
  align : isAligned 16 (t.regs.get64 .rsp + 8#64) = true
  /-- The output buffers `L`, `R` 32-aligned. -/
  out : isAligned 32 (arg3 t) = true ∧ isAligned 32 (arg4 t) = true

end Kraken.Examples.Sbr.SessionBin
