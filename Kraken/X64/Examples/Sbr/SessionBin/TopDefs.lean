import Kraken.X64.Examples.Sbr.SessionBin.Defs
import Kraken.X64.Examples.Sbr.SessionBin.UsacAsmS
import Kraken.X64.Examples.Sbr.Parse.InitLinkBase
import Kraken.X64.Examples.Sbr.Parse.VlcWit
import Kraken.X64.Examples.Sbr.SessionSpec

/-!
# A decoding session over the binary: the vocabulary of the headline theorem

The headline (`Top.lean`) speaks only of these names:
* `Setup`: the session's fixed parameters, chosen once by the caller;
* `Live S che ac`, `Ready S che ac`: "the SBR element at `che` (of the decoder `ac`) is in a
  state reachable from `ff_aac_sbr_ctx_alloc_init`" — and, for `Ready`, the last parse succeeded
  (what `ff_aac_sbr_apply` needs);
* `AcFields ac avctx er ps`: the three fields of `*ac` that the decoder sets and the SBR code
  reads (`avctx`, `oc[1].m4ac.ext_sample_rate`, `oc[1].m4ac.ps`); the caller owns them, with any
  values, between calls;
* `ElemOK che`: the element's address facts; the per-call obligations `DecCall`, `UsacCall`,
  `ConfigCall`, `ApplyCall`; the call objects `DecObj`, `UsacObjects`, `OutBufs`;
* `Ends f t ra Q stops`: a run entered at `f` returns to `ra` with `Q`, or reaches a stop.

The internal values (`SV`, `SReach`, the environment init produced) are hidden inside `Live`.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Session Kraken.Examples.Sbr.Parse

namespace Kraken.Examples.Sbr.SessionBin

/-! ## Parameters -/

theorem tAt_arg0 (che ac : BitVec 64) : arg0 (tAt che ac) = ac := by
  simp [tAt, arg0]

theorem tAt_arg1 (che ac : BitVec 64) : arg1 (tAt che ac) = che := by
  simp [tAt, arg1]

variable [CodeEnv]

/-! ## The element -/

/-- `SessW` is the element and the caller's `ac` fields. -/
theorem sessW_split (e : Env) (vs : Nat → Vlc.VlcTab) (vp : Nat → Ps.VlcTab) (σ : SV)
    (t : MachineData) : SessW e vs vp σ t = (ElemAt e vs vp σ (arg1 t) (arg0 t)
      ⋆ AcFields (arg0 t) σ.1.avctx σ.1.extRate σ.1.ps) := by
  have hs : sbrA (tAt (arg1 t) (arg0 t)) = sbrA t := by simp only [sbrA, tAt_arg1]
  have h1 : PsRest σ.1 (tAt (arg1 t) (arg0 t)) = PsRest σ.1 t := by unfold PsRest; rw [hs]
  have h2 : ArrW (tAt (arg1 t) (arg0 t)) = ArrW t := by unfold ArrW; rw [hs]
  have h3 : DspW e (tAt (arg1 t) (arg0 t)) = DspW e t := by unfold DspW; rw [hs]
  have h4 : FnW e σ.1 (tAt (arg1 t) (arg0 t)) = FnW e σ.1 t := by unfold FnW; rw [hs]
  unfold SessW ElemAt AcW AcFields
  simp only [h1, h2, h3, h4, hs]
  generalize DecExt.SbrF (toDS σ) (sbrA t) = A
  generalize PsRest σ.1 t = B
  generalize ArrW t = C
  generalize DspW e t = D
  generalize FnW e σ.1 t = F
  generalize CstW ⋆ PStat vs vp = G
  simp only [c8]
  generalize Int.toBytes 8 σ.1.avctx.toInt =@ (arg0 t + 0x8#64) = X1
  generalize Int.toBytes 8 σ.1.fdsp.toInt =@ (arg0 t + 0x2550#64) = X2
  generalize cell4 (arg0 t + 0x57f4#64) σ.1.extRate = X3
  generalize cell4 (arg0 t + 0x5800#64) σ.1.ps = X4
  ac_rfl

/-- The element does not read the caller's `ac` fields or memory. -/
theorem elemAt_frame (e : Env) (vs : Nat → Vlc.VlcTab) (vp : Nat → Ps.VlcTab) (σ : SV)
    (R : Mem 64 → Prop) (a : BitVec 64) (er ps : BitVec 32) (che ac : BitVec 64) :
    ElemAt e vs vp ({ σ.1 with R := R, avctx := a, extRate := er, ps := ps }, σ.2) che ac
      = ElemAt e vs vp σ che ac := rfl

/-! ## Runs -/

/-! ## Stack reservations -/

/-! ## The calls' objects and obligations -/

end Kraken.Examples.Sbr.SessionBin
