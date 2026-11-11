import Kraken.X64.Examples.Sbr.SessionBin.Bridge
import Kraken.X64.Examples.Sbr.SessionBin.FApplyD
import Kraken.X64.Examples.Sbr.SessionBin.FApplyS

/-!
# Footprint conversion for `ff_aac_sbr_apply` (F-apply)

`fApplyPre`, `fApplyPost`: the element `SessW` with the output buffers is apply's footprint
`ApplyF` with the gaps `GapA` and the parser's static data. Both sides are
`cell ⋆ ApplyCore ⋆ GapA ⋆ PStat ⋆ Rc` up to a permutation, where the cell is `sbr->usac`
(valued in `SessW`, raw in `ApplyF`). The groups are converted in `FApplyS` (scalars, tables) and
`FApplyD` (one `SBRData`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply

namespace Kraken.Examples.Sbr.SessionBin

variable [CodeEnv]

/-- `ApplyF` without the raw `sbr->usac` cell. -/
abbrev ApplyCore (e : Env) (x : Args) (t : MachineData) : Mem 64 → Prop :=
  ScA x (sbrA t) ⋆ (TabW x t ⋆ (DScW x.d0 t 0 ⋆ (DScW x.d1 t 1 ⋆ (DArrW t 0 ⋆ (DArrW t 1
    ⋆ (ArrW t ⋆ (PsW x t ⋆ (DspW e t ⋆ (FnW e x t ⋆ (AcW x t ⋆ (CstW ⋆ OutW x t)))))))))))

theorem fa_applyF (e : Env) (x : Args) (t : MachineData) :
    ApplyF e x t = 4 ?@ (sbrA t + 0x10#64) ⋆ ApplyCore e x t := by
  rw [ApplyF, fa_scw, Std.ExtHashMap.sep_assoc]

omit [CodeEnv] in
theorem fa_gapD (d : BitVec 64) : ChGap d = GapD d := rfl

omit [CodeEnv] in
theorem fa_gapA (hv : HV) (t : MachineData) :
    GapA hv t = GapS hv.it hv.amp hv.lb (sbrA t)
      ⋆ (GapT (sbrA t) ⋆ (GapD (dA t 0) ⋆ GapD (dA t 1))) := by
  simp only [GapA, GapS, GapT, fa_gapD, Std.ExtHashMap.sep_assoc]

omit [CodeEnv] in
theorem fa_psw (x : Args) (t : MachineData) :
    PsW x t = x.psc =@ (sbrA t + 0x2b600#64) ⋆ PsRest x t := rfl

omit [CodeEnv] in
theorem fa_sbrF (σ : SV) (t : MachineData) :
    DecExt.SbrF (toDS σ) (sbrA t)
      = (cell4 (sbrA t + 0x10#64) σ.2.usac ⋆ (ScA σ.1 (sbrA t) ⋆ GapS σ.2.it σ.2.amp σ.2.lb (sbrA t)))
        ⋆ ((DScW σ.1.d0 t 0 ⋆ (DArrW t 0 ⋆ GapD (dA t 0)))
        ⋆ ((DScW σ.1.d1 t 1 ⋆ (DArrW t 1 ⋆ GapD (dA t 1)))
        ⋆ (σ.1.psc =@ (sbrA t + 0x2b600#64) ⋆ (TabW σ.1 t ⋆ GapT (sbrA t))))) := by
  have h0 : sbrA t + 0x80#64 = dA t 0 := rfl
  have h1 : sbrA t + 0x15b40#64 = dA t 1 := rfl
  rw [DecExt.SbrF, fa_sbrS _ _ rfl, h0, h1, fa_dataF, fa_dataF, fa_tabF]
  rfl

omit [CodeEnv] in
theorem fa_perm (U SA GS D0 A0 G0 D1 A1 G1 Pc TW GT PR Arr Dsp Fn Ac Cst PS Out Rc :
    Mem 64 → Prop) :
    (((U ⋆ (SA ⋆ GS)) ⋆ ((D0 ⋆ (A0 ⋆ G0)) ⋆ ((D1 ⋆ (A1 ⋆ G1)) ⋆ (Pc ⋆ (TW ⋆ GT)))))
      ⋆ (PR ⋆ (Arr ⋆ (Dsp ⋆ (Fn ⋆ (Ac ⋆ (Cst ⋆ PS)))))))
      ⋆ (Out ⋆ Rc)
    = U ⋆ ((SA ⋆ (TW ⋆ (D0 ⋆ (D1 ⋆ (A0 ⋆ (A1 ⋆ (Arr ⋆ ((Pc ⋆ PR) ⋆ (Dsp ⋆ (Fn ⋆ (Ac
      ⋆ (Cst ⋆ Out))))))))))))
      ⋆ ((GS ⋆ (GT ⋆ (G0 ⋆ G1))) ⋆ (PS ⋆ Rc))) := by
  ac_rfl

/-- Both sides as the `sbr->usac` cell and the same rest. -/
theorem fa_main (e : Env) (vs : Nat → Vlc.VlcTab) (vp : Nat → Ps.VlcTab) (σ : SV)
    (t : MachineData) (Rc : Mem 64 → Prop) :
    SessW e vs vp σ t ⋆ (OutW σ.1 t ⋆ Rc)
      = cell4 (sbrA t + 0x10#64) σ.2.usac
        ⋆ (ApplyCore e σ.1 t ⋆ (GapA σ.2 t ⋆ (PStat vs vp ⋆ Rc))) := by
  rw [SessW, fa_sbrF, ApplyCore, fa_psw, fa_gapA]
  exact fa_perm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- **F-apply, at the call.** -/
theorem fApplyPre : FApplyPre := by
  intro e vs vp σ t Rc m h
  rw [fa_main] at h
  rw [fa_applyF, Std.ExtHashMap.sep_assoc]
  exact fa_cell4_blk h

/-- **F-apply, at the return.** -/
theorem fApplyPost : FApplyPost := by
  intro e vs vp y hv t Rc m h
  rw [fa_applyF, Std.ExtHashMap.sep_assoc] at h
  obtain ⟨u, hu⟩ := fa_blk_cell4 h
  exact ⟨u, by rw [fa_main]; exact hu⟩

end Kraken.Examples.Sbr.SessionBin
