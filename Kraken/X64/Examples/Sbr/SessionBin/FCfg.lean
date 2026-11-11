import Kraken.X64.Examples.Sbr.SessionBin.Bridge
import Kraken.X64.Examples.Sbr.SessionBin.Inv
import Kraken.X64.Examples.Sbr.SessionBin.FCfgA

/-!
# Footprint conversion for `ff_aac_sbr_config_usac` (F-config)

`fCfg`: the element `SessW` is `Usac.UF` with a frame `q.R`. The reader `*gb` and `ue->sbr`,
which `UF` names and `ff_aac_sbr_config_usac` does not read, are carved from `X_low` (`Carve`),
their values are what those bytes hold, and the bitstream is empty. Back, the bytes return to
`X_low`, `inter_tes` (raw in `UF`) gets some value, and the fields outside `UF` that the frame
reads are kept (`UKeep`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Usac

namespace Kraken.Examples.Sbr.SessionBin

variable [CodeEnv]

/-- The parser's static data besides `read_sbr_grid`'s jump table and `ceil_log2`. -/
abbrev Oth (vs : Nat → Vlc.VlcTab) (vp : Nat → Ps.VlcTab) : Mem 64 → Prop :=
  Vlc.VlcW vs ⋆ (Ps.PsTabs vp ⋆ (Reset.CstR ⋆ Reset.BwR))

/-- `PStat` with `e.Ext`. -/
abbrev Stat (e : Env) (vs : Nat → Vlc.VlcTab) (vp : Nat → Ps.VlcTab) : Mem 64 → Prop :=
  Grid.JtW ⋆ (Blocks [(lab "ceil_log2", 6)] ⋆ (e.Ext ⋆ Oth vs vp))

/-- The frame of the call: what `SessW` owns and `UF` does not, and the caller's rest. -/
abbrev QR (e : Env) (x : Args) (t : MachineData) (Rc : Mem 64 → Prop) : Mem 64 → Prop :=
  PsRest x t ⋆ (ArrRest t ⋆ (DspW e t ⋆ (FnWx e x t
    ⋆ (Int.toBytes 8 x.fdsp.toInt =@ (arg0 t + 0x2550#64) ⋆ (cell4 (arg0 t + 0x5800#64) x.ps
    ⋆ (x.psc =@ (sbrA t + 0x2b600#64) ⋆ (CstW ⋆ Rc)))))))

/-- `UF` without the reader, the bitstream, the read-only data and the raw `inter_tes`. -/
abbrev UCore (c a : BitVec 64) (x : Args) (u amp : BitVec 32) (lb : Nat) (sp : List UInt8) :
    Mem 64 → Prop :=
  SHWr c x u amp lb sp ⋆ (TWc c x ⋆ (DSc c 0 x.d0 ⋆ (DRaw c 0 ⋆ (DSc c 1 x.d1
    ⋆ (DRaw c 1 ⋆ AcU a x)))))

/-- The logical variable of `UF` at the call. -/
def qOf (e : Env) (vs : Nat → Vlc.VlcTab) (vp : Nat → Ps.VlcTab) (x : Args) (t : MachineData)
    (Rc : Mem 64 → Prop) (b : BitVec 64) (p : BitVec 32) (uev : List UInt8) : UQ :=
  ⟨QR e x t Rc, arg0 t, arg1 t, sbrA t + 0x4c348#64, sbrA t + 0x4c340#64, b, p, 0, uev, e.Ext,
    Oth vs vp⟩

omit [CodeEnv] in
theorem fc_acW (x : Args) (t : MachineData) :
    AcW x t = AcU (arg0 t) x ⋆ (Int.toBytes 8 x.fdsp.toInt =@ (arg0 t + 0x2550#64)
      ⋆ cell4 (arg0 t + 0x5800#64) x.ps) := by
  simp only [AcW, AcU]; generalize arg0 t = a; ac_rfl

omit [CodeEnv] in
theorem fc_fnW (e : Env) (x : Args) (t : MachineData) : FnW e x t = FnWx e x t ⋆ e.Ext := by
  simp only [FnW, FnWx, Std.ExtHashMap.sep_assoc]

omit [CodeEnv] in
theorem fc_perm1 (It SHr D0 R0 D1 R1 Pc TW PR Cv AR Dsp Fx Ex Ac Fd Ps Cst Jt Ce Ot Rc :
    Mem 64 → Prop) :
    (((It ⋆ SHr) ⋆ ((D0 ⋆ R0) ⋆ ((D1 ⋆ R1) ⋆ (Pc ⋆ TW))))
      ⋆ (PR ⋆ ((Cv ⋆ AR) ⋆ (Dsp ⋆ ((Fx ⋆ Ex) ⋆ ((Ac ⋆ (Fd ⋆ Ps)) ⋆ (Cst ⋆ (Jt ⋆ (Ce ⋆ Ot)))))))))
      ⋆ Rc
    = It ⋆ ((SHr ⋆ (TW ⋆ (D0 ⋆ (R0 ⋆ (D1 ⋆ (R1 ⋆ Ac))))))
      ⋆ (Cv ⋆ ((Jt ⋆ (Ce ⋆ (Ex ⋆ Ot)))
      ⋆ (PR ⋆ (AR ⋆ (Dsp ⋆ (Fx ⋆ (Fd ⋆ (Ps ⋆ (Pc ⋆ (Cst ⋆ Rc))))))))))) := by
  ac_rfl

/-- The element as the `inter_tes` cell, `UF`'s core, `Carve`, the static data and the frame. -/
theorem fc_sess (e : Env) (vs : Nat → Vlc.VlcTab) (vp : Nat → Ps.VlcTab) (σ : SV)
    (t : MachineData) (Rc : Mem 64 → Prop) :
    SessW e vs vp σ t ⋆ Rc
      = cell4 (sbrA t + 0x14#64) σ.2.it
        ⋆ (UCore (arg1 t) (arg0 t) σ.1 σ.2.usac σ.2.amp σ.2.lb (spBytes σ.1)
        ⋆ (Carve (sbrA t) ⋆ (Stat e vs vp ⋆ QR e σ.1 t Rc))) := by
  have eS : DecExt.SbrS (toDS σ) (sbrA t) = cell4 (sbrA t + 0x14#64) σ.2.it
      ⋆ SHWr (arg1 t) σ.1 σ.2.usac σ.2.amp σ.2.lb (spBytes σ.1) :=
    fc_sbrS (toDS σ) (arg1 t) (spBytes_length _)
  have e0 : DecExt.DataF (toDS σ).a.d0 (sbrA t + 0x80#64) = DSc (arg1 t) 0 σ.1.d0 ⋆ DRaw (arg1 t) 0 :=
    fc_dataF _ (arg1 t) 0
  have e1 : DecExt.DataF (toDS σ).a.d1 (sbrA t + 0x15b40#64)
      = DSc (arg1 t) 1 σ.1.d1 ⋆ DRaw (arg1 t) 1 :=
    fc_dataF _ (arg1 t) 1
  have eT : DecExt.TabF (toDS σ).a (sbrA t) = TWc (arg1 t) σ.1 := rfl
  have eP : PStat vs vp = Grid.JtW ⋆ (Blocks [(lab "ceil_log2", 6)] ⋆ Oth vs vp) := rfl
  rw [SessW, DecExt.SbrF, eS, e0, e1, eT, eP, fc_arrW, fc_fnW, fc_acW]
  exact fc_perm1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

omit [CodeEnv] in
theorem fc_perm2 (Z SHr TW D0 R0 D1 R1 Ac B I W P Bk Ce Jt U Ex Ot QR : Mem 64 → Prop)
    (h : Bk = Std.ExtHashMap.emp) :
    (Z ⋆ SHr) ⋆ (TW ⋆ (D0 ⋆ (R0 ⋆ (D1 ⋆ (R1 ⋆ (Ac ⋆ ((B ⋆ (I ⋆ (W ⋆ P)))
      ⋆ ((Bk ⋆ Ce) ⋆ (Jt ⋆ (U ⋆ (Ex ⋆ Ot))))))))))) ⋆ QR
    = Z ⋆ ((SHr ⋆ (TW ⋆ (D0 ⋆ (R0 ⋆ (D1 ⋆ (R1 ⋆ Ac))))))
      ⋆ ((B ⋆ (I ⋆ (W ⋆ (P ⋆ U)))) ⋆ ((Jt ⋆ (Ce ⋆ (Ex ⋆ Ot))) ⋆ QR))) := by
  subst h
  rw [Std.ExtHashMap.emp_sep]
  ac_rfl

/-- `UF` at `qOf` with its frame, in the shape of `fc_sess`. -/
theorem fc_uf (e : Env) (vs : Nat → Vlc.VlcTab) (vp : Nat → Ps.VlcTab) (x : Args)
    (t : MachineData) (Rc : Mem 64 → Prop) (b : BitVec 64) (p : BitVec 32) (uev : List UInt8)
    (st : USt) :
    UF (qOf e vs vp x t Rc b p uev) st ⋆ (qOf e vs vp x t Rc b p uev).R
      = 4 ?@ (sbrA t + 0x14#64)
        ⋆ (UCore (arg1 t) (arg0 t) st.x st.u st.amp st.h.lb st.sp
        ⋆ (GbX (sbrA t) b st.i p uev ⋆ (Stat e vs vp ⋆ QR e x t Rc))) := by
  rw [UF, fc_shw, GbU, RdU]
  exact fc_perm2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fc_blk0 b)

/-- The frame at values that keep the fields it reads. -/
theorem fc_qr (e : Env) (x y : Args) (sp : List UInt8) (t : MachineData) (Rc : Mem 64 → Prop)
    (hk : UKeep x y) : QR e (withSp y sp) t Rc = QR e x t Rc := by
  obtain ⟨hpsc, hpsh, ha, hs, hf, hps, -, -⟩ := hk
  show QR e y t Rc = QR e x t Rc
  simp only [QR, PsRest, FnWx, hpsc, hpsh, ha, hs, hf, hps]

/-- **F-config.** -/
theorem fCfg : FCfg := by
  intro e vs vp σ t Rc m h
  rw [fc_sess] at h
  obtain ⟨b, i, p, v, h2⟩ := fc_carve_ex (A := 4 ?@ (sbrA t + 0x14#64)) (fa_cell4_blk h)
  refine ⟨qOf e vs vp σ.1 t Rc b p (Int.toBytes 12 v.toInt), i, rfl, rfl, ?_, ?_⟩
  · rw [fc_uf]; exact h2
  · intro st m' hk hsp h3
    rw [fc_uf] at h3
    obtain ⟨it, h4⟩ := fa_blk_cell4 h3
    have h5 := fc_carve_back (Int.toBytes_length 12 _) h4
    refine ⟨it, ?_⟩
    rw [fc_sess]
    show (cell4 (sbrA t + 0x14#64) it
        ⋆ (UCore (arg1 t) (arg0 t) st.x st.u st.amp st.h.lb (spBytes (withSp st.x st.sp))
        ⋆ (Carve (sbrA t) ⋆ (Stat e vs vp ⋆ QR e (withSp st.x st.sp) t Rc)))) m'
    rw [spBytes_withSp _ hsp.1, fc_qr e σ.1 st.x st.sp t Rc hk]
    exact h5

end Kraken.Examples.Sbr.SessionBin
