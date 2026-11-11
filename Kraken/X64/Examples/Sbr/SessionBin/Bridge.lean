import Kraken.X64.Examples.Sbr.SessionBin.Defs
import Kraken.X64.Examples.Sbr.SessionSpec

/-!
# A decoding session over the binary: the bridges (statements)

The entries' footprints are regroupings of the element `SessW` and the objects of a call. This
file names the groups and states the regroupings as propositions; each is proved in its own
file (`FApply*.lean`, `FDec*.lean`, `FCfg*.lean`, `DecAsm.lean`).

* `GapA`: the bytes of `*sbr` the parser owns and `ApplyF` does not (between calls they are the
  caller's memory for apply): `inter_tes`, `bs_amp_res_header`, `bs_limiter_bands` with their
  values, and raw gaps.
* `DecRest`: what `SessW` owns and `DecF` does not.
* `ExtD`: the callee state of `ff_aac_sbr_decode_extension` (`Ext` of `DecExtSpec`): the
  parser's tables and `e.Ext`.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Session Kraken.Examples.Sbr.Parse

namespace Kraken.Examples.Sbr.SessionBin

variable [CodeEnv]

/-! ## Groups -/

/-- The bytes of one `SBRData` at `d` that `DataF` owns and `DScW`/`DArrW` do not:
`bs_frame_class`, padding after `bs_freq_res`, `bs_df_env`/`bs_df_noise`, padding,
the head of `synthesis_filterbank_samples`' alignment gap, the gap after `Ypos`, the last byte of
`noise_facs_q`, the padding before `f_indexnoise` and after `f_indexsine`. -/
def ChGap (d : BitVec 64) : Mem 64 → Prop :=
  Blocks [(d, 4), (d + 0x15#64, 3), (d + 0x1c#64, 11), (d + 0x61#64, 3), (d + 0x68#64, 0x18),
    (d + 0x7924#64, 12), (d + 0x15a5f#64, 1), (d + 0x15aa9#64, 3), (d + 0x15ab4#64, 12)]

/-- What `DecExt.SbrF` owns and `ApplyF` does not: `inter_tes`, `bs_amp_res_header`,
`bs_limiter_bands` (values `hv`), and the raw gaps of the scalars, of the tables (`f_master`,
padding) and of both channels. -/
def GapA (hv : HV) (t : MachineData) : Mem 64 → Prop :=
  let s := sbrA t
  cell4 (s + 0x14#64) hv.it ⋆ (2 ?@ (s + 0x22#64) ⋆ (cell4 (s + 0x24#64) hv.amp
    ⋆ (4 ?@ (s + 0x28#64) ⋆ (c4 (s + 0x2c#64) hv.lb ⋆ (16 ?@ (s + 0x44#64)
    ⋆ (0x18 ?@ (s + 0x68#64) ⋆ (98 ?@ (s + 0x4c1f0#64) ⋆ (2 ?@ (s + 0x4c32e#64)
    ⋆ (ChGap (dA t 0) ⋆ ChGap (dA t 1))))))))))

/-- `FnW` without `e.Ext`. -/
def FnWx (e : Env) (x : Args) (t : MachineData) : Mem 64 → Prop :=
  let s := sbrA t
  Int.toBytes 8 x.anaCtx.toInt =@ (s + 0x601c0#64) ⋆ (FnCell (s + 0x601c8#64) e.fs.mdctAna
    ⋆ (Int.toBytes 8 x.synCtx.toInt =@ (s + 0x601d0#64) ⋆ (FnCell (s + 0x601d8#64) e.fs.qfs.tx
    ⋆ (FnCell (s + 0x60250#64) e.fs.lfGen ⋆ (FnCell (s + 0x60258#64) e.fs.hfAsm
    ⋆ (FnCell (s + 0x60260#64) e.fs.xGen ⋆ (FnCell (s + 0x60268#64) e.fs.hfInv
    ⋆ (FnCell x.fdsp e.fs.qfs.fmul ⋆ (FnCell (x.fdsp + 0x30#64) e.fs.qfs.fmulAdd
    ⋆ (FnCell (x.fdsp + 0x38#64) e.fs.fmulRev ⋆ (e.Ctx x.anaCtx ⋆ (e.Ctx x.synCtx
    ⋆ (e.TxTab ⋆ e.PsTab)))))))))))))

/-- What `SessW` owns and `DecF` does not: the PS context beyond `ps->common`, the work arrays,
the slots, `FnW` without `e.Ext`, `ac->fdsp`, the constants. Reads of `x`: `psh`, `anaCtx`,
`synCtx`, `fdsp` (all kept by `DecExt.XKeep`). -/
def DecRest (e : Env) (x : Args) (t : MachineData) : Mem 64 → Prop :=
  PsRest x t ⋆ (ArrW t ⋆ (DspW e t ⋆ (FnWx e x t
    ⋆ (Int.toBytes 8 x.fdsp.toInt =@ (arg0 t + 0x2550#64) ⋆ CstW))))

/-- `ff_aac_sbr_decode_extension`'s callee state: `sbr_reset`'s constants, the limiter table,
the SBR and PS Huffman tables, `e.Ext` (the shape the glue lemmas `DecExtGlue*` compose to). -/
def ExtD (e : Env) (vs : Nat → Vlc.VlcTab) (vp : Nat → Ps.VlcTab) : Mem 64 → Prop :=
  Reset.CstR ⋆ (Reset.BwR ⋆ (Vlc.VlcW vs ⋆ (Ps.PsTabs vp ⋆ e.Ext)))

/-- `decode_extension`'s logical variables from the reader `b`, index `i`, the field
`oc[1].m4ac.sample_rate = sr`, values `d`, caller's rest `R`. -/
def xaOf (R : Mem 64 → Prop) (d : DecExt.DS) (b : Rdr) (i sr : BitVec 32) : DecExt.XA :=
  ⟨R, d, b.r, i, b.sib, b.pad, sr⟩

/-! ## The regroupings (statements) -/

/-- **F-apply, at the call.** The element and the output buffers are apply's footprint and the
gaps (which, with the parser's data and the caller's rest, are apply's `x.R`). `sbr->usac`
becomes raw. -/
def FApplyPre : Prop :=
  ∀ (e : Env) (vs : Nat → Vlc.VlcTab) (vp : Nat → Ps.VlcTab) (σ : SV) (t : MachineData)
    (Rc : Mem 64 → Prop) (m : Mem 64),
    (SessW e vs vp σ t ⋆ (OutW σ.1 t ⋆ Rc)) m →
    (ApplyF e σ.1 t ⋆ (GapA σ.2 t ⋆ (PStat vs vp ⋆ Rc))) m

/-- **F-apply, at the return.** Apply's footprint at `y` with the gaps is the element at `y`, for
some value `u` of `sbr->usac`. -/
def FApplyPost : Prop :=
  ∀ (e : Env) (vs : Nat → Vlc.VlcTab) (vp : Nat → Ps.VlcTab) (y : Args) (hv : HV)
    (t : MachineData) (Rc : Mem 64 → Prop) (m : Mem 64),
    (ApplyF e y t ⋆ (GapA hv t ⋆ (PStat vs vp ⋆ Rc))) m →
    ∃ u : BitVec 32, (SessW e vs vp (y, { hv with usac := u }) t ⋆ (OutW y t ⋆ Rc)) m

/-- **F-dec, at the call.** The element and the call's objects are `DecF` (for some value `sr` of
`oc[1].m4ac.sample_rate`, raw in `AcX`) and `DecRest`. -/
def FDecPre : Prop :=
  ∀ (e : Env) (vs : Nat → Vlc.VlcTab) (vp : Nat → Ps.VlcTab) (σ : SV) (b : Rdr)
    (i : BitVec 32) (Rc : Mem 64 → Prop) (t : MachineData) (m : Mem 64),
    (SessW e vs vp σ t ⋆ DecObj b σ.1.avctx Rc i t) m →
    ∃ sr : BitVec 32, (DecExt.DecF (ExtD e vs vp) (xaOf (DecRest e σ.1 t ⋆ Rc) (toDS σ) b i sr) t
      (toDS σ) i ⋆ (DecRest e σ.1 t ⋆ Rc)) m

/-- **F-dec, at the return.** `DecF` at the values `d` with `DecRest` of `x` (whose fields
`DecRest` reads are kept, `XKeep`) is the element at `ofDS d` with the call's objects. -/
def FDecPost : Prop :=
  ∀ (e : Env) (vs : Nat → Vlc.VlcTab) (vp : Nat → Ps.VlcTab) (x : Args) (d : DecExt.DS)
    (b : Rdr) (i sr : BitVec 32) (R Rc : Mem 64 → Prop) (t : MachineData) (m : Mem 64),
    DecExt.XKeep x d.a → d.sp.length = 6 →
    (DecExt.DecF (ExtD e vs vp) (xaOf R d b i sr) t d i ⋆ (DecRest e x t ⋆ Rc)) m →
    (SessW e vs vp (ofDS d) t ⋆ DecObj b d.a.avctx Rc i t) m

/-- **F-config.** The element is `UF` (the reader, the bitstream and `ue->sbr` that `UF` names,
which `ff_aac_sbr_config_usac` does not read, are carved from the raw work arrays `ArrW`), and
any `UF` at values `st` that keep the fields outside it (`UKeep`) is the element at `ofUSt st it`
for some `inter_tes = it` (raw in `UF`). -/
def FCfg : Prop :=
  ∀ (e : Env) (vs : Nat → Vlc.VlcTab) (vp : Nat → Ps.VlcTab) (σ : SV) (t : MachineData)
    (Rc : Mem 64 → Prop) (m : Mem 64),
    (SessW e vs vp σ t ⋆ Rc) m →
    ∃ (q : Usac.UQ) (i : BitVec 32), q.a = arg0 t ∧ q.c = arg1 t
      ∧ (Usac.UF q (toUSt σ i) ⋆ q.R) m
      ∧ ∀ (st : Usac.USt) (m' : Mem 64), Usac.UKeep σ.1 st.x → Usac.SpOk st →
        (Usac.UF q st ⋆ q.R) m' →
        ∃ it : BitVec 32, (SessW e vs vp (ofUSt st it) t ⋆ Rc) m'

/-! ## The parser's assembly (statement) -/

/-- **`decode_extension` from the routines' own specifications**: `DecExtSpec` with `PI = PsInv`
and `Ext = ExtD`, from the placement, the assumed contracts, the glue (`DecExtGlue*`). -/
def DecAsm : Prop :=
  ∀ (k : Nat) (e : Env) (vs : Nat → Vlc.VlcTab) (vp : Nat → Ps.VlcTab)
    (pw : BitVec 32 → BitVec 32 → BitVec 32) (lg : BitVec 32 → BitVec 32),
    0x9d0 + k ≤ 2 ^ 32 → SessPlaced → SessionAssumed k e vs vp pw lg →
    DecExt.DecExtSpec Ps.PsInv (decKc k) (ExtD e vs vp)

end Kraken.Examples.Sbr.SessionBin
