import Kraken.X64.Examples.Sbr.Parse.InitFoot
import Kraken.X64.Examples.Sbr.SessionSpec

/-!
# `ff_aac_sbr_ctx_alloc_init`: the specification

`ff_aac_sbr_ctx_alloc_init(ac, che, id_aac)` (`libavcodec/aacsbr_template.c`, FFmpeg n8.1,
l.70-113) allocates the channel element `ExtChannelElement` (`av_mallocz`, 0x88ba0 bytes), stores
it to `*che`, sets the two `predictor_state` pointers, `kx[0] = kx[1]`, `id_aac`, the stores of
`sbr_turnoff` and both `synthesis_filterbank_samples_offset`, initialises the two `av_tx` MDCT
contexts, `sbr->ps.dsp` (`ff_ps_ctx_init`, inlined: `ff_psdsp_init`), `sbr->dsp`
(`ff_sbrdsp_init`) and the four `sbr->c` slots (`aacsbr_func_ptr_init`, inlined). `ac` is not
read.

* The callees are assumed contracts (`InitAssumed`): `av_mallocz`, `av_tx_init`,
  `ff_psdsp_init`, `ff_sbrdsp_init`. They share an abstract state `X` (the allocator's, the cpu
  flags); `av_tx_init` also uses the `av_tx` tables `TxTab`, leaves its context owned as
  `Ctx c` and returns a function satisfying `TxSpec`; `ff_sbrdsp_init` leaves the `sbr->dsp`
  slots `DspSlotsOK` (the routines of `ff_sbrdsp_init_x86` with SSE, SSE2, SSE3, as in
  `SbrSlots`).
* The precondition owns only `*che` (8 bytes), `TxTab` and `X`.
* The postcondition, on every return: `0` with `*che = p` and the element at `p` owned with the
  values `evInit` (`ElemS`: zero except the cells listed in `EV`), the two contexts owned
  (`Ctx`), the two functions `TxSpec`, the slots `DspSlotsOK`; or `-12` (`AVERROR(ENOMEM)`,
  `av_mallocz` failed) with `*che` as it was; or a negative result of the first or the second
  `av_tx_init` with `*che = p` and the element with the cells stored before the call (`evPre`),
  the failed call's `*ctx`, `*tx` any bytes, after the second also the first context.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr
open Kraken.Examples.Sbr.Apply (c8)
open Kraken.Examples.Sbr.Session (zs)

namespace Kraken.Examples.Sbr.Init

variable [CodeEnv]

/-! ## The assumed contracts -/

/-! ## The values after a successful run -/

/-- The results of a successful run: the element `p`, the two `av_tx` contexts and functions,
the `sbr->dsp` slots, and the 64 bytes `ff_psdsp_init` leaves in `sbr->ps.dsp`. -/
structure IR where
  p : BitVec 64
  anaCtx : BitVec 64
  anaFn : Int64
  synCtx : BitVec 64
  synFn : Int64
  sl : Slots
  psd : List UInt8

/-- The cells after a successful run (`id_aac` is the low half of `rdx` at entry). The other
bytes of the element are zero (`ElemS`). -/
def evInit (idAac : BitVec 32) (r : IR) : EV where
  pr0 := Int.toBytes 8 (r.p + 0x1e120#64).toInt
  pr1 := Int.toBytes 8 (r.p + 0x23520#64).toInt
  sr := Int.toBytes 8 0
  id := Int.toBytes 4 idAac.toInt
  usac := Int.toBytes 4 0
  spLo := Int.toBytes 4 (-1)
  spHi := Int.toBytes 2 (-1)
  kx0 := Int.toBytes 4 0
  kx1 := Int.toBytes 4 32
  m1 := Int.toBytes 4 0
  v0 := Int.toBytes 4 0x480
  e0 := Int.toBytes 4 (-1)
  v1 := Int.toBytes 4 0x480
  e1 := Int.toBytes 4 (-1)
  ps := r.psd
  anaC := Int.toBytes 8 r.anaCtx.toInt
  anaF := fb r.anaFn
  synC := Int.toBytes 8 r.synCtx.toInt
  synF := fb r.synFn
  dsp := r.sl.bytes
  c0 := fb (entry "sbr_lf_gen")
  c1 := fb (entry "sbr_hf_assemble")
  c2 := fb (entry "sbr_x_gen")
  c3 := fb (entry "sbr_hf_inverse_filter")

/-- After a successful run: `*che = p`, the element at `p` with the cells `evInit`, the two
contexts. -/
def InitOK (Ctx : BitVec 64 → Mem 64 → Prop) (che : BitVec 64) (idAac : BitVec 32) (r : IR) :
    Mem 64 → Prop :=
  c8 che r.p ⋆ (ElemS r.p (evInit idAac r) ⋆ (Ctx r.anaCtx ⋆ Ctx r.synCtx))

/-! ## The specification -/

/-- The four outcomes (the result is `eax`). -/
abbrev InitPost (k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (TxTab X : Mem 64 → Prop)
    (R : Mem 64 → Prop) (ra : Int64) (t s : MachineData) : Prop :=
  let ret := (s.regs.get64 .rax).setWidth 32
  (ret = 0#32 ∧ ∃ r : IR, r.psd.length = 64 ∧ DspSlotsOK r.sl
      ∧ TxSpec Ctx TxTab k r.anaFn ∧ TxSpec Ctx TxTab k r.synFn
      ∧ CallPost (initNeed k) ((InitOK Ctx (arg1 t) (idOf t) r ⋆ (TxTab ⋆ X)) ⋆ R) ra t s)
  ∨ (ret = 0xfffffff4#32 ∧ CallPost (initNeed k) ((8 ?@ arg1 t ⋆ (TxTab ⋆ X)) ⋆ R) ra t s)
  -- `av_tx_init(&sbr->mdct, …)` failed: `*che = p`, the element with the stored cells and
  -- `*ctx`, `*tx` of `sbr->mdct` any bytes
  ∨ (ret.toInt < 0 ∧ ∃ (p : BitVec 64) (bc bf : List UInt8), bc.length = 8 ∧ bf.length = 8
      ∧ CallPost (initNeed k) ((c8 (arg1 t) p
          ⋆ (ElemS p { evPre (idOf t) p with synC := bc, synF := bf } ⋆ (TxTab ⋆ X))) ⋆ R)
        ra t s)
  -- `av_tx_init(&sbr->mdct_ana, …)` failed: also the first context `c` (owned, `Ctx c`) and the
  -- function `f` in `sbr->mdct`, `sbr->mdct_fn`; `sbr->mdct_ana`, `sbr->mdct_ana_fn` any bytes
  ∨ (ret.toInt < 0 ∧ ∃ (p c : BitVec 64) (f : Int64) (bc bf : List UInt8), bc.length = 8
      ∧ bf.length = 8 ∧ CallPost (initNeed k) ((c8 (arg1 t) p
          ⋆ (ElemS p
              { evPre (idOf t) p with
                synC := Int.toBytes 8 c.toInt, synF := fb f, anaC := bc, anaF := bf }
            ⋆ (Ctx c ⋆ (TxTab ⋆ X)))) ⋆ R) ra t s)

/-- `ff_aac_sbr_ctx_alloc_init` with its callees at `k` bytes of stack. -/
abbrev InitSpec (k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (TxTab X : Mem 64 → Prop) : Prop :=
  cenv.ProcSpec (entry "ff_aac_sbr_ctx_alloc_init") (InitPre k TxTab X) (InitPost k Ctx TxTab X)

end Kraken.Examples.Sbr.Init
