import Kraken.X64.Parser
import Kraken.Blocks
import Kraken.MachineWP
import Kraken.SysV
import Kraken.SeparationMem
import Kraken.X64.Examples.Sbr.ApplyText
import Kraken.X64.Examples.Sbr.Dsp.AutocorrelateText
import Kraken.X64.Examples.Sbr.Dsp.HfApplyNoiseText
import Kraken.X64.Examples.Sbr.Dsp.HfGenText
import Kraken.X64.Examples.Sbr.Dsp.HfGFiltText
import Kraken.X64.Examples.Sbr.Dsp.NegOdd64Text
import Kraken.X64.Examples.Sbr.Dsp.QmfDeintBflyText
import Kraken.X64.Examples.Sbr.Dsp.QmfDeintNegText
import Kraken.X64.Examples.Sbr.Dsp.QmfPostShuffleText
import Kraken.X64.Examples.Sbr.Dsp.QmfPreShuffleText
import Kraken.X64.Examples.Sbr.Dsp.Sum64x5Text
import Kraken.X64.Examples.Sbr.Dsp.SumSquareText
import Kraken.X64.Examples.Sbr.Dsp.VectorFmulAddText
import Kraken.X64.Examples.Sbr.Dsp.VectorFmulRevText
import Kraken.X64.Examples.Sbr.Dsp.VectorFmulText
import Kraken.X64.Examples.Sbr.HfAssembleText
import Kraken.X64.Examples.Sbr.HfInverseFilterText
import Kraken.X64.Examples.Sbr.LfGenText
import Kraken.X64.Examples.Sbr.Parse.DecExtText
import Kraken.X64.Examples.Sbr.Parse.DtdfText
import Kraken.X64.Examples.Sbr.Parse.EnvText
import Kraken.X64.Examples.Sbr.Parse.GridText
import Kraken.X64.Examples.Sbr.Parse.HdrText
import Kraken.X64.Examples.Sbr.Parse.InitText
import Kraken.X64.Examples.Sbr.Parse.InvfText
import Kraken.X64.Examples.Sbr.Parse.NoiseText
import Kraken.X64.Examples.Sbr.Parse.PsText
import Kraken.X64.Examples.Sbr.Parse.ResetBlocks
import Kraken.X64.Examples.Sbr.Parse.TlimText
import Kraken.X64.Examples.Sbr.Parse.UsacText
import Kraken.X64.Examples.Sbr.QmfSynthesisText
import Kraken.X64.Examples.Sbr.XGenText
import Kraken.X64.Examples.Sbr.SessionSpecData

/-!
# The specification of the SBR decoder's binary

This file, with the Huffman tables in `SessionSpecData.lean`, holds every definition that the
two final theorems' statements depend on, other than the machine model and the program texts:

```
theorem sbr_session_safe (B : SbrBinary) (S : Setup) (X : Mem 64 → Prop) (hx : InitExt S X)
    (hk : 0x9d0 + S.k ≤ 2 ^ 32) :
    InitSafe S X ∧ DecSafe S ∧ UsacSafe S ∧ ConfigSafe S ∧ ApplySafe S
```

(`SessionBin/Top.lean`; namespace `Kraken.Examples.Sbr.SessionBin`, `[CodeEnv]`) and
`ff_aac_sbr_apply_linked` (`Link.lean`), the contract of `ff_aac_sbr_apply` with its callees at
`k` bytes of stack.

## How to review

What a reader must trust to believe the two statements is the union of three things:

* the machine model: the modules `Kraken.*` outside `Kraken.X64.Examples` (the x86-64 syntax
  and semantics, memory, separation logic, `ProcSpec`, the System V convention, the parser of
  the program texts);
* the program texts, the `Program` constants this file mentions (`Apply.body`, `Ps.body`,
  `NegOdd64.body`, …, in the `…Text.lean` modules and `Parse/ResetBlocks.lean`, which import
  only the parser and the machine model). They are not to be read: translation validation
  (`scripts/sbr/tv`) checks each against the bytes of the compiled object;
* this file and `SessionSpecData.lean` (the twenty Huffman tables FFmpeg builds at start-up,
  generated and validated by `scripts/sbr/vlc/gen.py`).

`scripts/sbr/SpecCheck.lean` (run by `ci.sh`) checks that the two theorems' trusted closures
contain nothing else: every other declaration they reach is here, the text modules import only
the machine model and the parser, and this file imports only the machine model, the text
modules and `SessionSpecData`. `scripts/sbr/Tcb.lean` fingerprints the closures. The proofs
(everything else under `Kraken/X64/Examples/Sbr`) import this file and are checked by Lean.

The definitions are in dependency order, in one section per proof module (named in the
section's heading: it holds the lemmas about them, and they used to be defined there); within
a section, in that module's order, with the same namespaces and `open`s.

## Contents

* **Binary placement** — the texts placed in the ambient code (`Program.PlacedIn`) and the
  facts of the link: `SbrDspPlaced` (§7), `FloatDspPlaced` (§8), `SbrPlaced`, `SbrSlots`
  (§9), `SessPlaced` (§19), `SbrBinary` (§25).
* **External contracts** — the routines outside the binary, assumed: the leaf convention
  `LeafSpec` and `av_tx`/`memcpy`/`memset`/`ff_ps_apply`/`av_log` (§1); `memcpy`/`memset`
  with values (§5); `SbrAssumed` (§9); `powf`/`log2f` (§12); `av_mallocz`, `av_tx_init`, the
  DSP initialisers, `InitAssumed` (§14); `avpriv_request_sample` (§17); `SessionAssumed`
  (§19); `InitExt` (§24).
* **Numeric facts** — the floating-point facts the statement assumes: `BandsAt`, `NqOK`,
  `BandsOK` (§12).
* **Per-call frames** — the memory each call owns: `ff_aac_sbr_apply`'s `ScW` … `OutW`,
  `ApplyF` (§2); the element as cells `EV`, `ElemS` (§13); `decode_extension`'s `DataF`,
  `TabF`, `SbrF` (§17); `decode_usac_data`'s (§18); the reader and the caller's objects
  `Rdr`, `DecObj`, `UsacObj` (§19); `FdspW` (§20); `OutBufs`, `UsacObjects` (§23); init's
  `InitOwn`, `InitQ` (§24).
* **Vocabulary** — `Live`, `Ready`, `AcFields`, `ElemState`, `EnvOK`, `Ends`, `Traps`, and
  the call shapes `DecCall`, `UsacCall`, `ConfigCall`, `ApplyCall` (§23).
* **Models** — the functional models the invariants are stated in: the session (`ApplyRel`,
  `FrameStep`, `InitIn`, `GridInv`, §10); the parser's state (`ParseModel.Live`, `St`, §11);
  the session steps over the binary (`HV`, `SV`, `σInit`, `Step`, `SReach`, §19).
* **The apply specification** — `Apply.ApplySpec` with `ApplyPre`, `ApplyPost` and the
  environment `Apply.Env` (§2), over the callee contracts of §1.
* **Parser contracts used by the statement** — the Huffman tables' shape `VlcC` (§3, §4) and
  their addresses (§6), `read_sbr_grid`'s jump table (§16), `abort` (§15), the callee stacks
  `decKc`, `usacK` (§21, §22).
* **The headline** — `InitSafe`, `DecSafe`, `UsacSafe`, `ConfigSafe`, `ApplySafe` (§25).
-/

/-! ## §1. The leaf convention and the callee contracts

Lemmas about these: `Spec.lean`. -/

section

open Kraken
open Kraken.SysV
open Mem
namespace Kraken.Examples.Sbr
variable [CodeEnv]

/-- The address of a label of the ambient code. -/
abbrev lab (l : Label) : BitVec 64 := ((_root_.Executable.labels cenv).label l).toBitVec

/-- The address of a label as an `Int64` (what `ProcSpec` is stated at). -/
abbrev entry (l : Label) : Int64 := (_root_.Executable.labels cenv).label l

/-- The argument registers at entry, as 64-bit values. -/
abbrev arg0 (t : MachineData) : BitVec 64 := t.regs.get64 .rdi

abbrev arg1 (t : MachineData) : BitVec 64 := t.regs.get64 .rsi

abbrev arg2 (t : MachineData) : BitVec 64 := t.regs.get64 .rdx

abbrev arg3 (t : MachineData) : BitVec 64 := t.regs.get64 .rcx

abbrev arg4 (t : MachineData) : BitVec 64 := t.regs.get64 .r8

abbrev arg5 (t : MachineData) : BitVec 64 := t.regs.get64 .r9

/-- A leaf's specification: the convention with `need` bytes of stack, the
footprint `F t` (in terms of the entry state) owned in front of the caller's
memory, and the side conditions `C t` (alignment, sizes). It returns with the
convention restored and the footprint still owned (its contents changed). -/
abbrev LeafPre (need : Nat) (F : MachineData → Mem 64 → Prop) (C : MachineData → Prop)
    (R : Mem 64 → Prop) (ra : Int64) (t : MachineData) : Prop :=
  CallPre need (F t ⋆ R) ra t ∧ C t

abbrev LeafPost (need : Nat) (F : MachineData → Mem 64 → Prop)
    (R : Mem 64 → Prop) (ra : Int64) (t s : MachineData) : Prop :=
  CallPost need (F t ⋆ R) ra t s

/-- The `ProcSpec` of a leaf at label `l`. -/
abbrev LeafSpec (l : Label) (need : Nat) (F : MachineData → Mem 64 → Prop)
    (C : MachineData → Prop) : Prop :=
  cenv.ProcSpec (entry l) (LeafPre need F C) (LeafPost need F)

/-- A contract at a code address `f`: `LeafSpec` for a callee known only
through a pointer. `LeafSpec l` is `LeafSpecAt (entry l)`. -/
abbrev LeafSpecAt (f : Int64) (need : Nat) (F : MachineData → Mem 64 → Prop)
    (C : MachineData → Prop) : Prop :=
  cenv.ProcSpec f (LeafPre need F C) (LeafPost need F)

/-- Assumed: `mdct_fn(ctx, out, in, stride)` for the half-length inverse MDCT of
length 64 that `sbr->mdct` is initialised to (`av_tx_init(…, AV_TX_FLOAT_MDCT,
1, 64, …)`, `libavutil/tx.h`): it reads `in[64]`, writes `out[64]` (both 256
bytes, disjoint) and uses its context, an abstract owned predicate `Ctx ctx`
that it gives back, and `TxTab`, the shared static tables of `av_tx`
(`ff_tx_tab_*`, `tab_32_float`; `libavutil/tx_template.c`,
`libavutil/x86/tx_float.asm`), also given back (that it only reads them is not
expressed). The stride is the sample size, 4; `out` is 32-byte aligned (the
SIMD kernels store aligned). -/
abbrev TxF (Ctx : BitVec 64 → Mem 64 → Prop) (TxTab : Mem 64 → Prop) (t : MachineData) :
    Mem 64 → Prop :=
  Blocks [(arg1 t, 256), (arg2 t, 256)] ⋆ (Ctx (arg0 t) ⋆ TxTab)

abbrev TxC (t : MachineData) : Prop := arg3 t = 4#64 ∧ isAligned 32 (arg1 t) = true

abbrev TxSpec (Ctx : BitVec 64 → Mem 64 → Prop) (TxTab : Mem 64 → Prop) (need : Nat)
    (f : Int64) : Prop :=
  LeafSpecAt f need (TxF Ctx TxTab) TxC

/-- Assumed: `memcpy(dst, src, n)`: `dst[n]` written, `src[n]` read, disjoint. -/
abbrev MemcpyF (t : MachineData) : Mem 64 → Prop :=
  Blocks [(arg0 t, (arg2 t).toNat), (arg1 t, (arg2 t).toNat)]

abbrev MemcpySpec (need : Nat) : Prop := LeafSpec "memcpy" need MemcpyF (fun _ => True)

/-- Assumed: `memset(dst, c, n)`: `dst[n]` written, nothing else. -/
abbrev MemsetF (t : MachineData) : Mem 64 → Prop :=
  Blocks [(arg0 t, (arg2 t).toNat)]

abbrev MemsetSpec (need : Nat) : Prop := LeafSpec "memset" need MemsetF (fun _ => True)

/-- The code addresses `sbr_qmf_synthesis` calls through pointers. -/
structure QmfFns where
  negOdd64 : Int64
  deintNeg : Int64
  deintBfly : Int64
  tx : Int64
  fmul : Int64
  fmulAdd : Int64

/-- A code address `f` stored in the 8 bytes at `a` (a function-pointer slot). -/
abbrev FnCell (a : BitVec 64) (f : Int64) : Mem 64 → Prop := Int.toBytes 8 f.toBitVec.toInt =@ a

/-- A 4-byte `int` field holding `v`. -/
abbrev cell4 (a : BitVec 64) (v : BitVec 32) : Mem 64 → Prop := Int.toBytes 4 v.toInt =@ a

/-- The code addresses `sbr_hf_assemble` calls through `sbr->dsp`:
`hf_g_filt` and the four `hf_apply_noise[k]`. -/
structure HfFns where
  gfilt : Int64
  noise0 : Int64
  noise1 : Int64
  noise2 : Int64
  noise3 : Int64

/-- The signed little-endian 32-bit integer at byte offset `o` of `bs`. -/
abbrev i32 (bs : List UInt8) (o : Nat) : Int :=
  (BitVec.ofNat 32 (Nat.ofBytes ((bs.drop o).take 4))).toInt

/-- The signed byte at offset `o` of `bs`. -/
abbrev i8 (bs : List UInt8) (o : Nat) : Int :=
  (BitVec.ofNat 8 (bs.getD o 0).toNat).toInt

/-- The logical variables of `ff_ps_apply`: the caller's memory, the 764 bytes
of `PSCommonContext` (`ps->common`, at `ps + 0`) and the 68 bytes
`opd_hist[34] ++ ipd_hist[34]` (`int8_t`, at `ps + 133968`). -/
structure PsArgs where
  R : Mem 64 → Prop
  psc : List UInt8
  psh : List UInt8

/-- The PS state invariant (`libavcodec/aacps.h`, `aacps_common.c` = PC,
`aacps.c` = P). Offsets in `c = ps->common`: `start` 0, `enable_iid` 4,
`iid_quant` 8, `nr_iid_par` 12, `num_env_old` 40, `num_env` 44,
`border_position[6]` 52, `iid_par`/`icc_par`/`ipd_par`/`opd_par` (`[5][34]`
`int8_t`) 76/246/416/586, `is34bands` 756; in `h`: `opd_hist` 0, `ipd_hist` 34.
* W1 `is34bands ∈ {0,1}` (PC:263); W2 `0 ≤ num_env, num_env_old ≤ 5`
  (PC:170-171, 256); W3 `iid_quant ∈ {0,1}` (PC:153);
* W4 `icc_par ∈ [0,7]` (PC:108, 202, 233, 285); W5 `ipd_par, opd_par ∈ [0,7]`
  (PC:86/95/109, 236-237, 268-269, 286-287); W6 `opd_hist, ipd_hist ∈ [0,63]`
  (P:607/625, 649-650), all entries, unconditionally;
* when `start ≠ 0` (the PS data of the frame was parsed successfully):
  W7 `1 ≤ num_env` (PC:224-257); W8 `border_position[0] = -1`, nondecreasing
  up to `num_env`, `border_position[num_env] = 31` (PC:173-184, 224/257);
  W9 `enable_iid → nr_iid_par ∈ {10,20,34}` (PC:147, 152); W10 the live
  `iid_par` entries within `±(7 + 8·iid_quant)` (PC:107, 187-193, 241-246). -/
def PsWF (c h : List UInt8) : Prop :=
  c.length = 764 ∧ h.length = 68
  ∧ (i32 c 756 = 0 ∨ i32 c 756 = 1)
  ∧ (0 ≤ i32 c 44 ∧ i32 c 44 ≤ 5) ∧ (0 ≤ i32 c 40 ∧ i32 c 40 ≤ 5)
  ∧ (i32 c 8 = 0 ∨ i32 c 8 = 1)
  ∧ (∀ e < 5, ∀ b < 34, 0 ≤ i8 c (246 + 34 * e + b) ∧ i8 c (246 + 34 * e + b) ≤ 7)
  ∧ (∀ e < 5, ∀ b < 34, 0 ≤ i8 c (416 + 34 * e + b) ∧ i8 c (416 + 34 * e + b) ≤ 7
      ∧ 0 ≤ i8 c (586 + 34 * e + b) ∧ i8 c (586 + 34 * e + b) ≤ 7)
  ∧ (∀ b < 34, 0 ≤ i8 h b ∧ i8 h b ≤ 63 ∧ 0 ≤ i8 h (34 + b) ∧ i8 h (34 + b) ≤ 63)
  ∧ (i32 c 0 ≠ 0 →
      1 ≤ i32 c 44
      ∧ i32 c 52 = -1
      ∧ (∀ e : Nat, (e : Int) < i32 c 44 → i32 c (52 + 4 * e) ≤ i32 c (52 + 4 * (e + 1)))
      ∧ i32 c (52 + 4 * (i32 c 44).toNat) = 31
      ∧ (i32 c 4 ≠ 0 → i32 c 12 = 10 ∨ i32 c 12 = 20 ∨ i32 c 12 = 34)
      ∧ (∀ e : Nat, (e : Int) < i32 c 44 → ∀ b : Nat, b < 34 →
          (i32 c 4 = 0 ∨ (b : Int) < i32 c 12) →
          -(7 + 8 * i32 c 8) ≤ i8 c (76 + 34 * e + b)
            ∧ i8 c (76 + 34 * e + b) ≤ 7 + 8 * i32 c 8))

/-- The footprint of `ff_ps_apply(ps, L, R, top)` (`libavcodec/aacps.c`): the
whole `PSContext` (0x20be0 bytes at `ps`) with `ps->common` (764 bytes) and
`opd_hist`/`ipd_hist` (68 bytes at `ps + 133968`) as value cells, and the rest
raw — owning the whole struct over-approximates the writes of `ff_ps_apply`,
which stay in `[768, 134036)`; `L`, `R` (`[2][38][64]` floats, 0x4c00 bytes
each) read and written; and `PsTab`, the static tables of the PS decoder
(`g1_Q2`, `pd_re/im_smooth`, `HA`, `HB`, `f20_0_8`, `f34_*`,
`Q_fract_allpass`, `phi_fract`, `ff_k_to_i_20/34`, the decorrelation
coefficients, `ps_p1m1p1m1`, the `NR_*` constants), given back. -/
abbrev PsApplyF (PsTab : Mem 64 → Prop) (x : PsArgs) (t : MachineData) : Mem 64 → Prop :=
  x.psc =@ arg0 t ⋆ (4 ?@ (arg0 t + 764#64) ⋆ (133200 ?@ (arg0 t + 768#64)
    ⋆ (x.psh =@ (arg0 t + 133968#64) ⋆ (76 ?@ (arg0 t + 134036#64)
    ⋆ (Blocks [(arg1 t, 0x4c00), (arg2 t, 0x4c00)] ⋆ PsTab)))))

/-- The side conditions: `top` (an `int`) at most 64 (`aacps.c` memsets
`NR_BANDS - (top + NR_BANDS - 64)` entries; at the call `top = kx[1] + m[1]`,
`aacsbr_template.c:568`), the PS data parsed (`ps->common.start ≠ 0`, the
caller's test, `aacsbr_template.c:1760`), the invariant `PsWF`, and `ps`, `L`,
`R` 16-aligned. -/
abbrev PsApplyC (x : PsArgs) (t : MachineData) : Prop :=
  (arg3 t).toNat % 2 ^ 32 ≤ 64 ∧ i32 x.psc 0 ≠ 0 ∧ PsWF x.psc x.psh
    ∧ isAligned 16 (arg0 t) = true ∧ isAligned 16 (arg1 t) = true
    ∧ isAligned 16 (arg2 t) = true

/-- On return `ps->common` is unchanged and the phase histories are some values
still within W6. -/
def PsApplyFPost (PsTab : Mem 64 → Prop) (x : PsArgs) (t : MachineData) : Mem 64 → Prop :=
  fun m => ∃ h' : List UInt8, h'.length = 68
    ∧ (∀ b < 34, 0 ≤ i8 h' b ∧ i8 h' b ≤ 63 ∧ 0 ≤ i8 h' (34 + b) ∧ i8 h' (34 + b) ≤ 63)
    ∧ PsApplyF PsTab { x with psh := h' } t m

abbrev PsApplyPre (need : Nat) (PsTab : Mem 64 → Prop) (x : PsArgs) (ra : Int64)
    (t : MachineData) : Prop :=
  CallPre need (PsApplyF PsTab x t ⋆ x.R) ra t ∧ PsApplyC x t

abbrev PsApplyPost (need : Nat) (PsTab : Mem 64 → Prop) (x : PsArgs) (ra : Int64)
    (t s : MachineData) : Prop :=
  CallPost need (PsApplyFPost PsTab x t ⋆ x.R) ra t s

/-- Assumed (trusted): `ff_ps_apply` is memory-safe given `PsWF`, `top ≤ 64`
and 16-alignment, and preserves W6. Ownership of the whole `PSContext`
over-approximates its writes (`[768, 134036)`). Proving it is a possible M6. -/
abbrev PsApplySpec (PsTab : Mem 64 → Prop) (need : Nat) : Prop :=
  cenv.ProcSpec (entry "ff_ps_apply") (PsApplyPre need PsTab) (PsApplyPost need PsTab)

/-- Assumed: `av_log(avcl, level, fmt, ...)` (`libavutil/log.h`) touches only `Ext`
(the logging state, the context it reads), given back. -/
abbrev AvLogSpec (Ext : Mem 64 → Prop) (need : Nat) : Prop :=
  LeafSpec "av_log" need (fun _ => Ext) (fun _ => True)

/-- The double `1E20` (the constant `LCPI14_4` of `aacsbr.o`). -/
def dbl1E20 : BitVec 64 := 0x4415AF1D78B58C40#64

end Kraken.Examples.Sbr

end

/-! ## §2. `ff_aac_sbr_apply`: frames and specification

Lemmas about these: `ApplySpec.lean`. -/

section

open Kraken Kraken.X64.Parser Std.WP MachineWP Kraken.SysV Mem
namespace Kraken.Examples.Sbr.Apply

/-- The values of one `SBRData` (`sbr->data[ch]`, `libavcodec/sbr.h`) the code reads
and depends on. Byte arrays are lists of bytes; `u8 bs i` reads one. -/
structure DV where
  /-- `bs_num_env` (`int`, +0x8). -/
  nenv : Nat
  /-- `bs_freq_res[0..8]` (+0xc). -/
  freqRes : List UInt8
  /-- `bs_num_noise` (`int`, +0x18). -/
  nnoise : Nat
  /-- `bs_invf_mode[2][5]` (+0x27). -/
  invf : List UInt8
  /-- `synthesis_filterbank_samples_offset` (`int`, +0x3900). -/
  vOff : BitVec 32
  /-- `Ypos` (`int`, +0x7920). -/
  ypos : Nat
  /-- `t_env[0..8]`, `t_env_num_env_old` (+0x15a9c, 10 bytes). -/
  te : List UInt8
  /-- `t_q[0..2]` (+0x15aa6). -/
  tq : List UInt8
  /-- `f_indexnoise`, `f_indexsine` (+0x15aac, 8 bytes). -/
  idx : BitVec 64

/-- The function addresses reachable from `ff_aac_sbr_apply`: the fourteen
`sbr->dsp` slots (`SBRDSPContext`, `libavcodec/sbrdsp.h`), the four `sbr->c` slots,
`sbr->mdct_ana_fn`, and the `AVFloatDSPContext` slots used here and by
`sbr_qmf_synthesis` (with `mdct_fn`, in `qfs`). -/
structure Fns where
  sum64x5 : Int64
  sumSquare : Int64
  preShuffle : Int64
  postShuffle : Int64
  autocorr : Int64
  hfGen : Int64
  hfs : HfFns
  qfs : QmfFns
  lfGen : Int64
  hfAsm : Int64
  xGen : Int64
  hfInv : Int64
  mdctAna : Int64
  fmulRev : Int64

/-- The parameters of the specification: the function addresses, the owned state of
an `av_tx` context, the shared static tables of `av_tx` (`TxTab`) and of the PS
decoder (`PsTab`), and the state outside the footprint that `av_log` may read. -/
structure Env where
  fs : Fns
  Ctx : BitVec 64 → Mem 64 → Prop
  TxTab : Mem 64 → Prop
  PsTab : Mem 64 → Prop
  Ext : Mem 64 → Prop

/-- The logical variables: the caller's memory `R` and the decoder-state values. -/
structure Args where
  R : Mem 64 → Prop
  /-- `sbr->start`, `ready_for_dequant`, `id_aac`, `reset`, `bs_smoothing_mode`,
  `kx_and_m_pushed`. -/
  start : BitVec 32
  ready : BitVec 32
  idAac : BitVec 32
  reset : BitVec 32
  smooth : BitVec 32
  pushed : BitVec 32
  /-- `sbr->k[0]`, `kx[0..1]`, `m[0..1]`. -/
  k0 : Nat
  kx0 : Nat
  kx1 : Nat
  m0 : Nat
  m1 : Nat
  /-- `bs_limiter_gains`, `bs_interpol_freq`, `bs_coupling`. -/
  limGains : Nat
  interpol : BitVec 32
  coupling : BitVec 32
  /-- `n[0..1]`, `n_q`, `n_lim`, `num_patches`. -/
  n0 : Nat
  n1 : Nat
  nq : Nat
  nlim : Nat
  npatch : Nat
  /-- `patch_num_subbands[6]`, `patch_start_subband[6]` (bytes). -/
  pnum : List UInt8
  pstart : List UInt8
  /-- `f_tablelow[25]`, `f_tablehigh[49]`, `f_tablenoise[6]`, `f_tablelim[30]`
  (`uint16_t`, as bytes). -/
  ftLow : List UInt8
  ftHigh : List UInt8
  ftNoise : List UInt8
  ftLim : List UInt8
  /-- The two channels' `SBRData` values. -/
  d0 : DV
  d1 : DV
  /-- `sbr->sample_rate`. -/
  sampleRate : BitVec 32
  /-- `ac->avctx`, `ac->fdsp`, the extension sample rate and the PS flag. -/
  avctx : BitVec 64
  fdsp : BitVec 64
  extRate : BitVec 32
  ps : BitVec 32
  /-- The `av_tx` contexts `sbr->mdct_ana`, `sbr->mdct`. -/
  anaCtx : BitVec 64
  synCtx : BitVec 64
  /-- `sbr->ps.common` (`PSCommonContext`, 764 bytes at `sbr + 0x2b600`) and
  `sbr->ps.opd_hist ++ ipd_hist` (68 bytes at `sbr + 0x4c150`), see `PsWF`. -/
  psc : List UInt8
  psh : List UInt8
  /-- `sbr->spectrum_params` (`SpectrumParameters`, 6 bytes at `sbr + 0x1c`): bytes 0..3 and
  4..5, the two stores of `sbr_turnoff`'s `memset(&sbr->spectrum_params, -1, 6)`. Byte 0 is
  `bs_start_freq`. -/
  spLo : BitVec 32
  spHi : BitVec 16

/-- The frequency tables `ff_aac_sbr_apply` does not modify: `k[0]`, `n[0..1]`, `n_q`,
`n_lim`, `num_patches`, `patch_num_subbands`, `patch_start_subband`,
`f_tablelow/high/noise/lim` (written only by `sbr_make_f_master`, `sbr_make_f_derived`,
`sbr_make_f_tablelim` and `sbr_hf_calc_npatches`, from the parser's `sbr_reset` and header).
And `start` with `spectrum_params` are kept, or cleared together: the only writes of
`sbr->start` and `sbr->spectrum_params` reachable from apply are `sbr_turnoff`'s `start = 0`
and `memset(&sbr->spectrum_params, -1, …)` (`aacsbr_template.c`:58-68). -/
def Args.KeepT (x y : Args) : Prop :=
  y.k0 = x.k0 ∧ y.n0 = x.n0 ∧ y.n1 = x.n1 ∧ y.nq = x.nq ∧ y.nlim = x.nlim
  ∧ y.npatch = x.npatch ∧ y.pnum = x.pnum ∧ y.pstart = x.pstart ∧ y.ftLow = x.ftLow
  ∧ y.ftHigh = x.ftHigh ∧ y.ftNoise = x.ftNoise ∧ y.ftLim = x.ftLim
  ∧ ((y.start = 0 ∧ y.spLo = BitVec.allOnes 32 ∧ y.spHi = BitVec.allOnes 16)
      ∨ (y.start = x.start ∧ y.spLo = x.spLo ∧ y.spHi = x.spHi))

/-- The decoder state `ff_aac_sbr_apply` does not modify (INV-D5): both channels'
`bs_num_env`, `t_env`/`t_env_num_env_old`, `bs_freq_res`, `t_q`, and the PS common
context (only the grid parser, `read_sbr_grid`, and the PS parser write them), and the
frequency tables with `start` kept or cleared (`KeepT`). -/
abbrev Args.KeepD (x y : Args) : Prop :=
  y.d0.nenv = x.d0.nenv ∧ y.d0.te = x.d0.te ∧ y.d1.nenv = x.d1.nenv ∧ y.d1.te = x.d1.te
  ∧ y.d0.freqRes = x.d0.freqRes ∧ y.d1.freqRes = x.d1.freqRes
  ∧ y.d0.tq = x.d0.tq ∧ y.d1.tq = x.d1.tq ∧ y.psc = x.psc ∧ x.KeepT y

/-- `sbr_turnoff`'s effect on the scalar fields: `start = ready = 0`, `kx[1] = 32`,
`m[1] = 0` (the other fields it writes are raw in the footprint). -/
abbrev Args.turnoff (x : Args) : Args := { x with start := 0, ready := 0, kx1 := 32, m1 := 0 }

/-- Byte `i` of a byte array. -/
abbrev u8 (bs : List UInt8) (i : Nat) : Nat := (bs.getD i 0).toNat

/-- Element `i` of a little-endian `uint16_t` array. -/
abbrev u16 (bs : List UInt8) (i : Nat) : Nat := u8 bs (2 * i) + 256 * u8 bs (2 * i + 1)

variable [CodeEnv]

/-- `sbr` (the element's `SpectralBandReplication`, at `che + 0x28920`). -/
abbrev sbrA (t : MachineData) : BitVec 64 := arg1 t + 0x28920#64

/-- `&sbr->data[ch]` (`SBRData` is 0x15ac0 bytes at `sbr + 0x80`). -/
abbrev dA (t : MachineData) (ch : Nat) : BitVec 64 :=
  sbrA t + BitVec.ofNat 64 (0x80 + 0x15ac0 * ch)

/-- `downsampled` (`ac->oc[1].m4ac.ext_sample_rate < sbr->sample_rate`): 0 or 1. -/
abbrev dsN (x : Args) : Nat := if x.extRate.toInt < x.sampleRate.toInt then 1 else 0

abbrev c8 (a v : BitVec 64) : Mem 64 → Prop := Int.toBytes 8 v.toInt =@ a

abbrev c4 (a : BitVec 64) (v : Nat) : Mem 64 → Prop := Int.toBytes 4 (v : Int) =@ a

/-- The scalar fields of `*sbr`. -/
def ScW (x : Args) (t : MachineData) : Mem 64 → Prop :=
  let s := sbrA t
  cell4 s x.sampleRate ⋆ (cell4 (s + 0x4#64) x.start ⋆ (cell4 (s + 0x8#64) x.ready
    ⋆ (cell4 (s + 0xc#64) x.idAac ⋆ (4 ?@ (s + 0x10#64) ⋆ (cell4 (s + 0x18#64) x.reset
    ⋆ (cell4 (s + 0x1c#64) x.spLo ⋆ (Int.toBytes 2 x.spHi.toInt =@ (s + 0x20#64)
    ⋆ (c4 (s + 0x30#64) x.limGains ⋆ (cell4 (s + 0x34#64) x.interpol
    ⋆ (cell4 (s + 0x38#64) x.smooth ⋆ (cell4 (s + 0x3c#64) x.coupling
    ⋆ (c4 (s + 0x40#64) x.k0 ⋆ (c4 (s + 0x54#64) x.kx0 ⋆ (c4 (s + 0x58#64) x.kx1
    ⋆ (c4 (s + 0x5c#64) x.m0 ⋆ (c4 (s + 0x60#64) x.m1
    ⋆ cell4 (s + 0x64#64) x.pushed))))))))))))))))

/-- The frequency tables and their sizes, and the patches. -/
def TabW (x : Args) (t : MachineData) : Mem 64 → Prop :=
  let s := sbrA t
  c4 (s + 0x4c1e0#64) x.n0 ⋆ (c4 (s + 0x4c1e4#64) x.n1 ⋆ (c4 (s + 0x4c1e8#64) x.nq
    ⋆ (c4 (s + 0x4c1ec#64) x.nlim ⋆ (x.ftLow =@ (s + 0x4c252#64)
    ⋆ (x.ftHigh =@ (s + 0x4c284#64) ⋆ (x.ftNoise =@ (s + 0x4c2e6#64)
    ⋆ (x.ftLim =@ (s + 0x4c2f2#64) ⋆ (c4 (s + 0x4c330#64) x.npatch
    ⋆ (x.pnum =@ (s + 0x4c334#64) ⋆ x.pstart =@ (s + 0x4c33a#64))))))))))

/-- The scalar fields of `sbr->data[ch]` with values `v`. -/
def DScW (v : DV) (t : MachineData) (ch : Nat) : Mem 64 → Prop :=
  let d := dA t ch
  4 ?@ (d + 0x4#64) ⋆ (c4 (d + 0x8#64) v.nenv ⋆ (v.freqRes =@ (d + 0xc#64)
    ⋆ (c4 (d + 0x18#64) v.nnoise ⋆ (v.invf =@ (d + 0x27#64) ⋆ (48 ?@ (d + 0x31#64)
    ⋆ (4 ?@ (d + 0x64#64) ⋆ (cell4 (d + 0x3900#64) v.vOff ⋆ (8 ?@ (d + 0x3904#64)
    ⋆ (c4 (d + 0x7920#64) v.ypos ⋆ (v.te =@ (d + 0x15a9c#64) ⋆ (v.tq =@ (d + 0x15aa6#64)
    ⋆ Int.toBytes 8 v.idx.toInt =@ (d + 0x15aac#64))))))))))))

/-- The raw arrays of `sbr->data[ch]` (`d = &sbr->data[ch]`):
`synthesis_filterbank_samples` (9216 bytes at `d + 0x80`),
`analysis_filterbank_samples` (5248 at `d + 0x2480`; its first 2048 bytes are part of
the larger synthesis window, see `qmfVSize`), `bw_array[5]`, `W[2][32][32][2]`,
then `Y[2][38][64][2]` together with the first 24 bytes of `g_temp` (38936 bytes at
`d + 0x7930`, see `HfData`), the rest of `g_temp` (8040), `q_temp[42][48]`
(8064), `s_indexmapped`, the envelope and noise factors. The scalar gaps:
`bs_add_harmonic_flag` (`d + 0x4`), `bs_add_harmonic` (`d + 0x31`), `bs_amp_res`
(`d + 0x64`), `e_a` (`d + 0x3904`), all in `DScW`. Per-object views:
`gtemp_rejoin` (`Y[0]`, `Y[1]`, `g_temp ++ q_temp`), `a3_overread_carve`. -/
def DArrW (t : MachineData) (ch : Nat) : Mem 64 → Prop :=
  let d := dA t ch
  Blocks [(d + 0x80#64, 9216), (d + 0x2480#64, 5248), (d + 0x390c#64, 20),
    (d + 0x3920#64, 16384), (d + 0x7930#64, 38936), (d + 0x11148#64, 8040),
    (d + 0x130b0#64, 8064),
    (d + 0x15030#64, 432), (d + 0x151e0#64, 432), (d + 0x15390#64, 1728),
    (d + 0x15a50#64, 15), (d + 0x15a60#64, 60)]

/-- The work arrays of `*sbr` (`s = sbr`): `X_low`, `X_high`, `X[0]`, `X[1]` (0x4c00
bytes each), `alpha0/1`, `e_origmapped`, `q_mapped`, `s_mapped`, `e_curr`, `q_m`,
`s_m`, `gain` (1536 bytes each), `qmf_filter_scratch`. The PS state at
`s + 0x2b600` is `PsW`. ScW gap name: `usac`/`inter_tes` (`s + 0x10`, 4 bytes). -/
def ArrW (t : MachineData) : Mem 64 → Prop :=
  let s := sbrA t
  Blocks [(s + 0x4c340#64, 10240), (s + 0x4eb40#64, 20480),
    (s + 0x53b40#64, 0x4c00), (s + 0x58740#64, 0x4c00), (s + 0x5d340#64, 512),
    (s + 0x5d540#64, 512), (s + 0x5d740#64, 1536), (s + 0x5dd40#64, 1536),
    (s + 0x5e340#64, 384), (s + 0x5e4c0#64, 1536), (s + 0x5eac0#64, 1536),
    (s + 0x5f0c0#64, 1536), (s + 0x5f6c0#64, 1536), (s + 0x5fcc0#64, 1280)]

/-- `sbr->ps` (`PSContext`, 0x20be0 bytes at `sbr + 0x2b600`): `ps->common` (764
bytes, values `x.psc`), padding, the raw middle, `opd_hist ++ ipd_hist` (68 bytes,
values `x.psh`), the rest (with `dsp`). Owning the whole struct over-approximates the
writes of `ff_ps_apply` (`[768, 134036)`). -/
def PsW (x : Args) (t : MachineData) : Mem 64 → Prop :=
  let p := sbrA t + 0x2b600#64
  x.psc =@ p ⋆ (4 ?@ (p + 764#64) ⋆ (133200 ?@ (p + 768#64)
    ⋆ (x.psh =@ (p + 133968#64) ⋆ 76 ?@ (p + 134036#64))))

/-- The `sbr->dsp` slots. -/
def DspW (e : Env) (t : MachineData) : Mem 64 → Prop :=
  let p := sbrA t + 0x601e0#64
  FnCell p e.fs.sum64x5 ⋆ (FnCell (p + 0x8#64) e.fs.sumSquare
    ⋆ (FnCell (p + 0x10#64) e.fs.qfs.negOdd64 ⋆ (FnCell (p + 0x18#64) e.fs.preShuffle
    ⋆ (FnCell (p + 0x20#64) e.fs.postShuffle ⋆ (FnCell (p + 0x28#64) e.fs.qfs.deintNeg
    ⋆ (FnCell (p + 0x30#64) e.fs.qfs.deintBfly ⋆ (FnCell (p + 0x38#64) e.fs.autocorr
    ⋆ (FnCell (p + 0x40#64) e.fs.hfGen ⋆ (FnCell (p + 0x48#64) e.fs.hfs.gfilt
    ⋆ (FnCell (p + 0x50#64) e.fs.hfs.noise0 ⋆ (FnCell (p + 0x58#64) e.fs.hfs.noise1
    ⋆ (FnCell (p + 0x60#64) e.fs.hfs.noise2 ⋆ FnCell (p + 0x68#64) e.fs.hfs.noise3))))))))))))

/-- The other function-pointer cells (`sbr->c`, the `av_tx` fields, `*ac->fdsp`), the
`av_tx` contexts, the `av_tx` tables `TxTab` and the PS tables `PsTab` (all disjoint
by `⋆`), and `Ext`. -/
def FnW (e : Env) (x : Args) (t : MachineData) : Mem 64 → Prop :=
  let s := sbrA t
  Int.toBytes 8 x.anaCtx.toInt =@ (s + 0x601c0#64) ⋆ (FnCell (s + 0x601c8#64) e.fs.mdctAna
    ⋆ (Int.toBytes 8 x.synCtx.toInt =@ (s + 0x601d0#64) ⋆ (FnCell (s + 0x601d8#64) e.fs.qfs.tx
    ⋆ (FnCell (s + 0x60250#64) e.fs.lfGen ⋆ (FnCell (s + 0x60258#64) e.fs.hfAsm
    ⋆ (FnCell (s + 0x60260#64) e.fs.xGen ⋆ (FnCell (s + 0x60268#64) e.fs.hfInv
    ⋆ (FnCell x.fdsp e.fs.qfs.fmul ⋆ (FnCell (x.fdsp + 0x30#64) e.fs.qfs.fmulAdd
    ⋆ (FnCell (x.fdsp + 0x38#64) e.fs.fmulRev ⋆ (e.Ctx x.anaCtx ⋆ (e.Ctx x.synCtx
    ⋆ (e.TxTab ⋆ (e.PsTab ⋆ e.Ext))))))))))))))

/-- The fields of `*ac`. -/
def AcW (x : Args) (t : MachineData) : Mem 64 → Prop :=
  Int.toBytes 8 x.avctx.toInt =@ (arg0 t + 0x8#64)
    ⋆ (Int.toBytes 8 x.fdsp.toInt =@ (arg0 t + 0x2550#64)
    ⋆ (cell4 (arg0 t + 0x57f4#64) x.extRate ⋆ cell4 (arg0 t + 0x5800#64) x.ps))

/-- The read-only constants of the code (`.rodata.cst*`, `.lrodata` of `aacsbr.o`); the
value of `LCPI14_4` (`1E20`, compared against by the dequantisation assert, see
`DequantFloatModel`) is known; `sbr_hf_assemble`'s (`HfData`: `ff_sbr_noise_table`, `ps_noise*`,
`.LCPI17_*`, the mask `.LCPI17_11 = {0x1ff, 3, 0, 0}` with its contents); and
`pd_reverse` of `float_dsp.o`, the mask `vector_fmul_reverse` reads (note F1,
`VectorFmulRevF`). -/
def CstW : Mem 64 → Prop :=
  Blocks [(lab "LCPI14_0", 4), (lab "LCPI14_5", 4), (lab "LCPI14_6", 4), (lab "LCPI14_9", 4),
    (lab "LCPI14_10", 4), (lab "LCPI14_11", 4), (lab "LCPI14_12", 4), (lab "LCPI14_13", 4),
    (lab "LCPI14_14", 4), (lab "LCPI14_15", 4), (lab "LCPI14_16", 4), (lab "LCPI14_17", 4),
    (lab "LCPI14_3", 8), (lab "LCPI14_1", 16), (lab "LCPI14_2", 16),
    (lab "LCPI14_8", 16), (lab "exp2_tab", 16), (lab "bw_tab", 16), (lab "limgain", 16),
    (lab "sbr_qmf_window_ds", 1280), (lab "ff_ps_neg", 16), (lab "ps_mask", 16),
    (lab "LCPI19_0", 4), (lab "LCPI19_1", 4), (lab "LCPI19_2", 16), (lab "ps_mask3", 16),
    (lab "sbr_qmf_window_us", 2560), (lab "LCPI15_1", 4), (lab "ps_mask2", 16),
    (lab "ff_sbr_noise_table", 4160), (lab "ps_noise0", 16), (lab "ps_noise13", 48),
    (lab "ps_noise2", 16),
    (lab "LCPI17_6", 4), (lab "LCPI17_7", 4), (lab "LCPI17_8", 4), (lab "LCPI17_9", 4),
    (lab "LCPI17_10", 4), (lab "LCPI17_12", 4), (lab "pd_reverse", 32)]
    ⋆ (Int.toBytes 8 dbl1E20.toInt =@ lab "LCPI14_4"
      ⋆ Int.toBytes 16 0x3000001ff =@ lab "LCPI17_11")

/-- The output buffers `L`, `R` (`8192 >>> downsampled` bytes each). -/
def OutW (x : Args) (t : MachineData) : Mem 64 → Prop :=
  Blocks [(arg3 t, 8192 >>> dsN x), (arg4 t, 8192 >>> dsN x)]

/-- The whole footprint. -/
abbrev ApplyF (e : Env) (x : Args) (t : MachineData) : Mem 64 → Prop :=
  ScW x t ⋆ (TabW x t ⋆ (DScW x.d0 t 0 ⋆ (DScW x.d1 t 1 ⋆ (DArrW t 0 ⋆ (DArrW t 1
    ⋆ (ArrW t ⋆ (PsW x t ⋆ (DspW e t ⋆ (FnW e x t ⋆ (AcW x t ⋆ (CstW ⋆ OutW x t)))))))))))

/-- What `ff_aac_sbr_apply` needs of one channel's `SBRData` (kinds as in `Spec.lean`'s
`SbrWF` section: all invariants of the decoder unless marked). `live` says the channel's
grid is the output of a successful `read_sbr_grid` (`SbrWF` passes `start ≠ 0` for
channel 0 and `start ≠ 0 ∧ id_aac = CPE` for channel 1): `read_sbr_grid` stores the
grid before its checks (`aacsbr_template.c:662-735` vs. `740-752`), so after a rejected
grid `t_env` can be non-monotone or above 19, and the `t_env` clauses hold only for
live data. Note A1: the borders are bounded by `numTimeSlots + 3 = 19`, not 16
(`aacsbr_template.c:651, 756-772, 788`). `synthesis_filterbank_samples_offset ≤ 1664`
(`aacsbr_template.c:88-89, 1427-1432`); see `qmfVSize`. -/
def DWF (live : Prop) (v : DV) : Prop :=
  v.freqRes.length = 9 ∧ v.invf.length = 10 ∧ v.te.length = 10 ∧ v.tq.length = 3
  ∧ v.nenv ≤ 8
  ∧ (∀ e, e ≤ v.nenv → u8 v.freqRes e ≤ 1)   -- bs_freq_res[1..bs_num_env] is read
  ∧ v.nnoise ≤ 2 ∧ (∀ i, i < 5 → u8 v.invf i ≤ 3)
  ∧ v.ypos ≤ 1
  ∧ u8 v.te 9 ≤ 19
  ∧ (∀ q, q ≤ v.nnoise → u8 v.tq q ≤ 19)
  ∧ v.idx.toNat % 2 ^ 32 ≤ 515 ∧ v.idx.toNat / 2 ^ 32 < 4
  ∧ v.vOff.toInt ≤ 1664 ∧ v.vOff.toNat % 8 = 0
  ∧ (live → 1 ≤ v.nenv ∧ (∀ e, e ≤ v.nenv → u8 v.te e ≤ 19)
      ∧ (∀ e, e < v.nenv → u8 v.te e < u8 v.te (e + 1)))

/-- The frequency tables of a started decoder: each table inside the high band
`[kx[1], kx[1] + m[1]]`, nondecreasing; the patches inside `X_low`/`X_high`.

The last four conjuncts are the M4-F1 facts. They hold because, while `start == 1`, every
table field is the output of the last successful `sbr_make_f_master` + `sbr_make_f_derived`:
both are called only from `sbr_reset`, which calls `sbr_turnoff` (`start = 0`) on any
failure; `start = 1` is set only by a header, and the next header is forced to reset; and
`sbr_turnoff` does not clear the tables, hence the `start ≠ 0` guard in `SbrWF`.
Code citations are to libavcodec/aacsbr_template.c (FFmpeg n8.1):
* F1 `f_tablenoise[0] = kx[1]`: `kx[1] = f_tablehigh[0]` (l.565),
  `f_tablelow[0] = f_tablehigh[0]` (l.578), `f_tablenoise[0] = f_tablelow[0]` (l.606).
* F2 `f_tablenoise[n_q] = kx[1] + m[1]`: `kx[1] + m[1] = f_tablehigh[n[1]]` (l.564-565). The
  last noise border step divides by 1 (l.609), so it is `f_tablelow[n[0]]`, which is
  `f_tablehigh[n[1]]` (l.560, l.579-581).
* F3 `1 ≤ n_q` (`FFMAX(1, …)`, l.593-596; `n_q ≤ 5` is checked at l.600-604).
* F5 `Σ patch_num_subbands ≤ m[1]`: `usb` starts at `kx[1]` (l.498), each counted patch adds
  `sb - usb` and sets `usb = sb` (l.530-536), and `sb ≤ f_master[n_master] = kx[1] + m[1]`
  (l.504-506, 516-517, 541, 562); l.546 only drops the last patch.
With F2, F5 and the nondecreasing `f_tablenoise` (F4, above), `sbr_hf_gen`'s noise band search
(l.1499-1513) ends with `g ≤ n_q - 1 ≤ 4`, so `bw_array[g]` stays in `bw_array[5]`. -/
def TabWF (x : Args) : Prop :=
  x.ftLow.length = 50 ∧ x.ftHigh.length = 98 ∧ x.ftNoise.length = 12 ∧ x.ftLim.length = 60
  ∧ x.pnum.length = 6 ∧ x.pstart.length = 6
  ∧ 1 ≤ x.m1
  ∧ (∀ i, i ≤ x.n1 → x.kx1 ≤ u16 x.ftHigh i ∧ u16 x.ftHigh i ≤ x.kx1 + x.m1)
  ∧ (∀ i, i ≤ x.n0 → x.kx1 ≤ u16 x.ftLow i ∧ u16 x.ftLow i ≤ x.kx1 + x.m1)
  ∧ (∀ i, i ≤ x.nq → x.kx1 ≤ u16 x.ftNoise i ∧ u16 x.ftNoise i ≤ x.kx1 + x.m1)
  ∧ (∀ i, i ≤ x.nlim → x.kx1 ≤ u16 x.ftLim i ∧ u16 x.ftLim i ≤ x.kx1 + x.m1)
  ∧ (∀ i, i < x.n1 → u16 x.ftHigh i < u16 x.ftHigh (i + 1))   -- f_master: vDk > 0
  ∧ (∀ i, i < x.n0 → u16 x.ftLow i ≤ u16 x.ftLow (i + 1))
  ∧ (∀ i, i < x.nq → u16 x.ftNoise i ≤ u16 x.ftNoise (i + 1))
  ∧ (∀ i, i < x.nlim → u16 x.ftLim i ≤ u16 x.ftLim (i + 1))
  ∧ (∀ i, i < x.npatch → u8 x.pstart i + u8 x.pnum i ≤ 32)
  ∧ x.kx1 + (List.range x.npatch).foldl (fun a i => a + u8 x.pnum i) 0 ≤ 64
  ∧ u16 x.ftNoise 0 = x.kx1                                                   -- F1
  ∧ u16 x.ftNoise x.nq = x.kx1 + x.m1                                         -- F2
  ∧ 1 ≤ x.nq                                                                  -- F3
  ∧ (List.range x.npatch).foldl (fun a i => a + u8 x.pnum i) 0 ≤ x.m1         -- F5

/-- `SbrWF`: the decoder-state invariant `ff_aac_sbr_apply` assumes (M1–M3 clauses
of `Spec.lean` plus the bounds the build's checks and `sbr_mapping`'s loops need). -/
def SbrWF (x : Args) : Prop :=
  x.kx0 ≤ 32 ∧ x.kx1 ≤ 32 ∧ x.kx0 + x.m0 ≤ 64 ∧ x.kx1 + x.m1 ≤ 64 ∧ x.m1 ≤ 48 ∧ x.k0 ≤ 32
  ∧ x.limGains ≤ 3 ∧ x.n0 ≤ 24 ∧ x.n1 ≤ 48 ∧ x.nq ≤ 5 ∧ x.nlim ≤ 29 ∧ x.npatch ≤ 6
  ∧ (x.start ≠ 0 → TabWF x)
  ∧ DWF (x.start ≠ 0) x.d0 ∧ DWF (x.start ≠ 0 ∧ x.idAac = 1) x.d1
  ∧ PsWF x.psc x.psh

/-- Layout: alignments of the data and of the 16/32-byte constants read by aligned vector
operations (`LCPI14_1/2/8`, `sbr_qmf_window_ds/us`, `ff_ps_neg`, `ps_mask`, `ps_mask2`,
`ps_mask3`, `ps_noise0/13/2`,
and `pd_reverse` of `float_dsp.o`, note F1, `VectorFmulRevC`; facts
of the linked object's section layout), the stack convention, the signed bound of
`qmf_post_shuffle`'s operand. -/
def LayoutC (x : Args) (t : MachineData) : Prop :=
  isAligned 32 (arg1 t) = true ∧ isAligned 32 (sbrA t) = true
  ∧ isAligned 32 (arg3 t) = true ∧ isAligned 32 (arg4 t) = true
  ∧ isAligned 16 (t.regs.get64 .rsp + 8#64) = true
  ∧ isAligned 16 (lab "LCPI14_1") = true ∧ isAligned 16 (lab "LCPI14_2") = true
  ∧ isAligned 16 (lab "LCPI14_8") = true ∧ isAligned 32 (lab "sbr_qmf_window_ds") = true
  ∧ isAligned 16 (lab "ff_ps_neg") = true
  ∧ (isAligned 16 (lab "ps_mask") = true
      ∧ isAligned 32 (lab "sbr_qmf_window_us") = true ∧ isAligned 16 (lab "ps_mask2") = true)
  ∧ isAligned 16 (lab "ps_mask3") = true
  ∧ (isAligned 16 (lab "ps_noise0") = true ∧ isAligned 16 (lab "ps_noise13") = true
      ∧ isAligned 16 (lab "ps_noise2") = true)
  ∧ isAligned 32 (lab "pd_reverse") = true
  ∧ (sbrA t + 0x5fcc0#64).toInt + 1280 < 2 ^ 63

def ApplyC (x : Args) (t : MachineData) : Prop := SbrWF x ∧ LayoutC x t

/-- Own bytes (`push rbp`, five saved registers, `sub $0x198`), then the deepest
call: `sbr_hf_assemble`'s return-address slot and its `0x290 + k`. -/
abbrev applyNeed (k : Nat) : Nat := 0x460 + k

abbrev ApplyPre (k : Nat) (e : Env) (x : Args) (ra : Int64) (t : MachineData) : Prop :=
  CallPre (applyNeed k) (ApplyF e x t ⋆ x.R) ra t ∧ ApplyC x t

/-- On return the footprint is owned again, with other contents: the same groups at
values `y` (the pointers that place them unchanged), with the decoder state apply
does not write unchanged (`KeepD`, INV-D5: both channels' `bs_num_env`, `t_env`,
`bs_freq_res`, `t_q`, `ps->common`, and the frequency tables with `k[0]`; `start` and
`spectrum_params` kept, or cleared together by `sbr_turnoff`, so that I1 is kept,
`Args.KeepT.i1`), and with the decoder invariant `SbrWF`
re-established for `y` (the fields apply writes: both channels'
`synthesis_filterbank_samples_offset`, from `sbr_qmf_synthesis`, and the PS phase
histories, from `ff_ps_apply`), so that `ApplyC y t` holds again (`LayoutC` does not
depend on the values). -/
abbrev ApplyFPost (e : Env) (x : Args) (t : MachineData) : Mem 64 → Prop :=
  fun m => ∃ y : Args, y.extRate = x.extRate ∧ y.fdsp = x.fdsp ∧ y.anaCtx = x.anaCtx
    ∧ y.synCtx = x.synCtx ∧ y.sampleRate = x.sampleRate ∧ x.KeepD y ∧ SbrWF y
    ∧ y.avctx = x.avctx ∧ y.ps = x.ps ∧ ApplyF e y t m

abbrev ApplyPost (k : Nat) (e : Env) (x : Args) (ra : Int64) (t s : MachineData) : Prop :=
  CallPost (applyNeed k) (ApplyFPost e x t ⋆ x.R) ra t s

/-- `ff_aac_sbr_apply(ac, che, id_aac, L, R)` with its callees at `k` bytes of stack.
What the statement does and does not say:
1. hf_assemble's footprint includes the 24 bytes after Y[Ypos] (see `HfData`,
   `a2_row_spill`). For Ypos=0 the theorem itself bounds the access to Y[1] by these
   24 bytes; for Ypos=1 those bytes belong to `g_temp`, which hf_assemble owns anyway,
   so the 24-byte bound there rests on `a2_row_spill` and the row-crossing discipline
   (HfAssemble crosses a row of `Y` only through `a2_row_spill`; checked by tv.sh),
   not on the footprint.
2. The synthesis footprint in `v0` is `qmfVSize`; the call site carves it with
   `a3_overread_carve` when it is the larger window.
3. Granularity: the theorem bounds each procedure's accesses by the union of the bytes
   it owns; reads and writes are not distinguished; within `ApplyF`'s union, object and
   row boundaries are not enforced by the theorem (splitting an owned union into
   objects does not change it). Items 1 and 2 are fixed at the hf_assemble and
   synthesis boundaries and by `a2_row_spill`.
4. Trusted: `ff_ps_apply` given `PsWF`, `top ≤ 64` and 16-alignment (`PsApplySpec`);
   `av_tx` with its tables `TxTab` (`TxSpec`); `float_dsp` for `1 ≤ len < 2^30`;
   `memcpy`, `memset`, `av_log`; the placement of the text (`Program.PlacedIn`); the x86
   dsp initialisation (the slot contents, by cpu flags). -/
abbrev ApplySpec (k : Nat) (e : Env) : Prop :=
  cenv.ProcSpec (entry "ff_aac_sbr_apply") (ApplyPre k e) (ApplyPost k e)

end Kraken.Examples.Sbr.Apply

end

/-! ## §3. The PS parser's Huffman tables and PS state

Lemmas about these: `Parse/PsSpec.lean`. -/

section

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply
namespace Kraken.Examples.Sbr.Ps

/-- One table: its address and its bytes (`4 * N` bytes for `N` entries). -/
structure VlcTab where
  p : BitVec 64
  es : List UInt8

/-- The number of entries. -/
abbrev VlcTab.N (t : VlcTab) : Nat := t.es.length / 4

/-- `table[i].sym` and `table[i].len` (little-endian `int16_t`). -/
abbrev vsym (es : List UInt8) (i : Nat) : BitVec 16 :=
  BitVec.ofInt 16 (Int.ofBytes ((es.drop (4 * i)).take 2))

abbrev vlen (es : List UInt8) (i : Nat) : BitVec 16 :=
  BitVec.ofInt 16 (Int.ofBytes ((es.drop (4 * i + 2)).take 2))

/-- The index bits of table `k`. -/
abbrev vbits (k : Nat) : Nat := if k ≤ 5 then 9 else 5

/-- The levels `get_vlc2` reads in table `k` (`max_depth`): 3 for `iid` (`0..3`), 2 for `icc`
(`4, 5`), 1 for `ipd`/`opd` (`6..9`). -/
abbrev vdepth (k : Nat) : Nat := if k ≤ 3 then 3 else if k ≤ 5 then 2 else 1

/-- The entry a subtable entry `i` (`len < 0`) sends the window whose top bits are `j` to:
`j + sym` (32-bit). The code computes `j` as `w >>> (len & 31)` for the 32-bit window `w`. -/
abbrev vnext (es : List UInt8) (i j : Nat) : Nat :=
  (BitVec.ofNat 32 j + (vsym es i).signExtend 32).toNat

/-- A walk of at most `d` levels from entry `i` reads entries of the table only and ends on an
entry with `len ≥ 0` (the code adds the last level's `len` to the index unchecked). -/
def VWalk (es : List UInt8) : Nat → Nat → Prop
  | 0, _ => False
  | d + 1, i => i < es.length / 4 ∧ ((vlen es i).msb = false
      ∨ ∀ j, j < 2 ^ (32 - (vlen es i).toNat % 32) → VWalk es d (vnext es i j))

/-- A table the walk stays inside: every walk of at most `d` levels from a level-1 entry
(`2 ^ nb` of them) is a `VWalk`. A closed, decidable property of the table contents (of the
tables `ff_ps_init_common` builds). -/
def VlcOk (nb d : Nat) (t : VlcTab) : Prop :=
  t.es.length % 4 = 0 ∧ t.N < 2 ^ 28 ∧ ∀ i, i < 2 ^ nb → VWalk t.es d i

variable [CodeEnv]

/-- The pointer cells `vlc_ps[0..n-1]`. -/
def VPtrs (v : Nat → VlcTab) : Nat → Mem 64 → Prop
  | 0 => Std.ExtHashMap.emp
  | n + 1 => Int.toBytes 8 (v n).p.toInt =@ (lab "vlc_ps" + BitVec.ofNat 64 (8 * n)) ⋆ VPtrs v n

/-- The tables `0..n-1`. -/
def VTabs (v : Nat → VlcTab) : Nat → Mem 64 → Prop
  | 0 => Std.ExtHashMap.emp
  | n + 1 => (v n).es =@ (v n).p ⋆ VTabs v n

/-- Every table is `VlcOk` at its index width and depth. -/
def VlcC (v : Nat → VlcTab) : Prop := ∀ k, k < 10 → VlcOk (vbits k) (vdepth k) (v k)

/-- The constant tables the code reads (their values, from the object):
`num_env_tab[2][4]`, `nr_iidicc_par_tab[6]`, `nr_iidopd_par_tab[6]` (`int8_t`),
`huff_iid[4]` (`int`), `ff_log2_tab[0..5]` and its GOT slot, `LCPI0_28` (`{0, 1, 2, 3}`) and
`LCPI0_30` (`4`) of the vectorized fixed-border loop. -/
def ConstW : Mem 64 → Prop :=
  [0, 1, 2, 4, 1, 2, 3, 4] =@ lab "num_env_tab"
  ⋆ ([10, 20, 34, 10, 20, 34] =@ lab "nr_iidicc_par_tab"
  ⋆ ([5, 11, 17, 5, 11, 17] =@ lab "nr_iidopd_par_tab"
  ⋆ ([2, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0] =@ lab "huff_iid"
  ⋆ (Int.toBytes 8 (lab "ff_log2_tab").toInt =@ lab "ff_log2_tab_got"
  ⋆ ([0, 0, 1, 1, 2, 2] =@ lab "ff_log2_tab"
  ⋆ ([0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0] =@ lab "LCPI0_28"
  ⋆ [4, 0, 0, 0] =@ lab "LCPI0_30"))))))

/-- What is only read: the Huffman tables with `vlc_ps`, and `ConstW`. -/
def PsTabs (v : Nat → VlcTab) : Mem 64 → Prop :=
  VPtrs v 10 ⋆ (VTabs v 10 ⋆ ConstW)

/-- The bounds that keep the row accesses `PAR[e][b]` inside `[5][34]` (the object traps,
`ud1`, outside): `nr_iid_par` (12), `nr_ipdopd_par` (16), `nr_icc_par` (28) at most 34,
`num_env_old` (40) and `num_env` (44) in `[0, 5]`, `iid_quant` (8) in `{0, 1}` (it selects the
`iid` range). Without a header the code uses the values a previous call left; each is written
only from the tables or as a comparison result. -/
def PsInv (c : List UInt8) : Prop :=
  c.length = 764
  ∧ i32 c 12 ≤ 34 ∧ i32 c 16 ≤ 34 ∧ i32 c 28 ≤ 34
  ∧ (0 ≤ i32 c 40 ∧ i32 c 40 ≤ 5) ∧ (0 ≤ i32 c 44 ∧ i32 c 44 ≤ 5)
  ∧ (i32 c 8 = 0 ∨ i32 c 8 = 1)

end Kraken.Examples.Sbr.Ps

end

/-! ## §4. The SBR parser's Huffman tables

Lemmas about these: `Parse/EnvVlc.lean`. -/

section

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply
namespace Kraken.Examples.Sbr.Vlc

/-- One table: its address and its bytes (`4 * N` bytes for `N` entries). -/
structure VlcTab where
  p : BitVec 64
  es : List UInt8

/-- The number of entries. -/
abbrev VlcTab.N (t : VlcTab) : Nat := t.es.length / 4

/-- `table[i].sym` and `table[i].len` (little-endian `int16_t`). -/
abbrev vsym (es : List UInt8) (i : Nat) : BitVec 16 :=
  BitVec.ofInt 16 (Int.ofBytes ((es.drop (4 * i)).take 2))

abbrev vlen (es : List UInt8) (i : Nat) : BitVec 16 :=
  BitVec.ofInt 16 (Int.ofBytes ((es.drop (4 * i + 2)).take 2))

/-- The subtable entry reached from a subtable entry `i` (`len < 0`) with `j` the window
shifted right by `len & 31` (`j < 2 ^ (32 - len % 32)`). -/
abbrev vnext (es : List UInt8) (i j : Nat) : Nat :=
  (BitVec.ofNat 32 j + (vsym es i).signExtend 32).toNat

/-- A walk of at most `d` levels from entry `i` stays inside the table: every entry it reads
is an entry of the table, and a walk that has used its `d` levels ends on an entry with
`len ≥ 0`. -/
def VWalk (es : List UInt8) : Nat → Nat → Prop
  | 0, _ => False
  | d + 1, i => i < es.length / 4 ∧ ((vlen es i).msb = false
      ∨ ∀ j, j < 2 ^ (32 - (vlen es i).toNat % 32) → VWalk es d (vnext es i j))

/-- A table for `get_vlc2(gb, table, nb, d)`: whole entries, fewer than `2 ^ 28` of them,
and the walk from every `nb`-bit first-level index stays inside the table. -/
def VlcOk (nb d : Nat) (t : VlcTab) : Prop :=
  t.es.length % 4 = 0 ∧ t.N < 2 ^ 28 ∧ ∀ i, i < 2 ^ nb → VWalk t.es d i

variable [CodeEnv]

/-- The pointer cells `ff_aac_sbr_vlc[0..n-1]`. -/
def VPtrs (V : BitVec 64) (v : Nat → VlcTab) : Nat → Mem 64 → Prop
  | 0 => Std.ExtHashMap.emp
  | n + 1 => c8 (V + BitVec.ofNat 64 (8 * n)) (v n).p ⋆ VPtrs V v n

/-- The tables `0..n-1`. -/
def VTabs (v : Nat → VlcTab) : Nat → Mem 64 → Prop
  | 0 => Std.ExtHashMap.emp
  | n + 1 => (v n).es =@ (v n).p ⋆ VTabs v n

/-- The address of `ff_aac_sbr_vlc`. -/
abbrev VA : BitVec 64 := lab "ff_aac_sbr_vlc"

/-- `ff_aac_sbr_vlc[10]` and the ten tables (read only). -/
def VlcW (v : Nat → VlcTab) : Mem 64 → Prop :=
  VPtrs VA v 10 ⋆ VTabs v 10

/-- Every table is `VlcOk 9 3` (`get_vlc2(gb, t, 9, 3)` in `read_sbr_envelope` and
`read_sbr_noise`). -/
def VlcC (v : Nat → VlcTab) : Prop := ∀ k, k < 10 → VlcOk 9 3 (v k)

end Kraken.Examples.Sbr.Vlc

end

/-! ## §5. `memcpy`/`memset` as value contracts

Lemmas about these: `Parse/LibCall.lean`. -/

section

open Kraken Kraken.SysV Mem
open Kraken.Examples.Sbr
namespace Kraken.Examples.Sbr.Parse
variable [CodeEnv]

/-- `memcpy(dst, src, n)`'s logical variables: the caller's memory `R` and the source bytes. -/
structure McA where
  R : Mem 64 → Prop
  src : List UInt8

/-- `src[n]` (`n` the length of `src`) read, `dst[n]` written, the two disjoint (separate
cells) and disjoint from the caller's memory. -/
abbrev McPre (need : Nat) (x : McA) (ra : Int64) (t : MachineData) : Prop :=
  CallPre need ((x.src =@ arg1 t ⋆ (arg2 t).toNat ?@ arg0 t) ⋆ x.R) ra t
    ∧ x.src.length = (arg2 t).toNat

/-- Afterwards `dst[n]` holds the source bytes; the source and the caller's memory are kept. -/
abbrev McPost (need : Nat) (x : McA) (ra : Int64) (t s : MachineData) : Prop :=
  CallPost need ((x.src =@ arg1 t ⋆ x.src =@ arg0 t) ⋆ x.R) ra t s

/-- Assumed: `memcpy` copies, with `need` bytes of stack. -/
abbrev MemcpyValSpec (need : Nat) : Prop :=
  cenv.ProcSpec (entry "memcpy") (McPre need) (McPost need)

/-- `memset(dst, c, n)`'s logical variables: the caller's memory `R`. -/
structure MsA where
  R : Mem 64 → Prop

/-- `dst[n]` owned (any contents), disjoint from the caller's memory. -/
abbrev MsPre (need : Nat) (x : MsA) (ra : Int64) (t : MachineData) : Prop :=
  CallPre need ((arg2 t).toNat ?@ arg0 t ⋆ x.R) ra t

/-- Afterwards `dst[n]` holds `n` copies of `(unsigned char)c`, `rax = dst`; the caller's
memory is kept. -/
abbrev MsPost (need : Nat) (x : MsA) (ra : Int64) (t s : MachineData) : Prop :=
  s.regs.get64 .rax = arg0 t
  ∧ CallPost need
      (List.replicate (arg2 t).toNat (UInt8.ofBitVec ((arg1 t).setWidth 8)) =@ arg0 t ⋆ x.R) ra t s

/-- Assumed: `memset` fills (the C standard's `memset`), with `need` bytes of stack. -/
abbrev MemsetValSpec (need : Nat) : Prop :=
  cenv.ProcSpec (entry "memset") (MsPre need) (MsPost need)

end Kraken.Examples.Sbr.Parse

end

/-! ## §6. The Huffman tables at their addresses

Lemmas about these: `Parse/VlcWit.lean`. -/

section

open Kraken.Examples.Sbr
namespace Kraken.Examples.Sbr.VlcWit
open VlcData

/-- Byte `k` of `N`. -/
def byteN (N k : Nat) : UInt8 := UInt8.ofNat (N / 2 ^ (8 * k))

/-- The first `L` bytes of `N`. -/
def natBytes (N L : Nat) : List UInt8 := (List.range L).map (byteN N)

/-- `ff_aac_sbr_vlc[k]`'s table: bytes and number of entries. -/
def sbrN : Nat → Nat × Nat
  | 0 => (sbr0, sbr0E) | 1 => (sbr1, sbr1E) | 2 => (sbr2, sbr2E) | 3 => (sbr3, sbr3E)
  | 4 => (sbr4, sbr4E) | 5 => (sbr5, sbr5E) | 6 => (sbr6, sbr6E) | 7 => (sbr7, sbr7E)
  | 8 => (sbr8, sbr8E) | _ => (sbr9, sbr9E)

/-- `vlc_ps[k]`'s table. -/
def psN : Nat → Nat × Nat
  | 0 => (ps0, ps0E) | 1 => (ps1, ps1E) | 2 => (ps2, ps2E) | 3 => (ps3, ps3E)
  | 4 => (ps4, ps4E) | 5 => (ps5, ps5E) | 6 => (ps6, ps6E) | 7 => (ps7, ps7E)
  | 8 => (ps8, ps8E) | _ => (ps9, ps9E)

/-- The SBR tables at the addresses `ptr k`. -/
def vS (ptr : Nat → BitVec 64) (k : Nat) : Vlc.VlcTab :=
  ⟨ptr k, natBytes (sbrN k).1 (4 * (sbrN k).2)⟩

/-- The PS tables at the addresses `ptr k`. -/
def vP (ptr : Nat → BitVec 64) (k : Nat) : Ps.VlcTab :=
  ⟨ptr k, natBytes (psN k).1 (4 * (psN k).2)⟩

end Kraken.Examples.Sbr.VlcWit

end

/-! ## §7. Placement: the `SBRDSPContext` routines

Lemmas about these: `Dsp.lean`. -/

section

open Kraken
namespace Kraken.Examples.Sbr
variable [CodeEnv]

/-- The code of every routine, as its proof states it, placed in the ambient
code. `hf_apply_noise_k`'s four entries and `apply_noise_main` are one
program, as in the object. -/
def SbrDspPlaced : Prop :=
  Program.PlacedIn NegOdd64.body ∧ Program.PlacedIn Sum64x5.body
    ∧ Program.PlacedIn SumSquare.body ∧ Program.PlacedIn QmfPreShuffle.body
    ∧ Program.PlacedIn QmfPostShuffle.body ∧ Program.PlacedIn QmfDeintNeg.body
    ∧ Program.PlacedIn QmfDeintBfly.body ∧ Program.PlacedIn Autocorrelate.body
    ∧ Program.PlacedIn Autocorrelate.body3 ∧ Program.PlacedIn HfGen.body
    ∧ Program.PlacedIn HfGFilt.body ∧ Program.PlacedIn HfApplyNoise.body

end Kraken.Examples.Sbr

end

/-! ## §8. Placement: the `float_dsp` routines

Lemmas about these: `FloatDsp.lean`. -/

section

open Kraken
namespace Kraken.Examples.Sbr
variable [CodeEnv]

/-- The code of every `float_dsp` routine `ff_aac_sbr_apply` may reach, as its
proof states it, placed in the ambient code. -/
def FloatDspPlaced : Prop :=
  Program.PlacedIn VectorFmul.bodySse ∧ Program.PlacedIn VectorFmul.bodyAvx
    ∧ Program.PlacedIn VectorFmulAdd.bodySse ∧ Program.PlacedIn VectorFmulAdd.bodyAvx
    ∧ Program.PlacedIn VectorFmulAdd.bodyFma3
    ∧ Program.PlacedIn VectorFmulRev.bodySse ∧ Program.PlacedIn VectorFmulRev.bodyAvx
    ∧ Program.PlacedIn VectorFmulRev.bodyAvx2

end Kraken.Examples.Sbr

end

/-! ## §9. Placement and slots of `ff_aac_sbr_apply`'s cluster

Lemmas about these: `Link.lean`. -/

section

open Kraken
namespace Kraken.Examples.Sbr
open Apply (Env ApplySpec)
variable [CodeEnv]

/-- Placement: the text of each of the six C procedures, of every
`SBRDSPContext` routine (`SbrDspPlaced`) and of every `float_dsp` routine the
slots may hold (`FloatDspPlaced`), sits in the ambient code
(`Program.PlacedIn`: each block at its label, falling through to the next).

Not proved. The evidence is `tv.sh`: it re-assembles each text at the object
addresses and compares it with the objects (`aacsbr.o`, `sbrdsp.o`,
`float_dsp.o`). It exits 0
with no open link item. -/
structure SbrPlaced : Prop where
  apply : Program.PlacedIn Apply.body
  lfGen : Program.PlacedIn LfGen.body
  hfInv : Program.PlacedIn HfInverseFilter.body
  xGen : Program.PlacedIn XGen.body
  hfAsm : Program.PlacedIn HfAssemble.body
  qmfSyn : Program.PlacedIn QmfSynthesis.body
  dsp : SbrDspPlaced
  fdsp : FloatDspPlaced

/-- The slot contents. The `sbr->dsp` slots are set by `ff_sbrdsp_init_x86`
(`libavcodec/x86/sbrdsp_init.c`). With SSE, SSE2 and SSE3 present they hold the
routines below. `autocorrelate` is the SSE version, or the SSE3 version when
the cpu has SSE3, so it is a disjunction. The `sbr->c` slots are set by
`ff_aacsbr_func_ptr_init` (`libavcodec/aacsbr_template.c`) to the four C
procedures. The three `float_dsp` slots `ff_aac_sbr_apply` calls are set by
`ff_float_dsp_init_x86` (`libavutil/x86/float_dsp_init.c`): with SSE present
and an x86 asm build, each holds one of its SSE/AVX/FMA3/AVX2 routines, by cpu
flags, so each is a disjunction (the C fallbacks of `libavutil/float_dsp.c`
are excluded by that premise, the same as for `sbr->dsp`). The `av_tx` and
`mdct_ana` slots are not constrained: their contracts are assumed at whatever
they hold (`SbrAssumed`). -/
structure SbrSlots (e : Env) : Prop where
  sum64x5 : e.fs.sum64x5 = entry "ff_sbr_sum64x5_sse"
  sumSquare : e.fs.sumSquare = entry "ff_sbr_sum_square_sse"
  preShuffle : e.fs.preShuffle = entry "ff_sbr_qmf_pre_shuffle_sse2"
  postShuffle : e.fs.postShuffle = entry "ff_sbr_qmf_post_shuffle_sse"
  hfGen : e.fs.hfGen = entry "ff_sbr_hf_gen_sse"
  autocorr : e.fs.autocorr = entry "ff_sbr_autocorrelate_sse"
    ∨ e.fs.autocorr = entry "ff_sbr_autocorrelate_sse3"
  gfilt : e.fs.hfs.gfilt = entry "ff_sbr_hf_g_filt_sse"
  noise0 : e.fs.hfs.noise0 = entry "ff_sbr_hf_apply_noise_0_sse2"
  noise1 : e.fs.hfs.noise1 = entry "ff_sbr_hf_apply_noise_1_sse2"
  noise2 : e.fs.hfs.noise2 = entry "ff_sbr_hf_apply_noise_2_sse2"
  noise3 : e.fs.hfs.noise3 = entry "ff_sbr_hf_apply_noise_3_sse2"
  negOdd64 : e.fs.qfs.negOdd64 = entry "ff_sbr_neg_odd_64_sse"
  deintNeg : e.fs.qfs.deintNeg = entry "ff_sbr_qmf_deint_neg_sse"
  deintBfly : e.fs.qfs.deintBfly = entry "ff_sbr_qmf_deint_bfly_sse2"
  lfGen : e.fs.lfGen = entry "sbr_lf_gen"
  hfInv : e.fs.hfInv = entry "sbr_hf_inverse_filter"
  hfAsm : e.fs.hfAsm = entry "sbr_hf_assemble"
  xGen : e.fs.xGen = entry "sbr_x_gen"
  fmul : e.fs.qfs.fmul = entry "ff_vector_fmul_sse" ∨ e.fs.qfs.fmul = entry "ff_vector_fmul_avx"
  fmulAdd : e.fs.qfs.fmulAdd = entry "ff_vector_fmul_add_sse"
    ∨ e.fs.qfs.fmulAdd = entry "ff_vector_fmul_add_avx"
    ∨ e.fs.qfs.fmulAdd = entry "ff_vector_fmul_add_fma3"
  fmulRev : e.fs.fmulRev = entry "ff_vector_fmul_reverse_sse"
    ∨ e.fs.fmulRev = entry "ff_vector_fmul_reverse_avx"
    ∨ e.fs.fmulRev = entry "ff_vector_fmul_reverse_avx2"

/-- The assumed contracts (trusted, not proved, and not witnessed: nothing here
shows they are jointly satisfiable by real code). These are the callees outside
the cluster, with `k` bytes of stack:
`ff_ps_apply` given `PsWF`, `top ≤ 64` and 16-alignment; the two `av_tx` calls
(`mdct_ana_fn` and synthesis' `mdct_fn`) with their tables `TxTab`; `memcpy`,
`memset`, `av_log`. (The `float_dsp` contracts are no longer assumed: they are
proved of the routines `SbrSlots` allows, `FloatDsp.lean`.) -/
structure SbrAssumed (k : Nat) (e : Env) : Prop where
  psApply : PsApplySpec e.PsTab k
  txAna : TxSpec e.Ctx e.TxTab k e.fs.mdctAna
  txSyn : TxSpec e.Ctx e.TxTab k e.fs.qfs.tx
  memcpy : MemcpySpec k
  memset : MemsetSpec k
  avLog : AvLogSpec e.Ext k

end Kraken.Examples.Sbr

end

/-! ## §10. The session model: frames, init, grid

Lemmas about these: `Session.lean`. -/

section

open Kraken Kraken.X64.Parser Std.WP MachineWP Kraken.SysV Mem
namespace Kraken.Examples.Sbr.Session
open Apply
variable [CodeEnv]

/-- The value part of `ApplyFPost` (`applyFPost_iff`): the values `y` a call at `x` returns
with. -/
def ApplyRel (x y : Args) : Prop :=
  y.extRate = x.extRate ∧ y.fdsp = x.fdsp ∧ y.anaCtx = x.anaCtx ∧ y.synCtx = x.synCtx
    ∧ y.sampleRate = x.sampleRate ∧ x.KeepD y ∧ SbrWF y ∧ y.avctx = x.avctx ∧ y.ps = x.ps

/-- A frame step between calls: the caller's memory `R` and the `ac` fields the footprint
reads (`ac->avctx`, `ac->oc[1].m4ac.ext_sample_rate`, `ac->oc[1].m4ac.ps`) take new values;
every value of `*sbr` and `ac->fdsp` stays. (`ext_sample_rate` and `ps` change with the output
configuration; `ac->fdsp` is allocated once with the decoder.) -/
def FrameStep (x x' : Args) : Prop :=
  x' = { x with R := x'.R, avctx := x'.avctx, extRate := x'.extRate, ps := x'.ps }

/-- The inputs of init that the SBR code does not determine: the element type `id_aac` (the
`type` argument from `che_configure`, `D`:150), the `av_tx` contexts (`av_tx_init`, l.95-106),
and the caller's memory and `ac` fields (set by the decoder, not by init). -/
structure InitIn where
  idAac : BitVec 32
  R : Mem 64 → Prop
  avctx : BitVec 64
  fdsp : BitVec 64
  extRate : BitVec 32
  ps : BitVec 32
  anaCtx : BitVec 64
  synCtx : BitVec 64

/-- `n` zero bytes. -/
abbrev zs (n : Nat) : List UInt8 := List.replicate n 0

/-- A channel after init: `av_mallocz` (l.74) zeroes `SBRData`, then
`synthesis_filterbank_samples_offset = SBR_SYNTHESIS_BUF_SIZE - (1280 - 128) = 1152`
(l.88-89, `sbr.h`: `SBR_SYNTHESIS_BUF_SIZE = (1280 - 128) * 2`). -/
def dvInit : DV :=
  { nenv := 0, freqRes := zs 9, nnoise := 0, invf := zs 10, vOff := 1152, ypos := 0,
    te := zs 10, tq := zs 3, idx := 0 }

/-- The values `ff_aac_sbr_ctx_alloc_init(ac, che, id_aac)` (l.70-111) leaves. `xInit` models a
successful `ff_aac_sbr_ctx_alloc_init` (`InitIn` assumes it returned 0):
* `ExtChannelElement` comes from `av_mallocz` (l.74): every field starts at zero;
* `kx[0] = kx[1]` (l.85) is taken before `sbr_turnoff`, so `kx[0] = 0`;
* `id_aac` (l.86);
* `sbr_turnoff` (l.87, l.58-68): `start = ready_for_dequant = 0`, `kx[1] = 32`, `m[1] = 0`
  (and `usac = 0`, `e_a[1] = -1`, `spectrum_params` all ones: raw in the footprint);
* both `synthesis_filterbank_samples_offset = 1152` (l.88-89);
* `sbr->mdct`, `sbr->mdct_ana` from `av_tx_init` (l.95-106): parameters;
* `ff_ps_ctx_init` (l.108, `PH`:97-100) sets only `ps->dsp`: `ps->common` and the phase
  histories stay zero (`ff_ps_init`, `P`:740, builds static tables only);
* `ff_sbrdsp_init`, `aacsbr_func_ptr_init` (l.109-110) set the slots (`SbrSlots`).
`sample_rate` stays 0 until the first `ff_aac_sbr_decode_extension` (l.1146-1147). -/
def xInit (i : InitIn) : Args where
  R := i.R
  start := 0
  ready := 0
  idAac := i.idAac
  reset := 0
  smooth := 0
  pushed := 0
  k0 := 0
  kx0 := 0
  kx1 := 32
  m0 := 0
  m1 := 0
  limGains := 0
  interpol := 0
  coupling := 0
  n0 := 0
  n1 := 0
  nq := 0
  nlim := 0
  npatch := 0
  pnum := zs 6
  pstart := zs 6
  ftLow := zs 50
  ftHigh := zs 98
  ftNoise := zs 12
  ftLim := zs 60
  d0 := dvInit
  d1 := dvInit
  sampleRate := 0
  avctx := i.avctx
  fdsp := i.fdsp
  extRate := i.extRate
  ps := i.ps
  anaCtx := i.anaCtx
  synCtx := i.synCtx
  psc := zs 764
  psh := zs 68
  spLo := BitVec.allOnes 32
  spHi := BitVec.allOnes 16

/-- The candidate parser invariant for `t_env_num_env_old` (see `ParseStep`): each channel's last
border `t_env[bs_num_env]` is at most `19`, live or not. Not proved of the parser here. -/
def GridInv (x : Args) : Prop :=
  u8 x.d0.te x.d0.nenv ≤ 19 ∧ u8 x.d1.te x.d1.nenv ≤ 19

end Kraken.Examples.Sbr.Session

end

/-! ## §11. The parser's model: the live element

Lemmas about these: `ParseModel.lean`. -/

section

open Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Session
namespace Kraken.Examples.Sbr.ParseModel

/-- The clauses of `DWF` for a live grid. -/
def Live (v : DV) : Prop :=
  1 ≤ v.nenv ∧ (∀ e, e ≤ v.nenv → u8 v.te e ≤ 19) ∧ (∀ e, e < v.nenv → u8 v.te e < u8 v.te (e + 1))

/-- The row of `sbr_offset[][]` (`aacsbrdata.h`) for `sbr->sample_rate` (l.283-306), or `none`
(unsupported rate: return before any store). -/
def rateRow (sr : Int) : Option Nat :=
  if sr = 16000 then some 0 else if sr = 22050 then some 1 else if sr = 24000 then some 2
  else if sr = 32000 then some 3 else if sr = 44100 ∨ sr = 48000 ∨ sr = 64000 then some 4
  else if sr = 88200 ∨ sr = 96000 ∨ sr = 128000 ∨ sr = 176400 ∨ sr = 192000 then some 5
  else none

/-- `sbr_offset[6][16]` (`aacsbrdata.h`). -/
def sbrOffset : List (List Int) :=
  [[-8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7],
   [-5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 9, 11, 13],
   [-5, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 9, 11, 13, 16],
   [-6, -4, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 9, 11, 13, 16],
   [-4, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 9, 11, 13, 16, 20],
   [-2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 9, 11, 13, 16, 20, 24]]

/-- `k[0] = start_min + sbr_offset_ptr[bs_start_freq]` (l.308-318). -/
def k0Of (sr : Int) (row start : Nat) : Int :=
  let temp : Int := if sr < 32000 then 3000 else if sr < 64000 then 4000 else 5000
  (temp * 128 + sr / 2) / sr + (sbrOffset.getD row []).getD start 0

/-- The supported rates. -/
def rates : List Int :=
  [16000, 22050, 24000, 32000, 44100, 48000, 64000, 88200, 96000, 128000, 176400, 192000]

/-- The unconditional numeric clauses of `SbrWF`. -/
def Scal (x : Args) : Prop :=
  x.kx0 ≤ 32 ∧ x.kx1 ≤ 32 ∧ x.kx0 + x.m0 ≤ 64 ∧ x.kx1 + x.m1 ≤ 64 ∧ x.m1 ≤ 48 ∧ x.k0 ≤ 32
  ∧ x.limGains ≤ 3 ∧ x.n0 ≤ 24 ∧ x.n1 ≤ 48 ∧ x.nq ≤ 5 ∧ x.nlim ≤ 29 ∧ x.npatch ≤ 6

/-- `spectrum_params.bs_start_freq`, `spectrum_params.bs_xover_band`, `bs_limiter_bands`. -/
structure Hid where
  start : Nat
  xover : Nat
  lb : Nat

/-- `sbr_turnoff` sets `spectrum_params` to all ones (l.67). -/
def Hid.turnoff (h : Hid) : Hid := { h with start := 255, xover := 255 }

/-- The model's state. -/
abbrev St := Args × Hid

/-- `sbr_turnoff` (l.58-68) on the model's state. -/
def stOff (s : St) : St := (s.1.turnoff, s.2.turnoff)

/-- **I1**, a modelling device: while `start = 0`, `spectrum_params.bs_start_freq` is `0xFF`.
It is a fact about hidden state, so `ModelStep` quantifies the hidden state existentially under
it; this is sound only because the real decoder maintains I1: `sbr_turnoff` sets the byte to
`0xFF` (l.67) together with `start = 0` (l.61), at init too (l.87); `start = 1` is set only by a
header (l.197, l.1259), and each header writes the byte (l.207, l.1188) with a 4-bit value; no
other code writes `start` or the byte. -/
def I1 (x : Args) (h : Hid) : Prop := x.start = 0 → h.start = 255

/-- The invariant between calls, on `Args`: `SbrWF` without the live clauses, the started
decoder's tables with I2, and `GridInv`. -/
def AI (x : Args) : Prop :=
  Scal x ∧ (x.start ≠ 0 → TabWF x ∧ 1 ≤ x.n0 ∧ 1 ≤ x.npatch) ∧ DWF False x.d0
  ∧ DWF False x.d1 ∧ PsWF x.psc x.psh ∧ GridInv x

/-- The invariant between calls on the model's state: `AI` and I1. -/
def MI (s : St) : Prop := AI s.1 ∧ I1 s.1 s.2

/-- The live clauses of `SbrWF`, which the last call establishes. -/
def LiveC (x : Args) : Prop :=
  (x.start ≠ 0 → Live x.d0) ∧ (x.start ≠ 0 ∧ x.idAac = 1 → Live x.d1)

end Kraken.Examples.Sbr.ParseModel

end

/-! ## §12. `sbr_reset`: `powf`/`log2f` and the band facts

Lemmas about these: `Parse/ResetSpec.lean`. -/

section

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
namespace Kraken.Examples.Sbr.Reset

/-- `p`, multiplied by `b` `j` times (`prod *= base` of `make_bands`, as `vmulss`). -/
def chain (b p : BitVec 32) : Nat → BitVec 32
  | 0 => p
  | j + 1 => BitVec.f32mul b (chain b p j)

/-- The float `1.0f`. -/
abbrev f1 : BitVec 32 := 0x3f800000#32

/-- `make_bands(bands, start, stop, nb)` with `base = powf(stop / start, 1 / nb)`: every
`lrintf(prod)` of the loop is in `[0, 64]`. -/
def BandsAt (pw : BitVec 32 → BitVec 32 → BitVec 32) (start stop nb : Nat) : Prop :=
  ∀ j, 1 ≤ j → j < nb →
    let b := pw (BitVec.f32div (BitVec.sitof32 (BitVec.ofNat 32 stop))
                  (BitVec.sitof32 (BitVec.ofNat 32 start)))
                (BitVec.f32div f1 (BitVec.sitof32 (BitVec.ofNat 32 nb)))
    let v := (BitVec.f32toi64 (chain b (BitVec.sitof32 (BitVec.ofNat 32 start)) j)).toInt
    0 ≤ v ∧ v ≤ 64

/-- A band count: `2 * lrintf(h * log2f(stop / start))`, as the code computes it (`int`). -/
def nbOf (lg : BitVec 32 → BitVec 32) (start stop : Nat) (h : BitVec 32) : Int :=
  (BitVec.ofInt 32 (2 * (BitVec.f32toi64 (BitVec.f32mul
    (lg (BitVec.f32div (BitVec.sitof32 (BitVec.ofNat 32 stop))
      (BitVec.sitof32 (BitVec.ofNat 32 start)))) h)).toInt)).toInt

/-- `invwarp` (`.LCPI5_3`): `0.76923…f` if `bs_alter_scale`, else `1.0f`. -/
abbrev invwarp (alter : Nat) : BitVec 32 := if alter = 0 then f1 else 0x3f44ec4f#32

/-- `max_qmf_subbands` for a supported rate (the bound of the check `k[2] - k[0]`). -/
def maxQ (sr : Int) : Int := if sr ≤ 32000 then 48 else if sr = 44100 then 35 else 32

/-- `n_q`: `bs_noise_bands * log2f(k[2] / kx[1])` (`vmulss`), converted to int64 (`vcvtss2si`), is
below `2 ^ 32`: the code clamps it to `≥ 1` as an int64 and then truncates it to 32 bits. For every
`k[2] ≤ 64`, `kx[1] ≤ 32` and 8-bit `bs_noise_bands`. Decidable for a given `lg`. -/
def NqOK (lg : BitVec 32 → BitVec 32) : Prop :=
  ∀ k2, k2 ≤ 64 → ∀ kx, kx ≤ 32 → ∀ nb, nb < 256 →
    (BitVec.f32toi64 (BitVec.f32mul (lg (BitVec.f32div (BitVec.sitof32 (BitVec.ofNat 32 k2))
      (BitVec.sitof32 (BitVec.ofNat 32 kx)))) (BitVec.sitof32 (BitVec.ofNat 32 nb)))).toInt < 2 ^ 32

/-- **The floating-point hypothesis.** For every supported sample rate, every 4-bit
`bs_start_freq` (so `k[0] = k0Of …`), every `k[2] ∈ [k[0], 64]` with
`k[2] - k[0] ≤ max_qmf_subbands`, `bs_freq_scale ∈ {1, 2, 3}` and `bs_alter_scale ∈ {0, 1}`:
the first band count, when positive, is at most 48 and its `make_bands` borders are in
`[0, 64]`; with two regions the second band count is in `[2, 48]` and its borders are in
`[0, 64]`. These are the inputs the code can reach: it checks the rate, `k[2] ≤ 64` and
`k[2] - k[0]` before it calls `log2f`.

Memory safety needs the counts (the code writes `count` int16 into 49-entry stack arrays
before it checks them); the border ranges keep the int16 prefix sums from wrapping, so that
`f_master` is strictly increasing (`TabWF`). Decidable for given `lg`, `pw`; the quantifiers
range over finite sets of integers only. -/
def BandsOK (lg : BitVec 32 → BitVec 32) (pw : BitVec 32 → BitVec 32 → BitVec 32) : Prop :=
  (∀ sr ∈ rates, ∀ start, start < 16 → ∀ k2, k2 ≤ 64 → ∀ fs, 1 ≤ fs → fs ≤ 3 → ∀ alter, alter ≤ 1 →
  match rateRow sr with
  | none => True
  | some row =>
    let k0 := (k0Of sr row start).toNat
    k0 ≤ k2 → (k2 : Int) - k0 ≤ maxQ sr →
    let h0 := BitVec.sitof32 (BitVec.ofNat 32 (7 - fs))
    let k1 := if 110 * k0 < 49 * k2 then 2 * k0 else k2
    let nb0 := nbOf lg k0 k1 h0
    (0 < nb0 → nb0 ≤ 48 ∧ BandsAt pw k0 k1 nb0.toNat)
    ∧ (110 * k0 < 49 * k2 →
        let nb1 := nbOf lg k1 k2 (BitVec.f32mul h0 (invwarp alter))
        2 ≤ nb1 ∧ nb1 ≤ 48 ∧ BandsAt pw k1 k2 nb1.toNat))
  ∧ NqOK lg

/-- The parameters: the callees' state `Ext` (`av_log`, `memcpy`, `powf`, `log2f`) and the
functions `powf`, `log2f`. -/
structure REnv where
  Ext : Mem 64 → Prop
  pw : BitVec 32 → BitVec 32 → BitVec 32
  lg : BitVec 32 → BitVec 32

variable [CodeEnv]

/-- Row `r` of `sbr_offset`, as bytes. -/
def sbrOffsetBytes (r : Nat) : List UInt8 :=
  ((sbrOffset.getD r []).map fun z => UInt8.ofNat (z % 256).toNat)

/-- The read-only data: `sbr_offset` (six rows of 16 signed bytes) and the constants. -/
def CstR : Mem 64 → Prop :=
  sbrOffsetBytes 0 =@ lab "sbr_offset_0" ⋆ (sbrOffsetBytes 1 =@ lab "sbr_offset_1"
    ⋆ (sbrOffsetBytes 2 =@ lab "sbr_offset_2" ⋆ (sbrOffsetBytes 3 =@ lab "sbr_offset_3"
    ⋆ (sbrOffsetBytes 4 =@ lab "sbr_offset_4" ⋆ (sbrOffsetBytes 5 =@ lab "sbr_offset_5"
    ⋆ (cell4 (lab "LCPI5_0") 0x42800000#32 ⋆ (cell4 (lab "LCPI5_1") 0x3d9d89d9#32
    ⋆ (cell4 (lab "LCPI5_8") 0xffffffff#32
    ⋆ (Int.toBytes 8 (0x3f8000003f44ec4f : Int) =@ lab "LCPI5_3"
    ⋆ (Int.toBytes 16 (0x3f80000000000000 : Int) =@ lab "LCPI5_2"
    ⋆ (Int.toBytes 16 (0x01000100010001000100010001000100 : Int) =@ lab "LCPI5_4"
    ⋆ (Int.toBytes 16 (0x0f0e0d0c0d0c09080d0c090805040100 : Int) =@ lab "LCPI5_6"
    ⋆ Int.toBytes 16 (0x0d0c090805040100 : Int) =@ lab "LCPI5_9"))))))))))))

/-- `sbr_make_f_tablelim`'s read-only table (12 bytes), passed through to it. -/
abbrev BwR : Mem 64 → Prop := Blocks [(lab "sbr_make_f_tablelim_bw", 12)]

/-- `powf(a, b)` / `log2f(a)`: the result `pw a b` / `lg a` in the low lane of `xmm0`; the
callee-saved registers, the stack and `Ext` kept. -/
abbrev lo32 (s : MachineData) (r : RegMm) : BitVec 32 := (s.zmms.get (AvxReg.xmm r)).setWidth 32

abbrev PowfSpec (e : REnv) (need : Nat) : Prop :=
  cenv.ProcSpec (entry "powf") (LeafPre need (fun _ => e.Ext) (fun _ => True))
    (fun R ra t s => LeafPost need (fun _ => e.Ext) R ra t s
      ∧ lo32 s .mm0 = e.pw (lo32 t .mm0) (lo32 t .mm1))

abbrev Log2fSpec (e : REnv) (need : Nat) : Prop :=
  cenv.ProcSpec (entry "log2f") (LeafPre need (fun _ => e.Ext) (fun _ => True))
    (fun R ra t s => LeafPost need (fun _ => e.Ext) R ra t s ∧ lo32 s .mm0 = e.lg (lo32 t .mm0))

end Kraken.Examples.Sbr.Reset

end

/-! ## §13. `ff_aac_sbr_ctx_alloc_init`: the element as cells

Lemmas about these: `Parse/InitFoot.lean`. -/

section

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr.Session (zs)
namespace Kraken.Examples.Sbr.Init

/-- The bytes of the cells the routine writes or hands to a callee. -/
structure EV where
  /-- `ch.ch[0].predictor_state` (`ChannelElement`) (8 bytes at `p + 0x9e40`). -/
  pr0 : List UInt8
  /-- `ch.ch[1].predictor_state` (8 bytes at `p + 0x13c00`). -/
  pr1 : List UInt8
  /-- `sbr->start`, `sbr->ready_for_dequant` (one 8-byte store) (8 bytes at `p + 0x28924`). -/
  sr : List UInt8
  /-- `sbr->id_aac` (4 bytes at `p + 0x2892c`). -/
  id : List UInt8
  /-- `sbr->usac` (4 bytes at `p + 0x28930`). -/
  usac : List UInt8
  /-- `sbr->spectrum_params`, bytes 0..3 (4 bytes at `p + 0x2893c`). -/
  spLo : List UInt8
  /-- `sbr->spectrum_params`, bytes 4..5 (2 bytes at `p + 0x28940`). -/
  spHi : List UInt8
  /-- `sbr->kx[0]` (4 bytes at `p + 0x28974`). -/
  kx0 : List UInt8
  /-- `sbr->kx[1]` (4 bytes at `p + 0x28978`). -/
  kx1 : List UInt8
  /-- `sbr->m[1]` (4 bytes at `p + 0x28980`). -/
  m1 : List UInt8
  /-- `sbr->data[0].synthesis_filterbank_samples_offset` (4 bytes at `p + 0x2c2a0`). -/
  v0 : List UInt8
  /-- `sbr->data[0].e_a[1]` (4 bytes at `p + 0x2c2a8`). -/
  e0 : List UInt8
  /-- `sbr->data[1].synthesis_filterbank_samples_offset` (4 bytes at `p + 0x41d60`). -/
  v1 : List UInt8
  /-- `sbr->data[1].e_a[1]` (4 bytes at `p + 0x41d68`). -/
  e1 : List UInt8
  /-- `sbr->ps.dsp` (`PSDSPContext`, 64 bytes) (64 bytes at `p + 0x74ab8`). -/
  ps : List UInt8
  /-- `sbr->mdct_ana` (8 bytes at `p + 0x88ae0`). -/
  anaC : List UInt8
  /-- `sbr->mdct_ana_fn` (8 bytes at `p + 0x88ae8`). -/
  anaF : List UInt8
  /-- `sbr->mdct` (8 bytes at `p + 0x88af0`). -/
  synC : List UInt8
  /-- `sbr->mdct_fn` (8 bytes at `p + 0x88af8`). -/
  synF : List UInt8
  /-- `sbr->dsp` (`SBRDSPContext`, 0x70 bytes) (112 bytes at `p + 0x88b00`). -/
  dsp : List UInt8
  /-- `sbr->c.sbr_lf_gen` (8 bytes at `p + 0x88b70`). -/
  c0 : List UInt8
  /-- `sbr->c.sbr_hf_assemble` (8 bytes at `p + 0x88b78`). -/
  c1 : List UInt8
  /-- `sbr->c.sbr_x_gen` (8 bytes at `p + 0x88b80`). -/
  c2 : List UInt8
  /-- `sbr->c.sbr_hf_inverse_filter` (8 bytes at `p + 0x88b88`). -/
  c3 : List UInt8

/-- The element at `p` with the cells `v`. -/
def ElemS (p : BitVec 64) (v : EV) : Mem 64 → Prop :=
  zs 0x9e40 =@ p ⋆ (v.pr0 =@ (p + 0x9e40#64) ⋆ (zs 0x9db8 =@ (p + 0x9e48#64)
    ⋆ (v.pr1 =@ (p + 0x13c00#64) ⋆ (zs 0x14d1c =@ (p + 0x13c08#64) ⋆ (v.sr =@ (p + 0x28924#64)
    ⋆ (v.id =@ (p + 0x2892c#64) ⋆ (v.usac =@ (p + 0x28930#64) ⋆ (zs 0x8 =@ (p + 0x28934#64)
    ⋆ (v.spLo =@ (p + 0x2893c#64) ⋆ (v.spHi =@ (p + 0x28940#64) ⋆ (zs 0x32 =@ (p + 0x28942#64)
    ⋆ (v.kx0 =@ (p + 0x28974#64) ⋆ (v.kx1 =@ (p + 0x28978#64) ⋆ (zs 0x4 =@ (p + 0x2897c#64)
    ⋆ (v.m1 =@ (p + 0x28980#64) ⋆ (zs 0x391c =@ (p + 0x28984#64) ⋆ (v.v0 =@ (p + 0x2c2a0#64)
    ⋆ (zs 0x4 =@ (p + 0x2c2a4#64) ⋆ (v.e0 =@ (p + 0x2c2a8#64) ⋆ (zs 0x15ab4 =@ (p + 0x2c2ac#64)
    ⋆ (v.v1 =@ (p + 0x41d60#64) ⋆ (zs 0x4 =@ (p + 0x41d64#64) ⋆ (v.e1 =@ (p + 0x41d68#64)
    ⋆ (zs 0x32d4c =@ (p + 0x41d6c#64) ⋆ (v.ps =@ (p + 0x74ab8#64) ⋆ (zs 0x13fe8 =@ (p + 0x74af8#64)
    ⋆ (v.anaC =@ (p + 0x88ae0#64) ⋆ (v.anaF =@ (p + 0x88ae8#64) ⋆ (v.synC =@ (p + 0x88af0#64)
    ⋆ (v.synF =@ (p + 0x88af8#64) ⋆ (v.dsp =@ (p + 0x88b00#64) ⋆ (v.c0 =@ (p + 0x88b70#64)
    ⋆ (v.c1 =@ (p + 0x88b78#64) ⋆ (v.c2 =@ (p + 0x88b80#64) ⋆ (v.c3 =@ (p + 0x88b88#64)
    ⋆ zs 0x10 =@ (p + 0x88b90#64))))))))))))))))))))))))))))))))))))

end Kraken.Examples.Sbr.Init

end

/-! ## §14. `ff_aac_sbr_ctx_alloc_init`: external contracts and precondition

Lemmas about these: `Parse/InitSpec.lean`. -/

section

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr
open Kraken.Examples.Sbr.Apply (c8)
open Kraken.Examples.Sbr.Session (zs)
namespace Kraken.Examples.Sbr.Init
variable [CodeEnv]

/-- Assumed: `av_mallocz(size)` (`libavutil/mem.c`) returns `NULL`, or a new address holding
`size` zero bytes, disjoint from the caller's memory; it uses the external state `X` and gives it
back. -/
abbrev AvMalloczSpec (X : Mem 64 → Prop) (need : Nat) : Prop :=
  cenv.ProcSpec (entry "av_mallocz")
    (fun (R : Mem 64 → Prop) ra t => CallPre need (X ⋆ R) ra t)
    (fun R ra t s => (s.regs.get64 .rax = 0#64 ∧ CallPost need (X ⋆ R) ra t s)
      ∨ (s.regs.get64 .rax ≠ 0#64
        ∧ CallPost need ((zs (arg0 t).toNat =@ s.regs.get64 .rax ⋆ X) ⋆ R) ra t s))

/-- What `av_tx_init` reads or writes besides `*ctx` and `*tx`: `*scale` (4 bytes at `r9`), the
stack argument `flags` (above the return address), the tables `TxTab`, the state `X`. -/
abbrev TxIn (TxTab X : Mem 64 → Prop) (t : MachineData) : Mem 64 → Prop :=
  4 ?@ arg5 t ⋆ (8 ?@ (t.regs.get64 .rsp + 8#64) ⋆ (TxTab ⋆ X))

/-- `*ctx` and `*tx` after `av_tx_init`: on success (`eax ≥ 0`) a context `c`, owned as `Ctx c`,
and a function `f`; otherwise any bytes. -/
abbrev TxOut (Ctx : BitVec 64 → Mem 64 → Prop) (t s : MachineData) (c : BitVec 64) (f : Int64) :
    Mem 64 → Prop :=
  if 0 ≤ ((s.regs.get64 .rax).setWidth 32).toInt then
    c8 (arg0 t) c ⋆ (FnCell (arg1 t) f ⋆ Ctx c)
  else 8 ?@ arg0 t ⋆ 8 ?@ arg1 t

/-- Assumed: `av_tx_init(ctx, tx, type, inv, len, scale, flags)` (`libavutil/tx.c`) writes
`*ctx` and `*tx` (`TxOut`), reads `*scale` and `flags`, and uses `TxTab` and `X`. On success
(`eax ≥ 0`) the function `f` it returns satisfies the `av_tx` contract `TxSpec` (the transform
on the context `c`, owned as `Ctx c`, with the tables `TxTab`, at `need` bytes of stack).
Nothing is assumed of the arguments. -/
abbrev AvTxInitSpec (Ctx : BitVec 64 → Mem 64 → Prop) (TxTab X : Mem 64 → Prop) (need : Nat) :
    Prop :=
  cenv.ProcSpec (entry "av_tx_init")
    (fun (R : Mem 64 → Prop) ra t =>
      CallPre need ((8 ?@ arg0 t ⋆ (8 ?@ arg1 t ⋆ TxIn TxTab X t)) ⋆ R) ra t)
    (fun R ra t s => ∃ c f,
      (0 ≤ ((s.regs.get64 .rax).setWidth 32).toInt → TxSpec Ctx TxTab need f)
      ∧ CallPost need ((TxOut Ctx t s c f ⋆ TxIn TxTab X t) ⋆ R) ra t s)

/-- Assumed: `ff_psdsp_init(s)` (`libavcodec/aacpsdsp_template.c`) writes only `*s`
(`PSDSPContext`, 64 bytes) and uses `X`. -/
abbrev PsDspInitSpec (X : Mem 64 → Prop) (need : Nat) : Prop :=
  LeafSpec "ff_psdsp_init" need (fun t => 64 ?@ arg0 t ⋆ X) (fun _ => True)

/-- The fourteen `sbr->dsp` slots (`SBRDSPContext` order, as `DspW`) as `ff_sbrdsp_init` leaves
them. -/
structure Slots where
  sum64x5 : Int64
  sumSquare : Int64
  negOdd64 : Int64
  preShuffle : Int64
  postShuffle : Int64
  deintNeg : Int64
  deintBfly : Int64
  autocorr : Int64
  hfGen : Int64
  gfilt : Int64
  noise0 : Int64
  noise1 : Int64
  noise2 : Int64
  noise3 : Int64

/-- The bytes of a function pointer. -/
abbrev fb (f : Int64) : List UInt8 := Int.toBytes 8 f.toBitVec.toInt

/-- The slots' bytes. -/
def Slots.bytes (sl : Slots) : List UInt8 :=
  fb sl.sum64x5 ++ fb sl.sumSquare ++ fb sl.negOdd64 ++ fb sl.preShuffle ++ fb sl.postShuffle
    ++ fb sl.deintNeg ++ fb sl.deintBfly ++ fb sl.autocorr ++ fb sl.hfGen ++ fb sl.gfilt
    ++ fb sl.noise0 ++ fb sl.noise1 ++ fb sl.noise2 ++ fb sl.noise3

/-- The `sbr->dsp` slots as `ff_sbrdsp_init_x86` sets them with SSE, SSE2 and SSE3 present: the
fourteen `sbr->dsp` clauses of `SbrSlots`, stated of the slots. -/
structure DspSlotsOK (sl : Slots) : Prop where
  sum64x5 : sl.sum64x5 = entry "ff_sbr_sum64x5_sse"
  sumSquare : sl.sumSquare = entry "ff_sbr_sum_square_sse"
  preShuffle : sl.preShuffle = entry "ff_sbr_qmf_pre_shuffle_sse2"
  postShuffle : sl.postShuffle = entry "ff_sbr_qmf_post_shuffle_sse"
  hfGen : sl.hfGen = entry "ff_sbr_hf_gen_sse"
  autocorr : sl.autocorr = entry "ff_sbr_autocorrelate_sse"
    ∨ sl.autocorr = entry "ff_sbr_autocorrelate_sse3"
  gfilt : sl.gfilt = entry "ff_sbr_hf_g_filt_sse"
  noise0 : sl.noise0 = entry "ff_sbr_hf_apply_noise_0_sse2"
  noise1 : sl.noise1 = entry "ff_sbr_hf_apply_noise_1_sse2"
  noise2 : sl.noise2 = entry "ff_sbr_hf_apply_noise_2_sse2"
  noise3 : sl.noise3 = entry "ff_sbr_hf_apply_noise_3_sse2"
  negOdd64 : sl.negOdd64 = entry "ff_sbr_neg_odd_64_sse"
  deintNeg : sl.deintNeg = entry "ff_sbr_qmf_deint_neg_sse"
  deintBfly : sl.deintBfly = entry "ff_sbr_qmf_deint_bfly_sse2"

/-- Assumed: `ff_sbrdsp_init(s)` (`libavcodec/sbrdsp_template.c`, with
`ff_sbrdsp_init_x86`) writes only `*s` (`SBRDSPContext`, 0x70 bytes), leaving the slots
`DspSlotsOK`, and uses `X`. -/
abbrev SbrDspInitSpec (X : Mem 64 → Prop) (need : Nat) : Prop :=
  cenv.ProcSpec (entry "ff_sbrdsp_init")
    (fun (R : Mem 64 → Prop) ra t => CallPre need ((0x70 ?@ arg0 t ⋆ X) ⋆ R) ra t)
    (fun R ra t s => ∃ sl : Slots, DspSlotsOK sl
      ∧ CallPost need ((sl.bytes =@ arg0 t ⋆ X) ⋆ R) ra t s)

/-- The assumed contracts of the callees, with `need` bytes of stack each. -/
structure InitAssumed (need : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (TxTab X : Mem 64 → Prop) :
    Prop where
  mallocz : AvMalloczSpec X need
  txInit : AvTxInitSpec Ctx TxTab X need
  psdsp : PsDspInitSpec X need
  sbrdsp : SbrDspInitSpec X need

/-- The cells after the stores, before the first `av_tx_init` (l.70-104): the stored values of
a successful run; the `av_tx`, `ps.dsp`, `sbr->dsp`, `sbr->c` cells still zero (from
`av_mallocz`). -/
def evPre (idAac : BitVec 32) (p : BitVec 64) : EV where
  pr0 := Int.toBytes 8 (p + 0x1e120#64).toInt
  pr1 := Int.toBytes 8 (p + 0x23520#64).toInt
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
  ps := zs 64
  anaC := zs 8
  anaF := zs 8
  synC := zs 8
  synF := zs 8
  dsp := zs 0x70
  c0 := zs 8
  c1 := zs 8
  c2 := zs 8
  c3 := zs 8

/-- Own bytes (`push rbp`, three saved registers, `sub $0x18`), the return slot of a call, the
callee's `k`. -/
abbrev initNeed (k : Nat) : Nat := 0x40 + k

/-- The id at entry. -/
abbrev idOf (t : MachineData) : BitVec 32 := (arg2 t).setWidth 32

abbrev InitPre (k : Nat) (TxTab X : Mem 64 → Prop) (R : Mem 64 → Prop) (ra : Int64)
    (t : MachineData) : Prop :=
  CallPre (initNeed k) ((8 ?@ arg1 t ⋆ (TxTab ⋆ X)) ⋆ R) ra t

end Kraken.Examples.Sbr.Init

end

/-! ## §15. `abort`

Lemmas about these: `Parse/LibAbort.lean`. -/

section

open Kraken MachineWP Std.WP Lean.Order Mem
namespace Kraken.Examples.Sbr.Parse
variable [CodeEnv]

/-- The entry of `abort`. -/
abbrev abortA : Int64 := (_root_.Executable.labels cenv).label "abort"

end Kraken.Examples.Sbr.Parse

end

/-! ## §16. `read_sbr_grid`'s jump table

Lemmas about these: `Parse/GridSpec.lean`. -/

section

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply
namespace Kraken.Examples.Sbr.Grid
variable [CodeEnv]

/-- The switch's jump table (`.rodata` of `aacsbr.o`, four 32-bit offsets from the table). -/
abbrev JT : BitVec 64 := lab "read_sbr_grid_jt"

abbrev jtOff (l : Label) : BitVec 32 := (lab l - JT).setWidth 32

def JtW : Mem 64 → Prop :=
  cell4 JT (jtOff "read_sbr_grid.L448b") ⋆ (cell4 (JT + 4#64) (jtOff "read_sbr_grid.L4773")
    ⋆ (cell4 (JT + 8#64) (jtOff "read_sbr_grid.L44e3")
      ⋆ cell4 (JT + 12#64) (jtOff "read_sbr_grid.L46a2")))

/-- Layout: each entry, sign-extended, is the target's offset from the table. -/
def JtC : Prop :=
  (jtOff "read_sbr_grid.L448b").signExtend 64 = lab "read_sbr_grid.L448b" - JT
  ∧ (jtOff "read_sbr_grid.L4773").signExtend 64 = lab "read_sbr_grid.L4773" - JT
  ∧ (jtOff "read_sbr_grid.L44e3").signExtend 64 = lab "read_sbr_grid.L44e3" - JT
  ∧ (jtOff "read_sbr_grid.L46a2").signExtend 64 = lab "read_sbr_grid.L46a2" - JT

/-- The stack: five pushes, the return slot of a call, the callee's `k`. -/
abbrev gridNeed (k : Nat) : Nat := 0x30 + k

end Kraken.Examples.Sbr.Grid

end

/-! ## §17. `ff_aac_sbr_decode_extension`: frames and contracts

Lemmas about these: `Parse/DecExtSpec.lean`. -/

section

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse
namespace Kraken.Examples.Sbr.DecExt

/-- The decoder-state values: the model's `Args` and `Hid`, and the raw scalars `sbr->usac`,
`sbr->bs_amp_res_header` and the six bytes of `spectrum_params`. -/
structure DS where
  a : Args
  h : Hid
  usac : BitVec 32
  amp : BitVec 32
  sp : List UInt8
  /-- `sbr->inter_tes` (+0x14, read by `read_sbr_envelope`). -/
  it : BitVec 32

/-- The lengths of the byte arrays of the footprint (so that each list cell is the array). -/
def Lens (x : Args) : Prop :=
  x.ftLow.length = 50 ∧ x.ftHigh.length = 98 ∧ x.ftNoise.length = 12 ∧ x.ftLim.length = 60
  ∧ x.pnum.length = 6 ∧ x.pstart.length = 6 ∧ x.psc.length = 764

/-- `Hid.start` is `spectrum_params.bs_start_freq` (byte 0), `Hid.xover` is
`spectrum_params.bs_xover_band` (byte 2); the array lengths. -/
def DS.ok (d : DS) : Prop :=
  d.sp.length = 6 ∧ d.h.start = u8 d.sp 0 ∧ d.h.xover = u8 d.sp 2 ∧ Lens d.a

/-- The invariant of the raw scalars: the field width of `bs_limiter_bands` (2 bits). -/
def DS.si (d : DS) : Prop := d.h.lb ≤ 3

/-- The bit reader: the buffer, `size_in_bits_plus8`, and the bytes `[buf, buf + L)` owned. -/
structure Rd where
  buf : BitVec 64
  p8 : BitVec 32
  L : Nat

/-- The reader's precondition: every read loads at most 4 bytes at `buf + index / 8` with
`index ≤ size_in_bits_plus8`. -/
def Rd.ok (r : Rd) (i : BitVec 32) : Prop :=
  i.toNat ≤ r.p8.toNat ∧ r.p8.toNat < 2 ^ 31 ∧ r.p8.toNat / 8 + 4 ≤ r.L ∧ r.L < 2 ^ 32

/-- The fields of `Args` outside the footprint, and those no routine of the parser writes. -/
def XKeep (x y : Args) : Prop :=
  y.R = x.R ∧ y.fdsp = x.fdsp ∧ y.anaCtx = x.anaCtx ∧ y.synCtx = x.synCtx ∧ y.psh = x.psh
  ∧ y.avctx = x.avctx ∧ y.ps = x.ps

variable [CodeEnv]

/-- The scalar fields of `*sbr` at `s` (`0x0`–`0x80`). -/
def SbrS (d : DS) (s : BitVec 64) : Mem 64 → Prop :=
  cell4 s d.a.sampleRate ⋆ (cell4 (s + 0x4#64) d.a.start ⋆ (cell4 (s + 0x8#64) d.a.ready
  ⋆ (cell4 (s + 0xc#64) d.a.idAac ⋆ (cell4 (s + 0x10#64) d.usac ⋆ (cell4 (s + 0x14#64) d.it
  ⋆ (cell4 (s + 0x18#64) d.a.reset ⋆ (d.sp =@ (s + 0x1c#64)
  ⋆ (2 ?@ (s + 0x22#64) ⋆ (cell4 (s + 0x24#64) d.amp ⋆ (4 ?@ (s + 0x28#64)
  ⋆ (c4 (s + 0x2c#64) d.h.lb ⋆ (c4 (s + 0x30#64) d.a.limGains ⋆ (cell4 (s + 0x34#64) d.a.interpol
  ⋆ (cell4 (s + 0x38#64) d.a.smooth ⋆ (cell4 (s + 0x3c#64) d.a.coupling
  ⋆ (c4 (s + 0x40#64) d.a.k0 ⋆ (16 ?@ (s + 0x44#64) ⋆ (c4 (s + 0x54#64) d.a.kx0
  ⋆ (c4 (s + 0x58#64) d.a.kx1 ⋆ (c4 (s + 0x5c#64) d.a.m0 ⋆ (c4 (s + 0x60#64) d.a.m1
  ⋆ (cell4 (s + 0x64#64) d.a.pushed ⋆ 0x18 ?@ (s + 0x68#64)))))))))))))))))))))))

/-- One `SBRData` at `d` (`0x15ac0` bytes) with values `v`; the fields outside `DV` are raw. -/
def DataF (v : DV) (d : BitVec 64) : Mem 64 → Prop :=
  4 ?@ d ⋆ (4 ?@ (d + 0x4#64) ⋆ (c4 (d + 0x8#64) v.nenv ⋆ (v.freqRes =@ (d + 0xc#64)
  ⋆ (3 ?@ (d + 0x15#64) ⋆ (c4 (d + 0x18#64) v.nnoise ⋆ (11 ?@ (d + 0x1c#64)
  ⋆ (v.invf =@ (d + 0x27#64) ⋆ (48 ?@ (d + 0x31#64) ⋆ (3 ?@ (d + 0x61#64)
  ⋆ (4 ?@ (d + 0x64#64) ⋆ (0x3898 ?@ (d + 0x68#64) ⋆ (cell4 (d + 0x3900#64) v.vOff
  ⋆ (4 ?@ (d + 0x3904#64) ⋆ (4 ?@ (d + 0x3908#64) ⋆ (0x4014 ?@ (d + 0x390c#64)
  ⋆ (c4 (d + 0x7920#64) v.ypos
  ⋆ (0xe178 ?@ (d + 0x7924#64) ⋆ (v.te =@ (d + 0x15a9c#64) ⋆ (v.tq =@ (d + 0x15aa6#64)
  ⋆ (3 ?@ (d + 0x15aa9#64) ⋆ (Apply.c8 (d + 0x15aac#64) v.idx
    ⋆ 12 ?@ (d + 0x15ab4#64))))))))))))))))))))))

/-- The frequency tables (`n`, `n_q`, `n_lim`, `f_master` raw, the four tables, the patches)
at `s + 0x4c1e0`. -/
def TabF (x : Args) (s : BitVec 64) : Mem 64 → Prop :=
  c4 (s + 0x4c1e0#64) x.n0 ⋆ (c4 (s + 0x4c1e4#64) x.n1 ⋆ (c4 (s + 0x4c1e8#64) x.nq
  ⋆ (c4 (s + 0x4c1ec#64) x.nlim ⋆ (98 ?@ (s + 0x4c1f0#64) ⋆ (x.ftLow =@ (s + 0x4c252#64)
  ⋆ (x.ftHigh =@ (s + 0x4c284#64) ⋆ (x.ftNoise =@ (s + 0x4c2e6#64)
  ⋆ (x.ftLim =@ (s + 0x4c2f2#64) ⋆ (2 ?@ (s + 0x4c32e#64) ⋆ (c4 (s + 0x4c330#64) x.npatch
  ⋆ (x.pnum =@ (s + 0x4c334#64) ⋆ x.pstart =@ (s + 0x4c33a#64))))))))))))

/-- The decoder state at `sbr = s`: the scalars, `data[0]`, `data[1]`, `ps->common`, the
tables. -/
def SbrF (d : DS) (s : BitVec 64) : Mem 64 → Prop :=
  SbrS d s ⋆ (DataF d.a.d0 (s + 0x80#64) ⋆ (DataF d.a.d1 (s + 0x15b40#64)
  ⋆ (d.a.psc =@ (s + 0x2b600#64) ⋆ TabF d.a s)))

/-- Assumed: `avpriv_request_sample(avc, msg, ...)` touches only `Ext`. -/
abbrev AvReqSpec (Ext : Mem 64 → Prop) (need : Nat) : Prop :=
  LeafSpec "avpriv_request_sample" need (fun _ => Ext) (fun _ => True)

/-- The logical variables: the caller's memory, the decoder-state values, the reader `*gb_host`
(`index`, `size_in_bits`, the four padding bytes after `size_in_bits_plus8`, which the copy of
the struct reads), `ac->oc[1].m4ac.sample_rate`. -/
structure XA where
  R : Mem 64 → Prop
  d : DS
  r : Rd
  i : BitVec 32
  sib : BitVec 32
  pad : BitVec 32
  sr : BitVec 32

/-- Own bytes (`push rbp`, five saved registers, `sub $0x38`), the return slot of a call, and the
callee's reservation. -/
abbrev decNeed (kc : Nat) : Nat := 0x70 + kc

/-- What a return leaves: values with `MI` and `LiveC` (the conclusion of
`ParseModel.decext_spec`), `Hid` tied to `spectrum_params`, the fields outside the footprint
kept, the host reader advanced within `size_in_bits_plus8`, and `cnt` returned. -/
def DecOut (PI : List UInt8 → Prop) (X : XA) (d' : DS) : Prop :=
  MI (d'.a, d'.h) ∧ LiveC d'.a ∧ d'.ok ∧ PI d'.a.psc ∧ XKeep X.d.a d'.a ∧ d'.si

/-- The safe stops: `abort`'s entry (`read_sbr_grid`'s assertion) and the bounds trap of
`read_sbr_envelope` (`ud1`, an envelope index ≥ 6). -/
abbrev DStops (a : Int64) : Prop := a = abortA ∨ a = entry "read_sbr_envelope.L60f9"

end Kraken.Examples.Sbr.DecExt

end

/-! ## §18. `ff_aac_sbr_decode_usac_data`: frames

Lemmas about these: `Parse/UsacSpec.lean`. -/

section

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse
namespace Kraken.Examples.Sbr.Usac

/-- The values that stay fixed through the call: the caller's rest `R`, the addresses of
`ac`, `che`, `ue`, `gb`, the bit reader (`buffer`, `size_in_bits_plus8`, the buffer's length),
the twelve bytes `ue->sbr` at `ue + 0xc` (`bs_intertes`, the default header, `+0xc..+0x17`),
`av_log`'s state and the other callees' state. -/
structure UQ where
  R : Mem 64 → Prop
  a : BitVec 64
  c : BitVec 64
  ue : BitVec 64
  g : BitVec 64
  buf : BitVec 64
  p8 : BitVec 32
  L : Nat
  uev : List UInt8
  Ext : Mem 64 → Prop
  Oth : Mem 64 → Prop

/-- The values between blocks: the model's state `(x, h)`, the reader's `index`, `sbr->usac`,
`sbr->bs_amp_res_header`, the bytes of `spectrum_params`. -/
structure USt where
  x : Args
  h : Hid
  i : BitVec 32
  u : BitVec 32
  amp : BitVec 32
  sp : List UInt8

/-- `Hid` read from the bytes: `bs_start_freq`, `bs_xover_band` are bytes 0 and 2 of
`spectrum_params`; `bs_limiter_bands` (an `unsigned`) is a cell of its own, a 2-bit value
(`DecExt.DS.si`); the lengths of the byte arrays (`DecExt.Lens`). -/
def SpOk (st : USt) : Prop :=
  st.sp.length = 6 ∧ u8 st.sp 0 = st.h.start ∧ u8 st.sp 2 = st.h.xover ∧ st.h.lb ≤ 3
  ∧ DecExt.Lens st.x

variable [CodeEnv]

/-- `*gb` with `index = i` (`size_in_bits` raw). -/
def GbU (q : UQ) (i : BitVec 32) : Mem 64 → Prop :=
  Int.toBytes 8 q.buf.toInt =@ q.g ⋆ (cell4 (q.g + 8#64) i ⋆ (4 ?@ (q.g + 0xc#64)
    ⋆ cell4 (q.g + 0x10#64) q.p8))

/-- The `Args` fields outside the footprint are kept. -/
def UKeep (x y : Args) : Prop :=
  y.psc = x.psc ∧ y.psh = x.psh ∧ y.anaCtx = x.anaCtx ∧ y.synCtx = x.synCtx ∧ y.fdsp = x.fdsp
  ∧ y.ps = x.ps ∧ y.avctx = x.avctx ∧ y.extRate = x.extRate

/-- Own frame (`push rbp`, five saved registers, `sub $0x18`), a call's return slot, the
callee's `cneed k`. -/
abbrev cneed (k : Nat) : Nat := Grid.gridNeed k

abbrev usacNeed (k : Nat) : Nat := 0x50 + cneed k

end Kraken.Examples.Sbr.Usac

end

/-! ## §19. The session over the binary: placement, assumptions, objects

Lemmas about these: `SessionBin/Defs.lean`. -/

section

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Session Kraken.Examples.Sbr.Parse
namespace Kraken.Examples.Sbr.SessionBin

/-- The raw scalars of `*sbr` that only the parser reads: `sbr->usac` (+0x10), `inter_tes`
(+0x14), `bs_amp_res_header` (+0x24), `bs_limiter_bands` (+0x2c). -/
structure HV where
  usac : BitVec 32
  it : BitVec 32
  amp : BitVec 32
  lb : Nat

/-- The session's values. `Args.R` is not used: the caller's memory is part of each call's
frame. -/
abbrev SV := Args × HV

/-- The six bytes of `spectrum_params` (`Args.spLo`, `Args.spHi`, as `ScW` stores them). -/
def spBytes (x : Args) : List UInt8 := Int.toBytes 4 x.spLo.toInt ++ Int.toBytes 2 x.spHi.toInt

/-- The model's hidden state: `bs_start_freq` (byte 0), `bs_xover_band` (byte 2) of
`spectrum_params`, and `bs_limiter_bands`. -/
def hidOf (σ : SV) : Hid := ⟨u8 (spBytes σ.1) 0, u8 (spBytes σ.1) 2, σ.2.lb⟩

/-- `ff_aac_sbr_decode_extension`'s values. -/
def toDS (σ : SV) : DecExt.DS := ⟨σ.1, hidOf σ, σ.2.usac, σ.2.amp, spBytes σ.1, σ.2.it⟩

/-- The `spectrum_params` fields of `Args` from six bytes. -/
def withSp (x : Args) (sp : List UInt8) : Args :=
  { x with spLo := BitVec.ofInt 32 (Int.ofBytes (sp.take 4)),
           spHi := BitVec.ofInt 16 (Int.ofBytes (sp.drop 4)) }

/-- The session's values after `ff_aac_sbr_decode_extension` returned with `d` (the parser's
`d.a.spLo`/`spHi` are not in its footprint; the bytes `d.sp` are). -/
def ofDS (d : DecExt.DS) : SV := (withSp d.a d.sp, ⟨d.usac, d.it, d.amp, d.h.lb⟩)

/-- The session's values after a USAC entry returned with `st`; `inter_tes` (raw in `UF`) is
`it`. -/
def ofUSt (st : Usac.USt) (it : BitVec 32) : SV := (withSp st.x st.sp, ⟨st.u, it, st.amp, st.h.lb⟩)

/-- `ff_aac_sbr_ctx_alloc_init`'s raw scalars: `av_mallocz` zeroes them. -/
def hvInit : HV := ⟨0, 0, 0, 0⟩

/-- The values after init. -/
def σInit (i : InitIn) : SV := (xInit i, hvInit)

/-- The events of a session. -/
inductive Ev where
  | dec (id : BitVec 32)
  | usac (cpe : Bool)
  | config
  | apply
  | frame

/-- The value part of each entry's postcondition, with the flag `ok'` of the result. -/
inductive Step : Ev → SV → SV × Bool → Prop
  /-- `ff_aac_sbr_decode_extension`: `DecOut` (with `PsInv` as `PI`) at the values `d`. -/
  | dec {id : BitVec 32} {σ : SV} (d : DecExt.DS) :
      DecExt.DecOut Ps.PsInv ⟨σ.1.R, toDS σ, ⟨0, 0, 0⟩, 0, 0, 0, 0⟩ d →
      Step (.dec id) σ (ofDS d, true)
  /-- `ff_aac_sbr_decode_usac_data` with result `ret`: `UsacOut`, with the field width of
  `bs_limiter_bands` and the array lengths (the strengthened postcondition). -/
  | usac {cpe : Bool} {σ : SV} (st : Usac.USt) (ret it : BitVec 32) :
      MI (st.x, st.h) → (ret = 0#32 → LiveC st.x) → Usac.UKeep σ.1 st.x → Usac.SpOk st →
      st.h.lb ≤ 3 → DecExt.Lens st.x →
      Step (.usac cpe) σ (ofUSt st it, decide (ret = 0#32))
  /-- `ff_aac_sbr_config_usac`: `sbr_turnoff`. -/
  | config {σ : SV} (st : Usac.USt) (it : BitVec 32) :
      (st.x, st.h) = stOff (σ.1, hidOf σ) → Usac.SpOk st → Usac.UKeep σ.1 st.x →
      Step .config σ (ofUSt st it, true)
  /-- `ff_aac_sbr_apply`: `ApplyRel`; `sbr->usac` is raw in `ApplyF` (any `u`), the other raw
  scalars are outside it and kept. -/
  | apply {σ : SV} {y : Args} (u : BitVec 32) :
      ApplyRel σ.1 y → Step .apply σ ((y, { σ.2 with usac := u }), true)
  /-- The caller changes its memory and the `ac` fields (`FrameStep`). -/
  | frame {σ : SV} {x' : Args} (ok : Bool) : FrameStep σ.1 x' → Step .frame σ ((x', σ.2), ok)

/-- The values reachable from `σ₀`, with the flag `ok`. Apply steps only from `ok`; frame steps
keep the flag. -/
inductive SReach (σ₀ : SV) : SV → Bool → Prop
  | init : SReach σ₀ σ₀ true
  | step {σ σ' : SV} {ok ok' : Bool} (ev : Ev) :
      SReach σ₀ σ ok → (ev = .apply → ok = true) → (ev = .frame → ok' = ok) →
      Step ev σ (σ', ok') → SReach σ₀ σ' ok'

variable [CodeEnv]

/-- The parser's read-only data: `read_sbr_grid`'s jump table, `ceil_log2`, the SBR and PS
Huffman tables (with the PS constants `ConstW`), `sbr_reset`'s constants and `sbr_offset`, the
limiter table. -/
def PStat (vs : Nat → Vlc.VlcTab) (vp : Nat → Ps.VlcTab) : Mem 64 → Prop :=
  Grid.JtW ⋆ (Blocks [(lab "ceil_log2", 6)] ⋆ (Vlc.VlcW vs ⋆ (Ps.PsTabs vp
    ⋆ (Reset.CstR ⋆ Reset.BwR))))

/-- `sbr->ps` without `ps->common`: the rest of `PsW`. -/
def PsRest (x : Args) (t : MachineData) : Mem 64 → Prop :=
  let p := sbrA t + 0x2b600#64
  4 ?@ (p + 764#64) ⋆ (133200 ?@ (p + 768#64) ⋆ (x.psh =@ (p + 133968#64)
    ⋆ 76 ?@ (p + 134036#64)))

/-- The fields only `ff_aac_sbr_decode_extension` touches: `ac->oc[1].m4ac.sample_rate`,
`ac->warned_he_aac_mono`, `ac->avctx->profile`; owned by the caller per call, any contents. -/
def AcX (ac avctx : BitVec 64) : Mem 64 → Prop :=
  4 ?@ (ac + 0x57e0#64) ⋆ (4 ?@ (ac + 0x8850#64) ⋆ 4 ?@ (avctx + 0x2b0#64))

/-- Placement of every text: apply's cluster (`SbrPlaced`) and the parser's routines, and the
layout facts of the link (constant alignments, `read_sbr_grid`'s jump table). Not proved in
Lean; the evidence is translation validation of each text against the linked object. -/
structure SessPlaced : Prop where
  /-- `ff_aac_sbr_apply` and its callees, and the dsp kernels, are placed as decoded. -/
  apply : SbrPlaced
  /-- `ff_aac_sbr_decode_extension` is placed as decoded. -/
  decExt : Program.PlacedIn DecExt.body
  /-- `ff_aac_sbr_decode_usac_data` is placed as decoded. -/
  usac : Program.PlacedIn Usac.body
  /-- `ff_aac_sbr_config_usac` is placed as decoded. -/
  config : Program.PlacedIn Usac.cbody
  /-- `read_sbr_header` is placed as decoded. -/
  hdr : Program.PlacedIn Hdr.body
  /-- `sbr_reset` is placed as decoded. -/
  reset : Program.PlacedIn Reset.body
  /-- `sbr_make_f_tablelim` is placed as decoded. -/
  tlim : Program.PlacedIn Tlim.body
  /-- `read_sbr_grid` is placed as decoded. -/
  grid : Program.PlacedIn Grid.body
  /-- `read_sbr_dtdf` is placed as decoded. -/
  dtdf : Program.PlacedIn Dtdf.body
  /-- `read_sbr_invf` is placed as decoded. -/
  invf : Program.PlacedIn Invf.body
  /-- `read_sbr_envelope` is placed as decoded. -/
  env : Program.PlacedIn Env.body
  /-- `read_sbr_noise` is placed as decoded. -/
  noise : Program.PlacedIn Noise.body
  /-- `ff_ps_read_data` is placed as decoded. -/
  ps : Program.PlacedIn Ps.body
  /-- `ff_aac_sbr_ctx_alloc_init` is placed as decoded. -/
  init : Program.PlacedIn Init.body
  /-- The link places `sbr_reset`'s `vmovdqa` constant `LCPI5_6` 16-aligned (as `LayoutC`'s
  label clauses). -/
  lcpi : isAligned 16 (lab "LCPI5_6") = true
  /-- The link places `ff_aac_sbr_apply`'s constants aligned (`LayoutC`'s label clauses). -/
  labs : isAligned 16 (lab "LCPI14_1") = true ∧ isAligned 16 (lab "LCPI14_2") = true
    ∧ isAligned 16 (lab "LCPI14_8") = true ∧ isAligned 32 (lab "sbr_qmf_window_ds") = true
    ∧ isAligned 16 (lab "ff_ps_neg") = true ∧ isAligned 16 (lab "ps_mask") = true
    ∧ isAligned 32 (lab "sbr_qmf_window_us") = true ∧ isAligned 16 (lab "ps_mask2") = true
    ∧ isAligned 16 (lab "ps_mask3") = true ∧ isAligned 16 (lab "ps_noise0") = true
    ∧ isAligned 16 (lab "ps_noise13") = true ∧ isAligned 16 (lab "ps_noise2") = true
    ∧ isAligned 32 (lab "pd_reverse") = true
  /-- The layout of `read_sbr_grid`'s jump table. -/
  jt : Grid.JtC

/-- The assumed external contracts and data facts, with `k` bytes of stack for each external
routine: `ps_apply`, the two transforms, `av_log` on the logging state `e.Ext`, `memcpy` and
`memset` as value contracts (apply's raw-footprint versions follow, `memcpy_of_val`,
`memset_of_val`), `avpriv_request_sample` on `e.Ext`, `powf`/`log2f` as the functions `pw`/`lg` on
`e.Ext` with the floating-point hypothesis `BandsOK` (which includes `NqOK`), and the shape of
the SBR and PS Huffman tables (`VlcC`). (`abort`'s specification holds of any code,
`abortSpec_holds`.) -/
structure SessionAssumed (k : Nat) (e : Env) (vs : Nat → Vlc.VlcTab) (vp : Nat → Ps.VlcTab)
    (pw : BitVec 32 → BitVec 32 → BitVec 32) (lg : BitVec 32 → BitVec 32) : Prop where
  psApply : PsApplySpec e.PsTab k
  txAna : TxSpec e.Ctx e.TxTab k e.fs.mdctAna
  txSyn : TxSpec e.Ctx e.TxTab k e.fs.qfs.tx
  avLog : AvLogSpec e.Ext k
  memcpyV : MemcpyValSpec k
  memsetV : MemsetValSpec k
  avReq : DecExt.AvReqSpec e.Ext k
  powf : Reset.PowfSpec ⟨e.Ext, pw, lg⟩ k
  log2f : Reset.Log2fSpec ⟨e.Ext, pw, lg⟩ k
  bands : Reset.BandsOK lg pw
  vlcS : Vlc.VlcC vs
  vlcP : Ps.VlcC vp

/-- The bit reader `*gb` of a `decode_extension` call: the reader (`buf`, `size_in_bits_plus8`,
the bytes owned), `size_in_bits`, the padding after `size_in_bits_plus8`. -/
structure Rdr where
  r : DecExt.Rd
  sib : BitVec 32
  pad : BitVec 32

/-- `*gb_host` at `g` with `index = i` (`DecExt.GhW`). -/
abbrev RdrW (g : BitVec 64) (b : Rdr) (i : BitVec 32) : Mem 64 → Prop :=
  Apply.c8 g b.r.buf ⋆ (cell4 (g + 8#64) i ⋆ (cell4 (g + 0xc#64) b.sib
    ⋆ (cell4 (g + 0x10#64) b.r.p8 ⋆ cell4 (g + 0x14#64) b.pad)))

/-- The objects of a `decode_extension` call besides the element: `*gb` at index `i`, the
bitstream bytes, the three `*ac` fields, the caller's rest `Rc`. -/
abbrev DecObj (b : Rdr) (avctx : BitVec 64) (Rc : Mem 64 → Prop) (i : BitVec 32)
    (t : MachineData) : Mem 64 → Prop :=
  RdrW (arg2 t) b i ⋆ (Blocks [(b.r.buf, b.r.L)] ⋆ (AcX (arg0 t) avctx ⋆ Rc))

/-- The objects of a `decode_usac_data` call: `*gb` (`GbU`) at index `i`, the bitstream bytes,
`ue->sbr` (12 bytes), the caller's rest. -/
abbrev UsacObj (q : Usac.UQ) (i : BitVec 32) : Mem 64 → Prop :=
  Usac.GbU q i ⋆ (Blocks [(q.buf, q.L)] ⋆ (q.uev =@ (q.ue + 0xc#64) ⋆ q.R))

end Kraken.Examples.Sbr.SessionBin

end

/-! ## §20. The `float_dsp` slots after init

Lemmas about these: `Parse/InitLinkBase.lean`. -/

section

open Kraken Kraken.SysV Mem Kraken.X64.Parser
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply
open Kraken.Examples.Sbr.Session (zs InitIn xInit)
namespace Kraken.Examples.Sbr.Init
variable [CodeEnv]

/-- The `float_dsp` slots of `SbrSlots`. -/
structure FdspOK (e : Env) : Prop where
  fmul : e.fs.qfs.fmul = entry "ff_vector_fmul_sse" ∨ e.fs.qfs.fmul = entry "ff_vector_fmul_avx"
  fmulAdd : e.fs.qfs.fmulAdd = entry "ff_vector_fmul_add_sse"
    ∨ e.fs.qfs.fmulAdd = entry "ff_vector_fmul_add_avx"
    ∨ e.fs.qfs.fmulAdd = entry "ff_vector_fmul_add_fma3"
  fmulRev : e.fs.fmulRev = entry "ff_vector_fmul_reverse_sse"
    ∨ e.fs.fmulRev = entry "ff_vector_fmul_reverse_avx"
    ∨ e.fs.fmulRev = entry "ff_vector_fmul_reverse_avx2"

/-- The bytes of the element outside the session's description: the `ChannelElement` part and
the 16 bytes after `sbr->c`. -/
def InitGap (p : BitVec 64) : Mem 64 → Prop := Blocks [(p, 0x28920), (p + 0x88b90#64, 0x10)]

/-- The three `float_dsp` slots of `*ac->fdsp` in `FnW`. -/
def FdspW (e : Env) (fdsp : BitVec 64) : Mem 64 → Prop :=
  FnCell fdsp e.fs.qfs.fmul ⋆ (FnCell (fdsp + 0x30#64) e.fs.qfs.fmulAdd
    ⋆ FnCell (fdsp + 0x38#64) e.fs.fmulRev)

omit [CodeEnv]
end Kraken.Examples.Sbr.Init

end

/-! ## §21. `decode_extension`'s callee stack

Lemmas about these: `SessionBin/Bridge.lean`. -/

section

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Session Kraken.Examples.Sbr.Parse
namespace Kraken.Examples.Sbr.SessionBin
variable [CodeEnv]

/-- The stack of `decode_extension`'s callees from the leaf need `k`: the largest callee need,
`sbr_reset`'s (`Reset.resetNeed k`). -/
def decKc (k : Nat) : Nat := 0x9d0 + k

end Kraken.Examples.Sbr.SessionBin

end

/-! ## §22. `decode_usac_data`'s callee stack

Lemmas about these: `SessionBin/UsacAsmS.lean`. -/

section

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse
namespace Kraken.Examples.Sbr.SessionBin
variable [CodeEnv]

/-- The index of `decode_usac_data`'s callees from the leaf need `k`: their stack
`Usac.cneed (usacK k) = 0x9d0 + k` is `sbr_reset`'s. -/
def usacK (k : Nat) : Nat := 0x9a0 + k

end Kraken.Examples.Sbr.SessionBin

end

/-! ## §23. The vocabulary: `Live`, `Ready`, `AcFields`, the calls

Lemmas about these: `SessionBin/TopDefs.lean`. -/

section

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Session Kraken.Examples.Sbr.Parse
namespace Kraken.Examples.Sbr.SessionBin

/-- The fixed parameters of a session, chosen once by the caller. -/
structure Setup where
  /-- Bytes of stack each external routine (`av_log`, `memcpy`, `powf`, …) may use. -/
  k : Nat
  /-- The caller's environment: `av_log`'s state, the transforms' contexts and tables, the
  table of `ff_ps_apply`, the `float_dsp` routines. -/
  env : Env
  /-- What libm's `powf` computes, on bit patterns. -/
  pw : BitVec 32 → BitVec 32 → BitVec 32
  /-- What libm's `log2f` computes, on bit patterns. -/
  lg : BitVec 32 → BitVec 32
  /-- The addresses of FFmpeg's ten SBR Huffman tables (`ff_aac_sbr_vlc`). -/
  sbrTabs : Nat → BitVec 64
  /-- The addresses of FFmpeg's ten PS Huffman tables. -/
  psTabs : Nat → BitVec 64

/-- The SBR Huffman tables: FFmpeg's, at `S.sbrTabs`. -/
abbrev Setup.vs (S : Setup) : Nat → Vlc.VlcTab := VlcWit.vS S.sbrTabs

/-- The PS Huffman tables: FFmpeg's, at `S.psTabs`. -/
abbrev Setup.vp (S : Setup) : Nat → Ps.VlcTab := VlcWit.vP S.psTabs

/-- A call state whose first two arguments are `ac`, `che`. -/
def tAt (che ac : BitVec 64) : MachineData :=
  { regs := (({} : Reg64s).set64 .rdi ac).set64 .rsi che }

variable [CodeEnv]

/-- The three fields of `*ac` that the decoder sets and the SBR code reads: `ac->avctx`,
`ac->oc[1].m4ac.ext_sample_rate`, `ac->oc[1].m4ac.ps`. -/
def AcFields (ac avctx : BitVec 64) (er ps : BitVec 32) : Mem 64 → Prop :=
  c8 (ac + 0x8#64) avctx ⋆ (cell4 (ac + 0x57f4#64) er ⋆ cell4 (ac + 0x5800#64) ps)

/-- The element's memory at the values `σ`, by its addresses: `SessW` without `AcFields`. -/
def ElemAt (e : Env) (vs : Nat → Vlc.VlcTab) (vp : Nat → Ps.VlcTab) (σ : SV)
    (che ac : BitVec 64) : Mem 64 → Prop :=
  let t := tAt che ac
  DecExt.SbrF (toDS σ) (sbrA t) ⋆ (PsRest σ.1 t ⋆ (ArrW t ⋆ (DspW e t ⋆ (FnW e σ.1 t
    ⋆ (c8 (ac + 0x2550#64) σ.1.fdsp ⋆ (CstW ⋆ PStat vs vp))))))

/-- The environment the element was set up in meets the session's external contracts. -/
def EnvOK (S : Setup) (e : Env) : Prop :=
  SessionAssumed S.k e S.vs S.vp S.pw S.lg ∧ SbrSlots e

/-- The element at `che` in a state reachable from init with flag `ok`: its memory (the whole
allocation at `che`, and `ac->fdsp`) in some environment meeting the contracts. -/
def ElemState (S : Setup) (che ac : BitVec 64) (ok : Bool) : Mem 64 → Prop :=
  fun m => ∃ (e : Env) (i : InitIn) (σ : SV), EnvOK S e ∧ SReach (σInit i) σ ok
    ∧ (ElemAt e S.vs S.vp σ che ac ⋆ Init.InitGap che) m

/-- **The SBR element at `che` is live**: in a state reachable from `ff_aac_sbr_ctx_alloc_init`
by calls of the entry points. -/
def Live (S : Setup) (che ac : BitVec 64) : Mem 64 → Prop :=
  fun m => ∃ ok, ElemState S che ac ok m

/-- **The SBR element at `che` is ready**: live, and the last parse succeeded (what
`ff_aac_sbr_apply` needs). -/
def Ready (S : Setup) (che ac : BitVec 64) : Mem 64 → Prop :=
  ElemState S che ac true

/-- The element's address facts: `che` 32-aligned, the element well below the top of the
address space (no wrap, and apply's signed address arithmetic in range). -/
def ElemOK (che : BitVec 64) : Prop :=
  isAligned 32 che = true ∧ (che + 0x28920#64 + 0x5fcc0#64).toInt + 1280 < 2 ^ 63
  ∧ (che + 0x28920#64).toNat + 0x60000 < 2 ^ 64

/-- A run of the code entered at `f` in state `t` either returns to `ra` in a state `s` with
`Q s`, or reaches an address in `stops`. -/
def Ends (f : Label) (t : MachineData) (ra : Int64) (Q : MachineData → Prop)
    (stops : Int64 → Prop) : Prop :=
  Eventually cenv.instrStep (fun st => (st.2 = ra ∧ Q st.1) ∨ stops st.2) (t, entry f)

/-- The allowed stops: `abort` (an `av_assert0` in `read_sbr_grid`) and the bounds trap `ud1` of
`read_sbr_envelope`. -/
abbrev Traps (a : Int64) : Prop := DecExt.DStops a

/-- No stop allowed. -/
abbrev NoStops (_ : Int64) : Prop := False

/-- The 32-bit return value. -/
abbrev ret32 (s : MachineData) : BitVec 32 := (s.regs.get64 .rax).setWidth 32

/-- `ff_aac_sbr_decode_extension`'s stack. -/
abbrev decStack (k : Nat) : Nat := DecExt.decNeed (decKc k)

/-- `ff_aac_sbr_decode_usac_data`'s stack. -/
abbrev usacStack (k : Nat) : Nat := Usac.usacNeed (usacK k)

/-- `ff_aac_sbr_apply`'s stack. -/
abbrev applyStack (k : Nat) : Nat := applyNeed k

/-- The objects of a `decode_usac_data` call, in plain terms. -/
structure UsacIn where
  /-- `ue` (the USAC element configuration). -/
  ue : BitVec 64
  /-- `gb` (the bit reader). -/
  g : BitVec 64
  /-- The reader's buffer. -/
  buf : BitVec 64
  /-- The reader's `size_in_bits_plus8`. -/
  p8 : BitVec 32
  /-- The buffer's length in bytes. -/
  L : Nat
  /-- The twelve bytes of `ue->sbr`. -/
  uev : List UInt8

/-- The parser's view of a `decode_usac_data` call. -/
def UsacIn.q (u : UsacIn) (che ac : BitVec 64) (Rc : Mem 64 → Prop) : Usac.UQ :=
  ⟨Rc, ac, che, u.ue, u.g, u.buf, u.p8, u.L, u.uev, fun _ => True, fun _ => True⟩

/-- A `decode_usac_data` call's objects: `*gb` at index `i`, the buffer, `ue->sbr`, the rest. -/
def UsacObjects (u : UsacIn) (che ac : BitVec 64) (Rc : Mem 64 → Prop) (i : BitVec 32) :
    Mem 64 → Prop :=
  UsacObj (u.q che ac Rc) i

/-- `ff_aac_sbr_apply`'s output buffers `L`, `R` (2048 floats each). -/
def OutBufs (t : MachineData) : Mem 64 → Prop := Blocks [(arg3 t, 8192), (arg4 t, 8192)]

/-- What the caller guarantees at a `ff_aac_sbr_decode_extension(ac, che, gb, crc, cnt, id)`
call. -/
structure DecCall (che ac : BitVec 64) (b : Rdr) (i : BitVec 32) (t : MachineData) : Prop where
  /-- `ac` and `che` are the first two arguments. -/
  args : arg0 t = ac ∧ arg1 t = che
  /-- The element's address facts. -/
  elem : ElemOK che
  /-- The reader's index and size are in bounds and its buffer is owned. -/
  rd : b.r.ok i
  /-- The stack is 16-aligned at the call (ABI). -/
  align : isAligned 16 (t.regs.get64 .rsp + 8#64) = true

/-- What the caller guarantees at a `ff_aac_sbr_decode_usac_data(ac, che, ue, gb, …)` call. -/
structure UsacCall (che ac : BitVec 64) (u : UsacIn) (i : BitVec 32) (t : MachineData) :
    Prop where
  /-- `ac`, `che`, `ue`, `gb` are the first four arguments. -/
  args : arg0 t = ac ∧ arg1 t = che ∧ arg2 t = u.ue ∧ arg3 t = u.g
  /-- The element's address facts. -/
  elem : ElemOK che
  /-- The reader's index is within `size_in_bits_plus8`, which fits its buffer. -/
  rd : i.toNat ≤ u.p8.toNat ∧ u.p8.toNat < 2 ^ 31 ∧ u.p8.toNat / 8 + 4 ≤ u.L ∧ u.L < 2 ^ 32
  /-- `ue->sbr` has twelve bytes; its default header's `start_freq` (4 bits), `limiter_bands`,
  `limiter_gains` (2 bits each) are in range. -/
  ue : u.uev.length = 12 ∧ u8 u.uev 1 < 16 ∧ u8 u.uev 6 < 4 ∧ u8 u.uev 7 < 4
  /-- `ue->sbr`'s default header `freq_scale` is in range (2 bits). -/
  uev3 : u8 u.uev 3 ≤ 3
  /-- The stack is 16-aligned at the call (ABI). -/
  align : isAligned 16 (t.regs.get64 .rsp + 8#64) = true

/-- What the caller guarantees at a `ff_aac_sbr_config_usac(ac, che, ue)` call. -/
structure ConfigCall (che ac : BitVec 64) (t : MachineData) : Prop where
  /-- `ac` and `che` are the first two arguments. -/
  args : arg0 t = ac ∧ arg1 t = che

/-- What the caller guarantees at a `ff_aac_sbr_apply(ac, che, id, L, R)` call. -/
structure ApplyCall (che ac : BitVec 64) (t : MachineData) : Prop where
  /-- `ac` and `che` are the first two arguments. -/
  args : arg0 t = ac ∧ arg1 t = che
  /-- The element's address facts. -/
  elem : ElemOK che
  /-- The output buffers are 32-aligned. -/
  out : isAligned 32 (arg3 t) = true ∧ isAligned 32 (arg4 t) = true
  /-- The stack is 16-aligned at the call (ABI). -/
  align : isAligned 16 (t.regs.get64 .rsp + 8#64) = true

end Kraken.Examples.Sbr.SessionBin

end

/-! ## §24. Init's external contracts and outcome

Lemmas about these: `SessionBin/InitSafe.lean`. -/

section

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Session Kraken.Examples.Sbr.Parse Kraken.Examples.Sbr.Init
namespace Kraken.Examples.Sbr.SessionBin
variable [CodeEnv]

/-- The external contracts at the caller's environment `S.env`, with init's state `X`. -/
structure InitExt (S : Setup) (X : Mem 64 → Prop) : Prop where
  /-- The stack reservation fits in 32 bits. -/
  kle : S.k ≤ 2 ^ 32
  /-- Init's externals (`av_tx_init`, `av_mallocz`, `av_free`, …). -/
  init : InitAssumed S.k S.env.Ctx S.env.TxTab X
  /-- `ff_ps_apply`. -/
  psApply : PsApplySpec S.env.PsTab S.k
  /-- `av_log` on the logging state. -/
  avLog : AvLogSpec S.env.Ext S.k
  /-- `memcpy`, as a value contract. -/
  memcpyV : MemcpyValSpec S.k
  /-- `memset`, as a value contract. -/
  memsetV : MemsetValSpec S.k
  /-- `avpriv_request_sample` on the logging state. -/
  avReq : DecExt.AvReqSpec S.env.Ext S.k
  /-- `powf` computes `S.pw`. -/
  powf : Reset.PowfSpec ⟨S.env.Ext, S.pw, S.lg⟩ S.k
  /-- `log2f` computes `S.lg`. -/
  log2f : Reset.Log2fSpec ⟨S.env.Ext, S.pw, S.lg⟩ S.k
  /-- The floating-point facts on `S.pw`, `S.lg`. -/
  bands : Reset.BandsOK S.lg S.pw
  /-- The `float_dsp` slots of `S.env`. -/
  fdsp : FdspOK S.env

/-- What the caller owns at the call besides `*che` and init's state: the `ac` fields, the
`ac->fdsp` cell, the `float_dsp` slots, the PS tables, `av_log`'s state, the constants, the
parser's static data, and the rest `Rest`. -/
abbrev InitOwn (S : Setup) (ac avctx fdsp : BitVec 64) (er ps : BitVec 32)
    (Rest : Mem 64 → Prop) : Mem 64 → Prop :=
  AcFields ac avctx er ps ⋆ (c8 (ac + 0x2550#64) fdsp ⋆ (FdspW S.env fdsp ⋆ (S.env.PsTab
    ⋆ (S.env.Ext ⋆ (CstW ⋆ (PStat S.vs S.vp ⋆ Rest))))))

/-- What `ff_aac_sbr_ctx_alloc_init(ac, che, id)` (called in `t`, returning to `ra`) leaves in
`s`. In every branch the caller gets back everything of `InitOwn`, the transforms' tables and
init's state `X`.
* `0`: an address `p` such that the element at `p` (of `ac`) is live, with the caller's `ac`
  fields, the cell `*che = p`, `X` and the rest.
* `-12` (`AVERROR(ENOMEM)`), `av_mallocz` failed: nothing was allocated; the caller owns the 8
  bytes at `che` as before.
* A negative result, the first `av_tx_init` (`sbr->mdct`) failed: the caller owns `*che = p` and
  the element at `p` with the cells stored so far (`evPre`), the 16 bytes of `sbr->mdct` and
  `sbr->mdct_fn` any bytes `bc`, `bf`.
* A negative result, the second `av_tx_init` (`sbr->mdct_ana`) failed: as the previous branch,
  but `sbr->mdct`, `sbr->mdct_fn` hold the first transform's context `c` (owned, `Ctx c`) and
  function `f`, and the 16 bytes of `sbr->mdct_ana`, `sbr->mdct_ana_fn` are any bytes.

`av_tx_init` may itself return `-12`, so the result alone does not tell which failure
branch holds. -/
def InitQ (S : Setup) (X Rest : Mem 64 → Prop) (avctx fdsp : BitVec 64) (er ps : BitVec 32)
    (ra : Int64) (t s : MachineData) : Prop :=
  (ret32 s = 0#32 ∧ ∃ p : BitVec 64, CallPost (initNeed S.k) (Live S p (arg0 t)
      ⋆ (AcFields (arg0 t) avctx er ps ⋆ (Apply.c8 (arg1 t) p ⋆ (X ⋆ Rest)))) ra t s)
  ∨ (ret32 s = 0xfffffff4#32 ∧ CallPost (initNeed S.k)
      ((8 ?@ arg1 t ⋆ (S.env.TxTab ⋆ X)) ⋆ InitOwn S (arg0 t) avctx fdsp er ps Rest) ra t s)
  ∨ ((ret32 s).toInt < 0 ∧ ∃ (p : BitVec 64) (bc bf : List UInt8), bc.length = 8
      ∧ bf.length = 8 ∧ CallPost (initNeed S.k) ((Apply.c8 (arg1 t) p
        ⋆ (ElemS p { evPre (idOf t) p with synC := bc, synF := bf } ⋆ (S.env.TxTab ⋆ X)))
        ⋆ InitOwn S (arg0 t) avctx fdsp er ps Rest) ra t s)
  ∨ ((ret32 s).toInt < 0 ∧ ∃ (p c : BitVec 64) (f : Int64) (bc bf : List UInt8), bc.length = 8
      ∧ bf.length = 8 ∧ CallPost (initNeed S.k) ((Apply.c8 (arg1 t) p
        ⋆ (ElemS p
            { evPre (idOf t) p with
              synC := Int.toBytes 8 c.toInt, synF := fb f, anaC := bc, anaF := bf }
          ⋆ (S.env.Ctx c ⋆ (S.env.TxTab ⋆ X))))
        ⋆ InitOwn S (arg0 t) avctx fdsp er ps Rest) ra t s)

end Kraken.Examples.Sbr.SessionBin

end

/-! ## §25. The headline's parts: `SbrBinary` and the five call contracts

Lemmas about these: `SessionBin/Top.lean`. -/

section

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Session Kraken.Examples.Sbr.Parse Kraken.Examples.Sbr.Init
namespace Kraken.Examples.Sbr.SessionBin
variable [CodeEnv]

/-- **The binary**: the placement of every text (init, the parser, apply's cluster) and the
layout facts of the link. Not proved in Lean; the evidence is translation validation, which
compares each Lean text with the linked object's bytes. -/
abbrev SbrBinary : Prop := SessPlaced

/-- `ff_aac_sbr_ctx_alloc_init(ac, che, id)`: with the caller's `ac` fields, `ac->fdsp`, the
static data and init's state, the call returns; on `0` the element at the new `*che` is live.
On failure the caller gets back exactly what it owned plus, depending on which call failed,
the partly built element (`InitQ`). -/
def InitSafe (S : Setup) (X : Mem 64 → Prop) : Prop :=
  ∀ {avctx fdsp : BitVec 64} {er ps : BitVec 32} {Rest : Mem 64 → Prop} {ra : Int64}
    {t : MachineData},
    InitPre S.k S.env.TxTab X (InitOwn S (arg0 t) avctx fdsp er ps Rest) ra t →
    Ends "ff_aac_sbr_ctx_alloc_init" t ra (InitQ S X Rest avctx fdsp er ps ra t) NoStops

/-- `ff_aac_sbr_decode_extension(ac, che, gb, crc, cnt, id)` on a live element: returns `cnt`
with the element ready, the reader advanced within its bound, the caller's objects given back
(`ext_sample_rate` possibly set); or stops at a trap. -/
def DecSafe (S : Setup) : Prop :=
  ∀ {che ac avctx : BitVec 64} {er ps : BitVec 32} {b : Rdr} {i : BitVec 32}
    {Rc : Mem 64 → Prop} {ra : Int64} {t : MachineData},
    DecCall che ac b i t →
    CallPre (decStack S.k) (Live S che ac ⋆ (AcFields ac avctx er ps ⋆ DecObj b avctx Rc i t))
      ra t →
    Ends "ff_aac_sbr_decode_extension" t ra (fun s => ∃ (i' : BitVec 32) (er' : BitVec 32),
      i'.toNat ≤ b.r.p8.toNat ∧ ret32 s = (arg4 t).setWidth 32
      ∧ CallPost (decStack S.k)
        (Ready S che ac ⋆ (AcFields ac avctx er' ps ⋆ DecObj b avctx Rc i' t)) ra t s) Traps

/-- `ff_aac_sbr_decode_usac_data(ac, che, ue, gb, …)` on a live element: returns with the
element live (ready if it returned `0`), the reader advanced within its bound, the caller's
objects given back; or stops at a trap. -/
def UsacSafe (S : Setup) : Prop :=
  ∀ {che ac avctx : BitVec 64} {er ps : BitVec 32} {u : UsacIn} {i : BitVec 32}
    {Rc : Mem 64 → Prop} {ra : Int64} {t : MachineData},
    UsacCall che ac u i t →
    CallPre (usacStack S.k)
      (Live S che ac ⋆ (AcFields ac avctx er ps ⋆ UsacObjects u che ac Rc i)) ra t →
    Ends "ff_aac_sbr_decode_usac_data" t ra (fun s => ∃ i' : BitVec 32,
      i'.toNat ≤ u.p8.toNat
      ∧ CallPost (usacStack S.k) (ElemState S che ac (decide (ret32 s = 0#32))
        ⋆ (AcFields ac avctx er ps ⋆ UsacObjects u che ac Rc i')) ra t s) Traps

/-- `ff_aac_sbr_config_usac(ac, che, ue)` on a live element: returns `0` with the element
ready (switched off) and the caller's objects given back. -/
def ConfigSafe (S : Setup) : Prop :=
  ∀ {che ac avctx : BitVec 64} {er ps : BitVec 32} {Rc : Mem 64 → Prop} {ra : Int64}
    {t : MachineData},
    ConfigCall che ac t →
    CallPre 0 (Live S che ac ⋆ (AcFields ac avctx er ps ⋆ Rc)) ra t →
    Ends "ff_aac_sbr_config_usac" t ra (fun s => ret32 s = 0#32
      ∧ CallPost 0 (Ready S che ac ⋆ (AcFields ac avctx er ps ⋆ Rc)) ra t s) NoStops

/-- `ff_aac_sbr_apply(ac, che, id, L, R)` on a ready element: returns with the element ready,
the output buffers and the caller's objects given back. -/
def ApplySafe (S : Setup) : Prop :=
  ∀ {che ac avctx : BitVec 64} {er ps : BitVec 32} {Rc : Mem 64 → Prop} {ra : Int64}
    {t : MachineData},
    ApplyCall che ac t →
    CallPre (applyStack S.k) (Ready S che ac ⋆ (AcFields ac avctx er ps ⋆ (OutBufs t ⋆ Rc)))
      ra t →
    Ends "ff_aac_sbr_apply" t ra (fun s => CallPost (applyStack S.k)
      (Ready S che ac ⋆ (AcFields ac avctx er ps ⋆ (OutBufs t ⋆ Rc))) ra t s) NoStops

end Kraken.Examples.Sbr.SessionBin

end
