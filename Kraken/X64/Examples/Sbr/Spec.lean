import Kraken.SysV
import Kraken.SeparationMem
import Kraken.X64.Examples.Sbr.SessionSpec

/-!
# `ff_aac_sbr_apply`: the specifications

Specifications of the procedures of FFmpeg's SBR decoder
(`libavcodec/aacsbr_template.c`, `libavcodec/x86/sbrdsp.asm`) that the
memory-safety proof of `ff_aac_sbr_apply` uses, in the style of
`EvenOddGhost/Spec.lean`: each is a `ProcSpec` at the procedure's label whose
logical variable is the caller's memory `R`, and whose pre- and postcondition
are the calling convention's `CallPre`/`CallPost` over the procedure's
footprint `F ⋆ R`, plus the procedure's own conditions (alignment, sizes).
This file holds specifications only; proofs are in `Dsp/*.lean` (the
`SBRDSPContext` routines), `QmfSynthesis.lean`, `LfGen.lean`,
`HfInverseFilter.lean`, `XGen.lean` and `HfAssemble.lean` (the C procedures).
The preconditions the C procedures need of the decoder state are collected in
the section "`SbrWF`" at the end.

## The `SBRDSPContext` routines (`libavcodec/sbrdsp.h`)

On x86-64 every slot is an SSE/SSE2/SSE3 routine (`ff_sbrdsp_init_x86`). The
C code reaches them only through `sbr->dsp`, so the proof of the C side is
parametric in the slot contents, and these specifications are what it
assumes of each slot.

The footprint of each routine is what `tests/checkasm/sbrdsp.c` and the call
sites in `libavcodec/aacsbr_template.c` give it, in bytes (`float` = 4). The
routines use no stack except `autocorrelate` (a 32-byte local area plus
alignment, `sub $0x28,%rsp`), and touch only caller-saved registers.

## Read-only data

The routines read constants of `sbrdsp.asm`'s `SECTION_RODATA` (`ps_mask`,
`ps_mask2`, `ps_mask3`, `ps_noise0`, `ps_noise2`, `ps_noise13`) and the
external tables `ff_sbr_noise_table` and `ff_ps_neg`, through `sym(%rip)`
operands (and one `ps_noise13+16(%rip)`). Each is a label of the ambient code;
its address is that label's (plus the offset).
A specification owns the constant's bytes (they are part of `F`) and assumes
its alignment where an aligned SSE operand reads it; the linking step
discharges both from the layout (`Program.label_aligned_of_align`, as in
`SbrNegOdd64.lean`). Their contents are never needed: the values read are
float bits, and memory safety does not depend on them.
-/

open Kraken
open Kraken.SysV
open Mem

namespace Kraken.Examples.Sbr

variable [CodeEnv]

/-! ## `neg_odd_64(float *z)`: `z[64]` read and written, `ps_mask2` read -/

abbrev NegOdd64F (t : MachineData) : Mem 64 → Prop :=
  Blocks [(arg0 t, 256), (lab "ps_mask2", 16)]

abbrev NegOdd64C (t : MachineData) : Prop :=
  isAligned 16 (arg0 t) = true ∧ isAligned 16 (lab "ps_mask2") = true

abbrev NegOdd64Spec : Prop := LeafSpec "ff_sbr_neg_odd_64_sse" 0 NegOdd64F NegOdd64C

/-! ## `sum64x5(float *z)`: `z[320]` read and written -/

abbrev Sum64x5F (t : MachineData) : Mem 64 → Prop :=
  Blocks [(arg0 t, 1280)]

abbrev Sum64x5C (t : MachineData) : Prop :=
  isAligned 16 (arg0 t) = true

abbrev Sum64x5Spec : Prop := LeafSpec "ff_sbr_sum64x5_sse" 0 Sum64x5F Sum64x5C

/-! ## `sum_square` -/

/-- The count `n` as the code reads it: the low 32 bits of `rsi`, unsigned. -/
abbrev sumSquareN (t : MachineData) : Nat := (arg1 t).toNat % 2 ^ 32

/-- `sum_square(float (*x)[2], int n)`: `x[n][2]` read, `8 * n` bytes. -/
abbrev SumSquareF (t : MachineData) : Mem 64 → Prop :=
  Blocks [(arg0 t, 8 * sumSquareN t)]

/-- No side condition: the loads are `movups`, and `n` may have any shape. -/
abbrev SumSquareC (_t : MachineData) : Prop := True

abbrev SumSquareSpec : Prop := LeafSpec "ff_sbr_sum_square_sse" 0 SumSquareF SumSquareC

/-! ## `qmf_pre_shuffle` -/

/-- `qmf_pre_shuffle(float *z)`: `z[128]` read and written, `ff_ps_neg` read. -/
abbrev QmfPreShuffleF (t : MachineData) : Mem 64 → Prop :=
  Blocks [(arg0 t, 512), (lab "ff_ps_neg", 16)]

abbrev QmfPreShuffleC (t : MachineData) : Prop :=
  isAligned 16 (arg0 t) = true ∧ isAligned 16 (lab "ff_ps_neg") = true

abbrev QmfPreShuffleSpec : Prop :=
  LeafSpec "ff_sbr_qmf_pre_shuffle_sse2" 0 QmfPreShuffleF QmfPreShuffleC

/-! ## `qmf_post_shuffle(float W[32][2], const float *z)` -/

/-- `W[32][2]` (256 bytes) written, `z[64]` (256 bytes) and `ff_ps_neg` read. -/
abbrev QmfPostShuffleF (t : MachineData) : Mem 64 → Prop :=
  Blocks [(arg0 t, 256), (arg1 t, 256), (lab "ff_ps_neg", 16)]

/-- Aligned `W`, `z`, `ff_ps_neg`; `z .. z + 240` below the signed boundary
(the exit is a signed pointer compare). -/
abbrev QmfPostShuffleC (t : MachineData) : Prop :=
  isAligned 16 (arg0 t) = true ∧ isAligned 16 (arg1 t) = true
  ∧ isAligned 16 (lab "ff_ps_neg") = true ∧ (arg1 t).toInt + 240 < 2 ^ 63

abbrev QmfPostShuffleSpec : Prop :=
  LeafSpec "ff_sbr_qmf_post_shuffle_sse" 0 QmfPostShuffleF QmfPostShuffleC

/-! ## `qmf_deint_neg` -/

/-- `qmf_deint_neg(float *v, const float *src)`: `v[64]` written, `src[64]`
read, `ff_ps_neg` (16 bytes) read. -/
abbrev QmfDeintNegF (t : MachineData) : Mem 64 → Prop :=
  Blocks [(arg0 t, 256), (arg1 t, 256), (lab "ff_ps_neg", 16)]

abbrev QmfDeintNegC (t : MachineData) : Prop :=
  isAligned 16 (arg0 t) = true ∧ isAligned 16 (arg1 t) = true
    ∧ isAligned 16 (lab "ff_ps_neg") = true

abbrev QmfDeintNegSpec : Prop :=
  LeafSpec "ff_sbr_qmf_deint_neg_sse" 0 QmfDeintNegF QmfDeintNegC

/-! ## `qmf_deint_bfly` -/

/-- `qmf_deint_bfly(v, src0, src1)`: `v[128]` written, `src0[64]`, `src1[64]` read. -/
abbrev QmfDeintBflyF (t : MachineData) : Mem 64 → Prop :=
  Blocks [(arg0 t, 512), (arg1 t, 256), (arg2 t, 256)]

abbrev QmfDeintBflyC (t : MachineData) : Prop :=
  isAligned 16 (arg0 t) = true ∧ isAligned 16 (arg1 t) = true
    ∧ isAligned 16 (arg2 t) = true

abbrev QmfDeintBflySpec : Prop :=
  LeafSpec "ff_sbr_qmf_deint_bfly_sse2" 0 QmfDeintBflyF QmfDeintBflyC

/-! ## `autocorrelate(const float x[40][2], float phi[3][2][2])` -/

abbrev AutocorrelateF (t : MachineData) : Mem 64 → Prop :=
  Blocks [(arg0 t, 320), (arg1 t, 48), (lab "ps_mask3", 16)]

abbrev AutocorrelateC (t : MachineData) : Prop :=
  isAligned 16 (arg1 t) = true ∧ isAligned 16 (lab "ps_mask3") = true
  ∧ isAligned 16 (t.regs.get64 .rsp + 8#64) = true

abbrev AutocorrelateSpec (l : Label) : Prop := LeafSpec l 0x28 AutocorrelateF AutocorrelateC

/-! ## `hf_gen` -/

/-- `start`, as `movslq %r8d,%r8` reads it: the low 32 bits, sign-extended. -/
abbrev HfGenS (t : MachineData) : BitVec 64 := ((arg4 t).setWidth 32).signExtend 64

/-- `end`, as `movslq %r9d,%r9` reads it. -/
abbrev HfGenE (t : MachineData) : BitVec 64 := ((arg5 t).setWidth 32).signExtend 64

/-- The bytes of `X_high[start..end)`: `8 * (end - start)`. -/
abbrev HfGenN (t : MachineData) : BitVec 64 := (HfGenE t - HfGenS t) * 8#64

/-- `&X_high[start]`. -/
abbrev HfGenXh (t : MachineData) : BitVec 64 := arg0 t + HfGenS t * 8#64

/-- `&X_low[start - 2]`. -/
abbrev HfGenXl (t : MachineData) : BitVec 64 := arg1 t + HfGenS t * 8#64 - 16#64

/-- `hf_gen(X_high, X_low, alpha0, alpha1, bw, start, end)`: `X_high[start..end)`
written, `X_low[start-2..end)` read, `alpha0[2]`, `alpha1[2]` read, `ps_mask`
(16 bytes) read. -/
abbrev HfGenF (t : MachineData) : Mem 64 → Prop :=
  Blocks [(HfGenXh t, (HfGenN t).toNat), (HfGenXl t, (HfGenN t).toNat + 16),
    (arg2 t, 8), (arg3 t, 8), (lab "ps_mask", 16)]

/-- `start < end` (as signed 32-bit integers), `end - start` even, both
array bases 16-byte aligned at `start`, `ps_mask` aligned. -/
abbrev HfGenC (t : MachineData) : Prop :=
  ((arg4 t).setWidth 32).toInt < ((arg5 t).setWidth 32).toInt
    ∧ (HfGenE t - HfGenS t).toNat % 2 = 0
    ∧ isAligned 16 (HfGenXh t) = true ∧ isAligned 16 (HfGenXl t) = true
    ∧ isAligned 16 (lab "ps_mask") = true

abbrev HfGenSpec : Prop := LeafSpec "ff_sbr_hf_gen_sse" 0 HfGenF HfGenC

/-! ## `hf_g_filt` -/

/-- The row count as the code computes it: `m_max & 0xfc` rows by fours, then
`m_max & 3` single rows, so the low 8 bits of `rcx`. -/
abbrev hfGFiltM (t : MachineData) : Nat := (arg3 t).toNat % 256

/-- `hf_g_filt(float (*Y)[2], const float (*X_high)[40][2], const float *g_filt,
int m_max, intptr_t ixh)`: `Y[m][2]` written, `X_high[m][40][2]` read,
`g_filt[m]` read, with `m` the row count. -/
abbrev HfGFiltF (t : MachineData) : Mem 64 → Prop :=
  Blocks [(arg0 t, 8 * hfGFiltM t), (arg1 t, 320 * hfGFiltM t), (arg2 t, 4 * hfGFiltM t)]

/-- `ixh < 40`; at least one row; and when the low 8 bits of `rcx` are below 4
(no row by fours), all of `rcx` is (the single-row loop counts the whole
register down). -/
abbrev HfGFiltC (t : MachineData) : Prop :=
  (arg4 t).toNat < 40 ∧ 1 ≤ hfGFiltM t ∧ (hfGFiltM t < 4 → (arg3 t).toNat < 4)

abbrev HfGFiltSpec : Prop := LeafSpec "ff_sbr_hf_g_filt_sse" 0 HfGFiltF HfGFiltC

/-! ## `hf_apply_noise_k` -/

/-- `m_max`, the low 32 bits of `r9`. -/
abbrev HfApplyNoiseM (t : MachineData) : Nat := (arg5 t).toNat % 2 ^ 32

/-- Iterations of the loop (four elements each): `⌈m_max / 4⌉`. -/
abbrev HfApplyNoiseIt (t : MachineData) : Nat := (HfApplyNoiseM t + 3) / 4

abbrev HfApplyNoiseMainF (t : MachineData) : Mem 64 → Prop :=
  Blocks [(arg0 t, 32 * HfApplyNoiseIt t), (arg1 t, 16 * HfApplyNoiseIt t),
    (arg2 t, 16 * HfApplyNoiseIt t), (lab "ff_sbr_noise_table", 4160)]

abbrev HfApplyNoiseMainC (t : MachineData) : Prop :=
  isAligned 16 (arg1 t) = true ∧ isAligned 16 (arg2 t) = true
    ∧ 1 ≤ HfApplyNoiseM t ∧ HfApplyNoiseM t < 2 ^ 28
    ∧ (arg3 t).toNat % 2 ^ 32 ≤ 515

abbrev HfApplyNoiseMainSpec : Prop :=
  LeafSpec "apply_noise_main" 0 HfApplyNoiseMainF HfApplyNoiseMainC

/-- The footprint of entry `k`: `apply_noise_main`'s, plus the `phi_sign`
constant `c` the entry loads into `xmm0` (16 bytes for `k = 0, 2`; 32 for
`k = 1, 3`, which pick one of two 16-byte halves by `kx & 1`). -/
abbrev HfApplyNoiseF (c : BitVec 64 × Nat) (t : MachineData) : Mem 64 → Prop :=
  Blocks [(arg0 t, 32 * HfApplyNoiseIt t), (arg1 t, 16 * HfApplyNoiseIt t),
    (arg2 t, 16 * HfApplyNoiseIt t), (lab "ff_sbr_noise_table", 4160), c]

abbrev HfApplyNoiseC (c : BitVec 64) (t : MachineData) : Prop :=
  HfApplyNoiseMainC t ∧ isAligned 16 c = true

/-- The constants of the four entries (`.rodata` of `sbrdsp.asm`). -/
abbrev HfApplyNoiseK0 : BitVec 64 × Nat := (lab "ps_noise0", 16)
abbrev HfApplyNoiseK1 : BitVec 64 × Nat := (lab "ps_noise13", 32)
abbrev HfApplyNoiseK2 : BitVec 64 × Nat := (lab "ps_noise2", 16)
/-- `ps_noise13` is three 16-byte rows (48 bytes); entry 1 reads rows 0 and 1,
entry 3 (`ps_noise13+16(%rip)`) rows 1 and 2. -/
abbrev HfApplyNoiseK3 : BitVec 64 × Nat := (lab "ps_noise13" + 16#64, 32)

abbrev HfApplyNoise0Spec : Prop := LeafSpec "ff_sbr_hf_apply_noise_0_sse2" 0
  (HfApplyNoiseF HfApplyNoiseK0) (HfApplyNoiseC HfApplyNoiseK0.1)
abbrev HfApplyNoise1Spec : Prop := LeafSpec "ff_sbr_hf_apply_noise_1_sse2" 0
  (HfApplyNoiseF HfApplyNoiseK1) (HfApplyNoiseC HfApplyNoiseK1.1)
abbrev HfApplyNoise2Spec : Prop := LeafSpec "ff_sbr_hf_apply_noise_2_sse2" 0
  (HfApplyNoiseF HfApplyNoiseK2) (HfApplyNoiseC HfApplyNoiseK2.1)
abbrev HfApplyNoise3Spec : Prop := LeafSpec "ff_sbr_hf_apply_noise_3_sse2" 0
  (HfApplyNoiseF HfApplyNoiseK3) (HfApplyNoiseC HfApplyNoiseK3.1)

/-- The four `hf_apply_noise[k]` slots. -/
abbrev HfApplyNoiseSpec : Prop :=
  HfApplyNoise0Spec ∧ HfApplyNoise1Spec ∧ HfApplyNoise2Spec ∧ HfApplyNoise3Spec

/-! ## All of `SBRDSPContext` -/

/-- The specifications of every `SBRDSPContext` routine the x86-64 build
installs (`ff_sbrdsp_init_x86`): both `autocorrelate` variants (SSE, SSE3) and
the four `hf_apply_noise[k]` entries. Proved in `Dsp.lean`. -/
def SbrDspSpecs : Prop :=
  NegOdd64Spec ∧ Sum64x5Spec ∧ SumSquareSpec ∧ QmfPreShuffleSpec ∧ QmfPostShuffleSpec
    ∧ QmfDeintNegSpec ∧ QmfDeintBflySpec
    ∧ AutocorrelateSpec "ff_sbr_autocorrelate_sse" ∧ AutocorrelateSpec "ff_sbr_autocorrelate_sse3"
    ∧ HfGenSpec ∧ HfGFiltSpec ∧ HfApplyNoiseSpec


/-! ## `sbr_qmf_synthesis` (`libavcodec/aacsbr_template.c`)

The first C procedure of the cluster. It reaches its callees through function
pointers: three `SBRDSPContext` slots (`neg_odd_64`, `qmf_deint_neg`,
`qmf_deint_bfly`, specified above), two `AVFloatDSPContext` slots
(`vector_fmul`, `vector_fmul_add`) and the `av_tx` function `mdct_fn`, plus a
direct call to `memcpy`. The `SBRDSPContext` contracts are the proved ones; the
others are *assumed* (decisions 2 and 3 of the plan) and stated below as
`LeafSpecAt` contracts with explicit footprints. All callees may use `k`
bytes of stack (the `SBRDSPContext` routines use none). -/

/-- `len` of `vector_fmul`, the low 32 bits of `rcx` (`int`). -/
abbrev fmulN (t : MachineData) : Nat := (arg3 t).toNat % 2 ^ 32

/-- `vector_fmul(dst, src0, src1, len)` (`libavutil/float_dsp.h`):
`dst[len]` written, `src0[len]`, `src1[len]` read, the three disjoint, 32-byte
aligned, `len` a multiple of 16 with `1 ≤ len < 2 ^ 30` (the routines are
do-while loops, `libavutil/x86/float_dsp.asm`). Proved of the two x86 routines
(`Dsp/VectorFmul.lean`). -/
abbrev VectorFmulF (t : MachineData) : Mem 64 → Prop :=
  Blocks [(arg0 t, 4 * fmulN t), (arg1 t, 4 * fmulN t), (arg2 t, 4 * fmulN t)]

abbrev VectorFmulC (t : MachineData) : Prop :=
  fmulN t % 16 = 0 ∧ 1 ≤ fmulN t ∧ fmulN t < 2 ^ 30
    ∧ isAligned 32 (arg0 t) = true ∧ isAligned 32 (arg1 t) = true
    ∧ isAligned 32 (arg2 t) = true

abbrev VectorFmulSpec (need : Nat) (f : Int64) : Prop :=
  LeafSpecAt f need VectorFmulF VectorFmulC

/-- `len` of `vector_fmul_add`, the low 32 bits of `r8`. -/
abbrev fmulAddN (t : MachineData) : Nat := (arg4 t).toNat % 2 ^ 32

/-- `vector_fmul_add(dst, src0, src1, src2, len)`
(`libavutil/float_dsp.h`) in the form `sbr_qmf_synthesis` calls it, with
`src2 = dst`: `dst[len]` read and written, `src0[len]`, `src1[len]` read,
disjoint, 32-byte aligned, `len` a multiple of 16 with `1 ≤ len < 2 ^ 30`
(do-while loop). Proved of the three x86 routines (`Dsp/VectorFmulAdd.lean`). -/
abbrev VectorFmulAddF (t : MachineData) : Mem 64 → Prop :=
  Blocks [(arg0 t, 4 * fmulAddN t), (arg1 t, 4 * fmulAddN t), (arg2 t, 4 * fmulAddN t)]

abbrev VectorFmulAddC (t : MachineData) : Prop :=
  arg3 t = arg0 t ∧ fmulAddN t % 16 = 0 ∧ 1 ≤ fmulAddN t ∧ fmulAddN t < 2 ^ 30
    ∧ isAligned 32 (arg0 t) = true
    ∧ isAligned 32 (arg1 t) = true ∧ isAligned 32 (arg2 t) = true

abbrev VectorFmulAddSpec (need : Nat) (f : Int64) : Prop :=
  LeafSpecAt f need VectorFmulAddF VectorFmulAddC

/-- What the callees must meet: the three proved `SBRDSPContext` contracts at
the slot contents, and the assumed `av_tx`, `vector_fmul`, `vector_fmul_add`
and `memcpy` contracts with `k` bytes of stack. -/
abbrev QmfCallees (k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (TxTab : Mem 64 → Prop)
    (fs : QmfFns) : Prop :=
  LeafSpecAt fs.negOdd64 0 NegOdd64F NegOdd64C
    ∧ LeafSpecAt fs.deintNeg 0 QmfDeintNegF QmfDeintNegC
    ∧ LeafSpecAt fs.deintBfly 0 QmfDeintBflyF QmfDeintBflyC
    ∧ TxSpec Ctx TxTab k fs.tx ∧ VectorFmulSpec k fs.fmul ∧ VectorFmulAddSpec k fs.fmulAdd
    ∧ MemcpySpec k

/-- The logical variables: the caller's memory, the four stack arguments
(`mdct_buf`, `v0`, `v_off`; `div` is a parameter of the specification) and the
value `*v_off` on entry. -/
structure QmfArgs where
  R : Mem 64 → Prop
  mdctBuf : BitVec 64
  v0 : BitVec 64
  vOff : BitVec 64
  off : BitVec 32

/-- The stack: 0x128 own bytes (six saved registers, 31 spill slots), the
return-address slot of the calls, and the callees' `k`. -/
abbrev qmfNeed (k : Nat) : Nat := 0x130 + k

/-- The QMF window the code reads (`div ? sbr_qmf_window_ds :
sbr_qmf_window_us`, both `.lrodata` of `aacsbr.o`): 640 floats, or 320 when
downsampled. -/
abbrev qmfWin (d : Nat) : BitVec 64 :=
  if d = 0 then lab "sbr_qmf_window_us" else lab "sbr_qmf_window_ds"

/-- The bytes of `v0` the code may touch for `div = d` and entry `*v_off = off`:
9216 (`v0[2304]`, `synthesis_filterbank_samples`), or 11264 under the condition below,
where after the first step `off' ∈ (1024, 1536]` and the window reads reach float
`off' + 1280 ≤ 2816` (the caller carves the extra 2048 bytes with `a3_overread_carve`).
Writes stay inside `v0[2304]`. -/
abbrev qmfVSize (d : Nat) (off : BitVec 32) : Nat :=
  if d = 0 ∧ 1152 < off.toInt then 11264 else 9216

/-- The data `sbr_qmf_synthesis` touches except `X`, with `VC` the 4 bytes of
`*v_off`: `mdct_buf[2][64]` (two 256-byte halves), `v0` (`qmfVSize d x.off`
bytes: `synthesis_filterbank_samples`, plus for the larger window the 2048 bytes
after it), `out[32 * (64 >> div)]`, the window, the
sign-mask constant of the downsampled path (`.LCPI15_1`, 4 bytes), the
constants of the `SBRDSPContext` routines, the five function-pointer slots it
loads (`sbrdsp->neg_odd_64`, `->qmf_deint_neg`, `->qmf_deint_bfly`,
`fdsp->vector_fmul`, `->vector_fmul_add`), the `av_tx` context and the `av_tx`
tables `TxTab`. -/
abbrev QmfData' (d : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (TxTab : Mem 64 → Prop)
    (fs : QmfFns) (x : QmfArgs) (t : MachineData) (VC : Mem 64 → Prop) : Mem 64 → Prop :=
  256 ?@ x.mdctBuf ⋆ (256 ?@ (x.mdctBuf + 256#64) ⋆ (qmfVSize d x.off ?@ x.v0 ⋆ (VC
    ⋆ ((8192 >>> d) ?@ arg4 t ⋆ ((2560 >>> d) ?@ qmfWin d ⋆ (4 ?@ lab "LCPI15_1"
    ⋆ (16 ?@ lab "ps_mask2" ⋆ (16 ?@ lab "ff_ps_neg"
    ⋆ (FnCell (arg2 t + 0x10#64) fs.negOdd64 ⋆ (FnCell (arg2 t + 0x28#64) fs.deintNeg
    ⋆ (FnCell (arg2 t + 0x30#64) fs.deintBfly ⋆ (FnCell (arg3 t) fs.fmul
    ⋆ (FnCell (arg3 t + 0x30#64) fs.fmulAdd ⋆ (Ctx (arg0 t) ⋆ TxTab))))))))))))))

/-- All the data: `X[2][38][64]` (19456 bytes) in front, as a `Blocks` list so
that accesses at offsets into it are found. -/
abbrev QmfData (d : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (TxTab : Mem 64 → Prop)
    (fs : QmfFns) (x : QmfArgs) (t : MachineData) (VC : Mem 64 → Prop) : Mem 64 → Prop :=
  Blocks [(arg5 t, 19456)] ⋆ QmfData' d Ctx TxTab fs x t VC

/-- The stack arguments, in the caller's frame above the return address:
`mdct_buf`, `v0`, `v_off` (8 bytes each) and the low 4 bytes of `div`. -/
abbrev QmfArgCells (d : Nat) (x : QmfArgs) (t : MachineData) : Mem 64 → Prop :=
  let r := t.regs.get64 .rsp
  Int.toBytes 8 x.mdctBuf.toInt =@ (r + 8#64) ⋆ (Int.toBytes 8 x.v0.toInt =@ (r + 16#64)
    ⋆ (Int.toBytes 8 x.vOff.toInt =@ (r + 24#64) ⋆ Int.toBytes 4 (d : Int) =@ (r + 32#64)))

/-- The footprint on entry: the data with `*v_off = off`, the stack arguments. -/
abbrev QmfF (d : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (TxTab : Mem 64 → Prop)
    (fs : QmfFns) (x : QmfArgs) (t : MachineData) : Mem 64 → Prop :=
  QmfData d Ctx TxTab fs x t (Int.toBytes 4 x.off.toInt =@ x.vOff) ⋆ QmfArgCells d x t

/-- The `*v_off` cell at `a` on return: some `int` value `v`, at most 1664 and a
multiple of 8 (what `QmfC` asks of the value on entry, so that the next call's
condition holds again; `aacsbr_template.c:1427-1432`). -/
def VOffW (a : BitVec 64) : Mem 64 → Prop :=
  fun m => ∃ v : BitVec 32, v.toInt ≤ 1664 ∧ v.toNat % 8 = 0 ∧ (Int.toBytes 4 v.toInt =@ a) m

/-- The footprint on return: `*v_off` changed, within the bounds of `VOffW`. -/
abbrev QmfFPost (d : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (TxTab : Mem 64 → Prop)
    (fs : QmfFns) (x : QmfArgs) (t : MachineData) : Mem 64 → Prop :=
  QmfData d Ctx TxTab fs x t (VOffW x.vOff) ⋆ QmfArgCells d x t

/-- The side conditions: `div ∈ {0, 1}`; `rsi` holds `mdct_fn`; the alignments
the callees ask for (`X` 16; `mdct_buf`, `v0`, `out`, the window 32 — `mdct_buf`
is `qmf_filter_scratch`, `DECLARE_ALIGNED(32, …)`; the `SBRDSPContext`
constants 16); and `*v_off` (a signed `int`) at most 1664 and a multiple of 8
(the invariant of the synthesis buffer, `aacsbr_template.c:88-89, 1427-1432`; the
size of the `v0` footprint depends on it, see `qmfVSize`). -/
abbrev QmfC (d : Nat) (fs : QmfFns) (x : QmfArgs) (t : MachineData) : Prop :=
  d ≤ 1 ∧ Int64.ofBitVec (arg1 t) = fs.tx
    ∧ isAligned 16 (arg5 t) = true ∧ isAligned 32 x.mdctBuf = true
    ∧ isAligned 32 x.v0 = true ∧ isAligned 32 (arg4 t) = true
    ∧ isAligned 32 (qmfWin d) = true
    ∧ isAligned 16 (lab "ps_mask2") = true ∧ isAligned 16 (lab "ff_ps_neg") = true
    ∧ x.off.toInt ≤ 1664 ∧ x.off.toNat % 8 = 0

abbrev QmfPre (d k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (TxTab : Mem 64 → Prop)
    (fs : QmfFns) (x : QmfArgs) (ra : Int64) (t : MachineData) : Prop :=
  CallPre (qmfNeed k) (QmfF d Ctx TxTab fs x t ⋆ x.R) ra t ∧ QmfC d fs x t

abbrev QmfPost (d k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (TxTab : Mem 64 → Prop)
    (fs : QmfFns) (x : QmfArgs) (ra : Int64) (t s : MachineData) : Prop :=
  CallPost (qmfNeed k) (QmfFPost d Ctx TxTab fs x t ⋆ x.R) ra t s

/-- `sbr_qmf_synthesis(mdct, mdct_fn, sbrdsp, fdsp, out, X, mdct_buf, v0,
v_off, div)` at `div = d`, its callees at `fs`, `k` bytes of stack for them,
the `av_tx` context `Ctx` and tables `TxTab`. -/
abbrev QmfSynthesisSpec (d k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop)
    (TxTab : Mem 64 → Prop) (fs : QmfFns) : Prop :=
  cenv.ProcSpec (entry "sbr_qmf_synthesis") (QmfPre d k Ctx TxTab fs)
    (QmfPost d k Ctx TxTab fs)

/-! ## `sbr_lf_gen` (`libavcodec/aacsbr_template.c`)

Reached through `sbr->c.sbr_lf_gen`. Assumed callee: `memset`
(`MemsetSpec k`). Proof: `LfGen.lean`. -/

/-- The logical variables of `sbr_lf_gen`: the caller's memory and the values
of `sbr->kx[0]`, `sbr->kx[1]`. -/
structure LfGenArgs where
  R : Mem 64 → Prop
  kx0 : Nat
  kx1 : Nat

/-- `buf_idx`, the low 32 bits of `rcx` (`movslq %r12d,%rax`). -/
abbrev lfBuf (t : MachineData) : Nat := (arg3 t).toNat % 2 ^ 32

/-- The two `int` cells `sbr->kx[0]` (`sbr + 0x54`) and `sbr->kx[1]` (`sbr + 0x58`). -/
abbrev LfGenKx (x : LfGenArgs) (t : MachineData) : Mem 64 → Prop :=
  Int.toBytes 4 (x.kx0 : Int) =@ (arg0 t + 0x54#64)
    ⋆ Int.toBytes 4 (x.kx1 : Int) =@ (arg0 t + 0x58#64)

/-- `sbr_lf_gen(sbr, X_low, W, buf_idx)`: `X_low[32][40][2]` (10240 bytes)
written, `W[2][32][32][2]` (16384 bytes) read, the two `kx` cells read. -/
abbrev LfGenF (x : LfGenArgs) (t : MachineData) : Mem 64 → Prop :=
  Blocks [(arg1 t, 10240), (arg2 t, 16384)] ⋆ LfGenKx x t

/-- `buf_idx ∈ {0, 1}`, `kx[0], kx[1] ≤ 32`. -/
abbrev LfGenC (x : LfGenArgs) (t : MachineData) : Prop :=
  lfBuf t ≤ 1 ∧ x.kx0 ≤ 32 ∧ x.kx1 ≤ 32

/-- Five saved registers (0x28), `memset`'s return address slot, its `k`. -/
abbrev lfNeed (k : Nat) : Nat := 0x30 + k

abbrev LfGenPre (k : Nat) (x : LfGenArgs) (ra : Int64) (t : MachineData) : Prop :=
  CallPre (lfNeed k) (LfGenF x t ⋆ x.R) ra t ∧ LfGenC x t

abbrev LfGenPost (k : Nat) (x : LfGenArgs) (ra : Int64) (t s : MachineData) : Prop :=
  CallPost (lfNeed k) (LfGenF x t ⋆ x.R) ra t s

abbrev LfGenSpec (k : Nat) : Prop :=
  cenv.ProcSpec (entry "sbr_lf_gen") (LfGenPre k) (LfGenPost k)

/-! ## `sbr_hf_inverse_filter` (`libavcodec/aacsbr_template.c`)

Reached through `sbr->c.sbr_hf_inverse_filter`. Assumed callee: the
`autocorrelate` contract at the slot `dsp->autocorrelate`
(`HfInvCallees fa`). Proof: `HfInverseFilter.lean`. -/

/-- `k0`, the low 32 bits of `r8` (`int`), as an unsigned number (the
specification asks `k0 ≤ 32`, so it is the signed value too). -/
abbrev hfInvN (t : MachineData) : Nat := (arg4 t).toNat % 2 ^ 32

/-- `sbr_hf_inverse_filter(dsp, alpha0, alpha1, X_low, k0)`
(`libavcodec/aacsbr.c`): `X_low[k0][40][2]` read (320 bytes per row, handed
row by row to `dsp->autocorrelate`), `alpha0[k0][2]` and `alpha1[k0][2]`
written (8 bytes per row), the three constants of the routine (`.LCPI19_0`
= `-1.000001f`, `.LCPI19_1` = `16.0f`, `.LCPI19_2` the 16-byte sign mask of
the negation, all `.rodata.cst*` of `aacsbr.o`) and `ps_mask3` (read by the
callee) read, and the function-pointer slot `dsp->autocorrelate`
(`0x38(%rdi)`) holding the callee's address `fa`. -/
abbrev HfInvF (fa : Int64) (t : MachineData) : Mem 64 → Prop :=
  Blocks [(arg3 t, 320 * hfInvN t), (arg1 t, 8 * hfInvN t), (arg2 t, 8 * hfInvN t),
    (lab "LCPI19_0", 4), (lab "LCPI19_1", 4), (lab "LCPI19_2", 16), (lab "ps_mask3", 16)]
  ⋆ FnCell (arg0 t + 0x38#64) fa

/-- `k0 ≤ 32` (`X_low` has 32 rows; SbrWF, see the notes), `ps_mask3`
16-aligned (the callee's `xorps`), and the SysV stack alignment (`rsp + 8`
16-aligned at entry), which makes the local `phi` (`LOCAL_ALIGNED_16`) and
the callee's frame aligned. -/
abbrev HfInvC (t : MachineData) : Prop :=
  hfInvN t ≤ 32 ∧ isAligned 16 (lab "ps_mask3") = true
    ∧ isAligned 16 (t.regs.get64 .rsp + 8#64) = true

/-- Stack: the own 0x78 bytes (six saved registers, three spill slots, the
48-byte `phi`), the callee's return-address slot and its 0x28 bytes. -/
abbrev hfInvNeed : Nat := 0xa8

abbrev HfInvPre (fa : Int64) (R : Mem 64 → Prop) (ra : Int64) (t : MachineData) : Prop :=
  CallPre hfInvNeed (HfInvF fa t ⋆ R) ra t ∧ HfInvC t

abbrev HfInvPost (fa : Int64) (R : Mem 64 → Prop) (ra : Int64) (t s : MachineData) : Prop :=
  CallPost hfInvNeed (HfInvF fa t ⋆ R) ra t s

/-- `sbr_hf_inverse_filter` with `dsp->autocorrelate = fa`. -/
abbrev HfInverseFilterSpec (fa : Int64) : Prop :=
  cenv.ProcSpec (entry "sbr_hf_inverse_filter") (HfInvPre fa) (HfInvPost fa)

/-- What the callee must meet: the `autocorrelate` contract of `Spec.lean`
at the slot's content (`AutocorrelateSpec l` is this at `fa = entry l`). -/
abbrev HfInvCallees (fa : Int64) : Prop := LeafSpecAt fa 0x28 AutocorrelateF AutocorrelateC

/-! ## `sbr_x_gen` (`libavcodec/aacsbr_template.c`)

Reached through `sbr->c.sbr_x_gen`. Assumed callee: `memset`
(`MemsetSpec k`). Proof: `XGen.lean`. -/

/-- The logical variables of `sbr_x_gen`: the caller's memory and the decoder
fields the code reads (`sbr->kx[0..1]`, `sbr->m[0..1]`,
`sbr->data[ch].t_env_num_env_old`). -/
structure XGenArgs where
  R : Mem 64 → Prop
  kx0 : BitVec 32
  kx1 : BitVec 32
  m0 : BitVec 32
  m1 : BitVec 32
  te : BitVec 8

/-- `ch`, the low 32 bits of `r9`. -/
abbrev xgCh (t : MachineData) : Nat := (arg5 t).toNat % 2 ^ 32

/-- `&sbr->data[ch].t_env_num_env_old` (`SBRData` is 0x15ac0 bytes at
`sbr + 0x80`; the field is at 0x15aa5 in it). -/
abbrev xgTe (t : MachineData) : BitVec 64 := arg0 t + BitVec.ofNat 64 (0x15b25 + 0x15ac0 * xgCh t)

/-- A 1-byte field holding `v`. -/
abbrev cell1 (a : BitVec 64) (v : BitVec 8) : Mem 64 → Prop := Int.toBytes 1 v.toInt =@ a

/-- The fields of `*sbr` read, in front of `K`. -/
abbrev XGenSbrL (x : XGenArgs) (t : MachineData) (K : Mem 64 → Prop) : Mem 64 → Prop :=
  cell4 (arg0 t + 0x54#64) x.kx0 ⋆ (cell4 (arg0 t + 0x58#64) x.kx1 ⋆ (cell4 (arg0 t + 0x5c#64) x.m0
    ⋆ (cell4 (arg0 t + 0x60#64) x.m1 ⋆ (cell1 (xgTe t) x.te ⋆ K))))

/-- The arrays: `X[2][38][64]` (19456 bytes, written), `X_low[32][40][2]`
(10240 bytes), `Y0[38][64][2]` and `Y1[38][64][2]` (19456 bytes each), read. -/
abbrev XGenData (t : MachineData) : Mem 64 → Prop :=
  Blocks [(arg1 t, 0x4c00), (arg4 t, 10240), (arg2 t, 19456), (arg3 t, 19456)]

/-- `sbr_x_gen(sbr, X, Y0, Y1, X_low, ch)`'s footprint: the arrays and the fields. -/
abbrev XGenF (x : XGenArgs) (t : MachineData) : Mem 64 → Prop :=
  XGenData t ⋆ XGenSbrL x t Std.ExtHashMap.emp

/-- `i_Temp = FFMAX(2 * t_env_num_env_old - 32, 0)`. -/
def xgIT (x : XGenArgs) : Nat := if 17 ≤ x.te.toNat then 2 * x.te.toNat - 32 else 0

/-- The side conditions (the `SbrWF` clauses of `sbr_x_gen`): `ch < 2`;
`kx[0], kx[1] ≤ 32` (rows of `X_low`); `kx[i] + m[i] ≤ 64` (columns of `X`,
the build's bounds checks); `t_env_num_env_old ≤ 19` (rows of `Y0`). -/
abbrev XGenC (x : XGenArgs) (t : MachineData) : Prop :=
  xgCh t < 2 ∧ x.kx0.toNat ≤ 32 ∧ x.kx1.toNat ≤ 32 ∧ x.kx0.toNat + x.m0.toNat ≤ 64
    ∧ x.kx1.toNat + x.m1.toNat ≤ 64 ∧ x.te.toNat ≤ 19

/-- The stack: 0x58 own bytes (six saved registers, five slots), the return
address of the `memset` call, and `memset`'s `k`. -/
abbrev xgNeed (k : Nat) : Nat := 0x60 + k

abbrev XGenPre (k : Nat) (x : XGenArgs) (ra : Int64) (t : MachineData) : Prop :=
  CallPre (xgNeed k) (XGenF x t ⋆ x.R) ra t ∧ XGenC x t

abbrev XGenPost (k : Nat) (x : XGenArgs) (ra : Int64) (t s : MachineData) : Prop :=
  CallPost (xgNeed k) (XGenF x t ⋆ x.R) ra t s

/-- `sbr_x_gen` with `memset` using `k` bytes of stack. -/
abbrev XGenSpec (k : Nat) : Prop :=
  cenv.ProcSpec (entry "sbr_x_gen") (XGenPre k) (XGenPost k)

/-! ## `sbr_hf_assemble` (`libavcodec/aacsbr_template.c`)

Reached through `sbr->c.sbr_hf_assemble`. Callees: `hf_g_filt` and the four
`hf_apply_noise[k]` (the proved `SBRDSPContext` contracts, at the slot
contents) and the assumed `memcpy` (`HfCallees k fs`). Proof:
`HfAssemble.lean`. -/

/-- The callees: the proved `SBRDSPContext` contracts at the slot contents (no
stack) and the assumed `memcpy` with `k` bytes of stack. -/
abbrev HfCallees (k : Nat) (fs : HfFns) : Prop :=
  LeafSpecAt fs.gfilt 0 HfGFiltF HfGFiltC
    ∧ LeafSpecAt fs.noise0 0 (HfApplyNoiseF HfApplyNoiseK0) (HfApplyNoiseC HfApplyNoiseK0.1)
    ∧ LeafSpecAt fs.noise1 0 (HfApplyNoiseF HfApplyNoiseK1) (HfApplyNoiseC HfApplyNoiseK1.1)
    ∧ LeafSpecAt fs.noise2 0 (HfApplyNoiseF HfApplyNoiseK2) (HfApplyNoiseC HfApplyNoiseK2.1)
    ∧ LeafSpecAt fs.noise3 0 (HfApplyNoiseF HfApplyNoiseK3) (HfApplyNoiseC HfApplyNoiseK3.1)
    ∧ MemcpySpec k

/-- The logical variables: the caller's memory and the decoder-state values the
code reads (`sbr->reset`, `sbr->bs_smoothing_mode`, `sbr->kx[1]`, `sbr->m[1]`,
`ch_data->bs_num_env`, `ch_data->t_env[0..8]` and `t_env_num_env_old` as
`te 0..9`, `e_a[0..1]`, and the 8 bytes `f_indexnoise`/`f_indexsine`). -/
structure HfArgs where
  R : Mem 64 → Prop
  reset : BitVec 32
  smooth : BitVec 32
  kx : Nat
  m : Nat
  nenv : Nat
  te : Nat → Nat
  ea0 : BitVec 32
  ea1 : BitVec 32
  idx : BitVec 64
  /-- `ch_data->Ypos`: `Y1 = ch_data->Y[ypos]` (`aacsbr_template.c:1743`). -/
  ypos : Nat

/-- The stack: 0x288 own bytes (six saved registers, the spill slots,
`g_filt_tab`/`q_filt_tab`), the callees' return-address slot, their `k`. -/
abbrev hfNeed (k : Nat) : Nat := 0x290 + k

omit [CodeEnv] in
/-- `hf_apply_noise` (SSE2) on a row of `Y` (512 bytes:
`[64][2]` floats) writes the byte window `[8kx, 8kx + 32⌈m/4⌉)` of that row.
With `kx + m ≤ 64` the window lies in the row and the first 24 bytes of the
next one, and it leaves the row exactly when `kx + 4⌈m/4⌉ > 64`. This is the
only way `HfAssemble.lean` may cross a row of `Y` (the row-crossing discipline,
checked by `tv.sh`). (`1 ≤ m`, true at every call, is not needed.) -/
theorem a2_row_spill (kx m : Nat) (h : kx + m ≤ 64) :
    8 * kx + 32 * ((m + 3) / 4) ≤ 512 + 24
      ∧ (8 * kx + 32 * ((m + 3) / 4) > 512 ↔ kx + 4 * ((m + 3) / 4) > 64) := by
  omega

/-- The arrays: `Y1 = ch_data->Y[ypos]` (`[38][64][2]` floats, at
`ch_data + 0x7930 + 19456·ypos`), the 24 bytes right after it, the rest of
`ch_data->g_temp`/`q_temp` (`[42][48]` each, contiguous at
`ch_data + 0x11130`), `X_high[64][40][2]`, `sbr->q_m`, `s_m`, `gain`
(`[8][48]` floats each), and the read-only data of the callees and the code
(`ff_sbr_noise_table`, `ps_noise0/13/2`, the `.LCPI17_*` constants; the mask
`.LCPI17_11 = {0x1ff, 3, 0, 0}` with its contents).

The second block is the 24 bytes after `Y1` (see `a2_row_spill`):
`Y[1][0][0..3)` when `ypos = 0`, `g_temp[0][0..6)` when `ypos = 1` (then the
third block starts 24 bytes later, so the union is
`Y[ypos] ∪ g_temp ∪ q_temp ∪ 24 bytes` in both cases). For `ypos = 0` the
theorem itself bounds the access to `Y[1]` by these 24 bytes; for `ypos = 1`
`hf_assemble` owns those bytes anyway, so the 24-byte bound there rests on
`a2_row_spill` and the row-crossing discipline (`HfAssemble.lean` crosses a row
of `Y` only through `a2_row_spill`; checked by `tv.sh`), not on the footprint. -/
abbrev HfData (ypos : Nat) (t : MachineData) : Mem 64 → Prop :=
  Blocks [(arg3 t + 0x7930#64 + BitVec.ofNat 64 (19456 * ypos), 19456),
    (arg3 t + 0x7930#64 + BitVec.ofNat 64 (19456 * ypos) + 19456#64, 24),
    (arg3 t + 0x11130#64 + BitVec.ofNat 64 (24 * ypos), 16128 - 24 * ypos),
    (arg1 t, 20480), (arg2 t + 0x5eac0#64, 1536), (arg2 t + 0x5f0c0#64, 1536),
    (arg2 t + 0x5f6c0#64, 1536), (lab "ff_sbr_noise_table", 4160), (lab "ps_noise0", 16),
    (lab "ps_noise13", 48), (lab "ps_noise2", 16)]
  ⋆ (4 ?@ lab "LCPI17_6" ⋆ (4 ?@ lab "LCPI17_7" ⋆ (4 ?@ lab "LCPI17_8" ⋆ (4 ?@ lab "LCPI17_9"
  ⋆ (4 ?@ lab "LCPI17_10" ⋆ (4 ?@ lab "LCPI17_12"
  ⋆ Int.toBytes 16 0x3000001ff =@ lab "LCPI17_11"))))))

/-- The scalar fields of `sbr` the code reads. -/
abbrev HfSc (x : HfArgs) (t : MachineData) : Mem 64 → Prop :=
  Int.toBytes 4 x.reset.toInt =@ (arg2 t + 0x18#64)
  ⋆ (Int.toBytes 4 x.smooth.toInt =@ (arg2 t + 0x38#64)
  ⋆ (Int.toBytes 4 (x.kx : Int) =@ (arg2 t + 0x58#64)
  ⋆ Int.toBytes 4 (x.m : Int) =@ (arg2 t + 0x60#64)))

/-- The `sbr->dsp` slots: `hf_g_filt`, `hf_apply_noise[0..3]`. -/
abbrev HfFn (fs : HfFns) (t : MachineData) : Mem 64 → Prop :=
  FnCell (arg2 t + 0x60228#64) fs.gfilt ⋆ (FnCell (arg2 t + 0x60230#64) fs.noise0
  ⋆ (FnCell (arg2 t + 0x60238#64) fs.noise1 ⋆ (FnCell (arg2 t + 0x60240#64) fs.noise2
  ⋆ FnCell (arg2 t + 0x60248#64) fs.noise3)))

/-- `ch_data->bs_num_env` and the ten bytes `t_env[0..8]`, `t_env_num_env_old`. -/
abbrev HfTe (x : HfArgs) (t : MachineData) : Mem 64 → Prop :=
  Int.toBytes 4 (x.nenv : Int) =@ (arg3 t + 0x8#64)
  ⋆ (Int.toBytes 1 (x.te 0 : Int) =@ (arg3 t + 0x15a9c#64)
  ⋆ (Int.toBytes 1 (x.te 1 : Int) =@ (arg3 t + 0x15a9d#64)
  ⋆ (Int.toBytes 1 (x.te 2 : Int) =@ (arg3 t + 0x15a9e#64)
  ⋆ (Int.toBytes 1 (x.te 3 : Int) =@ (arg3 t + 0x15a9f#64)
  ⋆ (Int.toBytes 1 (x.te 4 : Int) =@ (arg3 t + 0x15aa0#64)
  ⋆ (Int.toBytes 1 (x.te 5 : Int) =@ (arg3 t + 0x15aa1#64)
  ⋆ (Int.toBytes 1 (x.te 6 : Int) =@ (arg3 t + 0x15aa2#64)
  ⋆ (Int.toBytes 1 (x.te 7 : Int) =@ (arg3 t + 0x15aa3#64)
  ⋆ (Int.toBytes 1 (x.te 8 : Int) =@ (arg3 t + 0x15aa4#64)
  ⋆ Int.toBytes 1 (x.te 9 : Int) =@ (arg3 t + 0x15aa5#64))))))))))

/-- `e_a[0]`, `e_a[1]`. -/
abbrev HfEa (x : HfArgs) (t : MachineData) : Mem 64 → Prop :=
  Int.toBytes 4 x.ea0.toInt =@ arg4 t ⋆ Int.toBytes 4 x.ea1.toInt =@ (arg4 t + 4#64)

abbrev HfF (fs : HfFns) (x : HfArgs) (t : MachineData) : Mem 64 → Prop :=
  HfData x.ypos t ⋆ (HfSc x t ⋆ (HfFn fs t ⋆ (HfTe x t ⋆ (HfEa x t
    ⋆ Int.toBytes 8 x.idx.toInt =@ (arg3 t + 0x15aac#64)))))

/-- `f_indexnoise`/`f_indexsine` on return: some value within the `HfC` bounds
(`hf_assemble` stores `(indexnoise + m_max) & 0x1ff` and `(indexsine + 1) & 3`). -/
def HfIdxOut (t : MachineData) : Mem 64 → Prop := fun m =>
  ∃ i : BitVec 64, i.toNat % 2 ^ 32 ≤ 515 ∧ i.toNat / 2 ^ 32 < 4
    ∧ (Int.toBytes 8 i.toInt =@ (arg3 t + 0x15aac#64)) m

/-- On return `f_indexnoise`/`f_indexsine` have changed, within their bounds. -/
abbrev HfFPost (fs : HfFns) (x : HfArgs) (t : MachineData) : Mem 64 → Prop :=
  HfData x.ypos t ⋆ (HfSc x t ⋆ (HfFn fs t ⋆ (HfTe x t ⋆ (HfEa x t ⋆ HfIdxOut t))))

/-- The side conditions (each an `SbrWF` clause or a layout fact):
the stack 16-aligned at the call (`rsp + 8`), `sbr`/`ch_data` 16-aligned (the
`hf_apply_noise` operands `s_m[e]`, `q_temp[i]`), the noise constants aligned,
`1 ≤ m[1] ≤ 48`, `kx[1] + m[1] ≤ 64`, `bs_num_env ≤ 8`, `t_env[e] ≤ 19` for
`e ≤ bs_num_env` and `t_env_num_env_old ≤ 19` (note A1: `read_sbr_grid`
bounds the borders by `numTimeSlots + 3`, `aacsbr_template.c:651, 788`),
`f_indexnoise ≤ 515`, `f_indexsine < 4` (as unsigned 32-bit values), and
`Y1 = ch_data->Y[ypos]` with `ypos ≤ 1` (`aacsbr_template.c:1743`). -/
abbrev HfC (x : HfArgs) (t : MachineData) : Prop :=
  isAligned 16 (t.regs.get64 .rsp + 8#64) = true ∧ isAligned 16 (arg2 t) = true
    ∧ isAligned 16 (arg3 t) = true
    ∧ isAligned 16 (lab "ps_noise0") = true ∧ isAligned 16 (lab "ps_noise13") = true
    ∧ isAligned 16 (lab "ps_noise2") = true
    ∧ 1 ≤ x.m ∧ x.m ≤ 48 ∧ x.kx + x.m ≤ 64 ∧ x.nenv ≤ 8
    ∧ (∀ e, e ≤ x.nenv → x.te e ≤ 19) ∧ x.te 9 ≤ 19
    ∧ x.idx.toNat % 2 ^ 32 ≤ 515 ∧ x.idx.toNat / 2 ^ 32 < 4
    ∧ x.ypos ≤ 1 ∧ arg0 t = arg3 t + 0x7930#64 + BitVec.ofNat 64 (19456 * x.ypos)

abbrev HfPre (k : Nat) (fs : HfFns) (x : HfArgs) (ra : Int64) (t : MachineData) : Prop :=
  CallPre (hfNeed k) (HfF fs x t ⋆ x.R) ra t ∧ HfC x t

abbrev HfPost (k : Nat) (fs : HfFns) (x : HfArgs) (ra : Int64) (t s : MachineData) : Prop :=
  CallPost (hfNeed k) (HfFPost fs x t ⋆ x.R) ra t s

/-- `sbr_hf_assemble(Y1, X_high, sbr, ch_data, e_a)`, its `sbr->dsp` callees at
`fs`, `k` bytes of stack for `memcpy`. -/
abbrev HfAssembleSpec (k : Nat) (fs : HfFns) : Prop :=
  cenv.ProcSpec (entry "sbr_hf_assemble") (HfPre k fs) (HfPost k fs)


/-! ## `SbrWF`: what the procedures need of the decoder state

Collected from the side conditions (`…C`) above; not yet one predicate over
the layout of `SpectralBandReplication` (M4 defines `SbrWF` and derives each
procedure's `…C` from it at the call site of `ff_aac_sbr_apply`). Field names
are those of `libavcodec/sbr.h`. Kinds:
*invariant* — a property of every `sbr` the decoder hands to
`ff_aac_sbr_apply` (established by `read_sbr_*`, `sbr_reset`,
`sbr_make_f_derived`, `sbr_turnoff`; assumed on entry);
*path* — established along `ff_aac_sbr_apply`'s control flow before the call
(a loop variable, a test the caller makes);
*layout* — alignment or disjointness of the memory the caller carves.

`sbr_lf_gen` (`LfGenC`, `LfGenF`):
* `0 ≤ kx[0], kx[1] ≤ 32` — invariant (`sbr_make_f_derived` rejects
  `kx[1] > 32`, `sbr_turnoff` sets 32; `kx[0]` is a previous `kx[1]` or 0).
  Without it the build's bounds check (`ud1`) is reached.
* `buf_idx = data[ch].Ypos ∈ {0, 1}` — invariant (initialised 0, toggled).
* `X_low`, `data[ch].W` and the `kx` cells disjoint — layout.

`sbr_hf_inverse_filter` (`HfInvC`):
* `k[0] ≤ 32` — invariant (`k[0] = start_min + sbr_offset[r][bs_start_freq]`,
  `aacsbr_template.c:315-318`, `aacsbrdata.h`; the maximum over all sample
  rates and start indices is 32, and the store precedes any validation, so it
  holds even after a rejected header).
* `ps_mask3` 16-aligned, `rsp + 8` 16-aligned at entry — layout / calling
  convention.

`sbr_x_gen` (`XGenC`):
* `ch < 2` — path (the channel loop).
* `kx[0], kx[1] ≤ 32` — invariant (as for `sbr_lf_gen`).
* `kx[i] + m[i] ≤ 64` — invariant (`sbr_make_f_derived`: the high band ends
  at most at 64 subbands).
* `data[ch].t_env_num_env_old ≤ 19` — invariant (`aacsbr_template.c:681`
  bounds the envelope borders).

`sbr_hf_assemble` (`HfC`):
* `1 ≤ m[1] ≤ 48` — `m[1] ≤ 48`: invariant; `1 ≤ m[1]`: path (with
  `bs_num_env ≥ 1`, the caller's non-empty high band; `sbr_turnoff` can make
  the band empty, see `hf_g_filt` below).
* `kx[1] + m[1] ≤ 64` — invariant.
* `bs_num_env ≤ 8` — invariant (`read_sbr_grid`); `1 ≤ bs_num_env` on the
  path that uses `m` — path.
* `t_env[e] ≤ 19` for `e ≤ bs_num_env`, `t_env_num_env_old ≤ 19` — invariant
  (note A1: `read_sbr_grid` bounds the borders by `numTimeSlots + 3 = 19`,
  not 16, `aacsbr_template.c:651, 740-752, 788`; `t_env[e]` for live data only,
  see `DWF`).
* `Y1 = Y[Ypos]`, `Ypos ≤ 1` — invariant / path (`aacsbr_template.c:1743`).
* `f_indexnoise ≤ 515`, `f_indexsine < 4` (the two 32-bit halves of the 8-byte
  cell) — invariant (both are reduced modulo 512 / 4 when stored).
* `rsp + 8`, `sbr`, `ch_data`, `ps_noise0/13/2` 16-aligned — layout.

The `SBRDSPContext` leaves, at their call sites (M1, M2):
* `hf_g_filt`: `m_max ≥ 1` (path: the caller excludes the empty band), row
  count `m_max mod 256`, `ixh < 40`, `rcx < 4` when `m_max mod 256 < 4`.
* `hf_apply_noise`: `noise ≤ 515` (the first table access is unmasked),
  `1 ≤ m_max < 2 ^ 28`; it writes `Y` up to `⌈m_max / 4⌉ · 4` entries, so `Y`
  needs that slack (see `HfData`, `a2_row_spill`).
* `hf_gen`: `t_env[0] < t_env[bs_num_env]` (signed), `end - start` even.
* `qmf_post_shuffle`: `z.toInt + 240 < 2 ^ 63` (layout).
* `sbr_qmf_synthesis` (`QmfC`): `div ≤ 1`, `*v_off ≤ 1664` and a multiple of 8
  (invariant of the synthesis buffer, `aacsbr_template.c:88-89, 1427-1432`),
  alignments (layout); the `v0` footprint is `qmfVSize`.
* `ff_ps_apply` (`PsApplyC`): `top ≤ 64`, the PS state invariant `PsWF`,
  16-aligned buffers.
-/

/-! ## Callees of `ff_aac_sbr_apply` outside the cluster

Contracts of the procedures outside the SBR cluster. Decision 2 of the plan
trusts libavutil and the PS decoder; of these, the `float_dsp` contract
`VectorFmulRevSpec` here (and `VectorFmulSpec`, `VectorFmulAddSpec` above) is
since proved of the x86 routines (`FloatDsp.lean`); the rest stay assumed
(`SbrAssumed`). -/

/-- `len` of `vector_fmul_reverse`, the low 32 bits of `rcx` (`int`). -/
abbrev fmulRevN (t : MachineData) : Nat := (arg3 t).toNat % 2 ^ 32

/-- `vector_fmul_reverse(dst, src0, src1, len)` (`libavutil/float_dsp.h`):
`dst[len]` written, `src0[len]`, `src1[len]` read, 32-byte aligned, `len` a multiple
of 16 with `1 ≤ len < 2 ^ 30` (do-while loop), and the 32-byte constant
`pd_reverse` (`libavutil/x86/float_dsp.asm`, `SECTION_RODATA 32`) read, 32-byte
aligned. Proved of the three x86 routines (`Dsp/VectorFmulRev.lean`).

Note F1: `ff_vector_fmul_reverse_avx2` loads its permutation mask
`pd_reverse(%rip)` with `vmovaps`; the contract assumed before the routines were
proved had only the three arrays, and was false of the AVX2 routine. The
constant is now in the footprint and its alignment in the precondition (the
caller owns it in `CstW` and assumes the alignment in `LayoutC`). -/
abbrev VectorFmulRevF (t : MachineData) : Mem 64 → Prop :=
  Blocks [(arg0 t, 4 * fmulRevN t), (arg1 t, 4 * fmulRevN t), (arg2 t, 4 * fmulRevN t),
    (lab "pd_reverse", 32)]

abbrev VectorFmulRevC (t : MachineData) : Prop :=
  fmulRevN t % 16 = 0 ∧ 1 ≤ fmulRevN t ∧ fmulRevN t < 2 ^ 30
    ∧ isAligned 32 (arg0 t) = true ∧ isAligned 32 (arg1 t) = true
    ∧ isAligned 32 (arg2 t) = true ∧ isAligned 32 (lab "pd_reverse") = true

abbrev VectorFmulRevSpec (need : Nat) (f : Int64) : Prop :=
  LeafSpecAt f need VectorFmulRevF VectorFmulRevC

/-- `abort` does not return: its precondition is `False`, so the specification holds
of any code, and a call to it must be shown unreachable. -/
abbrev AbortSpec : Prop :=
  cenv.ProcSpec (entry "abort") (fun (_ : Unit) _ _ => False) (fun _ _ _ _ => True)

/-! ## Float-model fact (R1)

`sbr_dequant` (coupled case) asserts `av_assert0(temp1 <= 1E20)` before the noise-floor
division, with `temp1 = exp2fi(NOISE_FLOOR_OFFSET - noise_facs_q + 1)`. The compiled code
builds `temp1` from its bit pattern (`2^(7 - q)` normal or subnormal, or `+0`, for the byte
`q`), widens it (`vcvtss2sd`, `BitVec.f32to64`) and compares it with the double `1E20`
(`vucomisd`, `BitVec.f64cmp`); the `jb` to `abort` is taken on "unordered or below".

`DequantFloatModel` states the fact the five `vucomisd` sites (blocks `L6bbc`, `L6c7d`,
`L6d51`, `L6e23`, `L6eeb` of `ff_aac_sbr_apply`) need. It is not an assumption of the final
theorem: it is proved, `dequantFloatModel_holds` (`DequantFloat.lean`), from a bit-level
model of the widening, and the proof of `sbr_dequant` uses that theorem directly. -/

/-- (R1) A single-precision value whose bit pattern is at most `0x43000000` (that is, a
non-negative number `≤ 128.0f`), widened to double, is ordered with and strictly below `1E20`:
`f64cmp 1E20 v = (unordered, less, equal) = (false, false, false)`. -/
def DequantFloatModel : Prop :=
  ∀ v : BitVec 32, v.toNat ≤ 0x43000000 →
    BitVec.f64cmp dbl1E20 (BitVec.f32to64 v) = (false, false, false)

end Kraken.Examples.Sbr
