import Kraken.X64.Parser
import Kraken.MachineWP
import Kraken.Rules.CfgTable
import Kraken.Rules.FrameLemmas
import Kraken.Rules.IndirectCall
import Kraken.Rules.IntMisc
import Kraken.Rules.PackedSse
import Kraken.Rules.ScalarFloat
import Kraken.Rules.HelperLemmas
import Kraken.Rules.ViewLemmas
import Kraken.Rules.SepStep
import Kraken.Rules.LexVar
import Kraken.X64.Examples.Sbr.Spec
import Kraken.X64.Examples.Sbr.DequantFloat
import Kraken.X64.Examples.Sbr.SessionSpec

/-!
# `ff_aac_sbr_apply`: the specification

`libavcodec/aacsbr_template.c` (FFmpeg n8.1), `ff_aac_sbr_apply(ac, che, id_aac, L, R)`.
This file is hand-written and holds only definitions: the logical variables (`Args`,
`DV`, `Env`), the addresses, the footprint `ApplyF` and its groups, the well-formedness
invariant `SbrWF`, the layout conditions `LayoutC`, the constants `CstW`, and
`ApplySpec` itself. Everything the statement of `ff_aac_sbr_apply_linked` says about
`ff_aac_sbr_apply` is defined here or in `Spec.lean`; no proof is needed to read it.

The text, the control-flow table and the block obligations are generated into
`ApplyTable.lean`, which imports this file; the proof is in `Apply/*.lean` and
`Apply.lean`.
-/

open Kraken Kraken.X64.Parser Std.WP MachineWP Kraken.SysV Mem

namespace Kraken.Examples.Sbr.Apply

/-! ## The logical variables -/

/-- What stays fixed while the body runs (also across `sbr_turnoff`): the caller's rest,
the pointers and rates the final state is stated with, and (`KeepD`, one nested
conjunct) the decoder state apply does not write. Entries where the arguments evolve
(the channel loop) read `∃ y, x.Keep y ∧ SbrWF y ∧ … ∧ (s.dmem =⋆ Mm k e y ra t₀ …)`. -/
abbrev Args.Keep (x y : Args) : Prop :=
  y.R = x.R ∧ y.avctx = x.avctx ∧ y.fdsp = x.fdsp ∧ y.extRate = x.extRate ∧ y.ps = x.ps
  ∧ y.anaCtx = x.anaCtx ∧ y.synCtx = x.synCtx ∧ y.sampleRate = x.sampleRate ∧ x.KeepD y

/-- Channel `ch`'s values. -/
abbrev Args.d (x : Args) (ch : Nat) : DV := if ch = 0 then x.d0 else x.d1

/-- `sbr_turnoff`'s `memset(&sbr->spectrum_params, -1, sizeof(SpectrumParameters))`. -/
abbrev Args.spSet (x : Args) : Args :=
  { x with spLo := BitVec.allOnes 32, spHi := BitVec.allOnes 16 }

/-- I1: a stopped decoder has `spectrum_params.bs_start_freq = 0xFF` (`sbr_turnoff`'s memset;
a header that sets `start` also sets `bs_start_freq`). -/
def Args.I1 (x : Args) : Prop := x.start = 0 → x.spLo.setWidth 8 = 0xFF#8

/-- The prologue's `kx_and_m_pushed` step (before `sbr_dequant`): `kx[0] = kx[1]`, `m[0] = m[1]`
unless pushed; then `kx_and_m_pushed = 0`. -/
abbrev Args.push (x : Args) : Args :=
  { x with kx0 := if x.pushed = 0 then x.kx1 else x.kx0,
           m0 := if x.pushed = 0 then x.m1 else x.m0, pushed := 0 }

/-- `sbr_qmf_synthesis` on channel 0 / 1 writes `synthesis_filterbank_samples_offset`
(`*v_off`): the values with that field `v`. -/
abbrev Args.setV0 (x : Args) (v : BitVec 32) : Args := { x with d0 := { x.d0 with vOff := v } }
abbrev Args.setV1 (x : Args) (v : BitVec 32) : Args := { x with d1 := { x.d1 with vOff := v } }

/-- D5 path fact (a), aacsbr_template.c:1693-1697: after the prologue's element-type check
(`id_aac != sbr->id_aac` → `sbr_turnoff`), a live state's `sbr->id_aac` equals the `id_aac`
argument (the low 32 bits of `rdx` at entry). -/
def IdLive (t : MachineData) (y : Args) : Prop :=
  y.start ≠ 0 → y.idAac = BitVec.setWidth 32 (arg2 t)

/-- D5 path facts carried in the channel loop: (a) `IdLive`; (b) the loop runs channel 1 only
for a CPE (`ch < (id_aac == TYPE_CPE) + 1`, aacsbr_template.c:1700). -/
def ChLive (t : MachineData) (ch : Nat) (y : Args) : Prop :=
  IdLive t y ∧ (ch ≠ 0 → BitVec.setWidth 32 (arg2 t) = 1#32)


variable [CodeEnv]

/-! ## Addresses -/

/-! ## The footprint (groups; each a `def`, opened by its view lemma) -/

/-! ## `SbrWF` -/

/-! ## The specification -/

/-- The callees at `k` bytes of stack: the proved `SBRDSPContext` contracts at the
slot contents, the C procedures of the cluster (the `sbr->c` slots hold them,
`ff_aacsbr_func_ptr_init`), and the assumed contracts. -/
abbrev ApplyCallees (k : Nat) (e : Env) : Prop :=
  LeafSpecAt e.fs.sum64x5 0 Sum64x5F Sum64x5C
  ∧ LeafSpecAt e.fs.sumSquare 0 SumSquareF SumSquareC
  ∧ LeafSpecAt e.fs.preShuffle 0 QmfPreShuffleF QmfPreShuffleC
  ∧ LeafSpecAt e.fs.postShuffle 0 QmfPostShuffleF QmfPostShuffleC
  ∧ LeafSpecAt e.fs.hfGen 0 HfGenF HfGenC
  ∧ e.fs.lfGen = entry "sbr_lf_gen" ∧ LfGenSpec k
  ∧ e.fs.hfInv = entry "sbr_hf_inverse_filter" ∧ HfInverseFilterSpec e.fs.autocorr
  ∧ e.fs.hfAsm = entry "sbr_hf_assemble" ∧ HfAssembleSpec k e.fs.hfs
  ∧ e.fs.xGen = entry "sbr_x_gen" ∧ XGenSpec k
  ∧ QmfSynthesisSpec 0 k e.Ctx e.TxTab e.fs.qfs ∧ QmfSynthesisSpec 1 k e.Ctx e.TxTab e.fs.qfs
  ∧ TxSpec e.Ctx e.TxTab k e.fs.mdctAna ∧ VectorFmulRevSpec k e.fs.fmulRev
  ∧ MemcpySpec k ∧ MemsetSpec k ∧ PsApplySpec e.PsTab k ∧ AvLogSpec e.Ext k ∧ AbortSpec

/-! ## I1 and the precondition

`ApplyFPost` keeps I1 (`Args.KeepD.i1`). The values of `spectrum_params` in `ScW` add no
assumption: `ScW` is `ScWRaw` (those six bytes unknown) at some values (`scWRaw_eq`). -/

/-- I1 survives apply: `start` and `spectrum_params` are kept, or cleared together. -/
theorem Args.KeepT.i1 {x y : Args} (h : x.KeepT y) (hx : x.I1) : y.I1 := by
  unfold Args.KeepT at h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h⟩ := h
  intro hy
  rcases h with ⟨-, hl, -⟩ | ⟨hs, hl, -⟩
  · rw [hl]; decide
  · rw [hl]; exact hx (hs ▸ hy)

theorem Args.KeepD.i1 {x y : Args} (h : x.KeepD y) (hx : x.I1) : y.I1 :=
  h.2.2.2.2.2.2.2.2.2.i1 hx

/-- The postcondition keeps I1: input I1 and apply give output I1. -/
theorem applyFPost_i1 {e : Env} {x : Args} {t : MachineData} {m : Mem 64} (hx : x.I1)
    (h : ApplyFPost e x t m) : ∃ y : Args, y.I1 ∧ ApplyF e y t m := by
  obtain ⟨y, -, -, -, -, -, hk, -, -, -, hm⟩ := h
  exact ⟨y, hk.i1 hx, hm⟩

theorem sep_ex_l {α : Type} (P : α → Mem 64 → Prop) (R : Mem 64 → Prop) :
    ((fun m => ∃ v, P v m) ⋆ R) = fun m => ∃ v, (P v ⋆ R) m := by
  funext m; apply propext; constructor
  · rintro ⟨a, b, h1, h2, ⟨v, hv⟩, hr⟩; exact ⟨v, a, b, h1, h2, hv, hr⟩
  · rintro ⟨v, a, b, h1, h2, hv, hr⟩; exact ⟨a, b, h1, h2, ⟨v, hv⟩, hr⟩

theorem sep_ex_r {α : Type} (P : α → Mem 64 → Prop) (L : Mem 64 → Prop) :
    (L ⋆ fun m => ∃ v, P v m) = fun m => ∃ v, (L ⋆ P v) m := by
  funext m; apply propext; constructor
  · rintro ⟨a, b, h1, h2, hl, ⟨v, hv⟩⟩; exact ⟨v, a, b, h1, h2, hl, hv⟩
  · rintro ⟨v, a, b, h1, h2, hl, hv⟩; exact ⟨a, b, h1, h2, hl, ⟨v, hv⟩⟩

theorem toBytes_ofInt_ofBytes (n : Nat) (bs : List UInt8) (h : bs.length = n) :
    Int.toBytes n (BitVec.ofInt (8 * n) (Int.ofBytes bs)).toInt = bs := by
  rw [BitVec.toInt_ofInt, ← Int.toBytes_emod, Int.take]
  have e : (Int.ofBytes bs).bmod (2 ^ (8 * n)) % (2 ^ (8 * n) : Int)
      = Int.ofBytes bs % 2 ^ (8 * n) := Int.bmod_emod
  rw [e, show Int.ofBytes bs % 2 ^ (8 * n) = (Int.ofBytes bs).take (8 * n) from rfl,
    Int.toBytes_emod, ← h, Int.toBytes_ofBytes_all]

/-- An unknown `n`-byte region is a known one with some `8n`-bit value. -/
theorem block_eq_exists (a : BitVec 64) (n : Nat) (hn : n ≤ 2 ^ 64) :
    (n ?@ a) = fun m => ∃ v : BitVec (8 * n), (Int.toBytes n v.toInt =@ a) m := by
  funext m; apply propext; constructor
  · rintro ⟨-, bs, hlen, h⟩
    exact ⟨BitVec.ofInt (8 * n) (Int.ofBytes bs), by
      show (Int.toBytes n _).At a = m; rw [toBytes_ofInt_ofBytes n bs hlen]; exact h⟩
  · rintro ⟨v, h⟩
    exact ⟨hn, _, Int.toBytes_length .., h⟩


/-- `ScW` with the six bytes of `spectrum_params` unknown (`6 ?@`), as the footprint was
stated before they had values. -/
def ScWRaw (x : Args) (t : MachineData) : Mem 64 → Prop :=
  let s := sbrA t
  cell4 s x.sampleRate ⋆ (cell4 (s + 0x4#64) x.start ⋆ (cell4 (s + 0x8#64) x.ready
    ⋆ (cell4 (s + 0xc#64) x.idAac ⋆ (4 ?@ (s + 0x10#64) ⋆ (cell4 (s + 0x18#64) x.reset ⋆ (6 ?@ (s + 0x1c#64)
    ⋆ (c4 (s + 0x30#64) x.limGains ⋆ (cell4 (s + 0x34#64) x.interpol
    ⋆ (cell4 (s + 0x38#64) x.smooth ⋆ (cell4 (s + 0x3c#64) x.coupling
    ⋆ (c4 (s + 0x40#64) x.k0 ⋆ (c4 (s + 0x54#64) x.kx0 ⋆ (c4 (s + 0x58#64) x.kx1
    ⋆ (c4 (s + 0x5c#64) x.m0 ⋆ (c4 (s + 0x60#64) x.m1
    ⋆ cell4 (s + 0x64#64) x.pushed)))))))))))))))

/-- The precondition is unchanged in meaning: the raw `spectrum_params` bytes are the valued
cells at some `spLo`, `spHi` (and `Args` is universally quantified in `ApplySpec`). -/
theorem scWRaw_eq (x : Args) (t : MachineData) :
    ScWRaw x t = fun m => ∃ (lo : BitVec 32) (hi : BitVec 16),
      ScW { x with spLo := lo, spHi := hi } t m := by
  unfold ScWRaw ScW
  dsimp only
  rw [Block.split_at (sbrA t + 0x1c#64) 6 4 (by decide) (by decide),
    block_eq_exists (sbrA t + 0x1c#64) 4 (by decide),
    block_eq_exists (sbrA t + 0x1c#64 + BitVec.ofNat 64 4) (6 - 4) (by decide),
    Std.ExtHashMap.sep_assoc]
  simp only [sep_ex_l, sep_ex_r, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat,
    Nat.reduceSub, Nat.reduceMul]
  funext m
  exact propext ⟨fun ⟨v, w, h⟩ => ⟨w, v, h⟩, fun ⟨w, v, h⟩ => ⟨v, w, h⟩⟩

