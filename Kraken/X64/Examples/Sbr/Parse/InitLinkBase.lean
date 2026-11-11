import Kraken.X64.Examples.Sbr.Parse.InitSpec
import Kraken.X64.Examples.Sbr.Parse.DecExtSpec
import Kraken.X64.Examples.Sbr.Link
import Kraken.X64.Examples.Sbr.SessionSpec

/-!
# `ff_aac_sbr_ctx_alloc_init`: the session's parameters from the results

The parameters a decoding session runs with, built from what a successful run leaves (`IR`):
the function slots of `envOf e₀ r` are the slots the run stored (the `sbr->dsp` slots, the two
`av_tx` functions, the four `sbr->c` procedures), the rest of the environment is `e₀`'s; the
inputs `inOf r …` take the `av_tx` contexts from the run. Also the helpers of the view of the
element (`InitLink`): raw blocks from known bytes, splits of zero runs, of the slots and of
`spectrum_params`.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply
open Kraken.Examples.Sbr.Session (zs InitIn xInit)

namespace Kraken.Examples.Sbr.Init

variable [CodeEnv]

/-! ## The parameters -/

/-- The function slots after the run: the `sbr->dsp` slots `r.sl`, `mdct_ana_fn` and `mdct_fn`
from `av_tx_init`, the four `sbr->c` procedures; the `float_dsp` slots are `f`'s. -/
def fsOf (f : Fns) (r : IR) : Fns where
  sum64x5 := r.sl.sum64x5
  sumSquare := r.sl.sumSquare
  preShuffle := r.sl.preShuffle
  postShuffle := r.sl.postShuffle
  autocorr := r.sl.autocorr
  hfGen := r.sl.hfGen
  hfs := ⟨r.sl.gfilt, r.sl.noise0, r.sl.noise1, r.sl.noise2, r.sl.noise3⟩
  qfs := ⟨r.sl.negOdd64, r.sl.deintNeg, r.sl.deintBfly, r.synFn, f.qfs.fmul, f.qfs.fmulAdd⟩
  lfGen := entry "sbr_lf_gen"
  hfAsm := entry "sbr_hf_assemble"
  xGen := entry "sbr_x_gen"
  hfInv := entry "sbr_hf_inverse_filter"
  mdctAna := r.anaFn
  fmulRev := f.fmulRev

/-- The session's environment after the run. -/
def envOf (e₀ : Env) (r : IR) : Env := { e₀ with fs := fsOf e₀.fs r }

/-- The session's inputs after the run with the element type `id`, the caller's memory `R`
and the `*ac` fields. -/
def inOf (r : IR) (id : BitVec 32) (R : Mem 64 → Prop) (avctx fdsp : BitVec 64)
    (extRate ps : BitVec 32) : InitIn :=
  ⟨id, R, avctx, fdsp, extRate, ps, r.anaCtx, r.synCtx⟩

/-- The slots of an environment in `sbr->dsp` order. -/
def slotsOf (e : Env) : Slots :=
  ⟨e.fs.sum64x5, e.fs.sumSquare, e.fs.qfs.negOdd64, e.fs.preShuffle, e.fs.postShuffle,
    e.fs.qfs.deintNeg, e.fs.qfs.deintBfly, e.fs.autocorr, e.fs.hfGen, e.fs.hfs.gfilt,
    e.fs.hfs.noise0, e.fs.hfs.noise1, e.fs.hfs.noise2, e.fs.hfs.noise3⟩

/-- `SbrSlots` is `DspSlotsOK` of the `sbr->dsp` slots, the four `sbr->c` procedures and
`FdspOK`. -/
theorem sbrSlots_iff (e : Env) :
    SbrSlots e ↔ DspSlotsOK (slotsOf e) ∧ e.fs.lfGen = entry "sbr_lf_gen"
      ∧ e.fs.hfInv = entry "sbr_hf_inverse_filter" ∧ e.fs.hfAsm = entry "sbr_hf_assemble"
      ∧ e.fs.xGen = entry "sbr_x_gen" ∧ FdspOK e := by
  constructor
  · intro h
    exact ⟨⟨h.sum64x5, h.sumSquare, h.preShuffle, h.postShuffle, h.hfGen, h.autocorr, h.gfilt,
      h.noise0, h.noise1, h.noise2, h.noise3, h.negOdd64, h.deintNeg, h.deintBfly⟩,
      h.lfGen, h.hfInv, h.hfAsm, h.xGen, ⟨h.fmul, h.fmulAdd, h.fmulRev⟩⟩
  · rintro ⟨d, h1, h2, h3, h4, f⟩
    exact ⟨d.sum64x5, d.sumSquare, d.preShuffle, d.postShuffle, d.hfGen, d.autocorr, d.gfilt,
      d.noise0, d.noise1, d.noise2, d.noise3, d.negOdd64, d.deintNeg, d.deintBfly, h1, h2, h3,
      h4, f.fmul, f.fmulAdd, f.fmulRev⟩

/-- The session's `SbrSlots` after the run: from the slots `ff_sbrdsp_init` left
(`DspSlotsOK`, InitPost) and `e₀`'s `float_dsp` slots. -/
theorem sbrSlots_envOf {e₀ : Env} {r : IR} (h : DspSlotsOK r.sl) (hf : FdspOK e₀) :
    SbrSlots (envOf e₀ r) :=
  (sbrSlots_iff _).2 ⟨h, rfl, rfl, rfl, rfl, ⟨hf.fmul, hf.fmulAdd, hf.fmulRev⟩⟩

/-- The session's two `av_tx` contracts (`SbrAssumed.txAna`, `.txSyn`) after the run: from the
contracts of the functions `av_tx_init` returned (InitPost). -/
theorem txSpecs_envOf {e₀ : Env} {r : IR} {k : Nat} (ha : TxSpec e₀.Ctx e₀.TxTab k r.anaFn)
    (hs : TxSpec e₀.Ctx e₀.TxTab k r.synFn) :
    TxSpec (envOf e₀ r).Ctx (envOf e₀ r).TxTab k (envOf e₀ r).fs.mdctAna
      ∧ TxSpec (envOf e₀ r).Ctx (envOf e₀ r).TxTab k (envOf e₀ r).fs.qfs.tx :=
  ⟨ha, hs⟩

/-! ## The memory -/

/-- `sbr->ps` beyond `ps->common` (the session's `PsRest`). -/
def PsRestI (x : Args) (t : MachineData) : Mem 64 → Prop :=
  let p := sbrA t + 0x2b600#64
  4 ?@ (p + 764#64) ⋆ (133200 ?@ (p + 768#64) ⋆ (x.psh =@ (p + 133968#64) ⋆ 76 ?@ (p + 134036#64)))

/-- The six bytes of `spectrum_params` (the session's `spBytes`). -/
def spB (x : Args) : List UInt8 := Int.toBytes 4 x.spLo.toInt ++ Int.toBytes 2 x.spHi.toInt

/-! ## Helpers -/

omit [CodeEnv]

theorem sep_mono' {X Y K K' : Mem 64 → Prop} (e₁ : Mem.Entails X Y)
    (e₂ : Mem.Entails K K') : Mem.Entails (X ⋆ K) (Y ⋆ K') := by
  intro m ⟨m₁, m₂, hd, hm, h₁, h₂⟩
  exact ⟨m₁, m₂, hd, hm, e₁ m₁ h₁, e₂ m₂ h₂⟩

/-- Known bytes as a raw block. -/
theorem vraw {l : List UInt8} {a : BitVec 64} {n : Nat} (hl : l.length = n)
    (hw : n ≤ 2 ^ 64) : Mem.Entails (l =@ a) (n ?@ a) := fun _ h => ⟨hw, l, hl, h⟩

/-- Known bytes in front of a raw block, as one raw block. -/
theorem raw_cons {l : List UInt8} {a b : BitVec 64} {n k : Nat} {R : Mem 64 → Prop}
    (hl : l.length = n) (hb : b = a + BitVec.ofNat 64 n) (hw : n + k ≤ 2 ^ 64)
    (e : Mem.Entails R (k ?@ b)) : Mem.Entails (l =@ a ⋆ R) ((n + k) ?@ a) := by
  intro m h
  rw [Block.split a n k hw, ← hb]
  exact sep_mono' (vraw hl (by omega)) e m h

theorem addr_step (p : BitVec 64) (o n o2 : Nat) (h : o + n = o2) :
    p + BitVec.ofNat 64 o2 = p + BitVec.ofNat 64 o + BitVec.ofNat 64 n := by
  subst h; rw [BitVec.add_assoc, BitVec.ofNat_add]

/-- A zero run at `p + o` split at `n`. -/
theorem zsS (p : BitVec 64) (o n k N o2 : Nat) (hN : n + k = N) (ho : o + n = o2)
    (hw : N ≤ 2 ^ 64) :
    zs N =@ (p + BitVec.ofNat 64 o)
      = zs n =@ (p + BitVec.ofNat 64 o) ⋆ zs k =@ (p + BitVec.ofNat 64 o2) := by
  subst hN ho
  exact zs_split p o n k hw

/-- A zero run at `p` split at `n`. -/
theorem zsS0 (p : BitVec 64) (n k N : Nat) (hN : n + k = N) (hw : N ≤ 2 ^ 64) :
    zs N =@ p = zs n =@ p ⋆ zs k =@ (p + BitVec.ofNat 64 n) := by
  subst hN
  exact zs_split0 p n k hw

theorem toB8_0 : Int.toBytes 8 0 = zs 8 := by decide
theorem toB4_0 : Int.toBytes 4 0 = zs 4 := by decide
theorem allOnes32 : (BitVec.allOnes 32).toInt = -1 := by decide
theorem allOnes16 : (BitVec.allOnes 16).toInt = -1 := by decide
theorem vOff_init : (1152 : BitVec 32).toInt = 0x480 := by decide

/-- `spectrum_params` after the run as its two cells. -/
theorem sp_split (p : BitVec 64) :
    (Int.toBytes 4 (-1) ++ Int.toBytes 2 (-1)) =@ (p + 0x2893c#64)
      = Int.toBytes 4 (-1) =@ (p + 0x2893c#64) ⋆ Int.toBytes 2 (-1) =@ (p + 0x28940#64) :=
  Val.append_eq _ _ _ _ (by rw [Int.toBytes_length]; exact addr_step p _ _ _ rfl)
    (by simp only [Int.toBytes_length]; decide)

/-- The `sbr->dsp` slots as fourteen cells. -/
theorem slots_split (p : BitVec 64) (sl : Slots) :
    sl.bytes =@ (p + 0x88b00#64)
      = fb sl.sum64x5 =@ (p + 0x88b00#64) ⋆ (fb sl.sumSquare =@ (p + 0x88b08#64)
        ⋆ (fb sl.negOdd64 =@ (p + 0x88b10#64) ⋆ (fb sl.preShuffle =@ (p + 0x88b18#64)
        ⋆ (fb sl.postShuffle =@ (p + 0x88b20#64) ⋆ (fb sl.deintNeg =@ (p + 0x88b28#64)
        ⋆ (fb sl.deintBfly =@ (p + 0x88b30#64) ⋆ (fb sl.autocorr =@ (p + 0x88b38#64)
        ⋆ (fb sl.hfGen =@ (p + 0x88b40#64) ⋆ (fb sl.gfilt =@ (p + 0x88b48#64)
        ⋆ (fb sl.noise0 =@ (p + 0x88b50#64) ⋆ (fb sl.noise1 =@ (p + 0x88b58#64)
        ⋆ (fb sl.noise2 =@ (p + 0x88b60#64) ⋆ fb sl.noise3 =@ (p + 0x88b68#64))))))))))))) := by
  have l : ∀ f : Int64, (fb f).length = 8 := fun f => Int.toBytes_length _ _
  have ll : ∀ (x : List UInt8) (f : Int64), (x ++ fb f).length = x.length + 8 := fun x f => by
    rw [List.length_append, l]
  simp only [Slots.bytes, List.append_assoc]
  repeat rw [Val.append_eq _ _ _ _ (by
    simp only [List.length_append, l]; exact addr_step p _ _ _ rfl) (by
    simp only [List.length_append, l]; decide)]

end Kraken.Examples.Sbr.Init
