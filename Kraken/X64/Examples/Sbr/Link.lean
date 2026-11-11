import Kraken.X64.Examples.Sbr.Apply
import Kraken.X64.Examples.Sbr.Dsp
import Kraken.X64.Examples.Sbr.FloatDsp
import Kraken.X64.Examples.Sbr.LfGen
import Kraken.X64.Examples.Sbr.XGen
import Kraken.X64.Examples.Sbr.HfInverseFilter
import Kraken.X64.Examples.Sbr.HfAssemble
import Kraken.X64.Examples.Sbr.QmfSynthesis
import Kraken.X64.Examples.Sbr.SessionSpec

/-!
# `ff_aac_sbr_apply`: the cluster linked

`Apply.spec` proves `ff_aac_sbr_apply` from the contracts of its callees
(`ApplyCallees`). Those contracts are proved separately: the six C procedures in
their modules, the `SBRDSPContext` routines in `Dsp/` and the three
`AVFloatDSPContext` routines in `Dsp/VectorFmul*.lean`. This file puts them
together. What remains is three named hypotheses, none of them proved here:

* `SbrPlaced`: every text the proofs talk about is placed in the ambient code.
* `SbrSlots e`: the function-pointer slots hold the routines the x86-64
  initialisation installs.
* `SbrAssumed k e`: the contracts of the callees outside the cluster.

`AbortSpec` is not among them. Its precondition is `False`, so it holds of any
code (`abortSpec_holds`). That makes it vacuous as an assumption, and nothing
else becomes vacuous: every call to `abort` in `ff_aac_sbr_apply` must still be
shown unreachable, and is (the `Trap` blocks, `DequantFloatModel`).
-/

open Kraken

namespace Kraken.Examples.Sbr

open Apply (Env ApplyCallees ApplySpec)

variable [CodeEnv]

/-- `abort`'s specification holds of any code: its precondition is `False`. -/
theorem abortSpec_holds : AbortSpec := fun _ _ _ h => h.elim

/-- The callees of `ff_aac_sbr_apply`, from the proofs of the cluster and the
three hypotheses. -/
theorem applyCallees_of_link (hpl : SbrPlaced) (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env)
    (hslots : SbrSlots e) (hasm : SbrAssumed k e) : ApplyCallees k e := by
  obtain ⟨hNeg, hSum, hSq, hPre, hPost, hDN, hDB, hAcS, hAcS3, hGen, hGF, hN0, hN1, hN2, hN3⟩ :=
    sbrDspSpecs hpl.dsp
  have hFm := vectorFmulSpec_of hpl.fdsp k hslots.fmul
  have hFa := vectorFmulAddSpec_of hpl.fdsp k hslots.fmulAdd
  have hFr := vectorFmulRevSpec_of hpl.fdsp k hslots.fmulRev
  have hAc : HfInvCallees e.fs.autocorr := by
    rcases hslots.autocorr with h | h <;> rw [h]
    · exact hAcS
    · exact hAcS3
  have hHf : HfCallees k e.fs.hfs := by
    refine ⟨?_, ?_, ?_, ?_, ?_, hasm.memcpy⟩
    · rw [hslots.gfilt]; exact hGF
    · rw [hslots.noise0]; exact hN0
    · rw [hslots.noise1]; exact hN1
    · rw [hslots.noise2]; exact hN2
    · rw [hslots.noise3]; exact hN3
  have hQ : QmfCallees k e.Ctx e.TxTab e.fs.qfs := by
    refine ⟨?_, ?_, ?_, hasm.txSyn, hFm, hFa, hasm.memcpy⟩
    · rw [hslots.negOdd64]; exact hNeg
    · rw [hslots.deintNeg]; exact hDN
    · rw [hslots.deintBfly]; exact hDB
  refine ⟨?_, ?_, ?_, ?_, ?_, hslots.lfGen, LfGen.spec hpl.lfGen k hk hasm.memset,
    hslots.hfInv, HfInverseFilter.spec hpl.hfInv _ hAc,
    hslots.hfAsm, HfAssemble.spec hpl.hfAsm k hk _ hHf,
    hslots.xGen, XGen.spec hpl.xGen k hk hasm.memset,
    QmfSynthesis.spec hpl.qmfSyn 0 k (by decide) hk _ _ _ hQ,
    QmfSynthesis.spec hpl.qmfSyn 1 k (by decide) hk _ _ _ hQ,
    hasm.txAna, hFr, hasm.memcpy, hasm.memset, hasm.psApply, hasm.avLog,
    abortSpec_holds⟩
  · rw [hslots.sum64x5]; exact hSum
  · rw [hslots.sumSquare]; exact hSq
  · rw [hslots.preShuffle]; exact hPre
  · rw [hslots.postShuffle]; exact hPost
  · rw [hslots.hfGen]; exact hGen

/-- **`ff_aac_sbr_apply`, linked.** `ApplySpec k e` (memory safety of
`ff_aac_sbr_apply(ac, che, id_aac, L, R)` with its callees at `k` bytes of
stack) under exactly three hypotheses: placement (`SbrPlaced`), slot contents
(`SbrSlots`) and the assumed external contracts (`SbrAssumed`).

What the statement does and does not say (as for `ApplySpec`):
1. hf_assemble's footprint includes the 24 bytes after Y[Ypos] (see `HfData`,
   `a2_row_spill`). For Ypos=0 the theorem itself bounds the access to Y[1] by
   these 24 bytes. For Ypos=1 those bytes belong to `g_temp`, which hf_assemble owns
   anyway, so there the 24-byte bound rests on `a2_row_spill` and the row-crossing
   discipline (HfAssemble crosses a row of `Y` only through `a2_row_spill`; checked
   by tv.sh), not on the footprint.
2. The synthesis footprint in `v0` is `qmfVSize` (D2); for the larger window the
   precondition owns the 2048 extra bytes (`a3_overread_carve`).
3. Granularity, under ruling (A): the theorem bounds each procedure's accesses by
   the union of the bytes it owns, and does not distinguish reads from writes.
   Within `ApplyF`'s union, object and row boundaries are not enforced by the
   theorem. Items 1 and 2 are fixed at the hf_assemble and synthesis boundaries and
   by `a2_row_spill`.
4. Trusted, all as hypotheses here:
   * `SbrAssumed`: the external contracts. These are not witnessed (no proof that
     real code meets them jointly).
   * `SbrPlaced`: placement of the texts, checked by tv.sh against the objects.
   * `SbrSlots`: the x86 dsp, `float_dsp` and `sbr->c` initialisation.
   Note F1: `vector_fmul_reverse`'s contract, assumed before its routines were
   proved, lacked the 32-byte mask `pd_reverse` that `ff_vector_fmul_reverse_avx2`
   reads; it is now in the contract, owned by the caller (`CstW`), its alignment in
   `LayoutC`.
5. Checked link facts, at source level: the sizes of the externals
   `ff_sbr_noise_table` and `ff_ps_neg` are checked against their source
   declarations, not against an object. Their alignment and ownership are
   conjuncts of the precondition (`LayoutC`, `ApplyF`), so they are obligations
   of the caller.
6. Satisfiability: `Witness.lean` shows `ApplyPre k e x ra t ∧ SbrSlots e` jointly
   satisfiable in four configurations: SCE downsampled; SCE+PS; CPE not downsampled with
   vOff = 1152; and not downsampled with the larger `qmfVSize` window. Those witnesses use a label-only
   ambient code (`Witness.wCE`), which places no text, so they do not give `SbrPlaced`.
   Closed: `Linked.lean` (`Linked.linked_hyps_sat_{sce,ps,cpe,a3}`) shows
   `SbrPlaced ∧ SbrSlots e ∧ ApplyPre k e x ra t` jointly satisfiable, in the same four
   configurations, under one ambient code: the laid-out image of every text (Apply, its
   five callees, the twelve dsp routines, the eight `float_dsp` routines) plus one cell per
   data label. -/
theorem ff_aac_sbr_apply_linked (hpl : SbrPlaced) (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env)
    (hslots : SbrSlots e) (hasm : SbrAssumed k e) : ApplySpec k e :=
  Apply.spec hpl.apply k hk e (applyCallees_of_link hpl k hk e hslots hasm)

end Kraken.Examples.Sbr
