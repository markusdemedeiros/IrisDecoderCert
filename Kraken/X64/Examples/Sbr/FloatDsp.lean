import Kraken.X64.Examples.Sbr.Dsp.VectorFmul
import Kraken.X64.Examples.Sbr.Dsp.VectorFmulAdd
import Kraken.X64.Examples.Sbr.Dsp.VectorFmulRev
import Kraken.X64.Examples.Sbr.SessionSpec

/-!
# `ff_aac_sbr_apply`: the `AVFloatDSPContext` routines together

`ff_aac_sbr_apply` calls three `AVFloatDSPContext` routines (through
`ac->fdsp`): `vector_fmul_reverse` (analysis), `vector_fmul` and
`vector_fmul_add` (synthesis). `ff_float_dsp_init_x86`
(`libavutil/x86/float_dsp_init.c`) installs, by cpu flags:

* `vector_fmul`: `ff_vector_fmul_sse` (SSE), `ff_vector_fmul_avx` (AVX);
* `vector_fmul_add`: `_sse` (SSE), `_avx` (AVX), `_fma3` (FMA3);
* `vector_fmul_reverse`: `_sse` (SSE), `_avx` (AVX), `_avx2` (AVX2).

Each later assignment overrides the earlier one, so each slot holds one of its
listed routines whenever SSE is present and the build has x86 asm (the same
premise as `SbrDspPlaced`: the C fallbacks of `libavutil/float_dsp.c` remain only
under `av_force_cpu_flags` without SSE or a `HAVE_X86ASM = 0` build).

`FloatDspPlaced` collects the placement of the eight texts, and the three
theorems below give each slot's contract for any routine it may hold.
-/

open Kraken

namespace Kraken.Examples.Sbr

variable [CodeEnv]

theorem vectorFmulSpec_of (h : FloatDspPlaced) (k : Nat) {f : Int64}
    (hf : f = entry "ff_vector_fmul_sse" ∨ f = entry "ff_vector_fmul_avx") :
    VectorFmulSpec k f := by
  obtain ⟨h1, h2, -⟩ := h
  rcases hf with rfl | rfl
  · exact VectorFmul.specSse h1 k
  · exact VectorFmul.specAvx h2 k

theorem vectorFmulAddSpec_of (h : FloatDspPlaced) (k : Nat) {f : Int64}
    (hf : f = entry "ff_vector_fmul_add_sse" ∨ f = entry "ff_vector_fmul_add_avx"
      ∨ f = entry "ff_vector_fmul_add_fma3") :
    VectorFmulAddSpec k f := by
  obtain ⟨-, -, h3, h4, h5, -⟩ := h
  rcases hf with rfl | rfl | rfl
  · exact VectorFmulAdd.specSse h3 k
  · exact VectorFmulAdd.specAvx h4 k
  · exact VectorFmulAdd.specFma3 h5 k

theorem vectorFmulRevSpec_of (h : FloatDspPlaced) (k : Nat) {f : Int64}
    (hf : f = entry "ff_vector_fmul_reverse_sse" ∨ f = entry "ff_vector_fmul_reverse_avx"
      ∨ f = entry "ff_vector_fmul_reverse_avx2") :
    VectorFmulRevSpec k f := by
  obtain ⟨-, -, -, -, -, h6, h7, h8⟩ := h
  rcases hf with rfl | rfl | rfl
  · exact VectorFmulRev.specSse h6 k
  · exact VectorFmulRev.specAvx h7 k
  · exact VectorFmulRev.specAvx2 h8 k

end Kraken.Examples.Sbr
