import Kraken.X64.Examples.Sbr.SessionBin.InitSafe
import Kraken.X64.Examples.Sbr.SessionBin.TopCalls
import Kraken.X64.Examples.Sbr.SessionSpec

/-!
# A decoding session over the binary: the headline

`sbr_session_safe`: for the linked machine code of FFmpeg's SBR decoder (`aacsbr.o` with its
callees), given the layout of the link (`SbrBinary`), the contracts of the external routines
(`InitExt`) and a 32-bit bound on their stack, every entry point is safe in every session:

* `ff_aac_sbr_ctx_alloc_init` returns; on `0` the element it allocated is `Live`;
* `ff_aac_sbr_decode_extension`, `ff_aac_sbr_decode_usac_data`, `ff_aac_sbr_config_usac` on a
  `Live` element return with it `Live` again (`Ready` when the parse succeeded), or (the two
  parsers) stop at FFmpeg's `abort`/bounds trap (`Traps`);
* `ff_aac_sbr_apply` on a `Ready` element returns with it `Ready` and the output written.

Every run stays in the memory it owns (the separation-logic pre/postconditions), returns to its
caller with the ABI's callee-saved registers, and uses at most the stated stack. The vocabulary
is in `TopDefs`; the four restatements are in `TopCalls`; init's is in `InitSafe`.

The Huffman tables are FFmpeg's (`Setup.vs`, `Setup.vp`); their prefix-code and bound facts are
proved (`VlcWit`), not assumed.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Session Kraken.Examples.Sbr.Parse Kraken.Examples.Sbr.Init

namespace Kraken.Examples.Sbr.SessionBin

variable [CodeEnv]

/-- **The SBR decoder's binary is safe in every session.** Given the link's layout, the
external routines' contracts at the caller's environment, and their stack `S.k` within a
32-bit offset of `sbr_reset`'s frame, every entry point meets its contract. -/
theorem sbr_session_safe (B : SbrBinary) (S : Setup) (X : Mem 64 → Prop) (hx : InitExt S X)
    (hk : 0x9d0 + S.k ≤ 2 ^ 32) :
    InitSafe S X ∧ DecSafe S ∧ UsacSafe S ∧ ConfigSafe S ∧ ApplySafe S :=
  ⟨fun hpre => init_safe B.init hx hpre, fun hc hm => dec_top B S hk hc hm,
    fun hc hm => usac_top B S hk hc hm, fun hc hm => config_top B S hc hm,
    fun hc hm => apply_top B S hk hc hm⟩

end Kraken.Examples.Sbr.SessionBin
