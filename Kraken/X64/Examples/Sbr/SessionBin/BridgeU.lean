import Kraken.X64.Examples.Sbr.SessionBin.Bridge
import Kraken.X64.Examples.Sbr.Parse.UsacSpec

/-!
# A decoding session over the binary: the `decode_usac_data` regrouping (statement)

`ff_aac_sbr_decode_usac_data`'s callees' states: `av_log`'s `e.Ext`, and `OthU` (`sbr_reset`'s
constants, the limiter table, the SBR and PS Huffman tables).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel

namespace Kraken.Examples.Sbr.SessionBin

variable [CodeEnv]

/-- The callees' state other than `av_log`'s. -/
def OthU (vs : Nat → Vlc.VlcTab) (vp : Nat → Ps.VlcTab) : Mem 64 → Prop :=
  Reset.CstR ⋆ (Reset.BwR ⋆ (Vlc.VlcW vs ⋆ Ps.PsTabs vp))

/-- `q` with the caller's rest `R` and the callees' states of the session. -/
def uq (e : Env) (vs : Nat → Vlc.VlcTab) (vp : Nat → Ps.VlcTab) (q : Usac.UQ)
    (R : Mem 64 → Prop) : Usac.UQ :=
  { q with R := R, Ext := e.Ext, Oth := OthU vs vp }

/-- **F-usac.** With `che = q.c`, `ac = q.a`, the element and the call's objects are `UF` at
the values `toUSt σ i` (with the caller's fixed values of `q`, the session's callee states, a rest
`R`), and any `UF` at values `st` that keep the fields outside it (`UKeep`, `SpOk`) is the element
at `ofUSt st it` for some `inter_tes = it` (raw in `UF`) with the call's objects at index
`st.i`. -/
def FUsac : Prop :=
  ∀ (e : Env) (vs : Nat → Vlc.VlcTab) (vp : Nat → Ps.VlcTab) (σ : SV) (q : Usac.UQ)
    (i : BitVec 32) (t : MachineData) (m : Mem 64),
    arg0 t = q.a → arg1 t = q.c →
    (SessW e vs vp σ t ⋆ UsacObj q i) m →
    ∃ R : Mem 64 → Prop, (Usac.UF (uq e vs vp q R) (toUSt σ i) ⋆ R) m
      ∧ ∀ (st : Usac.USt) (m' : Mem 64), Usac.UKeep σ.1 st.x → Usac.SpOk st →
        (Usac.UF (uq e vs vp q R) st ⋆ R) m' →
        ∃ it : BitVec 32, (SessW e vs vp (ofUSt st it) t ⋆ UsacObj q st.i) m'

end Kraken.Examples.Sbr.SessionBin
