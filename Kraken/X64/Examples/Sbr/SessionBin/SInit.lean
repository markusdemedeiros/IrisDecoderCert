import Kraken.X64.Examples.Sbr.SessionBin.Defs
import Kraken.X64.Examples.Sbr.Parse.InitLink

/-!
# A decoding session over the binary: the start

`ff_aac_sbr_ctx_alloc_init`'s memory on success (the element at `evInit`, the contexts, the
caller's cells and constants) is the session's element `SessW` at the initial values
`σInit (inOf r …)` in the environment `envOf e₀ r` built from init's results, with the bytes of
the element outside it (`InitGap`) and the caller's rest (`Init.init_sessW`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Session Kraken.Examples.Sbr.Parse Kraken.Examples.Sbr.Init

namespace Kraken.Examples.Sbr.SessionBin

variable [CodeEnv]

/-- **The session's start.** -/
theorem session_init {e₀ : Env} {r : IR} {id : BitVec 32} {R : Mem 64 → Prop}
    {avctx fdsp : BitVec 64} {extRate ps : BitVec 32} (vs : Nat → Vlc.VlcTab)
    (vp : Nat → Ps.VlcTab) {t : MachineData} {m : Mem 64} {F : Mem 64 → Prop}
    (hp : arg1 t = r.p) (hpsd : r.psd.length = 64)
    (h : m =⋆ ElemS r.p (evInit id r) ⋆ (e₀.Ctx r.anaCtx ⋆ (e₀.Ctx r.synCtx
      ⋆ (AcW (xInit (inOf r id R avctx fdsp extRate ps)) t ⋆ (FdspW e₀ fdsp ⋆ (e₀.TxTab
      ⋆ (e₀.PsTab ⋆ (e₀.Ext ⋆ (CstW ⋆ (PStat vs vp ⋆ F)))))))))) :
    m =⋆ SessW (envOf e₀ r) vs vp (σInit (inOf r id R avctx fdsp extRate ps)) t
      ⋆ (InitGap r.p ⋆ F) :=
  init_sessW (d := toDS (σInit (inOf r id R avctx fdsp extRate ps))) hp hpsd rfl rfl rfl rfl
    rfl rfl h

end Kraken.Examples.Sbr.SessionBin
