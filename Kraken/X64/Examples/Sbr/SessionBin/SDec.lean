import Kraken.X64.Examples.Sbr.SessionBin.Inv
import Kraken.X64.Examples.Sbr.SessionBin.DecAsm
import Kraken.X64.Examples.Sbr.SessionBin.FDec
import Kraken.X64.Examples.Sbr.SessionBin.SApply
import Kraken.X64.Examples.Sbr.SessionBin.LeafDerive

/-!
# A decoding session over the binary: a `decode_extension` call

At a reachable value the element and the call's objects are `decode_extension`'s footprint at
the values `toDS σ` with `DecRest` in the caller's memory (`FDecPre`); `DecC` holds from `SInv`
(`sreach_init_inv`) and the frame; `decAsm` runs the call; its outcome `DecOut` is a `Step.dec`,
and the footprint at the new values is the element again (`FDecPost`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Session Kraken.Examples.Sbr.Parse

namespace Kraken.Examples.Sbr.SessionBin

variable [CodeEnv]

/-- `ff_aac_sbr_decode_extension` in a session, from the footprint bridges `FDecPre`,
`FDecPost`. -/
theorem session_dec_of (fpre : FDecPre) (fpost : FDecPost) (hpl : SessPlaced) (k : Nat)
    (hk : 0x9d0 + k ≤ 2 ^ 32) (e : Env)
    (vs : Nat → Vlc.VlcTab) (vp : Nat → Ps.VlcTab) (pw : BitVec 32 → BitVec 32 → BitVec 32)
    (lg : BitVec 32 → BitVec 32) (has : SessionAssumed k e vs vp pw lg) (i : InitIn)
    {σ : SV} {ok : Bool} (hσ : SReach (σInit i) σ ok)
    {b : Rdr} {ix : BitVec 32} {Rc : Mem 64 → Prop} {ra : Int64} {t : MachineData}
    (hfr : DecFrame (decKc k) e vs vp σ b ix Rc ra t) :
    Eventually cenv.instrStep (fun st =>
      (st.2 = ra ∧ ∃ σ' i', SReach (σInit i) σ' true
        ∧ (σ'.1.avctx = σ.1.avctx ∧ σ'.1.ps = σ.1.ps) ∧ i'.toNat ≤ b.r.p8.toNat
        ∧ (st.1.regs.get64 .rax).setWidth 32 = (arg4 t).setWidth 32
        ∧ CallPost (DecExt.decNeed (decKc k)) (SessW e vs vp σ' t ⋆ DecObj b σ.1.avctx Rc i' t)
            ra t st.1)
      ∨ DecExt.DStops st.2)
      (t, entry "ff_aac_sbr_decode_extension") := by
  obtain ⟨a, b', hu, hi, ha, c, dd, hu2, hi2, hc, hd⟩ := hfr.own
  obtain ⟨sr, hF⟩ := fpre e vs vp σ b ix Rc t dd hd
  obtain ⟨hmi, hpi, hlb, hlens⟩ := (sreach_init_inv hσ).1
  have hel := hfr.elem
  have hdp : DecExt.DecPre Ps.PsInv (decKc k) (ExtD e vs vp)
      (xaOf (DecRest e σ.1 t ⋆ Rc) (toDS σ) b ix sr) ra t :=
    ⟨⟨a, b', hu, hi, ha, c, dd, hu2, hi2, hc, hF⟩, hmi, ⟨spBytes_length σ.1, rfl, rfl, hlens⟩,
      hpi, hfr.rd, hpl.jt, hfr.align, hlb, hel.1, sbrA_aligned hel.1, hel.2.1, hel.2.2⟩
  refine eventually_weaken _ _ _ _ (fun st h => h.imp (fun hr => ?_) id)
    (decAsm k e vs vp pw lg hk hpl has _ ra t hdp)
  obtain ⟨hra, d', i', hout, hi', hrax, h1, h2, h3, hm⟩ := hr
  have hav : d'.a.avctx = σ.1.avctx := hout.2.2.2.2.1.2.2.2.2.2.1
  have hm' := sep_imp_r2 (fun m hm => fpost e vs vp σ.1 d' b i' sr (DecRest e σ.1 t ⋆ Rc) Rc
    t m hout.2.2.2.2.1 hout.2.2.1.1 hm) hm
  rw [hav] at hm'
  exact ⟨hra, ofDS d', i', SReach.step (.dec 0#32) hσ (fun h => nomatch h) (fun h => nomatch h)
    (Step.dec d' hout), ⟨hav, hout.2.2.2.2.1.2.2.2.2.2.2⟩, hi', hrax, h1, h2, h3, hm'⟩

/-- **`ff_aac_sbr_decode_extension` in a session.** At every reachable value and every call state
with the caller's frame, the run returns to `ra` with the element at reachable values (flag set),
the reader's index within `size_in_bits_plus8`, `cnt` returned, the call's objects and the
caller's rest given back; or it stops at `abort` (`read_sbr_grid`'s assertion) or at the bounds
trap `read_sbr_envelope.L60f9`. -/
theorem session_dec (hpl : SessPlaced) (k : Nat) (hk : 0x9d0 + k ≤ 2 ^ 32) (e : Env)
    (vs : Nat → Vlc.VlcTab) (vp : Nat → Ps.VlcTab) (pw : BitVec 32 → BitVec 32 → BitVec 32)
    (lg : BitVec 32 → BitVec 32) (has : SessionAssumed k e vs vp pw lg) (i : InitIn)
    {σ : SV} {ok : Bool} (hσ : SReach (σInit i) σ ok)
    {b : Rdr} {ix : BitVec 32} {Rc : Mem 64 → Prop} {ra : Int64} {t : MachineData}
    (hfr : DecFrame (decKc k) e vs vp σ b ix Rc ra t) :
    Eventually cenv.instrStep (fun st =>
      (st.2 = ra ∧ ∃ σ' i', SReach (σInit i) σ' true
        ∧ (σ'.1.avctx = σ.1.avctx ∧ σ'.1.ps = σ.1.ps) ∧ i'.toNat ≤ b.r.p8.toNat
        ∧ (st.1.regs.get64 .rax).setWidth 32 = (arg4 t).setWidth 32
        ∧ CallPost (DecExt.decNeed (decKc k)) (SessW e vs vp σ' t ⋆ DecObj b σ.1.avctx Rc i' t)
            ra t st.1)
      ∨ DecExt.DStops st.2)
      (t, entry "ff_aac_sbr_decode_extension") :=
  session_dec_of fDecPre fDecPost hpl k hk e vs vp pw lg has i hσ hfr

end Kraken.Examples.Sbr.SessionBin
