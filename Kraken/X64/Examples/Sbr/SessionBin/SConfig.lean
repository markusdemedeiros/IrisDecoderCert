import Kraken.X64.Examples.Sbr.SessionBin.Inv
import Kraken.X64.Examples.Sbr.SessionBin.Bridge
import Kraken.X64.Examples.Sbr.SessionBin.FCfg
import Kraken.X64.Examples.Sbr.SessionBin.SApply
import Kraken.X64.Examples.Sbr.Parse.UsacCfg

/-!
# A decoding session over the binary: a `config_usac` call

At a reachable value the element is `config_usac`'s footprint at the values `toUSt σ i` (`FCfg`);
`MI` and `SpOk` hold there (`sreach_init_inv`); `configSpec_holds` runs the call; its
postcondition (`stOff`, `SpOk`, `UKeep`) is a `Step.config`, and the element at the new values is
given back by `FCfg`'s second half.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Session Kraken.Examples.Sbr.Parse

namespace Kraken.Examples.Sbr.SessionBin

/-- `MI` and `SpOk` at `toUSt σ i` from `SInv σ`. -/
theorem toUSt_ok {σ : SV} (h : SInv σ) (i : BitVec 32) :
    MI ((toUSt σ i).x, (toUSt σ i).h) ∧ Usac.SpOk (toUSt σ i) :=
  ⟨h.1, spBytes_length σ.1, rfl, rfl, h.2.2.1, h.2.2.2⟩

variable [CodeEnv]

/-- `ff_aac_sbr_config_usac` in a session, from the footprint bridge `FCfg`. -/
theorem session_config_of (hc : FCfg) (hpl : SessPlaced) (e : Env) (vs : Nat → Vlc.VlcTab)
    (vp : Nat → Ps.VlcTab) (i : InitIn) {σ : SV} {ok : Bool} (hσ : SReach (σInit i) σ ok)
    {Rc : Mem 64 → Prop} {ra : Int64} {t : MachineData} (hfr : ConfigFrame e vs vp σ Rc ra t) :
    Eventually cenv.instrStep (fun st => st.2 = ra ∧ ∃ σ', SReach (σInit i) σ' true
        ∧ (σ'.1.avctx = σ.1.avctx ∧ σ'.1.extRate = σ.1.extRate ∧ σ'.1.ps = σ.1.ps)
        ∧ (st.1.regs.get64 .rax).setWidth 32 = 0#32
        ∧ CallPost 0 (SessW e vs vp σ' t ⋆ Rc) ra t st.1)
      (t, entry "ff_aac_sbr_config_usac") := by
  obtain ⟨a, b, hu, hi, ha, c, d, hu2, hi2, hcr, hd⟩ := hfr.own
  obtain ⟨q, ix, -, hq1, hq, hk⟩ := hc e vs vp σ t Rc d hd
  obtain ⟨hmi, hsp⟩ := toUSt_ok (sreach_init_inv hσ).1 ix
  have hpre : Usac.ConfigPre (q, toUSt σ ix) ra t :=
    ⟨⟨a, b, hu, hi, ha, c, d, hu2, hi2, hcr, hq⟩, hmi, hsp, hq1.symm⟩
  refine eventually_weaken _ _ _ _ (fun st ⟨hra, hpost⟩ => ⟨hra, ?_⟩)
    (Usac.configSpec_holds hpl.config (q, toUSt σ ix) ra t hpre)
  obtain ⟨u, hst, -, hsp', hkp, hrax, h1, h2, h3, hm⟩ := hpost
  have hm' := sep_imp_r2 (fun m hm => hk u m hkp hsp' hm) hm
  obtain ⟨it, hmu⟩ := sep_ex_r2 hm'
  exact ⟨ofUSt u it, SReach.step .config hσ (fun h => nomatch h) (fun h => nomatch h)
    (Step.config u it hst hsp' hkp), ⟨hkp.2.2.2.2.2.2.1, hkp.2.2.2.2.2.2.2, hkp.2.2.2.2.2.1⟩,
    hrax, h1, h2, h3, hmu⟩

/-- **`ff_aac_sbr_config_usac` in a session.** At every reachable value and every call state
with the caller's frame, the run returns `0` to `ra` with the element at reachable values (flag
set) and the caller's rest. -/
theorem session_config (hpl : SessPlaced) (e : Env) (vs : Nat → Vlc.VlcTab)
    (vp : Nat → Ps.VlcTab) (i : InitIn) {σ : SV} {ok : Bool} (hσ : SReach (σInit i) σ ok)
    {Rc : Mem 64 → Prop} {ra : Int64} {t : MachineData} (hfr : ConfigFrame e vs vp σ Rc ra t) :
    Eventually cenv.instrStep (fun st => st.2 = ra ∧ ∃ σ', SReach (σInit i) σ' true
        ∧ (σ'.1.avctx = σ.1.avctx ∧ σ'.1.extRate = σ.1.extRate ∧ σ'.1.ps = σ.1.ps)
        ∧ (st.1.regs.get64 .rax).setWidth 32 = 0#32
        ∧ CallPost 0 (SessW e vs vp σ' t ⋆ Rc) ra t st.1)
      (t, entry "ff_aac_sbr_config_usac") :=
  session_config_of fCfg hpl e vs vp i hσ hfr

end Kraken.Examples.Sbr.SessionBin
