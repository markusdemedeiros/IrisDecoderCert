import Kraken.X64.Examples.Sbr.SessionBin.UsacAsmS
import Kraken.X64.Examples.Sbr.SessionBin.SConfig
import Kraken.X64.Examples.Sbr.SessionBin.FUsac
import Kraken.X64.Examples.Sbr.SessionBin.LeafDerive

/-!
# A decoding session over the binary: a `decode_usac_data` call

At a reachable value the element and the call's objects are `decode_usac_data`'s footprint `UF`
at the values `toUSt σ i` (`FUsac`); `UsacC` holds from `SInv` (`sreach_init_inv`) and the frame;
`usacAsm` runs the call; its outcome `UsacOut` is a `Step.usac`, and the footprint at the new
values is the element again (`FUsac`'s second half).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Session Kraken.Examples.Sbr.Parse

namespace Kraken.Examples.Sbr.SessionBin

variable [CodeEnv]

/-- `ff_aac_sbr_decode_usac_data` in a session, from the footprint bridge `FUsac`. -/
theorem session_usac_of (hb : FUsac) (hpl : SessPlaced) (k : Nat) (hk : 0x9d0 + k ≤ 2 ^ 32)
    (e : Env) (vs : Nat → Vlc.VlcTab) (vp : Nat → Ps.VlcTab)
    (pw : BitVec 32 → BitVec 32 → BitVec 32) (lg : BitVec 32 → BitVec 32)
    (has : SessionAssumed k e vs vp pw lg) (i : InitIn) (cpe : Bool)
    {σ : SV} {ok : Bool} (hσ : SReach (σInit i) σ ok)
    {q : Usac.UQ} {ix : BitVec 32} {ra : Int64} {t : MachineData}
    (hfr : UsacFrame (usacK k) e vs vp σ q ix ra t) :
    Eventually cenv.instrStep (fun st =>
      (st.2 = ra ∧ ∃ σ' i', SReach (σInit i) σ' (decide ((st.1.regs.get64 .rax).setWidth 32 = 0#32))
        ∧ (σ'.1.avctx = σ.1.avctx ∧ σ'.1.extRate = σ.1.extRate ∧ σ'.1.ps = σ.1.ps)
        ∧ i'.toNat ≤ q.p8.toNat
        ∧ CallPost (Usac.usacNeed (usacK k)) (SessW e vs vp σ' t ⋆ UsacObj q i') ra t st.1)
      ∨ Usac.usacStops st.2)
      (t, entry "ff_aac_sbr_decode_usac_data") := by
  obtain ⟨a, b', hu, hi, ha, c, dd, hu2, hi2, hc, hd⟩ := hfr.own
  obtain ⟨ha0, ha1, ha2, ha3⟩ := hfr.args
  obtain ⟨R, hUF, hk'⟩ := hb e vs vp σ q ix t dd ha0 ha1 hd
  obtain ⟨hmi, hsp⟩ := toUSt_ok (sreach_init_inv hσ).1 ix
  obtain ⟨u1, u2, u3, u4⟩ := hfr.ue
  obtain ⟨hal1, -, hwr⟩ := hfr.elem
  have hal := sbrA_aligned hal1
  have hs : sbrA t = Usac.sA q.c := by simp only [sbrA, Usac.sA, ha1]
  have hlay : Usac.LayU (uq e vs vp q R) := by
    refine ⟨?_, ?_⟩
    · show (Usac.sA q.c).toNat + 0x60000 < 2 ^ 64
      rw [← hs]; exact hwr
    · show (Usac.sA q.c).toNat % 32 = 0
      rw [← hs]; simpa [isAligned] using hal
  have hpre : Usac.UsacPre (usacK k) (uq e vs vp q R, toUSt σ ix) ra t
      ∧ Usac.QE e.Ext (OthU vs vp) (uq e vs vp q R) :=
    ⟨⟨⟨a, b', hu, hi, ha, c, dd, hu2, hi2, hc, hUF⟩,
      ⟨hmi, hsp, hfr.rd.1, hfr.rd.2, ⟨u1, u2, u3, u4, hfr.uev3⟩, hpl.jt, hlay⟩,
      ha0, ha1, ha2, ha3, hfr.align⟩, rfl, rfl⟩
  refine eventually_weaken _ _ _ _ (fun st h => h.imp (fun hr => ?_) id)
    (usacAsm k e vs vp pw lg hk hpl has _ ra t hpre)
  obtain ⟨hra, u, ⟨hmi', hlive, hkeep, hsp', hi'⟩, h1, h2, h3, hm⟩ := hr
  have hm' := sep_imp_r2 (fun m hm => hk' u m hkeep hsp' hm) hm
  obtain ⟨it, hmu⟩ := sep_ex_r2 hm'
  exact ⟨hra, ofUSt u it, u.i, SReach.step (.usac cpe) hσ (fun h => nomatch h)
    (fun h => nomatch h) (Step.usac u _ it hmi' hlive hkeep hsp' hsp'.2.2.2.1 hsp'.2.2.2.2),
    ⟨hkeep.2.2.2.2.2.2.1, hkeep.2.2.2.2.2.2.2, hkeep.2.2.2.2.2.1⟩, hi', h1, h2, h3, hmu⟩

/-- **`ff_aac_sbr_decode_usac_data` in a session.** At every reachable value and every call state
with the caller's frame, the run returns to `ra` with the element at reachable values (the flag
set iff it returns `0`), the reader's index within `size_in_bits_plus8`, the call's objects; or it
stops at `abort` (`read_sbr_grid`'s assertion) or at the bounds trap `read_sbr_envelope.L60f9`. -/
theorem session_usac (hpl : SessPlaced) (k : Nat) (hk : 0x9d0 + k ≤ 2 ^ 32)
    (e : Env) (vs : Nat → Vlc.VlcTab) (vp : Nat → Ps.VlcTab)
    (pw : BitVec 32 → BitVec 32 → BitVec 32) (lg : BitVec 32 → BitVec 32)
    (has : SessionAssumed k e vs vp pw lg) (i : InitIn) (cpe : Bool)
    {σ : SV} {ok : Bool} (hσ : SReach (σInit i) σ ok)
    {q : Usac.UQ} {ix : BitVec 32} {ra : Int64} {t : MachineData}
    (hfr : UsacFrame (usacK k) e vs vp σ q ix ra t) :
    Eventually cenv.instrStep (fun st =>
      (st.2 = ra ∧ ∃ σ' i', SReach (σInit i) σ' (decide ((st.1.regs.get64 .rax).setWidth 32 = 0#32))
        ∧ (σ'.1.avctx = σ.1.avctx ∧ σ'.1.extRate = σ.1.extRate ∧ σ'.1.ps = σ.1.ps)
        ∧ i'.toNat ≤ q.p8.toNat
        ∧ CallPost (Usac.usacNeed (usacK k)) (SessW e vs vp σ' t ⋆ UsacObj q i') ra t st.1)
      ∨ Usac.usacStops st.2)
      (t, entry "ff_aac_sbr_decode_usac_data") :=
  session_usac_of fUsac hpl k hk e vs vp pw lg has i cpe hσ hfr

end Kraken.Examples.Sbr.SessionBin
