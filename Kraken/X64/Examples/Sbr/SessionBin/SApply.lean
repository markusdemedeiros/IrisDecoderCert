import Kraken.X64.Examples.Sbr.SessionBin.Inv
import Kraken.X64.Examples.Sbr.SessionBin.FApply
import Kraken.X64.Examples.Sbr.Link
import Kraken.X64.Examples.Sbr.SessionBin.LeafDerive

/-!
# A decoding session over the binary: an apply call

At a reachable value with the flag set, the element and the output buffers are apply's
footprint (`fApplyPre`) with the gaps in the caller's memory `x.R`; `SbrWF` holds
(`sreach_wf`); the linked theorem runs the call; its postcondition is the element at the values
`(y, …)` again (`fApplyPost`), which are reachable (`Step.apply`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Session Kraken.Examples.Sbr.Parse

namespace Kraken.Examples.Sbr.SessionBin

/-! ## Separation helpers -/

theorem sep_imp_r {A P Q : Mem 64 → Prop} (h : ∀ m, P m → Q m) {m : Mem 64}
    (hm : (A ⋆ P) m) : (A ⋆ Q) m := by
  obtain ⟨a, b, hu, hi, ha, hb⟩ := hm
  exact ⟨a, b, hu, hi, ha, h b hb⟩

theorem sep_imp_r2 {A B P Q : Mem 64 → Prop} (h : ∀ m, P m → Q m) {m : Mem 64}
    (hm : (A ⋆ (B ⋆ P)) m) : (A ⋆ (B ⋆ Q)) m :=
  sep_imp_r (fun _ h' => sep_imp_r h h') hm

theorem sep_ex_r2 {α : Type} {A B : Mem 64 → Prop} {P : α → Mem 64 → Prop} {m : Mem 64}
    (hm : (A ⋆ (B ⋆ fun m => ∃ u, P u m)) m) : ∃ u, (A ⋆ (B ⋆ P u)) m := by
  obtain ⟨a, b, hu, hi, ha, c, d, hu2, hi2, hc, u, hd⟩ := hm
  exact ⟨u, a, b, hu, hi, ha, c, d, hu2, hi2, hc, hd⟩

/-- The output buffers' sizes read only the two rates. -/
theorem outW_congr {x y : Args} (t : MachineData) (h1 : y.extRate = x.extRate)
    (h2 : y.sampleRate = x.sampleRate) : OutW y t = OutW x t := by
  unfold OutW dsN; rw [h1, h2]

variable [CodeEnv]

/-- **`ff_aac_sbr_apply` in a session.** At every reachable value with the flag set and every
call state with the caller's frame, the run returns to `ra` with the element at reachable values
(flag set), the output buffers and the caller's rest. -/
theorem session_apply (hpl : SessPlaced) (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env)
    (vs : Nat → Vlc.VlcTab) (vp : Nat → Ps.VlcTab) (pw : BitVec 32 → BitVec 32 → BitVec 32)
    (lg : BitVec 32 → BitVec 32) (hslots : SbrSlots e) (has : SessionAssumed k e vs vp pw lg)
    (i : InitIn) {σ : SV} (hσ : SReach (σInit i) σ true)
    {Rc : Mem 64 → Prop} {ra : Int64} {t : MachineData} (hfr : ApplyFrame k e vs vp σ Rc ra t) :
    Eventually cenv.instrStep (fun st => st.2 = ra ∧ ∃ σ', SReach (σInit i) σ' true
        ∧ (σ'.1.avctx = σ.1.avctx ∧ σ'.1.extRate = σ.1.extRate ∧ σ'.1.ps = σ.1.ps)
        ∧ CallPost (applyNeed k) (SessW e vs vp σ' t ⋆ (OutW σ.1 t ⋆ Rc)) ra t st.1)
      (t, entry "ff_aac_sbr_apply") := by
  let x : Args := { σ.1 with R := GapA σ.2 t ⋆ (PStat vs vp ⋆ Rc) }
  have hpre : ApplyPre k e x ra t := by
    obtain ⟨l1, l2, l8, wds, neg, mk, wus, mk2, mk3, n0, n13, n2, pd⟩ := hpl.labs
    refine ⟨?_, sreach_wf hσ, hfr.elem.1, sbrA_aligned hfr.elem.1, hfr.out.1, hfr.out.2,
      hfr.align, l1, l2, l8, wds, neg, ⟨mk, wus, mk2⟩, mk3, ⟨n0, n13, n2⟩, pd, hfr.elem.2.1⟩
    exact sep_imp_r2 (fun m hm => fApplyPre e vs vp σ t Rc m hm) hfr.own
  refine eventually_weaken _ _ _ _ (fun st ⟨hra, hpost⟩ => ⟨hra, ?_⟩)
    (ff_aac_sbr_apply_linked hpl.apply k hk e hslots ⟨has.psApply, has.txAna, has.txSyn,
      memcpy_of_val has.memcpyV, memset_of_val has.memsetV, has.avLog⟩ x ra t hpre)
  obtain ⟨h1, h2, h3, hm⟩ := hpost
  obtain ⟨y, hy, hmy⟩ := post_mem hm
  have hmy' := sep_imp_r2 (fun m hm => fApplyPost e vs vp y σ.2 t Rc m hm) hmy
  obtain ⟨u, hmu⟩ := sep_ex_r2 hmy'
  have hout : OutW y t = OutW σ.1 t := outW_congr t hy.1 hy.2.2.2.2.1
  refine ⟨(y, { σ.2 with usac := u }), ?_, ⟨hy.2.2.2.2.2.2.2.1, hy.1, hy.2.2.2.2.2.2.2.2⟩,
    h1, h2, h3, ?_⟩
  · exact SReach.step .apply hσ (fun _ => rfl) (fun h => nomatch h) (Step.apply u hy)
  · rw [hout] at hmu; exact hmu

end Kraken.Examples.Sbr.SessionBin
