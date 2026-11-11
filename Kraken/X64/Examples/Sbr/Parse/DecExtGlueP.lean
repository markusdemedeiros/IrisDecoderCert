import Kraken.X64.Examples.Sbr.Parse.DecExtGlueG
import Kraken.X64.Examples.Sbr.Parse.PsSpec

/-!
# `ff_aac_sbr_decode_extension`: the `ff_ps_read_data` adapter

`ps_glue`: `ff_ps_read_data`'s statement (`Ps.PsReadSpec k E`, with its tables `Ps.PsTabs vp` and
`Ps.VlcC vp`) gives the local `PsSpec Ps.PsInv (psNeed k)` for a caller's
`Ext = A ⋆ (B ⋆ (V ⋆ (Ps.PsTabs vp ⋆ E)))`; the routine's invariant `PI` is `Ps.PsInv`, and
`PsWF` is kept through `Ps.psWF_iff`.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply

namespace Kraken.Examples.Sbr.DecExt

variable [CodeEnv]

/-- The caller's part at the `ff_ps_read_data` call. -/
abbrev FrP (A B V : Mem 64 → Prop) (p : PA) : Mem 64 → Prop :=
  Block (lab "ceil_log2") 6 ⋆ (A ⋆ (B ⋆ (V ⋆ p.R)))

theorem psf_eq (A B V PT E : Mem 64 → Prop) (p : PA) (c : List UInt8) (a : BitVec 64)
    (i : BitVec 32) :
    (c =@ a ⋆ (GbR p.g p.r i ⋆ (BufW p.r ⋆ (A ⋆ (B ⋆ (V ⋆ (PT ⋆ E))))))) ⋆ p.R
      = (c =@ a ⋆ (GbR p.g p.r i ⋆ (Blocks [(p.r.buf, p.r.L)] ⋆ (PT ⋆ E)))) ⋆ FrP A B V p := by
  simp only [BufW, Blocks, FrP]; ac_rfl

/-- `ff_ps_read_data`'s logical variable at the call. -/
abbrev pxOf (A B V : Mem 64 → Prop) (vp : Nat → Ps.VlcTab) (p : PA) : Ps.PArgs :=
  ⟨FrP A B V p, p.c, p.r.buf, p.i, p.r.p8, p.r.L, vp⟩

/-- **`ff_ps_read_data`'s adapter.** -/
theorem ps_glue (k : Nat) (A B V E : Mem 64 → Prop) (vp : Nat → Ps.VlcTab) (hv : Ps.VlcC vp)
    (hP : Ps.PsReadSpec k E) :
    PsSpec Ps.PsInv (Ps.psNeed k) (A ⋆ (B ⋆ (V ⋆ (Ps.PsTabs vp ⋆ E)))) := by
  intro p ra t ⟨hcall, hrok, h1, _, hinv, hbits⟩
  have hpre : Ps.PsPre k E (pxOf A B V vp p) ra t := by
    refine ⟨?_, by unfold Ps.PsC; exact ⟨hinv, hv, hrok.1, hrok.2.1, hrok.2.2.1, hrok.2.2.2, hbits⟩⟩
    have hm : t.dmem =⋆ _ ⋆ (_ ⋆ ((p.c =@ arg2 t ⋆ (GbR p.g p.r p.i ⋆ (BufW p.r
      ⋆ (A ⋆ (B ⋆ (V ⋆ (Ps.PsTabs vp ⋆ E))))))) ⋆ p.R)) := hcall
    rw [psf_eq] at hm
    show t.dmem =⋆ _ ⋆ (_ ⋆ (Ps.PF E (pxOf A B V vp p) t p.c p.i ⋆ FrP A B V p))
    simp only [Ps.PF, h1]
    exact hm
  refine eventually_weaken _ _ _ _ (fun st hst => ⟨hst.1, ?_⟩) (hP _ ra t hpre)
  obtain ⟨c', i', ho, hsr, hbp, hsv, hm⟩ := hst.2
  obtain ⟨hinv', hwfb, hi, hr0, hr1⟩ := ho
  refine ⟨c', i', fun h hw => ?_, hinv'.1, hinv', hi, hr0, hr1, hsr, hbp, hsv, ?_⟩
  · obtain ⟨hb, hh⟩ := (Ps.psWF_iff p.c h).1 hw
    exact (Ps.psWF_iff c' h).2 ⟨hwfb hb, hh⟩
  · show st.1.dmem =⋆ _ ⋆ (_ ⋆ ((c' =@ arg2 t ⋆ (GbR p.g p.r i' ⋆ (BufW p.r
      ⋆ (A ⋆ (B ⋆ (V ⋆ (Ps.PsTabs vp ⋆ E))))))) ⋆ p.R))
    rw [psf_eq]
    simp only [Ps.PF, h1] at hm
    exact hm

end Kraken.Examples.Sbr.DecExt
