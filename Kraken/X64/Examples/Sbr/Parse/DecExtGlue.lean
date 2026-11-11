import Kraken.X64.Examples.Sbr.Parse.DecExtSpec
import Kraken.X64.Examples.Sbr.Parse.HdrSpec
import Kraken.X64.Examples.Sbr.Parse.ResetSpec

/-!
# `ff_aac_sbr_decode_extension`: glue to the callees' own statements

The local contracts of `DecExtSpec` (`HdrSpec`, `ResetSpec`) state the callees on the whole decoder
state. The callees' own statements (`Hdr.HdrSpec`, `Reset.ResetSpec`) use smaller footprints and
their own values. This file holds the parts of the adapters between them:
* `ProcSpec.adapt`: a contract follows from another one at the same entry when every
  precondition of the first gives one of the second whose postcondition implies the first's.
* `reset_mi`: `sbr_reset`'s `ResetOut`, from `HI`, gives `MI` of the values left (with the hidden
  state read back from `spectrum_params`), `id_aac` and `ps->common` kept.
* `hdr_hi`: `read_sbr_header`'s `HdrOut`, from `MI` with no reset pending, is a model `Header`
  step, hence `HI` of the values left (`ParseModel.hdr_spec`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Session
open Kraken.Examples.Sbr.ParseModel

namespace Kraken.Examples.Sbr.DecExt

/-- Consequence for `ProcSpec` with a change of logical variable. -/
theorem ProcSpec.adapt {e : Kraken.Executable Directive} {l : Int64} {α β : Type}
    {Pre : α → Int64 → MachineData → Prop} {Post : α → Int64 → MachineData → MachineData → Prop}
    {Pre' : β → Int64 → MachineData → Prop} {Post' : β → Int64 → MachineData → MachineData → Prop}
    (hs : e.ProcSpec l Pre Post)
    (h : ∀ y ra t, Pre' y ra t → ∃ x, Pre x ra t ∧ ∀ s, Post x ra t s → Post' y ra t s) :
    e.ProcSpec l Pre' Post' := by
  intro y ra t hp
  obtain ⟨x, hx, himp⟩ := h y ra t hp
  exact eventually_weaken _ _ _ _ (fun st hst => ⟨hst.1, himp _ hst.2⟩) (hs x ra t hx)

/-- The hidden state read back from `spectrum_params` (bytes 0 and 2) and `bs_limiter_bands`. -/
abbrev hidOf (sp : List UInt8) (lb : Nat) : Hid := ⟨u8 sp 0, u8 sp 2, lb⟩

/-- `sbr_reset`'s outcome from `HI`: `MI`, `id_aac` and `ps->common` kept (as
`ParseModel.reset_step`, from `ResetOut` instead of the model's `Reset`). -/
theorem reset_mi {x : Args} {h : Hid} {sp : List UInt8} {lb us : BitVec 32} {x' : Args}
    {sp' : List UInt8} {us' : BitVec 32} (hi : HI (x, h)) (hs : h.start = u8 sp 0)
    (ho : Reset.ResetOut ⟨x, sp, lb, us⟩ x' sp' us') :
    MI (x', hidOf sp' h.lb) ∧ x'.idAac = x.idAac ∧ x'.psc = x.psc := by
  obtain ⟨a1, -, -, a4, a5, a6, a7, i1⟩ := hi
  obtain ⟨sc, -, y, ht, -, -, -, hz⟩ := ho
  obtain ⟨d0, d1⟩ := dwf_tframe ht a4 a5
  have hg := gridInv_tframe ht a7
  obtain ⟨-, -, -, hzs, hzid, hzpc, hzph, -, -, -, -, -⟩ := ht
  rcases hz with ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -, tz, n1, n2⟩
  · refine ⟨⟨⟨sc, fun h => absurd rfl h, d0, d1, ?_, hg⟩, fun _ => rfl⟩, hzid, hzpc⟩
    show PsWF y.psc y.psh
    rw [hzpc, hzph]; exact a6
  · refine ⟨⟨⟨sc, fun _ => ⟨tz, n1, n2⟩, d0, d1, ?_, hg⟩, fun h0 => ?_⟩, hzid, hzpc⟩
    · rw [hzpc, hzph]; exact a6
    · show u8 sp' 0 = 255
      rw [← hs]; exact i1 (by rw [← hzs]; exact h0)

/-- The scalar fields a header writes, with `reset = r`. -/
abbrev hdrSet (x : Args) (r : BitVec 32) (st : Hdr.HSt) : Args :=
  { x with start := 1, ready := 0, reset := r, limGains := st.lg.toNat, interpol := st.ip,
           smooth := st.sm }

/-- The values after a header (`HSt`), before `sbr_make_f_tablelim`. -/
abbrev hdrVals (x : Args) (st : Hdr.HSt) : Args := hdrSet x st.reset st

/-- `read_sbr_header`'s values (`Hdr.HdrOut`, `is_usac = 0`) as a model `Header` step from
`(x, h)`; `y` is the result of the optional `sbr_make_f_tablelim` (`Tablelim` when called). -/
theorem hdr_header {x : Args} {h : Hid} {hx : Hdr.HArgs} {st : Hdr.HSt} {ret : BitVec 32}
    {y : Args}
    (hr : x.reset = 0) (hrr : hx.reset = x.reset) (hs : h.start = u8 hx.sp 0)
    (hlb : hx.lb.toNat = h.lb) (ho : Hdr.HdrOut hx 0#32 st ret)
    (hy : if st.called hx then Tablelim st.lb.toNat (hdrVals x st) y else y = hdrVals x st) :
    Header false (x, h) (y, hidOf st.sp st.lb.toNat) := by
  obtain ⟨-, -, -, o0, -, o2, -, -, -, -, ores, olb, olg, -, -, -, -, -⟩ := ho
  have hres : st.reset = if decide (st.sp ≠ hx.sp) = true then 1 else x.reset := by
    rw [ores, hrr]; by_cases e : st.sp = hx.sp <;> simp [e]
  have hlim : HdrLim st.lb.toNat h.lb
      (hdrSet x (if decide (st.sp ≠ hx.sp) = true then 1 else x.reset) st) y := by
    rw [← hres]
    by_cases hc : st.called hx
    · rw [if_pos hc] at hy
      refine HdrLim.lim ?_ hc.2 hy
      intro e; apply hc.1; rw [← hlb] at e; exact BitVec.eq_of_toNat_eq e
    · rw [if_neg hc] at hy
      subst hy
      refine HdrLim.keep ?_
      by_cases e : st.lb = hx.lb
      · left; rw [e, hlb]
      · right; intro h0; exact hc ⟨e, h0⟩
  refine Header.mk (u8 st.sp 0) (u8 st.sp 2) st.lb.toNat st.lg.toNat 0 st.ip st.sm
    (decide (st.sp ≠ hx.sp)) o0 (fun _ => (o2 rfl).1) (fun e => absurd e (by decide)) olb olg
    (Or.inl rfl) ?_ hlim
  intro hne
  simp only [decide_eq_true_eq]
  intro e; apply hne; rw [hs, e]

/-- `read_sbr_header`'s values from `MI` with no reset pending: `HI`, `id_aac` kept. -/
theorem hdr_hi {x : Args} {h : Hid} {hx : Hdr.HArgs} {st : Hdr.HSt} {ret : BitVec 32} {y : Args}
    (hm : MI (x, h)) (hr : x.reset = 0) (hrr : hx.reset = x.reset) (hs : h.start = u8 hx.sp 0)
    (hlb : hx.lb.toNat = h.lb) (ho : Hdr.HdrOut hx 0#32 st ret)
    (hy : if st.called hx then Tablelim st.lb.toNat (hdrVals x st) y else y = hdrVals x st) :
    HI (y, hidOf st.sp st.lb.toNat) ∧ y.idAac = x.idAac :=
  hdr_spec hm hr (Or.inr (hdr_header hr hrr hs hlb ho hy))

end Kraken.Examples.Sbr.DecExt
