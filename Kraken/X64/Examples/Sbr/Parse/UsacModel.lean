import Kraken.X64.Examples.Sbr.Parse.UsacBase

/-!
# `ff_aac_sbr_decode_usac_data`: the model steps between blocks

The invariants `MI`/`HI` of `ParseModel.lean` through the single stores of the body (fields the
invariants do not read, or read only through bounds the store keeps), the callees' contracts,
and the default header as a `Header true` step.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

namespace Kraken.Examples.Sbr.Usac

theorem mi_reset {x : Args} {h : Hid} (r : BitVec 32) (hm : MI (x, h)) :
    MI ({ x with reset := r }, h) := by
  obtain ⟨⟨a1, a2, a3, a4, a5, a6⟩, i1⟩ := hm
  exact ⟨⟨a1, a2, a3, a4, a5, a6⟩, i1⟩

theorem mi_srid {x : Args} {h : Hid} (sr id : BitVec 32) (hm : MI (x, h)) :
    MI ({ x with sampleRate := sr, idAac := id }, h) := by
  obtain ⟨⟨a1, a2, a3, a4, a5, a6⟩, i1⟩ := hm
  exact ⟨⟨a1, a2, a3, a4, a5, a6⟩, i1⟩

theorem mi_xover {x : Args} {h : Hid} (v : Nat) (hm : MI (x, h)) :
    MI (x, { h with xover := v }) := by
  obtain ⟨a, i1⟩ := hm
  exact ⟨a, i1⟩

theorem mi_ready {x : Args} {h : Hid} (hm : MI (x, h)) : MI ({ x with ready := 1#32 }, h) := by
  obtain ⟨⟨a1, a2, a3, a4, a5, a6⟩, i1⟩ := hm
  exact ⟨⟨a1, a2, a3, a4, a5, a6⟩, i1⟩

theorem mi_coupling {x : Args} {h : Hid} (c : BitVec 32) (hm : MI (x, h)) :
    MI ({ x with coupling := c }, h) := by
  obtain ⟨⟨a1, a2, a3, a4, a5, a6⟩, i1⟩ := hm
  exact ⟨⟨a1, a2, a3, a4, a5, a6⟩, i1⟩

theorem mi_d0 {x : Args} {h : Hid} {w : DV} (hm : MI (x, h)) (hw : DWF False w)
    (hb : u8 w.te w.nenv ≤ 19) : MI ({ x with d0 := w }, h) := by
  obtain ⟨⟨a1, a2, a3, a4, a5, a6⟩, i1⟩ := hm
  exact ⟨⟨a1, a2, hw, a4, a5, ⟨hb, a6.2⟩⟩, i1⟩

theorem mi_d1 {x : Args} {h : Hid} {w : DV} (hm : MI (x, h)) (hw : DWF False w)
    (hb : u8 w.te w.nenv ≤ 19) : MI ({ x with d1 := w }, h) := by
  obtain ⟨⟨a1, a2, a3, a4, a5, a6⟩, i1⟩ := hm
  exact ⟨⟨a1, a2, a3, hw, a5, ⟨a6.1, hb⟩⟩, i1⟩

theorem hi_kxm {x : Args} {h : Hid} (hi : HI (x, h)) :
    HI ({ x with kx0 := x.kx1, m0 := x.m1 }, h) := by
  obtain ⟨⟨-, b2, -, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩, a2, a3, a4, a5, a6, a7, i1⟩ := hi
  exact ⟨⟨b2, b2, b4, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩, a2, a3, a4, a5, a6, a7, i1⟩

theorem hi_pushed {x : Args} {h : Hid} (hi : HI (x, h)) : HI ({ x with pushed := 1#32 }, h) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, i1⟩ := hi
  exact ⟨a1, a2, a3, a4, a5, a6, a7, i1⟩

theorem hi_of_s1 {t₀ : MachineData} {st : USt} (h : S1 t₀ st) : SH t₀ st :=
  ⟨hi_of_mi h.1.1 h.1.2.1, h.2, h.1.2.2, fun hr => absurd h.1.2.1 hr⟩

/-- The single channel element (`sbr_ch = 1`, so `id_aac = 0`): a live channel 0 is enough. -/
theorem fin_sce {t₀ : MachineData} {st : USt} (h : SE0 t₀ st) (hc : chv t₀ = 1#32) : Fin st := by
  obtain ⟨⟨hm, hid, -⟩, hl⟩ := h
  refine ⟨hm, fun _ => hl, fun h2 => ?_⟩
  rw [hid] at h2
  simp only [idv, hc] at h2
  exact absurd h2.2 (by decide)

theorem fin_cpe {t₀ : MachineData} {st : USt} (h : SE01 t₀ st) : Fin st :=
  ⟨h.1.1, fun _ => h.2.1, fun _ => h.2.2⟩

/-- `Fin` gives what a return of `0` needs. -/
theorem out_fin {A : UA} {st : USt} {r : BitVec 32} (hi : Inv A st) (hf : Fin st) :
    UsacOut A st r :=
  ⟨hf.1, fun _ => hf.2, hi.1, hi.2.1, hi.2.2⟩

/-- A failure (`r ≠ 0`) needs only `MI`. -/
theorem out_fail {A : UA} {st : USt} {r : BitVec 32} (hi : Inv A st) (hm : MI (st.x, st.h))
    (hr : r ≠ 0#32) : UsacOut A st r :=
  ⟨hm, fun h => absurd h hr, hi.1, hi.2.1, hi.2.2⟩

end Kraken.Examples.Sbr.Usac
