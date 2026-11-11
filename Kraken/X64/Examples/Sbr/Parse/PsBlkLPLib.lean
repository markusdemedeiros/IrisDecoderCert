import Kraken.X64.Examples.Sbr.Parse.PsBlkLLib
import Kraken.X64.Examples.Sbr.Parse.PsBlkL5

/-!
# `ff_ps_read_data`, the `icc` band loops and the `icc` memset: lemmas for `PsBlkLP*`
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Parse

namespace Kraken.Examples.Sbr.Ps

/-! ## The `icc` memset: 32-byte stores of zeros -/

/-- What the `icc` memset keeps of `WC` (the `icc` clause aside). -/
abbrev IccZ (c f : List UInt8) : Prop :=
  Rng0 c ∧ RngPO c ∧ Hdr c ∧ IidS c (rd f 0x18 4) ∧ IidB c (ne c) ∧ IidZ c

theorem lp_WZ_of_WC {c f : List UInt8} (h : WC c f) : IccZ c f :=
  ⟨⟨h.1.1, h.1.2.1⟩, h.1.2.2.2, h.2⟩

/-- A store into `icc_par` keeps `IccZ`. -/
theorem lp_WZ_wr {c f : List UInt8} {o n : Nat} (v : Int) (hl : c.length = 764) (h : IccZ c f)
    (ho : 246 ≤ o) (hn : o + n ≤ 416) : IccZ (wr c o n v) f := by
  obtain ⟨h0, hP, hH, hS, hB, hZ⟩ := h
  have e : ∀ o', o' + 4 ≤ 246 → i32 (wr c o n v) o' = i32 c o' :=
    fun o' hd => i32_wr c o n o' v (by omega) (Or.inl (by omega))
  have hne : ne (wr c o n v) = ne c := e 44 (by omega)
  refine ⟨Rng0_wr v hl h0 (by omega) (by omega), RngPO_wr v hl hP hn, Hdr_wr v hl hH (by omega)
    (by omega), IidS_wr v hl hS (by omega) (by omega), ?_, ?_⟩
  · rw [hne]; exact IidB_wr_icc v hl hB (by have := hH.2.1; omega) ho (by omega)
  · intro h4
    rw [e 4 (by omega)] at h4
    exact IidB_wr_icc v hl (hZ h4) (by omega) ho (by omega)

section
variable [CodeEnv]

/-- A store into `icc_par` keeps `AI` (same registers, new memory). -/
theorem lp_AI_wrc {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64} {t₀ s : MachineData}
    {c f : List UInt8} {o n : Nat} {v : Int} (h : AI k Ext x ra t₀ s c f) {s' : MachineData}
    (hr : s'.regs = s.regs)
    (hm : s'.dmem =⋆ Fr k Ext x ra t₀ f (wr c o n v) x.idx) (ho : 48 ≤ o) (hn : o + n ≤ 764) :
    AI k Ext x ra t₀ s' (wr c o n v) f := by
  obtain ⟨⟨⟨hC, ⟨hsp0, hbp0, hfl, hP, hb⟩, _⟩, hR, hI, ⟨⟨h0, h4, h58, h38⟩, h34, h68, h40⟩⟩,
    h10, h1c, hax⟩ := h
  have hl : c.length = 764 := hP.1
  have e : ∀ o', o' + 4 ≤ 48 → i32 (wr c o n v) o' = i32 c o' :=
    fun o' hd => i32_wr c o n o' v (by omega) (Or.inl (by omega))
  have hne : ne (wr c o n v) = ne c := e 44 (by omega)
  refine ⟨⟨⟨hC, ⟨by rw [hr]; exact hsp0, by rw [hr]; exact hbp0, hfl, PsInv_wr v hP ho hn, hb⟩,
    hm⟩, by simp only [Rdr, hr]; exact hR, by rw [hr]; exact hI,
    ⟨⟨?_, ?_, ?_, ?_⟩, ?_, h68, ?_⟩⟩, ?_, ?_, by rw [hr]; exact hax⟩
  all_goals first
    | (rw [hne]; assumption)
    | (rw [hr, hne]; assumption)
    | (rw [e 40 (by omega)]; assumption)
    | (rw [e 4 (by omega)]; assumption)
    | (rw [e 20 (by omega)]; assumption)

end

/-- A cleared `icc_par` is in range. -/
theorem lp_Rng_of {c : List UInt8} (h0 : Rng0 c) (hP : RngPO c) (hZ : Zr c 246 416) : Rng c := by
  refine ⟨h0.1, h0.2, ?_, hP⟩
  intro e he b hb
  have h1 := hZ (246 + 34 * e + b) (by omega) (by omega)
  simp only [i8, h1]
  decide

end Kraken.Examples.Sbr.Ps
