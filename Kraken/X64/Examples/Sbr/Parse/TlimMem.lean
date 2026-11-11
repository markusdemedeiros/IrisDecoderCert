import Kraken.X64.Examples.Sbr.Parse.TlimVar
import Kraken.X64.Examples.Sbr.Parse.TlimTab
import Kraken.X64.Examples.Sbr.Parse.Lib

/-!
# `sbr_make_f_tablelim`: focus equations and access lemmas

`T` is a separating conjunction of opaque groups. A block brings the group it touches to the
front with one of the AC equations below (`T_fl`, `T_nl`, `T_stk`, `T_pb`, `T_ro`, `T_fr`),
whose remainder does not mention that group's value, and applies an access lemma.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.Tlim

variable [CodeEnv]

section Focus

variable (k : Nat) (x : TArgs) (ra : Int64) (t₀ : MachineData)
  (FR : (Mem 64 → Prop) → Mem 64 → Prop)

/-- `T` without `f_tablelim`. -/
abbrev Tfl (nl : Nat) (stk pb : List UInt8) : Mem 64 → Prop :=
  let r := rS t₀
  8 ?@ (r - 0x450#64) ⋆ (Reserve k (r - 0x450#64)
    ⋆ (c4 (sA t₀ + 0x4c1ec#64) nl ⋆ (stk =@ (r - 0x448#64) ⋆ (pb =@ (r - 0x36#64)
    ⋆ (Junk r ⋆ (RO x t₀ ⋆ FR (Rest x.R ra t₀)))))))

theorem T_fl (st : TSt) :
    T k x ra t₀ FR st = st.fl =@ pA t₀ ⋆ Tfl k x ra t₀ FR st.nl st.stk st.pb := by
  simp only [T, Tfl]; ac_rfl

/-- `T` without `n_lim`. -/
abbrev Tnl (fl stk pb : List UInt8) : Mem 64 → Prop :=
  let r := rS t₀
  8 ?@ (r - 0x450#64) ⋆ (Reserve k (r - 0x450#64) ⋆ (fl =@ pA t₀
    ⋆ (stk =@ (r - 0x448#64) ⋆ (pb =@ (r - 0x36#64)
    ⋆ (Junk r ⋆ (RO x t₀ ⋆ FR (Rest x.R ra t₀)))))))

theorem T_nl (st : TSt) :
    T k x ra t₀ FR st = c4 (sA t₀ + 0x4c1ec#64) st.nl ⋆ Tnl k x ra t₀ FR st.fl st.stk st.pb := by
  simp only [T, Tnl]; ac_rfl

/-- `T` without the `AV_QSORT` stack. -/
abbrev Tstk (fl : List UInt8) (nl : Nat) (pb : List UInt8) : Mem 64 → Prop :=
  let r := rS t₀
  8 ?@ (r - 0x450#64) ⋆ (Reserve k (r - 0x450#64) ⋆ (fl =@ pA t₀
    ⋆ (c4 (sA t₀ + 0x4c1ec#64) nl ⋆ (pb =@ (r - 0x36#64)
    ⋆ (Junk r ⋆ (RO x t₀ ⋆ FR (Rest x.R ra t₀)))))))

theorem T_stk (st : TSt) :
    T k x ra t₀ FR st = st.stk =@ (rS t₀ - 0x448#64) ⋆ Tstk k x ra t₀ FR st.fl st.nl st.pb := by
  simp only [T, Tstk]; ac_rfl

/-- `T` without `patch_borders`. -/
abbrev Tpb (fl : List UInt8) (nl : Nat) (stk : List UInt8) : Mem 64 → Prop :=
  let r := rS t₀
  8 ?@ (r - 0x450#64) ⋆ (Reserve k (r - 0x450#64) ⋆ (fl =@ pA t₀
    ⋆ (c4 (sA t₀ + 0x4c1ec#64) nl ⋆ (stk =@ (r - 0x448#64)
    ⋆ (Junk r ⋆ (RO x t₀ ⋆ FR (Rest x.R ra t₀)))))))

theorem T_pb (st : TSt) :
    T k x ra t₀ FR st = st.pb =@ (rS t₀ - 0x36#64) ⋆ Tpb k x ra t₀ FR st.fl st.nl st.stk := by
  simp only [T, Tpb]; ac_rfl

/-- `T` without the read-only group. -/
abbrev Tro (st : TSt) : Mem 64 → Prop :=
  let r := rS t₀
  8 ?@ (r - 0x450#64) ⋆ (Reserve k (r - 0x450#64) ⋆ (st.fl =@ pA t₀
    ⋆ (c4 (sA t₀ + 0x4c1ec#64) st.nl ⋆ (st.stk =@ (r - 0x448#64) ⋆ (st.pb =@ (r - 0x36#64)
    ⋆ (Junk r ⋆ FR (Rest x.R ra t₀)))))))

theorem T_ro (st : TSt) : T k x ra t₀ FR st = RO x t₀ ⋆ Tro k x ra t₀ FR st := by
  simp only [T, Tro]; ac_rfl

/-- `T` without the frame part `FR`. -/
abbrev Tfr (st : TSt) : Mem 64 → Prop :=
  let r := rS t₀
  8 ?@ (r - 0x450#64) ⋆ (Reserve k (r - 0x450#64) ⋆ (st.fl =@ pA t₀
    ⋆ (c4 (sA t₀ + 0x4c1ec#64) st.nl ⋆ (st.stk =@ (r - 0x448#64) ⋆ (st.pb =@ (r - 0x36#64)
    ⋆ (Junk r ⋆ RO x t₀))))))

theorem T_fr (st : TSt) : T k x ra t₀ FR st = FR (Rest x.R ra t₀) ⋆ Tfr k x t₀ st := by
  simp only [T, Tfr]; ac_rfl

/-- `T` without `Junk`. -/
abbrev Tj (st : TSt) : Mem 64 → Prop :=
  let r := rS t₀
  8 ?@ (r - 0x450#64) ⋆ (Reserve k (r - 0x450#64) ⋆ (st.fl =@ pA t₀
    ⋆ (c4 (sA t₀ + 0x4c1ec#64) st.nl ⋆ (st.stk =@ (r - 0x448#64) ⋆ (st.pb =@ (r - 0x36#64)
    ⋆ (RO x t₀ ⋆ FR (Rest x.R ra t₀)))))))

theorem T_j (st : TSt) : T k x ra t₀ FR st = Junk (rS t₀) ⋆ Tj k x ra t₀ FR st := by
  simp only [T, Tj]; ac_rfl

end Focus

/-! ## The read-only fields -/

section RO

variable {m : Mem 64} {x : TArgs} {t₀ : MachineData} {F : Mem 64 → Prop}

theorem RO_lb (h : m =⋆ RO x t₀ ⋆ F) :
    m.loadInt (sA t₀ + 0x2c#64) 4 = some (Int.ofBytes (Int.toBytes 4 x.lb.toInt)) := by
  simp only [RO] at h
  obtain ⟨F, h⟩ := pick_ll h
  exact cell4_load h

theorem RO_n0 (h : m =⋆ RO x t₀ ⋆ F) :
    m.loadInt (sA t₀ + 0x4c1e0#64) 4 = some (Int.ofBytes (Int.toBytes 4 (x.a.n0 : Int))) := by
  simp only [RO] at h
  obtain ⟨F, h⟩ := pick_lr h
  obtain ⟨F, h⟩ := pick_lr h
  obtain ⟨F, h⟩ := pick_ll h
  exact loadInt_sep _ _ 4 F m h (Int.toBytes_length 4 _) (by omega)

end RO

/-! ## The frame -/

omit [CodeEnv] in
/-- The five pushes of the prologue fill the blank save slots. -/
theorem push5 {m : Mem 64} {r : BitVec 64} {K G : Mem 64 → Prop} (h : m =⋆ BlankS r K ⋆ G)
    (v1 v2 v3 v4 v5 : BitVec 64) :
    (m.loadInt (r - 8#64) 8).isSome = true
    ∧ ((m.storeInt (r - 8#64) 8 v1.toInt).loadInt (r - 16#64) 8).isSome = true
    ∧ (((m.storeInt (r - 8#64) 8 v1.toInt).storeInt (r - 16#64) 8 v2.toInt).loadInt
        (r - 24#64) 8).isSome = true
    ∧ ((((m.storeInt (r - 8#64) 8 v1.toInt).storeInt (r - 16#64) 8 v2.toInt).storeInt
        (r - 24#64) 8 v3.toInt).loadInt (r - 32#64) 8).isSome = true
    ∧ (((((m.storeInt (r - 8#64) 8 v1.toInt).storeInt (r - 16#64) 8 v2.toInt).storeInt
        (r - 24#64) 8 v3.toInt).storeInt (r - 32#64) 8 v4.toInt).loadInt
        (r - 40#64) 8).isSome = true
    ∧ ((((((m.storeInt (r - 8#64) 8 v1.toInt).storeInt (r - 16#64) 8 v2.toInt).storeInt
        (r - 24#64) 8 v3.toInt).storeInt (r - 32#64) 8 v4.toInt).storeInt
        (r - 40#64) 8 v5.toInt) =⋆
        (c8 (r - 0x28#64) v5 ⋆ (c8 (r - 0x20#64) v4 ⋆ (c8 (r - 0x18#64) v3
          ⋆ (c8 (r - 0x10#64) v2 ⋆ (c8 (r - 0x8#64) v1 ⋆ K))))) ⋆ G) := by
  simp only [BlankS] at h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> cells_grind

end Kraken.Examples.Sbr.Tlim
