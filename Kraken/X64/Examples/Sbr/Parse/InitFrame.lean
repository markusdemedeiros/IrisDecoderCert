import Kraken.X64.Examples.Sbr.Parse.InitBase
import Kraken.X64.Examples.Sbr.Parse.LibMem

/-!
# `ff_aac_sbr_ctx_alloc_init`: the frame

The prologue's pushes, the arrangements of the memory at a call (the return slot and the
callee's reservation in front, the callee's footprint, the rest as its frame), the pops.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr
open Kraken.Examples.Sbr.Apply (c8)
open Kraken.Examples.Sbr.Session (zs)
open Kraken.Examples.Sbr.Parse (slot_load slot_set)

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.Init

variable [CodeEnv]

section Frame

variable {m : Mem 64} {k : Nat} {TxTab X B E : Mem 64 → Prop} {t₀ : MachineData}

omit [CodeEnv]

/-- `push %rbp; …; push %rbx`: the store checks and the frame after. -/
theorem M_push (r : BitVec 64) (hr : t₀.regs.get64 .rsp = r)
    (h : m =⋆ MF k TxTab X t₀ (FrB t₀) B E) (v1 v2 v3 v4 : BitVec 64) :
    (m.loadInt (r - 8#64) 8).isSome = true
    ∧ ((m.storeInt (r - 8#64) 8 v1.toInt).loadInt (r - 16#64) 8).isSome = true
    ∧ (((m.storeInt (r - 8#64) 8 v1.toInt).storeInt (r - 16#64) 8 v2.toInt).loadInt
        (r - 24#64) 8).isSome = true
    ∧ ((((m.storeInt (r - 8#64) 8 v1.toInt).storeInt (r - 16#64) 8 v2.toInt).storeInt
        (r - 24#64) 8 v3.toInt).loadInt (r - 32#64) 8).isSome = true
    ∧ (((m.storeInt (r - 8#64) 8 v1.toInt).storeInt (r - 16#64) 8 v2.toInt).storeInt
        (r - 24#64) 8 v3.toInt).storeInt (r - 32#64) 8 v4.toInt
      =⋆ MF k TxTab X t₀ (c8 (r - 0x8#64) v1 ⋆ (c8 (r - 0x10#64) v2 ⋆ (c8 (r - 0x18#64) v3
        ⋆ (c8 (r - 0x20#64) v4 ⋆ (4 ?@ (r - 0x24#64) ⋆ (12 ?@ (r - 0x30#64)
        ⋆ 8 ?@ (r - 0x38#64))))))) B E := by
  simp only [MF, FrB, c8, hr] at h ⊢
  rw [Std.ExtHashMap.sep_assoc] at h
  have h1 := slot_set h v1.toInt
  have h1' : _ =⋆ 8 ?@ (r - 0x10#64) ⋆ (Int.toBytes 8 v1.toInt =@ (r - 0x8#64)
      ⋆ ((8 ?@ (r - 0x18#64) ⋆ (8 ?@ (r - 0x20#64) ⋆ (4 ?@ (r - 0x24#64) ⋆ (12 ?@ (r - 0x30#64)
        ⋆ 8 ?@ (r - 0x38#64))))) ⋆ (8 ?@ (r - 0x40#64) ⋆ (Reserve k (r - 0x40#64)
        ⋆ (B ⋆ (TxTab ⋆ (X ⋆ E))))))) := Mem.ac h1
  have h2 := slot_set h1' v2.toInt
  have h2' : _ =⋆ 8 ?@ (r - 0x18#64) ⋆ (Int.toBytes 8 v2.toInt =@ (r - 0x10#64)
      ⋆ (Int.toBytes 8 v1.toInt =@ (r - 0x8#64)
      ⋆ ((8 ?@ (r - 0x20#64) ⋆ (4 ?@ (r - 0x24#64) ⋆ (12 ?@ (r - 0x30#64)
        ⋆ 8 ?@ (r - 0x38#64)))) ⋆ (8 ?@ (r - 0x40#64) ⋆ (Reserve k (r - 0x40#64)
        ⋆ (B ⋆ (TxTab ⋆ (X ⋆ E)))))))) := Mem.ac h2
  have h3 := slot_set h2' v3.toInt
  have h3' : _ =⋆ 8 ?@ (r - 0x20#64) ⋆ (Int.toBytes 8 v3.toInt =@ (r - 0x18#64)
      ⋆ (Int.toBytes 8 v2.toInt =@ (r - 0x10#64) ⋆ (Int.toBytes 8 v1.toInt =@ (r - 0x8#64)
      ⋆ ((4 ?@ (r - 0x24#64) ⋆ (12 ?@ (r - 0x30#64)
        ⋆ 8 ?@ (r - 0x38#64))) ⋆ (8 ?@ (r - 0x40#64) ⋆ (Reserve k (r - 0x40#64)
        ⋆ (B ⋆ (TxTab ⋆ (X ⋆ E))))))))) := Mem.ac h3
  refine ⟨slot_load h (by omega), slot_load h1' (by omega), slot_load h2' (by omega),
    slot_load h3' (by omega), ?_⟩
  exact Mem.ac (slot_set h3' v4.toInt)

/-- At a call: the return slot and the callee's reservation in front. -/
theorem MF_call (Fm : Mem 64 → Prop) :
    MF k TxTab X t₀ Fm B E = 8 ?@ (t₀.regs.get64 .rsp - 0x40#64)
      ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x40#64) ⋆ (X ⋆ (Fm ⋆ (B ⋆ (TxTab ⋆ E))))) := by
  simp only [MF]; ac_rfl

end Frame

end Kraken.Examples.Sbr.Init
