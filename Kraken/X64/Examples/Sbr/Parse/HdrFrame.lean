import Kraken.X64.Examples.Sbr.Parse.HdrMem

/-!
# `read_sbr_header`: the frame

The prologue's pushes, the copy of `spectrum_params` to the locals and its reads, the
epilogue's pops, and the reservation split into the frame's slots.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.Hdr

open Kraken.Examples.Sbr.HdrLib
open Kraken.Examples.Sbr.Parse (cell8_load slot_load slot_store)

variable [CodeEnv]

section Frame

variable {m : Mem 64} {u : BitVec 32} {k : Nat} {x : HArgs} {ra : Int64} {t₀ : MachineData}
  {st : HSt} {Tl : Mem 64 → Prop}

omit [CodeEnv]

/-- `push %rbp; …; push %r14; push %rbx`: the store checks and the frame after. -/
theorem M_push (h : m =⋆ MU u k x ra t₀ (FrB t₀) st Tl) (v1 v2 v3 : BitVec 64) :
    let r := t₀.regs.get64 .rsp
    (m.loadInt (r - 8#64) 8).isSome = true
    ∧ ((m.storeInt (r - 8#64) 8 v1.toInt).loadInt (r - 16#64) 8).isSome = true
    ∧ (((m.storeInt (r - 8#64) 8 v1.toInt).storeInt (r - 16#64) 8 v2.toInt).loadInt
        (r - 24#64) 8).isSome = true
    ∧ (((m.storeInt (r - 8#64) 8 v1.toInt).storeInt (r - 16#64) 8 v2.toInt).storeInt
        (r - 24#64) 8 v3.toInt
      =⋆ MU u k x ra t₀ (c8 (r - 0x8#64) v1 ⋆ (c8 (r - 0x10#64) v2
        ⋆ (c8 (r - 0x18#64) v3 ⋆ (8 ?@ (r - 0x28#64) ⋆ (2 ?@ (r - 0x1a#64) ⋆ L0 t₀))))) st Tl) := by
  intro r
  rw [M_fm, Std.ExtHashMap.sep_assoc] at h
  have h1 := slot_set h v1.toInt
  have h1' : _ =⋆ 8 ?@ (r - 0x10#64) ⋆ (Int.toBytes 8 v1.toInt =@ (r - 0x8#64) ⋆ (8 ?@ (r - 0x18#64)
      ⋆ (8 ?@ (r - 0x28#64) ⋆ (2 ?@ (r - 0x1a#64) ⋆ L0 t₀)) ⋆ Mx_fm u k x ra t₀ (FrB t₀) st Tl)) :=
    Mem.ac h1
  have h2 := slot_set h1' v2.toInt
  have h2' : _ =⋆ 8 ?@ (r - 0x18#64) ⋆ (Int.toBytes 8 v2.toInt =@ (r - 0x10#64) ⋆ (Int.toBytes 8 v1.toInt =@ (r - 0x8#64)
      ⋆ ((8 ?@ (r - 0x28#64) ⋆ (2 ?@ (r - 0x1a#64) ⋆ L0 t₀)) ⋆ Mx_fm u k x ra t₀ (FrB t₀) st Tl))) :=
    Mem.ac h2
  refine ⟨slot_load h (by omega), slot_load h1' (by omega), slot_load h2' (by omega), ?_⟩
  rw [M_fm]
  simp only [c8]
  exact Mem.ac (slot_set h2' v3.toInt)

theorem toBytes2_ofBytes (bs : List UInt8) (h : 2 ≤ bs.length) :
    Int.toBytes 2 (BitVec.ofInt 16 (Int.ofBytes bs)).toInt = bs.take 2 :=
  UInt16.toBytes_ofBytes bs h

/-- The saved registers and the unused locals, around the locals `Lc`. -/
abbrev FrX (t₀ : MachineData) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  Int.toBytes 8 (t₀.regs.get64 .rbp).toInt =@ (r - 0x8#64)
    ⋆ (Int.toBytes 8 (t₀.regs.get64 .r14).toInt =@ (r - 0x10#64)
    ⋆ (Int.toBytes 8 (t₀.regs.get64 .rbx).toInt =@ (r - 0x18#64)
    ⋆ (8 ?@ (r - 0x28#64) ⋆ 2 ?@ (r - 0x1a#64))))

theorem M_fr (Lc : Mem 64 → Prop) :
    MU u k x ra t₀ (Fr t₀ Lc) st Tl = Lc ⋆ (FrX t₀ ⋆ Mx_fm u k x ra t₀ (Fr t₀ Lc) st Tl) := by
  rw [M_fm]; simp only [Fr, FrX, c8]; ac_rfl

/-- `mov %ax, -0x14(%rbp)`. -/
theorem M_loc1 (h : m =⋆ MU u k x ra t₀ (Fr t₀ (L0 t₀)) st Tl) (v : Int) :
    let r := t₀.regs.get64 .rsp
    (m.loadInt (r - 0x1c#64) 2).isSome = true
    ∧ m.storeInt (r - 0x1c#64) 2 v
      =⋆ MU u k x ra t₀ (Fr t₀ (4 ?@ (r - 0x20#64) ⋆ Int.toBytes 2 v =@ (r - 0x1c#64))) st Tl := by
  intro r
  rw [M_fr] at h
  simp only [L0] at h
  have h' : m =⋆ 2 ?@ (r - 0x1c#64) ⋆ (4 ?@ (r - 0x20#64) ⋆ (FrX t₀
      ⋆ Mx_fm u k x ra t₀ (Fr t₀ (L0 t₀)) st Tl)) := Mem.ac h
  refine ⟨slot_load h' (by omega), ?_⟩
  rw [M_fr]
  exact Mem.ac (slot_set h' v)

/-- `mov %eax, -0x18(%rbp)`. -/
theorem M_loc2 (l : List UInt8)
    (h : m =⋆ MU u k x ra t₀ (Fr t₀ (4 ?@ (t₀.regs.get64 .rsp - 0x20#64)
      ⋆ l =@ (t₀.regs.get64 .rsp - 0x1c#64))) st Tl) (v : Int) :
    let r := t₀.regs.get64 .rsp
    (m.loadInt (r - 0x20#64) 4).isSome = true
    ∧ m.storeInt (r - 0x20#64) 4 v
      =⋆ MU u k x ra t₀ (Fr t₀ (Int.toBytes 4 v =@ (r - 0x20#64) ⋆ l =@ (r - 0x1c#64))) st Tl := by
  intro r
  rw [M_fr] at h
  rw [Std.ExtHashMap.sep_assoc] at h
  refine ⟨slot_load h (by omega), ?_⟩
  rw [M_fr, Std.ExtHashMap.sep_assoc]
  exact slot_set h v

/-- The old `spectrum_params` from the locals. -/
theorem M_ld_loc (sp : List UInt8) (hl : sp.length = 6)
    (h : m =⋆ MU u k x ra t₀ (Fr t₀ (Lsp t₀ sp)) st Tl) :
    let r := t₀.regs.get64 .rsp
    m.loadInt (r - 0x20#64) 4 = some (Int.ofBytes (sp.take 4))
    ∧ m.loadInt (r - 0x1c#64) 2 = some (Int.ofBytes (sp.drop 4)) := by
  intro r
  rw [M_fr] at h
  simp only [Lsp] at h
  have h1 := h
  rw [Std.ExtHashMap.sep_assoc] at h1
  have h2 : m =⋆ sp.drop 4 =@ (r - 0x1c#64) ⋆ (sp.take 4 =@ (r - 0x20#64) ⋆ (FrX t₀
      ⋆ Mx_fm u k x ra t₀ (Fr t₀ (Lsp t₀ sp)) st Tl)) := Mem.ac h
  have e1 := val_load0 h1 (by simp [hl])
  have e2 := val_load0 h2 (by simp [hl])
  simp only [List.length_take, List.length_drop, hl] at e1 e2
  exact ⟨e1, e2⟩

/-- The locals after the copy, as `Lsp`. -/
theorem M_lsp {sp : List UInt8} {v w : Int} (hv : Int.toBytes 2 v = sp.drop 4)
    (hw : Int.toBytes 4 w = sp.take 4)
    (h : m =⋆ MU u k x ra t₀ (Fr t₀ (Int.toBytes 4 w =@ (t₀.regs.get64 .rsp - 0x20#64)
      ⋆ Int.toBytes 2 v =@ (t₀.regs.get64 .rsp - 0x1c#64))) st Tl) :
    m =⋆ MU u k x ra t₀ (Fr t₀ (Lsp t₀ sp)) st Tl := by
  rw [hv, hw] at h; exact h

end Frame

end Kraken.Examples.Sbr.Hdr
