import Kraken.X64.Examples.Sbr.Parse.InitMem

/-!
# `ff_aac_sbr_ctx_alloc_init`: the epilogue

The pops read the saved registers back; the frame's contents are then forgotten (`FrB`), and
`ret` takes the return address off.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr
open Kraken.Examples.Sbr.Apply (c8)

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.Init

section
variable [CodeEnv] {k : Nat} {Ctx : BitVec 64 → Mem 64 → Prop} {TxTab : Mem 64 → Prop}
  {t₀ : MachineData}
  {Mk Mk' : (Mem 64 → Prop) → Mem 64 → Prop} {ret : BitVec 32} {m : Mem 64}

/-- `Out` along a change of the memory around the body. -/
theorem Out_mono (hk : ∀ B, (m =⋆ Mk B) → (m =⋆ Mk' B)) (h : Out k Ctx TxTab t₀ Mk ret m) :
    Out k Ctx TxTab t₀ Mk' ret m := by
  rcases h with ⟨h1, r, h2, h4, ha, hs, h3⟩ | ⟨h1, h2⟩ | ⟨h1, p, bc, bf, l1, l2, h2⟩
    | ⟨h1, p, c, f, bc, bf, l1, l2, h2⟩
  · exact Or.inl ⟨h1, r, h2, h4, ha, hs, hk _ h3⟩
  · exact Or.inr (Or.inl ⟨h1, hk _ h2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h1, p, bc, bf, l1, l2, hk _ h2⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h1, p, c, f, bc, bf, l1, l2, hk _ h2⟩))

/-- Every outcome has some body. -/
theorem Out_ex (h : Out k Ctx TxTab t₀ Mk ret m) : ∃ B, m =⋆ Mk B := by
  rcases h with ⟨-, r, -, -, -, -, h⟩ | ⟨-, h⟩ | ⟨-, p, bc, bf, -, -, h⟩
    | ⟨-, p, c, f, bc, bf, -, -, h⟩
  · exact ⟨_, h⟩
  · exact ⟨_, h⟩
  · exact ⟨_, h⟩
  · exact ⟨_, h⟩

end

section
variable {k : Nat} {TxTab X R : Mem 64 → Prop} {ra : Int64} {t₀ : MachineData} {m : Mem 64}
  {B : Mem 64 → Prop}

/-- The pops: the saved registers. -/
theorem M_pop (h : m =⋆ M k TxTab X R ra t₀ B) :
    let r := t₀.regs.get64 .rsp
    m.loadInt (r - 0x20#64) 8 = some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 .rbx).toInt))
    ∧ m.loadInt (r - 0x18#64) 8 = some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 .r14).toInt))
    ∧ m.loadInt (r - 0x10#64) 8 = some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 .r15).toInt))
    ∧ m.loadInt (r - 0x8#64) 8
      = some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 .rbp).toInt)) := by
  intro r
  rw [M_eq] at h
  simp only [Mo, Fr, c8] at h
  generalize 8 ?@ (r - 0x40#64) ⋆ (Reserve k (r - 0x40#64) ⋆ (TxTab ⋆ (X ⋆ Rest R ra t₀)))
    = G at h
  generalize 4 ?@ (r - 0x24#64) ⋆ (12 ?@ (r - 0x30#64) ⋆ 8 ?@ (r - 0x38#64)) = L at h
  have k1 := Int.toBytes_length 8 (t₀.regs.get64 .rbx).toInt
  have k2 := Int.toBytes_length 8 (t₀.regs.get64 .r14).toInt
  have k3 := Int.toBytes_length 8 (t₀.regs.get64 .r15).toInt
  have k4 := Int.toBytes_length 8 (t₀.regs.get64 .rbp).toInt
  generalize Int.toBytes 8 (t₀.regs.get64 .rbx).toInt = l1 at h k1 ⊢
  generalize Int.toBytes 8 (t₀.regs.get64 .r14).toInt = l2 at h k2 ⊢
  generalize Int.toBytes 8 (t₀.regs.get64 .r15).toInt = l3 at h k3 ⊢
  generalize Int.toBytes 8 (t₀.regs.get64 .rbp).toInt = l4 at h k4 ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h' : m =⋆ l1 =@ (r - 0x20#64) ⋆ (B ⋆ l2 =@ (r - 0x18#64) ⋆ l3 =@ (r - 0x10#64)
        ⋆ l4 =@ (r - 0x8#64) ⋆ L ⋆ G) := Mem.ac h
    have e := loadInt_sep _ _ _ _ m h' rfl (by omega); rw [k1] at e; exact e
  · have h' : m =⋆ l2 =@ (r - 0x18#64) ⋆ (B ⋆ l1 =@ (r - 0x20#64) ⋆ l3 =@ (r - 0x10#64)
        ⋆ l4 =@ (r - 0x8#64) ⋆ L ⋆ G) := Mem.ac h
    have e := loadInt_sep _ _ _ _ m h' rfl (by omega); rw [k2] at e; exact e
  · have h' : m =⋆ l3 =@ (r - 0x10#64) ⋆ (B ⋆ l1 =@ (r - 0x20#64) ⋆ l2 =@ (r - 0x18#64)
        ⋆ l4 =@ (r - 0x8#64) ⋆ L ⋆ G) := Mem.ac h
    have e := loadInt_sep _ _ _ _ m h' rfl (by omega); rw [k3] at e; exact e
  · have h' : m =⋆ l4 =@ (r - 0x8#64) ⋆ (B ⋆ l1 =@ (r - 0x20#64) ⋆ l2 =@ (r - 0x18#64)
        ⋆ l3 =@ (r - 0x10#64) ⋆ L ⋆ G) := Mem.ac h
    have e := loadInt_sep _ _ _ _ m h' rfl (by omega); rw [k4] at e; exact e

theorem fg {bs : List UInt8} {a : BitVec 64} {n : Nat} {F : Mem 64 → Prop}
    (hl : bs.length = n) (hn : n ≤ 8) (h : m =⋆ (bs =@ a) ⋆ F) : m =⋆ (n ?@ a) ⋆ F :=
  Block.sep_intro hl (by omega) h

/-- The frame's contents forgotten. -/
theorem M_forget (h : m =⋆ M k TxTab X R ra t₀ B) :
    m =⋆ MF k TxTab X t₀ (FrB t₀) B (Rest R ra t₀) := by
  simp only [M, MF, Fr, FrB, c8] at h ⊢
  generalize 4 ?@ (t₀.regs.get64 .rsp - 0x24#64) ⋆ (12 ?@ (t₀.regs.get64 .rsp - 0x30#64)
    ⋆ 8 ?@ (t₀.regs.get64 .rsp - 0x38#64)) = L at h ⊢
  generalize 8 ?@ (t₀.regs.get64 .rsp - 0x40#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x40#64)
    ⋆ (B ⋆ (TxTab ⋆ (X ⋆ Rest R ra t₀)))) = G at h ⊢
  generalize t₀.regs.get64 .rsp = r at h ⊢
  have k1 := Int.toBytes_length 8 (t₀.regs.get64 .rbp).toInt
  have k2 := Int.toBytes_length 8 (t₀.regs.get64 .r15).toInt
  have k3 := Int.toBytes_length 8 (t₀.regs.get64 .r14).toInt
  have k4 := Int.toBytes_length 8 (t₀.regs.get64 .rbx).toInt
  generalize Int.toBytes 8 (t₀.regs.get64 .rbp).toInt = l1 at h k1
  generalize Int.toBytes 8 (t₀.regs.get64 .r15).toInt = l2 at h k2
  generalize Int.toBytes 8 (t₀.regs.get64 .r14).toInt = l3 at h k3
  generalize Int.toBytes 8 (t₀.regs.get64 .rbx).toInt = l4 at h k4
  have s1 := fg k1 (Nat.le_refl _) (Mem.ac h : m =⋆ l1 =@ (r - 0x8#64)
    ⋆ (l2 =@ (r - 0x10#64) ⋆ l3 =@ (r - 0x18#64) ⋆ l4 =@ (r - 0x20#64) ⋆ L ⋆ G))
  have s2 := fg k2 (Nat.le_refl _) (Mem.ac s1 : m =⋆ l2 =@ (r - 0x10#64)
    ⋆ (8 ?@ (r - 0x8#64) ⋆ l3 =@ (r - 0x18#64) ⋆ l4 =@ (r - 0x20#64) ⋆ L ⋆ G))
  have s3 := fg k3 (Nat.le_refl _) (Mem.ac s2 : m =⋆ l3 =@ (r - 0x18#64)
    ⋆ (8 ?@ (r - 0x10#64) ⋆ 8 ?@ (r - 0x8#64) ⋆ l4 =@ (r - 0x20#64) ⋆ L ⋆ G))
  have s4 := fg k4 (Nat.le_refl _) (Mem.ac s3 : m =⋆ l4 =@ (r - 0x20#64)
    ⋆ (8 ?@ (r - 0x18#64) ⋆ 8 ?@ (r - 0x10#64) ⋆ 8 ?@ (r - 0x8#64) ⋆ L ⋆ G))
  exact Mem.ac s4

/-- The return address at the top. -/
theorem MF_ret {Fm : Mem 64 → Prop} :
    MF k TxTab X t₀ Fm B (Rest R ra t₀)
      = RetCell ra (t₀.regs.get64 .rsp) ⋆ MF k TxTab X t₀ Fm B R := by
  simp only [MF, Rest]; ac_rfl

end

end Kraken.Examples.Sbr.Init
