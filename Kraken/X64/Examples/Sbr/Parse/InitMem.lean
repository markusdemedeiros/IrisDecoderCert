import Kraken.X64.Examples.Sbr.Parse.InitFrame

/-!
# `ff_aac_sbr_ctx_alloc_init`: the body of the memory in front

`M … B` with the body `B` (or the element) in front of the rest `Mo`, and the first stores
(`*che = p`, `sbr->ps … ` pointers).
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

/-- Everything but the body. -/
abbrev Mo (k : Nat) (TxTab X R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) :
    Mem 64 → Prop :=
  Fr t₀ ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x40#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x40#64)
    ⋆ (TxTab ⋆ (X ⋆ Rest R ra t₀))))

/-- The zero index of an address without index register. -/
theorem add0 (x : BitVec 64) : x + 0 = x := BitVec.add_zero x

section
omit [CodeEnv]
variable {k : Nat} {TxTab X R : Mem 64 → Prop} {ra : Int64} {t₀ : MachineData}

theorem M_eq (B : Mem 64 → Prop) : M k TxTab X R ra t₀ B = B ⋆ Mo k TxTab X R ra t₀ := by
  simp only [M, MF, Mo]; ac_rfl

theorem M_B2 (A B : Mem 64 → Prop) :
    M k TxTab X R ra t₀ (A ⋆ B) = A ⋆ (B ⋆ Mo k TxTab X R ra t₀) := by
  rw [M_eq]; ac_rfl

theorem M_BE0 (p : BitVec 64) (v : EV) :
    M k TxTab X R ra t₀ (BE0 t₀ p v) = ElemS p v ⋆ (c8 (arg1 t₀) p ⋆ Mo k TxTab X R ra t₀) := by
  rw [M_eq]; simp only [BE0]; ac_rfl

theorem M_BE1 (Ctx : BitVec 64 → Mem 64 → Prop) (p : BitVec 64) (v : EV) (c : BitVec 64) :
    M k TxTab X R ra t₀ (BE1 Ctx t₀ p v c)
      = ElemS p v ⋆ (c8 (arg1 t₀) p ⋆ (Ctx c ⋆ Mo k TxTab X R ra t₀)) := by
  rw [M_eq]; simp only [BE1]; ac_rfl

theorem M_BE2 (Ctx : BitVec 64 → Mem 64 → Prop) (p : BitVec 64) (v : EV) (c c' : BitVec 64) :
    M k TxTab X R ra t₀ (BE2 Ctx t₀ p v c c')
      = ElemS p v ⋆ (c8 (arg1 t₀) p ⋆ (Ctx c' ⋆ (Ctx c ⋆ Mo k TxTab X R ra t₀))) := by
  rw [M_eq]; simp only [BE2]; ac_rfl

variable {m : Mem 64}

theorem BE0_st {p : BitVec 64} {v : EV}
    (h : m =⋆ ElemS p v ⋆ (c8 (arg1 t₀) p ⋆ Mo k TxTab X R ra t₀)) :
    m =⋆ M k TxTab X R ra t₀ (BE0 t₀ p v) := by
  rw [M_BE0]; exact h

theorem BE1_st (Ctx : BitVec 64 → Mem 64 → Prop) {p c : BitVec 64} {v : EV}
    (h : m =⋆ ElemS p v ⋆ (c8 (arg1 t₀) p ⋆ (Ctx c ⋆ Mo k TxTab X R ra t₀))) :
    m =⋆ M k TxTab X R ra t₀ (BE1 Ctx t₀ p v c) := by
  rw [M_BE1]; exact h

theorem BE2_st (Ctx : BitVec 64 → Mem 64 → Prop) {p c c' : BitVec 64} {v : EV}
    (h : m =⋆ ElemS p v ⋆ (c8 (arg1 t₀) p ⋆ (Ctx c' ⋆ (Ctx c ⋆ Mo k TxTab X R ra t₀)))) :
    m =⋆ M k TxTab X R ra t₀ (BE2 Ctx t₀ p v c c') := by
  rw [M_BE2]; exact h

/-- A store of the `float scale` local. -/
theorem Mo_scale {A : Mem 64 → Prop} (h : m =⋆ A ⋆ Mo k TxTab X R ra t₀) (v : Int) :
    (m.loadInt (t₀.regs.get64 .rsp - 0x24#64) 4).isSome = true
    ∧ m.storeInt (t₀.regs.get64 .rsp - 0x24#64) 4 v =⋆ A ⋆ Mo k TxTab X R ra t₀ := by
  simp only [Mo, Fr] at h ⊢
  have h' : m =⋆ 4 ?@ (t₀.regs.get64 .rsp - 0x24#64) ⋆ (A
      ⋆ (c8 (t₀.regs.get64 .rsp - 0x8#64) (t₀.regs.get64 .rbp)
      ⋆ (c8 (t₀.regs.get64 .rsp - 0x10#64) (t₀.regs.get64 .r15)
      ⋆ (c8 (t₀.regs.get64 .rsp - 0x18#64) (t₀.regs.get64 .r14)
      ⋆ (c8 (t₀.regs.get64 .rsp - 0x20#64) (t₀.regs.get64 .rbx)
      ⋆ (12 ?@ (t₀.regs.get64 .rsp - 0x30#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x38#64)
      ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x40#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x40#64)
      ⋆ (TxTab ⋆ (X ⋆ Rest R ra t₀))))))))))) := Mem.ac h
  exact ⟨Kraken.Examples.Sbr.Parse.slot_load h' (Nat.le_refl _),
    Mem.ac (Kraken.Examples.Sbr.Parse.slot_store h' (Nat.le_refl _) v)⟩

/-- A store of the stack argument of `av_tx_init`. -/
theorem Mo_flags {A : Mem 64 → Prop} (h : m =⋆ A ⋆ Mo k TxTab X R ra t₀) (v : Int) :
    (m.loadInt (t₀.regs.get64 .rsp - 0x38#64) 8).isSome = true
    ∧ m.storeInt (t₀.regs.get64 .rsp - 0x38#64) 8 v =⋆ A ⋆ Mo k TxTab X R ra t₀ := by
  simp only [Mo, Fr] at h ⊢
  have h' : m =⋆ 8 ?@ (t₀.regs.get64 .rsp - 0x38#64) ⋆ (A
      ⋆ (c8 (t₀.regs.get64 .rsp - 0x8#64) (t₀.regs.get64 .rbp)
      ⋆ (c8 (t₀.regs.get64 .rsp - 0x10#64) (t₀.regs.get64 .r15)
      ⋆ (c8 (t₀.regs.get64 .rsp - 0x18#64) (t₀.regs.get64 .r14)
      ⋆ (c8 (t₀.regs.get64 .rsp - 0x20#64) (t₀.regs.get64 .rbx)
      ⋆ (4 ?@ (t₀.regs.get64 .rsp - 0x24#64) ⋆ (12 ?@ (t₀.regs.get64 .rsp - 0x30#64)
      ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x40#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x40#64)
      ⋆ (TxTab ⋆ (X ⋆ Rest R ra t₀))))))))))) := Mem.ac h
  exact ⟨Kraken.Examples.Sbr.Parse.slot_load h' (Nat.le_refl _),
    Mem.ac (Kraken.Examples.Sbr.Parse.slot_store h' (Nat.le_refl _) v)⟩

theorem Mo_scale2 {A B : Mem 64 → Prop} (h : m =⋆ A ⋆ (B ⋆ Mo k TxTab X R ra t₀)) (v : Int) :
    (m.loadInt (t₀.regs.get64 .rsp - 0x24#64) 4).isSome = true
    ∧ m.storeInt (t₀.regs.get64 .rsp - 0x24#64) 4 v =⋆ A ⋆ (B ⋆ Mo k TxTab X R ra t₀) := by
  rw [← Std.ExtHashMap.sep_assoc] at h ⊢; exact Mo_scale h v

theorem Mo_scale3 {A B C : Mem 64 → Prop} (h : m =⋆ A ⋆ (B ⋆ (C ⋆ Mo k TxTab X R ra t₀)))
    (v : Int) :
    (m.loadInt (t₀.regs.get64 .rsp - 0x24#64) 4).isSome = true
    ∧ m.storeInt (t₀.regs.get64 .rsp - 0x24#64) 4 v
      =⋆ A ⋆ (B ⋆ (C ⋆ Mo k TxTab X R ra t₀)) := by
  rw [← Std.ExtHashMap.sep_assoc B C] at h ⊢; exact Mo_scale2 h v

theorem Mo_flags2 {A B : Mem 64 → Prop} (h : m =⋆ A ⋆ (B ⋆ Mo k TxTab X R ra t₀)) (v : Int) :
    (m.loadInt (t₀.regs.get64 .rsp - 0x38#64) 8).isSome = true
    ∧ m.storeInt (t₀.regs.get64 .rsp - 0x38#64) 8 v =⋆ A ⋆ (B ⋆ Mo k TxTab X R ra t₀) := by
  rw [← Std.ExtHashMap.sep_assoc] at h ⊢; exact Mo_flags h v

theorem Mo_flags3 {A B C : Mem 64 → Prop} (h : m =⋆ A ⋆ (B ⋆ (C ⋆ Mo k TxTab X R ra t₀)))
    (v : Int) :
    (m.loadInt (t₀.regs.get64 .rsp - 0x38#64) 8).isSome = true
    ∧ m.storeInt (t₀.regs.get64 .rsp - 0x38#64) 8 v
      =⋆ A ⋆ (B ⋆ (C ⋆ Mo k TxTab X R ra t₀)) := by
  rw [← Std.ExtHashMap.sep_assoc B C] at h ⊢; exact Mo_flags2 h v

/-- `*che = p; sbr->ps.… = …`: the first two stores into the zeroed element. -/
theorem L2b_mem {p a : BitVec 64} (ha : a = arg1 t₀)
    (h : m =⋆ M k TxTab X R ra t₀ (8 ?@ arg1 t₀ ⋆ zs 0x88ba0 =@ p)) :
    (m.loadInt a 8).isSome = true
    ∧ ((m.storeInt a 8 p.toInt).loadInt (p + 0x9e40#64) 8).isSome = true
    ∧ (m.storeInt a 8 p.toInt).storeInt (p + 0x9e40#64) 8 (0x1e120#64 + p).toInt
      =⋆ M k TxTab X R ra t₀ (BE0 t₀ p (evA p)) := by
  subst ha
  rw [M_B2] at h
  have h1 := slot_set h p.toInt
  rw [zs_elemS] at h1
  have h2 : _ =⋆ ElemS p ev0 ⋆ ((Int.toBytes 8 p.toInt =@ arg1 t₀) ⋆ Mo k TxTab X R ra t₀) :=
    Mem.ac h1
  refine ⟨slot_load h (Nat.le_refl _), ?_, ?_⟩
  · rw [ElemS_ld_pr0 h2 rfl]; rfl
  · rw [BitVec.add_comm 0x1e120#64 p, M_BE0]; exact ElemS_st_pr0 h2 rfl _

end

end Kraken.Examples.Sbr.Init
