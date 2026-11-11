import Kraken.X64.Examples.Sbr.Parse.InitMem

/-!
# `ff_aac_sbr_ctx_alloc_init`: the memory at the calls of `av_tx_init`

`av_tx_init(&sbr->mdct, &sbr->mdct_fn, …)` is given the two cells, `*scale` (the local at
`r - 0x24`), the stack argument (at `r - 0x38`), `TxTab` and `X`; the frame `TxF` is the element
without the two cells, the rest of the body `A`, the saved registers and the caller's part.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr
open Kraken.Examples.Sbr.Apply (c8)
open Kraken.Examples.Sbr.Session (zs)

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.Init

variable [CodeEnv]

/-- The saved registers and the unused locals. -/
abbrev FrT (t₀ : MachineData) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14) ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .rbx)
    ⋆ 12 ?@ (r - 0x30#64))))

/-- The frame of a call: the element without the callee's cells `H`, the body's rest `A`. -/
abbrev TxF (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) (H A : Mem 64 → Prop) :
    Mem 64 → Prop :=
  H ⋆ (A ⋆ (FrT t₀ ⋆ Rest R ra t₀))

section
omit [CodeEnv]
variable {k : Nat} {TxTab X R : Mem 64 → Prop} {ra : Int64} {t₀ : MachineData} {m : Mem 64}

/-- The pieces at a call of `av_tx_init`: the return slot, the reservation, the callee's part
(the cells `a0`, `a1`, `TxI`), the frame. -/
theorem tx_pre {A H : Mem 64 → Prop} {a0 a1 : BitVec 64}
    (h : m =⋆ 8 ?@ a0 ⋆ (8 ?@ a1 ⋆ (H ⋆ (A ⋆ Mo k TxTab X R ra t₀)))) :
    m =⋆ 8 ?@ (t₀.regs.get64 .rsp - 0x40#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x40#64)
      ⋆ ((8 ?@ a0 ⋆ (8 ?@ a1 ⋆ (4 ?@ (t₀.regs.get64 .rsp - 0x24#64)
        ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x38#64) ⋆ (TxTab ⋆ X)))))
      ⋆ TxF R ra t₀ H A)) := by
  simp only [Mo, Fr, TxF, FrT] at h ⊢
  exact Mem.ac h

/-- … and back, with the callee's cells `Q`. -/
theorem tx_post {A H Q : Mem 64 → Prop}
    (h : m =⋆ 8 ?@ (t₀.regs.get64 .rsp - 0x40#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x40#64)
      ⋆ ((Q ⋆ (4 ?@ (t₀.regs.get64 .rsp - 0x24#64)
        ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x38#64) ⋆ (TxTab ⋆ X))))
      ⋆ TxF R ra t₀ H A))) :
    m =⋆ Q ⋆ (H ⋆ (A ⋆ Mo k TxTab X R ra t₀)) := by
  simp only [Mo, Fr, TxF, FrT] at h ⊢
  exact Mem.ac h

/-- A successful `av_tx_init(&sbr->mdct, &sbr->mdct_fn, …)`: the cells back into the element, the
context `c` owned. -/
theorem tx_ok_syn {A : Mem 64 → Prop} {Ctx : BitVec 64 → Mem 64 → Prop} {p c : BitVec 64}
    {f : Int64} {v : EV}
    (h : m =⋆ (c8 (p + 0x88af0#64) c ⋆ (FnCell (p + 0x88af8#64) f ⋆ Ctx c))
      ⋆ (ElemH_syn p v ⋆ (A ⋆ Mo k TxTab X R ra t₀))) :
    m =⋆ ElemS p { v with synC := Int.toBytes 8 c.toInt, synF := fb f }
      ⋆ (A ⋆ (Ctx c ⋆ Mo k TxTab X R ra t₀)) := by
  simp only [c8, FnCell] at h
  exact ElemS_in_syn (Mem.ac h)

/-- A successful `av_tx_init(&sbr->mdct_ana, &sbr->mdct_ana_fn, …)`. -/
theorem tx_ok_ana {A : Mem 64 → Prop} {Ctx : BitVec 64 → Mem 64 → Prop} {p c : BitVec 64}
    {f : Int64} {v : EV}
    (h : m =⋆ (c8 (p + 0x88ae0#64) c ⋆ (FnCell (p + 0x88ae8#64) f ⋆ Ctx c))
      ⋆ (ElemH_ana p v ⋆ (A ⋆ Mo k TxTab X R ra t₀))) :
    m =⋆ ElemS p { v with anaC := Int.toBytes 8 c.toInt, anaF := fb f }
      ⋆ (A ⋆ (Ctx c ⋆ Mo k TxTab X R ra t₀)) := by
  simp only [c8, FnCell] at h
  exact ElemS_in_ana (Mem.ac h)

theorem be2_of {E A C C' : Mem 64 → Prop} (h : m =⋆ E ⋆ ((A ⋆ C) ⋆ (C' ⋆ Mo k TxTab X R ra t₀))) :
    m =⋆ E ⋆ (A ⋆ (C' ⋆ (C ⋆ Mo k TxTab X R ra t₀))) := Mem.ac h

/-- A failed call: the body `A` and the rest `J`. -/
theorem tx_fail {A H Q : Mem 64 → Prop} (h : m =⋆ Q ⋆ (H ⋆ (A ⋆ Mo k TxTab X R ra t₀))) :
    m =⋆ M k TxTab X R ra t₀ (A ⋆ (Q ⋆ H)) := by
  rw [M_eq]; exact Mem.ac h

/-- A failed `av_tx_init(&sbr->mdct, …)`: the element with any bytes in the two cells. -/
theorem tx_fail_syn {A : Mem 64 → Prop} {p : BitVec 64} {v : EV}
    (h : m =⋆ (8 ?@ (p + 0x88af0#64) ⋆ 8 ?@ (p + 0x88af8#64))
      ⋆ (ElemH_syn p v ⋆ (A ⋆ Mo k TxTab X R ra t₀))) :
    ∃ bc bf : List UInt8, bc.length = 8 ∧ bf.length = 8
      ∧ (m =⋆ M k TxTab X R ra t₀ (A ⋆ ElemS p { v with synC := bc, synF := bf })) := by
  rw [Std.ExtHashMap.sep_assoc] at h
  obtain ⟨-, bc, hc, h1⟩ := Block.sep_elim h
  rw [Std.ExtHashMap.sep_comm_l] at h1
  obtain ⟨-, bf, hf, h2⟩ := Block.sep_elim h1
  rw [Std.ExtHashMap.sep_comm_l] at h2
  refine ⟨bc, bf, hc, hf, ?_⟩
  rw [M_eq]; exact Mem.ac (ElemS_in_syn h2)

theorem M_swap {A C E : Mem 64 → Prop} (h : m =⋆ M k TxTab X R ra t₀ ((A ⋆ C) ⋆ E)) :
    m =⋆ M k TxTab X R ra t₀ (A ⋆ (E ⋆ C)) := by
  rw [M_eq] at h ⊢; exact Mem.ac h

/-- A failed `av_tx_init(&sbr->mdct_ana, …)`. -/
theorem tx_fail_ana {A : Mem 64 → Prop} {p : BitVec 64} {v : EV}
    (h : m =⋆ (8 ?@ (p + 0x88ae0#64) ⋆ 8 ?@ (p + 0x88ae8#64))
      ⋆ (ElemH_ana p v ⋆ (A ⋆ Mo k TxTab X R ra t₀))) :
    ∃ bc bf : List UInt8, bc.length = 8 ∧ bf.length = 8
      ∧ (m =⋆ M k TxTab X R ra t₀ (A ⋆ ElemS p { v with anaC := bc, anaF := bf })) := by
  rw [Std.ExtHashMap.sep_assoc] at h
  obtain ⟨-, bc, hc, h1⟩ := Block.sep_elim h
  rw [Std.ExtHashMap.sep_comm_l] at h1
  obtain ⟨-, bf, hf, h2⟩ := Block.sep_elim h1
  rw [Std.ExtHashMap.sep_comm_l] at h2
  refine ⟨bc, bf, hc, hf, ?_⟩
  rw [M_eq]; exact Mem.ac (ElemS_in_ana h2)

end

/-- The frame of `ff_psdsp_init` / `ff_sbrdsp_init`. -/
abbrev DF (TxTab R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) (H B1 B2 B3 : Mem 64 → Prop) :
    Mem 64 → Prop :=
  H ⋆ (B1 ⋆ (B2 ⋆ (B3 ⋆ (Fr t₀ ⋆ (TxTab ⋆ Rest R ra t₀)))))

section
omit [CodeEnv]
variable {k : Nat} {TxTab X R : Mem 64 → Prop} {ra : Int64} {t₀ : MachineData} {m : Mem 64}

theorem dsp_pre {H B1 B2 B3 : Mem 64 → Prop} {n : Nat} {a : BitVec 64}
    (h : m =⋆ n ?@ a ⋆ (H ⋆ (B1 ⋆ (B2 ⋆ (B3 ⋆ Mo k TxTab X R ra t₀))))) :
    m =⋆ 8 ?@ (t₀.regs.get64 .rsp - 0x40#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x40#64)
      ⋆ ((n ?@ a ⋆ X) ⋆ DF TxTab R ra t₀ H B1 B2 B3)) := by
  simp only [Mo, DF] at h ⊢
  exact Mem.ac h

theorem dsp_post {H B1 B2 B3 : Mem 64 → Prop} {n : Nat} {a : BitVec 64}
    (h : m =⋆ 8 ?@ (t₀.regs.get64 .rsp - 0x40#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x40#64)
      ⋆ ((n ?@ a ⋆ X) ⋆ DF TxTab R ra t₀ H B1 B2 B3))) :
    m =⋆ n ?@ a ⋆ (H ⋆ (B1 ⋆ (B2 ⋆ (B3 ⋆ Mo k TxTab X R ra t₀)))) := by
  simp only [Mo, DF] at h ⊢
  exact Mem.ac h

end

end Kraken.Examples.Sbr.Init
