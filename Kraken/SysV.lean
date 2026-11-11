import Kraken.Step
import Kraken.SepCells

/-!
# Procedures under the SysV x86-64 calling convention

What a procedure specification (`ProcSpec`, `ProcSpecK` in `Kraken.Step`) says
about the stack and the registers when the code follows the SysV convention,
stated once for every procedure:

* `RetCell ra a`: the return address `ra` at `a` (`[rsp]` on entry);
* `Reserve d r`: `d` bytes of free stack below `r`, the procedure's *stack
  reservation* (Bedrock's `reserving` clause): the caller supplies it, the
  procedure may use it, and it comes back as owned bytes. The amount is a
  parameter; a recursive procedure exports it as a function of its argument
  (`need` in the `EvenOdd*` examples). It is exact, not "at least": a caller
  with more stack frames the excess off with `Reserve.excess`, so that the
  reservation is one cell the rules of `SepCells` move around whole;
* `SavedRegs t s`: the callee-saved registers other than `rbp` as they were;
* `CallPre d R ra t`, `CallPost d R ra t s`: the convention's share of a
  procedure's pre- and postcondition with caller's memory `R`; a procedure's
  specification is these plus its semantics (`ArgU32`, `RetU8` for the
  register conventions of `unsigned`/`bool`, and whatever it computes).

Kraken has no faulting model, so stack exhaustion cannot be a runtime error;
the reservation in the precondition is the only sound treatment. A tail call
is a run that reaches `ra` through the callee, so it is covered by the
callee's spec at the same `ra` and needs nothing here; a convention that
hands over `ra` or the frame differently (a segmented stack, a link register)
would replace `RetCell`/`Reserve` by its own cells and keep the rest.
-/

open Mem
open Std.ExtHashMap

namespace Kraken.SysV

/-- The bytes a return address occupies: the slot at `a` holds `ra`, as the
`call` wrote it. -/
abbrev RetCell (ra : Int64) (a : BitVec 64) : Mem 64 → Prop :=
  Int.toBytes 8 ra.toBitVec.toInt =@ a

/-- `d` bytes of free stack just below `r`, not wrapping past address `0`: a procedure's stack
reservation. A `def`, so that `grind` moves it as one cell (`Split.at_head`). -/
def Reserve (d : Nat) (r : BitVec 64) : Mem 64 → Prop :=
  fun m => d ≤ r.toNat ∧ (d ?@ (r - .ofNat 64 d)) m

/-- A pure fact on the right of a separating conjunction. -/
theorem sep_pure_r {P Q : Mem 64 → Prop} {φ : Prop} :
    (P ⋆ fun m => φ ∧ Q m) = fun m => φ ∧ (P ⋆ Q) m := by
  funext m; apply propext; constructor
  · rintro ⟨a, b, h1, h2, ha, hφ, hb⟩; exact ⟨hφ, a, b, h1, h2, ha, hb⟩
  · rintro ⟨hφ, a, b, h1, h2, ha, hb⟩; exact ⟨a, b, h1, h2, ha, hφ, hb⟩

/-- A pure fact on the left of a separating conjunction. -/
theorem sep_pure_l {P Q : Mem 64 → Prop} {φ : Prop} :
    ((fun m => φ ∧ P m) ⋆ Q) = fun m => φ ∧ (P ⋆ Q) m := by
  rw [sep_comm, sep_pure_r, sep_comm]

/-- A reservation is its block once the bound is known. -/
theorem Reserve_eq (d : Nat) (r : BitVec 64) (h : d ≤ r.toNat) :
    Reserve d r = d ?@ (r - .ofNat 64 d) := by
  funext m; exact propext ⟨fun h' => h'.2, fun h' => ⟨h, h'⟩⟩

/-- The bound a reservation states. -/
theorem Reserve.le {d : Nat} {r : BitVec 64} {m : Mem 64} (h : Reserve d r m) : d ≤ r.toNat :=
  h.1

/-- The bound of a reservation at the head of a tree. -/
theorem Reserve.le_head {d : Nat} {r : BitVec 64} {K : Mem 64 → Prop} {m : Mem 64}
    (h : m =⋆ Reserve d r ⋆ K) : d ≤ r.toNat := by
  obtain ⟨_, _, _, _, h1, _⟩ := h; exact h1.1

/-- The block form of `Reserve_split` (the reservation before the bound). -/
theorem block_split_top (a d : Nat) (r : BitVec 64) (h : a + d ≤ 2 ^ 64) :
    ((a + d) ?@ (r - .ofNat 64 (a + d)) : Mem 64 → Prop)
      = a ?@ (r - .ofNat 64 a) ⋆ d ?@ (r - .ofNat 64 a - .ofNat 64 d) := by
  rw [Block.split_at (r - BitVec.ofNat 64 (a + d)) (a + d) d (by omega) h, sep_comm]
  have e1 : r - BitVec.ofNat 64 (a + d) + BitVec.ofNat 64 d = r - BitVec.ofNat 64 a := by
    bv_omega
  have e2 : r - BitVec.ofNat 64 a - BitVec.ofNat 64 d = r - BitVec.ofNat 64 (a + d) := by
    bv_omega
  rw [e1, e2, Nat.add_sub_cancel]

/-- The reservation, with `a` bytes carved off its top: the rest is a smaller
reservation `a` bytes lower. The one lemma the stack discipline needs, at a
procedure's entry (its own bytes off the top), at a call (the return address
slot off what is left), and in reverse at its exit. The carved bytes do not
carry the bound, hence `h` (at an entry it follows from the reservation,
`Reserve.le_head`; elsewhere from the entry's). -/
theorem Reserve_split (a d : Nat) (r : BitVec 64) (h : a ≤ r.toNat) :
    Reserve (a + d) r = a ?@ (r - .ofNat 64 a) ⋆ Reserve d (r - .ofNat 64 a) := by
  have hr : (r - BitVec.ofNat 64 a).toNat = r.toNat - a := by
    rw [BitVec.toNat_sub_of_le (by simp [BitVec.le_def]; omega)]
    simp; omega
  unfold Reserve
  rw [sep_pure_r, hr]
  funext m; apply propext; constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by omega, by rw [← block_split_top a d r (by have := r.isLt; omega)]; exact h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨by omega, ?_⟩
    rw [block_split_top a d r (by have := r.isLt; omega)]; exact h2

/-- `Reserve_split` from left to right needs no side condition. -/
theorem Reserve_split_mp {a d : Nat} {r : BitVec 64} {K : Mem 64 → Prop} {m : Mem 64}
    (hm : m =⋆ Reserve (a + d) r ⋆ K) :
    m =⋆ a ?@ (r - .ofNat 64 a) ⋆ Reserve d (r - .ofNat 64 a) ⋆ K := by
  have h := Reserve.le_head hm
  rw [Reserve_split a d r (by omega)] at hm; exact hm

/-- A caller with `d'` bytes where `d` are needed: the excess sits below. -/
theorem Reserve.excess (d d' : Nat) (r : BitVec 64) (h : d ≤ d') (hw : d' ≤ r.toNat) :
    Reserve d' r = Reserve d r ⋆ (d' - d) ?@ (r - .ofNat 64 d') := by
  rw [Reserve_eq d' r hw, Reserve_eq d r (by omega)]
  have := block_split_top d (d' - d) r (by have := r.isLt; omega)
  rw [Nat.add_sub_cancel' h] at this
  rw [this]
  have e : r - BitVec.ofNat 64 d - BitVec.ofNat 64 (d' - d) = r - BitVec.ofNat 64 d' := by
    bv_omega
  rw [e]

/-- The callee-saved registers other than `rbp` (which a frame-pointer
prologue moves and the epilogue restores) hold their entry values. -/
abbrev SavedRegs (t s : MachineData) : Prop :=
  s.regs.get64 .rbx = t.regs.get64 .rbx
  ∧ s.regs.get64 .r12 = t.regs.get64 .r12 ∧ s.regs.get64 .r13 = t.regs.get64 .r13
  ∧ s.regs.get64 .r14 = t.regs.get64 .r14 ∧ s.regs.get64 .r15 = t.regs.get64 .r15

/-- The convention's share of a procedure's precondition, with caller's memory
`R`: the return address on the stack, and `d` bytes reserved below it. -/
abbrev CallPre (d : Nat) (R : Mem 64 → Prop) (ra : Int64) (t : MachineData) : Prop :=
  t.dmem =⋆ RetCell ra (t.regs.get64 .rsp) ⋆ (Reserve d (t.regs.get64 .rsp) ⋆ R)

/-- The convention's share of a procedure's postcondition: the return address
popped, `rbp` and the callee-saved registers as they were, the reservation and
the slot given back. -/
abbrev CallPost (d : Nat) (R : Mem 64 → Prop) (_ra : Int64) (t s : MachineData) : Prop :=
  s.regs.get64 .rsp = t.regs.get64 .rsp + 8
  ∧ s.regs.get64 .rbp = t.regs.get64 .rbp ∧ SavedRegs t s
  ∧ (s.dmem =⋆ 8 ?@ (t.regs.get64 .rsp) ⋆ (Reserve d (t.regs.get64 .rsp) ⋆ R))

/-- The bound of the reservation at a call. -/
theorem CallPre.le {d : Nat} {R : Mem 64 → Prop} {ra : Int64} {t : MachineData}
    (h : CallPre d R ra t) : d ≤ (t.regs.get64 .rsp).toNat := by
  obtain ⟨_, _, _, _, _, _, _, _, _, h1, _⟩ := h; exact h1.1

/-- An `unsigned` argument: the low 32 bits of `rdi`. -/
abbrev ArgU32 (t : MachineData) (n : Nat) : Prop := (t.regs.get64 .rdi).toNat % 2 ^ 32 = n

theorem ArgU32.lt {t : MachineData} {n : Nat} (h : ArgU32 t n) : n < 2 ^ 32 :=
  h ▸ Nat.mod_lt _ (by decide)

/-- A `bool`/byte result in `al` — all 8 bits of it. -/
abbrev RetU8 (s : MachineData) (v : Nat) : Prop := (s.regs.get64 .rax).toNat % 256 = v

end Kraken.SysV
