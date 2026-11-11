import Kraken.X64.Parser
import Kraken.MachineWP
import Kraken.X64.Examples.EvenOddExistential.Spec

/-!
# `odd`, existential style, proved against `even` below `N`

`odd_specK`: from `EvenSpecK N` (the spec of `even` for arguments below `N`,
one proposition, an assumption here; `Link.lean` discharges it), `odd` meets
`OddSpecK (N + 1)`. The mirror image of `Even.lean`; the notes there apply.
See `Spec.lean` for the form of the specification and
`EvenOddGhost/Spec.lean` for the conditions in it.

## How this differs from the ghost proof

`ProcSpecK.of_cfg_exists` (`MachineWP`) takes the witness `(n, R)` of the
specification as a logical variable, so the table and the block obligations
are those of `EvenOddGhost/Odd.lean`, with the bound `n < N + 1` in hand.
The one place the style shows is the call: the callee's spec is existential,
so the call site *produces* the witnesses — `even`'s argument `k` and the
memory it is to leave alone (our cells) — where the ghost proof passes the
memory to `call_proc_spec_at`. The steps around the call are the same
(`call_simp`, the `refine` for the rule's shape, `vcgen` for the tail,
`grind_cells`).
-/

open Kraken.X64.Parser
open Kraken
open Kraken.SysV
open Std.WP
open Mem
open MachineWP

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.EvenOddExistential.Odd

open EvenOddGhost

/-- `odd`, as clang `-O0` emits it: the text of `even` with the base case
returning `0` and the call going to `even` (AT&T syntax; labels renamed for
the parser; the `ret` is kept — Kraken's `ret_spec` reads the address at
`[rsp]`). -/
def odd_body : Program := parse("
odd:
  pushq %rbp
  movq %rsp, %rbp
  subq $16, %rsp
  movl %edi, -8(%rbp)
  cmpl $0, -8(%rbp)
  jne .LBB1_2
  movb $0, -1(%rbp)
  jmp .LBB1_3
.LBB1_2:
  movl -8(%rbp), %edi
  subl $1, %edi
  call even
  andb $1, %al
  movb %al, -1(%rbp)
.LBB1_3:
  movb -1(%rbp), %al
  andb $1, %al
  addq $16, %rsp
  popq %rbp
  ret
")

/-! ## The frame

The stack layout of this body, as clang `-O0` laid it out: nothing here is
shared with any other procedure (that `even` happens to have the same frame is
a coincidence of two identical prologues). -/

/-- What is reserved below a procedure's own 24 bytes: `need n - 24`. -/
def below (n : Nat) : Nat := 32 * n

theorem need_eq (n : Nat) : need n = 24 + below n := rfl

/-- The reservation below the own bytes, at `n + 1`: the slot the call pushes
into, then the callee's reservation (`hr`: the slot is below `r`). The call
block opens it this way (an equation in `grind`'s context). -/
theorem Reserve_below_succ (k : Nat) (r : BitVec 64) (hr : 8 ≤ r.toNat) :
    Reserve (below (k + 1)) r = 8 ?@ (r - 8) ⋆ Reserve (need k) (r - 8) := by
  have e : below (k + 1) = 8 + need k := by unfold below need; omega
  rw [e, Reserve_split 8 (need k) r hr]
  rfl

/-- The procedure's own 24 bytes as the cells its code uses, in front of `X`:
the unused 8, the spilled argument, padding, the `bool` local, the saved
`rbp`. -/
abbrev OwnCells (r : BitVec 64) (X : Mem 64 → Prop) : Mem 64 → Prop :=
  8 ?@ (r - 24) ⋆ (4 ?@ (r - 16) ⋆ (3 ?@ (r - 12) ⋆ (1 ?@ (r - 9) ⋆ (8 ?@ (r - 8) ⋆ X))))

theorem own_cells (r : BitVec 64) (X : Mem 64 → Prop) :
    24 ?@ (r - 24) ⋆ X = OwnCells r X := by
  have h24 : (24 : Nat) = 8 + (4 + (3 + (1 + 8))) := rfl
  have e1 : r - 24 + BitVec.ofNat 64 8 = r - 16 := by bv_omega
  have e2 : r - 16 + BitVec.ofNat 64 4 = r - 12 := by bv_omega
  have e3 : r - 12 + BitVec.ofNat 64 3 = r - 9 := by bv_omega
  have e4 : r - 9 + BitVec.ofNat 64 1 = r - 8 := by bv_omega
  rw [h24, Block.split _ 8 _ (by decide), e1, Block.split _ 4 _ (by decide), e2,
    Block.split _ 3 _ (by decide), e3, Block.split _ 1 _ (by decide), e4]
  simp only [Std.ExtHashMap.sep_assoc]

/-- The reservation in front of `X` is the cells the code uses in front of
the reservation below them. Used at a procedure's entry (`hpre`) and exit
(`hpost`) so that inside the blocks every tree names the same cells at the
same address terms (see the note on addresses in `SepCells`). Not a `grind`
rewrite: the blocks pass the callee's reservation around whole. -/
theorem Reserve_cells (n : Nat) (r : BitVec 64) (X : Mem 64 → Prop)
    (hn : 24 ≤ r.toNat) :
    Reserve (need n) r ⋆ X = 8 ?@ (r - 24) ⋆ (4 ?@ (r - 16) ⋆ (3 ?@ (r - 12)
      ⋆ (1 ?@ (r - 9) ⋆ (8 ?@ (r - 8) ⋆ (Reserve (below n) (r - 24) ⋆ X))))) := by
  rw [need_eq]
  have e : BitVec.ofNat 64 24 = (24 : BitVec 64) := rfl
  rw [Reserve_split 24 (below n) r hn, e, Std.ExtHashMap.sep_assoc, own_cells]

/-- The frame after the prologue, read off the body with `r` the entry `rsp`
and `rbp = r - 8`: the saved `rbp` at `(%rbp)`, the `bool` local at
`-1(%rbp)`, 3 bytes of padding, the spilled argument at `-8(%rbp)`, 8 unused
bytes at `-16(%rbp)`, and the return address at `r`. `L` is the local's cell,
given its address (`(1 ?@ ·)` before the store, the result after); `X` is what
sits below the frame. -/
abbrev Frame (t₀ : MachineData) (ra : Int64) (L : BitVec 64 → Mem 64 → Prop)
    (X : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  L (r - 9) ⋆ (Int.toBytes 8 (t₀.regs.get64 .rbp).toInt =@ (r - 8) ⋆ (3 ?@ (r - 12)
    ⋆ (Int.toBytes 4 ((t₀.regs.get64 .rdi).setWidth 32).toInt =@ (r - 16)
    ⋆ (8 ?@ (r - 24) ⋆ (RetCell ra r ⋆ X)))))

/-- `CallPre`'s memory as the entry block reads it. -/
theorem CallPre.cells {n : Nat} {R : Mem 64 → Prop} {ra : Int64} {t : MachineData}
    (h : CallPre (need n) R ra t) :
    t.dmem =⋆ RetCell ra (t.regs.get64 .rsp)
      ⋆ OwnCells (t.regs.get64 .rsp) (Reserve (below n) (t.regs.get64 .rsp - 24) ⋆ R) := by
  have hmem : t.dmem =⋆ RetCell ra (t.regs.get64 .rsp)
      ⋆ (Reserve (need n) (t.regs.get64 .rsp) ⋆ R) := h
  rw [Reserve_cells _ _ _ (by have := CallPre.le h; unfold need at this; omega)] at hmem
  exact hmem

/-- `CallPost` as the exit block leaves it: the own bytes as the cells the code
used, the rest of the reservation below them. The blocks establish this;
`CallPost.of_cells` folds it (`hpost` of `ProcSpec.of_cfg_post_pre`, with the entry's
headroom `hr`). -/
abbrev CallPostCells (n : Nat) (R : Mem 64 → Prop) (_ra : Int64) (t s : MachineData) : Prop :=
  s.regs.get64 .rsp = t.regs.get64 .rsp + 8
  ∧ s.regs.get64 .rbp = t.regs.get64 .rbp ∧ SavedRegs t s
  ∧ (s.dmem =⋆ 8 ?@ (t.regs.get64 .rsp)
      ⋆ OwnCells (t.regs.get64 .rsp) (Reserve (below n) (t.regs.get64 .rsp - 24) ⋆ R))

theorem CallPost.of_cells {n : Nat} {R : Mem 64 → Prop} {ra : Int64} {t s : MachineData}
    (hr : 24 ≤ (t.regs.get64 .rsp).toNat) (h : CallPostCells n R ra t s) :
    CallPost (need n) R ra t s := by
  obtain ⟨h₁, h₂, h₃, hmem⟩ := h
  exact ⟨h₁, h₂, h₃, by rw [Reserve_cells _ _ _ hr]; exact hmem⟩

variable [CodeEnv]

/-- The table of `odd` at `n`, for caller's memory `R`, return address `ra`
and entry state `t₀` (`r` its `rsp`); the one of `EvenOddGhost/Odd.lean`. -/
abbrev odd_table (n : Nat) (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) :
    Label → MachineData → Prop
  | "odd", s =>
    let r := t₀.regs.get64 .rsp
    s = t₀ ∧ ArgU32 t₀ n
    ∧ (t₀.dmem =⋆ RetCell ra r ⋆ OwnCells r (Reserve (below n) (r - 24) ⋆ R))
  | ".LBB1_2", s =>
    let r := t₀.regs.get64 .rsp
    n ≠ 0 ∧ ArgU32 t₀ n
    ∧ s.regs.get64 .rsp = r - 24 ∧ s.regs.get64 .rbp = r - 8 ∧ SavedRegs t₀ s
    ∧ (s.dmem =⋆ Frame t₀ ra (1 ?@ ·) (Reserve (below n) (r - 24) ⋆ R))
  | ".LBB1_3", s =>
    let r := t₀.regs.get64 .rsp
    ArgU32 t₀ n
    ∧ s.regs.get64 .rsp = r - 24 ∧ s.regs.get64 .rbp = r - 8 ∧ SavedRegs t₀ s
    ∧ (s.dmem =⋆ Frame t₀ ra (Int.toBytes 1 ((n % 2 : Nat) : Int) =@ ·)
        (Reserve (below n) (r - 24) ⋆ R))
  | _, _ => False

set_option maxHeartbeats 4000000 in
theorem odd_specK (hpl : Program.PlacedIn odd_body) (N : Nat) (ih : EvenSpecK N) :
    OddSpecK (N + 1) := by
  refine Kraken.Executable.ProcSpecK.of_cfg_exists (p := odd_body) (β := Nat × (Mem 64 → Prop))
    (fun x ra t₀ => odd_table x.1 x.2 ra t₀)
    (fun x ra t₀ s => x.1 < 2 ^ 32 ∧ CallPostCells x.1 x.2 ra t₀ s ∧ RetU8 s (x.1 % 2))
    (fun ra K t₀ x => x.1 < N + 1 ∧ need x.1 ≤ (t₀.regs.get64 .rsp).toNat
      ∧ ∀ s', OddPost x.1 x.2 ra t₀ s' → K s')
    (hblocks := ?_) (hpre := ?_) (hpost := ?_)
  · rintro ⟨n, R⟩ ra K t₀ ⟨hN, hW, -⟩
    dsimp only at hN hW ⊢
    cfg_cases [odd_body]
    · -- entry: prologue, spill, test
      vcgen
      all_goals call_simp
      all_goals grind_cells
    · -- the call: `even` at `n - 1` by its spec, with our cells as its caller's memory
      rcases n with _ | k
      · exact Triple.intro fun s h => absurd rfl h.1.1
      · have e := Reserve_below_succ k (t₀.regs.get64 .rsp - 24)
          (by unfold need at hW; bv_omega)
        vcgen [MachineWP.call_proc_specK_at "even" ih]
        all_goals call_simp
        -- the witnesses: the callee's argument, and its caller memory — our frame,
        -- the local unwritten, over `R`
        all_goals try refine ⟨fun w => ⟨k, Frame t₀ ra (1 ?@ ·) R, Nat.lt_of_succ_lt_succ hN, ?_,
          fun s' hpost => ?_⟩, ?_⟩
        all_goals try (vcgen; all_goals call_simp)
        all_goals grind_cells
    · -- the result and the epilogue
      vcgen
      all_goals call_simp
      all_goals grind_cells
  · rintro ra K t ⟨n, R, hN, ⟨hcall, harg⟩, hK⟩
    exact ⟨(n, R), ⟨hN, CallPre.le hcall, hK⟩, rfl, harg, CallPre.cells hcall⟩
  · rintro ra K t₀ ⟨n, R⟩ ⟨-, hW, hK⟩ s ⟨-, hcells, hal⟩
    exact hK s ⟨CallPost.of_cells (by unfold need at hW; omega) hcells, hal⟩

end Kraken.Examples.EvenOddExistential.Odd
