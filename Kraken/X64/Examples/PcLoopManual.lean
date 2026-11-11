import Kraken.X64.Parser
import Kraken.MachineWP

/-!
# A loop that reads the pc, by hand

The program and specification of `PcLoopCfg.lean`:

```
; rax = rdi, by counting
count:
    xor     eax, eax
.Lloop:
    lea     rcx, [rip]                ; rcx = address of the next instruction = .Lhere
.Lhere:
    test    rdi, rdi
    jz      .Ldone
    dec     rdi
    add     rax, 1
    sub     rcx, .Lhere - .Lloop      ; rcx = .Lloop (the immediate is a label difference)
    jmp     rcx                       ; back edge
.Ldone:
    ret
```

proved without `ProcSpec.of_cfg_at`/`TripleAt`, i.e. with the control-flow
rule as it was before that change.

## The difficulty

A triple holds at every placement of its fragment, so no triple says what
`lea rcx, [rip]` puts in `rcx`: the block `.Lloop` has no triple, and
`ProcSpec.of_cfg` asks for one of every block. Outside `of_cfg` the
instruction can be stepped at a known address (`lea_rip_disp_run`), but then
everything `of_cfg` did must be done by hand:

* **The induction.** `of_cfg` inducts on a variant once, for every loop. Here
  the proof states the loop's property as an `Eventually` from `.Lloop` and
  proves it by strong induction on `rdi`, threading the invariant through.
* **The placement.** Each block's place (`PlacedIn.block`) and the fall-through
  addresses (`PlacedIn.next`) are spelled out, block text included.
* **The gluing.** Each block is a triple read at its address
  (`Triple.run_at`), and the runs are chained with `eventually_trans`; the
  exits of each block are given by hand, with the facts the next block needs.
  `vcgen` still proves each block's triple, but not the whole procedure.

`RipJump.lean` is a straight line, so it needs no induction and the chain is
the whole proof. With a loop, the hand-written part grows with the control
flow, which is what `of_cfg` exists to absorb. Compare `PcLoopCfg.lean`.
-/

open Kraken MachineWP Std.WP Lean.Order

namespace Kraken.Examples.PcLoopManual

def count_body : Program := parse("
count:
  xorl %eax, %eax
.Lloop:
  leaq 0(%rip), %rcx
.Lhere:
  testq %rdi, %rdi
  je .Ldone
  decq %rdi
  addq $1, %rax
  subq $.Lhere-.Lloop, %rcx
  jmp %rcx
.Ldone:
  ret
")

/-- The back edge: `rcx = .Lhere`, minus `.Lhere - .Lloop`, is `.Lloop`. -/
theorem back_edge {rcx : BitVec 64} {a b : Int64} (h : rcx = a.toBitVec) :
    Int64.ofBitVec (rcx - BitVec.setWidth 64 (a - b).toBitVec) = b := by
  apply Int64.toBitVec_inj.mp
  rw [Int64.toBitVec_ofBitVec, BitVec.setWidth_eq, Int64.toBitVec_sub, h]
  bv_omega

variable [CodeEnv]

/-- The address of a label in the ambient code. -/
local macro "L" : term => `((_root_.Executable.labels cenv).label)

def CountSpec : Prop :=
  cenv.ProcSpec (L "count") (α := Unit)
    (fun _ ra t => t.retAddr = some ra)
    (fun _ _ t s => s.regs.get64 .rsp = t.regs.get64 .rsp + 8 ∧ s.dmem = t.dmem
      ∧ s.regs.get64 .rax = t.regs.get64 .rdi)

/-- The loop invariant: what is counted plus what is left is the argument, and
the stack and memory are as on entry. -/
abbrev Inv (ra : Int64) (t₀ s : MachineData) : Prop :=
  s.regs.get64 .rax + s.regs.get64 .rdi = t₀.regs.get64 .rdi
  ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.dmem = t₀.dmem ∧ t₀.retAddr = some ra

/-- At `.Ldone`: the count is the argument. -/
abbrev Done (ra : Int64) (t₀ s : MachineData) : Prop :=
  s.regs.get64 .rax = t₀.regs.get64 .rdi
  ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.dmem = t₀.dmem ∧ t₀.retAddr = some ra

theorem count_spec (hpl : Program.PlacedIn count_body) : CountSpec := by
  intro _ ra t₀ hra
  -- where the blocks sit, and where the first two fall through to
  have h0 : cenv.sits (L "count") (parse("
  xorl %eax, %eax
")) := hpl.block "count" _ rfl
  have hn0 : cenv.after (L "count") (parse("
  xorl %eax, %eax
")) = L ".Lloop" := hpl.next "count" _ ".Lloop" rfl rfl
  have h1 : cenv.sits (L ".Lloop") (parse("
  leaq 0(%rip), %rcx
")) := hpl.block ".Lloop" _ rfl
  have hn1 : cenv.after (L ".Lloop") (parse("
  leaq 0(%rip), %rcx
")) = L ".Lhere" := hpl.next ".Lloop" _ ".Lhere" rfl rfl
  have h2 : cenv.sits (L ".Lhere") (parse("
  testq %rdi, %rdi
  je .Ldone
  decq %rdi
  addq $1, %rax
  subq $.Lhere-.Lloop, %rcx
  jmp %rcx
")) := hpl.block ".Lhere" _ rfl
  have h3 : cenv.sits (L ".Ldone") (parse("
  ret
")) := hpl.block ".Ldone" _ rfl
  -- `.Lhere`, as a triple: out to `.Ldone`, or back to `.Lloop` with less left
  have hbody : ∀ n, ⦃ fun s => Inv ra t₀ s ∧ s.regs.get64 .rcx = (L ".Lhere").toBitVec
        ∧ (s.regs.get64 .rdi).toNat = n ⦄
      (parse("
  testq %rdi, %rdi
  je .Ldone
  decq %rdi
  addq $1, %rax
  subq $.Lhere-.Lloop, %rcx
  jmp %rcx
"))
      ⦃ fun _ _ => False;
        fun a s => (a = L ".Ldone" ∧ Done ra t₀ s)
          ∨ (a = L ".Lloop" ∧ Inv ra t₀ s ∧ (s.regs.get64 .rdi).toNat < n) ⦄ := by
    intro n
    vcgen
    all_goals call_simp
    · grind [BitVec.and_self]
    · rw [back_edge (a := L ".Lhere") (by grind)]
      grind [BitVec.and_self]
  -- `.Ldone`, as a triple: return
  have hdone : ⦃ fun s => Done ra t₀ s ⦄ (parse("
  ret
")) ⦃ fun _ _ => False; fun a s => a = ra ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp + 8
        ∧ s.dmem = t₀.dmem ∧ s.regs.get64 .rax = t₀.regs.get64 .rdi ⦄ := by
    vcgen
    all_goals call_simp
    all_goals grind
  -- the loop, from `.Lloop`, by strong induction on what is left in `rdi`
  have loop : ∀ n s, (s.regs.get64 .rdi).toNat = n → Inv ra t₀ s →
      Eventually cenv.instrStep (fun st => st.2 = ra ∧ st.1.regs.get64 .rsp = t₀.regs.get64 .rsp + 8
        ∧ st.1.dmem = t₀.dmem ∧ st.1.regs.get64 .rax = t₀.regs.get64 .rdi)
        (s, L ".Lloop") := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
    intro s hn hinv
    -- `.Lloop`: the pc read, stepped at its address
    refine lea_rip_disp_run .rcx 0 h1 ?_
    rw [hn1]
    -- `.Lhere`
    refine eventually_trans _ _ _ _ (Triple.run_at (hbody n) h2 ?_) ?_
    · simp_all [Inv]
    rintro ⟨s', a⟩ hst
    rcases hst.resolve_left (·.2) with ⟨rfl, hd⟩ | ⟨rfl, hinv', hlt⟩
    · -- out: `.Ldone`
      refine eventually_trans _ _ _ _ (Triple.run_at hdone h3 hd) ?_
      rintro ⟨s'', a⟩ hst
      exact Eventually.done _ (hst.resolve_left (·.2))
    · -- back: `.Lloop`, with less left
      exact ih _ hlt s' rfl hinv'
  -- `count`: clear `eax`, fall into the loop
  have hentry : ⦃ fun s => s = t₀ ⦄ (parse("
  xorl %eax, %eax
")) ⦃ fun _ s => Inv ra t₀ s; fun _ _ => False ⦄ := by
    vcgen
    all_goals call_simp
    all_goals grind
  refine eventually_trans _ _ _ _ (Triple.run_at hentry h0 rfl) ?_
  rintro ⟨s, a⟩ hst
  obtain ⟨rfl, hinv⟩ := hst.resolve_right id
  rw [hn0]
  exact loop _ s rfl hinv

end Kraken.Examples.PcLoopManual
