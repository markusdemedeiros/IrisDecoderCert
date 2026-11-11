import Kraken.X64.Parser
import Kraken.MachineWP

/-!
# A loop that reads the pc, through the control-flow rule at addresses

`count` counts `rdi` down to zero in a loop whose back edge is a computed
jump, to an address derived from the pc:

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

`count_spec`: entered with a return address on the stack, `count` returns to
it with `rax = rdi`, the stack popped and the memory unchanged.

## The difficulty

`Executable.wp`, and so every triple `⦃P⦄ q ⦃Q; E⦄`, quantifies over every
placement of `q`: one triple holds wherever the fragment sits. That is what
makes the rules reusable, and it is also why no rule can name the value
`lea rcx, [rip]` computes, the address right after it. That value differs
from one placement to the next, and a precondition cannot depend on the
placement. So the block `.Lloop: lea rcx, [rip]` has no triple that says
`rcx = .Lhere`. And `ProcSpec.of_cfg`, which supplies the induction a loop
needs (here on `rdi`), asks for a triple of every block.

`PcLoopManual.lean` proves the same program without changing the library: it
redoes `of_cfg`'s induction by hand.

## The fix used here

`MachineWP.TripleAt pc P q Q E` is the judgment at one address. Every triple
gives one at every address (`TripleAt.of_triple`), and the pc-reading
instruction has a rule in this form (`lea_rip_disp_at`). Its precondition
names `cenv.after pc [lea]`, a term in the fixed `pc`, which the placement
fact `PlacedIn.next` rewrites to `.Lhere`'s address. `ProcSpec.of_cfg_at` is
`of_cfg` with each block's obligation a `TripleAt` at its label's address.
`of_cfg` itself is now the special case where every obligation comes from a
triple, so nothing else changed. In the proof below, three blocks are ordinary
triples (`TripleAt.of_triple`, then `vcgen` and `grind`; the back edge also
uses `back_edge` for the jump target), and only `.Lloop` uses the address.
That block takes four lines, where `PcLoopManual.lean` writes out the
induction, the placements and the gluing by hand.
-/

open Kraken MachineWP Std.WP Lean.Order

namespace Kraken.Examples.PcLoopCfg

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

abbrev count_table (ra : Int64) (t₀ : MachineData) : Label → MachineData → Prop
  | "count", s => s = t₀ ∧ t₀.retAddr = some ra
  | ".Lloop", s => Inv ra t₀ s
  | ".Lhere", s => Inv ra t₀ s ∧ s.regs.get64 .rcx = (L ".Lhere").toBitVec
  | ".Ldone", s => s.regs.get64 .rax = t₀.regs.get64 .rdi
      ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.dmem = t₀.dmem ∧ t₀.retAddr = some ra
  | _, _ => False

theorem count_spec (hpl : Program.PlacedIn count_body) : CountSpec := by
  -- `.Lloop` (the `lea`) ends at `.Lhere`: the placement fact the pc read needs
  have hn : cenv.after (L ".Lloop") (parse("
  leaq 0(%rip), %rcx
")) = L ".Lhere" := hpl.next ".Lloop" _ ".Lhere" rfl rfl
  refine Kraken.Executable.ProcSpec.of_cfg_at (p := count_body)
    (fun _ ra t₀ => count_table ra t₀) (var := fun _ s => (s.regs.get64 .rdi).toNat)
    (hblocks := ?_) (hpre := ?_)
  · intro _ ra t₀
    cfg_cases [count_body]
    · -- entry: `xor eax, eax`
      apply TripleAt.of_triple
      vcgen
      all_goals call_simp
      all_goals grind
    · -- `.Lloop`: the pc read, at the block's own address
      refine TripleAt.pre ?_ (lea_rip_disp_at .rcx 0 (L ".Lloop"))
      rintro s ⟨⟨h1, h2, h3, h4⟩, rfl⟩
      rw [hn]
      simp_all [count_table, Inv]
    · -- `.Lhere`: the test, the count, and the computed back edge
      apply TripleAt.of_triple
      vcgen
      all_goals call_simp
      · grind [BitVec.and_self]
      · rw [back_edge (a := L ".Lhere") (by grind)]
        grind [BitVec.and_self]
    · -- `.Ldone`: return
      apply TripleAt.of_triple
      vcgen
      all_goals call_simp
      all_goals grind
  · rintro _ ra t hra
    exact ⟨rfl, hra⟩

end Kraken.Examples.PcLoopCfg
