import Kraken.X64.Parser
import Kraken.MachineWP

/-!
# A computed jump that reads the pc

`rip_jump` jumps forward to `start`, computes the address of `L0` from a
difference of labels and the address of `L1` (read off the pc), jumps there
through a register, and returns. `rip_jump_spec`: entered with a return
address on the stack, it returns to it, with the stack popped and the memory
unchanged.

The program is the one asked for (`mov L0-L1, %rax` / `jmp %rip(%rax)`),
made legal: x86-64 has no rip-plus-register address, `%rip` reads the address
*behind* the current instruction, and `jmp *d(%rip)` loads its target from
memory. So `%rip` is read once by `lea 0(%rip), %rcx`, which sits just before
`L1` and so yields `L1`, and the jump goes through `%rax`. A leading label
names the entry.

## Findings

* The computed jump itself is unremarkable. The exit channel of the wp is
  pc-valued, so `jmp %r` has a position-independent rule (`jmp_reg_spec`):
  it exits at the register's value. The proof then shows that value is
  `L0`'s address, which is plain `Int64` arithmetic.
* The label difference is also position-independent: `$L0-L1` is a constant
  (`mov_reg_imm_label_sub_spec`). It needed a small parser extension
  (`parseSymImm`); the syntax tree already had `ConstExpr.sub`.
* *Reading the pc* is what doesn't fit. `Executable.wp` quantifies over every
  placement of a fragment, so no precondition can name the value of
  `lea 0(%rip)`. Its rule is stated at a known address instead
  (`lea_rip_disp_run`). For that reason the proof cannot go through
  `ProcSpec.of_cfg`, whose block obligations are triples. It chains the four
  blocks by hand at their labels' addresses (`Triple.run_at` reads a block's
  triple there), using `PlacedIn.next` to learn that the `lea` block ends at
  `L1`. This is easy here because there is no loop; a looping body that reads
  the pc would need a `cfg` whose block obligations may be stated at the
  block's address.
-/

open Kraken MachineWP Std.WP Lean.Order

namespace Kraken.Examples.RipJump

def rip_jump_body : Program := parse("
rip_jump:
  jmp start
L0:
  ret
start:
  mov $L0-L1, %rax
  lea 0(%rip), %rcx
L1:
  add %rcx, %rax
  jmp %rax
")

variable [CodeEnv]

/-- The address of a label in the ambient code. -/
local macro "L" : term => `((_root_.Executable.labels cenv).label)

/-- Entered with `ra` on the stack, `rip_jump` returns to `ra`, with the stack
popped and the memory unchanged. -/
def RipJumpSpec : Prop :=
  cenv.ProcSpec (L "rip_jump") (α := Unit)
    (fun _ ra t => t.retAddr = some ra)
    (fun _ _ t s => s.regs.get64 .rsp = t.regs.get64 .rsp + 8 ∧ s.dmem = t.dmem)

theorem rip_jump_spec (hpl : Program.PlacedIn rip_jump_body) : RipJumpSpec := by
  intro _ ra t hra
  -- where the blocks sit, and that `start` falls into `L1`
  have h0 : cenv.sits (L "rip_jump") (parse("
  jmp start
")) := hpl.block "rip_jump" _ rfl
  have h1 : cenv.sits (L "L0") (parse("
  ret
")) := hpl.block "L0" _ rfl
  have h2 : cenv.sits (L "start") (parse("
  mov $L0-L1, %rax
  lea 0(%rip), %rcx
")) := hpl.block "start" _ rfl
  have h3 : cenv.sits (L "L1") (parse("
  add %rcx, %rax
  jmp %rax
")) := hpl.block "L1" _ rfl
  have hn2 : cenv.after (L "start") (parse("
  mov $L0-L1, %rax
  lea 0(%rip), %rcx
")) = L "L1" := hpl.next "start" _ "L1" rfl rfl
  -- `rip_jump`: jump to `start`
  refine eventually_trans _ _ _ _ (Triple.run_at
    (jmp_label_spec (p := []) (Q := fun _ _ => False)
      (E := fun a s => a = L "start" ∧ s = t) .W64 .W64 "start")
    h0 ⟨rfl, rfl⟩) ?_
  rintro ⟨s, a⟩ hst
  obtain ⟨ha, hs⟩ := hst.resolve_left (·.2)
  dsimp only at ha hs
  subst ha
  subst s
  -- `start`: the label difference, then the pc
  obtain ⟨z, rest, hc, hs'⟩ := h2
  replace hn2 : cenv.after (L "start" + .ofNat z) (parse("
  lea 0(%rip), %rcx
")) = L "L1" := by
    rw [← hn2]; simp only [Executable.after, hc]
  refine eventually_trans _ _ _ _ (Triple.run_at
    (mov_reg_imm_label_sub_spec (p := []) (E := fun _ _ => False)
      (Q := fun _ s => s = { t with
        regs := t.regs.set64 .rax (BitVec.setWidth 64 (L "L0" - L "L1").toBitVec) })
      .W64 .rax "L0" "L1")
    ⟨z, rest, hc, trivial⟩ (fun _ _ => Eventually.done _ (Or.inl ⟨rfl, rfl⟩))) ?_
  rintro ⟨s, a⟩ hst
  obtain ⟨ha, rfl⟩ := hst.resolve_right id
  simp only [Executable.after, hc] at ha
  subst ha
  -- the pc read: `start` ends at `L1` (placement), so `%rcx` is `L1`'s address
  refine lea_rip_disp_run .rcx 0 hs' ?_
  rw [hn2]
  -- `L1`: add, and jump to `L0`
  refine eventually_trans _ _ _ _ (Triple.run_at
    (add_reg_reg_spec (p := parse("
  jmp %rax
")) (Q := fun _ _ => False)
      (E := fun a s => a = L "L0" ∧ s.regs.get64 .rsp = t.regs.get64 .rsp ∧ s.dmem = t.dmem)
      .W64 .rax .rcx) h3 ?_) ?_
  · apply (jmp_reg_spec (p := []) (Q := fun _ _ => False)
      (E := fun a s => a = L "L0" ∧ s.regs.get64 .rsp = t.regs.get64 .rsp ∧ s.dmem = t.dmem)
      .W64 .W64 .rax).le_wp
    refine ⟨?_, ?_, rfl⟩
    · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
      apply Int64.toBitVec_inj.mp
      simp [Int64.toBitVec_sub]
      rw [BitVec.add_comm, BitVec.sub_add_cancel]
    · simp
  rintro ⟨s, a⟩ hst
  obtain ⟨rfl, hrsp, hmem⟩ := hst.resolve_left (·.2)
  -- `L0`: return
  refine eventually_trans _ _ _ _ (Triple.run_at
    (ret_spec (p := []) (Q := fun _ _ => False)
      (E := fun a s' => a = ra ∧ s'.regs.get64 .rsp = t.regs.get64 .rsp + 8 ∧ s'.dmem = t.dmem)
      .W64 .W64) h1 ?_) ?_
  · have hr : s.retAddr = some ra := by
      rw [MachineData.retAddr_eq, hrsp, hmem, ← MachineData.retAddr_eq, hra]
    simp only [meet_prop_eq_and]
    refine ⟨by simp [hr], fun ra' h' => ⟨?_, ?_, hmem⟩⟩
    · rw [hr] at h'; exact (Option.some.inj h').symm
    · simp [hrsp]
  rintro ⟨s', a⟩ hst
  obtain ⟨rfl, h⟩ := hst.resolve_left (·.2)
  exact Eventually.done _ ⟨rfl, h⟩

end Kraken.Examples.RipJump
