import Kraken.X64.Parser
import Kraken.Rules.IndirectCall

/-!
# Calls through a code pointer: one fragment per shape

Each fragment is a single indirect call. The callee is any procedure `f`
whose `ProcSpec` returns with `rax = 42` and pops the return address, and the
caller's state says the pointer is `f`:

```
call qword ptr [rdi + 8]             ; callDisp: a struct field
call qword ptr [rdi]                 ; callZero: displacement 0
call rax                             ; callReg
call qword ptr [rdi + 8*rcx + 8]     ; callIdx: a table slot
```

## Findings

* `call_mem_proc_spec_at` and `call_reg_proc_spec_at` take the callee's
  `ProcSpec` as `call_proc_spec_at` does, and a call site uses the same steps
  as for a direct call. `vcgen [prog, hc]` steps the call. A `refine` opens
  the rule's `∀ ra` shape, and a second `vcgen` steps the tail (here the empty
  tail) under the callee's postcondition. `grind` closes the rest: the pointer
  is `f`, `retAddr` of the pushed state, and the stack slot.
* With no rule passed in, `vcgen` picks the `@[spec low]` `call_mem_spec`.
  Its obligation `CallsTo (ptr) K s` is closed by
  `CallsTo.of_procSpec () hf`, once `grind` shows the loaded value is `f`
  (`call_idx_generic`).
* The pointer is read as `(load a 8).map toAddr = some f`, the `fnPtr` form of
  `IndirectTailCall`. `grind` matches the generic address
  `rdi + offset64 idx regs + 8` against the precondition's `rdi + rcx * 8 + 8`
  through the `AddrIndex.offset64_*` normalisation in `GenericMem`.
-/

open Kraken MachineWP Std.WP Lean.Order
open scoped Kraken.Rules.GenericMem.Norm

set_option mvcgen.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.IndirectCall

def callDisp : Program := parse("
  call *8(%rdi)
")

def callZero : Program := parse("
  call *(%rdi)
")

def callReg : Program := parse("
  call *%rax
")

def callIdx : Program := parse("
  call *8(%rdi,%rcx,8)
")

variable [CodeEnv]

/-- The callee's contract: entered by a call, it returns with `rax = 42` and
the stack pointer one word above its entry value. -/
abbrev Pre : Unit → Int64 → MachineData → Prop := fun _ ra t => t.retAddr = some ra

abbrev Post : Unit → Int64 → MachineData → MachineData → Prop :=
  fun _ _ t s => s.regs.get64 .rax = 42 ∧ s.regs.get64 .rsp = t.regs.get64 .rsp + 8

/-- The 8 bytes at `a`, read as an address. -/
abbrev ptrAt (t : MachineData) (a : BitVec 64) : Option Int64 :=
  (Mem.loadInt t.dmem a 8).map (fun v => Int64.ofBitVec (BitVec.ofInt 64 v))

/-- The stack slot a call writes is mapped. -/
abbrev Slot (t : MachineData) : Prop :=
  (Mem.loadInt t.dmem (t.regs.get64 .rsp - Width.W64.bytesv) Width.W64.bytes).isSome = true

theorem call_disp {f : Int64} (hf : cenv.ProcSpec f Pre Post) (s₀ : MachineData) :
    ⦃ fun s => s = s₀ ∧ ptrAt s (s.regs.get64 .rdi + 8) = some f ∧ Slot s ⦄
      callDisp
    ⦃ fun _ s => s.regs.get64 .rax = 42 ∧ s.regs.get64 .rsp = s₀.regs.get64 .rsp ⦄ := by
  vcgen [callDisp, call_mem_proc_spec_at () f hf]
  refine ⟨?_, fun ra => ⟨?_, fun s' hpost => ?_⟩, ?_⟩
  all_goals try (vcgen; all_goals call_simp)
  all_goals grind

theorem call_zero {f : Int64} (hf : cenv.ProcSpec f Pre Post) (s₀ : MachineData) :
    ⦃ fun s => s = s₀ ∧ ptrAt s (s.regs.get64 .rdi) = some f ∧ Slot s ⦄
      callZero
    ⦃ fun _ s => s.regs.get64 .rax = 42 ∧ s.regs.get64 .rsp = s₀.regs.get64 .rsp ⦄ := by
  vcgen [callZero, call_mem_proc_spec_at () f hf]
  refine ⟨?_, fun ra => ⟨?_, fun s' hpost => ?_⟩, ?_⟩
  all_goals try (vcgen; all_goals call_simp)
  all_goals grind

theorem call_reg {f : Int64} (hf : cenv.ProcSpec f Pre Post) (s₀ : MachineData) :
    ⦃ fun s => s = s₀ ∧ Int64.ofBitVec (s.regs.get64 .rax) = f ∧ Slot s ⦄
      callReg
    ⦃ fun _ s => s.regs.get64 .rax = 42 ∧ s.regs.get64 .rsp = s₀.regs.get64 .rsp ⦄ := by
  vcgen [callReg, call_reg_proc_spec_at () f hf]
  refine ⟨?_, fun ra => ⟨?_, fun s' hpost => ?_⟩, ?_⟩
  all_goals try (vcgen; all_goals call_simp)
  all_goals grind

theorem call_idx {f : Int64} (hf : cenv.ProcSpec f Pre Post) (s₀ : MachineData) :
    ⦃ fun s => s = s₀
        ∧ ptrAt s (s.regs.get64 .rdi + s.regs.get64 .rcx * 8 + 8) = some f ∧ Slot s ⦄
      callIdx
    ⦃ fun _ s => s.regs.get64 .rax = 42 ∧ s.regs.get64 .rsp = s₀.regs.get64 .rsp ⦄ := by
  vcgen [callIdx, call_mem_proc_spec_at () f hf]
  refine ⟨?_, fun ra => ⟨?_, fun s' hpost => ?_⟩, ?_⟩
  all_goals try (vcgen; all_goals call_simp)
  all_goals grind

theorem call_idx_generic {f : Int64} (hf : cenv.ProcSpec f Pre Post) (s₀ : MachineData) :
    ⦃ fun s => s = s₀
        ∧ ptrAt s (s.regs.get64 .rdi + s.regs.get64 .rcx * 8 + 8) = some f ∧ Slot s ⦄
      callIdx
    ⦃ fun _ s => s.regs.get64 .rax = 42 ∧ s.regs.get64 .rsp = s₀.regs.get64 .rsp ⦄ := by
  vcgen [callIdx]
  case vc3 =>
    rename_i v hv
    have hvf : Int64.ofBitVec (BitVec.ofInt 64 v) = f := by grind [Option.map_eq_some_iff]
    rw [hvf]
    refine CallsTo.of_procSpec () hf fun ra => ⟨?_, fun s' hpost => ?_⟩
    all_goals try (vcgen; all_goals call_simp)
    all_goals grind
  all_goals grind [Option.map_eq_some_iff]

end Kraken.Examples.IndirectCall
