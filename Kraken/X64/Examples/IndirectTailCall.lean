import Kraken.X64.Parser
import Kraken.MachineWP

/-!
# An indirect tail call through a code pointer in memory

`invoke` calls the function an object points to, as a tail call:

```c
struct obj { long data; long (*fn)(struct obj *); };
long invoke(struct obj *o) { return o->fn(o); }
```

```
invoke:
    jmp     qword ptr [rdi + 8]       ; o->fn, at offset 8
```

`invoke_spec` is higher-order: it is stated over any procedure `f` and its
`ProcSpec`. If the object's pointer is `f` and `f`'s precondition holds, then
`invoke` meets `f`'s spec. `handler` is one such `f` (`mov eax, 42; ret`), and
`invoke_handler` instantiates `invoke_spec` with it.

## Findings

* The rule `jmp_mem_base_disp_spec` asks that the 8 bytes be readable and
  exits at the address they hold. Like `jmp %r`, it is position-independent:
  where control lands is the caller's business.
* The control-flow rule already handles a jump out of the procedure to an
  unknown address. `ProcSpec.of_cfg` takes the exits besides the return
  (`Exit`) and a proof that each exit reaches `ra` with `Post` (`hexit`).
  Here the exit is "at `f`, in the entry state", and `hexit` is `f`'s
  `ProcSpec`. A tail call reaches `ra` through `f`.
* The pointer is stated as `fnPtr t = some f`: the 8 bytes at `rdi + 8`,
  decoded as an address, in the style of `MachineData.retAddr`. The caller,
  not the program, establishes it. Kraken has no data directive for a label's
  address (`.quad handler`), so a statically initialised object would be an
  assumption about `dmem` too (compare the note in `JumpTable.lean`).
-/

open Kraken MachineWP Std.WP Lean.Order

namespace Kraken.Examples.IndirectTailCall

def invoke_body : Program := parse("
invoke:
  jmp *8(%rdi)
")

def handler_body : Program := parse("
handler:
  movl $42, %eax
  ret
")

variable [CodeEnv]

/-- The address of a label in the ambient code. -/
local macro "L" : term => `((_root_.Executable.labels cenv).label)

/-- The code pointer of the object `rdi` points to: the 8 bytes at offset 8,
read as an address. -/
abbrev fnPtr (t : MachineData) : Option Int64 :=
  (Mem.loadInt t.dmem (t.regs.get64 .rdi + 8) 8).map (fun v => Int64.ofBitVec (BitVec.ofInt 64 v))

/-- Whatever `f` does, `invoke` does, given that the object points to `f`. -/
theorem invoke_spec {α : Type} {Pre : α → Int64 → MachineData → Prop}
    {Post : α → Int64 → MachineData → MachineData → Prop} {f : Int64}
    (hf : cenv.ProcSpec f Pre Post) (hpl : Program.PlacedIn invoke_body) :
    cenv.ProcSpec (L "invoke") (fun x ra t => fnPtr t = some f ∧ Pre x ra t) Post := by
  refine Kraken.Executable.ProcSpec.of_cfg (p := invoke_body)
    (fun x ra t₀ l s => l = "invoke" ∧ s = t₀ ∧ fnPtr t₀ = some f ∧ Pre x ra t₀)
    (Exit := fun x ra t₀ a s => a = f ∧ s = t₀ ∧ Pre x ra t₀)
    (hblocks := ?_) (hpre := ?_) (hexit := ?_)
  · intro x ra t₀
    cfg_cases [invoke_body]
    vcgen
    all_goals simp_all
    -- the pointer is readable (the target being `f` is solved by `simp_all`)
    rename_i h
    obtain ⟨⟨-, ⟨v, hv, -⟩, -⟩, -⟩ := h
    simp [hv]
  · rintro x ra t ⟨hp, hpre⟩
    exact ⟨rfl, rfl, hp, hpre⟩
  · -- the tail call: from `f`, in the entry state, `f`'s spec reaches `ra`
    rintro x ra t₀ a s ⟨rfl, rfl, hpre⟩
    exact hf x ra s hpre

/-- `handler` returns 42. -/
def HandlerSpec : Prop :=
  cenv.ProcSpec (L "handler") (α := Unit)
    (fun _ ra t => t.retAddr = some ra)
    (fun _ _ t s => s.regs.get64 .rsp = t.regs.get64 .rsp + 8 ∧ s.dmem = t.dmem
      ∧ s.regs.get64 .rax = 42)

theorem handler_spec (hpl : Program.PlacedIn handler_body) : HandlerSpec := by
  refine Kraken.Executable.ProcSpec.of_cfg (p := handler_body)
    (fun _ ra t₀ l s => l = "handler" ∧ s = t₀ ∧ t₀.retAddr = some ra)
    (hblocks := ?_) (hpre := ?_)
  · intro _ ra t₀
    cfg_cases [handler_body]
    vcgen
    all_goals call_simp
    all_goals grind
  · rintro _ ra t hra
    exact ⟨rfl, rfl, hra⟩

/-- `invoke` on an object that points to `handler` returns 42. -/
theorem invoke_handler (hpl₁ : Program.PlacedIn invoke_body)
    (hpl₂ : Program.PlacedIn handler_body) :
    cenv.ProcSpec (L "invoke") (α := Unit)
      (fun _ ra t => fnPtr t = some (L "handler") ∧ t.retAddr = some ra)
      (fun _ _ t s => s.regs.get64 .rsp = t.regs.get64 .rsp + 8 ∧ s.dmem = t.dmem
        ∧ s.regs.get64 .rax = 42) :=
  invoke_spec (handler_spec hpl₂) hpl₁

end Kraken.Examples.IndirectTailCall
