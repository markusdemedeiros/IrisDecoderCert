/-
Trap instructions (`ud1`, `ud2`, `int3`) have no successor state: a step that
reaches one satisfies no postcondition, so a proof that the routine reaches
its return address proves every trap unreachable. They cannot be run by the
hardware tests (they would kill the test process), so they are checked here.
-/
import Kraken.X64.OmniSemantics
import Kraken.X64.Parser

open Kraken.X64.Parser

theorem Operation.ud1_faults [Labels] [AddressSize] {w} (r : Reg w) (src : RegOrMem w)
    (p : Std.Rco Int64) (s : MachineData) (next : MachineData → Effects)
    (jmp : Int64 → MachineData → Effects) (P : MachineState → Prop) :
    ¬ (Operation.interp (.ud1 r src) p s next jmp).All P := by
  simp [Operation.interp, Effects.All]

theorem Operation.ud2_faults [Labels] [AddressSize] {w} (p : Std.Rco Int64) (s : MachineData)
    (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects)
    (P : MachineState → Prop) :
    ¬ (Operation.interp (w := w) .ud2 p s next jmp).All P := by
  simp [Operation.interp, Effects.All]

theorem Operation.int3_faults [Labels] [AddressSize] {w} (p : Std.Rco Int64) (s : MachineData)
    (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects)
    (P : MachineState → Prop) :
    ¬ (Operation.interp (w := w) .int3 p s next jmp).All P := by
  simp [Operation.interp, Effects.All]

/-- A whole step through a parsed `ud1` (the bounds-check trap that clang
emits for `-fsanitize=array-bounds -fsanitize-trap`) faults. -/
theorem ud1_step_faults [Labels] (s : MachineData) (p : Std.Rco Int64)
    (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects)
    (P : MachineState → Prop) :
    ¬ (Directive.interp
        (.instr (.regular .W32 .W32 (.ud1 (.low .rax .W32) (.mem ⟨some (.reg .rax), none, .int64 0x12⟩))))
        s p next jmp).All P := by
  simp [Directive.interp, Instr.interp, Operation.interp, Effects.All]

/-- The parser produces exactly that directive. -/
example : parse("ud1 0x12(%eax),%eax") =
    [.instr (.regular .W32 .W32 (.ud1 (.low .rax .W32) (.mem ⟨some (.reg .rax), none, .int64 0x12⟩)))] := rfl

private def runFrom (prog : Program) : Except String Reg64s :=
  let exe := Program.fakeLayout prog
  let start := (Executable.labels exe).label "main"
  let data : MachineData := { dmem := (List.replicate 64 0).At 0x100, regs := { rsp := 0x120 } }
  (Executable.eval exe (data, start) (fun _ => false)).map (·.1.regs)

/-- info: Except.error "trap: ud2" -/
#guard_msgs in
#eval runFrom parse("main:\n  inc %rax\n  ud2\n  ret")

/-- info: Except.error "trap: int3" -/
#guard_msgs in
#eval runFrom parse("main:\n  int3")

/-- info: Except.error "trap: ud1" -/
#guard_msgs in
#eval runFrom parse("main:\n  ud1 0x12(%eax),%eax")

/-! A legacy SSE 128-bit memory operand must be 16-byte aligned (`movdqu` and
the VEX forms need not be). -/

/--
info: Except.error "#GP: Memory op at 0x0000000000000108#64 did not have mandatory alignment of 16"
-/
#guard_msgs in
#eval runFrom parse("main:\n  movdqa 0x108(,%rax,1),%xmm0\n  ud2")

/-- info: Except.error "trap: ud2" -/
#guard_msgs in
#eval runFrom parse("main:\n  movdqu 0x108(,%rax,1),%xmm0\n  ud2")
