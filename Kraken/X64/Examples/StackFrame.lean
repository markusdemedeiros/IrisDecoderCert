import Kraken.X64.Parser
import Kraken.MachineWP
import Kraken.SepCells

/-!
A compiler's frame code, straight-line: the prologue, a spill of the argument,
a compare against it, a reload, a byte local written and read back, and the
epilogue. The proof exercises the stack and sub-register rules together with
the `=@`/`?@` cells: the saved frame pointer survives the local stores, the
locals are read back as written, and the frame comes back as owned bytes.
-/

open Kraken.X64.Parser
open Kraken
open Std.WP
open Std.ExtHashMap
open Mem
open MachineWP
open Lean.Order

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.StackFrame

def frame : Program := parse("
start:
  pushq %rbp
  movq %rsp, %rbp
  subq $16, %rsp
  movl %edi, -8(%rbp)
  cmpl $0, -8(%rbp)
  movl -8(%rbp), %edi
  movb $1, -1(%rbp)
  movb -1(%rbp), %al
  andb $1, %al
  addq $16, %rsp
  popq %rbp
")

variable [layout : _root_.Layout]

local instance frame.env : CodeEnv := ⟨layout frame⟩

/-- The cells of the frame below the entry stack pointer `r`, in front of the
rest `R`: the saved frame pointer's slot, the unused 8 bytes, the 4-byte
local, 3 unused bytes, the byte local. -/
abbrev FrameCells (r : BitVec 64) (R : Mem 64 → Prop) : Mem 64 → Prop :=
  8 ?@ (r - 8) ⋆ (8 ?@ (r - 24) ⋆ (4 ?@ (r - 16) ⋆ (3 ?@ (r - 12) ⋆ (1 ?@ (r - 9) ⋆ R))))

/- The cell rules chain through the tree (a demand down to the cell, a split
back up, per access, then a walk of the goal's tree), so `finish` needs many
more E-matching rounds and a deeper generation bound than its defaults; see
`grind_cells` in `SepCells`. -/
theorem frame_correct (d : MachineData) (R : Mem 64 → Prop)
    (hmem : d.dmem =⋆ FrameCells (d.regs.get64 .rsp) R) :
    ⦃ fun s => s = d ⦄
      frame
    ⦃ fun _ s =>
        s.regs.get64 .rsp = d.regs.get64 .rsp
        ∧ s.regs.get64 .rbp = d.regs.get64 .rbp
        ∧ (s.regs.get64 .rdi).toNat = (d.regs.get64 .rdi).toNat % 2 ^ 32
        ∧ (s.regs.get64 .rax).toNat % 256 = 1
        ∧ s.dmem =⋆ FrameCells (d.regs.get64 .rsp) R ⦄ := by
  vcgen [frame] with finish (ematch := 400) (gen := 400) (instances := 20000)

end Kraken.Examples.StackFrame
