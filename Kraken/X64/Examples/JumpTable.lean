import Kraken.X64.Parser
import Kraken.MachineWP

/-!
# A jump table

`sel` is what clang `-O2` emits for

```c
int sel(unsigned x) {
  switch (x) { case 0: return 10; case 1: return 20; case 2: return 30; default: return 0; }
}
```

In Intel syntax (the body below is its AT&T transcription; Kraken's parser
reads AT&T):

```
sel:
    cmp     edi, 2
    ja      .Ldefault
    mov     eax, edi                          ; zero-extends x into rax
    lea     rcx, [rip + .LJTI0_0]             ; table base
    movsxd  rax, dword ptr [rcx + 4*rax]      ; entry = case label - table base
    add     rax, rcx                          ; absolute target
    jmp     rax
.Lcase0:
    mov     eax, 10
    ret
.Lcase1:
    mov     eax, 20
    ret
.Lcase2:
    mov     eax, 30
    ret
.Ldefault:
    xor     eax, eax
    ret

    .section .rodata
    .p2align 2
.LJTI0_0:
    .long   .Lcase0 - .LJTI0_0
    .long   .Lcase1 - .LJTI0_0
    .long   .Lcase2 - .LJTI0_0
```

`sel_spec`: entered with a return address on the stack and the table in
memory, `sel` returns to it with `eax = selFn x` (zero-extended into `rax`),
the stack popped and the memory unchanged.

> **Note: the table is an assumption, not part of the program.** Kraken's
> syntax has no `.long`. Its only data directive is `.byte`, which holds fixed
> bytes, not label differences, and loads read the data memory `dmem`, not
> the code image. So the `.rodata` table is not in `sel_body`. Instead,
> `JumpTable` (in the precondition) says that `dmem` holds the three entries
> at `.LJTI0_0`, each one the offset of its case from the table: what the
> loader, having applied the relocations, puts there. Making the table part
> of the program would need a symbolic data directive (`.long a - b`) and a
> placement fact tying `dmem` at a data label to the directive's value.

## Findings

* With the table in the precondition, a jump table is ordinary code for the
  machine-founded wp. The pc is read only through a label
  (`lea .LJTI0_0(%rip)`), which the assembler's displacement makes
  position-independent, so every rule is a `@[spec]` triple and the proof
  goes through `ProcSpec.of_cfg` with `vcgen`, unlike `RipJump`.
* The computed jump exits at `L .LJTI0_0 + sext entry`. `JumpTable` turns
  that into `L .Lcase_x` (`target_eq`), and the label table picks block
  `.Lcase_x`.
* The `movsxd` address depends on `x`, so the dispatch block splits on
  `x ∈ {0, 1, 2}` by hand after the bounds check. That split, and matching
  each load against its table entry, is the only manual part. The case
  blocks and the out-of-range branch are `vcgen` + `grind`.
* Library additions this needed: the parser learned `movslq`; there are new
  rules for `cmpl $i, %r32`, `movl` (register and immediate), `xorl`,
  `leaq sym(%rip)` and `movslq (%b,%i,s)`; and `CondCode.interp_a_sub` /
  `interp_be_sub` read `ja`/`jbe` after `cmp` as the unsigned order.
-/

open Kraken MachineWP Std.WP Lean.Order

namespace Kraken.Examples.JumpTable

def sel_body : Program := parse("
sel:
  cmpl $2, %edi
  ja .Ldefault
  movl %edi, %eax
  leaq .LJTI0_0(%rip), %rcx
  movslq (%rcx,%rax,4), %rax
  addq %rcx, %rax
  jmp %rax
.Lcase0:
  movl $10, %eax
  ret
.Lcase1:
  movl $20, %eax
  ret
.Lcase2:
  movl $30, %eax
  ret
.Ldefault:
  xorl %eax, %eax
  ret
")

/-- The C function. -/
def selFn (x : BitVec 32) : BitVec 32 :=
  if x = 0 then 10 else if x = 1 then 20 else if x = 2 then 30 else 0

/-- The jump target: the table's address plus the loaded entry, sign-extended,
is the case's address, by the table's entry. -/
theorem target_eq {m : DataMem} {a : BitVec 64} {tbl tgt : Int64} {e v : Int}
    (hl : Mem.loadInt m a 4 = some e) (hv : Mem.loadInt m a 4 = some v)
    (ht : (BitVec.ofInt 32 e).signExtend 64 + tbl.toBitVec = tgt.toBitVec) :
    tbl + Int64.ofBitVec ((BitVec.ofInt 32 v).signExtend 64) = tgt := by
  rw [hl, Option.some.injEq] at hv
  subst hv
  apply Int64.toBitVec_inj.mp
  rw [Int64.toBitVec_add, Int64.toBitVec_ofBitVec, BitVec.add_comm, ht]

variable [CodeEnv]

/-- The address of a label in the ambient code. -/
local macro "L" : term => `((_root_.Executable.labels cenv).label)

/-- Entry `k` of the table: the 4 bytes at `.LJTI0_0 + 4k`, sign-extended and
added to the table's address, give `target`'s address. -/
def Entry (m : DataMem) (k : Nat) (target : Label) : Prop :=
  ∃ e, Mem.loadInt m ((L ".LJTI0_0").toBitVec + BitVec.ofNat 64 k * BitVec.ofNat 64 4) 4
      = some e
    ∧ (BitVec.ofInt 32 e).signExtend 64 + (L ".LJTI0_0").toBitVec = (L target).toBitVec

/-- The table, as the loader leaves it in memory. -/
def JumpTable (m : DataMem) : Prop :=
  Entry m 0 ".Lcase0" ∧ Entry m 1 ".Lcase1" ∧ Entry m 2 ".Lcase2"

/-- The argument. -/
abbrev arg (t : MachineData) : BitVec 32 := (t.regs.get64 .rdi).setWidth 32

def SelSpec : Prop :=
  cenv.ProcSpec (L "sel") (α := Unit)
    (fun _ ra t => t.retAddr = some ra ∧ JumpTable t.dmem)
    (fun _ _ t s => s.regs.get64 .rsp = t.regs.get64 .rsp + 8 ∧ s.dmem = t.dmem
      ∧ s.regs.get64 .rax = (selFn (arg t)).setWidth 64)

/-- What every case block may assume: the stack and memory as on entry. -/
abbrev AtCase (ra : Int64) (t₀ s : MachineData) : Prop :=
  s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.dmem = t₀.dmem ∧ t₀.retAddr = some ra

abbrev sel_table (ra : Int64) (t₀ : MachineData) : Label → MachineData → Prop
  | "sel", s => s = t₀ ∧ t₀.retAddr = some ra ∧ JumpTable t₀.dmem
  | ".Lcase0", s => arg t₀ = 0 ∧ AtCase ra t₀ s
  | ".Lcase1", s => arg t₀ = 1 ∧ AtCase ra t₀ s
  | ".Lcase2", s => arg t₀ = 2 ∧ AtCase ra t₀ s
  | ".Ldefault", s => 2 < arg t₀ ∧ AtCase ra t₀ s
  | _, _ => False

theorem sel_spec (hpl : Program.PlacedIn sel_body) : SelSpec := by
  refine Kraken.Executable.ProcSpec.of_cfg (p := sel_body) (fun _ ra t₀ => sel_table ra t₀)
    (hblocks := ?_) (hpre := ?_)
  · intro _ ra t₀
    cfg_cases [sel_body]
    · -- dispatch. `grind` takes the `ja` to `.Ldefault` (`CondCode.interp_a_sub`
      -- reads the flags as `2 < x`); what is left is the jump through the table.
      vcgen
      all_goals (try grind)
      -- in range: the entry at `x` is readable, and it leads to `.Lcase_x`
      · rename_i s hT hja
        obtain ⟨⟨hs, hra, ⟨e0, h0l, h0t⟩, ⟨e1, h1l, h1t⟩, ⟨e2, h2l, h2t⟩⟩, -⟩ := hT
        subst s
        have hle : (arg t₀).toNat ≤ 2 := by grind
        have hx : arg t₀ = 0 ∨ arg t₀ = 1 ∨ arg t₀ = 2 := by bv_omega
        rcases hx with hx | hx | hx <;> simp at hx h0l h1l h2l ⊢ <;> simp [hx, h0l, h1l, h2l]
      · rename_i s hT hja v hv
        obtain ⟨⟨hs, hra, ⟨e0, h0l, h0t⟩, ⟨e1, h1l, h1t⟩, ⟨e2, h2l, h2t⟩⟩, -⟩ := hT
        subst s
        have hle : (arg t₀).toNat ≤ 2 := by grind
        have hx : arg t₀ = 0 ∨ arg t₀ = 1 ∨ arg t₀ = 2 := by bv_omega
        rcases hx with hx | hx | hx <;> simp at hx h0l h1l h2l hv ⊢ <;> simp [hx] at hv ⊢
        · rw [target_eq h0l hv h0t]; grind
        · rw [target_eq h1l hv h1t]; grind
        · rw [target_eq h2l hv h2t]; grind
    -- the cases and the default: set `eax`, return
    all_goals vcgen
    all_goals call_simp
    all_goals grind [selFn, BitVec.xor_self]
  · rintro _ ra t ⟨hra, htab⟩
    exact ⟨rfl, hra, htab⟩

end Kraken.Examples.JumpTable
