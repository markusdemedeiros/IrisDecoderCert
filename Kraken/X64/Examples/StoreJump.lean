import Kraken.X64.Parser
import Kraken.MachineWP

/-!
# A jump through an address the program stores itself

```
store_jump:                          ; returns 42
    lea     rax, [rip + .Ltarget]
    mov     qword ptr [rsp - 8], rax ; red-zone slot
    jmp     qword ptr [rsp - 8]
.Lbad:
    xor     eax, eax
    ret
.Ltarget:
    mov     eax, 42
    ret
```

`store_jump_spec`: entered with a return address on the stack and the slot
below it writable, `store_jump` returns 42 with the stack popped. The memory
is as on entry except the slot, which holds `.Ltarget`'s address.

## Findings

The label address has to survive a round trip through memory: from the
register as a `BitVec`, stored as an `Int` (`toInt`) in 8 bytes, loaded back as
an `Int`, and decoded to the jump target as an `Int64`. The lemmas that read
back a pushed return address (`Mem.loadInt_storeInt_64`,
`Int64.ofBitVec_ofBytes_toBytes`) cover this, so the round trip needs no new
reasoning. One wrinkle: those lemmas spell the width `Width.W64.bytes`, while
the store and jump rules write `8`. So the proof restates them at `8`
(`hrt`, `hdec`) and rewrites with them by hand instead of leaving it to
`grind`. Likewise, the displacement arrives as `rsp + (-8).toBitVec` (`hm8`).

The new part is the frame: the store must not disturb the return address
that `ret` reads at `[rsp]`, 8 bytes above the slot. The memory model's lemmas
spoke only of loads at the address of the last store. The separation-logic
rules (`SepSpecs`) get disjointness from their frames, but the rules used
here do not have frames. `Mem.loadInt_storeInt_of_above` (in `Mem.lean`) fills
the gap: a load that starts at least `n` bytes above an `n`-byte store, without
wrapping around, reads what was there before. For `rsp` and `rsp - 8`,
`bv_omega` discharges both side conditions.

The precondition asks that the slot be mapped, as the store rule requires,
and the postcondition gives the memory exactly: `t.dmem` with the slot
overwritten.
-/

open Kraken MachineWP Std.WP Lean.Order

namespace Kraken.Examples.StoreJump

def store_jump_body : Program := parse("
store_jump:
  leaq .Ltarget(%rip), %rax
  movq %rax, -8(%rsp)
  jmp *-8(%rsp)
.Lbad:
  xorl %eax, %eax
  ret
.Ltarget:
  movl $42, %eax
  ret
")

variable [CodeEnv]

/-- The address of a label in the ambient code. -/
local macro "L" : term => `((_root_.Executable.labels cenv).label)

/-- The slot below the return address. -/
abbrev slot (t : MachineData) : BitVec 64 := t.regs.get64 .rsp - 8

/-- The memory after the store: the slot holds `.Ltarget`'s address. -/
abbrev stored (t : MachineData) : DataMem :=
  Mem.storeInt t.dmem (slot t) 8 (L ".Ltarget").toBitVec.toInt

def StoreJumpSpec : Prop :=
  cenv.ProcSpec (L "store_jump") (α := Unit)
    (fun _ ra t => t.retAddr = some ra ∧ (Mem.loadInt t.dmem (slot t) 8).isSome)
    (fun _ _ t s => s.regs.get64 .rsp = t.regs.get64 .rsp + 8 ∧ s.dmem = stored t
      ∧ s.regs.get64 .rax = 42)

/-- The store leaves the return address alone: it is 8 bytes below it. -/
theorem retAddr_stored (t : MachineData) (s : MachineData)
    (hrsp : s.regs.get64 .rsp = t.regs.get64 .rsp) (hmem : s.dmem = stored t) :
    s.retAddr = t.retAddr := by
  rw [MachineData.retAddr_eq, MachineData.retAddr_eq, hrsp, hmem, stored,
    Mem.loadInt_storeInt_of_above _ _ _ 8 _ _ (by simp; bv_omega) (by simp; bv_omega)]

abbrev store_jump_table (ra : Int64) (t₀ : MachineData) : Label → MachineData → Prop
  | "store_jump", s => s = t₀ ∧ t₀.retAddr = some ra ∧ (Mem.loadInt t₀.dmem (slot t₀) 8).isSome
  | ".Ltarget", s => s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.dmem = stored t₀
      ∧ s.retAddr = some ra
  | _, _ => False

theorem store_jump_spec (hpl : Program.PlacedIn store_jump_body) : StoreJumpSpec := by
  -- the displacement, and the address's round trip through the slot
  have hm8 : ∀ x : BitVec 64, x + (-8 : Int64).toBitVec = x - 8 := by
    intro x; simp; bv_omega
  have hrt : ∀ (m : DataMem) (a : BitVec 64) (l : Int64),
      (m.storeInt a 8 l.toBitVec.toInt).loadInt a 8
        = some (Int.ofBytes (Int.toBytes 8 l.toBitVec.toInt)) :=
    fun m a _ => Mem.loadInt_storeInt_64 m a _
  have hdec : ∀ l : Int64,
      Int64.ofBitVec (BitVec.ofInt 64 (Int.ofBytes (Int.toBytes 8 l.toBitVec.toInt))) = l :=
    Int64.ofBitVec_ofBytes_toBytes
  refine Kraken.Executable.ProcSpec.of_cfg (p := store_jump_body)
    (fun _ ra t₀ => store_jump_table ra t₀) (hblocks := ?_) (hpre := ?_)
  · intro _ ra t₀
    cfg_cases [store_jump_body]
    · -- the store and the jump through it
      vcgen
      all_goals call_simp
      all_goals simp only [hm8, hrt, Option.isSome_some, Option.some.injEq] at *
      · grind
      · -- the load reads back `.Ltarget`'s address; the return address is intact
        rename_i s v hpre hv
        obtain ⟨⟨rfl, hra, -⟩, h0⟩ := hpre
        subst hv
        rw [hdec]
        left
        apply Table.ofLabels_at
        refine ⟨rfl, ⟨?_, rfl, ?_⟩, ?_⟩
        · simp
        · rw [retAddr_stored s _ (by simp) rfl, hra]
        · grind
    · -- `.Lbad` is not reached
      vcgen
      all_goals simp_all
    · -- `.Ltarget`
      vcgen
      all_goals call_simp
      all_goals grind
  · rintro _ ra t ⟨hra, hslot⟩
    exact ⟨rfl, hra, hslot⟩

end Kraken.Examples.StoreJump
