import Kraken.X64.Parser
import Kraken.MachineWP
import Kraken.Rules.GenericMem
import Kraken.Rules.PackedSse
import Kraken.Rules.AvxExtra
import Kraken.Rules.LeafLemmas
import Kraken.X64.Examples.Sbr.Spec

/-!
# Shared pieces of the `float_dsp` leaf proofs

The `AVFloatDSPContext` routines `ff_sbr_apply` reaches (`vector_fmul`,
`vector_fmul_add`, `vector_fmul_reverse`, `libavutil/x86/float_dsp.asm`) share
their shape: `lea -c(,%e?x,4),%r?x` turns the float count into the byte offset of
the last chunk (a 32-bit address computation, zero-extended), then a do-while
loop walks the chunks from the end down. This file has what their proofs share:

* `lea_len_toNat`: the value of that `lea` for `16 ≤ len < 2 ^ 30`;
* `gen_store_vals`: generalizes the values a block stores and the vector
  register file it leaves. Memory safety does not depend on them, and the float
  terms (`packedBinOp f32mul …` over nested `setLegacy`) make `grind` run out of
  memory (measured: 12 GB on `ff_vector_fmul_sse` without it);
* `fdsp_block`: the proof of a work block (`vcgen`, then `grind` with 40 case
  splits, after normalising the index operands);
* `Rest`, the caller's memory behind a footprint, a `def` so that `grind`
  moves it whole (as in `NegOdd64.lean`), with `need` bytes of reservation.

The work blocks are cut so that no load follows a store in the same block (a
free label between the store pairs): the loads of the next block then read the
memory of the block's precondition, not a chain of `storeInt`s.
-/

open Kraken
open Kraken.SysV
open Mem

namespace Kraken.Examples.Sbr.FloatDsp

/-- `lea -c(,%e?x,4),%r?x` (`k` the sign-extended `-c`): `4 len - c`, for a
`len` (the low 32 bits of `x`) that is a positive multiple of 16 below `2 ^ 30`
and `0 < c ≤ 64`. -/
theorem lea_len_toNat (x : BitVec 64) (k : BitVec 32) (c : Nat)
    (hk : k = BitVec.ofNat 32 (2 ^ 32 - c)) (hc0 : 0 < c) (hc : c ≤ 64)
    (h0 : x.toNat % 2 ^ 32 % 16 = 0) (h1 : 1 ≤ x.toNat % 2 ^ 32)
    (h2 : x.toNat % 2 ^ 32 < 2 ^ 30) :
    (BitVec.setWidth 64 (x.setWidth 32 * 4#32 + k)).toNat = 4 * (x.toNat % 2 ^ 32) - c := by
  subst hk
  generalize hn : x.toNat % 2 ^ 32 = n at *
  have hx : (x.setWidth 32).toNat = n := by rw [BitVec.toNat_setWidth]; exact hn
  rw [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_mul, hx]
  have e1 : (4#32).toNat = 4 := rfl
  have e2 : (BitVec.ofNat 32 (2 ^ 32 - c)).toNat = 2 ^ 32 - c := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  rw [e1, e2]
  omega

open Lean Meta Elab Tactic in
/-- Generalize, in the goal, the values stored by `Mem.storeInt` and the vector
register file of a machine state (`MachineData.mk _ z _ _` with `z` a
`setLegacy`/`set` chain). -/
elab "gen_store_vals" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let vs ← IO.mkRef (#[] : Array Expr)
  forEachExpr t fun e => do
    if e.isAppOfArity ``Mem.storeInt 5 then
      let v := e.appArg!
      unless v.isFVar do
        vs.modify fun a => if a.contains v then a else a.push v
    if e.isAppOfArity ``MachineData.mk 4 then
      let z := e.getArg! 1
      if z.isAppOf ``RegZmms.setLegacy || z.isAppOf ``RegZmms.set then
        vs.modify fun a => if a.contains z then a else a.push z
  let a ← vs.get
  unless a.isEmpty do
    let (_, g') ← g.generalize (a.map fun v => ({ expr := v } : GeneralizeArg))
    replaceMainGoal [g']

/-- A work block of a `float_dsp` loop. -/
macro "fdsp_block" : tactic =>
  `(tactic| (
    vcgen
    all_goals dsimp only at *
    all_goals gen_store_vals
    all_goals simp only [AddrIndex.offset64_scale1] at *
    all_goals grind (splits := 40)))

variable [CodeEnv]

/-- The caller's side of memory behind the footprint: the return address, the
reservation of `need` bytes and `R`. -/
def Rest (need : Nat) (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) : Mem 64 → Prop :=
  RetCell ra (t₀.regs.get64 .rsp) ⋆ (Reserve need (t₀.regs.get64 .rsp) ⋆ R)

/-- What the exit block leaves: `CallPost` with the footprint `F t₀` in front. -/
abbrev Post' (F : MachineData → Mem 64 → Prop) (need : Nat) (R : Mem 64 → Prop) (_ra : Int64)
    (t₀ s : MachineData) : Prop :=
  s.regs.get64 .rsp = t₀.regs.get64 .rsp + 8
  ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp ∧ SavedRegs t₀ s
  ∧ (s.dmem =⋆ F t₀ ⋆ (8 ?@ (t₀.regs.get64 .rsp)
      ⋆ (Reserve need (t₀.regs.get64 .rsp) ⋆ R)))

end Kraken.Examples.Sbr.FloatDsp
