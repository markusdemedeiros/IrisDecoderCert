/-
The rewrite set `vcgen simplifying_assumptions` normalizes each state literal
with as it is produced, registered as `Sym.simp` theorems.

The specs of `Kraken/Specs.lean` leave a program's state chain as nested record
literals. `Sym.Simp` expands each state exactly once as it traverses the goal
bottom-up, caching by pointer, and collapses the value on the spot with these
rules; `kfold` reuses the same set on the finished verification condition.
-/
import Lean
import Kraken.Specs

open Lean Meta Sym Sym.Simp

namespace Kraken.Fold

/-- Reading the register just written, with no condition to discharge. -/
theorem get64_set64_self (s : Reg64s) (r : Reg64) (v : BitVec 64) :
    (s.set64 r v).get64 r = v := by
  cases r <;> simp [Reg64s.set64, Reg64s.get64]

/-- Writing a register that is written again later leaves no trace. Without
this the value of a state's register file is a write chain as long as the
program, and every read has to look through all of it. -/
theorem set64_set64_self (s : Reg64s) (r : Reg64) (v w : BitVec 64) :
    (s.set64 r v).set64 r w = s.set64 r w := by
  cases r <;> simp [Reg64s.set64]

/-- Reassociation, so a chain over a symbolic start presents adjacent literals
to `evalGround`. -/
theorem add_assoc_rev {w : Nat} (a b c : BitVec w) : a + (b + c) = a + b + c :=
  (BitVec.add_assoc a b c).symm

/-- The state of the segment weakest precondition is a `MachineState` pair;
its projections reduce like the record projections. -/
theorem fst_mk {α β} (a : α) (b : β) : (Prod.mk a b).1 = a := rfl
theorem snd_mk {α β} (a : α) (b : β) : (Prod.mk a b).2 = b := rfl

/-- The rewrite lemmas the chain's values reduce with: literal normalization,
register read-over-write, the record projections that turn a read of a state
literal back into the component it was built from, and flag reduction. Ground
arithmetic is left to `evalGround`, conditions to `simpControl` and
`reduceCtorEq`. -/
def lemmaNames : Array Name := #[
  ``Int64.toBitVec_ofNat, ``BitVec.ofNat_eq_ofNat, ``BitVec.setWidth_eq,
  ``get64_set64_self, ``Reg64s.get64_set64, ``set64_set64_self,
  ``Reg64s.rax_set64, ``Reg64s.rbx_set64, ``Reg64s.rcx_set64, ``Reg64s.rdx_set64,
  ``Reg64s.rsi_set64, ``Reg64s.rdi_set64, ``Reg64s.rsp_set64, ``Reg64s.rbp_set64,
  ``Reg64s.r8_set64, ``Reg64s.r9_set64, ``Reg64s.r10_set64, ``Reg64s.r11_set64,
  ``Reg64s.r12_set64, ``Reg64s.r13_set64, ``Reg64s.r14_set64, ``Reg64s.r15_set64,
  ``MachineData.regs_mk, ``MachineData.zmms_mk, ``MachineData.status_mk, ``MachineData.dmem_mk,
  ``fst_mk, ``snd_mk,
  ``Sys.machine_mk, ``Sys.device_mk,
  ``StatusFlags.cf_from_result, ``StatusFlags.from_result.Remaining.cf_mk,
  ``BitVec.add_zero, ``BitVec.unsigned_eq, ``BitVec.toNat_ofNat,
  ``Nat.zero_mod, ``Int.add_zero, ``Int.cast_ofNat_Int, ``bne_self_eq_false, ``Bool.toNat_false,
  ``_root_.ite_true, ``_root_.ite_false ]

/-- `lemmaNames` plus reassociation and the register-index comparison, the
rewrite set the state-simplification pass runs as each spec application produces
a state literal. Reassociating there brings the literal a step contributes next
to the one the chain so far carries, and `evalGround` collapses the pair, so a
component's value stays a single literal plus the symbolic start. The index
comparison turns a read-over-write condition into one `evalGround` decides,
which `kfold` does with the `reduceCtorEq` simproc instead. -/
def stateLemmaNames : Array Name := lemmaNames ++ #[``add_assoc_rev, ``Reg64.eq_eq_idx_eq]

end Kraken.Fold

-- Register the fold rewrite set as `Sym.simp` theorems, so `vcgen simplifying_assumptions`
-- normalizes the state literal a spec application leaves in the goal with the same rules
-- `kfold` uses on the finished verification condition.
open Lean Elab Command in
run_cmd liftTermElabM do
  for n in Kraken.Fold.stateLemmaNames do
    Sym.Simp.addSymSimpTheorem Sym.Simp.symSimpExtension n .global
  Sym.Simp.addSymSimpDecl Sym.Simp.symSimpExtension ``Reg64.idx .global
