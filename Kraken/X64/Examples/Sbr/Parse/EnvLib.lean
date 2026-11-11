import Kraken.X64.Parser
import Kraken.MachineWP
import Kraken.Rules.IntMisc
import Kraken.Rules.CallFrame
import Kraken.Rules.CfgList
import Kraken.Rules.LeafLemmas
import Kraken.Rules.FrameLemmas
import Kraken.Rules.HelperLemmas
import Kraken.Rules.SepStep

/-!
# Helpers for the `read_sbr_envelope` proof

* Havoc rules for the bit reader's intermediate values (as in the `read_sbr_grid` proof): the
  register gets any 64-bit value and the flags any status. Passed to `vcgen` explicitly.
* `shr_cl32_lo`: `shr %cl, %r32` with the low 32 bits of the result kept (the Huffman walk adds
  them to a table offset) and the upper bits forgotten.
-/

open Kraken MachineWP Std.WP Lean.Order Mem

namespace Kraken.Examples.Sbr.Env

section Havoc

variable [CodeEnv] {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}
  {p : Program}

omit [CodeEnv] in
theorem regs_set_get (rs : Reg64s) (r : Reg64) : rs.set64 r (rs.get64 r) = rs := by
  cases rs; cases r <;> rfl

/-- `bswap %r32`, value forgotten. -/
theorem bswap32_havoc (asz : Width) (r : Reg64) :
    ⦃ fun s => ∀ v : BitVec 64, ∀ st : StatusFlags,
        WP.wp p Q E { s with regs := s.regs.set64 r v, status := st } ⦄
      (Directive.instr (.regular asz .W32 (.bswap (.low r .W32))) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    rw [after_instr hseg]
    refine step_here hseg (Or.inl ?_)
    simp only [Directive.interp, Instr.interp, Operation.interp,
      MachineData.setReg, Reg64s.set_low32, Effects.All]
    exact h _ s.status _ hpl'

/-- `shl %cl, %r32`, value forgotten. -/
theorem shl_cl32_havoc (asz : Width) (r : Reg64) :
    ⦃ fun s => ∀ v : BitVec 64, ∀ st : StatusFlags,
        WP.wp p Q E { s with regs := s.regs.set64 r v, status := st } ⦄
      (Directive.instr (.regular asz .W32 (.shl (.reg (.low r .W32)) .cl)) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s hs => (MachineWP.shl_reg_cl_w32_spec (p := p) (Q := Q) (E := E) asz r).le_wp s
    (fun cf af of => by
      split
      · have h := hs (s.regs.get64 r) s.status
        rw [regs_set_get] at h; exact h
      · exact hs _ _)

/-- `shr %cl, %r32`, value forgotten. -/
theorem shr_cl32_havoc (asz : Width) (r : Reg64) :
    ⦃ fun s => ∀ v : BitVec 64, ∀ st : StatusFlags,
        WP.wp p Q E { s with regs := s.regs.set64 r v, status := st } ⦄
      (Directive.instr (.regular asz .W32 (.shr (.reg (.low r .W32)) .cl)) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s hs => (MachineWP.shr_reg_cl_w32_spec (p := p) (Q := Q) (E := E) asz r).le_wp s
    (fun cf af of => by
      split
      · have h := hs (s.regs.get64 r) s.status
        rw [regs_set_get] at h; exact h
      · exact hs _ _)

/-- `shr %cl, %r32`: the low 32 bits are the shifted value (count `%cl` mod 32); the upper
bits and the flags are forgotten. -/
theorem shr_cl32_lo (asz : Width) (r : Reg64) :
    ⦃ fun s => ∀ v : BitVec 64, ∀ st : StatusFlags,
        v.setWidth 32 = ((s.regs.get64 r).setWidth 32).ushiftRight ((s.regs.get64 .rcx).toNat % 256 % 32) →
        WP.wp p Q E { s with regs := s.regs.set64 r v, status := st } ⦄
      (Directive.instr (.regular asz .W32 (.shr (.reg (.low r .W32)) .cl)) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s hs => (MachineWP.shr_reg_cl_w32_spec (p := p) (Q := Q) (E := E) asz r).le_wp s
    (fun cf af of => by
      split
      · rename_i h0
        have h := hs (s.regs.get64 r) s.status (by rw [h0]; simp)
        rw [regs_set_get] at h; exact h
      · exact hs _ _ (by
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight]
          have := ((s.regs.get64 r).setWidth 32).isLt
          rw [Nat.mod_eq_of_lt (by
            have : (BitVec.setWidth 32 (s.regs.get64 r)).toNat >>> ((s.regs.get64 .rcx).toNat % 256 % 32)
                ≤ (BitVec.setWidth 32 (s.regs.get64 r)).toNat := Nat.shiftRight_le _ _
            simp only [BitVec.toNat_setWidth] at this ⊢; omega)]
          rw [Nat.mod_eq_of_lt (by
            have : (BitVec.setWidth 32 (s.regs.get64 r)).toNat >>> ((s.regs.get64 .rcx).toNat % 256 % 32)
                ≤ (BitVec.setWidth 32 (s.regs.get64 r)).toNat := Nat.shiftRight_le _ _
            simp only [BitVec.toNat_setWidth] at this ⊢; omega)]))

/-- `inc %r32`, value and flags forgotten (the `delta` of `read_sbr_envelope`, stored to a raw
frame slot). -/
theorem inc32_havoc (asz : Width) (r : Reg64) :
    ⦃ fun s => ∀ v : BitVec 64, ∀ st : StatusFlags,
        WP.wp p Q E { s with regs := s.regs.set64 r v, status := st } ⦄
      (Directive.instr (.regular asz .W32 (.inc (.reg (.low r .W32)))) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    rw [after_instr hseg]
    refine step_here hseg (Or.inl ?_)
    simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp,
      MachineData.set, MachineData.setReg, Reg64s.set_low32, Effects.All]
    exact h _ _ _ hpl'

end Havoc

/-! ## Flags -/

theorem z_sub_iff {w : Nat} (a b : BitVec w) (f : StatusFlags.from_result.Remaining) :
    CondCode.z.interp (StatusFlags.from_result (a - b) f) = true ↔ a = b := by
  rw [CondCode.interp_z, StatusFlags.zf_from_result]
  simp only [beq_iff_eq, BitVec.zero_eq]
  constructor
  · intro h; have := congrArg (· + b) h
    simp only [BitVec.sub_add_cancel, BitVec.zero_add] at this; exact this
  · intro h; subst h; simp

theorem z_and_iff {w : Nat} (a : BitVec w) (f : StatusFlags.from_result.Remaining) :
    CondCode.z.interp (StatusFlags.from_result (a &&& a) f) = true ↔ a = 0#w := by
  rw [CondCode.interp_z, StatusFlags.zf_from_result]
  simp [BitVec.and_self]

theorem c_sub {w : Nat} (a b : BitVec w) (f : StatusFlags.from_result.Remaining)
    (hf : f.cf = ((a - b).unsigned != a.unsigned - b.unsigned)) :
    CondCode.c.interp (StatusFlags.from_result (a - b) f) = decide (a.toNat < b.toNat) := by
  rw [CondCode.interp_c, StatusFlags.cf_from_result, hf]
  have ⟨h₁, h₂⟩ := BitVec.toNat_sub_cases a b
  have ha := a.isLt
  have hb := b.isLt
  rw [BitVec.unsigned_eq, BitVec.unsigned_eq, BitVec.unsigned_eq]
  by_cases h : b.toNat ≤ a.toNat
  · rw [h₁ h]
    have : ¬ a.toNat < b.toNat := by omega
    simp only [this, decide_false, bne_eq_false_iff_eq]
    omega
  · rw [h₂ (by omega)]
    have : a.toNat < b.toNat := by omega
    simp only [this, decide_true, bne_iff_ne, ne_eq]
    omega

end Kraken.Examples.Sbr.Env
