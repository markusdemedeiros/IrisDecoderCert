import Kraken.MachineWP
import Kraken.Specs
import Kraken.Rules.GenericMem
import Kraken.Rules.PackedSse

/-!
# VEX scalar-float rules

`@[spec low]` rules for the VEX scalar single/double forms, the conversions
and the `vmovd`/`vmovq` moves between general-purpose and xmm registers.

Each instruction whose source is a register or memory gets a register rule and
a memory rule. The memory rule is stated once over the operand
`⟨some (.reg b), idx, .int64 d⟩`, as in `GenericMem.lean`; the forms that
compiled code applies to constants also get a `sym(%rip)` rule, and a
`sym+o(%rip)` twin (`_rip_off_spec`).

A scalar `m32`/`m64` operand goes through the general-purpose
`MachineData.load`/`store` at 32 or 64 bits (`AvxRegOrMem.interpLow`): there
is no alignment check. The memory side condition is that the 4 or 8 bytes at
the address be present in the data memory (`Mem.loadInt … = some _`), for a
load and for a store alike.

Results are stated exactly. A register destination gets the operation's
low element, the rest of bits 127..0 from `src1`, and the bits above 127
cleared, which is what `RegZmms.set` does. `vucomiss`/`vucomisd` set the flags
`StatusFlags.ofFCmp`; the field lemmas below and `CondCode.interp_p`/`_np`
let a following `jcc` reduce to the three comparison outcomes.
`RegZmms.get_set_xmm_same`/`_ne` read an xmm register back over a write.
-/

open Kraken MachineWP Std.WP Lean.Order

/-! ## Flags of a floating-point compare -/

@[simp] theorem StatusFlags.zf_ofFCmp (c : Bool × Bool × Bool) :
    (StatusFlags.ofFCmp c).zf = (c.1 || c.2.2) := rfl
@[simp] theorem StatusFlags.pf_ofFCmp (c : Bool × Bool × Bool) :
    (StatusFlags.ofFCmp c).pf = c.1 := rfl
@[simp] theorem StatusFlags.cf_ofFCmp (c : Bool × Bool × Bool) :
    (StatusFlags.ofFCmp c).cf = (c.1 || c.2.1) := rfl
@[simp] theorem StatusFlags.sf_ofFCmp (c : Bool × Bool × Bool) :
    (StatusFlags.ofFCmp c).sf = false := rfl
@[simp] theorem StatusFlags.of_ofFCmp (c : Bool × Bool × Bool) :
    (StatusFlags.ofFCmp c).of = false := rfl

@[simp] theorem CondCode.interp_p (s : StatusFlags) :
    CondCode.p.interp s = s.pf := rfl
@[simp] theorem CondCode.interp_np (s : StatusFlags) :
    CondCode.np.interp s = !s.pf := rfl

/-! The `grind` attributes of this file are scoped: `open scoped
Kraken.Rules.ScalarFloat.FCmp` (the flags of a float compare, `jp`/`jnp`) and
`Kraken.Rules.ScalarFloat.Xmm` (xmm reads over VEX writes). -/
namespace Kraken.Rules.ScalarFloat.FCmp
attribute [scoped grind =] StatusFlags.zf_ofFCmp StatusFlags.pf_ofFCmp StatusFlags.cf_ofFCmp
  StatusFlags.sf_ofFCmp StatusFlags.of_ofFCmp CondCode.interp_p CondCode.interp_np
end Kraken.Rules.ScalarFloat.FCmp

/-! ## Reads of xmm registers over VEX writes -/

theorem RegZmms.get512_set512_same (s : RegZmms) (r : RegMm) (v : AvxWidth.W512.type) :
    (s.set512 r v).get512 r = v := by
  cases r <;> rfl

theorem RegZmms.get512_set512_ne (s : RegZmms) (r r' : RegMm) (v : AvxWidth.W512.type)
    (h : r ≠ r') : (s.set512 r v).get512 r' = s.get512 r' := by
  cases r <;> cases r' <;> first | rfl | exact absurd rfl h

set_option exponentiation.threshold 512 in
/-- A VEX write to an xmm register reads back as written. -/
@[simp] theorem RegZmms.get_set_xmm_same (s : RegZmms) (x : RegMm) (v : BitVec 128) :
    (s.set (.xmm x) v).get (.xmm x) = v := by
  simp only [RegZmms.get, RegZmms.set, AvxReg.base]
  rw [RegZmms.get512_set512_same]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.take, BitVec.extractLsb'_toNat, AvxWidth.bits]
  exact v.isLt

/-- A write to one xmm register leaves the others. -/
@[simp] theorem RegZmms.get_set_xmm_ne (s : RegZmms) (x y : RegMm) (v : BitVec 128)
    (h : x ≠ y) : (s.set (.xmm x) v).get (.xmm y) = s.get (.xmm y) := by
  simp only [RegZmms.get, RegZmms.set, AvxReg.base]
  rw [RegZmms.get512_set512_ne _ _ _ _ h]

namespace Kraken.Rules.ScalarFloat.Xmm
attribute [scoped grind =] RegZmms.get_set_xmm_same RegZmms.get_set_xmm_ne
end Kraken.Rules.ScalarFloat.Xmm

open scoped Kraken.Rules.ScalarFloat.FCmp Kraken.Rules.ScalarFloat.Xmm

section Specs

variable [CodeEnv] {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}
  {p : Program}

local macro "wp_step" : tactic =>
  `(tactic| simp only [Executable.stepAt, Directive.interp, Instr.interp,
      Operation.interp, AvxOperation.interp, Operand.interp, RegOrMem.interp,
      AvxRegOrMem.interp, RelRegOrMem.interp, ConstExpr.interp,
      MachineData.set, MachineData.setReg, MachineData.setAvxLegacy, MachineData.setAvxLegacyReg,
      MachineData.setAvx, MachineData.setAvxReg,
      Reg64s.get_low64, Reg64s.set_low64, Effects.All, or_false, false_or])

/-- The proof of a register rule: one cell, reduced. -/
local macro "reg_rule" : tactic =>
  `(tactic| exact fallthrough_spec (fun s rng P hP => by
      wp_step
      try simp only [AvxRegOrMem.interpLow, Reg64s.get_low32, Reg64s.set_low32]
      exact hP))

/-- The proof of a memory rule (load or store): the bytes are present, so the
access takes its `some` branch. -/
local macro "mem_rule" : tactic =>
  `(tactic| (
    refine Triple.intro fun s h => ?_
    simp only [meet_prop_eq_and] at h
    obtain ⟨hsome, hk⟩ := h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    rw [after_instr hseg]
    refine step_here hseg (Or.inl ?_)
    wp_step
    simp only [AvxRegOrMem.interpLow, MachineData.load, MachineData.store,
      AddrExpr.zeroExtend_interp_base_idx_disp, AddrExpr.zeroExtend_interp_rip_label,
      AddrExpr.zeroExtend_interp_rip_label_add,
      Width.bytes, hv, Effects.All]
    first
      | exact hk v hv _ hpl'
      | exact hk _ hpl'))

/-- The address of a label in the ambient code. -/
local macro "L" : term => `((_root_.Executable.labels cenv).label)

/-! ## vmovss / vmovsd -/

/-- `vmovss d(%b,%i,s), %xmm`: the 4 bytes must be present; the register gets
them zero-extended. -/
@[spec low] theorem MachineWP.vmovss_load_mem_spec (x : AvxReg .W128) (b : Reg64)
    (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 4).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 4 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set x ((BitVec.ofInt 32 v).zeroExtend 128) }) ⦄
      (Directive.instr (.avx .W64 .W128
          (.vmovssMem (.avx x) (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_rule

/-- `vmovss sym(%rip), %xmm`. -/
@[spec low] theorem MachineWP.vmovss_load_rip_spec (x : AvxReg .W128) (l : Label) :
    ⦃ fun s =>
        let a := (L l).toBitVec
        ((Mem.loadInt s.dmem a 4).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 4 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set x ((BitVec.ofInt 32 v).zeroExtend 128) }) ⦄
      (Directive.instr (.avx .W64 .W128
          (.vmovssMem (.avx x) (.mem ⟨some .rip, none, .sub (.label l) .after_current_instruction⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_rule

/-- `vmovss %xmm, d(%b,%i,s)`: the 4 bytes must be present; they get the low
float of the register. -/
@[spec low] theorem MachineWP.vmovss_store_mem_spec (b : Reg64) (idx : Option AddrIndex)
    (d : Int64) (x : AvxReg .W128) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 4).isSome = true)
          ⊓ WP.wp p Q E { s with
              dmem := Mem.storeInt s.dmem a 4 ((s.zmms.get x).setWidth 32).toInt } ⦄
      (Directive.instr (.avx .W64 .W128
          (.vmovssMem (.mem ⟨some (.reg b), idx, .int64 d⟩) (.avx x))) :: p)
    ⦃ Q; E ⦄ := by mem_rule

/-- `vmovsd d(%b,%i,s), %xmm`: the 8 bytes must be present; the register gets
them zero-extended. -/
@[spec low] theorem MachineWP.vmovsd_load_mem_spec (x : AvxReg .W128) (b : Reg64)
    (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 8).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 8 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set x ((BitVec.ofInt 64 v).zeroExtend 128) }) ⦄
      (Directive.instr (.avx .W64 .W128
          (.vmovsdMem (.avx x) (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_rule

/-- `vmovsd sym(%rip), %xmm`. -/
@[spec low] theorem MachineWP.vmovsd_load_rip_spec (x : AvxReg .W128) (l : Label) :
    ⦃ fun s =>
        let a := (L l).toBitVec
        ((Mem.loadInt s.dmem a 8).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 8 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set x ((BitVec.ofInt 64 v).zeroExtend 128) }) ⦄
      (Directive.instr (.avx .W64 .W128
          (.vmovsdMem (.avx x) (.mem ⟨some .rip, none, .sub (.label l) .after_current_instruction⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_rule

/-- `vmovsd %xmm, d(%b,%i,s)`: the 8 bytes must be present. -/
@[spec low] theorem MachineWP.vmovsd_store_mem_spec (b : Reg64) (idx : Option AddrIndex)
    (d : Int64) (x : AvxReg .W128) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 8).isSome = true)
          ⊓ WP.wp p Q E { s with
              dmem := Mem.storeInt s.dmem a 8 ((s.zmms.get x).setWidth 64).toInt } ⦄
      (Directive.instr (.avx .W64 .W128
          (.vmovsdMem (.mem ⟨some (.reg b), idx, .int64 d⟩) (.avx x))) :: p)
    ⦃ Q; E ⦄ := by mem_rule

/-! ### vsubss -/

/-- `vsubss %src2, %src1, %dst`: `dst := src1 - src2` on the low float. -/
@[spec low] theorem MachineWP.vsubss_reg_spec {w : AvxWidth} (asz : Width) (dst src1 src2 : AvxReg .W128) :
    ⦃ fun s =>
        WP.wp p Q E { s with zmms := (s.zmms.set dst
          ((s.zmms.get src1).extractLsb' 32 96 ++ BitVec.f32sub ((s.zmms.get src1).extractLsb' 0 32) ((s.zmms.get src2).setWidth 32))) } ⦄
      (Directive.instr (.avx asz w (.vsubss dst src1 (.avx src2))) :: p)
    ⦃ Q; E ⦄ := by reg_rule

/-- `vsubss d(%b,%i,s), %src1, %dst`: the 4 bytes must be present; `dst := src1 - src2` on the low float. -/
@[spec low] theorem MachineWP.vsubss_load_mem_spec (dst src1 : AvxReg .W128) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 4).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 4 = some v →
            WP.wp p Q E { s with zmms := (s.zmms.set dst
              ((s.zmms.get src1).extractLsb' 32 96 ++ BitVec.f32sub ((s.zmms.get src1).extractLsb' 0 32) (BitVec.ofInt 32 v))) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vsubss dst src1 (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_rule

/-! ### vmulss -/

/-- `vmulss %src2, %src1, %dst`: `dst := src1 * src2` on the low float. -/
@[spec low] theorem MachineWP.vmulss_reg_spec {w : AvxWidth} (asz : Width) (dst src1 src2 : AvxReg .W128) :
    ⦃ fun s =>
        WP.wp p Q E { s with zmms := (s.zmms.set dst
          ((s.zmms.get src1).extractLsb' 32 96 ++ BitVec.f32mul ((s.zmms.get src1).extractLsb' 0 32) ((s.zmms.get src2).setWidth 32))) } ⦄
      (Directive.instr (.avx asz w (.vmulss dst src1 (.avx src2))) :: p)
    ⦃ Q; E ⦄ := by reg_rule

/-- `vmulss d(%b,%i,s), %src1, %dst`: the 4 bytes must be present; `dst := src1 * src2` on the low float. -/
@[spec low] theorem MachineWP.vmulss_load_mem_spec (dst src1 : AvxReg .W128) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 4).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 4 = some v →
            WP.wp p Q E { s with zmms := (s.zmms.set dst
              ((s.zmms.get src1).extractLsb' 32 96 ++ BitVec.f32mul ((s.zmms.get src1).extractLsb' 0 32) (BitVec.ofInt 32 v))) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vmulss dst src1 (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_rule

/-! ### vdivss -/

/-- `vdivss %src2, %src1, %dst`: `dst := src1 / src2` on the low float. -/
@[spec low] theorem MachineWP.vdivss_reg_spec {w : AvxWidth} (asz : Width) (dst src1 src2 : AvxReg .W128) :
    ⦃ fun s =>
        WP.wp p Q E { s with zmms := (s.zmms.set dst
          ((s.zmms.get src1).extractLsb' 32 96 ++ BitVec.f32div ((s.zmms.get src1).extractLsb' 0 32) ((s.zmms.get src2).setWidth 32))) } ⦄
      (Directive.instr (.avx asz w (.vdivss dst src1 (.avx src2))) :: p)
    ⦃ Q; E ⦄ := by reg_rule

/-- `vdivss d(%b,%i,s), %src1, %dst`: the 4 bytes must be present; `dst := src1 / src2` on the low float. -/
@[spec low] theorem MachineWP.vdivss_load_mem_spec (dst src1 : AvxReg .W128) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 4).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 4 = some v →
            WP.wp p Q E { s with zmms := (s.zmms.set dst
              ((s.zmms.get src1).extractLsb' 32 96 ++ BitVec.f32div ((s.zmms.get src1).extractLsb' 0 32) (BitVec.ofInt 32 v))) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vdivss dst src1 (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_rule

/-- `vdivss sym(%rip), %src1, %dst`: the 4 bytes at `sym` must be present. -/
@[spec low] theorem MachineWP.vdivss_load_rip_spec (dst src1 : AvxReg .W128) (l : Label) :
    ⦃ fun s =>
        let a := (L l).toBitVec
        ((Mem.loadInt s.dmem a 4).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 4 = some v →
            WP.wp p Q E { s with zmms := (s.zmms.set dst
              ((s.zmms.get src1).extractLsb' 32 96 ++ BitVec.f32div ((s.zmms.get src1).extractLsb' 0 32) (BitVec.ofInt 32 v))) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vdivss dst src1 (.mem ⟨some .rip, none, .sub (.label l) .after_current_instruction⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_rule

/-- `vdivss sym+o(%rip), %src1, %dst`: the 4 bytes at `sym+o` must be present. -/
@[spec low] theorem MachineWP.vdivss_load_rip_off_spec (dst src1 : AvxReg .W128) (l : Label) (o : Int64) :
    ⦃ fun s =>
        let a := (L l).toBitVec + o.toBitVec
        ((Mem.loadInt s.dmem a 4).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 4 = some v →
            WP.wp p Q E { s with zmms := (s.zmms.set dst
              ((s.zmms.get src1).extractLsb' 32 96 ++ BitVec.f32div ((s.zmms.get src1).extractLsb' 0 32) (BitVec.ofInt 32 v))) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vdivss dst src1 (.mem ⟨some .rip, none, .sub (.add (.label l) (.int64 o)) .after_current_instruction⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_rule

/-! ### vminss -/

/-- `vminss %src2, %src1, %dst`: `dst := min src1 src2` on the low float. -/
@[spec low] theorem MachineWP.vminss_reg_spec {w : AvxWidth} (asz : Width) (dst src1 src2 : AvxReg .W128) :
    ⦃ fun s =>
        WP.wp p Q E { s with zmms := (s.zmms.set dst
          ((s.zmms.get src1).extractLsb' 32 96 ++ BitVec.f32min ((s.zmms.get src1).extractLsb' 0 32) ((s.zmms.get src2).setWidth 32))) } ⦄
      (Directive.instr (.avx asz w (.vminss dst src1 (.avx src2))) :: p)
    ⦃ Q; E ⦄ := by reg_rule

/-- `vminss d(%b,%i,s), %src1, %dst`: the 4 bytes must be present; `dst := min src1 src2` on the low float. -/
@[spec low] theorem MachineWP.vminss_load_mem_spec (dst src1 : AvxReg .W128) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 4).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 4 = some v →
            WP.wp p Q E { s with zmms := (s.zmms.set dst
              ((s.zmms.get src1).extractLsb' 32 96 ++ BitVec.f32min ((s.zmms.get src1).extractLsb' 0 32) (BitVec.ofInt 32 v))) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vminss dst src1 (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_rule

/-- `vminss sym(%rip), %src1, %dst`: the 4 bytes at `sym` must be present. -/
@[spec low] theorem MachineWP.vminss_load_rip_spec (dst src1 : AvxReg .W128) (l : Label) :
    ⦃ fun s =>
        let a := (L l).toBitVec
        ((Mem.loadInt s.dmem a 4).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 4 = some v →
            WP.wp p Q E { s with zmms := (s.zmms.set dst
              ((s.zmms.get src1).extractLsb' 32 96 ++ BitVec.f32min ((s.zmms.get src1).extractLsb' 0 32) (BitVec.ofInt 32 v))) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vminss dst src1 (.mem ⟨some .rip, none, .sub (.label l) .after_current_instruction⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_rule

/-- `vminss sym+o(%rip), %src1, %dst`: the 4 bytes at `sym+o` must be present. -/
@[spec low] theorem MachineWP.vminss_load_rip_off_spec (dst src1 : AvxReg .W128) (l : Label) (o : Int64) :
    ⦃ fun s =>
        let a := (L l).toBitVec + o.toBitVec
        ((Mem.loadInt s.dmem a 4).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 4 = some v →
            WP.wp p Q E { s with zmms := (s.zmms.set dst
              ((s.zmms.get src1).extractLsb' 32 96 ++ BitVec.f32min ((s.zmms.get src1).extractLsb' 0 32) (BitVec.ofInt 32 v))) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vminss dst src1 (.mem ⟨some .rip, none, .sub (.add (.label l) (.int64 o)) .after_current_instruction⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_rule

/-! ### vsqrtss -/

/-- `vsqrtss %src2, %src1, %dst`: `dst := sqrt src2` on the low float, the rest from `src1`. -/
@[spec low] theorem MachineWP.vsqrtss_reg_spec {w : AvxWidth} (asz : Width) (dst src1 src2 : AvxReg .W128) :
    ⦃ fun s =>
        WP.wp p Q E { s with zmms := (s.zmms.set dst
          ((s.zmms.get src1).extractLsb' 32 96 ++ BitVec.f32sqrt ((s.zmms.get src2).setWidth 32))) } ⦄
      (Directive.instr (.avx asz w (.vsqrtss dst src1 (.avx src2))) :: p)
    ⦃ Q; E ⦄ := by reg_rule

/-- `vsqrtss d(%b,%i,s), %src1, %dst`: the 4 bytes must be present; `dst := sqrt src2` on the low float, the rest from `src1`. -/
@[spec low] theorem MachineWP.vsqrtss_load_mem_spec (dst src1 : AvxReg .W128) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 4).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 4 = some v →
            WP.wp p Q E { s with zmms := (s.zmms.set dst
              ((s.zmms.get src1).extractLsb' 32 96 ++ BitVec.f32sqrt (BitVec.ofInt 32 v))) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vsqrtss dst src1 (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_rule

/-! ### vmulsd -/

/-- `vmulsd %src2, %src1, %dst`: `dst := src1 * src2` on the low double. -/
@[spec low] theorem MachineWP.vmulsd_reg_spec {w : AvxWidth} (asz : Width) (dst src1 src2 : AvxReg .W128) :
    ⦃ fun s =>
        WP.wp p Q E { s with zmms := (s.zmms.set dst
          ((s.zmms.get src1).extractLsb' 64 64 ++ BitVec.f64mul ((s.zmms.get src1).extractLsb' 0 64) ((s.zmms.get src2).setWidth 64))) } ⦄
      (Directive.instr (.avx asz w (.vmulsd dst src1 (.avx src2))) :: p)
    ⦃ Q; E ⦄ := by reg_rule

/-- `vmulsd d(%b,%i,s), %src1, %dst`: the 8 bytes must be present; `dst := src1 * src2` on the low double. -/
@[spec low] theorem MachineWP.vmulsd_load_mem_spec (dst src1 : AvxReg .W128) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 8).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 8 = some v →
            WP.wp p Q E { s with zmms := (s.zmms.set dst
              ((s.zmms.get src1).extractLsb' 64 64 ++ BitVec.f64mul ((s.zmms.get src1).extractLsb' 0 64) (BitVec.ofInt 64 v))) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vmulsd dst src1 (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_rule

/-! ### vcvtss2sd -/

/-- `vcvtss2sd %src2, %src1, %dst`: the low float of `src2` widened to the low double. -/
@[spec low] theorem MachineWP.vcvtss2sd_reg_spec {w : AvxWidth} (asz : Width) (dst src1 src2 : AvxReg .W128) :
    ⦃ fun s =>
        WP.wp p Q E { s with zmms := (s.zmms.set dst
          ((s.zmms.get src1).extractLsb' 64 64 ++ BitVec.f32to64 ((s.zmms.get src2).setWidth 32))) } ⦄
      (Directive.instr (.avx asz w (.vcvtss2sd dst src1 (.avx src2))) :: p)
    ⦃ Q; E ⦄ := by reg_rule

/-- `vcvtss2sd d(%b,%i,s), %src1, %dst`: the 4 bytes must be present; the low float of `src2` widened to the low double. -/
@[spec low] theorem MachineWP.vcvtss2sd_load_mem_spec (dst src1 : AvxReg .W128) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 4).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 4 = some v →
            WP.wp p Q E { s with zmms := (s.zmms.set dst
              ((s.zmms.get src1).extractLsb' 64 64 ++ BitVec.f32to64 (BitVec.ofInt 32 v))) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vcvtss2sd dst src1 (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_rule

/-! ### vcvtsd2ss -/

/-- `vcvtsd2ss %src2, %src1, %dst`: the low double of `src2` narrowed to the low float. -/
@[spec low] theorem MachineWP.vcvtsd2ss_reg_spec {w : AvxWidth} (asz : Width) (dst src1 src2 : AvxReg .W128) :
    ⦃ fun s =>
        WP.wp p Q E { s with zmms := (s.zmms.set dst
          ((s.zmms.get src1).extractLsb' 32 96 ++ BitVec.f64to32 ((s.zmms.get src2).setWidth 64))) } ⦄
      (Directive.instr (.avx asz w (.vcvtsd2ss dst src1 (.avx src2))) :: p)
    ⦃ Q; E ⦄ := by reg_rule

/-- `vcvtsd2ss d(%b,%i,s), %src1, %dst`: the 8 bytes must be present; the low double of `src2` narrowed to the low float. -/
@[spec low] theorem MachineWP.vcvtsd2ss_load_mem_spec (dst src1 : AvxReg .W128) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 8).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 8 = some v →
            WP.wp p Q E { s with zmms := (s.zmms.set dst
              ((s.zmms.get src1).extractLsb' 32 96 ++ BitVec.f64to32 (BitVec.ofInt 64 v))) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vcvtsd2ss dst src1 (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_rule

/-! ### vcmpss -/

/-- `vcmpss %src2, %src1, %dst`: the low element all ones if predicate `pred` holds of `src1`, `src2`, else zero. -/
@[spec low] theorem MachineWP.vcmpss_reg_spec {w : AvxWidth} (asz : Width) (pred : UInt8) (dst src1 src2 : AvxReg .W128) :
    ⦃ fun s =>
        WP.wp p Q E { s with zmms := (s.zmms.set dst
          ((s.zmms.get src1).extractLsb' 32 96 ++ (if BitVec.f32cmpPred pred ((s.zmms.get src1).extractLsb' 0 32) ((s.zmms.get src2).setWidth 32) then BitVec.allOnes 32 else 0#32))) } ⦄
      (Directive.instr (.avx asz w (.vcmpss pred dst src1 (.avx src2))) :: p)
    ⦃ Q; E ⦄ := by reg_rule

/-- `vcmpss d(%b,%i,s), %src1, %dst`: the 4 bytes must be present; the low element all ones if predicate `pred` holds of `src1`, `src2`, else zero. -/
@[spec low] theorem MachineWP.vcmpss_load_mem_spec (pred : UInt8) (dst src1 : AvxReg .W128) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 4).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 4 = some v →
            WP.wp p Q E { s with zmms := (s.zmms.set dst
              ((s.zmms.get src1).extractLsb' 32 96 ++ (if BitVec.f32cmpPred pred ((s.zmms.get src1).extractLsb' 0 32) (BitVec.ofInt 32 v) then BitVec.allOnes 32 else 0#32))) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vcmpss pred dst src1 (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_rule

/-- `vcmpss sym(%rip), %src1, %dst`: the 4 bytes at `sym` must be present. -/
@[spec low] theorem MachineWP.vcmpss_load_rip_spec (pred : UInt8) (dst src1 : AvxReg .W128) (l : Label) :
    ⦃ fun s =>
        let a := (L l).toBitVec
        ((Mem.loadInt s.dmem a 4).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 4 = some v →
            WP.wp p Q E { s with zmms := (s.zmms.set dst
              ((s.zmms.get src1).extractLsb' 32 96 ++ (if BitVec.f32cmpPred pred ((s.zmms.get src1).extractLsb' 0 32) (BitVec.ofInt 32 v) then BitVec.allOnes 32 else 0#32))) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vcmpss pred dst src1 (.mem ⟨some .rip, none, .sub (.label l) .after_current_instruction⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_rule

/-- `vcmpss sym+o(%rip), %src1, %dst`: the 4 bytes at `sym+o` must be present. -/
@[spec low] theorem MachineWP.vcmpss_load_rip_off_spec (pred : UInt8) (dst src1 : AvxReg .W128) (l : Label) (o : Int64) :
    ⦃ fun s =>
        let a := (L l).toBitVec + o.toBitVec
        ((Mem.loadInt s.dmem a 4).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 4 = some v →
            WP.wp p Q E { s with zmms := (s.zmms.set dst
              ((s.zmms.get src1).extractLsb' 32 96 ++ (if BitVec.f32cmpPred pred ((s.zmms.get src1).extractLsb' 0 32) (BitVec.ofInt 32 v) then BitVec.allOnes 32 else 0#32))) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vcmpss pred dst src1 (.mem ⟨some .rip, none, .sub (.add (.label l) (.int64 o)) .after_current_instruction⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_rule

/-! ### vaddss with a memory operand -/

/-- `vaddss d(%b,%i,s), %src1, %dst`: the 4 bytes must be present. -/
@[spec low] theorem MachineWP.vaddss_load_mem_spec (dst src1 : AvxReg .W128) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 4).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 4 = some v →
            WP.wp p Q E { s with zmms := (s.zmms.set dst
              ((s.zmms.get src1).extractLsb' 32 96 ++ BitVec.f32add ((s.zmms.get src1).extractLsb' 0 32) (BitVec.ofInt 32 v))) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vaddssMem dst src1 ⟨some (.reg b), idx, .int64 d⟩)) :: p)
    ⦃ Q; E ⦄ := by mem_rule

/-- `vaddss sym(%rip), %src1, %dst`: the 4 bytes at `sym` must be present. -/
@[spec low] theorem MachineWP.vaddss_load_rip_spec (dst src1 : AvxReg .W128) (l : Label) :
    ⦃ fun s =>
        let a := (L l).toBitVec
        ((Mem.loadInt s.dmem a 4).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 4 = some v →
            WP.wp p Q E { s with zmms := (s.zmms.set dst
              ((s.zmms.get src1).extractLsb' 32 96 ++ BitVec.f32add ((s.zmms.get src1).extractLsb' 0 32) (BitVec.ofInt 32 v))) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vaddssMem dst src1 ⟨some .rip, none, .sub (.label l) .after_current_instruction⟩)) :: p)
    ⦃ Q; E ⦄ := by mem_rule

/-- `vaddss sym+o(%rip), %src1, %dst`: the 4 bytes at `sym+o` must be present. -/
@[spec low] theorem MachineWP.vaddss_load_rip_off_spec (dst src1 : AvxReg .W128) (l : Label) (o : Int64) :
    ⦃ fun s =>
        let a := (L l).toBitVec + o.toBitVec
        ((Mem.loadInt s.dmem a 4).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 4 = some v →
            WP.wp p Q E { s with zmms := (s.zmms.set dst
              ((s.zmms.get src1).extractLsb' 32 96 ++ BitVec.f32add ((s.zmms.get src1).extractLsb' 0 32) (BitVec.ofInt 32 v))) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vaddssMem dst src1 ⟨some .rip, none, .sub (.add (.label l) (.int64 o)) .after_current_instruction⟩)) :: p)
    ⦃ Q; E ⦄ := by mem_rule

/-! ### vucomiss -/

/-- `vucomiss %src2, %src1`: the flags of the unordered compare of the low elements. -/
@[spec low] theorem MachineWP.vucomiss_reg_spec {w : AvxWidth} (asz : Width) (src1 src2 : AvxReg .W128) :
    ⦃ fun s =>
        WP.wp p Q E { s with status := (StatusFlags.ofFCmp
          (BitVec.f32cmp ((s.zmms.get src1).extractLsb' 0 32) ((s.zmms.get src2).setWidth 32))) } ⦄
      (Directive.instr (.avx asz w (.vucomiss src1 (.avx src2))) :: p)
    ⦃ Q; E ⦄ := by reg_rule

/-- `vucomiss d(%b,%i,s), %src1`: the 4 bytes must be present. -/
@[spec low] theorem MachineWP.vucomiss_load_mem_spec (src1 : AvxReg .W128) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 4).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 4 = some v →
            WP.wp p Q E { s with status := (StatusFlags.ofFCmp
              (BitVec.f32cmp ((s.zmms.get src1).extractLsb' 0 32) (BitVec.ofInt 32 v))) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vucomiss src1 (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_rule

/-! ### vucomisd -/

/-- `vucomisd %src2, %src1`: the flags of the unordered compare of the low elements. -/
@[spec low] theorem MachineWP.vucomisd_reg_spec {w : AvxWidth} (asz : Width) (src1 src2 : AvxReg .W128) :
    ⦃ fun s =>
        WP.wp p Q E { s with status := (StatusFlags.ofFCmp
          (BitVec.f64cmp ((s.zmms.get src1).extractLsb' 0 64) ((s.zmms.get src2).setWidth 64))) } ⦄
      (Directive.instr (.avx asz w (.vucomisd src1 (.avx src2))) :: p)
    ⦃ Q; E ⦄ := by reg_rule

/-- `vucomisd d(%b,%i,s), %src1`: the 8 bytes must be present. -/
@[spec low] theorem MachineWP.vucomisd_load_mem_spec (src1 : AvxReg .W128) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 8).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 8 = some v →
            WP.wp p Q E { s with status := (StatusFlags.ofFCmp
              (BitVec.f64cmp ((s.zmms.get src1).extractLsb' 0 64) (BitVec.ofInt 64 v))) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vucomisd src1 (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_rule

/-! ### vcvtsi2ss -/

/-- `vcvtsi2ss %r32, %src1, %dst`: the signed 32-bit integer rounded to the low float. -/
@[spec low] theorem MachineWP.vcvtsi2ss_reg32_spec {w : AvxWidth} (asz : Width) (dst src1 : AvxReg .W128) (r : Reg64) :
    ⦃ fun s =>
        WP.wp p Q E { s with zmms := (s.zmms.set dst
          ((s.zmms.get src1).extractLsb' 32 96 ++ BitVec.sitof32 ((s.regs.get64 r).setWidth 32))) } ⦄
      (Directive.instr (.avx asz w (.vcvtsi2ss dst src1 (RegOrMem.reg (.low r .W32)))) :: p)
    ⦃ Q; E ⦄ := by reg_rule

/-- `vcvtsi2ss %r64, %src1, %dst`: the signed 64-bit integer rounded to the low float. -/
@[spec low] theorem MachineWP.vcvtsi2ss_reg64_spec {w : AvxWidth} (asz : Width) (dst src1 : AvxReg .W128) (r : Reg64) :
    ⦃ fun s =>
        WP.wp p Q E { s with zmms := (s.zmms.set dst
          ((s.zmms.get src1).extractLsb' 32 96 ++ BitVec.sitof32 (s.regs.get64 r))) } ⦄
      (Directive.instr (.avx asz w (.vcvtsi2ss dst src1 (RegOrMem.reg (.low r .W64)))) :: p)
    ⦃ Q; E ⦄ := by reg_rule

/-- `vcvtsi2ssl d(%b,%i,s), %src1, %dst`: the 4 bytes must be present. -/
@[spec low] theorem MachineWP.vcvtsi2ss_load32_mem_spec (dst src1 : AvxReg .W128) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 4).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 4 = some v →
            WP.wp p Q E { s with zmms := (s.zmms.set dst
              ((s.zmms.get src1).extractLsb' 32 96 ++ BitVec.sitof32 (BitVec.ofInt 32 v))) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vcvtsi2ss dst src1 (RegOrMem.mem (w := .W32) ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_rule

/-! ### vcvtps2pd -/

/-- `vcvtps2pd %src, %dst`: the two low floats widened to doubles. -/
@[spec low] theorem MachineWP.vcvtps2pd_reg_spec {w : AvxWidth} (asz : Width) (dst src : AvxReg .W128) :
    ⦃ fun s =>
        WP.wp p Q E { s with zmms := (s.zmms.set dst
          (BitVec.f32to64 (((s.zmms.get src).setWidth 64).dw 1) ++ BitVec.f32to64 (((s.zmms.get src).setWidth 64).dw 0))) } ⦄
      (Directive.instr (.avx asz w (.vcvtps2pd dst (.avx src))) :: p)
    ⦃ Q; E ⦄ := by reg_rule

/-! ### vmovd -/

/-- `vmovd %r, %xmm`: the register zero-extended into the xmm register. -/
@[spec low] theorem MachineWP.vmovd_to_reg_spec {w : AvxWidth} (asz : Width) (dst : AvxReg .W128) (r : Reg64) :
    ⦃ fun s =>
        WP.wp p Q E { s with zmms := s.zmms.set dst (((s.regs.get64 r).setWidth 32).zeroExtend 128) } ⦄
      (Directive.instr (.avx asz w (.vmovdTo dst (RegOrMem.reg (.low r .W32)))) :: p)
    ⦃ Q; E ⦄ := by reg_rule

/-- `vmovd d(%b,%i,s), %xmm`: the 4 bytes must be present; they are zero-extended into the register. -/
@[spec low] theorem MachineWP.vmovd_to_load_mem_spec (dst : AvxReg .W128) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 4).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 4 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set dst ((BitVec.ofInt 32 v).zeroExtend 128) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vmovdTo dst (RegOrMem.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_rule

/-- `vmovd sym(%rip), %xmm`: the 4 bytes at `sym` must be present. -/
@[spec low] theorem MachineWP.vmovd_to_load_rip_spec (dst : AvxReg .W128) (l : Label) :
    ⦃ fun s =>
        let a := (L l).toBitVec
        ((Mem.loadInt s.dmem a 4).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 4 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set dst ((BitVec.ofInt 32 v).zeroExtend 128) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vmovdTo dst (RegOrMem.mem ⟨some .rip, none, .sub (.label l) .after_current_instruction⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_rule

/-- `vmovd sym+o(%rip), %xmm`: the 4 bytes at `sym+o` must be present. -/
@[spec low] theorem MachineWP.vmovd_to_load_rip_off_spec (dst : AvxReg .W128) (l : Label) (o : Int64) :
    ⦃ fun s =>
        let a := (L l).toBitVec + o.toBitVec
        ((Mem.loadInt s.dmem a 4).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 4 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set dst ((BitVec.ofInt 32 v).zeroExtend 128) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vmovdTo dst (RegOrMem.mem ⟨some .rip, none, .sub (.add (.label l) (.int64 o)) .after_current_instruction⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_rule

/-- `vmovd %xmm, %r`: the low 32 bits of the xmm register, zero-extended. -/
@[spec low] theorem MachineWP.vmovd_from_reg_spec {w : AvxWidth} (asz : Width) (r : Reg64) (src : AvxReg .W128) :
    ⦃ fun s =>
        WP.wp p Q E { s with regs := s.regs.set64 r (((s.zmms.get src).setWidth 32).setWidth 64) } ⦄
      (Directive.instr (.avx asz w (.vmovdFrom (RegOrMem.reg (.low r .W32)) src)) :: p)
    ⦃ Q; E ⦄ := by reg_rule

/-- `vmovd %xmm, d(%b,%i,s)`: the 4 bytes must be present; they get the low 32 bits of the register. -/
@[spec low] theorem MachineWP.vmovd_from_store_mem_spec (b : Reg64) (idx : Option AddrIndex) (d : Int64) (src : AvxReg .W128) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 4).isSome = true)
          ⊓ WP.wp p Q E { s with dmem := Mem.storeInt s.dmem a 4 ((s.zmms.get src).setWidth 32).toInt } ⦄
      (Directive.instr (.avx .W64 .W128 (.vmovdFrom (RegOrMem.mem ⟨some (.reg b), idx, .int64 d⟩) src)) :: p)
    ⦃ Q; E ⦄ := by mem_rule

/-! ### vmovq -/

/-- `vmovq %r, %xmm`: the register zero-extended into the xmm register. -/
@[spec low] theorem MachineWP.vmovq_to_reg_spec {w : AvxWidth} (asz : Width) (dst : AvxReg .W128) (r : Reg64) :
    ⦃ fun s =>
        WP.wp p Q E { s with zmms := s.zmms.set dst ((s.regs.get64 r).zeroExtend 128) } ⦄
      (Directive.instr (.avx asz w (.vmovqTo dst (RegOrMem.reg (.low r .W64)))) :: p)
    ⦃ Q; E ⦄ := by reg_rule

/-- `vmovq d(%b,%i,s), %xmm`: the 8 bytes must be present; they are zero-extended into the register. -/
@[spec low] theorem MachineWP.vmovq_to_load_mem_spec (dst : AvxReg .W128) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 8).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 8 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set dst ((BitVec.ofInt 64 v).zeroExtend 128) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vmovqTo dst (RegOrMem.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_rule

/-- `vmovq %xmm, %r`: the low 64 bits of the xmm register. -/
@[spec low] theorem MachineWP.vmovq_from_reg_spec {w : AvxWidth} (asz : Width) (r : Reg64) (src : AvxReg .W128) :
    ⦃ fun s =>
        WP.wp p Q E { s with regs := s.regs.set64 r ((s.zmms.get src).setWidth 64) } ⦄
      (Directive.instr (.avx asz w (.vmovqFrom (RegOrMem.reg (.low r .W64)) src)) :: p)
    ⦃ Q; E ⦄ := by reg_rule

/-- `vmovq %xmm, d(%b,%i,s)`: the 8 bytes must be present; they get the low 64 bits of the register. -/
@[spec low] theorem MachineWP.vmovq_from_store_mem_spec (b : Reg64) (idx : Option AddrIndex) (d : Int64) (src : AvxReg .W128) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 8).isSome = true)
          ⊓ WP.wp p Q E { s with dmem := Mem.storeInt s.dmem a 8 ((s.zmms.get src).setWidth 64).toInt } ⦄
      (Directive.instr (.avx .W64 .W128 (.vmovqFrom (RegOrMem.mem ⟨some (.reg b), idx, .int64 d⟩) src)) :: p)
    ⦃ Q; E ⦄ := by mem_rule

/-! ### vxorpd

The register form is `MachineWP.vxorpd_reg_spec` in PackedSse.lean
(`vxorpd %x, %x, %x` zeroes `x`, by `BitVec.xor_self`). -/

end Specs
