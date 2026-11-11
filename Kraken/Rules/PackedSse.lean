import Kraken.Rules.GenericMem

/-!
# Rules for packed SSE and AVX instructions

`MachineWP` rules for the packed vector forms that compiled C (VEX-encoded,
`-mavx`) and hand-written SSE (`libavcodec/x86/sbrdsp.asm`) use: moves,
lanewise arithmetic and logic, shuffles, blends, inserts and extracts.

Each memory rule is stated once over the operand `⟨some (.reg b), idx, .int64 d⟩`
(any index and scale, or none), whose address is
`regs.get64 b + AddrIndex.offset64 idx regs + d.toBitVec`, as in
`GenericMem.lean`. A few forms that compiled C uses with constants also get a
`sym(%rip)` rule (`_rip_spec`) and a `sym+o(%rip)` rule (`_rip_off_spec`).

The memory side conditions are the ones the semantics checks:

* every access needs its bytes readable (`Mem.loadInt … = some _`); stores need
  them owned, which is the same condition;
* `isAligned n a` appears exactly where `AvxOperation.interp` passes
  `checkAlign := true`: the VEX aligned moves (`vmovaps`, `vmovapd`, `vmovdqa`,
  16 bytes at `.W128` and 32 at `.W256`), and every legacy 128-bit memory
  operand except those of `movups` and `movdqu`;
* `m32`/`m64` operands (`vbroadcastss`, `vinsertps`, `vmovlps`, `movss`,
  `movsd`, `movq`, `movlps`, `movhps`, `addss`, `movddup`) go through the
  general-purpose 4- or 8-byte access and are never alignment-checked.

The register values are stated exactly, as `AvxOperation.interp` computes them.

The rules are per constructor: `vcgen` picks a rule by the shape of the
instruction, so one rule with a variable operation would match every vector
instruction. The proofs are shared instead: `mem_load`/`mem_store` (and their
aligned variants) run the proof of `GenericMem.lean` for any form whose
interpretation is one memory access followed by a fall-through, and register
forms use `fallthrough_spec`.

All rules are `@[spec low]`, so the shape-specific rules of `MachineWP.lean`
and `GenericMem.lean` keep priority where both fit. Forms those files already
cover (`movaps`/`addps`/`subps` register forms, the generic `movaps` load,
`vxorps`/`vaddps`/`vshufps` register forms) are not repeated.
-/

open Kraken MachineWP Std.WP Lean.Order

set_option linter.unusedSimpArgs false

section Specs

variable [CodeEnv] {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}
  {p : Program}

local macro "wp_step" : tactic =>
  `(tactic| simp only [Executable.stepAt, Directive.interp, Instr.interp,
      Operation.interp, AvxOperation.interp, Operand.interp, RegOrMem.interp,
      AvxRegOrMem.interp, AvxRegOrMem.interpLow, RelRegOrMem.interp, ConstExpr.interp,
      MachineData.set, MachineData.setReg, MachineData.setAvxLegacy, MachineData.setAvxLegacyReg,
      MachineData.setAvx, MachineData.setAvxReg,
      Reg64s.get_low64, Reg64s.set_low64, Effects.All, or_false, false_or])

/-- After `wp_step`: unfold the one memory access and discharge its checks. -/
local macro "mem_access" hal:ident hv:ident : tactic =>
  `(tactic| simp only [MachineData.loadAvx, MachineData.storeAvx, MachineData.load,
      MachineData.store, AddrExpr.zeroExtend_interp_base_idx_disp,
      AddrExpr.zeroExtend_interp_rip_label, AddrExpr.zeroExtend_interp_rip_label_add,
      $hal:ident, $hv:ident, AvxWidth.bytes, Width.bytes,
      Bool.not_true, Bool.and_false, Bool.false_and, Bool.false_eq_true, ite_false,
      Effects.All])

/-- Proof of a load rule with precondition
`isSome ⊓ (∀ v, load = some v → wp …)`. -/
local macro "mem_load" : tactic =>
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
    mem_access hv hv
    exact hk v hv _ hpl'))

/-- Proof of a load rule with precondition
`aligned ⊓ isSome ⊓ (∀ v, load = some v → wp …)`. -/
local macro "mem_load_al" : tactic =>
  `(tactic| (
    refine Triple.intro fun s h => ?_
    simp only [meet_prop_eq_and] at h
    obtain ⟨⟨hal, hsome⟩, hk⟩ := h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    rw [after_instr hseg]
    refine step_here hseg (Or.inl ?_)
    wp_step
    mem_access hal hv
    exact hk v hv _ hpl'))

/-- Proof of a store rule with precondition `isSome ⊓ wp …`. -/
local macro "mem_store" : tactic =>
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
    mem_access hv hv
    exact hk _ hpl'))

/-- Proof of a store rule with precondition `aligned ⊓ isSome ⊓ wp …`. -/
local macro "mem_store_al" : tactic =>
  `(tactic| (
    refine Triple.intro fun s h => ?_
    simp only [meet_prop_eq_and] at h
    obtain ⟨⟨hal, hsome⟩, hk⟩ := h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    rw [after_instr hseg]
    refine step_here hseg (Or.inl ?_)
    wp_step
    mem_access hal hv
    exact hk _ hpl'))

/-- Proof of a register rule: the cell computes the stated state and falls
through. -/
local macro "reg_proof" : term =>
  `(fallthrough_spec (fun _ _ _ hP => by
      wp_step
      (try simp only [Reg64s.get_low32, Reg64s.set_low32])
      exact hP))


/-! ### VEX packed moves

`vmovaps`, `vmovapd` and `vmovdqa` check alignment (16 bytes at `.W128`, 32
at `.W256`); `vmovups` does not. A register destination is written with the
bits above the operation width cleared (`RegZmms.set`).
-/

/-- `vmovaps m128, %xmm`: 16 readable bytes, 16-byte aligned. -/
@[spec low] theorem MachineWP.vmovaps_load_mem_spec (x : AvxReg .W128) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        (isAligned 16 a = true) ⊓ ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set x (BitVec.ofInt 128 v) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vmovaps (.avx x) (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load_al

/-- `vmovaps %xmm, m128`: 16 owned bytes, 16-byte aligned. -/
@[spec low] theorem MachineWP.vmovaps_store_mem_spec (x : AvxReg .W128) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        (isAligned 16 a = true) ⊓ ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ WP.wp p Q E { s with dmem := Mem.storeInt s.dmem a 16 (s.zmms.get x).toInt } ⦄
      (Directive.instr (.avx .W64 .W128 (.vmovaps (.mem ⟨some (.reg b), idx, .int64 d⟩) (.avx x))) :: p)
    ⦃ Q; E ⦄ := by mem_store_al

/-- `vmovaps m256, %ymm`: 32 readable bytes, 32-byte aligned. -/
@[spec low] theorem MachineWP.vmovaps256_load_mem_spec (y : AvxReg .W256) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        (isAligned 32 a = true) ⊓ ((Mem.loadInt s.dmem a 32).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 32 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set y (BitVec.ofInt 256 v) }) ⦄
      (Directive.instr (.avx .W64 .W256 (.vmovaps (.avx y) (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load_al

/-- `vmovaps %ymm, m256`: 32 owned bytes, 32-byte aligned. -/
@[spec low] theorem MachineWP.vmovaps256_store_mem_spec (y : AvxReg .W256) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        (isAligned 32 a = true) ⊓ ((Mem.loadInt s.dmem a 32).isSome = true)
          ⊓ WP.wp p Q E { s with dmem := Mem.storeInt s.dmem a 32 (s.zmms.get y).toInt } ⦄
      (Directive.instr (.avx .W64 .W256 (.vmovaps (.mem ⟨some (.reg b), idx, .int64 d⟩) (.avx y))) :: p)
    ⦃ Q; E ⦄ := by mem_store_al

/-- `vmovapd m128, %xmm`: 16 readable bytes, 16-byte aligned. -/
@[spec low] theorem MachineWP.vmovapd_load_mem_spec (x : AvxReg .W128) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        (isAligned 16 a = true) ⊓ ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set x (BitVec.ofInt 128 v) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vmovapd (.avx x) (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load_al

/-- `vmovapd %xmm, m128`: 16 owned bytes, 16-byte aligned. -/
@[spec low] theorem MachineWP.vmovapd_store_mem_spec (x : AvxReg .W128) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        (isAligned 16 a = true) ⊓ ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ WP.wp p Q E { s with dmem := Mem.storeInt s.dmem a 16 (s.zmms.get x).toInt } ⦄
      (Directive.instr (.avx .W64 .W128 (.vmovapd (.mem ⟨some (.reg b), idx, .int64 d⟩) (.avx x))) :: p)
    ⦃ Q; E ⦄ := by mem_store_al

/-- `vmovapd m256, %ymm`: 32 readable bytes, 32-byte aligned. -/
@[spec low] theorem MachineWP.vmovapd256_load_mem_spec (y : AvxReg .W256) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        (isAligned 32 a = true) ⊓ ((Mem.loadInt s.dmem a 32).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 32 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set y (BitVec.ofInt 256 v) }) ⦄
      (Directive.instr (.avx .W64 .W256 (.vmovapd (.avx y) (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load_al

/-- `vmovapd %ymm, m256`: 32 owned bytes, 32-byte aligned. -/
@[spec low] theorem MachineWP.vmovapd256_store_mem_spec (y : AvxReg .W256) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        (isAligned 32 a = true) ⊓ ((Mem.loadInt s.dmem a 32).isSome = true)
          ⊓ WP.wp p Q E { s with dmem := Mem.storeInt s.dmem a 32 (s.zmms.get y).toInt } ⦄
      (Directive.instr (.avx .W64 .W256 (.vmovapd (.mem ⟨some (.reg b), idx, .int64 d⟩) (.avx y))) :: p)
    ⦃ Q; E ⦄ := by mem_store_al

/-- `vmovdqa m128, %xmm`: 16 readable bytes, 16-byte aligned. -/
@[spec low] theorem MachineWP.vmovdqa_load_mem_spec (x : AvxReg .W128) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        (isAligned 16 a = true) ⊓ ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set x (BitVec.ofInt 128 v) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vmovdqa (.avx x) (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load_al

/-- `vmovdqa %xmm, m128`: 16 owned bytes, 16-byte aligned. -/
@[spec low] theorem MachineWP.vmovdqa_store_mem_spec (x : AvxReg .W128) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        (isAligned 16 a = true) ⊓ ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ WP.wp p Q E { s with dmem := Mem.storeInt s.dmem a 16 (s.zmms.get x).toInt } ⦄
      (Directive.instr (.avx .W64 .W128 (.vmovdqa (.mem ⟨some (.reg b), idx, .int64 d⟩) (.avx x))) :: p)
    ⦃ Q; E ⦄ := by mem_store_al

/-- `vmovdqa m256, %ymm`: 32 readable bytes, 32-byte aligned. -/
@[spec low] theorem MachineWP.vmovdqa256_load_mem_spec (y : AvxReg .W256) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        (isAligned 32 a = true) ⊓ ((Mem.loadInt s.dmem a 32).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 32 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set y (BitVec.ofInt 256 v) }) ⦄
      (Directive.instr (.avx .W64 .W256 (.vmovdqa (.avx y) (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load_al

/-- `vmovdqa %ymm, m256`: 32 owned bytes, 32-byte aligned. -/
@[spec low] theorem MachineWP.vmovdqa256_store_mem_spec (y : AvxReg .W256) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        (isAligned 32 a = true) ⊓ ((Mem.loadInt s.dmem a 32).isSome = true)
          ⊓ WP.wp p Q E { s with dmem := Mem.storeInt s.dmem a 32 (s.zmms.get y).toInt } ⦄
      (Directive.instr (.avx .W64 .W256 (.vmovdqa (.mem ⟨some (.reg b), idx, .int64 d⟩) (.avx y))) :: p)
    ⦃ Q; E ⦄ := by mem_store_al

/-- `vmovups m128, %xmm`: 16 readable bytes, at any alignment. -/
@[spec low] theorem MachineWP.vmovups_load_mem_spec (x : AvxReg .W128) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set x (BitVec.ofInt 128 v) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vmovups (.avx x) (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load

/-- `vmovups %xmm, m128`: 16 owned bytes, at any alignment. -/
@[spec low] theorem MachineWP.vmovups_store_mem_spec (x : AvxReg .W128) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ WP.wp p Q E { s with dmem := Mem.storeInt s.dmem a 16 (s.zmms.get x).toInt } ⦄
      (Directive.instr (.avx .W64 .W128 (.vmovups (.mem ⟨some (.reg b), idx, .int64 d⟩) (.avx x))) :: p)
    ⦃ Q; E ⦄ := by mem_store

/-- `vmovups m256, %ymm`: 32 readable bytes, at any alignment. -/
@[spec low] theorem MachineWP.vmovups256_load_mem_spec (y : AvxReg .W256) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 32).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 32 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set y (BitVec.ofInt 256 v) }) ⦄
      (Directive.instr (.avx .W64 .W256 (.vmovups (.avx y) (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load

/-- `vmovups %ymm, m256`: 32 owned bytes, at any alignment. -/
@[spec low] theorem MachineWP.vmovups256_store_mem_spec (y : AvxReg .W256) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 32).isSome = true)
          ⊓ WP.wp p Q E { s with dmem := Mem.storeInt s.dmem a 32 (s.zmms.get y).toInt } ⦄
      (Directive.instr (.avx .W64 .W256 (.vmovups (.mem ⟨some (.reg b), idx, .int64 d⟩) (.avx y))) :: p)
    ⦃ Q; E ⦄ := by mem_store

/-- `vmovaps %src, %dst` (register form, any width). -/
@[spec low] theorem MachineWP.vmovaps_reg_spec {w : AvxWidth} (dst src : AvxReg w) (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.set dst (s.zmms.get src) } ⦄
      (Directive.instr (.avx asz w (.vmovaps (.avx dst) (.avx src))) :: p)
    ⦃ Q; E ⦄ := reg_proof

/-- `vmovapd %src, %dst` (register form, any width). -/
@[spec low] theorem MachineWP.vmovapd_reg_spec {w : AvxWidth} (dst src : AvxReg w) (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.set dst (s.zmms.get src) } ⦄
      (Directive.instr (.avx asz w (.vmovapd (.avx dst) (.avx src))) :: p)
    ⦃ Q; E ⦄ := reg_proof

/-- `vmovdqa %src, %dst` (register form, any width). -/
@[spec low] theorem MachineWP.vmovdqa_reg_spec {w : AvxWidth} (dst src : AvxReg w) (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.set dst (s.zmms.get src) } ⦄
      (Directive.instr (.avx asz w (.vmovdqa (.avx dst) (.avx src))) :: p)
    ⦃ Q; E ⦄ := reg_proof

/-- `vmovups %src, %dst` (register form, any width). -/
@[spec low] theorem MachineWP.vmovups_reg_spec {w : AvxWidth} (dst src : AvxReg w) (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.set dst (s.zmms.get src) } ⦄
      (Directive.instr (.avx asz w (.vmovups (.avx dst) (.avx src))) :: p)
    ⦃ Q; E ⦄ := reg_proof

/-- `vmovlps %xmm, m64`: 8 owned bytes, any alignment; the low quadword is stored. -/
@[spec low] theorem MachineWP.vmovlps_store_mem_spec (x : AvxReg .W128) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 8).isSome = true)
          ⊓ WP.wp p Q E { s with dmem := Mem.storeInt s.dmem a 8 ((s.zmms.get x).setWidth 64).toInt } ⦄
      (Directive.instr (.avx .W64 .W128 (.vmovlpsStore ⟨some (.reg b), idx, .int64 d⟩ x)) :: p)
    ⦃ Q; E ⦄ := by mem_store

/-! ### VEX three-operand packed operations

`dst := f src1 src2`, with `src2` a register or 16 bytes of memory at any
alignment (VEX forms other than the aligned moves do not check alignment).
-/

/-- `vaddps m128, %src1, %dst`: 16 readable bytes, any alignment. -/
@[spec low] theorem MachineWP.vaddps_load_mem_spec (dst src1 : AvxReg .W128) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set dst (BitVec.packedBinOp 32 BitVec.f32add (s.zmms.get src1) (BitVec.ofInt 128 v)) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vaddps dst src1 (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load

/-- `vmulps m128, %src1, %dst`: 16 readable bytes, any alignment. -/
@[spec low] theorem MachineWP.vmulps_load_mem_spec (dst src1 : AvxReg .W128) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set dst (BitVec.packedBinOp 32 BitVec.f32mul (s.zmms.get src1) (BitVec.ofInt 128 v)) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vmulps dst src1 (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load

/-- `vsubps m128, %src1, %dst`: 16 readable bytes, any alignment. -/
@[spec low] theorem MachineWP.vsubps_load_mem_spec (dst src1 : AvxReg .W128) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set dst (BitVec.packedBinOp 32 BitVec.f32sub (s.zmms.get src1) (BitVec.ofInt 128 v)) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vsubps dst src1 (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load

/-- `vsubps %src2, %src1, %dst` (register form, any width). -/
@[spec low] theorem MachineWP.vsubps_reg_spec {w : AvxWidth} (dst src1 src2 : AvxReg w) (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.set dst (BitVec.packedBinOp 32 BitVec.f32sub (s.zmms.get src1) (s.zmms.get src2)) } ⦄
      (Directive.instr (.avx asz w (.vsubps dst src1 (.avx src2))) :: p)
    ⦃ Q; E ⦄ := reg_proof

/-- `vdivps m128, %src1, %dst`: 16 readable bytes, any alignment. -/
@[spec low] theorem MachineWP.vdivps_load_mem_spec (dst src1 : AvxReg .W128) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set dst (BitVec.packedBinOp 32 BitVec.f32div (s.zmms.get src1) (BitVec.ofInt 128 v)) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vdivps dst src1 (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load

/-- `vdivps %src2, %src1, %dst` (register form, any width). -/
@[spec low] theorem MachineWP.vdivps_reg_spec {w : AvxWidth} (dst src1 src2 : AvxReg w) (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.set dst (BitVec.packedBinOp 32 BitVec.f32div (s.zmms.get src1) (s.zmms.get src2)) } ⦄
      (Directive.instr (.avx asz w (.vdivps dst src1 (.avx src2))) :: p)
    ⦃ Q; E ⦄ := reg_proof

/-- `vaddsubps m128, %src1, %dst`: 16 readable bytes, any alignment. -/
@[spec low] theorem MachineWP.vaddsubps_load_mem_spec (dst src1 : AvxReg .W128) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set dst (BitVec.packedBinOpIdx 32
              (fun i x y => if i % 2 = 0 then BitVec.f32sub x y else BitVec.f32add x y) (s.zmms.get src1) (BitVec.ofInt 128 v)) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vaddsubps dst src1 (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load

/-- `vaddsubps %src2, %src1, %dst` (register form, any width). -/
@[spec low] theorem MachineWP.vaddsubps_reg_spec {w : AvxWidth} (dst src1 src2 : AvxReg w) (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.set dst (BitVec.packedBinOpIdx 32 (fun i x y => if i % 2 = 0 then BitVec.f32sub x y else BitVec.f32add x y) (s.zmms.get src1) (s.zmms.get src2)) } ⦄
      (Directive.instr (.avx asz w (.vaddsubps dst src1 (.avx src2))) :: p)
    ⦃ Q; E ⦄ := reg_proof

/-- `vandps m128, %src1, %dst`: 16 readable bytes, any alignment. -/
@[spec low] theorem MachineWP.vandps_load_mem_spec (dst src1 : AvxReg .W128) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set dst ((s.zmms.get src1) &&& (BitVec.ofInt 128 v)) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vandps dst src1 (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load

/-- `vandps %src2, %src1, %dst` (register form, any width). -/
@[spec low] theorem MachineWP.vandps_reg_spec {w : AvxWidth} (dst src1 src2 : AvxReg w) (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.set dst ((s.zmms.get src1) &&& (s.zmms.get src2)) } ⦄
      (Directive.instr (.avx asz w (.vandps dst src1 (.avx src2))) :: p)
    ⦃ Q; E ⦄ := reg_proof

/-- `vandnps m128, %src1, %dst`: 16 readable bytes, any alignment. -/
@[spec low] theorem MachineWP.vandnps_load_mem_spec (dst src1 : AvxReg .W128) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set dst (~~~(s.zmms.get src1) &&& (BitVec.ofInt 128 v)) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vandnps dst src1 (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load

/-- `vandnps %src2, %src1, %dst` (register form, any width). -/
@[spec low] theorem MachineWP.vandnps_reg_spec {w : AvxWidth} (dst src1 src2 : AvxReg w) (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.set dst (~~~(s.zmms.get src1) &&& (s.zmms.get src2)) } ⦄
      (Directive.instr (.avx asz w (.vandnps dst src1 (.avx src2))) :: p)
    ⦃ Q; E ⦄ := reg_proof

/-- `vxorps m128, %src1, %dst`: 16 readable bytes, any alignment. -/
@[spec low] theorem MachineWP.vxorps_load_mem_spec (dst src1 : AvxReg .W128) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set dst ((s.zmms.get src1) ^^^ (BitVec.ofInt 128 v)) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vxorps dst src1 (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load

/-- `vxorps m128, %src1, %dst`: 16 readable bytes, any alignment. -/
@[spec low] theorem MachineWP.vxorps_load_rip_spec (dst src1 : AvxReg .W128) (l : Label) :
    ⦃ fun s =>
        let a := ((_root_.Executable.labels cenv).label l).toBitVec
        ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set dst ((s.zmms.get src1) ^^^ (BitVec.ofInt 128 v)) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vxorps dst src1 (.mem ⟨some .rip, none, .sub (.label l) .after_current_instruction⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load

/-- `vxorps m128, %src1, %dst`: 16 readable bytes, any alignment. -/
@[spec low] theorem MachineWP.vxorps_load_rip_off_spec (dst src1 : AvxReg .W128) (l : Label) (o : Int64) :
    ⦃ fun s =>
        let a := ((_root_.Executable.labels cenv).label l).toBitVec + o.toBitVec
        ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set dst ((s.zmms.get src1) ^^^ (BitVec.ofInt 128 v)) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vxorps dst src1 (.mem ⟨some .rip, none, .sub (.add (.label l) (.int64 o)) .after_current_instruction⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load

/-- `vxorpd m128, %src1, %dst`: 16 readable bytes, any alignment. -/
@[spec low] theorem MachineWP.vxorpd_load_mem_spec (dst src1 : AvxReg .W128) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set dst ((s.zmms.get src1) ^^^ (BitVec.ofInt 128 v)) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vxorpd dst src1 (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load

/-- `vxorpd %src2, %src1, %dst` (register form, any width). -/
@[spec low] theorem MachineWP.vxorpd_reg_spec {w : AvxWidth} (dst src1 src2 : AvxReg w) (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.set dst ((s.zmms.get src1) ^^^ (s.zmms.get src2)) } ⦄
      (Directive.instr (.avx asz w (.vxorpd dst src1 (.avx src2))) :: p)
    ⦃ Q; E ⦄ := reg_proof

/-- `vpaddd m128, %src1, %dst`: 16 readable bytes, any alignment. -/
@[spec low] theorem MachineWP.vpaddd_load_mem_spec (dst src1 : AvxReg .W128) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set dst (BitVec.packedBinOp 32 (· + ·) (s.zmms.get src1) (BitVec.ofInt 128 v)) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vpaddd dst src1 (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load

/-- `vpaddd m128, %src1, %dst`: 16 readable bytes, any alignment. -/
@[spec low] theorem MachineWP.vpaddd_load_rip_spec (dst src1 : AvxReg .W128) (l : Label) :
    ⦃ fun s =>
        let a := ((_root_.Executable.labels cenv).label l).toBitVec
        ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set dst (BitVec.packedBinOp 32 (· + ·) (s.zmms.get src1) (BitVec.ofInt 128 v)) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vpaddd dst src1 (.mem ⟨some .rip, none, .sub (.label l) .after_current_instruction⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load

/-- `vpaddd m128, %src1, %dst`: 16 readable bytes, any alignment. -/
@[spec low] theorem MachineWP.vpaddd_load_rip_off_spec (dst src1 : AvxReg .W128) (l : Label) (o : Int64) :
    ⦃ fun s =>
        let a := ((_root_.Executable.labels cenv).label l).toBitVec + o.toBitVec
        ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set dst (BitVec.packedBinOp 32 (· + ·) (s.zmms.get src1) (BitVec.ofInt 128 v)) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vpaddd dst src1 (.mem ⟨some .rip, none, .sub (.add (.label l) (.int64 o)) .after_current_instruction⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load

/-- `vpaddd %src2, %src1, %dst` (register form, any width). -/
@[spec low] theorem MachineWP.vpaddd_reg_spec {w : AvxWidth} (dst src1 src2 : AvxReg w) (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.set dst (BitVec.packedBinOp 32 (· + ·) (s.zmms.get src1) (s.zmms.get src2)) } ⦄
      (Directive.instr (.avx asz w (.vpaddd dst src1 (.avx src2))) :: p)
    ⦃ Q; E ⦄ := reg_proof

/-- `vpand m128, %src1, %dst`: 16 readable bytes, any alignment. -/
@[spec low] theorem MachineWP.vpand_load_mem_spec (dst src1 : AvxReg .W128) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set dst ((s.zmms.get src1) &&& (BitVec.ofInt 128 v)) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vpand dst src1 (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load

/-- `vpand m128, %src1, %dst`: 16 readable bytes, any alignment. -/
@[spec low] theorem MachineWP.vpand_load_rip_spec (dst src1 : AvxReg .W128) (l : Label) :
    ⦃ fun s =>
        let a := ((_root_.Executable.labels cenv).label l).toBitVec
        ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set dst ((s.zmms.get src1) &&& (BitVec.ofInt 128 v)) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vpand dst src1 (.mem ⟨some .rip, none, .sub (.label l) .after_current_instruction⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load

/-- `vpand m128, %src1, %dst`: 16 readable bytes, any alignment. -/
@[spec low] theorem MachineWP.vpand_load_rip_off_spec (dst src1 : AvxReg .W128) (l : Label) (o : Int64) :
    ⦃ fun s =>
        let a := ((_root_.Executable.labels cenv).label l).toBitVec + o.toBitVec
        ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set dst ((s.zmms.get src1) &&& (BitVec.ofInt 128 v)) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vpand dst src1 (.mem ⟨some .rip, none, .sub (.add (.label l) (.int64 o)) .after_current_instruction⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load

/-- `vpand %src2, %src1, %dst` (register form, any width). -/
@[spec low] theorem MachineWP.vpand_reg_spec {w : AvxWidth} (dst src1 src2 : AvxReg w) (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.set dst ((s.zmms.get src1) &&& (s.zmms.get src2)) } ⦄
      (Directive.instr (.avx asz w (.vpand dst src1 (.avx src2))) :: p)
    ⦃ Q; E ⦄ := reg_proof

/-- `vpxor m128, %src1, %dst`: 16 readable bytes, any alignment. -/
@[spec low] theorem MachineWP.vpxor_load_mem_spec (dst src1 : AvxReg .W128) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set dst ((s.zmms.get src1) ^^^ (BitVec.ofInt 128 v)) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vpxor dst src1 (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load

/-- `vpxor %src2, %src1, %dst` (register form, any width). -/
@[spec low] theorem MachineWP.vpxor_reg_spec {w : AvxWidth} (dst src1 src2 : AvxReg w) (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.set dst ((s.zmms.get src1) ^^^ (s.zmms.get src2)) } ⦄
      (Directive.instr (.avx asz w (.vpxor dst src1 (.avx src2))) :: p)
    ⦃ Q; E ⦄ := reg_proof

/-- `vmulps %src2, %src1, %dst` (register form, any width). -/
@[spec low] theorem MachineWP.vmulps_reg_spec {w : AvxWidth} (dst src1 src2 : AvxReg w) (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.set dst (BitVec.packedBinOp 32 BitVec.f32mul (s.zmms.get src1) (s.zmms.get src2)) } ⦄
      (Directive.instr (.avx asz w (.vmulps dst src1 (.avx src2))) :: p)
    ⦃ Q; E ⦄ := reg_proof

/-- `vblendvps %mask, m128, %src1, %dst`: 16 readable bytes, any alignment. -/
@[spec low] theorem MachineWP.vblendvps_load_mem_spec (dst src1 mask : AvxReg .W128) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set dst (BitVec.packedTernOp 32 (fun x y m => if m.msb then y else x)
              (s.zmms.get src1) (BitVec.ofInt 128 v) (s.zmms.get mask)) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vblendvps dst src1 (.mem ⟨some (.reg b), idx, .int64 d⟩) mask)) :: p)
    ⦃ Q; E ⦄ := by mem_load

/-- `vblendvps %mask, m128, %src1, %dst`: 16 readable bytes, any alignment. -/
@[spec low] theorem MachineWP.vblendvps_load_rip_spec (dst src1 mask : AvxReg .W128) (l : Label) :
    ⦃ fun s =>
        let a := ((_root_.Executable.labels cenv).label l).toBitVec
        ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set dst (BitVec.packedTernOp 32 (fun x y m => if m.msb then y else x)
              (s.zmms.get src1) (BitVec.ofInt 128 v) (s.zmms.get mask)) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vblendvps dst src1 (.mem ⟨some .rip, none, .sub (.label l) .after_current_instruction⟩) mask)) :: p)
    ⦃ Q; E ⦄ := by mem_load

/-- `vblendvps %mask, m128, %src1, %dst`: 16 readable bytes, any alignment. -/
@[spec low] theorem MachineWP.vblendvps_load_rip_off_spec (dst src1 mask : AvxReg .W128) (l : Label) (o : Int64) :
    ⦃ fun s =>
        let a := ((_root_.Executable.labels cenv).label l).toBitVec + o.toBitVec
        ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set dst (BitVec.packedTernOp 32 (fun x y m => if m.msb then y else x)
              (s.zmms.get src1) (BitVec.ofInt 128 v) (s.zmms.get mask)) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vblendvps dst src1 (.mem ⟨some .rip, none, .sub (.add (.label l) (.int64 o)) .after_current_instruction⟩) mask)) :: p)
    ⦃ Q; E ⦄ := by mem_load

/-- `vblendvps %mask, %src2, %src1, %dst` (register form). -/
@[spec low] theorem MachineWP.vblendvps_reg_spec {w : AvxWidth} (dst src1 src2 mask : AvxReg w) (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.set dst (BitVec.packedTernOp 32 (fun x y m => if m.msb then y else x) (s.zmms.get src1) (s.zmms.get src2) (s.zmms.get mask)) } ⦄
      (Directive.instr (.avx asz w (.vblendvps dst src1 (.avx src2) mask)) :: p)
    ⦃ Q; E ⦄ := reg_proof

/-- `vshufpd $imm, m128, %src1, %dst`: 16 readable bytes, any alignment. -/
@[spec low] theorem MachineWP.vshufpd_load_mem_spec (dst src1 : AvxReg .W128) (imm : UInt8) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set dst (BitVec.packedBinOpIdx 128 (fun k x y =>
              let i := imm.toNat >>> (2 * k);
              (if (i >>> 1) % 2 = 1 then y.qw 1 else y.qw 0) ++ (if i % 2 = 1 then x.qw 1 else x.qw 0))
              (s.zmms.get src1) (BitVec.ofInt 128 v)) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vshufpd dst src1 (.mem ⟨some (.reg b), idx, .int64 d⟩) imm)) :: p)
    ⦃ Q; E ⦄ := by mem_load

/-- `vshufpd $imm, %src2, %src1, %dst` (register form). -/
@[spec low] theorem MachineWP.vshufpd_reg_spec {w : AvxWidth} (dst src1 src2 : AvxReg w) (imm : UInt8) (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.set dst (BitVec.packedBinOpIdx 128 (fun k x y => let i := imm.toNat >>> (2 * k); (if (i >>> 1) % 2 = 1 then y.qw 1 else y.qw 0) ++ (if i % 2 = 1 then x.qw 1 else x.qw 0)) (s.zmms.get src1) (s.zmms.get src2)) } ⦄
      (Directive.instr (.avx asz w (.vshufpd dst src1 (.avx src2) imm)) :: p)
    ⦃ Q; E ⦄ := reg_proof

/-- `vshufps $imm, m128, %src1, %dst`: 16 readable bytes, any alignment. -/
@[spec low] theorem MachineWP.vshufps_load_mem_spec (dst src1 : AvxReg .W128) (imm : UInt8) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set dst (BitVec.packedBinOp 128 (BitVec.shufps128 imm) (s.zmms.get src1) (BitVec.ofInt 128 v)) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vshufps dst src1 (.mem ⟨some (.reg b), idx, .int64 d⟩) imm)) :: p)
    ⦃ Q; E ⦄ := by mem_load

/-- `vpblendw $imm, m128, %src1, %dst`: 16 readable bytes, any alignment. -/
@[spec low] theorem MachineWP.vpblendw_load_mem_spec (dst src1 : AvxReg .W128) (imm : UInt8) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set dst (BitVec.packedBinOpIdx 16
              (fun i x y => if (imm.toNat >>> (i % 8)) % 2 = 1 then y else x) (s.zmms.get src1) (BitVec.ofInt 128 v)) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vpblendw dst src1 (.mem ⟨some (.reg b), idx, .int64 d⟩) imm)) :: p)
    ⦃ Q; E ⦄ := by mem_load

/-- `vpblendw $imm, %src2, %src1, %dst` (register form). -/
@[spec low] theorem MachineWP.vpblendw_reg_spec {w : AvxWidth} (dst src1 src2 : AvxReg w) (imm : UInt8) (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.set dst (BitVec.packedBinOpIdx 16 (fun i x y => if (imm.toNat >>> (i % 8)) % 2 = 1 then y else x) (s.zmms.get src1) (s.zmms.get src2)) } ⦄
      (Directive.instr (.avx asz w (.vpblendw dst src1 (.avx src2) imm)) :: p)
    ⦃ Q; E ⦄ := reg_proof

/-! ### VEX two-operand packed operations
-/

/-- `vpermilps $imm, m128, %dst`: 16 readable bytes, any alignment. -/
@[spec low] theorem MachineWP.vpermilps_load_mem_spec (dst : AvxReg .W128) (imm : UInt8) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set dst (BitVec.packedBinOp 128 (fun x _ => BitVec.pshufd128 imm x) (BitVec.ofInt 128 v) (BitVec.ofInt 128 v)) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vpermilps dst (.mem ⟨some (.reg b), idx, .int64 d⟩) imm)) :: p)
    ⦃ Q; E ⦄ := by mem_load

/-- `vpermilps $imm, %src, %dst` (register form). -/
@[spec low] theorem MachineWP.vpermilps_reg_spec {w : AvxWidth} (dst src : AvxReg w) (imm : UInt8) (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.set dst (BitVec.packedBinOp 128 (fun x _ => BitVec.pshufd128 imm x) (s.zmms.get src) (s.zmms.get src)) } ⦄
      (Directive.instr (.avx asz w (.vpermilps dst (.avx src) imm)) :: p)
    ⦃ Q; E ⦄ := reg_proof

/-- `vmovshdup m128, %dst`: 16 readable bytes, any alignment. -/
@[spec low] theorem MachineWP.vmovshdup_load_mem_spec (dst : AvxReg .W128) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set dst (BitVec.packedBinOp 128
              (fun x _ => x.dw 3 ++ x.dw 3 ++ x.dw 1 ++ x.dw 1) (BitVec.ofInt 128 v) (BitVec.ofInt 128 v)) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vmovshdup dst (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load

/-- `vmovshdup %src, %dst` (register form). -/
@[spec low] theorem MachineWP.vmovshdup_reg_spec {w : AvxWidth} (dst src : AvxReg w) (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.set dst (BitVec.packedBinOp 128 (fun x _ => x.dw 3 ++ x.dw 3 ++ x.dw 1 ++ x.dw 1) (s.zmms.get src) (s.zmms.get src)) } ⦄
      (Directive.instr (.avx asz w (.vmovshdup dst (.avx src))) :: p)
    ⦃ Q; E ⦄ := reg_proof

/-- `vmovsldup m128, %dst`: 16 readable bytes, any alignment. -/
@[spec low] theorem MachineWP.vmovsldup_load_mem_spec (dst : AvxReg .W128) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set dst (BitVec.packedBinOp 128
              (fun x _ => x.dw 2 ++ x.dw 2 ++ x.dw 0 ++ x.dw 0) (BitVec.ofInt 128 v) (BitVec.ofInt 128 v)) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vmovsldup dst (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load

/-- `vmovsldup %src, %dst` (register form). -/
@[spec low] theorem MachineWP.vmovsldup_reg_spec {w : AvxWidth} (dst src : AvxReg w) (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.set dst (BitVec.packedBinOp 128 (fun x _ => x.dw 2 ++ x.dw 2 ++ x.dw 0 ++ x.dw 0) (s.zmms.get src) (s.zmms.get src)) } ⦄
      (Directive.instr (.avx asz w (.vmovsldup dst (.avx src))) :: p)
    ⦃ Q; E ⦄ := reg_proof

/-- `vpslld $imm, %src, %dst`: each dword shifted left (zero past 31). -/
@[spec low] theorem MachineWP.vpslld_imm_spec {w : AvxWidth} (dst src : AvxReg w) (imm : UInt8) (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.set dst (BitVec.packedBinOp 32 (fun x _ => if imm.toNat > 31 then 0#32 else x <<< imm.toNat) (s.zmms.get src) (s.zmms.get src)) } ⦄
      (Directive.instr (.avx asz w (.vpslld dst src imm)) :: p)
    ⦃ Q; E ⦄ := reg_proof

/-- `vbroadcastss m32, %dst` (any width): 4 readable bytes, any alignment. -/
@[spec low] theorem MachineWP.vbroadcastss_load_mem_spec {w : AvxWidth} (dst : AvxReg w) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 4).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 4 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set dst (BitVec.packedBinOp 32 (fun _ _ => (BitVec.ofInt 32 v)) 0 0) }) ⦄
      (Directive.instr (.avx .W64 w (.vbroadcastss dst (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load

/-- `vbroadcastss m32, %dst` (any width): 4 readable bytes, any alignment. -/
@[spec low] theorem MachineWP.vbroadcastss_load_rip_spec {w : AvxWidth} (dst : AvxReg w) (l : Label) :
    ⦃ fun s =>
        let a := ((_root_.Executable.labels cenv).label l).toBitVec
        ((Mem.loadInt s.dmem a 4).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 4 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set dst (BitVec.packedBinOp 32 (fun _ _ => (BitVec.ofInt 32 v)) 0 0) }) ⦄
      (Directive.instr (.avx .W64 w (.vbroadcastss dst (.mem ⟨some .rip, none, .sub (.label l) .after_current_instruction⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load

/-- `vbroadcastss m32, %dst` (any width): 4 readable bytes, any alignment. -/
@[spec low] theorem MachineWP.vbroadcastss_load_rip_off_spec {w : AvxWidth} (dst : AvxReg w) (l : Label) (o : Int64) :
    ⦃ fun s =>
        let a := ((_root_.Executable.labels cenv).label l).toBitVec + o.toBitVec
        ((Mem.loadInt s.dmem a 4).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 4 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set dst (BitVec.packedBinOp 32 (fun _ _ => (BitVec.ofInt 32 v)) 0 0) }) ⦄
      (Directive.instr (.avx .W64 w (.vbroadcastss dst (.mem ⟨some .rip, none, .sub (.add (.label l) (.int64 o)) .after_current_instruction⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load

/-- `vbroadcastss %xmm, %dst` (register form). -/
@[spec low] theorem MachineWP.vbroadcastss_reg_spec {w : AvxWidth} (dst : AvxReg w) (src : AvxReg .W128) (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.set dst (BitVec.packedBinOp 32 (fun _ _ => ((s.zmms.get src).setWidth 32)) 0 0) } ⦄
      (Directive.instr (.avx asz w (.vbroadcastss dst (.avx src))) :: p)
    ⦃ Q; E ⦄ := reg_proof

/-- `vinsertps $imm, m32, %src1, %dst`: 4 readable bytes, any alignment. -/
@[spec low] theorem MachineWP.vinsertps_load_mem_spec (dst src1 : AvxReg .W128) (imm : UInt8) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 4).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 4 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set dst (BitVec.insertps imm (s.zmms.get src1) (BitVec.ofInt 32 v)) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vinsertps dst src1 (.mem ⟨some (.reg b), idx, .int64 d⟩) imm)) :: p)
    ⦃ Q; E ⦄ := by mem_load

/-- `vinsertps $imm, %src2, %src1, %dst` (register form). -/
@[spec low] theorem MachineWP.vinsertps_reg_spec {w : AvxWidth} (dst src1 src2 : AvxReg .W128) (imm : UInt8) (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.set dst (BitVec.insertps imm (s.zmms.get src1) ((s.zmms.get src2).dw ((imm.toNat >>> 6) % 4))) } ⦄
      (Directive.instr (.avx asz w (.vinsertps dst src1 (.avx src2) imm)) :: p)
    ⦃ Q; E ⦄ := reg_proof

/-- `vpinsrd $imm, %r32, %src1, %dst`. -/
@[spec low] theorem MachineWP.vpinsrd_reg_spec {w : AvxWidth} (dst src1 : AvxReg .W128) (r : Reg64) (imm : UInt8) (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.set dst (BitVec.packedBinOpIdx 32 (fun i x _ => if i = imm.toNat % 4 then (s.regs.get64 r).setWidth 32 else x) (s.zmms.get src1) (s.zmms.get src1)) } ⦄
      (Directive.instr (.avx asz w (.vpinsrd dst src1 (.reg (.low r .W32)) imm)) :: p)
    ⦃ Q; E ⦄ := reg_proof

/-- `vpextrd $imm, %src, %r32`: the dword, zero-extended into the register. -/
@[spec low] theorem MachineWP.vpextrd_reg_spec {w : AvxWidth} (r : Reg64) (src : AvxReg .W128) (imm : UInt8) (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with regs := s.regs.set64 r (((s.zmms.get src).dw (imm.toNat % 4)).setWidth 64) } ⦄
      (Directive.instr (.avx asz w (.vpextrd (.reg (.low r .W32)) src imm)) :: p)
    ⦃ Q; E ⦄ := reg_proof

/-! ### Legacy SSE moves

A register destination keeps bits 255..128 (`RegZmms.setLegacy`). 128-bit
memory operands are 16-byte aligned except for `movups`/`movdqu`; the
`m32`/`m64` operands of `movss`, `movsd`, `movq`, `movlps`, `movhps` are not
alignment-checked.
-/

/-- `movdqa m128, %xmm`: 16 readable bytes, 16-byte aligned. -/
@[spec low] theorem MachineWP.movdqa_load_mem_spec (x : RegMm) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        (isAligned 16 a = true) ⊓ ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm x) (BitVec.ofInt 128 v) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.movdqa (.avx (.xmm x)) (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load_al

/-- `movdqa m128, %xmm`: 16 readable bytes, 16-byte aligned. -/
@[spec low] theorem MachineWP.movdqa_load_rip_spec (x : RegMm) (l : Label) :
    ⦃ fun s =>
        let a := ((_root_.Executable.labels cenv).label l).toBitVec
        (isAligned 16 a = true) ⊓ ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm x) (BitVec.ofInt 128 v) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.movdqa (.avx (.xmm x)) (.mem ⟨some .rip, none, .sub (.label l) .after_current_instruction⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load_al

/-- `movdqa m128, %xmm`: 16 readable bytes, 16-byte aligned. -/
@[spec low] theorem MachineWP.movdqa_load_rip_off_spec (x : RegMm) (l : Label) (o : Int64) :
    ⦃ fun s =>
        let a := ((_root_.Executable.labels cenv).label l).toBitVec + o.toBitVec
        (isAligned 16 a = true) ⊓ ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm x) (BitVec.ofInt 128 v) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.movdqa (.avx (.xmm x)) (.mem ⟨some .rip, none, .sub (.add (.label l) (.int64 o)) .after_current_instruction⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load_al

/-- `movdqa %xmm, m128`: 16 owned bytes, 16-byte aligned. -/
@[spec low] theorem MachineWP.movdqa_store_mem_spec (x : RegMm) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        (isAligned 16 a = true) ⊓ ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ WP.wp p Q E { s with dmem := Mem.storeInt s.dmem a 16 ((s.zmms.get (.xmm x))).toInt } ⦄
      (Directive.instr (.avx .W64 .W128 (.movdqa (.mem ⟨some (.reg b), idx, .int64 d⟩) (.avx (.xmm x)))) :: p)
    ⦃ Q; E ⦄ := by mem_store_al

/-- `movdqa %xs, %xd`. -/
@[spec low] theorem MachineWP.movdqa_reg_spec (xd xs : RegMm) (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm xd) (s.zmms.get (.xmm xs)) } ⦄
      (Directive.instr (.avx asz .W128 (.movdqa (.avx (.xmm xd)) (.avx (.xmm xs)))) :: p)
    ⦃ Q; E ⦄ := reg_proof

/-- `movdqu m128, %xmm`: 16 readable bytes, any alignment. -/
@[spec low] theorem MachineWP.movdqu_load_mem_spec (x : RegMm) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm x) (BitVec.ofInt 128 v) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.movdqu (.avx (.xmm x)) (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load

/-- `movdqu %xmm, m128`: 16 owned bytes, any alignment. -/
@[spec low] theorem MachineWP.movdqu_store_mem_spec (x : RegMm) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ WP.wp p Q E { s with dmem := Mem.storeInt s.dmem a 16 ((s.zmms.get (.xmm x))).toInt } ⦄
      (Directive.instr (.avx .W64 .W128 (.movdqu (.mem ⟨some (.reg b), idx, .int64 d⟩) (.avx (.xmm x)))) :: p)
    ⦃ Q; E ⦄ := by mem_store

/-- `movdqu %xs, %xd`. -/
@[spec low] theorem MachineWP.movdqu_reg_spec (xd xs : RegMm) (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm xd) (s.zmms.get (.xmm xs)) } ⦄
      (Directive.instr (.avx asz .W128 (.movdqu (.avx (.xmm xd)) (.avx (.xmm xs)))) :: p)
    ⦃ Q; E ⦄ := reg_proof

/-- `movups m128, %xmm`: 16 readable bytes, any alignment. -/
@[spec low] theorem MachineWP.movups_load_mem_spec (x : RegMm) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm x) (BitVec.ofInt 128 v) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.movups (.avx (.xmm x)) (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load

/-- `movups %xmm, m128`: 16 owned bytes, any alignment. -/
@[spec low] theorem MachineWP.movups_store_mem_spec (x : RegMm) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ WP.wp p Q E { s with dmem := Mem.storeInt s.dmem a 16 ((s.zmms.get (.xmm x))).toInt } ⦄
      (Directive.instr (.avx .W64 .W128 (.movups (.mem ⟨some (.reg b), idx, .int64 d⟩) (.avx (.xmm x)))) :: p)
    ⦃ Q; E ⦄ := by mem_store

/-- `movups %xs, %xd`. -/
@[spec low] theorem MachineWP.movups_reg_spec (xd xs : RegMm) (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm xd) (s.zmms.get (.xmm xs)) } ⦄
      (Directive.instr (.avx asz .W128 (.movups (.avx (.xmm xd)) (.avx (.xmm xs)))) :: p)
    ⦃ Q; E ⦄ := reg_proof

/-- `movaps sym(%rip), %xmm`: 16 readable bytes, 16-byte aligned. -/
@[spec low] theorem MachineWP.movaps_load_rip_spec (x : RegMm) (l : Label) :
    ⦃ fun s =>
        let a := ((_root_.Executable.labels cenv).label l).toBitVec
        (isAligned 16 a = true) ⊓ ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm x) (BitVec.ofInt 128 v) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.movaps (.avx (.xmm x)) (.mem ⟨some .rip, none, .sub (.label l) .after_current_instruction⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load_al

/-- `movaps sym+o(%rip), %xmm`: 16 readable bytes, 16-byte aligned. -/
@[spec low] theorem MachineWP.movaps_load_rip_off_spec (x : RegMm) (l : Label) (o : Int64) :
    ⦃ fun s =>
        let a := ((_root_.Executable.labels cenv).label l).toBitVec + o.toBitVec
        (isAligned 16 a = true) ⊓ ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm x) (BitVec.ofInt 128 v) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.movaps (.avx (.xmm x)) (.mem ⟨some .rip, none, .sub (.add (.label l) (.int64 o)) .after_current_instruction⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load_al

/-- `movaps %xmm, m128`: 16 owned bytes, 16-byte aligned. -/
@[spec low] theorem MachineWP.movaps_store_mem_spec (x : RegMm) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        (isAligned 16 a = true) ⊓ ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ WP.wp p Q E { s with dmem := Mem.storeInt s.dmem a 16 ((s.zmms.get (.xmm x))).toInt } ⦄
      (Directive.instr (.avx .W64 .W128 (.movaps (.mem ⟨some (.reg b), idx, .int64 d⟩) (.avx (.xmm x)))) :: p)
    ⦃ Q; E ⦄ := by mem_store_al

/-- `movss m32, %xmm`: 4 readable bytes, any alignment; bits 127..32 cleared. -/
@[spec low] theorem MachineWP.movss_load_mem_spec (x : RegMm) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 4).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 4 = some v →
            WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm x) ((BitVec.ofInt 32 v).zeroExtend 128) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.movss (.avx (.xmm x)) (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load

/-- `movss %xmm, m32`: 4 owned bytes, any alignment. -/
@[spec low] theorem MachineWP.movss_store_mem_spec (x : RegMm) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 4).isSome = true)
          ⊓ WP.wp p Q E { s with dmem := Mem.storeInt s.dmem a 4 ((s.zmms.get (.xmm x)).setWidth 32).toInt } ⦄
      (Directive.instr (.avx .W64 .W128 (.movss (.mem ⟨some (.reg b), idx, .int64 d⟩) (.avx (.xmm x)))) :: p)
    ⦃ Q; E ⦄ := by mem_store

/-- `movsd m64, %xmm`: 8 readable bytes, any alignment; bits 127..64 cleared. -/
@[spec low] theorem MachineWP.movsd_load_mem_spec (x : RegMm) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 8).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 8 = some v →
            WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm x) ((BitVec.ofInt 64 v).zeroExtend 128) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.movsd (.avx (.xmm x)) (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load

/-- `movsd %xmm, m64`: 8 owned bytes, any alignment. -/
@[spec low] theorem MachineWP.movsd_store_mem_spec (x : RegMm) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 8).isSome = true)
          ⊓ WP.wp p Q E { s with dmem := Mem.storeInt s.dmem a 8 ((s.zmms.get (.xmm x)).setWidth 64).toInt } ⦄
      (Directive.instr (.avx .W64 .W128 (.movsd (.mem ⟨some (.reg b), idx, .int64 d⟩) (.avx (.xmm x)))) :: p)
    ⦃ Q; E ⦄ := by mem_store

/-- `movqx m64, %xmm`: 8 readable bytes, any alignment; bits 127..64 cleared. -/
@[spec low] theorem MachineWP.movqx_load_mem_spec (x : RegMm) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 8).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 8 = some v →
            WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm x) ((BitVec.ofInt 64 v).zeroExtend 128) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.movqx (.avx (.xmm x)) (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load

/-- `movqx %xmm, m64`: 8 owned bytes, any alignment. -/
@[spec low] theorem MachineWP.movqx_store_mem_spec (x : RegMm) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 8).isSome = true)
          ⊓ WP.wp p Q E { s with dmem := Mem.storeInt s.dmem a 8 ((s.zmms.get (.xmm x)).setWidth 64).toInt } ⦄
      (Directive.instr (.avx .W64 .W128 (.movqx (.mem ⟨some (.reg b), idx, .int64 d⟩) (.avx (.xmm x)))) :: p)
    ⦃ Q; E ⦄ := by mem_store

/-- `movss %xs, %xd`: merges the low float. -/
@[spec low] theorem MachineWP.movss_reg_spec (xd xs : RegMm) (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm xd) ((s.zmms.get (.xmm xd)).extractLsb' 32 96 ++ (s.zmms.get (.xmm xs)).extractLsb' 0 32) } ⦄
      (Directive.instr (.avx asz .W128 (.movss (.avx (.xmm xd)) (.avx (.xmm xs)))) :: p)
    ⦃ Q; E ⦄ := reg_proof

/-- `movsd %xs, %xd`: merges the low double. -/
@[spec low] theorem MachineWP.movsd_reg_spec (xd xs : RegMm) (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm xd) ((s.zmms.get (.xmm xd)).extractLsb' 64 64 ++ (s.zmms.get (.xmm xs)).extractLsb' 0 64) } ⦄
      (Directive.instr (.avx asz .W128 (.movsd (.avx (.xmm xd)) (.avx (.xmm xs)))) :: p)
    ⦃ Q; E ⦄ := reg_proof

/-- `movq %xs, %xd`: the low quadword, zero-extended. -/
@[spec low] theorem MachineWP.movqx_reg_spec (xd xs : RegMm) (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm xd) (((s.zmms.get (.xmm xs)).setWidth 64).zeroExtend 128) } ⦄
      (Directive.instr (.avx asz .W128 (.movqx (.avx (.xmm xd)) (.avx (.xmm xs)))) :: p)
    ⦃ Q; E ⦄ := reg_proof

/-- `movlps m64, %xmm`: 8 readable bytes, any alignment; the low quadword replaced. -/
@[spec low] theorem MachineWP.movlps_load_mem_spec (x : RegMm) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 8).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 8 = some v →
            WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm x) ((s.zmms.get (.xmm x)).extractLsb' 64 64 ++ (BitVec.ofInt 64 v)) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.movlps (.avx (.xmm x)) (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load

/-- `movlps %xmm, m64`: 8 owned bytes, any alignment. -/
@[spec low] theorem MachineWP.movlps_store_mem_spec (x : RegMm) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 8).isSome = true)
          ⊓ WP.wp p Q E { s with dmem := Mem.storeInt s.dmem a 8 ((s.zmms.get (.xmm x)).setWidth 64).toInt } ⦄
      (Directive.instr (.avx .W64 .W128 (.movlps (.mem ⟨some (.reg b), idx, .int64 d⟩) (.avx (.xmm x)))) :: p)
    ⦃ Q; E ⦄ := by mem_store

/-- `movhps m64, %xmm`: 8 readable bytes, any alignment; the high quadword replaced. -/
@[spec low] theorem MachineWP.movhps_load_mem_spec (x : RegMm) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 8).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 8 = some v →
            WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm x) ((BitVec.ofInt 64 v) ++ (s.zmms.get (.xmm x)).extractLsb' 0 64) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.movhps (.avx (.xmm x)) (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load

/-- `movhps %xmm, m64`: 8 owned bytes, any alignment; the high quadword stored. -/
@[spec low] theorem MachineWP.movhps_store_mem_spec (x : RegMm) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 8).isSome = true)
          ⊓ WP.wp p Q E { s with dmem := Mem.storeInt s.dmem a 8 ((s.zmms.get (.xmm x)).extractLsb' 64 64).toInt } ⦄
      (Directive.instr (.avx .W64 .W128 (.movhps (.mem ⟨some (.reg b), idx, .int64 d⟩) (.avx (.xmm x)))) :: p)
    ⦃ Q; E ⦄ := by mem_store

/-- `movlhps %xs, %xd`. -/
@[spec low] theorem MachineWP.movlhps_spec (xd xs : RegMm) (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm xd) ((s.zmms.get (.xmm xs)).extractLsb' 0 64 ++ (s.zmms.get (.xmm xd)).extractLsb' 0 64) } ⦄
      (Directive.instr (.avx asz .W128 (.movlhps (.xmm xd) (.xmm xs))) :: p)
    ⦃ Q; E ⦄ := reg_proof

/-- `movhlps %xs, %xd`. -/
@[spec low] theorem MachineWP.movhlps_spec (xd xs : RegMm) (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm xd) ((s.zmms.get (.xmm xd)).extractLsb' 64 64 ++ (s.zmms.get (.xmm xs)).extractLsb' 64 64) } ⦄
      (Directive.instr (.avx asz .W128 (.movhlps (.xmm xd) (.xmm xs))) :: p)
    ⦃ Q; E ⦄ := reg_proof

/-! ### Legacy SSE arithmetic

`dst := f dst src`, with `src` a register or 16 bytes of 16-byte aligned
memory; `addss` and `movddup` read 4 and 8 bytes, unaligned.
-/

/-- `addps m128, %xmm`: 16 readable bytes, 16-byte aligned. -/
@[spec low] theorem MachineWP.addps_load_mem_spec (x : RegMm) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        (isAligned 16 a = true) ⊓ ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm x) (BitVec.packedBinOp 32 (fun d c => Float32.toBitVec (BitVec.toFloat32 d + BitVec.toFloat32 c)) (s.zmms.get (.xmm x)) (BitVec.ofInt 128 v)) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.addps (.avx (.xmm x)) (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load_al

/-- `subps m128, %xmm`: 16 readable bytes, 16-byte aligned. -/
@[spec low] theorem MachineWP.subps_load_mem_spec (x : RegMm) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        (isAligned 16 a = true) ⊓ ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm x) (BitVec.packedBinOp 32 (fun d c => Float32.toBitVec (BitVec.toFloat32 d - BitVec.toFloat32 c)) (s.zmms.get (.xmm x)) (BitVec.ofInt 128 v)) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.subps (.avx (.xmm x)) (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load_al

/-- `mulps m128, %xmm`: 16 readable bytes, 16-byte aligned. -/
@[spec low] theorem MachineWP.mulps_load_mem_spec (x : RegMm) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        (isAligned 16 a = true) ⊓ ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm x) (BitVec.packedBinOp 32 BitVec.f32mul (s.zmms.get (.xmm x)) (BitVec.ofInt 128 v)) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.mulps (.avx (.xmm x)) (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load_al

/-- `mulps %xs, %xd`. -/
@[spec low] theorem MachineWP.mulps_reg_spec (xd xs : RegMm) (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm xd) (BitVec.packedBinOp 32 BitVec.f32mul (s.zmms.get (.xmm xd)) (s.zmms.get (.xmm xs))) } ⦄
      (Directive.instr (.avx asz .W128 (.mulps (.avx (.xmm xd)) (.avx (.xmm xs)))) :: p)
    ⦃ Q; E ⦄ := reg_proof

/-- `xorps m128, %xmm`: 16 readable bytes, 16-byte aligned. -/
@[spec low] theorem MachineWP.xorps_load_mem_spec (x : RegMm) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        (isAligned 16 a = true) ⊓ ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm x) ((s.zmms.get (.xmm x)) ^^^ (BitVec.ofInt 128 v)) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.xorps (.avx (.xmm x)) (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load_al

/-- `xorps %xs, %xd`. -/
@[spec low] theorem MachineWP.xorps_reg_spec (xd xs : RegMm) (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm xd) ((s.zmms.get (.xmm xd)) ^^^ (s.zmms.get (.xmm xs))) } ⦄
      (Directive.instr (.avx asz .W128 (.xorps (.avx (.xmm xd)) (.avx (.xmm xs)))) :: p)
    ⦃ Q; E ⦄ := reg_proof

/-- `shufps $imm, m128, %xmm`: 16 readable bytes, 16-byte aligned. -/
@[spec low] theorem MachineWP.shufps_load_mem_spec (x : RegMm) (imm : UInt8) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        (isAligned 16 a = true) ⊓ ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm x) (BitVec.shufps128 imm (s.zmms.get (.xmm x)) (BitVec.ofInt 128 v)) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.shufps (.xmm x) (.mem ⟨some (.reg b), idx, .int64 d⟩) imm)) :: p)
    ⦃ Q; E ⦄ := by mem_load_al

/-- `shufps $imm, %xs, %xd`. -/
@[spec low] theorem MachineWP.shufps_reg_spec (xd xs : RegMm) (imm : UInt8) (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm xd) (BitVec.shufps128 imm (s.zmms.get (.xmm xd)) (s.zmms.get (.xmm xs))) } ⦄
      (Directive.instr (.avx asz .W128 (.shufps (.xmm xd) (.avx (.xmm xs)) imm)) :: p)
    ⦃ Q; E ⦄ := reg_proof

/-- `unpcklps m128, %xmm`: 16 readable bytes, 16-byte aligned. -/
@[spec low] theorem MachineWP.unpcklps_load_mem_spec (x : RegMm) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        (isAligned 16 a = true) ⊓ ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm x) ((BitVec.ofInt 128 v).dw 1 ++ (s.zmms.get (.xmm x)).dw 1 ++ (BitVec.ofInt 128 v).dw 0 ++ (s.zmms.get (.xmm x)).dw 0) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.unpcklps (.xmm x) (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load_al

/-- `unpcklps %xs, %xd`. -/
@[spec low] theorem MachineWP.unpcklps_reg_spec (xd xs : RegMm) (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm xd) ((s.zmms.get (.xmm xs)).dw 1 ++ (s.zmms.get (.xmm xd)).dw 1 ++ (s.zmms.get (.xmm xs)).dw 0 ++ (s.zmms.get (.xmm xd)).dw 0) } ⦄
      (Directive.instr (.avx asz .W128 (.unpcklps (.xmm xd) (.avx (.xmm xs)))) :: p)
    ⦃ Q; E ⦄ := reg_proof

/-- `punpckldq m128, %xmm`: 16 readable bytes, 16-byte aligned. -/
@[spec low] theorem MachineWP.punpckldq_load_mem_spec (x : RegMm) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        (isAligned 16 a = true) ⊓ ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm x) ((BitVec.ofInt 128 v).dw 1 ++ (s.zmms.get (.xmm x)).dw 1 ++ (BitVec.ofInt 128 v).dw 0 ++ (s.zmms.get (.xmm x)).dw 0) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.punpckldq (.xmm x) (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load_al

/-- `punpckldq %xs, %xd`. -/
@[spec low] theorem MachineWP.punpckldq_reg_spec (xd xs : RegMm) (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm xd) ((s.zmms.get (.xmm xs)).dw 1 ++ (s.zmms.get (.xmm xd)).dw 1 ++ (s.zmms.get (.xmm xs)).dw 0 ++ (s.zmms.get (.xmm xd)).dw 0) } ⦄
      (Directive.instr (.avx asz .W128 (.punpckldq (.xmm xd) (.avx (.xmm xs)))) :: p)
    ⦃ Q; E ⦄ := reg_proof

/-- `unpckhps m128, %xmm`: 16 readable bytes, 16-byte aligned. -/
@[spec low] theorem MachineWP.unpckhps_load_mem_spec (x : RegMm) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        (isAligned 16 a = true) ⊓ ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm x) ((BitVec.ofInt 128 v).dw 3 ++ (s.zmms.get (.xmm x)).dw 3 ++ (BitVec.ofInt 128 v).dw 2 ++ (s.zmms.get (.xmm x)).dw 2) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.unpckhps (.xmm x) (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load_al

/-- `unpckhps %xs, %xd`. -/
@[spec low] theorem MachineWP.unpckhps_reg_spec (xd xs : RegMm) (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm xd) ((s.zmms.get (.xmm xs)).dw 3 ++ (s.zmms.get (.xmm xd)).dw 3 ++ (s.zmms.get (.xmm xs)).dw 2 ++ (s.zmms.get (.xmm xd)).dw 2) } ⦄
      (Directive.instr (.avx asz .W128 (.unpckhps (.xmm xd) (.avx (.xmm xs)))) :: p)
    ⦃ Q; E ⦄ := reg_proof

/-- `punpckhdq m128, %xmm`: 16 readable bytes, 16-byte aligned. -/
@[spec low] theorem MachineWP.punpckhdq_load_mem_spec (x : RegMm) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        (isAligned 16 a = true) ⊓ ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm x) ((BitVec.ofInt 128 v).dw 3 ++ (s.zmms.get (.xmm x)).dw 3 ++ (BitVec.ofInt 128 v).dw 2 ++ (s.zmms.get (.xmm x)).dw 2) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.punpckhdq (.xmm x) (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load_al

/-- `punpckhdq %xs, %xd`. -/
@[spec low] theorem MachineWP.punpckhdq_reg_spec (xd xs : RegMm) (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm xd) ((s.zmms.get (.xmm xs)).dw 3 ++ (s.zmms.get (.xmm xd)).dw 3 ++ (s.zmms.get (.xmm xs)).dw 2 ++ (s.zmms.get (.xmm xd)).dw 2) } ⦄
      (Directive.instr (.avx asz .W128 (.punpckhdq (.xmm xd) (.avx (.xmm xs)))) :: p)
    ⦃ Q; E ⦄ := reg_proof

/-- `haddps m128, %xmm`: 16 readable bytes, 16-byte aligned. -/
@[spec low] theorem MachineWP.haddps_load_mem_spec (x : RegMm) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        (isAligned 16 a = true) ⊓ ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm x) (BitVec.haddps128 (s.zmms.get (.xmm x)) (BitVec.ofInt 128 v)) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.haddps (.xmm x) (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load_al

/-- `haddps %xs, %xd`. -/
@[spec low] theorem MachineWP.haddps_reg_spec (xd xs : RegMm) (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm xd) (BitVec.haddps128 (s.zmms.get (.xmm xd)) (s.zmms.get (.xmm xs))) } ⦄
      (Directive.instr (.avx asz .W128 (.haddps (.xmm xd) (.avx (.xmm xs)))) :: p)
    ⦃ Q; E ⦄ := reg_proof

/-- `movshdup m128, %xmm`: 16 readable bytes, 16-byte aligned. -/
@[spec low] theorem MachineWP.movshdup_load_mem_spec (x : RegMm) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        (isAligned 16 a = true) ⊓ ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm x) ((BitVec.ofInt 128 v).dw 3 ++ (BitVec.ofInt 128 v).dw 3 ++ (BitVec.ofInt 128 v).dw 1 ++ (BitVec.ofInt 128 v).dw 1) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.movshdup (.xmm x) (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load_al

/-- `movshdup %xs, %xd`. -/
@[spec low] theorem MachineWP.movshdup_reg_spec (xd xs : RegMm) (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm xd) ((s.zmms.get (.xmm xs)).dw 3 ++ (s.zmms.get (.xmm xs)).dw 3 ++ (s.zmms.get (.xmm xs)).dw 1 ++ (s.zmms.get (.xmm xs)).dw 1) } ⦄
      (Directive.instr (.avx asz .W128 (.movshdup (.xmm xd) (.avx (.xmm xs)))) :: p)
    ⦃ Q; E ⦄ := reg_proof

/-- `pxor m128, %xmm`: 16 readable bytes, 16-byte aligned. -/
@[spec low] theorem MachineWP.pxor_load_mem_spec (x : RegMm) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        (isAligned 16 a = true) ⊓ ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm x) ((s.zmms.get (.xmm x)) ^^^ (BitVec.ofInt 128 v)) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.pxor (.xmm x) (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load_al

/-- `pxor %xs, %xd`. -/
@[spec low] theorem MachineWP.pxor_reg_spec (xd xs : RegMm) (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm xd) ((s.zmms.get (.xmm xd)) ^^^ (s.zmms.get (.xmm xs))) } ⦄
      (Directive.instr (.avx asz .W128 (.pxor (.xmm xd) (.avx (.xmm xs)))) :: p)
    ⦃ Q; E ⦄ := reg_proof

/-- `pand m128, %xmm`: 16 readable bytes, 16-byte aligned. -/
@[spec low] theorem MachineWP.pand_load_mem_spec (x : RegMm) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        (isAligned 16 a = true) ⊓ ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm x) ((s.zmms.get (.xmm x)) &&& (BitVec.ofInt 128 v)) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.pand (.xmm x) (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load_al

/-- `pand %xs, %xd`. -/
@[spec low] theorem MachineWP.pand_reg_spec (xd xs : RegMm) (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm xd) ((s.zmms.get (.xmm xd)) &&& (s.zmms.get (.xmm xs))) } ⦄
      (Directive.instr (.avx asz .W128 (.pand (.xmm xd) (.avx (.xmm xs)))) :: p)
    ⦃ Q; E ⦄ := reg_proof

/-- `pcmpeqd m128, %xmm`: 16 readable bytes, 16-byte aligned. -/
@[spec low] theorem MachineWP.pcmpeqd_load_mem_spec (x : RegMm) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        (isAligned 16 a = true) ⊓ ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm x) (BitVec.packedBinOp 32
              (fun x y => if x = y then BitVec.allOnes 32 else 0#32) (s.zmms.get (.xmm x)) (BitVec.ofInt 128 v)) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.pcmpeqd (.xmm x) (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load_al

/-- `pcmpeqd %xs, %xd`. -/
@[spec low] theorem MachineWP.pcmpeqd_reg_spec (xd xs : RegMm) (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm xd) (BitVec.packedBinOp 32 (fun x y => if x = y then BitVec.allOnes 32 else 0#32) (s.zmms.get (.xmm xd)) (s.zmms.get (.xmm xs))) } ⦄
      (Directive.instr (.avx asz .W128 (.pcmpeqd (.xmm xd) (.avx (.xmm xs)))) :: p)
    ⦃ Q; E ⦄ := reg_proof

/-- `pshufd $imm, m128, %xmm`: 16 readable bytes, 16-byte aligned. -/
@[spec low] theorem MachineWP.pshufd_load_mem_spec (x : RegMm) (imm : UInt8) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        (isAligned 16 a = true) ⊓ ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm x) (BitVec.pshufd128 imm (BitVec.ofInt 128 v)) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.pshufd (.xmm x) (.mem ⟨some (.reg b), idx, .int64 d⟩) imm)) :: p)
    ⦃ Q; E ⦄ := by mem_load_al

/-- `pshufd $imm, %xs, %xd`. -/
@[spec low] theorem MachineWP.pshufd_reg_spec (xd xs : RegMm) (imm : UInt8) (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm xd) (BitVec.pshufd128 imm (s.zmms.get (.xmm xs))) } ⦄
      (Directive.instr (.avx asz .W128 (.pshufd (.xmm xd) (.avx (.xmm xs)) imm)) :: p)
    ⦃ Q; E ⦄ := reg_proof

/-- `addss m32, %xmm`: 4 readable bytes, any alignment. -/
@[spec low] theorem MachineWP.addss_load_mem_spec (x : RegMm) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 4).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 4 = some v →
            WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm x) ((s.zmms.get (.xmm x)).extractLsb' 32 96 ++ BitVec.f32add ((s.zmms.get (.xmm x)).extractLsb' 0 32) (BitVec.ofInt 32 v)) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.addss (.xmm x) (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load

/-- `addss %xs, %xd`. -/
@[spec low] theorem MachineWP.addss_reg_spec (xd xs : RegMm) (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm xd) ((s.zmms.get (.xmm xd)).extractLsb' 32 96 ++ BitVec.f32add ((s.zmms.get (.xmm xd)).extractLsb' 0 32) ((s.zmms.get (.xmm xs)).setWidth 32)) } ⦄
      (Directive.instr (.avx asz .W128 (.addss (.xmm xd) (.avx (.xmm xs)))) :: p)
    ⦃ Q; E ⦄ := reg_proof

/-- `movddup m64, %xmm`: 8 readable bytes, any alignment. -/
@[spec low] theorem MachineWP.movddup_load_mem_spec (x : RegMm) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 8).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 8 = some v →
            WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm x) ((BitVec.ofInt 64 v) ++ (BitVec.ofInt 64 v)) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.movddup (.xmm x) (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load

/-- `movddup %xs, %xd`. -/
@[spec low] theorem MachineWP.movddup_reg_spec (xd xs : RegMm) (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm xd) ((s.zmms.get (.xmm xs)).setWidth 64 ++ (s.zmms.get (.xmm xs)).setWidth 64) } ⦄
      (Directive.instr (.avx asz .W128 (.movddup (.xmm xd) (.avx (.xmm xs)))) :: p)
    ⦃ Q; E ⦄ := reg_proof

end Specs
