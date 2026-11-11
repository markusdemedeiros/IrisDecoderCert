import Kraken.X64.Parser
import Kraken.MachineWP
import Kraken.SeparationMem
import Kraken.Rules.GenericMem
import Kraken.Rules.ScalarFloat

/-!
# Checks for the VEX scalar-float rules

Straight-line fragments of the forms the SBR code uses, proved by
`vcgen with finish` against the rules of `Kraken/Rules/ScalarFloat.lean`:
scaled-index scalar loads and stores (`(%b,%i,4)`, `0x4(%b,%i,4)`,
`(%b,%i,8)`), the scalar arithmetic, `vucomiss`/`vucomisd` followed by a `jbe`
and a `jp` whose taken and fall-through outcomes are both specified, the
conversions and `vmovd`/`vmovq` in both directions, the zeroing idioms, and
`sym(%rip)` and `sym+o(%rip)` constant loads.

## Findings

- The memory side conditions discharge from a `Mem.Blocks` precondition as
  in `GenericMem`, including a load from a slot an earlier instruction of the
  fragment stored to.
- Register results are exact. Reading an xmm register back after VEX writes
  needs `RegZmms.get_set_xmm_same`/`_ne` (added in `ScalarFloat.lean`);
  without them `grind` cannot see that `vxorps %xmm7,%xmm7,%xmm7` leaves zero
  in `xmm7` once `xmm8` is written after it.
- After `vucomiss`, `jbe`/`ja`/`jp` reduce through `StatusFlags.ofFCmp`'s
  field lemmas to the triple `BitVec.f32cmp a b = (unordered, less, equal)`;
  the fall-through of `jbe` gives `(false, false, false)`.
- A displacement into the middle of a block that does not start at a base
  register (`0x48(%rdi)` in a block at `rdi + 0x40`) is not found by the
  `Blocks.Inside` rules; the check uses `0x8(%rdi)` in the block at `rdi`.
- The parser takes `vmovd`/`vmovq` memory operands only with a numeric
  displacement (`parseRegOrMem`), so `vmovd sym(%rip), %xmm` is written out
  as a cell in `rip_prog`.
- A failing `finish` on a long fragment can run for minutes (the full
  20-instruction fragment with one bad side condition did); splitting the
  fragment localises the failure in seconds.
-/

open Kraken.X64.Parser
open Kraken MachineWP Std.WP Lean.Order
open scoped Kraken.Rules.GenericMem.Norm Kraken.Rules.ScalarFloat.FCmp Kraken.Rules.ScalarFloat.Xmm

set_option experimental.vcgen true

namespace Kraken.Examples.ScalarFloatRules

variable [CodeEnv]

/-- The address of a label in the ambient code. -/
local macro "L" : term => `((_root_.Executable.labels cenv).label)

/-! ## Arithmetic with scaled-index operands -/

def arith_prog : Program := parse("
    vmovss (%rdi,%rcx,4),%xmm0
    vmulss 0x4(%rdi,%rcx,4),%xmm0,%xmm1
    vaddss 0x80(%rsi),%xmm1,%xmm1
    vsubss %xmm0,%xmm1,%xmm2
    vdivss %xmm2,%xmm1,%xmm3
    vminss %xmm3,%xmm2,%xmm2
    vsqrtss %xmm2,%xmm2,%xmm2
    vmovss %xmm2,(%rsi,%rcx,8)
    vmovss %xmm3,0x80(%rsi)
")

theorem arith_correct (d : MachineData) (R : DataMem → Prop)
    (hrcx : (d.regs.get64 .rcx).toNat < 15)
    (h_mem : d.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, 64), (d.regs.get64 .rsi, 128),
      (d.regs.get64 .rsi + 0x80#64, 4)] ⋆ R) :
    ⦃ fun s => s = d ⦄
      arith_prog
    ⦃ fun _ s => s.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, 64), (d.regs.get64 .rsi, 128),
      (d.regs.get64 .rsi + 0x80#64, 4)] ⋆ R; fun _ _ => False ⦄ := by
  vcgen [arith_prog] with finish

#print axioms arith_correct

/-! ## `vucomiss` / `vucomisd` and a conditional jump on each outcome -/

/-- The low float of an xmm register. -/
abbrev lo32 (s : MachineData) (x : RegMm) : BitVec 32 := (s.zmms.get (.xmm x)).extractLsb' 0 32

/-- The low double of an xmm register. -/
abbrev lo64 (s : MachineData) (x : RegMm) : BitVec 64 := (s.zmms.get (.xmm x)).extractLsb' 0 64

def ucomi_prog : Program := parse("
    vucomiss %xmm0,%xmm1
    jbe .Lnot_above
    vmovss %xmm1,(%rdi,%rcx,4)
    vucomisd %xmm3,%xmm2
    jp .Lunordered
")

/-- Falling through `jbe`, `xmm1 > xmm0` (ordered, not less, not equal) and the
store happens; taking it, one of unordered, less, equal holds and memory is
untouched. `jp` is taken exactly on an unordered double compare. -/
theorem ucomi_correct (d : MachineData) (R : DataMem → Prop)
    (hrcx : (d.regs.get64 .rcx).toNat < 16)
    (h_mem : d.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, 64)] ⋆ R) :
    ⦃ fun s => s = d ⦄
      ucomi_prog
    ⦃ fun _ s =>
        (BitVec.f32cmp (lo32 d .mm1) ((d.zmms.get (.xmm .mm0)).setWidth 32)) = (false, false, false)
          ∧ (BitVec.f64cmp (lo64 d .mm2) ((d.zmms.get (.xmm .mm3)).setWidth 64)).1 = false
          ∧ s.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, 64)] ⋆ R;
      fun pc s =>
        (pc = L ".Lnot_above" ∧ s.dmem = d.dmem
          ∧ (let c := BitVec.f32cmp (lo32 d .mm1) ((d.zmms.get (.xmm .mm0)).setWidth 32)
             c.1 || c.2.1 || c.2.2) = true)
        ∨ (pc = L ".Lunordered"
          ∧ (BitVec.f64cmp (lo64 d .mm2) ((d.zmms.get (.xmm .mm3)).setWidth 64)).1 = true
          ∧ s.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, 64)] ⋆ R) ⦄ := by
  vcgen [ucomi_prog] with finish

#print axioms ucomi_correct

/-! ## Conversions, `vmovd`/`vmovq`, zeroing, `vcmpss` -/

def conv_prog : Program := parse("
    vcvtsi2ss %esi,%xmm15,%xmm0
    vcvtss2sd %xmm0,%xmm0,%xmm1
    vmulsd (%rdx,%rcx,8),%xmm1,%xmm1
    vcvtsd2ss %xmm1,%xmm1,%xmm1
    vcvtps2pd %xmm1,%xmm2
    vmovd %esi,%xmm3
    vmovd %xmm3,%eax
    vmovq %xmm2,%r8
    vmovq %r8,%xmm4
    vmovd %xmm1,(%rdi,%rcx,4)
    vmovq %xmm4,0x40(%rdi)
    vmovd 0x4(%rdi),%xmm5
    vmovq 0x40(%rdi),%xmm6
    vxorps %xmm7,%xmm7,%xmm7
    vxorpd %xmm8,%xmm8,%xmm8
    vcmpltss %xmm1,%xmm0,%xmm9
    vmovsd (%rdx),%xmm10
    vmovsd %xmm10,0x8(%rdi)
    vucomiss 0x4(%rdi),%xmm0
")

theorem conv_correct (d : MachineData) (R : DataMem → Prop)
    (hrcx : (d.regs.get64 .rcx).toNat < 16)
    (h_mem : d.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, 64), (d.regs.get64 .rdi + 0x40#64, 16),
      (d.regs.get64 .rdx, 128)] ⋆ R) :
    ⦃ fun s => s = d ⦄
      conv_prog
    ⦃ fun _ s =>
        s.zmms.get (.xmm .mm7) = 0 ∧ s.zmms.get (.xmm .mm8) = 0
          ∧ s.regs.get64 .rax = ((d.regs.get64 .rsi).setWidth 32).setWidth 64
          ∧ s.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, 64), (d.regs.get64 .rdi + 0x40#64, 16),
              (d.regs.get64 .rdx, 128)] ⋆ R;
      fun _ _ => False ⦄ := by
  vcgen [conv_prog] with finish

#print axioms conv_correct

/-! ## `sym(%rip)` constants -/

/-- The parser takes `vmovd sym(%rip), %xmm` only with a numeric
displacement, so its cell is written out. -/
def rip_prog : Program := parse("
    vmovss cst(%rip),%xmm3
    vminss cst(%rip),%xmm1,%xmm1
    vdivss cst(%rip),%xmm4,%xmm4
    vcmpltss cst(%rip),%xmm0,%xmm2
    vaddss cst(%rip),%xmm1,%xmm1
    vmovsd dcst(%rip),%xmm5
") ++ [Directive.instr (.avx .W64 .W128 (.vmovdTo (.xmm .mm6)
    (.mem ⟨some .rip, none, .sub (.label "cst") .after_current_instruction⟩)))]

theorem rip_correct (d : MachineData)
    (hc : (Mem.loadInt d.dmem (L "cst").toBitVec 4).isSome = true)
    (hd : (Mem.loadInt d.dmem (L "dcst").toBitVec 8).isSome = true) :
    ⦃ fun s => s = d ⦄
      rip_prog
    ⦃ fun _ s => s.dmem = d.dmem ∧ s.regs = d.regs; fun _ _ => False ⦄ := by
  vcgen [rip_prog, List.cons_append, List.nil_append] with finish

#print axioms rip_correct

/-- `sym+o(%rip)` and `sym-o(%rip)`: loads at the label plus an offset (the
`_rip_off_spec` rules) and `lea` of both forms. -/
def rip_off_prog : Program := parse("
    vminss cst+4(%rip),%xmm1,%xmm1
    vdivss cst+4(%rip),%xmm4,%xmm4
    lea cst+4(%rip),%rax
    lea cst-0x8(%rip),%rcx
")

theorem rip_off_correct (d : MachineData)
    (hc : (Mem.loadInt d.dmem ((L "cst").toBitVec + 4#64) 4).isSome = true) :
    ⦃ fun s => s = d ⦄
      rip_off_prog
    ⦃ fun _ s => s.dmem = d.dmem ∧ s.regs.get64 .rax = (L "cst").toBitVec + 4#64
        ∧ s.regs.get64 .rcx = (L "cst").toBitVec - 8#64; fun _ _ => False ⦄ := by
  vcgen [rip_off_prog] with finish

#print axioms rip_off_correct

end Kraken.Examples.ScalarFloatRules
