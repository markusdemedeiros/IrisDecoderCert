import Kraken.Attribute
import Kraken.Layout
import Lean
import Std

inductive Width | W8 | W16 | W32 | W64 deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

instance : ToString Width where
  toString | .W8 => "w8" | .W16 => "w16" | .W32 => "w32" | .W64 => "w64"

namespace Width
@[kstep, simp, reducible] def bits : Width → Nat | W8 => 8 | W16 => 16 | W32 => 32 | W64 => 64
@[kstep, simp, reducible] def bytes : Width → Nat | W8 => 1 | W16 => 2 | W32 => 4 | W64 => 8
@[kstep] abbrev bytesv (w : Width) {n} : BitVec n := BitVec.ofNat n w.bytes
@[kstep] abbrev type (w : Width) : Type := BitVec w.bits
instance {w : Width} : Coe Bool w.type where coe := fun b : Bool => BitVec.ofNat _ b.toNat
end Width

unif_hint (w : Width) where
  w =?= Width.W8 |- Width.type w =?= BitVec 8

unif_hint (w : Width) where
  w =?= Width.W16 |- Width.type w =?= BitVec 16

unif_hint (w : Width) where
  w =?= Width.W32 |- Width.type w =?= BitVec 32

unif_hint (w : Width) where
  w =?= Width.W64 |- Width.type w =?= BitVec 64

inductive AvxWidth | W128 | W256 | W512 deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

instance : ToString AvxWidth where
  toString |.W128 => "w128" | .W256 => "w256" | .W512 => "w512"

namespace AvxWidth
@[simp, reducible] def bits : AvxWidth → Nat | W128 => 128 | W256 => 256 | W512 => 512
@[simp, reducible] def bytes : AvxWidth → Nat | W128 => 16 | W256 => 32 | W512 => 64
abbrev bytesv (w : AvxWidth) {n} : BitVec n := BitVec.ofNat n w.bytes
abbrev type (w : AvxWidth) : Type := BitVec w.bits
instance {w : AvxWidth} : Coe Bool w.type where coe := fun b : Bool => BitVec.ofNat _ b.toNat
end AvxWidth

unif_hint (w : AvxWidth) where
  w =?= AvxWidth.W128 |- AvxWidth.type w =?= BitVec 128

unif_hint (w : AvxWidth) where
  w =?= AvxWidth.W256 |- AvxWidth.type w =?= BitVec 256

unif_hint (w : AvxWidth) where
  w =?= AvxWidth.W512 |- AvxWidth.type w =?= BitVec 512

inductive RegMm
  | mm0  | mm1  | mm2  | mm3
  | mm4  | mm5  | mm6  | mm7
  | mm8  | mm9  | mm10 | mm11
  | mm12 | mm13 | mm14 | mm15
  | mm16 | mm17 | mm18 | mm19
  | mm20 | mm21 | mm22 | mm23
  | mm24 | mm25 | mm26 | mm27
  | mm28 | mm29 | mm30 | mm31
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

inductive Reg64
  | rax | rbx | rcx | rdx
  | rsi | rdi | rsp | rbp
  | r8  | r9  | r10 | r11
  | r12 | r13 | r14 | r15
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

inductive Reg : Width → Type
  | low (_ : Reg64) (w : Width) : Reg w
  | ah : Reg .W8 | bh : Reg .W8 | ch : Reg .W8| dh : Reg .W8
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

inductive AvxReg : AvxWidth → Type
  | xmm (_ : RegMm) : AvxReg AvxWidth.W128
  | ymm (_ : RegMm) : AvxReg AvxWidth.W256
  | zmm (_ : RegMm) : AvxReg AvxWidth.W512
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

abbrev Label := String

inductive ConstExpr
  | label (_ : Label)
  | int64 (_ : Int64)
  | before_current_instruction | after_current_instruction
  | add (_ _ : ConstExpr) | sub (_ _ : ConstExpr)
  -- Careful adding operations here! Need to match overflow behavior of all
  -- assemblers we want compatibility with. We assume oversized literals error;
  -- clang and gcc seem to always use 64-bit arithmetic (MCValue has an int64).
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr
instance : Coe Label ConstExpr where coe := .label
instance : Coe Int64 ConstExpr where coe := .int64
attribute [coe] ConstExpr.label
attribute [coe] ConstExpr.int64

structure RegW where (w : Width) (reg : Reg w)
  deriving Repr, DecidableEq, Hashable, Lean.ToExpr, Hashable, Lean.ToExpr

structure AvxRegW where (w : AvxWidth) (reg : AvxReg w)
  deriving Repr, DecidableEq, Hashable, Lean.ToExpr, Hashable, Lean.ToExpr

-- For address expressions, the width of the register is determined only by the
-- instruction-wide address prefix. Concretely:
-- * movb $2 (%eax) denotes moving a single byte (operand width) into the memory
--   location at the 32-bit address stored in %eax (address width) -- note that
--   there is inference here!
-- * addr32 movb $2 (%rax) means the exact same thing, so the `addr32` prefix
--   acts as an instruction-wide override (at least for Clang; GCC rejects this)
--
-- Note that by doing so, we faithfully model two key things
-- * high byte registers cannot appear within memory operands:
--   test.S:1:11: error: invalid base+index expression
--   movb $2, (%ah)
-- * the operand encoding in the instruction encoding does not actually contain
--   a width -- it's all in the instruction-wide address size, modeled via the
--   `AddressSize` type class, below.
--
-- Implementation-wise, this means that our parser *will* have to do some amount
-- of type inference.
inductive RegOrRip where | reg (_ : Reg64) | rip : RegOrRip
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

structure AddrIndex where
  reg : Reg64
  scale: Width
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

structure AddrExpr where
  base : Option RegOrRip
  idx : Option AddrIndex
  disp : ConstExpr := .int64 0
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

class AddressSize where address_size : Width
export AddressSize (address_size)

inductive RegOrMem w | reg (r : Reg w) | mem (_ : AddrExpr)
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr
instance {w} : Coe AddrExpr (RegOrMem w) where coe := RegOrMem.mem
attribute [coe] RegOrMem.mem
instance {w} : Coe (Reg w) (RegOrMem w) where coe := .reg
attribute [coe] RegOrMem.reg
abbrev Dst := RegOrMem

inductive AvxRegOrMem (w : AvxWidth) | avx (r : AvxReg w) | mem (_ : AddrExpr)
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr
instance {w} : Coe AddrExpr (AvxRegOrMem w) where coe := AvxRegOrMem.mem
attribute [coe] AvxRegOrMem.mem
instance {w} : Coe (AvxReg w) (AvxRegOrMem w) where coe := .avx
attribute [coe] AvxRegOrMem.avx
abbrev AvxDst := AvxRegOrMem

inductive Operand w | regOrMem (_ : RegOrMem w) | imm (v : ConstExpr)
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr
instance {w} : Coe (RegOrMem w) (Operand w) where coe := .regOrMem
attribute [coe] Operand.regOrMem
instance {w} : Coe ConstExpr (Operand w) where coe := Operand.imm
attribute [coe] Operand.imm
abbrev Operand.reg {w} (r : Reg w) : Operand w := regOrMem (.reg r)
abbrev Operand.mem {w} (m : AddrExpr) : Operand w := regOrMem (.mem m)

-- TODO: We could remove this and use AvxRegOrMem directly.
inductive AvxOperand (w : AvxWidth) | regOrMem (_ : AvxRegOrMem w)
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr
instance {w} : Coe (AvxRegOrMem w) (AvxOperand w) where coe := .regOrMem
attribute [coe] AvxOperand.regOrMem
abbrev AvxOperand.avx {w} (r : AvxReg w) : AvxOperand w := regOrMem (.avx r)
abbrev AvxOperand.mem {w} (m : AddrExpr) : AvxOperand w := regOrMem (.mem m)

inductive CondCode | z | nz | c | nc | a | be | l | le | ge | g | p | np | s | ns
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr
abbrev CondCode.e := CondCode.z
abbrev CondCode.ne := CondCode.nz
abbrev CondCode.b := CondCode.c
abbrev CondCode.ae := CondCode.nc

inductive ShiftCountExpr | cl | imm8 (v : ConstExpr)
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

inductive RelRegOrMem | rel (_ : ConstExpr) | reg (r : Reg .W64) | mem (_ : AddrExpr)
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

inductive Operation (w : Width)
  -- Data movement
  | mov (_ : Dst w) (src : Operand w)
  | movsx {w'} (_ : Dst w) (src : RegOrMem w') -- {_ : w'.bits < w.bits ∧ w'.bits < 32}
  | movzx {w'} (_ : Dst w) (src : RegOrMem w') -- {_ : w'.bits < w.bits ∧ w'.bits < 32}
  | push (src : Operand w)
  | pop  (_ : Dst w)
  | setcc (_ : CondCode) (_ : Dst w) -- {_ : w = .W8}
  | cmovcc (_ : CondCode) (_ : Reg w) (src : RegOrMem w)
  -- Arithmetic
  | lea (_ : Reg w) (src : AddrExpr) -- {_ : 16 <= w.bits}
  | add  (_ : Dst w) (src : Operand w)
  | adc  (_ : Dst w) (src : Operand w)
  | adcx (_ : Reg w) (src : RegOrMem w) -- {_ : 32 <= w.bits}
  | adox (dst : Reg w) (src : RegOrMem w) -- {_ : 32 <= w.bits}
  | inc  (_ : RegOrMem w)
  | dec  (_ : RegOrMem w)
  | neg  (_ : RegOrMem w)
  | sub  (_ : Dst w) (src : Operand w)
  | sbb  (_ : Dst w) (src : Operand w)
  | cmp  (a : RegOrMem w) (b : Operand w)
  | mul  (src : RegOrMem w)
  | mulx (hi lo : Reg w) (src : RegOrMem w) -- {_ : 32 <= w.bits}
  -- imul1 and imul collectively describe variants of the same
  -- syntax level `imul` instruction, where imul1 is the 1-operand case
  | imul1 (src : RegOrMem w)
  | imul (_ : Option (Dst w)) (src1 : RegOrMem w) (src2 : Operand w)
  -- Unsigned (`div`) and signed (`idiv`) division of `rdx:rax` (`ax` for
  -- `.W8`) by `src`: quotient to `rax`, remainder to `rdx` (`al`, `ah` for
  -- `.W8`). A zero divisor or a quotient that does not fit raises #DE.
  | div  (src : RegOrMem w)
  | idiv (src : RegOrMem w)
  -- Bitwise
  | test (a : RegOrMem w) (b : Operand w)
  | and  (_ : Dst w) (src : Operand w)
  | not  (_ : Dst w)
  | or   (_ : Dst w) (src : Operand w)
  | xor  (_ : Dst w) (src : Operand w)
  | shl  (_ : Dst w) (_ : ShiftCountExpr)
  | shr  (_ : Dst w) (_ : ShiftCountExpr)
  | sar  (_ : Dst w) (_ : ShiftCountExpr)
  | shld (_ : Dst w) (src : Reg w) (_ : ShiftCountExpr) -- {_ : 16 <= w.bits}
  | shrd (_ : Dst w) (src : Reg w) (_ : ShiftCountExpr) -- {_ : 16 <= w.bits}
  | rol  (_ : Dst w) (_ : ShiftCountExpr)
  | ror  (_ : Dst w) (_ : ShiftCountExpr)
  | rcl  (_ : Dst w) (_ : ShiftCountExpr)
  | rcr  (_ : Dst w) (_ : ShiftCountExpr)
  | bswap  (dst : Reg w) -- (_ : w = .W32 ∨ w = .W64)
  -- `cltq` (Intel `cdqe`): `rax := sign-extend eax`
  | cltq
  -- `cltd` (Intel `cdq`): `edx := ` every bit a copy of bit 31 of `eax`
  | cltd
  -- Traps: each raises an exception (#UD, #BP) before touching its operands,
  -- so a step never has a successor state. `ud1`'s operands only fill the
  -- encoding (compilers put a check identifier in the ModRM byte).
  | ud1 (_ : Reg w) (src : RegOrMem w)
  | ud2
  | int3
  -- Control flow
  | jcc (cc : CondCode) (target : Label)
  | jmp (target : RelRegOrMem)
  | call (target : RelRegOrMem)
  | ret
  | nop (length : Nat)
  -- TODO: optiona third argument, with the caveat that `.align 16,,0` is valid
  -- syntax
  | nopalign (alignment : Nat) (pad : Option Nat)
  deriving Repr, DecidableEq, Hashable, Lean.ToExpr

-- The non-v* variants take SSE registers only.
-- TODO: AVX512 extensions (write-masking, ...)
inductive AvxOperation (w : AvxWidth)
  | movups (_ : AvxDst w) (src : AvxRegOrMem w)
  | vmovups (_ : AvxDst w) (src : AvxRegOrMem w)
  | movaps (_ : AvxDst w) (src : AvxRegOrMem w)
  | subps (_ : AvxDst w) (src : AvxRegOrMem w)
  | addps (_ : AvxDst w) (src : AvxRegOrMem w)
  | mulps (_ : AvxDst w) (src : AvxRegOrMem w)
  | xorps (_ : AvxDst w) (src : AvxRegOrMem w)
  -- VEX-encoded forms. A register destination is written with the bits above
  -- `w` cleared. The three-operand forms read `src1` and `src2`, in Intel
  -- order (AT&T writes `src2, src1, dst`).
  | vmovaps (_ : AvxDst w) (src : AvxRegOrMem w)
  | vxorps (_ : AvxReg w) (src1 : AvxReg w) (src2 : AvxRegOrMem w)
  | vaddps (_ : AvxReg w) (src1 : AvxReg w) (src2 : AvxRegOrMem w)
  | vmulps (_ : AvxReg w) (src1 : AvxReg w) (src2 : AvxRegOrMem w)
  -- `dst := src1 * src2 + dst`, lanewise, rounded once
  | vfmadd231ps (_ : AvxReg w) (src1 : AvxReg w) (src2 : AvxRegOrMem w)
  -- `dst := dst * src2 + src1`, lanewise, rounded once
  | vfmadd132ps (_ : AvxReg w) (src1 : AvxReg w) (src2 : AvxRegOrMem w)
  -- `dst[i] := src2[src1[i] mod 8]` on 32-bit elements (AVX2, VEX.256 only)
  | vpermps (_ : AvxReg w) (src1 : AvxReg w) (src2 : AvxRegOrMem w)
  | vshufps (_ : AvxReg w) (src1 : AvxReg w) (src2 : AvxRegOrMem w) (imm : UInt8)
  -- Forms whose operands have fixed widths; `w` is the vector length of the
  -- encoding (`vextractf128` is VEX.256, the others VEX.128). Only the
  -- register forms are modeled.
  | vextractf128 (_ : AvxReg .W128) (src : AvxReg .W256) (imm : UInt8)
  -- `src1` with its 128-bit lane `imm[0]` replaced by `src2` (VEX.256; `src2`
  -- may be memory, 16 bytes at any alignment)
  | vinsertf128 (_ : AvxReg .W256) (src1 : AvxReg .W256) (src2 : AvxRegOrMem .W128) (imm : UInt8)
  | vmovhlps (_ : AvxReg .W128) (src1 src2 : AvxReg .W128)
  | vmovss (_ : AvxReg .W128) (src1 src2 : AvxReg .W128)
  | vaddss (_ : AvxReg .W128) (src1 src2 : AvxReg .W128)
  | vzeroupper
  /- VEX scalar float forms (VEX.128; `w` is `.W128`). An `AvxRegOrMem .W128`
  marked `m32`/`m64` reads the low 32/64 bits of a register, or that many
  bytes of memory. The result is written to the low element of `dst`, the
  rest of bits 127..0 come from `src1`, and the bits above 127 are cleared. -/
  -- `vmovss m32, xmm` (zeroes bits 32 and up) and `vmovss xmm, m32`; exactly
  -- one operand is memory (the register-register form is `vmovss` above).
  | vmovssMem (_ : AvxDst .W128) (src : AvxRegOrMem .W128)
  -- `vmovsd m64, xmm` and `vmovsd xmm, m64`.
  | vmovsdMem (_ : AvxDst .W128) (src : AvxRegOrMem .W128)
  | vaddssMem (_ : AvxReg .W128) (src1 : AvxReg .W128) (src2 : AddrExpr)
  | vsubss (_ : AvxReg .W128) (src1 : AvxReg .W128) (src2 : AvxRegOrMem .W128) -- m32
  | vmulss (_ : AvxReg .W128) (src1 : AvxReg .W128) (src2 : AvxRegOrMem .W128) -- m32
  | vdivss (_ : AvxReg .W128) (src1 : AvxReg .W128) (src2 : AvxRegOrMem .W128) -- m32
  | vminss (_ : AvxReg .W128) (src1 : AvxReg .W128) (src2 : AvxRegOrMem .W128) -- m32
  | vsqrtss (_ : AvxReg .W128) (src1 : AvxReg .W128) (src2 : AvxRegOrMem .W128) -- m32
  | vmulsd (_ : AvxReg .W128) (src1 : AvxReg .W128) (src2 : AvxRegOrMem .W128) -- m64
  -- `vcmpss` with predicate `pred` (0..31; `vcmpltss` is 1, `vcmpeqss` 0):
  -- the low element becomes all ones or all zeros.
  | vcmpss (pred : UInt8) (_ : AvxReg .W128) (src1 : AvxReg .W128) (src2 : AvxRegOrMem .W128) -- m32
  -- Flag-setting unordered compares of `src1` with `src2`.
  | vucomiss (src1 : AvxReg .W128) (src2 : AvxRegOrMem .W128) -- m32
  | vucomisd (src1 : AvxReg .W128) (src2 : AvxRegOrMem .W128) -- m64
  | vcvtsi2ss {iw : Width} (_ : AvxReg .W128) (src1 : AvxReg .W128) (src2 : RegOrMem iw)
  | vcvtss2sd (_ : AvxReg .W128) (src1 : AvxReg .W128) (src2 : AvxRegOrMem .W128) -- m32
  | vcvtsd2ss (_ : AvxReg .W128) (src1 : AvxReg .W128) (src2 : AvxRegOrMem .W128) -- m64
  -- The two low floats of `src` (xmm or m64) widened to doubles.
  | vcvtps2pd (_ : AvxReg .W128) (src : AvxRegOrMem .W128)
  -- `vmovd r/m32, xmm` (zero-extends) and `vmovd xmm, r/m32`.
  | vmovdTo (_ : AvxReg .W128) (src : RegOrMem .W32)
  | vmovdFrom (_ : RegOrMem .W32) (src : AvxReg .W128)
  -- `vmovq r/m64, xmm` (zero-extends) and `vmovq xmm, r/m64`.
  | vmovqTo (_ : AvxReg .W128) (src : RegOrMem .W64)
  | vmovqFrom (_ : RegOrMem .W64) (src : AvxReg .W128)
  /- VEX packed forms; `w` is the vector length. -/
  | vmovapd (_ : AvxDst w) (src : AvxRegOrMem w)
  | vmovdqa (_ : AvxDst w) (src : AvxRegOrMem w)
  | vxorpd (_ : AvxReg w) (src1 : AvxReg w) (src2 : AvxRegOrMem w)
  | vsubps (_ : AvxReg w) (src1 : AvxReg w) (src2 : AvxRegOrMem w)
  | vdivps (_ : AvxReg w) (src1 : AvxReg w) (src2 : AvxRegOrMem w)
  -- even lanes `src1 - src2`, odd lanes `src1 + src2`
  | vaddsubps (_ : AvxReg w) (src1 : AvxReg w) (src2 : AvxRegOrMem w)
  | vandps (_ : AvxReg w) (src1 : AvxReg w) (src2 : AvxRegOrMem w)
  -- `~~~src1 &&& src2`
  | vandnps (_ : AvxReg w) (src1 : AvxReg w) (src2 : AvxRegOrMem w)
  | vpaddd (_ : AvxReg w) (src1 : AvxReg w) (src2 : AvxRegOrMem w)
  | vpand (_ : AvxReg w) (src1 : AvxReg w) (src2 : AvxRegOrMem w)
  | vpxor (_ : AvxReg w) (src1 : AvxReg w) (src2 : AvxRegOrMem w)
  -- lane `i` from `src2` when the sign bit of lane `i` of `mask` is set
  | vblendvps (_ : AvxReg w) (src1 : AvxReg w) (src2 : AvxRegOrMem w) (mask : AvxReg w)
  | vshufpd (_ : AvxReg w) (src1 : AvxReg w) (src2 : AvxRegOrMem w) (imm : UInt8)
  | vpblendw (_ : AvxReg w) (src1 : AvxReg w) (src2 : AvxRegOrMem w) (imm : UInt8)
  | vpermilps (_ : AvxReg w) (src : AvxRegOrMem w) (imm : UInt8)
  | vpslld (_ : AvxReg w) (src : AvxReg w) (imm : UInt8)
  | vmovshdup (_ : AvxReg w) (src : AvxRegOrMem w)
  | vmovsldup (_ : AvxReg w) (src : AvxRegOrMem w)
  -- the low float of `src` (m32 or xmm) in every lane of `dst`
  | vbroadcastss (_ : AvxReg w) (src : AvxRegOrMem .W128)
  | vinsertps (_ : AvxReg .W128) (src1 : AvxReg .W128) (src2 : AvxRegOrMem .W128) (imm : UInt8) -- m32
  | vpinsrd (_ : AvxReg .W128) (src1 : AvxReg .W128) (src2 : RegOrMem .W32) (imm : UInt8)
  | vpextrd (_ : RegOrMem .W32) (src : AvxReg .W128) (imm : UInt8)
  -- `vmovlps xmm, m64`
  | vmovlpsStore (_ : AddrExpr) (src : AvxReg .W128)
  -- like `vmovdqa`, but a memory operand may have any alignment
  | vmovdqu (_ : AvxDst w) (src : AvxRegOrMem w)
  -- signed 32-bit integer lanes converted to floats
  | vcvtdq2ps (_ : AvxReg w) (src : AvxRegOrMem w)
  -- lane `i` from `src2` when bit `i` of `imm` is set (32-bit lanes)
  | vblendps (_ : AvxReg w) (src1 : AvxReg w) (src2 : AvxRegOrMem w) (imm : UInt8)
  -- wrapping add of 16-bit lanes
  | vpaddw (_ : AvxReg w) (src1 : AvxReg w) (src2 : AvxRegOrMem w)
  -- signed minimum of 32-bit lanes
  | vpminsd (_ : AvxReg w) (src1 : AvxReg w) (src2 : AvxRegOrMem w)
  -- byte `i` of each 128-bit lane is zero when bit 7 of byte `i` of `src2`
  -- is set, else byte `src2[i] & 15` of the same lane of `src1`
  | vpshufb (_ : AvxReg w) (src1 : AvxReg w) (src2 : AvxRegOrMem w)
  -- each 128-bit lane: the low quadword of `src1`, then that of `src2`
  | vpunpcklqdq (_ : AvxReg w) (src1 : AvxReg w) (src2 : AvxRegOrMem w)
  -- the 32-bit elements of each 128-bit lane permuted by `imm` (as `pshufd`)
  | vpshufd (_ : AvxReg w) (src : AvxRegOrMem w) (imm : UInt8)
  -- the low float of `src` (xmm or m32) to a 64-bit signed integer
  | vcvtss2si (_ : Reg .W64) (src : AvxRegOrMem .W128) -- m32
  -- 16-bit element `imm & 7` of `src1` replaced by the low 16 bits of `src2`
  -- (only the register form is modeled)
  | vpinsrw (_ : AvxReg .W128) (src1 : AvxReg .W128) (src2 : Reg .W32) (imm : UInt8)
  -- the four low 16-bit elements of `src` (xmm or m64) sign-extended to 32 bits
  | vpmovsxwd (_ : AvxReg .W128) (src : AvxRegOrMem .W128) -- m64
  -- each 32-bit lane all ones when the lanes of `src1` and `src2` are equal,
  -- else zero (Intel SDM vol. 2, PCMPEQD, VEX encoded versions:
  -- `DEST[31:0] ← IF SRC1[31:0] = SRC2[31:0] THEN FFFFFFFFH ELSE 0`, for each
  -- doubleword; `DEST[MAXVL-1:VL] ← 0`)
  | vpcmpeqd (_ : AvxReg w) (src1 : AvxReg w) (src2 : AvxRegOrMem w)
  -- `vpsrld %count, %src, %dst`: each 32-bit lane of `src` shifted right
  -- (logical) by the low 64 bits of `count` read as an unsigned number; zero
  -- past 31 (only the register form of `count` is modeled). Intel SDM vol. 2,
  -- PSRLW/PSRLD/PSRLQ, `LOGICAL_RIGHT_SHIFT_DWORDS`: `COUNT ← COUNT_SRC[63:0];
  -- IF (COUNT > 31) THEN DEST ← 0 ELSE DEST[31:0] ← ZeroExtend(SRC[31:0] >>
  -- COUNT)`, for each doubleword; VEX: `DEST[MAXVL-1:VL] ← 0`
  | vpsrldx (_ : AvxReg w) (src : AvxReg w) (count : AvxReg .W128)
  -- the two low 32-bit elements of `src` (xmm or m64) zero-extended to 64 bits
  -- (Intel SDM vol. 2, PMOVZX, `PACKED_ZERO_EXTEND_DWORD_TO_QWORD`:
  -- `DEST[63:0] ← ZeroExtend(SRC[31:0]); DEST[127:64] ← ZeroExtend(SRC[63:32])`;
  -- VEX.128: `DEST[MAXVL-1:128] ← 0`)
  | vpmovzxdq (_ : AvxReg .W128) (src : AvxRegOrMem .W128) -- m64
  /- Legacy SSE/SSE2/SSE3 forms (`w` is `.W128`). A register destination keeps
  bits 255..128. A 128-bit memory operand must be 16-byte aligned, except for
  `movdqu`; 32- and 64-bit memory operands need no alignment. -/
  -- `movss xmm, xmm` merges the low float; `movss m32, xmm` zeroes bits
  -- 127..32; `movss xmm, m32` stores. Not both operands memory.
  | movss (_ : AvxDst .W128) (src : AvxRegOrMem .W128)
  | movsd (_ : AvxDst .W128) (src : AvxRegOrMem .W128)
  -- `movq xmm/m64, xmm` (zeroes bits 127..64) and `movq xmm, m64`.
  | movqx (_ : AvxDst .W128) (src : AvxRegOrMem .W128)
  -- the low (`movlps`) or high (`movhps`) quadword, to or from m64
  | movlps (_ : AvxDst .W128) (src : AvxRegOrMem .W128)
  | movhps (_ : AvxDst .W128) (src : AvxRegOrMem .W128)
  | movdqa (_ : AvxDst .W128) (src : AvxRegOrMem .W128)
  | movdqu (_ : AvxDst .W128) (src : AvxRegOrMem .W128)
  | addss (_ : AvxReg .W128) (src : AvxRegOrMem .W128) -- m32
  | movlhps (_ : AvxReg .W128) (src : AvxReg .W128)
  | movhlps (_ : AvxReg .W128) (src : AvxReg .W128)
  | shufps (_ : AvxReg .W128) (src : AvxRegOrMem .W128) (imm : UInt8)
  | unpcklps (_ : AvxReg .W128) (src : AvxRegOrMem .W128)
  | unpckhps (_ : AvxReg .W128) (src : AvxRegOrMem .W128)
  | haddps (_ : AvxReg .W128) (src : AvxRegOrMem .W128)
  | movddup (_ : AvxReg .W128) (src : AvxRegOrMem .W128) -- m64
  | movshdup (_ : AvxReg .W128) (src : AvxRegOrMem .W128)
  | pxor (_ : AvxReg .W128) (src : AvxRegOrMem .W128)
  | pand (_ : AvxReg .W128) (src : AvxRegOrMem .W128)
  | pcmpeqd (_ : AvxReg .W128) (src : AvxRegOrMem .W128)
  | pshufd (_ : AvxReg .W128) (src : AvxRegOrMem .W128) (imm : UInt8)
  | punpckldq (_ : AvxReg .W128) (src : AvxRegOrMem .W128)
  | punpckhdq (_ : AvxReg .W128) (src : AvxRegOrMem .W128)
  deriving Repr, DecidableEq, Hashable, Lean.ToExpr

inductive Instr
  | regular (address_size : Width) (operation_size : Width) (operation : Operation operation_size)
  | avx (address_size : Width) (operation_size : AvxWidth) (operation : AvxOperation operation_size)
  deriving Repr, DecidableEq, Hashable, Lean.ToExpr

instance [AddressSize] {w : Width} : CoeOut (Operation w) Instr where
  coe op := Instr.regular address_size w op

instance [AddressSize] {w : AvxWidth} : CoeOut (AvxOperation w) Instr where
  coe op := Instr.avx address_size w op

instance : Repr ByteArray where reprPrec _ _ := "<opaque byte array>"

deriving instance Lean.ToExpr for ByteArray
inductive Directive
  | instr (_ : Instr)
  | label (_ : Label)
  | byteArray (_ : ByteArray)
  deriving BEq, DecidableEq, Repr, Hashable, Lean.ToExpr

abbrev Program := List Directive
abbrev Executable := Kraken.Executable Directive

namespace Reg
@[match_pattern] abbrev rax := low .rax .W64
@[match_pattern] abbrev rbx := low .rbx .W64
@[match_pattern] abbrev rcx := low .rcx .W64
@[match_pattern] abbrev rdx := low .rdx .W64
@[match_pattern] abbrev rsi := low .rsi .W64
@[match_pattern] abbrev rdi := low .rdi .W64
@[match_pattern] abbrev rsp := low .rsp .W64
@[match_pattern] abbrev rbp := low .rbp .W64
@[match_pattern] abbrev r8  := low .r8  .W64
@[match_pattern] abbrev r9  := low .r9  .W64
@[match_pattern] abbrev r10 := low .r10 .W64
@[match_pattern] abbrev r11 := low .r11 .W64
@[match_pattern] abbrev r12 := low .r12 .W64
@[match_pattern] abbrev r13 := low .r13 .W64
@[match_pattern] abbrev r14 := low .r14 .W64
@[match_pattern] abbrev r15 := low .r15 .W64

@[match_pattern] abbrev eax  := low .rax .W32
@[match_pattern] abbrev ebx  := low .rbx .W32
@[match_pattern] abbrev ecx  := low .rcx .W32
@[match_pattern] abbrev edx  := low .rdx .W32
@[match_pattern] abbrev esi  := low .rsi .W32
@[match_pattern] abbrev edi  := low .rdi .W32
@[match_pattern] abbrev esp  := low .rsp .W32
@[match_pattern] abbrev ebp  := low .rbp .W32
@[match_pattern] abbrev r8d  := low .r8  .W32
@[match_pattern] abbrev r9d  := low .r9  .W32
@[match_pattern] abbrev r10d := low .r10 .W32
@[match_pattern] abbrev r11d := low .r11 .W32
@[match_pattern] abbrev r12d := low .r12 .W32
@[match_pattern] abbrev r13d := low .r13 .W32
@[match_pattern] abbrev r14d := low .r14 .W32
@[match_pattern] abbrev r15d := low .r15 .W32

@[match_pattern] abbrev ax   := low .rax .W16
@[match_pattern] abbrev bx   := low .rbx .W16
@[match_pattern] abbrev cx   := low .rcx .W16
@[match_pattern] abbrev dx   := low .rdx .W16
@[match_pattern] abbrev si   := low .rsi .W16
@[match_pattern] abbrev di   := low .rdi .W16
@[match_pattern] abbrev sp   := low .rsp .W16
@[match_pattern] abbrev bp   := low .rbp .W16
@[match_pattern] abbrev r8w  := low .r8  .W16
@[match_pattern] abbrev r9w  := low .r9  .W16
@[match_pattern] abbrev r10w := low .r10 .W16
@[match_pattern] abbrev r11w := low .r11 .W16
@[match_pattern] abbrev r12w := low .r12 .W16
@[match_pattern] abbrev r13w := low .r13 .W16
@[match_pattern] abbrev r14w := low .r14 .W16
@[match_pattern] abbrev r15w := low .r15 .W16

@[match_pattern] abbrev al   := low .rax .W8
@[match_pattern] abbrev bl   := low .rbx .W8
@[match_pattern] abbrev cl   := low .rcx .W8
@[match_pattern] abbrev dl   := low .rdx .W8
@[match_pattern] abbrev sil  := low .rsi .W8
@[match_pattern] abbrev dil  := low .rdi .W8
@[match_pattern] abbrev spl  := low .rsp .W8
@[match_pattern] abbrev bpl  := low .rbp .W8
@[match_pattern] abbrev r8b  := low .r8  .W8
@[match_pattern] abbrev r9b  := low .r9  .W8
@[match_pattern] abbrev r10b := low .r10 .W8
@[match_pattern] abbrev r11b := low .r11 .W8
@[match_pattern] abbrev r12b := low .r12 .W8
@[match_pattern] abbrev r13b := low .r13 .W8
@[match_pattern] abbrev r14b := low .r14 .W8
@[match_pattern] abbrev r15b := low .r15 .W8
end Reg
