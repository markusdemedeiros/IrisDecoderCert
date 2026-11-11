-- The reference semantics are taken from https://www.felixcloutier.com/x86/,
-- which itself is just extracted from https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html

import Kraken.Attribute
import Kraken.Float32Fma
import Kraken.Layout
import Kraken.Mem
import Kraken.X64.Syntax
import Lean
import Std

-- injective coercions only
attribute [-instance] BitVec.instNatCast
attribute [-instance] BitVec.instIntCast
instance : Coe Bool Nat where coe := Bool.toNat

namespace BitVec
def unsigned {w} (x : BitVec w) : Int := x.toNat
def signed {w} (x : BitVec w) : Int := x.toInt
@[kstep] def take {w} (x : BitVec w) (n : Nat) : BitVec n := x.extractLsb' 0 n
@[kstep] def drop {w} (x : BitVec w) (n : Nat) : BitVec (w - n) := x.extractLsb' n (w-n)
end BitVec
attribute [kstep]
  BitVec.extractLsb'
  BitVec.ofInt_add
  BitVec.ofInt_toInt
  BitVec.signed
  BitVec.truncate
def BitVec.replaceLow {w n} (old : BitVec w) (new : BitVec n) : BitVec w :=
  (BitVec.append (old.drop n) new).setWidth _

namespace Reg
@[kstep] def base {w} (r : Reg w) : Reg64 := match r with
  | .low r _ => r
  | .ah => .rax | .bh => .rbx | .ch => .rcx | .dh => .rdx

@[kstep] def offset {w} (r : Reg w) : Nat := match r with
  | .low _ _ => 0
  | .ah | .bh | .ch | .dh => 8
end Reg

namespace AvxReg
def base {w} (r : AvxReg w) : RegMm := match r with
  | .xmm r => r
  | .ymm r => r
  | .zmm r => r
end AvxReg

structure Reg64s where
  rax : UInt64 := 0
  rbx : UInt64 := 0
  rcx : UInt64 := 0
  rdx : UInt64 := 0
  rsi : UInt64 := 0
  rdi : UInt64 := 0
  rsp : UInt64 := 0
  rbp : UInt64 := 0
  r8  : UInt64 := 0
  r9  : UInt64 := 0
  r10 : UInt64 := 0
  r11 : UInt64 := 0
  r12 : UInt64 := 0
  r13 : UInt64 := 0
  r14 : UInt64 := 0
  r15 : UInt64 := 0
  deriving Repr, BEq, DecidableEq, Hashable, Hashable, Lean.ToExpr

/-- The register file's own width is the literal 64: stating it as `BitVec 64`
makes every consumer store the literal as the width index, the one spelling
`grind`'s congruence and `bv_decide` read syntactically. `Width.W64.type` is
definitionally the same type; an index spelled through it depends on which
reduction path the elaborator took (`Width.W64.bits`, a stranded `bits` match,
or `64`), and syntactically distinct spellings of one index split atoms. -/
@[kstep] def Reg64s.get64 (s : Reg64s) (r : Reg64) : BitVec 64 := UInt64.toBitVec (match r with
  | .rax => s.rax | .rbx => s.rbx | .rcx => s.rcx | .rdx => s.rdx
  | .rsi => s.rsi | .rdi => s.rdi | .rsp => s.rsp | .rbp => s.rbp
  | .r8  => s.r8  | .r9  => s.r9  | .r10 => s.r10 | .r11 => s.r11
  | .r12 => s.r12 | .r13 => s.r13 | .r14 => s.r14 | .r15 => s.r15)

@[kstep] def Reg64s.set64 (regs : Reg64s) (r : Reg64) (v : BitVec 64) : Reg64s :=
  let  v := UInt64.ofBitVec v
  match r with
  | .rax => { regs with rax := v } | .rbx => { regs with rbx := v }
  | .rcx => { regs with rcx := v } | .rdx => { regs with rdx := v }
  | .rsi => { regs with rsi := v } | .rdi => { regs with rdi := v }
  | .rsp => { regs with rsp := v } | .rbp => { regs with rbp := v }
  | .r8  => { regs with r8  := v } | .r9  => { regs with r9  := v }
  | .r10 => { regs with r10 := v } | .r11 => { regs with r11 := v }
  | .r12 => { regs with r12 := v } | .r13 => { regs with r13 := v }
  | .r14 => { regs with r14 := v } | .r15 => { regs with r15 := v }

@[kstep] def Reg64s.get (s : Reg64s) {w} (r : Reg w) : w.type :=
  ((s.get64 r.base).drop r.offset).take w.bits
  -- BitVec because it may be signed or unsigned depending on context

@[kstep] def Reg64s.set (s : Reg64s) {w} (r : Reg w) (v : w.type) : Reg64s := match r with
  | .low r .W64 => s.set64 r v
  | .low r .W32 => s.set64 r (v.zeroExtend _)
  | .low r w => s.set64 r ((s.get64 r).replaceLow v)
  | .ah | .bh | .ch | .dh => let old := s.get64 r.base;
    s.set64 r.base (old.replaceLow (BitVec.append v (s.get (.low r.base .W8))))

def ZmmValue : Type := BitVec 512
  deriving Repr, BEq, DecidableEq, Hashable, Hashable, Lean.ToExpr

def zmmZero : ZmmValue := 0#512

structure RegZmms where
  zmm0  : ZmmValue := zmmZero
  zmm1  : ZmmValue := zmmZero
  zmm2  : ZmmValue := zmmZero
  zmm3  : ZmmValue := zmmZero
  zmm4  : ZmmValue := zmmZero
  zmm5  : ZmmValue := zmmZero
  zmm6  : ZmmValue := zmmZero
  zmm7  : ZmmValue := zmmZero
  zmm8  : ZmmValue := zmmZero
  zmm9  : ZmmValue := zmmZero
  zmm10 : ZmmValue := zmmZero
  zmm11 : ZmmValue := zmmZero
  zmm12 : ZmmValue := zmmZero
  zmm13 : ZmmValue := zmmZero
  zmm14 : ZmmValue := zmmZero
  zmm15 : ZmmValue := zmmZero
  zmm16 : ZmmValue := zmmZero
  zmm17 : ZmmValue := zmmZero
  zmm18 : ZmmValue := zmmZero
  zmm19 : ZmmValue := zmmZero
  zmm20 : ZmmValue := zmmZero
  zmm21 : ZmmValue := zmmZero
  zmm22 : ZmmValue := zmmZero
  zmm23 : ZmmValue := zmmZero
  zmm24 : ZmmValue := zmmZero
  zmm25 : ZmmValue := zmmZero
  zmm26 : ZmmValue := zmmZero
  zmm27 : ZmmValue := zmmZero
  zmm28 : ZmmValue := zmmZero
  zmm29 : ZmmValue := zmmZero
  zmm30 : ZmmValue := zmmZero
  zmm31 : ZmmValue := zmmZero
  deriving Repr, BEq, DecidableEq, Hashable, Hashable, Lean.ToExpr

def RegZmms.get512 (s : RegZmms) (r : RegMm) : AvxWidth.W512.type := (match r with
  | .mm0  => s.zmm0  | .mm1  => s.zmm1  | .mm2  => s.zmm2  | .mm3  => s.zmm3
  | .mm4  => s.zmm4  | .mm5  => s.zmm5  | .mm6  => s.zmm6  | .mm7  => s.zmm7
  | .mm8  => s.zmm8  | .mm9  => s.zmm9  | .mm10 => s.zmm10 | .mm11 => s.zmm11
  | .mm12 => s.zmm12 | .mm13 => s.zmm13 | .mm14 => s.zmm14 | .mm15 => s.zmm15
  | .mm16 => s.zmm16 | .mm17 => s.zmm17 | .mm18 => s.zmm18 | .mm19 => s.zmm19
  | .mm20 => s.zmm20 | .mm21 => s.zmm21 | .mm22 => s.zmm22 | .mm23 => s.zmm23
  | .mm24 => s.zmm24 | .mm25 => s.zmm25 | .mm26 => s.zmm26 | .mm27 => s.zmm27
  | .mm28 => s.zmm28 | .mm29 => s.zmm29 | .mm30 => s.zmm30 | .mm31 => s.zmm31)

def RegZmms.set512 (regs : RegZmms) (r : RegMm) (v : AvxWidth.W512.type) : RegZmms :=
  match r with
  | .mm0  => { regs with zmm0  := v } | .mm1  => { regs with zmm1  := v }
  | .mm2  => { regs with zmm2  := v } | .mm3  => { regs with zmm3  := v }
  | .mm4  => { regs with zmm4  := v } | .mm5  => { regs with zmm5  := v }
  | .mm6  => { regs with zmm6  := v } | .mm7  => { regs with zmm7  := v }
  | .mm8  => { regs with zmm8  := v } | .mm9  => { regs with zmm9  := v }
  | .mm10 => { regs with zmm10 := v } | .mm11 => { regs with zmm11 := v }
  | .mm12 => { regs with zmm12 := v } | .mm13 => { regs with zmm13 := v }
  | .mm14 => { regs with zmm14 := v } | .mm15 => { regs with zmm15 := v }
  | .mm16 => { regs with zmm16 := v } | .mm17 => { regs with zmm17 := v }
  | .mm18 => { regs with zmm18 := v } | .mm19 => { regs with zmm19 := v }
  | .mm20 => { regs with zmm20 := v } | .mm21 => { regs with zmm21 := v }
  | .mm22 => { regs with zmm22 := v } | .mm23 => { regs with zmm23 := v }
  | .mm24 => { regs with zmm24 := v } | .mm25 => { regs with zmm25 := v }
  | .mm26 => { regs with zmm26 := v } | .mm27 => { regs with zmm27 := v }
  | .mm28 => { regs with zmm28 := v } | .mm29 => { regs with zmm29 := v }
  | .mm30 => { regs with zmm30 := v } | .mm31 => { regs with zmm31 := v }

def RegZmms.get (s : RegZmms) {w} (r : AvxReg w) : w.type :=
  (s.get512 r.base).take w.bits

def RegZmms.set (s : RegZmms) {w} (r : AvxReg w) (v : w.type) : RegZmms := match r with
  | .zmm r => s.set512 r v
  | .ymm r => s.set512 r (v.zeroExtend _)
  | .xmm r => s.set512 r (v.zeroExtend _)

def RegZmms.setLegacy (s : RegZmms) {w} (r : AvxReg w) (v : w.type) : RegZmms := match r with
  | .zmm r => s.set512 r v  -- impossible
  | .ymm r => s.set512 r ((s.get512 r).replaceLow v)  -- impossible
  | .xmm r => s.set512 r ((s.get512 r).replaceLow v)

/-- `vzeroupper` in 64-bit mode: bits 511:128 of zmm0–15 are cleared, and
zmm16–31 are left alone. -/
def RegZmms.zeroUpper (s : RegZmms) : RegZmms :=
  let z (v : ZmmValue) : ZmmValue := (BitVec.setWidth 128 v).setWidth 512
  { s with
    zmm0 := z s.zmm0, zmm1 := z s.zmm1, zmm2 := z s.zmm2, zmm3 := z s.zmm3,
    zmm4 := z s.zmm4, zmm5 := z s.zmm5, zmm6 := z s.zmm6, zmm7 := z s.zmm7,
    zmm8 := z s.zmm8, zmm9 := z s.zmm9, zmm10 := z s.zmm10, zmm11 := z s.zmm11,
    zmm12 := z s.zmm12, zmm13 := z s.zmm13, zmm14 := z s.zmm14, zmm15 := z s.zmm15 }

@[kstep]
def BitVec.toAddressSize [address_size: AddressSize] (w: BitVec 64): BitVec address_size.address_size.bits :=
  w.take address_size.address_size.bits

-- TODO: consider adding a `split` helper to switch representations between
-- u128, 4xu32, etc.
def BitVec.packedBinOp {w : Nat} (c : Nat) (op : BitVec c → BitVec c → BitVec c) (a b : BitVec w) : BitVec w :=
  if _ : c = 0 ∨ w < c then
    a -- Fallback/Base case (w = 0 or invalid chunk size)
  else
    -- Extract the lowest chunk
    let a_low := a.take c
    let b_low := b.take c
    let res_low := op a_low b_low

    -- Recursively process the remaining high bits
    let a_high := a.drop c
    let b_high := b.drop c
    let res_high := BitVec.packedBinOp c op a_high b_high

    -- Recombine: res_high is the high part, res_low is the low part
    (BitVec.append res_high res_low).setWidth _
termination_by w
decreasing_by omega

def BitVec.toFloat32 (v : BitVec 32) : Float32 :=
  Float32.ofBits (UInt32.ofBitVec v)

def Float32.toBitVec (f : Float32) : BitVec 32 :=
  UInt32.toBitVec (Float32.toBits f)

/-- The three-operand sibling of `packedBinOp`: `op` on each `c`-bit chunk of
`a`, `b` and `d`. -/
def BitVec.packedTernOp {w : Nat} (c : Nat) (op : BitVec c → BitVec c → BitVec c → BitVec c)
    (a b d : BitVec w) : BitVec w :=
  if _ : c = 0 ∨ w < c then
    a
  else
    let res_low := op (a.take c) (b.take c) (d.take c)
    let res_high := BitVec.packedTernOp c op (a.drop c) (b.drop c) (d.drop c)
    (BitVec.append res_high res_low).setWidth _
termination_by w
decreasing_by omega

/-! Single-precision lane arithmetic, on the bits of a lane. The model rounds
to nearest, ties to even (MXCSR is not modeled). -/

/-- `a + b` on single-precision lanes. -/
def BitVec.f32add (a b : BitVec 32) : BitVec 32 :=
  Float32.toBitVec (BitVec.toFloat32 a + BitVec.toFloat32 b)

/-- `a * b` on single-precision lanes. -/
def BitVec.f32mul (a b : BitVec 32) : BitVec 32 :=
  Float32.toBitVec (BitVec.toFloat32 a * BitVec.toFloat32 b)

/-- `a * b + c` on single-precision lanes, rounded once. -/
def BitVec.f32fma (a b c : BitVec 32) : BitVec 32 :=
  Float32.toBitVec
    (Kraken.Float32.fma (BitVec.toFloat32 a) (BitVec.toFloat32 b) (BitVec.toFloat32 c))

/-- `a - b` on single-precision lanes. -/
def BitVec.f32sub (a b : BitVec 32) : BitVec 32 :=
  Float32.toBitVec (BitVec.toFloat32 a - BitVec.toFloat32 b)

/-- `a / b` on single-precision lanes. -/
def BitVec.f32div (a b : BitVec 32) : BitVec 32 :=
  Float32.toBitVec (BitVec.toFloat32 a / BitVec.toFloat32 b)

/-- `minss`: `a` when `a < b`, otherwise `b`. So a NaN in either operand, or
two zeros of either sign, give `b`, as the hardware does. -/
def BitVec.f32min (a b : BitVec 32) : BitVec 32 :=
  if BitVec.toFloat32 a < BitVec.toFloat32 b then a else b

/-- Correctly rounded square root on a single-precision lane. -/
def BitVec.f32sqrt (a : BitVec 32) : BitVec 32 :=
  Float32.toBitVec (BitVec.toFloat32 a).sqrt

def BitVec.toFloat64 (v : BitVec 64) : Float :=
  Float.ofBits (UInt64.ofBitVec v)

def Float.toBitVec64 (f : Float) : BitVec 64 :=
  UInt64.toBitVec (Float.toBits f)

/-- `a * b` on double-precision lanes. -/
def BitVec.f64mul (a b : BitVec 64) : BitVec 64 :=
  Float.toBitVec64 (BitVec.toFloat64 a * BitVec.toFloat64 b)

/-- An unpacked float rounded (to nearest, ties to even) to the format `spec`, in the canonical
form that `UnpackedFloat.pack spec` expects. Infinities, NaN and zeros are unchanged. Values
that overflow `spec` are packed as infinity by `pack`. -/
def Kraken.roundUnpacked (spec : Float.Model.Format) :
    Float.Model.UnpackedFloat → Float.Model.UnpackedFloat
  | .finite s m e _ => Float.Model.UnpackedFloat.round spec s m e
  | f => f

/-- `cvtss2sd`/`cvtps2pd` on one lane: the exact widening, defined through Lean core's float
model (every binary32 value is a binary64 value, so the rounding is exact; a NaN becomes the
canonical quiet NaN `0x7FF8000000000000`). Unlike `Float32.toFloat` (an opaque C cast), this
reduces in the kernel. -/
def BitVec.f32to64 (a : BitVec 32) : BitVec 64 :=
  Float.Model.UnpackedFloat.pack .binary64
    (Kraken.roundUnpacked .binary64 (Float.Model.UnpackedFloat.unpack .binary32 a))

/-- `cvtsd2ss` on one lane, rounded to nearest even, defined through Lean core's float model
(overflow gives infinity, a NaN becomes the canonical quiet NaN `0x7FC00000`). -/
def BitVec.f64to32 (a : BitVec 64) : BitVec 32 :=
  Float.Model.UnpackedFloat.pack .binary32
    (Kraken.roundUnpacked .binary32 (Float.Model.UnpackedFloat.unpack .binary64 a))

/-- `cvtsi2ss`: a signed integer (32 or 64 bits) rounded to single precision. -/
def BitVec.sitof32 {n} (a : BitVec n) : BitVec 32 :=
  Float32.toBitVec (Int64.ofInt a.toInt).toFloat32

/-- The nonnegative rational `m * 2 ^ e` rounded to the nearest integer, ties to even. -/
def Kraken.roundNatRNE (m : Nat) (e : Int) : Nat :=
  if 0 ≤ e then m * 2 ^ e.toNat else
  let k := (-e).toNat
  let q := m / 2 ^ k
  let r := m % 2 ^ k
  if 2 ^ k < 2 * r ∨ (2 * r = 2 ^ k ∧ q % 2 = 1) then q + 1 else q

/-- `cvtss2si` with a 64-bit destination: the float rounded to the nearest integer, ties to
even, defined through Lean core's float model. A NaN, an infinity, or a value whose rounded
result is outside the signed 64-bit range gives the integer indefinite `0x8000000000000000`.
MXCSR is not modeled: the default rounding mode (to nearest even) is assumed, and the
floating-point exceptions are masked. -/
def BitVec.f32toi64 (a : BitVec 32) : BitVec 64 :=
  match Float.Model.UnpackedFloat.unpack .binary32 a with
  | .finite s m e _ =>
    let v : Int := s.apply (Kraken.roundNatRNE m e)
    if -2 ^ 63 ≤ v ∧ v < 2 ^ 63 then BitVec.ofInt 64 v else 0x8000000000000000#64
  | .zero _ => 0#64
  | _ => 0x8000000000000000#64

/-- The outcome of an IEEE comparison: `(unordered, less, equal)`. Exactly one
holds, or none when `a > b`. -/
def BitVec.f32cmp (a b : BitVec 32) : Bool × Bool × Bool :=
  let x := BitVec.toFloat32 a
  let y := BitVec.toFloat32 b
  let un := x.isNaN || y.isNaN
  (un, !un && x < y, !un && x == y)

def BitVec.f64cmp (a b : BitVec 64) : Bool × Bool × Bool :=
  let x := BitVec.toFloat64 a
  let y := BitVec.toFloat64 b
  let un := x.isNaN || y.isNaN
  (un, !un && x < y, !un && x == y)

/-- The `cmpss` predicates 0..31 (bit 4 only selects signaling behavior,
which is not modeled since exceptions are masked). -/
def BitVec.f32cmpPred (pred : UInt8) (a b : BitVec 32) : Bool :=
  let (un, lt, eq) := BitVec.f32cmp a b
  let gt := !un && !lt && !eq
  match pred.toNat % 16 with
  | 0 => eq | 1 => lt | 2 => lt || eq | 3 => un
  | 4 => !eq | 5 => !lt | 6 => !(lt || eq) | 7 => !un
  | 8 => eq || un | 9 => lt || un | 10 => !gt | 11 => false
  | 12 => !eq && !un | 13 => gt || eq | 14 => gt | _ => true

/-- The 32-bit element `i` of `x`. -/
abbrev BitVec.dw {n} (x : BitVec n) (i : Nat) : BitVec 32 := x.extractLsb' (32 * i) 32

/-- The 64-bit element `i` of `x`. -/
abbrev BitVec.qw {n} (x : BitVec n) (i : Nat) : BitVec 64 := x.extractLsb' (64 * i) 64

/-- `packedBinOp` whose lane operation also receives the lane index. -/
def BitVec.packedBinOpIdx {w : Nat} (c : Nat) (op : Nat → BitVec c → BitVec c → BitVec c)
    (a b : BitVec w) (i : Nat := 0) : BitVec w :=
  if _ : c = 0 ∨ w < c then
    a
  else
    let res_low := op i (a.take c) (b.take c)
    let res_high := BitVec.packedBinOpIdx c op (a.drop c) (b.drop c) (i + 1)
    (BitVec.append res_high res_low).setWidth _
termination_by w
decreasing_by omega

/-- One 128-bit lane of `haddps`. -/
def BitVec.haddps128 (a b : BitVec 128) : BitVec 128 :=
  BitVec.f32add (b.dw 2) (b.dw 3) ++ BitVec.f32add (b.dw 0) (b.dw 1)
    ++ BitVec.f32add (a.dw 2) (a.dw 3) ++ BitVec.f32add (a.dw 0) (a.dw 1)

/-- One 128-bit lane of `pshufd`/`vpermilps`: element `i` is element
`imm[2i+1:2i]` of `a`. -/
def BitVec.pshufd128 (imm : UInt8) (a : BitVec 128) : BitVec 128 :=
  let pick (k : Nat) : BitVec 32 := a.dw ((imm.toNat >>> k) % 4)
  pick 6 ++ pick 4 ++ pick 2 ++ pick 0

/-- `insertps`: element `imm[5:4]` of `a` replaced by `v`, then the elements
selected by `imm[3:0]` zeroed. -/
def BitVec.insertps (imm : UInt8) (a : BitVec 128) (v : BitVec 32) : BitVec 128 :=
  let d := (imm.toNat >>> 4) % 4
  let el (i : Nat) : BitVec 32 :=
    if (imm.toNat >>> i) % 2 = 1 then 0#32 else if i = d then v else a.dw i
  el 3 ++ el 2 ++ el 1 ++ el 0

/-- One 128-bit lane of `shufps`: the low two floats of the result come from
`a` and the high two from `b`, each picked by two bits of `imm`. -/
def BitVec.shufps128 (imm : UInt8) (a b : BitVec 128) : BitVec 128 :=
  let pick (x : BitVec 128) (k : Nat) : BitVec 32 :=
    x.extractLsb' (32 * ((imm.toNat >>> k) % 4)) 32
  pick b 6 ++ pick b 4 ++ pick a 2 ++ pick a 0

/-- One 128-bit lane of `pshufb`: byte `i` is zero when bit 7 of byte `i` of `ctl` is set, and
otherwise byte `ctl[i] & 15` of `a`. -/
def BitVec.pshufb128 (a ctl : BitVec 128) : BitVec 128 :=
  BitVec.packedBinOp 8
    (fun c _ => if c.msb then 0#8 else a.extractLsb' (8 * (c.toNat % 16)) 8) ctl ctl

structure StatusFlags where
  cf : Bool
  pf : Bool
  af : Bool
  zf : Bool
  sf : Bool
  of : Bool
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

/-- The `(u)comiss`/`(u)comisd` flags: ZF, PF, CF are `111` unordered, `000`
greater, `001` less, `100` equal; OF, SF, AF are cleared. -/
def StatusFlags.ofFCmp (c : Bool × Bool × Bool) : StatusFlags :=
  let (un, lt, eq) := c
  { zf := un || eq, pf := un, cf := un || lt, of := false, sf := false, af := false }

abbrev DataMem := Mem 64
instance : Repr DataMem where reprPrec _ _ := "<opaque memory>"
structure MachineData where -- does not include code or program position
  regs : Reg64s := {}
  zmms : RegZmms := {}
  status : StatusFlags := .mk false false false false false false
  dmem : DataMem := ∅
  deriving Repr, BEq, DecidableEq

-- We only allow nondeterministic choices for a fixed set of types.
class inductive NondetSupportingType : Type -> Type
  | bitvec (w : Width) : NondetSupportingType w.type
  | avx_bitvec (aw : AvxWidth) : NondetSupportingType aw.type
  | bool : NondetSupportingType Bool
  | statusFlags : NondetSupportingType StatusFlags

def NondetSupportingType.from_hash {α} [t : NondetSupportingType α] (h : UInt64) : α :=
  match t with
  | .bool => h % 2 != 0
  | .statusFlags => let h := h.toBitVec; (.mk h[0] h[1] h[2] h[3] h[4] h[5])
  | .bitvec w => h.toBitVec.setWidth w.bits
  | .avx_bitvec w => h.toBitVec.setWidth w.bits

instance (w : Width) : NondetSupportingType w.type := .bitvec w
instance (w : AvxWidth) : NondetSupportingType w.type := .avx_bitvec w
instance : NondetSupportingType Bool := .bool
instance : NondetSupportingType StatusFlags := .statusFlags

inductive Effects
  | done (a : MachineData × Int64)
  | unimplemented (msg : String)
  | gp_unaligned (addr : BitVec 64) (w : Nat)
  -- A trap instruction (`ud1`, `ud2`, `int3`) raised its exception: like a
  -- faulting access, the step has no successor state.
  | trap (what : String)
  -- loads and stores *outside* the data memory, eg. MMIO, might still affect the data memory:
  -- for instance, MMIO reads/writes at certain device register addresses might change what
  -- data memory the process logically owns vs what memory is owned by devices
  | nonmem_load (dmem : DataMem) (addr : BitVec 64) (w : Width) (ret : w.type → DataMem → Effects)
  | nonmem_store (dmem : DataMem) (addr : BitVec 64) {w : Width} (v : w.type) (ret: DataMem → Effects)
  | undefined {α : Type} [NondetSupportingType α] (ret : α → Effects)
  | require_read_access (addr : BitVec 64) (w : Width) (ok : Unit → Effects)
  | require_write_access (addr : BitVec 64) (w : Width) (ok : Unit → Effects)
  | require_exec_access (p: Std.Rco Int64) (ok : Unit → Effects)
export Effects (unimplemented nonmem_load nonmem_store undefined require_read_access require_write_access require_exec_access)

-- the unused `Std.Rco Int64` argument and the unmodified `MachineData` return
-- value are present for uniformity with RegOrMem.interp
@[kstep] def Reg.interp {w} (r : Reg w) (s : MachineData) (_ : Std.Rco Int64)
  (ret : w.type → MachineData → Effects) : Effects :=
  ret (s.regs.get r) s

-- Since MMIO can cause devices to do arbitrary actions, a load might actually
-- *modify* memory. For instance:
-- A TEST instruction might load a flag from an MMIO address and bitwise-and it with
-- an immediate, and if the result is non-zero, it might mean that some device has
-- finished processing a buffer and therefore now passes ownership of that buffer
-- to the CPU.
-- Note that `ret` takes a whole `MachineData` instead of only `DataMem`, which
-- provides a bit more flexibility than we need: MachineData.load might change
-- dmem, but will not change the registers or status flags.
-- But this superfluous flexibility helps us simplify the state-threading:
-- Instead of writing `fun v dmem => ... { s with dmem } ...` everywhere, we
-- can just write `fun v s => ...` and the new `s` will shadow the old `s`.
def MachineData.load
  (s : MachineData) (addr : BitVec 64) (w : Width)
  (ret : w.type → MachineData → Effects): Effects :=
  require_read_access addr w (fun _unit =>
    match Mem.loadInt s.dmem addr w.bytes with
    | .some i => ret (.ofInt _ i) s
    | .none => nonmem_load s.dmem addr w (fun v dmem => ret v { s with dmem }))

-- Alternatively, we could define this in terms of BitVecs without %:
-- (addr &&& BitVec.ofNat 64 (bytes - 1)) == 0#64
def isAligned (bytes : Nat) (addr : BitVec 64) : Bool :=
  addr.toNat % bytes == 0

-- Legacy SSE instructions are generally stricter about alignment requirements,
-- while AVX (VEX-encoded) instructions can mostly deal with unaligned
-- addresses (https://discourse.llvm.org/t/memory-alignment-model-on-avx-avx2-and-avx-512-targets/34705).
-- For this reason we default checkAlign to false.
def MachineData.loadAvx
  (s : MachineData) (addr : BitVec 64) (w : AvxWidth)
  (ret : w.type → MachineData → Effects) (checkAlign : Bool := false) : Effects :=
  if checkAlign && !(isAligned w.bytes addr) then
    .gp_unaligned addr w.bytes
  else
    require_read_access addr .W64 (fun _unit =>
  match Mem.loadInt s.dmem addr w.bytes with
      | .some i => ret (.ofInt _ i) s
      | .none => unimplemented "AVX nonmem load not supported")

def MachineData.store (s : MachineData) (addr : BitVec 64) {w : Width} (v : w.type) (ret: MachineData → Effects) : Effects :=
  require_write_access addr w (fun _unit =>
    match Mem.loadInt s.dmem addr w.bytes with
    | .some _ =>
        ret { s with dmem := Mem.storeInt s.dmem addr w.bytes v.toInt }
    | .none => nonmem_store s.dmem addr v (fun dmem' => ret { s with dmem := dmem' }))

def MachineData.storeAvx (s : MachineData) (addr : BitVec 64) {w : AvxWidth} (v : w.type) (ret: MachineData → Effects) (checkAlign : Bool := false) : Effects :=
  if checkAlign && !(isAligned w.bytes addr) then
    .gp_unaligned addr w.bytes
  else
    require_write_access addr .W64 (fun _unit =>
  match Mem.loadInt s.dmem addr w.bytes with
      | .some _ =>
          ret { s with dmem := Mem.storeInt s.dmem addr w.bytes v.toInt }
      | .none => unimplemented "AVX nonmem store not supported")

class Labels where label : Label → Int64
export Labels (label)

@[kstep] def ConstExpr.interp [Labels] : ConstExpr → Std.Rco _root_.Int64 → _root_.Int64
  | .label l, _ => Labels.label l
  | .int64 i, _ => i
  | .before_current_instruction, r => r.lower
  | .after_current_instruction, r => r.upper
  | .add e1 e2, p => e1.interp p + e2.interp p
  | .sub e1 e2, p => e1.interp p - e2.interp p

@[kstep] def AddrExpr.interp [Labels] [address_size : AddressSize] (a : AddrExpr) (s : Reg64s) (p : Std.Rco Int64) :=
  let base := match a.base with
              | .some (.reg r) => (s.get64 r).toAddressSize.signed
              | .some .rip => p.upper.toInt
              | .none => 0
  let idx := match a.idx with
             | .some ⟨r, c⟩ => (s.get64 r).toAddressSize.signed * c.bytes
             | .none => 0
  BitVec.ofInt address_size.address_size.bits (base + idx + (a.disp.interp p).toInt)

@[kstep] def RegOrMem.interp {w} [Labels] [AddressSize]
  (o : RegOrMem w) (s : MachineData) (p : Std.Rco Int64)
  (ret : w.type → MachineData → Effects) :=
match o with
  | .reg r => ret (s.regs.get r) s
  | .mem a => s.load ((a.interp s.regs p).zeroExtend _) w ret

def AvxRegOrMem.interp {w} [Labels] [AddressSize]
  (o : AvxRegOrMem w) (s : MachineData) (p : Std.Rco Int64)
  (ret : w.type → MachineData → Effects) (checkAlign : Bool := false) :=
match o with
  | .avx r => ret (s.zmms.get r) s
  | .mem a => s.loadAvx ((a.interp s.regs p).zeroExtend _) w ret checkAlign

/-- A scalar read of an xmm-or-memory operand: the low `n` bits of the
register, or an `n`-bit memory load (`m32`/`m64` operands, which need no
alignment). -/
def AvxRegOrMem.interpLow [Labels] [AddressSize]
  (o : AvxRegOrMem .W128) (n : Width) (s : MachineData) (p : Std.Rco Int64)
  (ret : n.type → MachineData → Effects) : Effects :=
match o with
  | .avx r => ret ((s.zmms.get r).setWidth n.bits) s
  | .mem a => s.load ((a.interp s.regs p).zeroExtend _) n ret

@[kstep]
def MachineData.setReg (s : MachineData) {w} (r : Reg w) (v : w.type) : MachineData :=
  { s with regs := s.regs.set r v }

def MachineData.setAvxReg (s : MachineData) {w : AvxWidth} (r : AvxReg w) (v : w.type) : MachineData :=
  { s with zmms := s.zmms.set r v }

def MachineData.setAvxLegacyReg (s : MachineData) {w : AvxWidth} (r : AvxReg w) (v : w.type) : MachineData :=
  { s with zmms := s.zmms.setLegacy r v }

@[kstep]
def MachineData.set {w} [Labels] [AddressSize] (s : MachineData) (d : Dst w) (v : w.type) (p : Std.Rco Int64) (ret : MachineData → Effects) : Effects :=
  match d with
  | .reg r => ret (s.setReg r v)
  | .mem a => s.store ((a.interp s.regs p).zeroExtend _) v ret

def MachineData.setAvx {aw} [Labels] [AddressSize] (s : MachineData) (d : AvxDst aw) (v : aw.type) (p : Std.Rco Int64) (ret : MachineData → Effects) (checkAlign : Bool := false) : Effects :=
match d with
  | .avx r => ret (s.setAvxReg r v)
  | .mem a => s.storeAvx ((a.interp s.regs p).zeroExtend _) v ret checkAlign

def MachineData.setAvxLegacy {w} [Labels] [AddressSize] (s : MachineData) (d : AvxDst w) (v : w.type) (p : Std.Rco Int64) (ret : MachineData → Effects) (checkAlign : Bool := false) : Effects :=
match d with
  | .avx r => ret (s.setAvxLegacyReg r v)
  | .mem a => s.storeAvx ((a.interp s.regs p).zeroExtend _) v ret checkAlign

@[kstep] def Operand.interp {w} [Labels] [AddressSize]
  (o : Operand w) (s : MachineData) (p : Std.Rco Int64)
  (ret : w.type → MachineData → Effects) :=
  match o with
  | regOrMem rm => rm.interp s p ret
  | .imm v => ret ((v.interp p).toBitVec.truncate _) s
  -- we rely on assemblers erroring out on too-large immediates in uniform ops

def AvxOperand.interp {aw} [Labels] [AddressSize]
  (o : AvxOperand aw) (s : MachineData) (p : Std.Rco Int64)
  (ret : aw.type → MachineData → Effects) (checkAlign : Bool := false) :=
match o with
  | regOrMem rm => rm.interp s p ret checkAlign

@[kstep]
def CondCode.interp (cc : CondCode) (s : StatusFlags) : Bool := match cc with
  | .z  => s.zf | .nz => !s.zf | .c  => s.cf | .nc => !s.cf
  | .a  => !s.cf && !s.zf | .be => s.cf || s.zf
  | .l => s.sf != s.of | .le => (s.sf != s.of) || s.zf
  | .ge => s.sf == s.of | .g => !s.zf && (s.sf == s.of)
  | .p => s.pf | .np => !s.pf
  | .s => s.sf | .ns => !s.sf

@[kstep] def ShiftCountExpr.interp [Labels] (c : ShiftCountExpr) (s : MachineData) (p : Std.Rco Int64) := match c with
  | .cl => s.regs.rcx.toBitVec.take 8
  | .imm8 v => (v.interp p).toBitVec.take _
@[kstep] def ShiftCountExpr.interpMasked [Labels] (c : ShiftCountExpr) (s : MachineData) (p : Std.Rco Int64) (w : Width) : Nat :=
  (c.interp s p).toNat &&& match w with | .W64 => 0x3f | _ => 0x1f -- "masked to 5 bits (or 6 bits with a 64-bit operand)"

def RelRegOrMem.interp [Labels] [AddressSize]
  (o : RelRegOrMem) (s : MachineData) (p : Std.Rco Int64)
  (ret : BitVec 64 → MachineData → Effects) :=
  match o with
  | .rel c => ret (p.upper + c.interp p).toBitVec s
  | .reg r => ret (s.regs.get r) s
  | .mem a => s.load ((a.interp s.regs p).zeroExtend _) .W64 ret

structure StatusFlags.from_result.Remaining where
  cf : Bool
  af : Bool
  of : Bool
  deriving Repr, BEq, DecidableEq

-- TEMPORARY: definitions stolen from Lean 4.28's standard library, but with a
-- different name so that this file builds with both 4.27 and 4.28
namespace BitVec
def cpopNatRec_ {w} (x : BitVec w) (pos acc : Nat) : Nat :=
  match pos with
  | 0 => acc
  | n + 1 => x.cpopNatRec_ n (acc + (x.getLsbD n).toNat)

def cpop_ {w} (x : BitVec w) : BitVec w := BitVec.ofNat w (cpopNatRec_ x w 0)
end BitVec

@[kstep] def StatusFlags.from_result {w} (result : BitVec w) (f : from_result.Remaining) : StatusFlags :=
  { pf := (result.take 8).cpop_ % 2 == BitVec.zero _
    zf := result == BitVec.zero _
    sf := result.msb, cf := f.cf, af := f.af, of := f.of }



set_option maxHeartbeats 1000000
@[kstep] def Operation.interp [Labels] [address_size : AddressSize]
  {w} (i : Operation w) (p : Std.Rco Int64) (s : MachineData)
  (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects) : Effects :=
  match (generalizing := false) (motive := Operation w → Effects) i with
  | .mov dst src => src.interp s p (fun val s => s.set dst val p next)
  | .movsx dst src => src.interp s p (fun val s => s.set dst (val.signExtend _) p next)
  | .movzx dst src => src.interp s p (fun val s => s.set dst (val.zeroExtend _) p next)
  | .push src =>
    src.interp s p (fun v s =>
    let rsp := s.regs.get64 .rsp - w.bytesv
    -- The store precedes the rsp commit, so a faulting push leaves rsp at its
    -- original value, as a restartable fault requires.
    s.store rsp v (fun s => next { s with regs := s.regs.set64 .rsp rsp }))
  | .pop dst =>
    let rsp := s.regs.get64 .rsp
    s.load rsp w (fun val s =>
    let s := { s with regs := s.regs.set64 .rsp (rsp + w.bytesv) }
    s.set dst val p next)
  | .setcc cc dst =>
    s.set dst (cc.interp s.status) p next
  | .cmovcc cc dst src =>
    src.interp s p (fun src s =>
    let v := if cc.interp s.status then src else s.regs.get dst
    next (s.setReg dst v))
-- Arithmetic
  | .lea dst src => next (s.setReg dst ((src.interp s.regs p).zeroExtend _))
  | .add dst src =>
    src.interp s p (fun a s =>
    dst.interp s p (fun b s =>
    let v := a + b
    let status := .from_result v {
      cf := v.unsigned != a.unsigned + b.unsigned
      af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned,
      of := v.signed != a.signed + b.signed }
    { s with status }.set dst v p next))
  | .adc dst src =>
    src.interp s p (fun a s =>
    dst.interp s p (fun b s =>
    let c := s.status.cf
    let v := a + b + c
    let status := .from_result v {
      cf := v.unsigned != a.unsigned + b.unsigned + c
      af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned + c,
      of := v.signed != a.signed + b.signed + c }
    { s with status }.set dst v p next))
  | .adcx dst src =>
    src.interp s p (fun a s =>
    dst.interp s p (fun b s =>
    let v := a + b + s.status.cf
    let cf := v.unsigned != a.unsigned + b.unsigned + s.status.cf
    next { s with regs := s.regs.set dst v, status := { s.status with cf := cf }}))
  | .adox dst src =>
    src.interp s p (fun a s =>
    dst.interp s p (fun b s =>
    let v := a + b + s.status.of
    let of := v.unsigned != a.unsigned + b.unsigned + s.status.of
    next { s with regs := s.regs.set dst v, status := { s.status with of := of }}))
  | .inc dst =>
    dst.interp s p (fun a s =>
    let v := a + 1
    let status := .from_result v {
      cf := s.status.cf
      af := (v.take 4).unsigned != (a.take 4).unsigned + 1,
      of := v.signed != a.signed + 1 }
    { s with status }.set dst v p next)
  | .dec dst =>
    dst.interp s p (fun a s =>
    let v := a - 1
    let status := .from_result v {
      cf := s.status.cf
      af := (v.take 4).unsigned != (a.take 4).unsigned - 1,
      of := v.signed != a.signed - 1 }
    { s with status }.set dst v p next)
  | .neg dst =>
    dst.interp s p (fun b s =>
    let v := -b
    let status := .from_result v {
      cf := b != 0
      af := (b.take 4) != 0,
      of := v.signed != - b.signed }
    { s with status }.set dst v p next)
  | .sub dst src =>
    src.interp s p (fun a s =>
    dst.interp s p (fun b s =>
    let v := b - a
    let status := .from_result v {
      cf := v.unsigned != b.unsigned - a.unsigned
      af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned,
      of := v.signed != b.signed - a.signed }
    { s with status }.set dst v p next))
  | .sbb dst src =>
    src.interp s p (fun a s =>
    dst.interp s p (fun b s =>
    let c := s.status.cf
    let v := b - a - c
    let status := .from_result v {
      cf := v.unsigned != b.unsigned - a.unsigned - c
      af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned - c,
      of := v.signed != b.signed - a.signed - c }
    { s with status }.set dst v p next))
  | .cmp a b =>
    a.interp s p (fun a s =>
    b.interp s p (fun b s =>
    let v := a - b
    let status := .from_result v {
      cf := v.unsigned != a.unsigned - b.unsigned
      af := (v.take 4).unsigned != (a.take 4).unsigned - (b.take 4).unsigned,
      of := v.signed != a.signed - b.signed }
    next { s with status }))
  | .mul src =>
    let a := s.regs.get (Reg.low .rax w)
    src.interp s p (fun b s =>
    let v := a * b
    let vn := a.unsigned * b.unsigned
    let s := if w == .W8
      then s.setReg (.low .rax .W16) (.ofInt _ vn)
      else (s.setReg (.low .rax w) v).setReg (.low .rdx w) (.ofInt _ (vn >>> w.bits))
    undefined (λ sf => undefined (λ zf => undefined (λ af => undefined (λ pf =>
    next { s with status := { cf := v.unsigned != vn, pf, af, zf, sf, of := v.unsigned != vn }})))))
  | .mulx r_hi r_lo src1 =>
    src1.interp s p (fun a s =>
    let b := s.regs.get (.low .rdx w)
    let v := a.unsigned * b.unsigned
    let s := s.setReg r_lo (.ofInt _ v) -- if r_hi = r_li, hi is written:
    let s := s.setReg r_hi (.ofInt _ (v >>> w.bits))
    next s)
  -- imul1 and imul collectively describe variants of the same
  -- syntax level `imul` instruction, where imul1 is the 1-operand case
  | .imul1 src =>
    let a := s.regs.get (Reg.low .rax w)
    src.interp s p (fun b s =>
    let v := a.toInt * b.toInt
    let s := if w == .W8 then
      s.setReg (.low .rax .W16) (BitVec.ofInt 16 v)
    else
      let result := BitVec.ofInt (w.bits * 2) v
      let low := result.take w.bits
      let high := (result.drop w.bits).setWidth _
      (s.setReg (.low .rax w) low).setReg (.low .rdx w) high
    undefined (λ sf => undefined (λ zf => undefined (λ af => undefined (λ pf =>
    let low := BitVec.ofInt w.bits v
    let cf := v != low.toInt
    next { s with status := { cf := cf, pf, af, zf, sf, of := cf }})))))
  | .imul dst src1 src2 =>
    src1.interp s p (fun a s =>
    src2.interp s p (fun b s =>
    let v := a * b
    s.set (match (generalizing := false) (motive := Option (RegOrMem w) → RegOrMem w)
             dst with | .some dst => dst | _ => src1) v p (fun s =>
    let cf := v.signed != a.signed * b.signed
    undefined (λ sf => undefined (λ zf => undefined (λ af => undefined (λ pf =>
    next { s with status := { cf := cf, pf, af, zf, sf, of := cf }})))))))
  -- The dividend is `rdx:rax` (`ax` for `.W8`). A zero divisor or a quotient
  -- outside the destination's range raises #DE, a trap with no successor.
  -- `idiv` truncates toward zero (the remainder has the dividend's sign).
  -- All six status flags are undefined (one nondeterministic `StatusFlags`).
  | .div src =>
    src.interp s p (fun b s =>
    let n : Nat := if w == .W8 then (s.regs.get (.low .rax .W16)).toNat else
      (s.regs.get (.low .rdx w)).toNat * 2 ^ w.bits + (s.regs.get (.low .rax w)).toNat
    let d : Nat := b.toNat
    if d = 0 ∨ 2 ^ w.bits ≤ n / d then .trap "#DE" else
    let q := n / d
    let r := n % d
    let s := if w == .W8
      then s.setReg (.low .rax .W16) (.ofNat _ (r * 2 ^ 8 + q))
      else (s.setReg (.low .rax w) (.ofNat _ q)).setReg (.low .rdx w) (.ofNat _ r)
    undefined (λ (status : StatusFlags) => next { s with status }))
  | .idiv src =>
    src.interp s p (fun b s =>
    let n : Int := if w == .W8 then (s.regs.get (.low .rax .W16)).toInt else
      (s.regs.get (.low .rdx w)).toInt * 2 ^ w.bits + (s.regs.get (.low .rax w)).toNat
    let d : Int := b.toInt
    let q := n.tdiv d
    let r := n.tmod d
    if d = 0 ∨ q < -2 ^ (w.bits - 1) ∨ 2 ^ (w.bits - 1) ≤ q then .trap "#DE" else
    let s := if w == .W8
      then s.setReg (.low .rax .W16) (BitVec.ofInt 8 r ++ BitVec.ofInt 8 q)
      else (s.setReg (.low .rax w) (.ofInt _ q)).setReg (.low .rdx w) (.ofInt _ r)
    undefined (λ (status : StatusFlags) => next { s with status }))
-- Bitwise
  | .test a b =>
    a.interp s p (fun a s =>
    b.interp s p (fun b s =>
    let v := a &&& b
    undefined (fun af =>
    let status := .from_result v { cf := false, af, of := false}
    next { s with status})))
  | .and dst src | .or dst src | .xor dst src =>
    dst.interp s p (fun a s =>
    src.interp s p (fun b s =>
    let v := match i with | .and _ _ => a &&& b | .or _ _ => a ||| b | _ => a ^^^ b
    undefined (fun af =>
    let status := .from_result v { cf := false, of := false, af }
    { s with status }.set dst v p next)))
  | .not dst =>
    dst.interp s p (fun a s =>
    let v := ~~~a
    s.set dst v p next)
  | .shl dst count =>
    dst.interp s p (fun a s =>
    let count := count.interpMasked s p w
    if count == 0 then next s else
    let v := a <<< count
    undefined (λ af =>
    (λ setcf => if count < w.bits then setcf (a <<< (count-1)).msb else undefined setcf) (λ cf =>
    (λ setof => if count == 1 then setof (v.msb != a.msb) else undefined setof) (λ of =>
    { s with status := .from_result v { s.status with cf, af, of } }.set dst v p next))))
  | .shr dst count =>
    dst.interp s p (fun a s =>
    let count := count.interpMasked s p w
    if count == 0 then next s else
    let v := a.ushiftRight count
    undefined (λ af =>
    (λ setcf => if count < w.bits then setcf (a.getLsbD (count-1)) else undefined setcf) (λ cf =>
    (λ setof => if count == 1 then setof a.msb else undefined setof) (λ of =>
    { s with status := .from_result v { s.status with cf, af, of } }.set dst v p next))))
  | .sar dst count =>
    dst.interp s p (fun a s =>
    let count := count.interpMasked s p w
    if count == 0 then next s else
    let v := a.sshiftRight count
    undefined (λ af =>
    (λ setcf => if count < w.bits then setcf (a.getLsbD (count-1)) else undefined setcf) (λ cf =>
    (λ setof => if count == 1 then setof false else undefined setof) (λ of =>
    { s with status := .from_result v { s.status with cf, af, of } }.set dst v p next))))
  | .shrd dst src count =>
    dst.interp s p (fun a s =>
    src.interp s p (fun b s =>
    let count := count.interpMasked s p w
    if count == 0 then next s else
    let v := (((b.append a) >>> count).take w.bits).setWidth _
    (λ setstatus => if count >= w.bits then undefined setstatus else
      let cf := a.getLsbD (count-1)
      undefined (λ af =>
      (λ setof => if count == 1 then setof (v.msb != a.msb) else undefined setof) (λ of =>
      setstatus (.from_result v { cf, af, of})))) (λ status =>
    { s with status }.set dst v p next)))
  | .shld dst src count =>
    dst.interp s p (fun a s =>
    src.interp s p (fun b s =>
    let count := count.interpMasked s p w
    if count == 0 then next s else
    let v := (((a.append b) <<< count).drop w.bits).setWidth _
    (λ setstatus => if count >= w.bits then undefined setstatus else
      let cf := (a <<< (count-1)).msb
      undefined (λ af =>
      (λ setof => if count == 1 then setof (v.msb != a.msb) else undefined setof) (λ of =>
      setstatus (.from_result v { cf, af, of})))) (λ status =>
    { s with status }.set dst v p next)))
  | .rol dst count =>
    dst.interp s p (fun a s =>
    let count := count.interpMasked s p w
    if count == 0 then next s else
    let v := a.rotateLeft count
    let cf := v.getLsbD 0
    (λ setof => if count == 1 then setof (v.msb != a.msb) else undefined setof) (λ of =>
    { s with status := { s.status with cf, of } }.set dst v p next))
  | .ror dst count =>
    dst.interp s p (fun a s =>
    let count := count.interpMasked s p w
    if count == 0 then next s else
    let v := a.rotateRight count
    let cf := v.msb
    (λ setof => if count == 1 then setof (v.msb != a.msb) else undefined setof) (λ of =>
    { s with status := { s.status with cf, of } }.set dst v p next))
  | .rcr dst count =>
    dst.interp s p (fun a s =>
    let count := count.interpMasked s p w
    if count == 0 then next s else
    let t := (BitVec.ofBool s.status.cf ++ a).rotateRight count
    let (cf, v) := (t.msb, t.take w.bits)
    (λ setof => if count == 1 then setof (v.msb != a.msb) else undefined setof) (λ of =>
    { s with status := { s.status with cf, of } }.set dst v p next))
  | .rcl dst count =>
    dst.interp s p (fun a s =>
    let count := count.interpMasked s p w
    if count == 0 then next s else
    let t := (BitVec.ofBool s.status.cf ++ a).rotateLeft count
    let (cf, v) := (t.msb, t.take w.bits)
    (λ setof => if count == 1 then setof (v.msb != a.msb) else undefined setof) (λ of =>
    { s with status := { s.status with cf, of } }.set dst v p next))
  | .bswap dst =>
    let a := s.regs.get dst
    match (generalizing := false) (motive := Width → Effects) w with
    | .W32 =>
      let v := a.take 8 ++ a.extractLsb' 8 8 ++ a.extractLsb' 16 8 ++ a.drop 24
      next (s.setReg dst (v.setWidth _))
    | .W64 =>
      let v := a.take 8 ++ a.extractLsb' 8 8 ++ a.extractLsb' 16 8 ++ a.extractLsb' 24 8
            ++ a.extractLsb' 32 8 ++ a.extractLsb' 40 8 ++ a.extractLsb' 48 8 ++ a.drop 56
      next (s.setReg dst (v.setWidth _))
    | _ => undefined (fun v => next (s.setReg dst v))
  | .cltq =>
    next (s.setReg (.low .rax .W64) ((s.regs.get (.low .rax .W32)).signExtend 64))
  | .cltd =>
    next (s.setReg (.low .rdx .W32) ((s.regs.get (.low .rax .W32)).sshiftRight 31))
  | .ud1 _ _ => .trap "ud1"
  | .ud2 => .trap "ud2"
  | .int3 => .trap "int3"
  | .jcc cc l =>
    if cc.interp s.status
    then jmp (label l) s
    else next s
  | .jmp tgt =>
    tgt.interp s p (fun a s =>
    jmp (.ofBitVec a) s)
  | .call tgt =>
    tgt.interp s p (fun a s =>
    let rsp := s.regs.get64 .rsp - Width.W64.bytesv
    { s with regs := s.regs.set64 .rsp rsp }.store rsp (w:=.W64) p.upper.toBitVec (jmp (.ofBitVec a)))
  | .ret =>
    let rsp := s.regs.get64 .rsp
    s.load rsp .W64 (fun ra s =>
    jmp (.ofBitVec ra) { s with regs := s.regs.set64 .rsp (rsp + 8) })
  | nop _ | nopalign _ _ => next s

-- AVX Operations Interpreter
def AvxOperation.interp [Labels] [address_size : AddressSize]
  {w} (i : AvxOperation w) (p : Std.Rco Int64) (s : MachineData)
  (next : MachineData → Effects) : Effects :=
match i with
  | .movups dst src => src.interp s p (fun val s => s.setAvxLegacy dst val p next)
  | .vmovups dst src => src.interp s p (fun val s => s.setAvx dst val p next)
  | .movaps dst src =>
    src.interp s p (checkAlign := true)
      (fun val s => s.setAvxLegacy dst val p (checkAlign := true) next)
  -- TODO: MXCSR
  | .subps dst src =>
    src.interp s p (checkAlign := true) (fun a s =>
    dst.interp s p (fun b s =>
      let v := BitVec.packedBinOp 32 (fun dst_chunk src_chunk =>
        let f_dst := BitVec.toFloat32 dst_chunk
        let f_src := BitVec.toFloat32 src_chunk
        Float32.toBitVec (f_dst - f_src)
      ) b a
      s.setAvxLegacy dst v p next))
  | .addps dst src =>
    src.interp s p (checkAlign := true) (fun a s =>
    dst.interp s p (fun b s =>
      let v := BitVec.packedBinOp 32 (fun dst_chunk src_chunk =>
        let f_dst := BitVec.toFloat32 dst_chunk
        let f_src := BitVec.toFloat32 src_chunk
        Float32.toBitVec (f_dst + f_src)
      ) b a
      s.setAvxLegacy dst v p next))
  | .mulps dst src =>
    src.interp s p (checkAlign := true) (fun a s =>
    dst.interp s p (fun b s =>
      s.setAvxLegacy dst (BitVec.packedBinOp 32 BitVec.f32mul b a) p next))
  | .xorps dst src =>
    src.interp s p (checkAlign := true) (fun a s =>
    dst.interp s p (fun b s =>
      s.setAvxLegacy dst (b ^^^ a) p next))
  -- VEX-encoded forms: a register destination is written with the bits above
  -- the operation width cleared, and only `vmovaps` requires an aligned memory
  -- operand.
  | .vmovaps dst src =>
    src.interp s p (checkAlign := true)
      (fun val s => s.setAvx dst val p (checkAlign := true) next)
  | .vxorps dst src1 src2 =>
    src2.interp s p (fun b s =>
      next (s.setAvxReg dst (s.zmms.get src1 ^^^ b)))
  | .vaddps dst src1 src2 =>
    src2.interp s p (fun b s =>
      next (s.setAvxReg dst (BitVec.packedBinOp 32 BitVec.f32add (s.zmms.get src1) b)))
  | .vmulps dst src1 src2 =>
    src2.interp s p (fun b s =>
      next (s.setAvxReg dst (BitVec.packedBinOp 32 BitVec.f32mul (s.zmms.get src1) b)))
  | .vfmadd231ps dst src1 src2 =>
    src2.interp s p (fun b s =>
      next (s.setAvxReg dst
        (BitVec.packedTernOp 32 BitVec.f32fma (s.zmms.get src1) b (s.zmms.get dst))))
  | .vfmadd132ps dst src1 src2 =>
    src2.interp s p (fun b s =>
      next (s.setAvxReg dst
        (BitVec.packedTernOp 32 BitVec.f32fma (s.zmms.get dst) b (s.zmms.get src1))))
  | .vpermps dst src1 src2 =>
    src2.interp s p (fun b s =>
      next (s.setAvxReg dst (BitVec.packedBinOp 32
        (fun i _ => b.extractLsb' (32 * (i.toNat % 8)) 32) (s.zmms.get src1) (s.zmms.get src1))))
  | .vshufps dst src1 src2 imm =>
    src2.interp s p (fun b s =>
      next (s.setAvxReg dst (BitVec.packedBinOp 128 (BitVec.shufps128 imm) (s.zmms.get src1) b)))
  | .vextractf128 dst src imm =>
    next (s.setAvxReg dst ((s.zmms.get src).extractLsb' (128 * (imm.toNat % 2)) 128))
  | .vinsertf128 dst src1 src2 imm =>
    src2.interp s p (fun b s =>
      let a := s.zmms.get src1
      next (s.setAvxReg dst
        (if imm.toNat % 2 = 0 then a.extractLsb' 128 128 ++ b else b ++ a.extractLsb' 0 128)))
  | .vmovhlps dst src1 src2 =>
    next (s.setAvxReg dst
      ((s.zmms.get src1).extractLsb' 64 64 ++ (s.zmms.get src2).extractLsb' 64 64))
  | .vmovss dst src1 src2 =>
    next (s.setAvxReg dst
      ((s.zmms.get src1).extractLsb' 32 96 ++ (s.zmms.get src2).extractLsb' 0 32))
  | .vaddss dst src1 src2 =>
    let a := s.zmms.get src1
    let b := s.zmms.get src2
    next (s.setAvxReg dst
      (a.extractLsb' 32 96 ++ BitVec.f32add (a.extractLsb' 0 32) (b.extractLsb' 0 32)))
  | .vzeroupper => next { s with zmms := s.zmms.zeroUpper }
  -- VEX scalar forms. Scalar memory operands go through the general-purpose
  -- `load`/`store` at 32 or 64 bits, without an alignment check.
  | .vmovssMem dst src =>
    match dst, src with
    | .avx d, .mem a =>
      s.load ((a.interp s.regs p).zeroExtend _) .W32 (fun v s =>
        next (s.setAvxReg d (v.zeroExtend 128)))
    | .mem a, .avx r =>
      s.store ((a.interp s.regs p).zeroExtend _) (w := .W32) ((s.zmms.get r).setWidth 32) next
    | _, _ => unimplemented "vmovss: exactly one operand is memory"
  | .vmovsdMem dst src =>
    match dst, src with
    | .avx d, .mem a =>
      s.load ((a.interp s.regs p).zeroExtend _) .W64 (fun v s =>
        next (s.setAvxReg d (v.zeroExtend 128)))
    | .mem a, .avx r =>
      s.store ((a.interp s.regs p).zeroExtend _) (w := .W64) ((s.zmms.get r).setWidth 64) next
    | _, _ => unimplemented "vmovsd: exactly one operand is memory"
  | .vaddssMem dst src1 src2 =>
    s.load ((src2.interp s.regs p).zeroExtend _) .W32 (fun b s =>
      let a := s.zmms.get src1
      next (s.setAvxReg dst (a.extractLsb' 32 96 ++ BitVec.f32add (a.extractLsb' 0 32) b)))
  | .vsubss dst src1 src2 =>
    src2.interpLow .W32 s p (fun b s =>
      let a := s.zmms.get src1
      next (s.setAvxReg dst (a.extractLsb' 32 96 ++ BitVec.f32sub (a.extractLsb' 0 32) b)))
  | .vmulss dst src1 src2 =>
    src2.interpLow .W32 s p (fun b s =>
      let a := s.zmms.get src1
      next (s.setAvxReg dst (a.extractLsb' 32 96 ++ BitVec.f32mul (a.extractLsb' 0 32) b)))
  | .vdivss dst src1 src2 =>
    src2.interpLow .W32 s p (fun b s =>
      let a := s.zmms.get src1
      next (s.setAvxReg dst (a.extractLsb' 32 96 ++ BitVec.f32div (a.extractLsb' 0 32) b)))
  | .vminss dst src1 src2 =>
    src2.interpLow .W32 s p (fun b s =>
      let a := s.zmms.get src1
      next (s.setAvxReg dst (a.extractLsb' 32 96 ++ BitVec.f32min (a.extractLsb' 0 32) b)))
  | .vsqrtss dst src1 src2 =>
    src2.interpLow .W32 s p (fun b s =>
      let a := s.zmms.get src1
      next (s.setAvxReg dst (a.extractLsb' 32 96 ++ BitVec.f32sqrt b)))
  | .vmulsd dst src1 src2 =>
    src2.interpLow .W64 s p (fun b s =>
      let a := s.zmms.get src1
      next (s.setAvxReg dst (a.extractLsb' 64 64 ++ BitVec.f64mul (a.extractLsb' 0 64) b)))
  | .vcmpss pred dst src1 src2 =>
    src2.interpLow .W32 s p (fun b s =>
      let a := s.zmms.get src1
      let r : BitVec 32 :=
        if BitVec.f32cmpPred pred (a.extractLsb' 0 32) b then BitVec.allOnes 32 else 0#32
      next (s.setAvxReg dst (a.extractLsb' 32 96 ++ r)))
  | .vucomiss src1 src2 =>
    src2.interpLow .W32 s p (fun b s =>
      next { s with status := .ofFCmp (BitVec.f32cmp ((s.zmms.get src1).extractLsb' 0 32) b) })
  | .vucomisd src1 src2 =>
    src2.interpLow .W64 s p (fun b s =>
      next { s with status := .ofFCmp (BitVec.f64cmp ((s.zmms.get src1).extractLsb' 0 64) b) })
  | .vcvtsi2ss dst src1 src2 =>
    src2.interp s p (fun b s =>
      let a := s.zmms.get src1
      next (s.setAvxReg dst (a.extractLsb' 32 96 ++ BitVec.sitof32 b)))
  | .vcvtss2sd dst src1 src2 =>
    src2.interpLow .W32 s p (fun b s =>
      let a := s.zmms.get src1
      next (s.setAvxReg dst (a.extractLsb' 64 64 ++ BitVec.f32to64 b)))
  | .vcvtsd2ss dst src1 src2 =>
    src2.interpLow .W64 s p (fun b s =>
      let a := s.zmms.get src1
      next (s.setAvxReg dst (a.extractLsb' 32 96 ++ BitVec.f64to32 b)))
  | .vcvtps2pd dst src =>
    src.interpLow .W64 s p (fun b s =>
      next (s.setAvxReg dst (BitVec.f32to64 (b.dw 1) ++ BitVec.f32to64 (b.dw 0))))
  | .vmovdTo dst src =>
    src.interp s p (fun v s => next (s.setAvxReg dst (v.zeroExtend 128)))
  | .vmovdFrom dst src =>
    s.set dst ((s.zmms.get src).setWidth 32) p next
  | .vmovqTo dst src =>
    src.interp s p (fun v s => next (s.setAvxReg dst (v.zeroExtend 128)))
  | .vmovqFrom dst src =>
    s.set dst ((s.zmms.get src).setWidth 64) p next
  -- VEX packed forms
  | .vmovapd dst src =>
    src.interp s p (checkAlign := true)
      (fun val s => s.setAvx dst val p (checkAlign := true) next)
  | .vmovdqa dst src =>
    src.interp s p (checkAlign := true)
      (fun val s => s.setAvx dst val p (checkAlign := true) next)
  | .vxorpd dst src1 src2 =>
    src2.interp s p (fun b s =>
      next (s.setAvxReg dst (s.zmms.get src1 ^^^ b)))
  | .vsubps dst src1 src2 =>
    src2.interp s p (fun b s =>
      next (s.setAvxReg dst (BitVec.packedBinOp 32 BitVec.f32sub (s.zmms.get src1) b)))
  | .vdivps dst src1 src2 =>
    src2.interp s p (fun b s =>
      next (s.setAvxReg dst (BitVec.packedBinOp 32 BitVec.f32div (s.zmms.get src1) b)))
  | .vaddsubps dst src1 src2 =>
    src2.interp s p (fun b s =>
      next (s.setAvxReg dst (BitVec.packedBinOpIdx 32
        (fun i x y => if i % 2 = 0 then BitVec.f32sub x y else BitVec.f32add x y)
        (s.zmms.get src1) b)))
  | .vandps dst src1 src2 =>
    src2.interp s p (fun b s =>
      next (s.setAvxReg dst (s.zmms.get src1 &&& b)))
  | .vandnps dst src1 src2 =>
    src2.interp s p (fun b s =>
      next (s.setAvxReg dst (~~~(s.zmms.get src1) &&& b)))
  | .vpaddd dst src1 src2 =>
    src2.interp s p (fun b s =>
      next (s.setAvxReg dst (BitVec.packedBinOp 32 (· + ·) (s.zmms.get src1) b)))
  | .vpand dst src1 src2 =>
    src2.interp s p (fun b s =>
      next (s.setAvxReg dst (s.zmms.get src1 &&& b)))
  | .vpxor dst src1 src2 =>
    src2.interp s p (fun b s =>
      next (s.setAvxReg dst (s.zmms.get src1 ^^^ b)))
  | .vblendvps dst src1 src2 mask =>
    src2.interp s p (fun b s =>
      next (s.setAvxReg dst (BitVec.packedTernOp 32 (fun x y m => if m.msb then y else x)
        (s.zmms.get src1) b (s.zmms.get mask))))
  | .vshufpd dst src1 src2 imm =>
    src2.interp s p (fun b s =>
      next (s.setAvxReg dst (BitVec.packedBinOpIdx 128 (fun k x y =>
        let i := imm.toNat >>> (2 * k)
        (if (i >>> 1) % 2 = 1 then y.qw 1 else y.qw 0) ++ (if i % 2 = 1 then x.qw 1 else x.qw 0))
        (s.zmms.get src1) b)))
  | .vpblendw dst src1 src2 imm =>
    src2.interp s p (fun b s =>
      next (s.setAvxReg dst (BitVec.packedBinOpIdx 16
        (fun i x y => if (imm.toNat >>> (i % 8)) % 2 = 1 then y else x) (s.zmms.get src1) b)))
  | .vpermilps dst src imm =>
    src.interp s p (fun b s =>
      next (s.setAvxReg dst (BitVec.packedBinOp 128 (fun x _ => BitVec.pshufd128 imm x) b b)))
  | .vpslld dst src imm =>
    let a := s.zmms.get src
    next (s.setAvxReg dst (BitVec.packedBinOp 32
      (fun x _ => if imm.toNat > 31 then 0#32 else x <<< imm.toNat) a a))
  | .vmovshdup dst src =>
    src.interp s p (fun b s =>
      next (s.setAvxReg dst (BitVec.packedBinOp 128
        (fun x _ => x.dw 3 ++ x.dw 3 ++ x.dw 1 ++ x.dw 1) b b)))
  | .vmovsldup dst src =>
    src.interp s p (fun b s =>
      next (s.setAvxReg dst (BitVec.packedBinOp 128
        (fun x _ => x.dw 2 ++ x.dw 2 ++ x.dw 0 ++ x.dw 0) b b)))
  | .vbroadcastss dst src =>
    src.interpLow .W32 s p (fun v s =>
      next (s.setAvxReg dst (BitVec.packedBinOp 32 (fun _ _ => v) 0 0)))
  | .vinsertps dst src1 src2 imm =>
    match src2 with
    | .avx r =>
      next (s.setAvxReg dst (BitVec.insertps imm (s.zmms.get src1)
        ((s.zmms.get r).dw ((imm.toNat >>> 6) % 4))))
    | .mem a =>
      s.load ((a.interp s.regs p).zeroExtend _) .W32 (fun v s =>
        next (s.setAvxReg dst (BitVec.insertps imm (s.zmms.get src1) v)))
  | .vpinsrd dst src1 src2 imm =>
    src2.interp s p (fun v s =>
      let a := s.zmms.get src1
      next (s.setAvxReg dst (BitVec.packedBinOpIdx 32
        (fun i x _ => if i = imm.toNat % 4 then v else x) a a)))
  | .vpextrd dst src imm =>
    s.set dst ((s.zmms.get src).dw (imm.toNat % 4)) p next
  | .vmovlpsStore dst src =>
    s.store ((dst.interp s.regs p).zeroExtend _) (w := .W64) ((s.zmms.get src).setWidth 64) next
  | .vmovdqu dst src =>
    src.interp s p (fun val s => s.setAvx dst val p next)
  | .vcvtdq2ps dst src =>
    src.interp s p (fun b s =>
      next (s.setAvxReg dst (BitVec.packedBinOp 32 (fun x _ => BitVec.sitof32 x) b b)))
  | .vblendps dst src1 src2 imm =>
    src2.interp s p (fun b s =>
      next (s.setAvxReg dst (BitVec.packedBinOpIdx 32
        (fun i x y => if (imm.toNat >>> (i % 8)) % 2 = 1 then y else x) (s.zmms.get src1) b)))
  | .vpaddw dst src1 src2 =>
    src2.interp s p (fun b s =>
      next (s.setAvxReg dst (BitVec.packedBinOp 16 (· + ·) (s.zmms.get src1) b)))
  | .vpminsd dst src1 src2 =>
    src2.interp s p (fun b s =>
      next (s.setAvxReg dst (BitVec.packedBinOp 32
        (fun x y => if x.slt y then x else y) (s.zmms.get src1) b)))
  | .vpshufb dst src1 src2 =>
    src2.interp s p (fun b s =>
      next (s.setAvxReg dst (BitVec.packedBinOp 128 BitVec.pshufb128 (s.zmms.get src1) b)))
  | .vpunpcklqdq dst src1 src2 =>
    src2.interp s p (fun b s =>
      next (s.setAvxReg dst (BitVec.packedBinOp 128
        (fun x y => y.qw 0 ++ x.qw 0) (s.zmms.get src1) b)))
  | .vpshufd dst src imm =>
    src.interp s p (fun b s =>
      next (s.setAvxReg dst (BitVec.packedBinOp 128 (fun x _ => BitVec.pshufd128 imm x) b b)))
  | .vcvtss2si dst src =>
    src.interpLow .W32 s p (fun b s => next (s.setReg dst (BitVec.f32toi64 b)))
  | .vpinsrw dst src1 src2 imm =>
    let v := (s.regs.get src2).setWidth 16
    let a := s.zmms.get src1
    next (s.setAvxReg dst (BitVec.packedBinOpIdx 16
      (fun i x _ => if i = imm.toNat % 8 then v else x) a a))
  | .vpmovsxwd dst src =>
    src.interpLow .W64 s p (fun b s =>
      let el (i : Nat) : BitVec 32 := (b.extractLsb' (16 * i) 16).signExtend 32
      next (s.setAvxReg dst (el 3 ++ el 2 ++ el 1 ++ el 0)))
  | .vpcmpeqd dst src1 src2 =>
    src2.interp s p (fun b s =>
      next (s.setAvxReg dst (BitVec.packedBinOp 32
        (fun x y => if x = y then BitVec.allOnes 32 else 0#32) (s.zmms.get src1) b)))
  | .vpsrldx dst src count =>
    let n := ((s.zmms.get count).extractLsb' 0 64).toNat
    let a := s.zmms.get src
    next (s.setAvxReg dst (BitVec.packedBinOp 32
      (fun x _ => if n > 31 then 0#32 else x >>> n) a a))
  | .vpmovzxdq dst src =>
    src.interpLow .W64 s p (fun b s =>
      next (s.setAvxReg dst ((b.dw 1).zeroExtend 64 ++ (b.dw 0).zeroExtend 64)))
  -- Legacy SSE forms: register writes keep bits 255..128.
  | .movss dst src =>
    match dst, src with
    | .avx d, .avx r =>
      next (s.setAvxLegacyReg d
        ((s.zmms.get d).extractLsb' 32 96 ++ (s.zmms.get r).extractLsb' 0 32))
    | .avx d, .mem a =>
      s.load ((a.interp s.regs p).zeroExtend _) .W32 (fun v s =>
        next (s.setAvxLegacyReg d (v.zeroExtend 128)))
    | .mem a, .avx r =>
      s.store ((a.interp s.regs p).zeroExtend _) (w := .W32) ((s.zmms.get r).setWidth 32) next
    | .mem _, .mem _ => unimplemented "movss: two memory operands"
  | .movsd dst src =>
    match dst, src with
    | .avx d, .avx r =>
      next (s.setAvxLegacyReg d
        ((s.zmms.get d).extractLsb' 64 64 ++ (s.zmms.get r).extractLsb' 0 64))
    | .avx d, .mem a =>
      s.load ((a.interp s.regs p).zeroExtend _) .W64 (fun v s =>
        next (s.setAvxLegacyReg d (v.zeroExtend 128)))
    | .mem a, .avx r =>
      s.store ((a.interp s.regs p).zeroExtend _) (w := .W64) ((s.zmms.get r).setWidth 64) next
    | .mem _, .mem _ => unimplemented "movsd: two memory operands"
  | .movqx dst src =>
    match dst, src with
    | .avx d, .avx r =>
      next (s.setAvxLegacyReg d (((s.zmms.get r).setWidth 64).zeroExtend 128))
    | .avx d, .mem a =>
      s.load ((a.interp s.regs p).zeroExtend _) .W64 (fun v s =>
        next (s.setAvxLegacyReg d (v.zeroExtend 128)))
    | .mem a, .avx r =>
      s.store ((a.interp s.regs p).zeroExtend _) (w := .W64) ((s.zmms.get r).setWidth 64) next
    | .mem _, .mem _ => unimplemented "movq: two memory operands"
  | .movlps dst src =>
    match dst, src with
    | .avx d, .mem a =>
      s.load ((a.interp s.regs p).zeroExtend _) .W64 (fun v s =>
        next (s.setAvxLegacyReg d ((s.zmms.get d).extractLsb' 64 64 ++ v)))
    | .mem a, .avx r =>
      s.store ((a.interp s.regs p).zeroExtend _) (w := .W64) ((s.zmms.get r).setWidth 64) next
    | _, _ => unimplemented "movlps: exactly one operand is memory"
  | .movhps dst src =>
    match dst, src with
    | .avx d, .mem a =>
      s.load ((a.interp s.regs p).zeroExtend _) .W64 (fun v s =>
        next (s.setAvxLegacyReg d (v ++ (s.zmms.get d).extractLsb' 0 64)))
    | .mem a, .avx r =>
      s.store ((a.interp s.regs p).zeroExtend _) (w := .W64) ((s.zmms.get r).extractLsb' 64 64) next
    | _, _ => unimplemented "movhps: exactly one operand is memory"
  | .movdqa dst src =>
    src.interp s p (checkAlign := true)
      (fun val s => s.setAvxLegacy dst val p (checkAlign := true) next)
  | .movdqu dst src => src.interp s p (fun val s => s.setAvxLegacy dst val p next)
  | .addss dst src =>
    src.interpLow .W32 s p (fun b s =>
      let a := s.zmms.get dst
      next (s.setAvxLegacyReg dst (a.extractLsb' 32 96 ++ BitVec.f32add (a.extractLsb' 0 32) b)))
  | .movlhps dst src =>
    next (s.setAvxLegacyReg dst ((s.zmms.get src).extractLsb' 0 64 ++ (s.zmms.get dst).extractLsb' 0 64))
  | .movhlps dst src =>
    next (s.setAvxLegacyReg dst ((s.zmms.get dst).extractLsb' 64 64 ++ (s.zmms.get src).extractLsb' 64 64))
  | .shufps dst src imm =>
    src.interp s p (checkAlign := true) (fun b s =>
      next (s.setAvxLegacyReg dst (BitVec.shufps128 imm (s.zmms.get dst) b)))
  | .unpcklps dst src | .punpckldq dst src =>
    src.interp s p (checkAlign := true) (fun b s =>
      let a := s.zmms.get dst
      next (s.setAvxLegacyReg dst (b.dw 1 ++ a.dw 1 ++ b.dw 0 ++ a.dw 0)))
  | .unpckhps dst src | .punpckhdq dst src =>
    src.interp s p (checkAlign := true) (fun b s =>
      let a := s.zmms.get dst
      next (s.setAvxLegacyReg dst (b.dw 3 ++ a.dw 3 ++ b.dw 2 ++ a.dw 2)))
  | .haddps dst src =>
    src.interp s p (checkAlign := true) (fun b s =>
      next (s.setAvxLegacyReg dst (BitVec.haddps128 (s.zmms.get dst) b)))
  | .movddup dst src =>
    src.interpLow .W64 s p (fun v s => next (s.setAvxLegacyReg dst (v ++ v)))
  | .movshdup dst src =>
    src.interp s p (checkAlign := true) (fun b s =>
      next (s.setAvxLegacyReg dst (b.dw 3 ++ b.dw 3 ++ b.dw 1 ++ b.dw 1)))
  | .pxor dst src =>
    src.interp s p (checkAlign := true) (fun b s =>
      next (s.setAvxLegacyReg dst (s.zmms.get dst ^^^ b)))
  | .pand dst src =>
    src.interp s p (checkAlign := true) (fun b s =>
      next (s.setAvxLegacyReg dst (s.zmms.get dst &&& b)))
  | .pcmpeqd dst src =>
    src.interp s p (checkAlign := true) (fun b s =>
      next (s.setAvxLegacyReg dst (BitVec.packedBinOp 32
        (fun x y => if x = y then BitVec.allOnes 32 else 0#32) (s.zmms.get dst) b)))
  | .pshufd dst src imm =>
    src.interp s p (checkAlign := true) (fun b s =>
      next (s.setAvxLegacyReg dst (BitVec.pshufd128 imm b)))

@[kstep]
def Instr.interp [Labels]
  (i : Instr) (s : MachineData) (p : Std.Rco Int64)
  (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects) : Effects :=
  require_exec_access p (fun _unit =>
    match i with
      | .regular addr_sz op_sz op =>
          Operation.interp (w := op_sz) (address_size := .mk addr_sz) op p s next jmp
      | .avx addr_sz op_sz op =>
          AvxOperation.interp (w := op_sz) (address_size := .mk addr_sz) op p s next
  )

@[kstep] def Directive.interp [Labels]
  (d : Directive) (s : MachineData) (p : Std.Rco Int64)
  (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects) : Effects :=
  match d with
  | .label _ => next s
  | .instr i => i.interp s p next jmp
  | .byteArray _ => .unimplemented s!"Unimplemented: execution reached data block at {p.1}"

def Directives.interp [Labels]
  (ds : List (Directive × Nat)) (s : MachineData) (pc : Int64)
  (ret : Int64 → MachineData → Effects) : Effects :=
  match ds with
  | [] => ret pc s
  | (d, sz) :: ds =>
    d.interp s (.mk pc (pc+.ofNat sz)) (jmp:=ret) (next := (fun s =>
    interp ds s (pc+.ofNat sz) ret))

abbrev Layout := Kraken.Layout Directive

@[reducible]
def Executable.labels (e : Executable) : Labels :=
  { label l := (e.withAddresses.findSome?
      (fun (p, d, _) => if d = .label l then .some p else .none)).getD (-1) }

def Executable.directivesFromLabel (e : Executable) (l : Label) : List (Directive × Nat) :=
  e.2.dropWhile (·.1 != .label l)

abbrev MachineState := MachineData × Int64

def Executable.step (e : Executable) (s : MachineState) (ret : MachineState → Effects) : Effects :=
  let := Executable.labels e
  Directives.interp (e.directivesAtAddress s.2) s.1 s.2 (fun pc s => ret (s, pc))

def Executable.straightline (e : Executable) (s : MachineState) (ret : MachineState → Effects) : Effects :=
  let := Executable.labels e
  Directives.interp (e.directivesFromAddress s.2) s.1 s.2 (fun pc s => ret (s, pc))

-- -- Concrete evaluators for expedient testing

partial def Executable.eval (e : Executable) (s : MachineState) (until_ : MachineState → Bool) : Except String (MachineState) :=
  if until_ s then .ok s else handleEffects (Executable.straightline e s .done)
where
  handleEffects es :=
    match es with
    | .done s => eval e s until_
    | .unimplemented msg => .error msg
    | .gp_unaligned addr w => .error s!"#GP: Memory op at {repr addr} did not have mandatory alignment of {w}"
    | .trap what => .error s!"trap: {what}"
    | .require_read_access _ _ ok => handleEffects (ok ())
    | .require_write_access _ _ ok => handleEffects (ok ())
    | .require_exec_access _ ok => handleEffects (ok ())
    | .nonmem_load _ addr _ _ => .error s!"Load at unmapped address {repr addr}"
    | .nonmem_store _ addr _ _ => .error s!"Store at unmapped address {repr addr}"
    | @Effects.undefined _ t cont => handleEffects (cont (t.from_hash (hash s.1.regs)))

def Directive.fakeSize (hashOfProgram : UInt64) (d : Directive) : Nat :=
  match d with
  | .label _ => 0
  | .instr (.regular _ _ (.nop sz)) => sz -- may be zero
  | .instr i => (1 + hash (hashOfProgram, i) % 15).toNat
  | .byteArray bs => bs.size

def Program.fakeLayout (prog : Program) : Executable :=
  let : Inhabited Directive := .mk (.byteArray (.mk #[]))
  let h := hash prog;
  let layout : Layout := { start := h.toInt64<<<16, size i := prog[i]!.fakeSize h }
  layout prog

abbrev eval [layout : Layout] (prog : Program) := Executable.eval (layout prog)

/-- info: Except.ok 42 -/
#guard_msgs in
#eval
  let exe := Program.fakeLayout [
    .label "main",
    .instr (.regular .W64 .W64 (.lea (.low .rax .W64) (.mk .none .none (.int64 41)))),
    .instr (.regular .W64 .W64 (.inc (.reg (.low .rax .W64)))),
    .instr (.regular .W64 .W64 .ret) ]
  let start := (Executable.labels exe).label "main"
  let data : MachineData := { dmem := Mem.storeInt {} 0x100 8 0x1337, regs := {rsp := 0x100} }
  (Executable.eval exe (data, start) (fun (_, pc) => pc = 0x1337)).bind (fun s => .ok s.1.regs.rax)
