#!/usr/bin/env python3
"""Generates Kraken/Rules/PackedSse.lean."""
import sys

GEN_BIND = "(b : Reg64) (idx : Option AddrIndex) (d : Int64)"
GEN_ADDR = "s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec"
GEN_AE = "⟨some (.reg b), idx, .int64 d⟩"
RIP_BIND = "(l : Label)"
RIP_ADDR = "((_root_.Executable.labels cenv).label l).toBitVec"
RIP_AE = "⟨some .rip, none, .sub (.label l) .after_current_instruction⟩"
# `sym+o(%rip)`: every `sym(%rip)` rule also gets this form (`_rip_off_spec`).
RIPO_BIND = "(l : Label) (o : Int64)"
RIPO_ADDR = "((_root_.Executable.labels cenv).label l).toBitVec + o.toBitVec"
RIPO_AE = "⟨some .rip, none, .sub (.add (.label l) (.int64 o)) .after_current_instruction⟩"

out = []
names = []

def emit(s):
  out.append(s)

def M(n):
  return f"(BitVec.ofInt {n} v)"

def mem_rule(kind, name, doc, args, width, op, n, value, align=None, rip=False):
  """kind: load (value = record field update using v) or store (value = stored bitvector).
  rip=True emits the `sym(%rip)` rule and its `sym+o(%rip)` twin (rip="off")."""
  if rip is True:
    mem_rule(kind, name, doc, args, width, op, n, value, align, rip="rip")
    mem_rule(kind, name, doc.replace("sym(%rip)", "sym+o(%rip)"), args, width, op, n, value,
             align, rip="off")
    return
  bind, addr, ae = {"rip": (RIP_BIND, RIP_ADDR, RIP_AE), "off": (RIPO_BIND, RIPO_ADDR, RIPO_AE),
                    False: (GEN_BIND, GEN_ADDR, GEN_AE)}[rip]
  name = name + {"rip": "_rip_spec", "off": "_rip_off_spec", False: "_mem_spec"}[rip]
  names.append((name, doc))
  op = op.replace("MEM", f"(.mem {ae})").replace("ADDR", ae)
  side = f"(isAligned {align} a = true) ⊓ " if align else ""
  if kind == "load":
    post = (f"(∀ v, Mem.loadInt s.dmem a {n} = some v →\n"
            f"            WP.wp p Q E {{ s with {value} }})")
    tac = "mem_load_al" if align else "mem_load"
  else:
    post = f"WP.wp p Q E {{ s with dmem := Mem.storeInt s.dmem a {n} ({value}).toInt }}"
    tac = "mem_store_al" if align else "mem_store"
  value = value.replace("\n              ", " ")
  emit(f"""/-- {doc} -/
@[spec low] theorem MachineWP.{name} {args} {bind} :
    ⦃ fun s =>
        let a := {addr}
        {side}((Mem.loadInt s.dmem a {n}).isSome = true)
          ⊓ {post} ⦄
      (Directive.instr (.avx .W64 {width} ({op})) :: p)
    ⦃ Q; E ⦄ := by {tac}
""")

def reg_rule(name, doc, args, width, op, value):
  name = name + "_spec"
  names.append((name, doc))
  value = value.replace("\n              ", " ")
  emit(f"""/-- {doc} -/
@[spec low] theorem MachineWP.{name} {args} (asz : Width) :
    ⦃ fun s => WP.wp p Q E {{ s with {value} }} ⦄
      (Directive.instr (.avx asz {width} ({op})) :: p)
    ⦃ Q; E ⦄ := reg_proof
""")

def section(title, text=""):
  emit(f"/-! ### {title}\n{text}-/\n")

HEADER = open(sys.argv[1]).read()
emit(HEADER)

# ---------------------------------------------------------------- VEX moves
section("VEX packed moves", """
`vmovaps`, `vmovapd` and `vmovdqa` check alignment (16 bytes at `.W128`, 32
at `.W256`); `vmovups` does not. A register destination is written with the
bits above the operation width cleared (`RegZmms.set`).
""")
for op, al in [("vmovaps", True), ("vmovapd", True), ("vmovdqa", True), ("vmovups", False)]:
  for w, n, r in [("W128", 16, "x"), ("W256", 32, "y")]:
    sfx = "" if w == "W128" else "256"
    a = n if al else None
    adoc = f", {n}-byte aligned" if al else ", at any alignment"
    mem_rule("load", f"{op}{sfx}_load", f"`{op} m{n*8}, %{'x' if n == 16 else 'y'}mm`: {n} readable bytes{adoc}.",
             f"({r} : AvxReg .{w})", f".{w}", f".{op} (.avx {r}) MEM", n,
             f"zmms := s.zmms.set {r} {M(n*8)}", a)
    mem_rule("store", f"{op}{sfx}_store", f"`{op} %{'x' if n == 16 else 'y'}mm, m{n*8}`: {n} owned bytes{adoc}.",
             f"({r} : AvxReg .{w})", f".{w}", f".{op} MEM (.avx {r})", n,
             f"s.zmms.get {r}", a)
for op in ["vmovaps", "vmovapd", "vmovdqa", "vmovups"]:
  reg_rule(f"{op}_reg", f"`{op} %src, %dst` (register form, any width).",
           "{w : AvxWidth} (dst src : AvxReg w)", "w", f".{op} (.avx dst) (.avx src)",
           "zmms := s.zmms.set dst (s.zmms.get src)")
mem_rule("store", "vmovlps_store", "`vmovlps %xmm, m64`: 8 owned bytes, any alignment; the low quadword is stored.",
         "(x : AvxReg .W128)", ".W128", ".vmovlpsStore ADDR x", 8, "(s.zmms.get x).setWidth 64")

# ------------------------------------------------------------ VEX binary ops
section("VEX three-operand packed operations", """
`dst := f src1 src2`, with `src2` a register or 16 bytes of memory at any
alignment (VEX forms other than the aligned moves do not check alignment).
""")
BIN = [
  ("vaddps", "BitVec.packedBinOp 32 BitVec.f32add «A» «B»", False),
  ("vmulps", "BitVec.packedBinOp 32 BitVec.f32mul «A» «B»", False),
  ("vsubps", "BitVec.packedBinOp 32 BitVec.f32sub «A» «B»", True),
  ("vdivps", "BitVec.packedBinOp 32 BitVec.f32div «A» «B»", True),
  ("vaddsubps", "BitVec.packedBinOpIdx 32\n              (fun i x y => if i % 2 = 0 then BitVec.f32sub x y else BitVec.f32add x y) «A» «B»", True),
  ("vandps", "«A» &&& «B»", True),
  ("vandnps", "~~~«A» &&& «B»", True),
  ("vxorps", "«A» ^^^ «B»", False),
  ("vxorpd", "«A» ^^^ «B»", True),
  ("vpaddd", "BitVec.packedBinOp 32 (· + ·) «A» «B»", True),
  ("vpand", "«A» &&& «B»", True),
  ("vpxor", "«A» ^^^ «B»", True),
]
RIP_BIN = {"vxorps", "vpand", "vpaddd"}
for op, f, needreg in BIN:
  v = f.replace("«A»", "(s.zmms.get src1)").replace("«B»", M(128))
  for rip in ([False, True] if op in RIP_BIN else [False]):
    mem_rule("load", f"{op}_load", f"`{op} m128, %src1, %dst`: 16 readable bytes, any alignment.",
             "(dst src1 : AvxReg .W128)", ".W128", f".{op} dst src1 MEM", 16,
             f"zmms := s.zmms.set dst ({v})", rip=rip)
  if needreg:
    vr = f.replace("«A»", "(s.zmms.get src1)").replace("«B»", "(s.zmms.get src2)")
    reg_rule(f"{op}_reg", f"`{op} %src2, %src1, %dst` (register form, any width).",
             "{w : AvxWidth} (dst src1 src2 : AvxReg w)", "w", f".{op} dst src1 (.avx src2)",
             f"zmms := s.zmms.set dst ({vr})")
reg_rule("vmulps_reg", "`vmulps %src2, %src1, %dst` (register form, any width).",
         "{w : AvxWidth} (dst src1 src2 : AvxReg w)", "w", ".vmulps dst src1 (.avx src2)",
         "zmms := s.zmms.set dst (BitVec.packedBinOp 32 BitVec.f32mul (s.zmms.get src1) (s.zmms.get src2))")

BLEND = "BitVec.packedTernOp 32 (fun x y m => if m.msb then y else x)\n              (s.zmms.get src1) «B» (s.zmms.get mask)"
for rip in [False, True]:
  mem_rule("load", "vblendvps_load", "`vblendvps %mask, m128, %src1, %dst`: 16 readable bytes, any alignment.",
           "(dst src1 mask : AvxReg .W128)", ".W128", ".vblendvps dst src1 MEM mask", 16,
           f"zmms := s.zmms.set dst ({BLEND.replace('«B»', M(128))})", rip=rip)
reg_rule("vblendvps_reg", "`vblendvps %mask, %src2, %src1, %dst` (register form).",
         "{w : AvxWidth} (dst src1 src2 mask : AvxReg w)", "w", ".vblendvps dst src1 (.avx src2) mask",
         f"zmms := s.zmms.set dst ({BLEND.replace('«B»', '(s.zmms.get src2)')})")

SHUFPD = ("BitVec.packedBinOpIdx 128 (fun k x y =>\n"
          "              let i := imm.toNat >>> (2 * k);\n"
          "              (if (i >>> 1) % 2 = 1 then y.qw 1 else y.qw 0) ++ (if i % 2 = 1 then x.qw 1 else x.qw 0))\n"
          "              (s.zmms.get src1) «B»")
SHUFPS = "BitVec.packedBinOp 128 (BitVec.shufps128 imm) (s.zmms.get src1) «B»"
BLENDW = "BitVec.packedBinOpIdx 16\n              (fun i x y => if (imm.toNat >>> (i % 8)) % 2 = 1 then y else x) (s.zmms.get src1) «B»"
for op, f in [("vshufpd", SHUFPD), ("vshufps", SHUFPS), ("vpblendw", BLENDW)]:
  mem_rule("load", f"{op}_load", f"`{op} $imm, m128, %src1, %dst`: 16 readable bytes, any alignment.",
           "(dst src1 : AvxReg .W128) (imm : UInt8)", ".W128", f".{op} dst src1 MEM imm", 16,
           f"zmms := s.zmms.set dst ({f.replace('«B»', M(128))})")
  if op != "vshufps":
    reg_rule(f"{op}_reg", f"`{op} $imm, %src2, %src1, %dst` (register form).",
             "{w : AvxWidth} (dst src1 src2 : AvxReg w) (imm : UInt8)", "w", f".{op} dst src1 (.avx src2) imm",
             f"zmms := s.zmms.set dst ({f.replace('«B»', '(s.zmms.get src2)')})")

section("VEX two-operand packed operations", "")
UN = [
  ("vpermilps", "BitVec.packedBinOp 128 (fun x _ => BitVec.pshufd128 imm x) «B» «B»", True),
  ("vmovshdup", "BitVec.packedBinOp 128\n              (fun x _ => x.dw 3 ++ x.dw 3 ++ x.dw 1 ++ x.dw 1) «B» «B»", False),
  ("vmovsldup", "BitVec.packedBinOp 128\n              (fun x _ => x.dw 2 ++ x.dw 2 ++ x.dw 0 ++ x.dw 0) «B» «B»", False),
]
for op, f, imm in UN:
  ia = " (imm : UInt8)" if imm else ""
  isfx = " imm" if imm else ""
  idoc = "$imm, " if imm else ""
  mem_rule("load", f"{op}_load", f"`{op} {idoc}m128, %dst`: 16 readable bytes, any alignment.",
           f"(dst : AvxReg .W128){ia}", ".W128", f".{op} dst MEM{isfx}", 16,
           f"zmms := s.zmms.set dst ({f.replace('«B»', M(128))})")
  reg_rule(f"{op}_reg", f"`{op} {idoc}%src, %dst` (register form).",
           f"{{w : AvxWidth}} (dst src : AvxReg w){ia}", "w", f".{op} dst (.avx src){isfx}",
           f"zmms := s.zmms.set dst ({f.replace('«B»', '(s.zmms.get src)')})")
reg_rule("vpslld_imm", "`vpslld $imm, %src, %dst`: each dword shifted left (zero past 31).",
         "{w : AvxWidth} (dst src : AvxReg w) (imm : UInt8)", "w", ".vpslld dst src imm",
         "zmms := s.zmms.set dst (BitVec.packedBinOp 32\n              (fun x _ => if imm.toNat > 31 then 0#32 else x <<< imm.toNat) (s.zmms.get src) (s.zmms.get src))")
BCAST = "BitVec.packedBinOp 32 (fun _ _ => «B») 0 0"
for rip in [False, True]:
  mem_rule("load", "vbroadcastss_load", "`vbroadcastss m32, %dst` (any width): 4 readable bytes, any alignment.",
           "{w : AvxWidth} (dst : AvxReg w)", "w", ".vbroadcastss dst MEM", 4,
           f"zmms := s.zmms.set dst ({BCAST.replace('«B»', M(32))})", rip=rip)
reg_rule("vbroadcastss_reg", "`vbroadcastss %xmm, %dst` (register form).",
         "{w : AvxWidth} (dst : AvxReg w) (src : AvxReg .W128)", "w", ".vbroadcastss dst (.avx src)",
         f"zmms := s.zmms.set dst ({BCAST.replace('«B»', '((s.zmms.get src).setWidth 32)')})")
mem_rule("load", "vinsertps_load", "`vinsertps $imm, m32, %src1, %dst`: 4 readable bytes, any alignment.",
         "(dst src1 : AvxReg .W128) (imm : UInt8)", ".W128", ".vinsertps dst src1 MEM imm", 4,
         f"zmms := s.zmms.set dst (BitVec.insertps imm (s.zmms.get src1) {M(32)})")
reg_rule("vinsertps_reg", "`vinsertps $imm, %src2, %src1, %dst` (register form).",
         "{w : AvxWidth} (dst src1 src2 : AvxReg .W128) (imm : UInt8)", "w", ".vinsertps dst src1 (.avx src2) imm",
         "zmms := s.zmms.set dst (BitVec.insertps imm (s.zmms.get src1)\n              ((s.zmms.get src2).dw ((imm.toNat >>> 6) % 4)))")
reg_rule("vpinsrd_reg", "`vpinsrd $imm, %r32, %src1, %dst`.",
         "{w : AvxWidth} (dst src1 : AvxReg .W128) (r : Reg64) (imm : UInt8)", "w", ".vpinsrd dst src1 (.reg (.low r .W32)) imm",
         "zmms := s.zmms.set dst (BitVec.packedBinOpIdx 32\n              (fun i x _ => if i = imm.toNat % 4 then (s.regs.get64 r).setWidth 32 else x)\n              (s.zmms.get src1) (s.zmms.get src1))")
reg_rule("vpextrd_reg", "`vpextrd $imm, %src, %r32`: the dword, zero-extended into the register.",
         "{w : AvxWidth} (r : Reg64) (src : AvxReg .W128) (imm : UInt8)", "w", ".vpextrd (.reg (.low r .W32)) src imm",
         "regs := s.regs.set64 r (((s.zmms.get src).dw (imm.toNat % 4)).setWidth 64)")

# ------------------------------------------------------------- legacy SSE
section("Legacy SSE moves", """
A register destination keeps bits 255..128 (`RegZmms.setLegacy`). 128-bit
memory operands are 16-byte aligned except for `movups`/`movdqu`; the
`m32`/`m64` operands of `movss`, `movsd`, `movq`, `movlps`, `movhps` are not
alignment-checked.
""")
X = "(s.zmms.get (.xmm x))"
for op, al in [("movdqa", True), ("movdqu", False), ("movups", False)]:
  a = 16 if al else None
  adoc = ", 16-byte aligned" if al else ", any alignment"
  for rip in ([False, True] if op == "movdqa" else [False]):
    mem_rule("load", f"{op}_load", f"`{op} m128, %xmm`: 16 readable bytes{adoc}.",
             "(x : RegMm)", ".W128", f".{op} (.avx (.xmm x)) MEM", 16,
             f"zmms := s.zmms.setLegacy (.xmm x) {M(128)}", a, rip=rip)
  mem_rule("store", f"{op}_store", f"`{op} %xmm, m128`: 16 owned bytes{adoc}.",
           "(x : RegMm)", ".W128", f".{op} MEM (.avx (.xmm x))", 16, X, a)
  reg_rule(f"{op}_reg", f"`{op} %xs, %xd`.", "(xd xs : RegMm)", ".W128",
           f".{op} (.avx (.xmm xd)) (.avx (.xmm xs))",
           "zmms := s.zmms.setLegacy (.xmm xd) (s.zmms.get (.xmm xs))")
mem_rule("load", "movaps_load", "`movaps sym(%rip), %xmm`: 16 readable bytes, 16-byte aligned.",
         "(x : RegMm)", ".W128", ".movaps (.avx (.xmm x)) MEM", 16,
         f"zmms := s.zmms.setLegacy (.xmm x) {M(128)}", 16, rip=True)
mem_rule("store", "movaps_store", "`movaps %xmm, m128`: 16 owned bytes, 16-byte aligned.",
         "(x : RegMm)", ".W128", ".movaps MEM (.avx (.xmm x))", 16, X, 16)
SC = [("movss", 4, 32), ("movsd", 8, 64), ("movqx", 8, 64)]
for op, n, bits in SC:
  mem_rule("load", f"{op}_load", f"`{op} m{bits}, %xmm`: {n} readable bytes, any alignment; bits 127..{bits} cleared.",
           "(x : RegMm)", ".W128", f".{op} (.avx (.xmm x)) MEM", n,
           f"zmms := s.zmms.setLegacy (.xmm x) ({M(bits)}.zeroExtend 128)")
  mem_rule("store", f"{op}_store", f"`{op} %xmm, m{bits}`: {n} owned bytes, any alignment.",
           "(x : RegMm)", ".W128", f".{op} MEM (.avx (.xmm x))", n, f"{X}.setWidth {bits}")
reg_rule("movss_reg", "`movss %xs, %xd`: merges the low float.", "(xd xs : RegMm)", ".W128",
         ".movss (.avx (.xmm xd)) (.avx (.xmm xs))",
         "zmms := s.zmms.setLegacy (.xmm xd)\n              ((s.zmms.get (.xmm xd)).extractLsb' 32 96 ++ (s.zmms.get (.xmm xs)).extractLsb' 0 32)")
reg_rule("movsd_reg", "`movsd %xs, %xd`: merges the low double.", "(xd xs : RegMm)", ".W128",
         ".movsd (.avx (.xmm xd)) (.avx (.xmm xs))",
         "zmms := s.zmms.setLegacy (.xmm xd)\n              ((s.zmms.get (.xmm xd)).extractLsb' 64 64 ++ (s.zmms.get (.xmm xs)).extractLsb' 0 64)")
reg_rule("movqx_reg", "`movq %xs, %xd`: the low quadword, zero-extended.", "(xd xs : RegMm)", ".W128",
         ".movqx (.avx (.xmm xd)) (.avx (.xmm xs))",
         "zmms := s.zmms.setLegacy (.xmm xd) (((s.zmms.get (.xmm xs)).setWidth 64).zeroExtend 128)")
mem_rule("load", "movlps_load", "`movlps m64, %xmm`: 8 readable bytes, any alignment; the low quadword replaced.",
         "(x : RegMm)", ".W128", ".movlps (.avx (.xmm x)) MEM", 8,
         f"zmms := s.zmms.setLegacy (.xmm x) ({X}.extractLsb' 64 64 ++ {M(64)})")
mem_rule("store", "movlps_store", "`movlps %xmm, m64`: 8 owned bytes, any alignment.",
         "(x : RegMm)", ".W128", ".movlps MEM (.avx (.xmm x))", 8, f"{X}.setWidth 64")
mem_rule("load", "movhps_load", "`movhps m64, %xmm`: 8 readable bytes, any alignment; the high quadword replaced.",
         "(x : RegMm)", ".W128", ".movhps (.avx (.xmm x)) MEM", 8,
         f"zmms := s.zmms.setLegacy (.xmm x) ({M(64)} ++ {X}.extractLsb' 0 64)")
mem_rule("store", "movhps_store", "`movhps %xmm, m64`: 8 owned bytes, any alignment; the high quadword stored.",
         "(x : RegMm)", ".W128", ".movhps MEM (.avx (.xmm x))", 8, f"{X}.extractLsb' 64 64")
reg_rule("movlhps", "`movlhps %xs, %xd`.", "(xd xs : RegMm)", ".W128", ".movlhps (.xmm xd) (.xmm xs)",
         "zmms := s.zmms.setLegacy (.xmm xd)\n              ((s.zmms.get (.xmm xs)).extractLsb' 0 64 ++ (s.zmms.get (.xmm xd)).extractLsb' 0 64)")
reg_rule("movhlps", "`movhlps %xs, %xd`.", "(xd xs : RegMm)", ".W128", ".movhlps (.xmm xd) (.xmm xs)",
         "zmms := s.zmms.setLegacy (.xmm xd)\n              ((s.zmms.get (.xmm xd)).extractLsb' 64 64 ++ (s.zmms.get (.xmm xs)).extractLsb' 64 64)")

section("Legacy SSE arithmetic", """
`dst := f dst src`, with `src` a register or 16 bytes of 16-byte aligned
memory; `addss` and `movddup` read 4 and 8 bytes, unaligned.
""")
ADDPS = "BitVec.packedBinOp 32 (fun d c => Float32.toBitVec (BitVec.toFloat32 d + BitVec.toFloat32 c)) «A» «B»"
SUBPS = "BitVec.packedBinOp 32 (fun d c => Float32.toBitVec (BitVec.toFloat32 d - BitVec.toFloat32 c)) «A» «B»"
LEG = [
  ("addps", ADDPS, False, False),
  ("subps", SUBPS, False, False),
  ("mulps", "BitVec.packedBinOp 32 BitVec.f32mul «A» «B»", True, False),
  ("xorps", "«A» ^^^ «B»", True, False),
  ("shufps", "BitVec.shufps128 imm «A» «B»", True, True),
  ("unpcklps", "«B».dw 1 ++ «A».dw 1 ++ «B».dw 0 ++ «A».dw 0", True, False),
  ("punpckldq", "«B».dw 1 ++ «A».dw 1 ++ «B».dw 0 ++ «A».dw 0", True, False),
  ("unpckhps", "«B».dw 3 ++ «A».dw 3 ++ «B».dw 2 ++ «A».dw 2", True, False),
  ("punpckhdq", "«B».dw 3 ++ «A».dw 3 ++ «B».dw 2 ++ «A».dw 2", True, False),
  ("haddps", "BitVec.haddps128 «A» «B»", True, False),
  ("movshdup", "«B».dw 3 ++ «B».dw 3 ++ «B».dw 1 ++ «B».dw 1", True, False),
  ("pxor", "«A» ^^^ «B»", True, False),
  ("pand", "«A» &&& «B»", True, False),
  ("pcmpeqd", "BitVec.packedBinOp 32\n              (fun x y => if x = y then BitVec.allOnes 32 else 0#32) «A» «B»", True, False),
  ("pshufd", "BitVec.pshufd128 imm «B»", True, True),
]
DSTFORM = {"addps", "subps", "mulps", "xorps"}  # these take an AvxDst
for op, f, needreg, imm in LEG:
  ia = " (imm : UInt8)" if imm else ""
  isfx = " imm" if imm else ""
  idoc = "$imm, " if imm else ""
  dm = "(.avx (.xmm x))" if op in DSTFORM else "(.xmm x)"
  v = f.replace("«A»", X).replace("«B»", M(128))
  mem_rule("load", f"{op}_load", f"`{op} {idoc}m128, %xmm`: 16 readable bytes, 16-byte aligned.",
           f"(x : RegMm){ia}", ".W128", f".{op} {dm} MEM{isfx}", 16,
           f"zmms := s.zmms.setLegacy (.xmm x) ({v})", 16)
  if needreg:
    dr = "(.avx (.xmm xd))" if op in DSTFORM else "(.xmm xd)"
    vr = f.replace("«A»", "(s.zmms.get (.xmm xd))").replace("«B»", "(s.zmms.get (.xmm xs))")
    reg_rule(f"{op}_reg", f"`{op} {idoc}%xs, %xd`.", f"(xd xs : RegMm){ia}", ".W128",
             f".{op} {dr} (.avx (.xmm xs)){isfx}",
             f"zmms := s.zmms.setLegacy (.xmm xd) ({vr})")
ADDSS = "«A».extractLsb' 32 96 ++ BitVec.f32add («A».extractLsb' 0 32) «B»"
mem_rule("load", "addss_load", "`addss m32, %xmm`: 4 readable bytes, any alignment.",
         "(x : RegMm)", ".W128", ".addss (.xmm x) MEM", 4,
         f"zmms := s.zmms.setLegacy (.xmm x) ({ADDSS.replace('«A»', X).replace('«B»', M(32))})")
reg_rule("addss_reg", "`addss %xs, %xd`.", "(xd xs : RegMm)", ".W128", ".addss (.xmm xd) (.avx (.xmm xs))",
         f"zmms := s.zmms.setLegacy (.xmm xd)\n              ({ADDSS.replace('«A»', '(s.zmms.get (.xmm xd))').replace('«B»', '((s.zmms.get (.xmm xs)).setWidth 32)')})")
mem_rule("load", "movddup_load", "`movddup m64, %xmm`: 8 readable bytes, any alignment.",
         "(x : RegMm)", ".W128", ".movddup (.xmm x) MEM", 8,
         f"zmms := s.zmms.setLegacy (.xmm x) ({M(64)} ++ {M(64)})")
reg_rule("movddup_reg", "`movddup %xs, %xd`.", "(xd xs : RegMm)", ".W128", ".movddup (.xmm xd) (.avx (.xmm xs))",
         "zmms := s.zmms.setLegacy (.xmm xd)\n              ((s.zmms.get (.xmm xs)).setWidth 64 ++ (s.zmms.get (.xmm xs)).setWidth 64)")

emit("end Specs\n")
open(sys.argv[2], "w").write("\n".join(out))
with open(sys.argv[3], "w") as fh:
  for n, d in names:
    fh.write(f"MachineWP.{n}\t{d}\n")
print(len(names), "rules")
