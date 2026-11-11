import sys
out=[]
MEM="⟨some (.reg b), idx, .int64 d⟩"
RIP="⟨some .rip, none, .sub (.label l) .after_current_instruction⟩"
ADDR_MEM="s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec"
ADDR_RIP="(L l).toBitVec"
def rule(name, doc, params, instr_reg, post, asz_generic=True):
    pass
# ops: (name, ctor, n bytes, result(b) as expression over A=(s.zmms.get src1), doc, rip?)
A="(s.zmms.get src1)"
ops=[
 ("vsubss","vsubss",4,lambda b:f"{A}.extractLsb' 32 96 ++ BitVec.f32sub ({A}.extractLsb' 0 32) {b}","`dst := src1 - src2` on the low float",False),
 ("vmulss","vmulss",4,lambda b:f"{A}.extractLsb' 32 96 ++ BitVec.f32mul ({A}.extractLsb' 0 32) {b}","`dst := src1 * src2` on the low float",False),
 ("vdivss","vdivss",4,lambda b:f"{A}.extractLsb' 32 96 ++ BitVec.f32div ({A}.extractLsb' 0 32) {b}","`dst := src1 / src2` on the low float",True),
 ("vminss","vminss",4,lambda b:f"{A}.extractLsb' 32 96 ++ BitVec.f32min ({A}.extractLsb' 0 32) {b}","`dst := min src1 src2` on the low float",True),
 ("vsqrtss","vsqrtss",4,lambda b:f"{A}.extractLsb' 32 96 ++ BitVec.f32sqrt {b}","`dst := sqrt src2` on the low float, the rest from `src1`",False),
 ("vmulsd","vmulsd",8,lambda b:f"{A}.extractLsb' 64 64 ++ BitVec.f64mul ({A}.extractLsb' 0 64) {b}","`dst := src1 * src2` on the low double",False),
 ("vcvtss2sd","vcvtss2sd",4,lambda b:f"{A}.extractLsb' 64 64 ++ BitVec.f32to64 {b}","the low float of `src2` widened to the low double",False),
 ("vcvtsd2ss","vcvtsd2ss",8,lambda b:f"{A}.extractLsb' 32 96 ++ BitVec.f64to32 {b}","the low double of `src2` narrowed to the low float",False),
 ("vcmpss","vcmpss pred",4,lambda b:f"{A}.extractLsb' 32 96 ++ (if BitVec.f32cmpPred pred ({A}.extractLsb' 0 32) {b} then BitVec.allOnes 32 else 0#32)","the low element all ones if predicate `pred` holds of `src1`, `src2`, else zero",True),
]
def head(name, params, pre, instr, doc, low=True):
    return f"""/-- {doc} -/
@[spec low] theorem MachineWP.{name} {params} :
    ⦃ fun s =>{pre} ⦄
      (Directive.instr {instr} :: p)
    ⦃ Q; E ⦄ := by {"mem_rule" if 'Mem.loadInt' in pre else "reg_rule"}
"""
def loadpre(addr, n, upd):
    return f"""
        let a := {addr}
        ((Mem.loadInt s.dmem a {n}).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a {n} = some v →
            WP.wp p Q E {{ s with {upd} }})"""
def storepre(addr,n,val):
    return f"""
        let a := {addr}
        ((Mem.loadInt s.dmem a {n}).isSome = true)
          ⊓ WP.wp p Q E {{ s with dmem := Mem.storeInt s.dmem a {n} {val} }}"""
for (nm,ctor,n,res,doc,rip) in ops:
    bits=8*n
    pp = "(pred : UInt8) " if nm=="vcmpss" else ""
    out.append(f"/-! ### {nm} -/\n")
    rb=f"((s.zmms.get src2).setWidth {bits})"
    out.append(head(f"{nm}_reg_spec", "{w : AvxWidth} (asz : Width) "+pp+"(dst src1 src2 : AvxReg .W128)",
      f"\n        WP.wp p Q E {{ s with zmms := (s.zmms.set dst\n          ({res(rb)})) }}",
      f"(.avx asz w (.{ctor} dst src1 (.avx src2)))", f"`{nm} %src2, %src1, %dst`: {doc}."))
    mb=f"(BitVec.ofInt {bits} v)"
    out.append(head(f"{nm}_load_mem_spec", pp+"(dst src1 : AvxReg .W128) (b : Reg64) (idx : Option AddrIndex) (d : Int64)",
      loadpre(ADDR_MEM,n,f"zmms := s.zmms.set dst\n              ({res(mb)})"),
      f"(.avx .W64 .W128 (.{ctor} dst src1 (.mem {MEM})))", f"`{nm} d(%b,%i,s), %src1, %dst`: the {n} bytes must be present; {doc}."))
    if rip:
        out.append(head(f"{nm}_load_rip_spec", pp+"(dst src1 : AvxReg .W128) (l : Label)",
          loadpre(ADDR_RIP,n,f"zmms := s.zmms.set dst\n              ({res(mb)})"),
          f"(.avx .W64 .W128 (.{ctor} dst src1 (.mem {RIP})))", f"`{nm} sym(%rip), %src1, %dst`: the {n} bytes at `sym` must be present."))
# vaddssMem
ADD=lambda b:f"{A}.extractLsb' 32 96 ++ BitVec.f32add ({A}.extractLsb' 0 32) {b}"
out.append("/-! ### vaddss with a memory operand -/\n")
out.append(head("vaddss_load_mem_spec","(dst src1 : AvxReg .W128) (b : Reg64) (idx : Option AddrIndex) (d : Int64)",
  loadpre(ADDR_MEM,4,f"zmms := s.zmms.set dst\n              ({ADD('(BitVec.ofInt 32 v)')})"),
  f"(.avx .W64 .W128 (.vaddssMem dst src1 {MEM}))","`vaddss d(%b,%i,s), %src1, %dst`: the 4 bytes must be present."))
out.append(head("vaddss_load_rip_spec","(dst src1 : AvxReg .W128) (l : Label)",
  loadpre(ADDR_RIP,4,f"zmms := s.zmms.set dst\n              ({ADD('(BitVec.ofInt 32 v)')})"),
  f"(.avx .W64 .W128 (.vaddssMem dst src1 {RIP}))","`vaddss sym(%rip), %src1, %dst`: the 4 bytes at `sym` must be present."))
# vucomis
for nm,n,cmp in [("vucomiss",4,"f32cmp"),("vucomisd",8,"f64cmp")]:
    bits=8*n
    out.append(f"/-! ### {nm} -/\n")
    out.append(head(f"{nm}_reg_spec","{w : AvxWidth} (asz : Width) (src1 src2 : AvxReg .W128)",
      f"\n        WP.wp p Q E {{ s with status := StatusFlags.ofFCmp\n          (BitVec.{cmp} ((s.zmms.get src1).extractLsb' 0 {bits}) ((s.zmms.get src2).setWidth {bits})) }}",
      f"(.avx asz w (.{nm} src1 (.avx src2)))", f"`{nm} %src2, %src1`: the flags of the unordered compare of the low elements."))
    out.append(head(f"{nm}_load_mem_spec","(src1 : AvxReg .W128) (b : Reg64) (idx : Option AddrIndex) (d : Int64)",
      loadpre(ADDR_MEM,n,f"status := StatusFlags.ofFCmp\n              (BitVec.{cmp} ((s.zmms.get src1).extractLsb' 0 {bits}) (BitVec.ofInt {bits} v))"),
      f"(.avx .W64 .W128 (.{nm} src1 (.mem {MEM})))", f"`{nm} d(%b,%i,s), %src1`: the {n} bytes must be present."))
# vcvtsi2ss
CV=lambda b:f"{A}.extractLsb' 32 96 ++ BitVec.sitof32 {b}"
out.append("/-! ### vcvtsi2ss -/\n")
out.append(head("vcvtsi2ss_reg32_spec","{w : AvxWidth} (asz : Width) (dst src1 : AvxReg .W128) (r : Reg64)",
  f"\n        WP.wp p Q E {{ s with zmms := s.zmms.set dst\n          ({CV('((s.regs.get64 r).setWidth 32)')}) }}",
  "(.avx asz w (.vcvtsi2ss dst src1 (RegOrMem.reg (.low r .W32))))","`vcvtsi2ss %r32, %src1, %dst`: the signed 32-bit integer rounded to the low float."))
out.append(head("vcvtsi2ss_reg64_spec","{w : AvxWidth} (asz : Width) (dst src1 : AvxReg .W128) (r : Reg64)",
  f"\n        WP.wp p Q E {{ s with zmms := s.zmms.set dst\n          ({CV('(s.regs.get64 r)')}) }}",
  "(.avx asz w (.vcvtsi2ss dst src1 (RegOrMem.reg (.low r .W64))))","`vcvtsi2ss %r64, %src1, %dst`: the signed 64-bit integer rounded to the low float."))
out.append(head("vcvtsi2ss_load32_mem_spec","(dst src1 : AvxReg .W128) (b : Reg64) (idx : Option AddrIndex) (d : Int64)",
  loadpre(ADDR_MEM,4,f"zmms := s.zmms.set dst\n              ({CV('(BitVec.ofInt 32 v)')})"),
  f"(.avx .W64 .W128 (.vcvtsi2ss dst src1 (RegOrMem.mem (w := .W32) {MEM})))","`vcvtsi2ssl d(%b,%i,s), %src1, %dst`: the 4 bytes must be present."))
# vcvtps2pd
out.append("/-! ### vcvtps2pd -/\n")
PB="((s.zmms.get src).setWidth 64)"
out.append(head("vcvtps2pd_reg_spec","{w : AvxWidth} (asz : Width) (dst src : AvxReg .W128)",
  f"\n        WP.wp p Q E {{ s with zmms := s.zmms.set dst\n          (BitVec.f32to64 ({PB}.dw 1) ++ BitVec.f32to64 ({PB}.dw 0)) }}",
  "(.avx asz w (.vcvtps2pd dst (.avx src)))","`vcvtps2pd %src, %dst`: the two low floats widened to doubles."))
# vmovd / vmovq
for nm,ctorTo,ctorFrom,W,n in [("vmovd","vmovdTo","vmovdFrom",".W32",4),("vmovq","vmovqTo","vmovqFrom",".W64",8)]:
    bits=8*n
    out.append(f"/-! ### {nm} -/\n")
    rv = "((s.regs.get64 r).setWidth 32)" if n==4 else "(s.regs.get64 r)"
    out.append(head(f"{nm}_to_reg_spec","{w : AvxWidth} (asz : Width) (dst : AvxReg .W128) (r : Reg64)",
      f"\n        WP.wp p Q E {{ s with zmms := s.zmms.set dst ({rv}.zeroExtend 128) }}",
      f"(.avx asz w (.{ctorTo} dst (RegOrMem.reg (.low r {W}))))",f"`{nm} %r, %xmm`: the register zero-extended into the xmm register."))
    out.append(head(f"{nm}_to_load_mem_spec","(dst : AvxReg .W128) (b : Reg64) (idx : Option AddrIndex) (d : Int64)",
      loadpre(ADDR_MEM,n,f"zmms := s.zmms.set dst ((BitVec.ofInt {bits} v).zeroExtend 128)"),
      f"(.avx .W64 .W128 (.{ctorTo} dst (RegOrMem.mem {MEM})))",f"`{nm} d(%b,%i,s), %xmm`: the {n} bytes must be present; they are zero-extended into the register."))
    if n==4:
        out.append(head(f"{nm}_to_load_rip_spec","(dst : AvxReg .W128) (l : Label)",
          loadpre(ADDR_RIP,n,f"zmms := s.zmms.set dst ((BitVec.ofInt {bits} v).zeroExtend 128)"),
          f"(.avx .W64 .W128 (.{ctorTo} dst (RegOrMem.mem {RIP})))",f"`{nm} sym(%rip), %xmm`: the {n} bytes at `sym` must be present."))
    sv = f"(((s.zmms.get src).setWidth 32).setWidth 64)" if n==4 else "((s.zmms.get src).setWidth 64)"
    out.append(head(f"{nm}_from_reg_spec","{w : AvxWidth} (asz : Width) (r : Reg64) (src : AvxReg .W128)",
      f"\n        WP.wp p Q E {{ s with regs := s.regs.set64 r {sv} }}",
      f"(.avx asz w (.{ctorFrom} (RegOrMem.reg (.low r {W})) src))",f"`{nm} %xmm, %r`: the low {bits} bits of the xmm register{', zero-extended' if n==4 else ''}."))
    out.append(head(f"{nm}_from_store_mem_spec","(b : Reg64) (idx : Option AddrIndex) (d : Int64) (src : AvxReg .W128)",
      storepre(ADDR_MEM,n,f"((s.zmms.get src).setWidth {bits}).toInt"),
      f"(.avx .W64 .W128 (.{ctorFrom} (RegOrMem.mem {MEM}) src))",f"`{nm} %xmm, d(%b,%i,s)`: the {n} bytes must be present; they get the low {bits} bits of the register."))
# Every `sym(%rip)` rule gets a `sym+o(%rip)` twin (`_rip_off_spec`).
RIPO="⟨some .rip, none, .sub (.add (.label l) (.int64 o)) .after_current_instruction⟩"
def rip_off(r):
    return (r.replace("_rip_spec", "_rip_off_spec").replace("(l : Label)", "(l : Label) (o : Int64)")
             .replace(RIP, RIPO).replace(f"let a := {ADDR_RIP}", f"let a := {ADDR_RIP} + o.toBitVec")
             .replace("sym(%rip)", "sym+o(%rip)").replace("at `sym`", "at `sym+o`"))
out = [x for r in out for x in ([r, rip_off(r)] if RIP in r else [r])]
# The vxorpd register form is MachineWP.vxorpd_reg_spec in PackedSse.lean.
# A record field whose value spans two lines must be parenthesised: Lean does
# not continue an application across the line break inside `{ s with … }`.
import re
txt = "\n".join(out)
txt = re.sub(r"(\{ s with (?:zmms|status|regs) := )(?!\()((?:(?! \}).)*?\n(?:(?! \}).)*?)( \})",
             lambda m: m.group(1) + "(" + m.group(2) + ")" + m.group(3), txt, flags=re.S)
print(txt)
