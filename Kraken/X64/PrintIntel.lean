import Kraken.X64.Syntax
/-!
# IntelPrinter
This file prints Kraken-supported x64 assembly in Intel syntax.
This is different from Parser.lean which expects AT&T syntax.
-/

instance : ToString Reg64 where
  toString r := match r with
  | .rax => "rax" | .rbx => "rbx" | .rcx => "rcx" | .rdx => "rdx"
  | .rsi => "rsi" | .rdi => "rdi" | .rsp => "rsp" | .rbp => "rbp"
  | .r8  => "r8"  | .r9  => "r9"  | .r10 => "r10" | .r11 => "r11"
  | .r12 => "r12" | .r13 => "r13" | .r14 => "r14" | .r15 => "r15"

instance : ToString RegMm where
  toString r := match r with
  | .mm0  => "mm0"  | .mm1  => "mm1"  | .mm2  => "mm2"  | .mm3  => "mm3"
  | .mm4  => "mm4"  | .mm5  => "mm5"  | .mm6  => "mm6"  | .mm7  => "mm7"
  | .mm8  => "mm8"  | .mm9  => "mm9"  | .mm10 => "mm10" | .mm11 => "mm11"
  | .mm12 => "mm12" | .mm13 => "mm13" | .mm14 => "mm14" | .mm15 => "mm15"
  | .mm16 => "mm16" | .mm17 => "mm17" | .mm18 => "mm18" | .mm19 => "mm19"
  | .mm20 => "mm20" | .mm21 => "mm21" | .mm22 => "mm22" | .mm23 => "mm23"
  | .mm24 => "mm24" | .mm25 => "mm25" | .mm26 => "mm26" | .mm27 => "mm27"
  | .mm28 => "mm28" | .mm29 => "mm29" | .mm30 => "mm30" | .mm31 => "mm31"

def Reg.toStr {w} (r : Reg w) : String := match w, r with
  | .W64, .low r _ => toString r
  | .W32, .low r _ => match r with
    | .rax => "eax" | .rbx => "ebx" | .rcx => "ecx" | .rdx => "edx"
    | .rsi => "esi" | .rdi => "edi" | .rsp => "esp" | .rbp => "ebp"
    | .r8  => "r8d" | .r9  => "r9d" | .r10 => "r10d" | .r11 => "r11d"
    | .r12 => "r12d"| .r13 => "r13d"| .r14 => "r14d"| .r15 => "r15d"
  | .W16, .low r _ => match r with
    | .rax => "ax" | .rbx => "bx" | .rcx => "cx" | .rdx => "dx"
    | .rsi => "si" | .rdi => "di" | .rsp => "sp" | .rbp => "bp"
    | .r8  => "r8w" | .r9  => "r9w" | .r10 => "r10w" | .r11 => "r11w"
    | .r12 => "r12w"| .r13 => "r13w"| .r14 => "r14w"| .r15 => "r15w"
  | .W8, .low r _ => match r with
    | .rax => "al" | .rbx => "bl" | .rcx => "cl" | .rdx => "dl"
    | .rsi => "sil" | .rdi => "dil" | .rsp => "spl" | .rbp => "bpl"
    | .r8  => "r8b" | .r9  => "r9b" | .r10 => "r10b" | .r11 => "r11b"
    | .r12 => "r12b"| .r13 => "r13b"| .r14 => "r14b"| .r15 => "r15b"
  | .W8, .ah => "ah" | .W8, .bh => "bh" | .W8, .ch => "ch" | .W8, .dh => "dh"

instance {w} : ToString (Reg w) where toString := Reg.toStr

instance {w} : ToString (AvxReg w) where
  toString r := match r with
  | .xmm r => "x" ++ toString r
  | .ymm r => "y" ++ toString r
  | .zmm r => "z" ++ toString r

def RegOrRip.toStr (b : RegOrRip) (addr_w : Width := .W64) : String := match b with
  | .reg r => toString (Reg.low r addr_w)
  | .rip => "rip"
instance : ToString RegOrRip where toString b := b.toStr

def ConstExpr.toStr : ConstExpr → String
  | .label l => l
  | .int64 i => s!"{i}"
  | .before_current_instruction => "."
  | .after_current_instruction => "."
  | .add e1 e2 => s!"({e1.toStr} + {e2.toStr})"
  | .sub e1 e2 => s!"({e1.toStr} - {e2.toStr})"
instance : ToString ConstExpr where toString := ConstExpr.toStr

def AddrExpr.toStr (a : AddrExpr) (addr_w : Width := .W64) : String :=
  let dispStr := match a.base, a.disp with
    -- Unwrap RIP-relative displacements back to just the label for printing
    -- (like RelRegOrMem.toStr below)
    | .some .rip, .sub e .after_current_instruction => toString e
    | _, _ => toString a.disp
  "[" ++ "+".intercalate (
    (match a.base with | .some b => [b.toStr addr_w] | _ => [])
    ++ (match a.idx with | .some ⟨r, s⟩ => [s!"{Reg.low r addr_w}*{s.bytes}"] | _ => [])
    ++ [dispStr]
  ) ++ "]"

def RegOrMem.toStr {w} (rm : RegOrMem w) (addr_w : Width := .W64) : String := match rm with
  | .reg r => ToString.toString r
  | .mem a => match w with
    | .W64 => "QWORD PTR " ++ a.toStr addr_w
    | .W32 => "DWORD PTR " ++ a.toStr addr_w
    | .W16 => "WORD PTR " ++ a.toStr addr_w
    | .W8 => "BYTE PTR " ++ a.toStr addr_w
instance {w} : ToString (RegOrMem w) where toString rm := rm.toStr

def AvxRegOrMem.toStr {w} (rm : AvxRegOrMem w) (addr_w : Width := .W64) : String := match rm with
  | .avx r => ToString.toString r
  | .mem a => match w with
    | .W512 => "ZMMWORD PTR " ++ a.toStr addr_w
    | .W256 => "YMMWORD PTR " ++ a.toStr addr_w
    | .W128 => "XMMWORD PTR " ++ a.toStr addr_w
instance {w} : ToString (AvxRegOrMem w) where toString rm := rm.toStr

/-- An xmm register, or a scalar memory operand of `n` bits (`m32`, `m64`). -/
def AvxRegOrMem.toStrLow {w} (rm : AvxRegOrMem w) (n : Width) (addr_w : Width := .W64) : String :=
  match rm with
  | .avx r => ToString.toString r
  | .mem a => (RegOrMem.mem (w := n) a).toStr addr_w

def Operand.toStr {w} (op : Operand w) (addr_w : Width := .W64) : String := match op with
  | .regOrMem rm => rm.toStr addr_w
  | .imm v => toString v
instance {w} : ToString (Operand w) where toString op := op.toStr

def AvxOperand.toStr {w} (op : AvxOperand w) (addr_w : Width := .W64) : String := match op with
  | .regOrMem rm => rm.toStr addr_w
instance {w} : ToString (AvxOperand w) where toString op := op.toStr

def RelRegOrMem.toStr (rel : RelRegOrMem) (addr_w : Width := .W64) : String := match rel with
  | .rel (.sub e .after_current_instruction) => toString e
  | .rel c => toString c
  | .reg r => toString r
  | .mem a => "QWORD PTR " ++ a.toStr addr_w
instance : ToString RelRegOrMem where toString rel := rel.toStr

instance : ToString CondCode where toString
  | .z => "e" | .nz => "ne" | .c => "b" | .nc => "ae" | .a => "a" | .be => "be" | .l => "l" | .le => "le"
  | .ge => "ge" | .g => "g" | .p => "p" | .np => "np"
  | .s => "s" | .ns => "ns"

instance : ToString ShiftCountExpr where toString
  | .cl => "cl"
  | .imm8 v => ToString.toString v

set_option maxHeartbeats 2000000 in
def Operation.toStr {w} (op : Operation w) (addr_w : Width := .W64) : String := match op with
  | .mov dst src => s!"mov {dst.toStr addr_w}, {src.toStr addr_w}"
  | @Operation.movsx _ w' dst src =>
    -- Intel spells the 32-to-64-bit form `movsxd` (opcode 63 /r, AT&T `movslq`).
    let m := if w == .W64 && w' == .W32 then "movsxd" else "movsx"
    s!"{m} {dst.toStr addr_w}, {src.toStr addr_w}"
  | .movzx dst src => s!"movzx {dst.toStr addr_w}, {src.toStr addr_w}"
  | .push src => s!"push {src.toStr addr_w}"
  | .pop dst => s!"pop {dst.toStr addr_w}"
  | .setcc cc dst => s!"set{cc} {dst.toStr addr_w}"
  | .cmovcc cc dst src => s!"cmov{cc} {dst}, {src.toStr addr_w}"
  | .lea dst src => s!"lea {dst}, {src.toStr addr_w}"
  | .add dst src => s!"add {dst.toStr addr_w}, {src.toStr addr_w}"
  | .adc dst src => s!"adc {dst.toStr addr_w}, {src.toStr addr_w}"
  | .adcx dst src => s!"adcx {dst}, {src.toStr addr_w}"
  | .adox dst src => s!"adox {dst}, {src.toStr addr_w}"
  | .inc dst => s!"inc {dst.toStr addr_w}"
  | .dec dst => s!"dec {dst.toStr addr_w}"
  | .neg dst => s!"neg {dst.toStr addr_w}"
  | .sub dst src => s!"sub {dst.toStr addr_w}, {src.toStr addr_w}"
  | .sbb dst src => s!"sbb {dst.toStr addr_w}, {src.toStr addr_w}"
  | .cmp a b => s!"cmp {a.toStr addr_w}, {b.toStr addr_w}"
  | .mul src => s!"mul {src.toStr addr_w}"
  | .mulx hi lo src => s!"mulx {hi}, {lo}, {src.toStr addr_w}"
  | .imul none src1 src2 => s!"imul {src1.toStr addr_w}, {src2.toStr addr_w}"
  | .imul (some dst) src1 src2 => s!"imul {dst.toStr addr_w}, {src1.toStr addr_w}, {src2.toStr addr_w}"
  | .imul1 src => s!"imul {src.toStr addr_w}"
  | .div src => s!"div {src.toStr addr_w}"
  | .idiv src => s!"idiv {src.toStr addr_w}"
  | .test a b => s!"test {a.toStr addr_w}, {b.toStr addr_w}"
  | .and dst src => s!"and {dst.toStr addr_w}, {src.toStr addr_w}"
  | .not dst => s!"not {dst.toStr addr_w}"
  | .or dst src => s!"or {dst.toStr addr_w}, {src.toStr addr_w}"
  | .xor dst src => s!"xor {dst.toStr addr_w}, {src.toStr addr_w}"
  | .shl dst cnt => s!"shl {dst.toStr addr_w}, {cnt}"
  | .shr dst cnt => s!"shr {dst.toStr addr_w}, {cnt}"
  | .sar dst cnt => s!"sar {dst.toStr addr_w}, {cnt}"
  | .shld dst src cnt => s!"shld {dst.toStr addr_w}, {src}, {cnt}"
  | .shrd dst src cnt => s!"shrd {dst.toStr addr_w}, {src}, {cnt}"
  | .rol dst cnt => s!"rol {dst.toStr addr_w}, {cnt}"
  | .ror dst cnt => s!"ror {dst.toStr addr_w}, {cnt}"
  | .rcl dst cnt => s!"rcl {dst.toStr addr_w}, {cnt}"
  | .rcr dst cnt => s!"rcr {dst.toStr addr_w}, {cnt}"
  | .bswap dst => s!"bswap {dst}"
  | .cltq => "cdqe"
  | .cltd => "cdq"
  | .ud1 dst src => s!"ud1 {dst}, {src.toStr addr_w}"
  | .ud2 => "ud2"
  | .int3 => "int3"
  | .jcc cc l => s!"j{cc} {l}"
  | .jmp tgt => s!"jmp {tgt.toStr addr_w}"
  | .call tgt => s!"call {tgt.toStr addr_w}"
  | .ret => "ret"
  | .nop n => s!".nops {n}"
  | .nopalign a none => s!".align {a}"
  | .nopalign a (some p) => s!".align {a}, {p}"
instance {w} : ToString (Operation w) where toString op := op.toStr

/-- The mnemonic infix of the `cmpss` predicates 0..7. -/
def vcmpPredName (pred : UInt8) : Option String :=
  match pred.toNat with
  | 0 => some "eq" | 1 => some "lt" | 2 => some "le" | 3 => some "unord"
  | 4 => some "neq" | 5 => some "nlt" | 6 => some "nle" | 7 => some "ord"
  | _ => none

set_option maxHeartbeats 2000000 in
def AvxOperation.toStr {w} (op : AvxOperation w) (addr_w : Width := .W64) : String := match op with
  | .movups dst src => s!"movups {dst.toStr addr_w}, {src.toStr addr_w}"
  | .vmovups dst src => s!"vmovups {dst.toStr addr_w}, {src.toStr addr_w}"
  | .movaps dst src => s!"movaps {dst.toStr addr_w}, {src.toStr addr_w}"
  | .subps dst src => s!"subps {dst.toStr addr_w}, {src.toStr addr_w}"
  | .addps dst src => s!"addps {dst.toStr addr_w}, {src.toStr addr_w}"
  | .mulps dst src => s!"mulps {dst.toStr addr_w}, {src.toStr addr_w}"
  | .xorps dst src => s!"xorps {dst.toStr addr_w}, {src.toStr addr_w}"
  | .vmovaps dst src => s!"vmovaps {dst.toStr addr_w}, {src.toStr addr_w}"
  | .vxorps dst src1 src2 => s!"vxorps {dst}, {src1}, {src2.toStr addr_w}"
  | .vaddps dst src1 src2 => s!"vaddps {dst}, {src1}, {src2.toStr addr_w}"
  | .vmulps dst src1 src2 => s!"vmulps {dst}, {src1}, {src2.toStr addr_w}"
  | .vfmadd231ps dst src1 src2 => s!"vfmadd231ps {dst}, {src1}, {src2.toStr addr_w}"
  | .vfmadd132ps dst src1 src2 => s!"vfmadd132ps {dst}, {src1}, {src2.toStr addr_w}"
  | .vpermps dst src1 src2 => s!"vpermps {dst}, {src1}, {src2.toStr addr_w}"
  | .vshufps dst src1 src2 imm => s!"vshufps {dst}, {src1}, {src2.toStr addr_w}, {imm}"
  | .vextractf128 dst src imm => s!"vextractf128 {dst}, {src}, {imm}"
  | .vinsertf128 dst src1 src2 imm => s!"vinsertf128 {dst}, {src1}, {src2.toStr addr_w}, {imm}"
  | .vmovhlps dst src1 src2 => s!"vmovhlps {dst}, {src1}, {src2}"
  | .vmovss dst src1 src2 => s!"vmovss {dst}, {src1}, {src2}"
  | .vaddss dst src1 src2 => s!"vaddss {dst}, {src1}, {src2}"
  | .vzeroupper => "vzeroupper"
  | .vmovssMem dst src => s!"vmovss {dst.toStrLow .W32 addr_w}, {src.toStrLow .W32 addr_w}"
  | .vmovsdMem dst src => s!"vmovsd {dst.toStrLow .W64 addr_w}, {src.toStrLow .W64 addr_w}"
  | .vaddssMem dst src1 src2 => s!"vaddss {dst}, {src1}, {(RegOrMem.mem (w := .W32) src2).toStr addr_w}"
  | .vsubss dst src1 src2 => s!"vsubss {dst}, {src1}, {src2.toStrLow .W32 addr_w}"
  | .vmulss dst src1 src2 => s!"vmulss {dst}, {src1}, {src2.toStrLow .W32 addr_w}"
  | .vdivss dst src1 src2 => s!"vdivss {dst}, {src1}, {src2.toStrLow .W32 addr_w}"
  | .vminss dst src1 src2 => s!"vminss {dst}, {src1}, {src2.toStrLow .W32 addr_w}"
  | .vsqrtss dst src1 src2 => s!"vsqrtss {dst}, {src1}, {src2.toStrLow .W32 addr_w}"
  | .vmulsd dst src1 src2 => s!"vmulsd {dst}, {src1}, {src2.toStrLow .W64 addr_w}"
  | .vcmpss pred dst src1 src2 =>
    match vcmpPredName pred with
    | some n => s!"vcmp{n}ss {dst}, {src1}, {src2.toStrLow .W32 addr_w}"
    | none => s!"vcmpss {dst}, {src1}, {src2.toStrLow .W32 addr_w}, {pred}"
  | .vucomiss src1 src2 => s!"vucomiss {src1}, {src2.toStrLow .W32 addr_w}"
  | .vucomisd src1 src2 => s!"vucomisd {src1}, {src2.toStrLow .W64 addr_w}"
  | .vcvtsi2ss dst src1 src2 => s!"vcvtsi2ss {dst}, {src1}, {src2.toStr addr_w}"
  | .vcvtss2sd dst src1 src2 => s!"vcvtss2sd {dst}, {src1}, {src2.toStrLow .W32 addr_w}"
  | .vcvtsd2ss dst src1 src2 => s!"vcvtsd2ss {dst}, {src1}, {src2.toStrLow .W64 addr_w}"
  | .vcvtps2pd dst src => s!"vcvtps2pd {dst}, {src.toStrLow .W64 addr_w}"
  | .vmovdTo dst src => s!"vmovd {dst}, {src.toStr addr_w}"
  | .vmovdFrom dst src => s!"vmovd {dst.toStr addr_w}, {src}"
  | .vmovqTo dst src => s!"vmovq {dst}, {src.toStr addr_w}"
  | .vmovqFrom dst src => s!"vmovq {dst.toStr addr_w}, {src}"
  | .vmovapd dst src => s!"vmovapd {dst.toStr addr_w}, {src.toStr addr_w}"
  | .vmovdqa dst src => s!"vmovdqa {dst.toStr addr_w}, {src.toStr addr_w}"
  | .vxorpd dst src1 src2 => s!"vxorpd {dst}, {src1}, {src2.toStr addr_w}"
  | .vsubps dst src1 src2 => s!"vsubps {dst}, {src1}, {src2.toStr addr_w}"
  | .vdivps dst src1 src2 => s!"vdivps {dst}, {src1}, {src2.toStr addr_w}"
  | .vaddsubps dst src1 src2 => s!"vaddsubps {dst}, {src1}, {src2.toStr addr_w}"
  | .vandps dst src1 src2 => s!"vandps {dst}, {src1}, {src2.toStr addr_w}"
  | .vandnps dst src1 src2 => s!"vandnps {dst}, {src1}, {src2.toStr addr_w}"
  | .vpaddd dst src1 src2 => s!"vpaddd {dst}, {src1}, {src2.toStr addr_w}"
  | .vpand dst src1 src2 => s!"vpand {dst}, {src1}, {src2.toStr addr_w}"
  | .vpxor dst src1 src2 => s!"vpxor {dst}, {src1}, {src2.toStr addr_w}"
  | .vblendvps dst src1 src2 mask => s!"vblendvps {dst}, {src1}, {src2.toStr addr_w}, {mask}"
  | .vshufpd dst src1 src2 imm => s!"vshufpd {dst}, {src1}, {src2.toStr addr_w}, {imm}"
  | .vpblendw dst src1 src2 imm => s!"vpblendw {dst}, {src1}, {src2.toStr addr_w}, {imm}"
  | .vpermilps dst src imm => s!"vpermilps {dst}, {src.toStr addr_w}, {imm}"
  | .vpslld dst src imm => s!"vpslld {dst}, {src}, {imm}"
  | .vmovshdup dst src => s!"vmovshdup {dst}, {src.toStr addr_w}"
  | .vmovsldup dst src => s!"vmovsldup {dst}, {src.toStr addr_w}"
  | .vbroadcastss dst src => s!"vbroadcastss {dst}, {src.toStrLow .W32 addr_w}"
  | .vinsertps dst src1 src2 imm => s!"vinsertps {dst}, {src1}, {src2.toStrLow .W32 addr_w}, {imm}"
  | .vpinsrd dst src1 src2 imm => s!"vpinsrd {dst}, {src1}, {src2.toStr addr_w}, {imm}"
  | .vpextrd dst src imm => s!"vpextrd {dst.toStr addr_w}, {src}, {imm}"
  | .vmovlpsStore dst src => s!"vmovlps {(RegOrMem.mem (w := .W64) dst).toStr addr_w}, {src}"
  | .vmovdqu dst src => s!"vmovdqu {dst.toStr addr_w}, {src.toStr addr_w}"
  | .vcvtdq2ps dst src => s!"vcvtdq2ps {dst}, {src.toStr addr_w}"
  | .vblendps dst src1 src2 imm => s!"vblendps {dst}, {src1}, {src2.toStr addr_w}, {imm}"
  | .vpaddw dst src1 src2 => s!"vpaddw {dst}, {src1}, {src2.toStr addr_w}"
  | .vpminsd dst src1 src2 => s!"vpminsd {dst}, {src1}, {src2.toStr addr_w}"
  | .vpshufb dst src1 src2 => s!"vpshufb {dst}, {src1}, {src2.toStr addr_w}"
  | .vpunpcklqdq dst src1 src2 => s!"vpunpcklqdq {dst}, {src1}, {src2.toStr addr_w}"
  | .vpshufd dst src imm => s!"vpshufd {dst}, {src.toStr addr_w}, {imm}"
  | .vcvtss2si dst src => s!"vcvtss2si {dst}, {src.toStrLow .W32 addr_w}"
  | .vpinsrw dst src1 src2 imm => s!"vpinsrw {dst}, {src1}, {src2}, {imm}"
  | .vpmovsxwd dst src => s!"vpmovsxwd {dst}, {src.toStrLow .W64 addr_w}"
  | .vpcmpeqd dst src1 src2 => s!"vpcmpeqd {dst}, {src1}, {src2.toStr addr_w}"
  | .vpsrldx dst src count => s!"vpsrld {dst}, {src}, {count}"
  | .vpmovzxdq dst src => s!"vpmovzxdq {dst}, {src.toStrLow .W64 addr_w}"
  | .movss dst src => s!"movss {dst.toStrLow .W32 addr_w}, {src.toStrLow .W32 addr_w}"
  | .movsd dst src => s!"movsd {dst.toStrLow .W64 addr_w}, {src.toStrLow .W64 addr_w}"
  | .movqx dst src => s!"movq {dst.toStrLow .W64 addr_w}, {src.toStrLow .W64 addr_w}"
  | .movlps dst src => s!"movlps {dst.toStrLow .W64 addr_w}, {src.toStrLow .W64 addr_w}"
  | .movhps dst src => s!"movhps {dst.toStrLow .W64 addr_w}, {src.toStrLow .W64 addr_w}"
  | .movdqa dst src => s!"movdqa {dst.toStr addr_w}, {src.toStr addr_w}"
  | .movdqu dst src => s!"movdqu {dst.toStr addr_w}, {src.toStr addr_w}"
  | .addss dst src => s!"addss {dst}, {src.toStrLow .W32 addr_w}"
  | .movlhps dst src => s!"movlhps {dst}, {src}"
  | .movhlps dst src => s!"movhlps {dst}, {src}"
  | .shufps dst src imm => s!"shufps {dst}, {src.toStr addr_w}, {imm}"
  | .unpcklps dst src => s!"unpcklps {dst}, {src.toStr addr_w}"
  | .unpckhps dst src => s!"unpckhps {dst}, {src.toStr addr_w}"
  | .haddps dst src => s!"haddps {dst}, {src.toStr addr_w}"
  | .movddup dst src => s!"movddup {dst}, {src.toStrLow .W64 addr_w}"
  | .movshdup dst src => s!"movshdup {dst}, {src.toStr addr_w}"
  | .pxor dst src => s!"pxor {dst}, {src.toStr addr_w}"
  | .pand dst src => s!"pand {dst}, {src.toStr addr_w}"
  | .pcmpeqd dst src => s!"pcmpeqd {dst}, {src.toStr addr_w}"
  | .pshufd dst src imm => s!"pshufd {dst}, {src.toStr addr_w}, {imm}"
  | .punpckldq dst src => s!"punpckldq {dst}, {src.toStr addr_w}"
  | .punpckhdq dst src => s!"punpckhdq {dst}, {src.toStr addr_w}"
instance {w} : ToString (Operation w) where toString op := op.toStr

instance : ToString Instr where
  toString i := match i with
  | .regular a _ o => o.toStr a
  | .avx a _ o => o.toStr a

instance : ToString Directive where
  toString
  | .instr i => ToString.toString i
  | .label l => s!"{l}:"
  | .byteArray bs => ".byte "++", ".intercalate (bs.toList.map (fun b => s!"{b}"))
