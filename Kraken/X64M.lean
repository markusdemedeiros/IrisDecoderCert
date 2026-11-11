/-
The monadic instruction semantics and the denotational spec monad.

The first half re-encodes the baseline `Operation.interp` as a straightline
interpreter `Operation.interpM` over `MachineM`, an error-state monad on
`MachineData`: a control transfer throws `X64Exit.jump`, and an effect the
straightline model leaves unresolved (a non-memory access, an architecturally
undefined flag) throws the corresponding exit. Address and constant evaluation
reuse the baseline `AddrExpr.interp`/`ConstExpr.interp` unchanged.

`Operation.interpM` refines the baseline `Operation.interp`: a run's
fall-through or jump outcome is the unique baseline behavior, proved in
`Operation.interpM_All` through `Executable.straightlineM_adequate`
(Kraken/Adequacy.lean). The re-encoding is a determinization: where the
baseline branches on an `undefined` flag or resumes a
`nonmem_load`/`nonmem_store`, `interpM` throws instead of committing, so a
throwing run claims nothing about the baseline. AVX instructions throw
`unimplemented`, joining that under-approximated family.

The second half is the spec monad `X64M D`, parameterized by a device-state
type `D`: `labels` sits in a reader, `rip` in state, over the error-state
machine monad whose state is `Sys D`. Putting `D` in the machine state (rather
than an outer `StateT`) means a `jump` — an `EStateM` throw that carries the
state — preserves the device state, exactly as it preserves `MachineData`.

Instruction primitives mirror the `Operation` constructors and touch only the
`MachineData` component, threading `D` untouched, so their `@[spec]` triples are
polymorphic in `D`. Memory operands are evaluated through the baseline
`AddrExpr.interp`; conditional jumps carry a resolved `Int64` target.
-/
import Kraken.Specs

open Std.WP
open Std.WP.WPMonad
open Lean.Order

/-! ## The monadic instruction semantics -/

/-- Exceptional exits from a monadic run of the instruction semantics.
`jump` carries a control-flow target out of the state monad; the remaining
constructors flag effects the straightline model leaves unresolved. -/
inductive X64Exit
  | jump (pc : Int64)
  | unimplemented (msg : String)
  | nonmemLoad (dmem : DataMem) (addr : BitVec 64) (w : Width)
  | nonmemStore (dmem : DataMem) (addr : BitVec 64) (w : Width)
  | undefinedFlags
  deriving Repr

/-- The instruction-semantics monad: error-state over `MachineData`. -/
abbrev MachineM := EStateM X64Exit MachineData

section InterpM

variable (labels : Labels) (address_size : AddressSize)

-- A load inside the mapped data memory returns the stored value. Outside it,
-- straightline execution throws: MMIO and other nonmemory effects are not modeled.
def MachineData.loadM (addr : BitVec 64) (w : Width) : MachineM w.type := do
  let s ← get
  match Mem.loadInt s.dmem addr w.bytes with
  | .some i => pure (.ofInt _ i)
  | .none => throw (.nonmemLoad s.dmem addr w)

def MachineData.storeM (addr : BitVec 64) {w : Width} (v : w.type) : MachineM Unit := do
  let s ← get
  match Mem.loadInt s.dmem addr w.bytes with
  | .some _ => MonadStateOf.set { s with dmem := Mem.storeInt s.dmem addr w.bytes v.toInt }
  | .none => throw (.nonmemStore s.dmem addr w)

def RegOrMem.interpM {w} (o : RegOrMem w) (p : Std.Rco Int64) : MachineM w.type := do
  match o with
  | .reg r => return (← get).regs.get r
  | .mem a => MachineData.loadM ((@AddrExpr.interp labels address_size a (← get).regs p).zeroExtend _) w

def MachineData.setM {w} (d : Dst w) (v : w.type) (p : Std.Rco Int64) : MachineM Unit := do
  match d with
  | .reg r => modify (·.setReg r v)
  | .mem a => MachineData.storeM ((@AddrExpr.interp labels address_size a (← get).regs p).zeroExtend _) v

def Operand.interpM {w} (o : Operand w) (p : Std.Rco Int64) : MachineM w.type := do
  match o with
  | .regOrMem rm => rm.interpM labels address_size p
  | .imm v => pure ((@ConstExpr.interp labels v p).toBitVec.truncate _)

def RelRegOrMem.interpM (o : RelRegOrMem) (p : Std.Rco Int64) : MachineM (BitVec 64) := do
  match o with
  | .rel c => pure (p.upper + @ConstExpr.interp labels c p).toBitVec
  | .reg r => return (← get).regs.get r
  | .mem a => MachineData.loadM ((@AddrExpr.interp labels address_size a (← get).regs p).zeroExtend _) .W64

set_option maxHeartbeats 1000000 in
def Operation.interpM {w} (i : Operation w) (p : Std.Rco Int64) : MachineM Unit := do
  match i with
  | .mov dst src =>
    let val ← src.interpM labels address_size p
    MachineData.setM labels address_size dst val p
  | .movsx dst src =>
    let val ← src.interpM labels address_size p
    MachineData.setM labels address_size dst (val.signExtend _) p
  | .movzx dst src =>
    let val ← src.interpM labels address_size p
    MachineData.setM labels address_size dst (val.zeroExtend _) p
  | .push src =>
    let v ← src.interpM labels address_size p
    let s ← get
    let rsp := s.regs.get64 .rsp - w.bytesv
    -- The store precedes the rsp commit, so a faulting push leaves rsp at its
    -- original value, as a restartable fault requires.
    MachineData.storeM rsp v
    modify (fun s => { s with regs := s.regs.set64 .rsp rsp })
  | .pop dst =>
    let rsp := (← get).regs.get64 .rsp
    let val ← MachineData.loadM rsp w
    modify (fun s => { s with regs := s.regs.set64 .rsp (rsp + w.bytesv) })
    MachineData.setM labels address_size dst val p
  | .setcc cc dst =>
    MachineData.setM labels address_size dst (cc.interp (← get).status) p
  | .cmovcc cc dst src =>
    let src ← src.interpM labels address_size p
    let s ← get
    let v := if cc.interp s.status then src else s.regs.get dst
    set (s.setReg dst v)
-- Arithmetic
  | .lea dst src =>
    let s ← get
    set (s.setReg dst ((@AddrExpr.interp labels address_size src s.regs p).zeroExtend _))
  | .add dst src =>
    let a ← src.interpM labels address_size p
    let b ← dst.interpM labels address_size p
    let v := a + b
    let status := StatusFlags.from_result v {
      cf := v.unsigned != a.unsigned + b.unsigned
      af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned,
      of := v.signed != a.signed + b.signed }
    modify (fun s => { s with status })
    MachineData.setM labels address_size dst v p
  | .adc dst src =>
    let a ← src.interpM labels address_size p
    let b ← dst.interpM labels address_size p
    let c := (← get).status.cf
    let v := a + b + c
    let status := StatusFlags.from_result v {
      cf := v.unsigned != a.unsigned + b.unsigned + c
      af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned + c,
      of := v.signed != a.signed + b.signed + c }
    modify (fun s => { s with status })
    MachineData.setM labels address_size dst v p
  | .adcx dst src =>
    let a ← src.interpM labels address_size p
    let s ← get
    let b := s.regs.get dst
    let v := a + b + s.status.cf
    let cf := v.unsigned != a.unsigned + b.unsigned + s.status.cf
    set { s with regs := s.regs.set dst v, status := { s.status with cf := cf } }
  | .adox dst src =>
    let a ← src.interpM labels address_size p
    let s ← get
    let b := s.regs.get dst
    let v := a + b + s.status.of
    let of := v.unsigned != a.unsigned + b.unsigned + s.status.of
    set { s with regs := s.regs.set dst v, status := { s.status with of := of } }
  | .inc dst =>
    let a ← dst.interpM labels address_size p
    let cf := (← get).status.cf
    let v := a + 1
    let status := StatusFlags.from_result v {
      cf := cf
      af := (v.take 4).unsigned != (a.take 4).unsigned + 1,
      of := v.signed != a.signed + 1 }
    modify (fun s => { s with status })
    MachineData.setM labels address_size dst v p
  | .dec dst =>
    let a ← dst.interpM labels address_size p
    let cf := (← get).status.cf
    let v := a - 1
    let status := StatusFlags.from_result v {
      cf := cf
      af := (v.take 4).unsigned != (a.take 4).unsigned - 1,
      of := v.signed != a.signed - 1 }
    modify (fun s => { s with status })
    MachineData.setM labels address_size dst v p
  | .neg dst =>
    let b ← dst.interpM labels address_size p
    let v := -b
    let status := StatusFlags.from_result v {
      cf := b != 0
      af := (b.take 4) != 0,
      of := v.signed != - b.signed }
    modify (fun s => { s with status })
    MachineData.setM labels address_size dst v p
  | .sub dst src =>
    let a ← src.interpM labels address_size p
    let b ← dst.interpM labels address_size p
    let v := b - a
    let status := StatusFlags.from_result v {
      cf := v.unsigned != b.unsigned - a.unsigned
      af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned,
      of := v.signed != b.signed - a.signed }
    modify (fun s => { s with status })
    MachineData.setM labels address_size dst v p
  | .sbb dst src =>
    let a ← src.interpM labels address_size p
    let b ← dst.interpM labels address_size p
    let c := (← get).status.cf
    let v := b - a - c
    let status := StatusFlags.from_result v {
      cf := v.unsigned != b.unsigned - a.unsigned - c
      af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned - c,
      of := v.signed != b.signed - a.signed - c }
    modify (fun s => { s with status })
    MachineData.setM labels address_size dst v p
  | .cmp a b =>
    let a ← a.interpM labels address_size p
    let b ← b.interpM labels address_size p
    let v := a - b
    let status := StatusFlags.from_result v {
      cf := v.unsigned != a.unsigned - b.unsigned
      af := (v.take 4).unsigned != (a.take 4).unsigned - (b.take 4).unsigned,
      of := v.signed != a.signed - b.signed }
    modify (fun s => { s with status })
  | .mulx r_hi r_lo src1 =>
    let a ← src1.interpM labels address_size p
    let s ← get
    let b := s.regs.get (.low .rdx w)
    let v := a.unsigned * b.unsigned
    modify (fun s => (s.setReg r_lo (.ofInt _ v)).setReg r_hi (.ofInt _ (v >>> w.bits)))
  | .not dst =>
    let a ← dst.interpM labels address_size p
    MachineData.setM labels address_size dst (~~~a) p
  | .bswap dst =>
    let a := (← get).regs.get dst
    match w with
    | .W32 =>
      let v := a.take 8 ++ a.extractLsb' 8 8 ++ a.extractLsb' 16 8 ++ a.drop 24
      modify (fun s => s.setReg dst (v.setWidth _))
    | .W64 =>
      let v := a.take 8 ++ a.extractLsb' 8 8 ++ a.extractLsb' 16 8 ++ a.extractLsb' 24 8
            ++ a.extractLsb' 32 8 ++ a.extractLsb' 40 8 ++ a.extractLsb' 48 8 ++ a.drop 56
      modify (fun s => s.setReg dst (v.setWidth _))
    | _ => throw .undefinedFlags -- TODO: model undefined flags for bswap on W8/W16
  | .cltq =>
    modify (fun s => s.setReg (.low .rax .W64) ((s.regs.get (.low .rax .W32)).signExtend 64))
  | .cltd =>
    modify (fun s => s.setReg (.low .rdx .W32) ((s.regs.get (.low .rax .W32)).sshiftRight 31))
  -- A trap has no successor state; the straightline model claims nothing.
  | .ud1 _ _ | .ud2 | .int3 => throw (.unimplemented "trap")
  | .jcc cc l =>
    if cc.interp (← get).status
    then throw (.jump (labels.label l))
    else pure ()
  | .jmp tgt =>
    let a ← tgt.interpM labels address_size p
    throw (.jump (.ofBitVec a))
  | .call tgt =>
    let a ← tgt.interpM labels address_size p
    let s ← get
    let rsp := s.regs.get64 .rsp - Width.W64.bytesv
    set { s with regs := s.regs.set64 .rsp rsp }
    MachineData.storeM rsp (w := .W64) p.upper.toBitVec
    throw (.jump (.ofBitVec a))
  | .ret =>
    let rsp := (← get).regs.get64 .rsp
    let ra ← MachineData.loadM rsp .W64
    modify (fun s => { s with regs := s.regs.set64 .rsp (rsp + 8) })
    throw (.jump (.ofBitVec ra))
  | nop _ | nopalign _ _ => pure ()
  -- TODO: the following instructions leave some status flags undefined; the
  -- straightline model throws rather than committing to a nondeterministic value.
  | .mul .. | .imul1 .. | .imul .. | .div .. | .idiv .. | .test .. | .and .. | .or .. | .xor ..
  | .shl .. | .shr .. | .sar .. | .shld .. | .shrd ..
  | .rol .. | .ror .. | .rcl .. | .rcr .. => throw .undefinedFlags

end InterpM

def Instr.interpM (labels : Labels) (i : Instr) (p : Std.Rco Int64) : MachineM Unit :=
  match i with
    | .regular addr_sz op_sz op =>
        Operation.interpM (w := op_sz) labels (.mk addr_sz) op p
    | .avx _ _ _ => throw (.unimplemented "AVX not modeled straightline")

def Directive.interpM (labels : Labels) (d : Directive) (p : Std.Rco Int64) : MachineM Unit :=
  match d with
  | .label _ => pure ()
  | .instr i => i.interpM labels p
  | .byteArray _ => throw (.unimplemented s!"Unimplemented: execution reached data block at {p.1}")

def Directives.interpM (labels : Labels)
  (ds : List (Directive × Nat)) (pc : Int64) : MachineM Int64 := do
  match ds with
  | [] => pure pc
  | (d, sz) :: ds =>
    d.interpM labels (.mk pc (pc+.ofNat sz))
    Directives.interpM labels ds (pc+.ofNat sz)

def Executable.stepM (e : Executable) (pc : Int64) : MachineM Int64 :=
  Directives.interpM e.labels (e.directivesAtAddress pc) pc

def Executable.straightlineM (e : Executable) (pc : Int64) : MachineM Int64 :=
  Directives.interpM e.labels (e.directivesFromAddress pc) pc

/-- Concrete evaluator over the monadic semantics, for expedient testing. -/
partial def Executable.evalM (e : Executable) (s : MachineState) (until_ : MachineState → Bool) : Except String (MachineState) :=
  if until_ s then .ok s else
  match (e.straightlineM s.2).run s.1 with
  | .ok pc s' => evalM e (s', pc) until_
  | .error (.jump pc) s' => evalM e (s', pc) until_
  | .error (.unimplemented msg) _ => .error msg
  | .error (.nonmemLoad _ addr _) _ => .error s!"Load at unmapped address {repr addr}"
  | .error (.nonmemStore _ addr _) _ => .error s!"Store at unmapped address {repr addr}"
  | .error .undefinedFlags _ => .error "undefined flags encountered"

/-- info: Except.ok 42 -/
#guard_msgs in
#eval
  let exe := Program.fakeLayout [
    .label "main",
    .instr (.regular .W64 .W64 (.lea (.low .rax .W64) (.mk .none .none (.int64 41)))),
    .instr (.regular .W64 .W64 (.inc (.reg (.low .rax .W64)))),
    .instr (.regular .W64 .W64 .ret) ]
  let start := exe.labels.label "main"
  let data := { dmem := Mem.storeInt {} 0x100 8 0x1337, regs := {rsp := 0x100} }
  (exe.evalM (data, start) (fun (_, pc) => pc = 0x1337)).bind (fun s => .ok s.1.regs.rax)

/-! ## The spec monad -/

namespace Kraken

/-- Program-constant inputs: the label table, together with the encoded length of
the instruction now executing, from which the position range's upper bound (the
address of the next instruction) is formed. -/
structure Env where
  labels : Labels
  curSize : Nat

/-- Error-state over the system state `Sys D`. A thrown exit (a `jump`)
carries this whole state, so the device component survives control transfer. -/
abbrev SysM (D : Type) := EStateM X64Exit (Sys D)

/-- Reader over the label environment, state over `rip`, over the system monad. -/
abbrev X64M (D : Type) := ReaderT Env (StateT Int64 (SysM D))

/-- Read the `MachineData` component of the system state. -/
def getMachine {D : Type} : X64M D MachineData := do
  let s ← liftM (getThe (Sys D) : SysM D (Sys D))
  pure s.machine

/-- Update the `MachineData` component, leaving the device state untouched. -/
def modifyMachine {D : Type} (f : MachineData → MachineData) : X64M D Unit :=
  liftM (modify (fun s => { s with machine := f s.machine }) : SysM D Unit)

/-- Effective address of a memory operand, via the baseline address semantics.
The position range is `rip` up to the next instruction's address `rip + curSize`,
matching the x86 resolution of a rip-relative reference against the following
instruction. -/
def evalAddr {D : Type} (ae : AddrExpr) : X64M D (BitVec 64) := do
  let e ← read
  let pc ← getThe Int64
  let s ← getMachine
  pure (AddrExpr.interp64 e.labels ae s.regs (.mk pc (pc + Int64.ofNat e.curSize)))

namespace Op
variable {D : Type}

def mov (dst : Dst .W64) (src : Operand .W64) : X64M D Unit := do
  match dst, src with
  | .reg (.low r _), .imm (.int64 i) =>
    modifyMachine (fun s => { s with regs := s.regs.set64 r ((BitVec.setWidth 64 i.toBitVec)) })
  | .reg (.low rd _), .regOrMem (.reg (.low rs _)) =>
    modifyMachine (fun s => { s with regs := s.regs.set64 rd (s.regs.get64 rs) })
  | .reg (.low dst _), .regOrMem (.mem ae) =>
    let addr ← evalAddr ae
    let s ← getMachine
    match Mem.loadInt s.dmem addr 8 with
    | some i => modifyMachine (fun s => { s with regs := s.regs.set64 dst ((BitVec.ofInt 64 i)) })
    | none => liftM (throw (.nonmemLoad s.dmem addr .W64) : SysM D Unit)
  | .mem ae, .imm (.int64 i) =>
    let addr ← evalAddr ae
    let s ← getMachine
    match Mem.loadInt s.dmem addr 8 with
    | some _ =>
      modifyMachine (fun s => { s with dmem := Mem.storeInt s.dmem addr 8 (BitVec.setWidth 64 i.toBitVec).toInt })
    | none => liftM (throw (.nonmemStore s.dmem addr .W64) : SysM D Unit)
  | .mem ae, .regOrMem (.reg (.low src _)) =>
    let addr ← evalAddr ae
    let s ← getMachine
    match Mem.loadInt s.dmem addr 8 with
    | some _ =>
      modifyMachine (fun s => { s with dmem := Mem.storeInt s.dmem addr 8 (s.regs.get64 src).toInt })
    | none => liftM (throw (.nonmemStore s.dmem addr .W64) : SysM D Unit)
  | _, _ => liftM (throw (.unimplemented "mov") : SysM D Unit)

def dec (o : Dst .W64) : X64M D Unit := do
  match o with
  | .reg (.low r _) =>
    modifyMachine (fun s =>
      let a := s.regs.get64 r
      let v := a - 1
      let status := StatusFlags.from_result v
        { cf := s.status.cf,
          af := (v.take 4).unsigned != (a.take 4).unsigned - 1,
          of := v.signed != a.signed - 1 }
      { s with status := status, regs := s.regs.set64 r (v) })
  | _ => liftM (throw (.unimplemented "dec") : SysM D Unit)

/-- Conditional jump to a resolved `Int64` target: jump when the condition holds,
fall through otherwise. -/
def jcc (cc : CondCode) (l : Int64) : X64M D Unit := do
  let s ← getMachine
  if cc.interp s.status then liftM (throw (.jump l) : SysM D Unit) else pure ()

def add (dst : Dst .W64) (src : Operand .W64) : X64M D Unit := do
  match dst, src with
  | .reg (.low r _), .imm (.int64 i) =>
    modifyMachine (fun s =>
      let a := BitVec.setWidth 64 i.toBitVec
      let b := s.regs.get64 r
      let v := a + b
      let status := StatusFlags.from_result v
        { cf := v.unsigned != a.unsigned + b.unsigned,
          af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned,
          of := v.signed != a.signed + b.signed }
      { s with status := status, regs := s.regs.set64 r (v) })
  | .reg (.low dst _), .regOrMem (.mem ae) =>
    let addr ← evalAddr ae
    let s ← getMachine
    match Mem.loadInt s.dmem addr 8 with
    | some x =>
      modifyMachine (fun s =>
        let av := BitVec.ofInt 64 x
        let bv := s.regs.get64 dst
        let v := av + bv
        let status := StatusFlags.from_result v
          { cf := v.unsigned != av.unsigned + bv.unsigned,
            af := (v.take 4).unsigned != (av.take 4).unsigned + (bv.take 4).unsigned,
            of := v.signed != av.signed + bv.signed }
        { s with status := status, regs := s.regs.set64 dst (v) })
    | none => liftM (throw (.nonmemLoad s.dmem addr .W64) : SysM D Unit)
  | _, _ => liftM (throw (.unimplemented "add") : SysM D Unit)

def adc (dst : Dst .W64) (src : Operand .W64) : X64M D Unit := do
  match dst, src with
  | .reg (.low rd _), .regOrMem (.reg (.low rs _)) =>
    modifyMachine (fun s =>
      let a := s.regs.get64 rs
      let b := s.regs.get64 rd
      let c := s.status.cf
      let v := a + b + BitVec.ofNat 64 c.toNat
      let status := StatusFlags.from_result v
        { cf := v.unsigned != a.unsigned + b.unsigned + c.toNat,
          af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned + c.toNat,
          of := v.signed != a.signed + b.signed + c.toNat }
      { s with status := status, regs := s.regs.set64 rd (v) })
  | _, _ => liftM (throw (.unimplemented "adc") : SysM D Unit)

def lea (dst : Reg64) (ae : AddrExpr) : X64M D Unit := do
  let addr ← evalAddr ae
  modifyMachine (fun s => { s with regs := s.regs.set64 dst (addr) })

/-- `xor` leaves `AF` architecturally undefined, so the baseline throws
`undefinedFlags` rather than commit to a value; the encoding matches it. -/
def xor (_dst : Dst .W64) (_src : Operand .W64) : X64M D Unit :=
  liftM (throw .undefinedFlags : SysM D Unit)

def push (o : Operand .W64) : X64M D Unit := do
  match o with
  | .regOrMem (.reg (.low r _)) =>
    let s ← getMachine
    let rsp := s.regs.get64 .rsp - 8#64
    match Mem.loadInt s.dmem rsp 8 with
    | some _ =>
      modifyMachine (fun s => { s with
        regs := s.regs.set64 .rsp (rsp),
        dmem := Mem.storeInt s.dmem rsp 8 (s.regs.get64 r).toInt })
    | none => liftM (throw (.nonmemStore s.dmem rsp .W64) : SysM D Unit)
  | _ => liftM (throw (.unimplemented "push") : SysM D Unit)

def pop (dst : Dst .W64) : X64M D Unit := do
  match dst with
  | .reg (.low d _) =>
    let s ← getMachine
    let rsp := s.regs.get64 .rsp
    match Mem.loadInt s.dmem rsp 8 with
    | some i =>
      modifyMachine (fun s => { s with
        regs := (s.regs.set64 .rsp ((rsp + 8#64))).set64 d ((BitVec.ofInt 64 i)) })
    | none => liftM (throw (.nonmemLoad s.dmem rsp .W64) : SysM D Unit)
  | _ => liftM (throw (.unimplemented "pop") : SysM D Unit)

/-- Dispatch a decoded operation to its encoded primitive, resolving a jump's
label against the environment. An operation or operand shape without an encoding
throws `unimplemented`. -/
def exec (op : Operation .W64) : X64M D Unit :=
  match op with
  | .mov dst src => mov dst src
  | .add dst src => add dst src
  | .adc dst src => adc dst src
  | .dec o => dec o
  | .xor dst src => xor dst src
  | .lea (.low r _) ae => lea r ae
  | .push src => push src
  | .pop dst => pop dst
  | .jcc cc l => do let env ← read; jcc cc (env.labels.label l)
  | _ => liftM (throw (.unimplemented "exec") : SysM D Unit)

end Op

/-! ## Program driver

`execDirs` runs a laid-out directive list the way the baseline `Directives.interpM`
does: each instruction executes at its address, `rip` advancing by the encoded
size, so the position range read for that instruction is `.mk pc (pc+sz)`, the one
the baseline supplies. An instruction dispatches through `Op.exec`; a label is a
no-op; a data block or a non-64-bit instruction throws. -/

def execDir {D : Type} (d : Directive) : X64M D Unit :=
  match d with
  | .label _ => pure ()
  | .instr (.regular .W64 .W64 op) => Op.exec op
  | _ => liftM (throw (.unimplemented "execDir") : SysM D Unit)

/-- Run `x` with the executing instruction's encoded length recorded on the
reader, so the position range it reads spans to the next instruction. -/
def withCurSize {D α : Type} (sz : Nat) (x : X64M D α) : X64M D α :=
  withReader (fun e => { e with curSize := sz }) x

def execDirs {D : Type} (ds : List (Directive × Nat)) : X64M D Unit := do
  match ds with
  | [] => pure ()
  | (d, sz) :: ds =>
    withCurSize sz (execDir d)
    modifyThe Int64 (· + Int64.ofNat sz)
    execDirs ds

/-! ## Control flow

`execStraightlineFrom` runs from the current `rip` to the end of the program, a
taken jump throwing `X64Exit.jump`. `execProgram` catches that throw and resumes
at the target, bounded by `fuel`: unrolling it `fuel` times yields a finite
do-block, so a loop is verified by running the body a fixed number of times. A
`modifyMachine` write lands in the `Sys D` state a `jump` throw carries, so the
machine state at the jump survives into the handler; the handler sets `rip` to the
target, replacing whatever `rip` the interrupted segment reached. -/

def execStraightlineFrom {D : Type} (e : _root_.Executable) : X64M D Unit := do
  let pc ← getThe Int64
  execDirs (e.directivesFromAddress pc)

def execProgram {D : Type} (e : _root_.Executable) : Nat → X64M D Unit
  | 0 => pure ()
  | fuel + 1 =>
    tryCatch (execStraightlineFrom e) fun exc =>
      match exc with
      | .jump pc => do modifyThe Int64 (fun _ => pc); execProgram e fuel
      | exc => throw exc

/-! ## Specs, discriminating on operand shape, polymorphic in `D` -/

section
variable {D : Type} (Q : Unit → Env → Int64 → Sys D → Prop)
    (E : X64Exit → Sys D → Prop)

@[spec] theorem Op.mov_reg_imm_spec (r : Reg64) (i : Int64) :
    ⦃ fun env rip s =>
        Q () env rip { s with machine := { s.machine with regs := s.machine.regs.set64 r ((BitVec.setWidth 64 i.toBitVec)) } } ⦄
      Op.mov (.reg (.low r .W64)) (.imm (.int64 i)) ⦃ Q; E ⦄ := by
  sym =>
    vcgen [Op.mov, modifyMachine]
    all_goals finish

@[spec] theorem Op.mov_reg_reg_spec (rd rs : Reg64) :
    ⦃ fun env rip s => Q () env rip { s with machine := { s.machine with regs := s.machine.regs.set64 rd (s.machine.regs.get64 rs) } } ⦄
      Op.mov (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))) ⦃ Q; E ⦄ := by
  sym =>
    vcgen [Op.mov, modifyMachine]
    all_goals finish

@[spec] theorem Op.mov_reg_mem_spec (dst : Reg64) (ae : AddrExpr) (v : Int) :
    ⦃ fun env rip s =>
        (Mem.loadInt s.machine.dmem (AddrExpr.interp64 env.labels ae s.machine.regs (.mk rip (rip + Int64.ofNat env.curSize))) 8 = some v) ⊓
        Q () env rip { s with machine := { s.machine with regs := s.machine.regs.set64 dst ((BitVec.ofInt 64 v)) } } ⦄
      Op.mov (.reg (.low dst .W64)) (.regOrMem (.mem ae)) ⦃ Q; E ⦄ := by
  sym =>
    vcgen [Op.mov, evalAddr, getMachine, modifyMachine]
    all_goals finish

@[spec] theorem Op.mov_mem_imm_spec (ae : AddrExpr) (i : Int64) (v : Int) :
    ⦃ fun env rip s =>
        (Mem.loadInt s.machine.dmem (AddrExpr.interp64 env.labels ae s.machine.regs (.mk rip (rip + Int64.ofNat env.curSize))) 8 = some v) ⊓
        Q () env rip { s with machine := { s.machine with
          dmem := Mem.storeInt s.machine.dmem (AddrExpr.interp64 env.labels ae s.machine.regs (.mk rip (rip + Int64.ofNat env.curSize))) 8
            (BitVec.setWidth 64 i.toBitVec).toInt } } ⦄
      Op.mov (.mem ae) (.imm (.int64 i)) ⦃ Q; E ⦄ := by
  sym =>
    vcgen [Op.mov, evalAddr, getMachine, modifyMachine]
    all_goals finish

@[spec] theorem Op.mov_mem_reg_spec (ae : AddrExpr) (src : Reg64) (v : Int) :
    ⦃ fun env rip s =>
        (Mem.loadInt s.machine.dmem (AddrExpr.interp64 env.labels ae s.machine.regs (.mk rip (rip + Int64.ofNat env.curSize))) 8 = some v) ⊓
        Q () env rip { s with machine := { s.machine with
          dmem := Mem.storeInt s.machine.dmem (AddrExpr.interp64 env.labels ae s.machine.regs (.mk rip (rip + Int64.ofNat env.curSize))) 8
            (s.machine.regs.get64 src).toInt } } ⦄
      Op.mov (.mem ae) (.regOrMem (.reg (.low src .W64))) ⦃ Q; E ⦄ := by
  sym =>
    vcgen [Op.mov, evalAddr, getMachine, modifyMachine]
    all_goals finish

@[spec] theorem Op.dec_reg_spec (r : Reg64) :
    ⦃ fun env rip s =>
        Q () env rip { s with machine := { s.machine with
            regs := s.machine.regs.set64 r (((s.machine.regs.get64 r) - 1))
            status := StatusFlags.from_result ((s.machine.regs.get64 r) - 1)
              { cf := s.machine.status.cf,
                af := (((s.machine.regs.get64 r) - 1).take 4).unsigned
                  != ((s.machine.regs.get64 r).take 4).unsigned - 1,
                of := ((s.machine.regs.get64 r) - 1).signed
                  != (s.machine.regs.get64 r).signed - 1 } } } ⦄
      Op.dec (.reg (.low r .W64)) ⦃ Q; E ⦄ := by
  sym =>
    vcgen [Op.dec, modifyMachine]
    all_goals finish

/-- A conditional jump: the jump post under the taken condition, the fall-through
post otherwise. On a jump the exception post receives the whole state `s`, so the
device component survives. -/
@[spec] theorem Op.jcc_spec (cc : CondCode) (l : Int64) :
    ⦃ fun env rip s =>
        (cc.interp s.machine.status = true → E (X64Exit.jump l) s)
          ⊓ (cc.interp s.machine.status = false → Q () env rip s) ⦄
      Op.jcc cc l ⦃ Q; E ⦄ := by
  sym =>
    vcgen [Op.jcc, getMachine]
    all_goals finish

@[spec] theorem Op.add_reg_imm_spec (r : Reg64) (i : Int64) :
    ⦃ fun env rip s =>
        Q () env rip { s with machine := { s.machine with
            regs := s.machine.regs.set64 r
              ((BitVec.setWidth 64 i.toBitVec + (s.machine.regs.get64 r)))
            status := StatusFlags.from_result
              (BitVec.setWidth 64 i.toBitVec + (s.machine.regs.get64 r))
              { cf := (BitVec.setWidth 64 i.toBitVec + (s.machine.regs.get64 r)).unsigned
                  != (BitVec.setWidth 64 i.toBitVec).unsigned + (s.machine.regs.get64 r).unsigned,
                af := ((BitVec.setWidth 64 i.toBitVec + (s.machine.regs.get64 r)).take 4).unsigned
                  != ((BitVec.setWidth 64 i.toBitVec).take 4).unsigned
                    + ((s.machine.regs.get64 r).take 4).unsigned,
                of := (BitVec.setWidth 64 i.toBitVec + (s.machine.regs.get64 r)).signed
                  != (BitVec.setWidth 64 i.toBitVec).signed + (s.machine.regs.get64 r).signed } } } ⦄
      Op.add (.reg (.low r .W64)) (.imm (.int64 i)) ⦃ Q; E ⦄ := by
  sym =>
    vcgen [Op.add, modifyMachine]
    all_goals finish

@[spec] theorem Op.add_reg_mem_spec (dst : Reg64) (ae : AddrExpr) (v : Int) :
    ⦃ fun env rip s =>
        (Mem.loadInt s.machine.dmem (AddrExpr.interp64 env.labels ae s.machine.regs (.mk rip (rip + Int64.ofNat env.curSize))) 8 = some v) ⊓
        Q () env rip { s with machine := { s.machine with
            regs := s.machine.regs.set64 dst ((BitVec.ofInt 64 v + (s.machine.regs.get64 dst)))
            status := StatusFlags.from_result (BitVec.ofInt 64 v + (s.machine.regs.get64 dst))
              { cf := (BitVec.ofInt 64 v + (s.machine.regs.get64 dst)).unsigned
                  != (BitVec.ofInt 64 v).unsigned + (s.machine.regs.get64 dst).unsigned,
                af := ((BitVec.ofInt 64 v + (s.machine.regs.get64 dst)).take 4).unsigned
                  != ((BitVec.ofInt 64 v).take 4).unsigned + ((s.machine.regs.get64 dst).take 4).unsigned,
                of := (BitVec.ofInt 64 v + (s.machine.regs.get64 dst)).signed
                  != (BitVec.ofInt 64 v).signed + (s.machine.regs.get64 dst).signed } } } ⦄
      Op.add (.reg (.low dst .W64)) (.regOrMem (.mem ae)) ⦃ Q; E ⦄ := by
  sym =>
    vcgen [Op.add, evalAddr, getMachine, modifyMachine]
    all_goals finish

@[spec] theorem Op.adc_reg_reg_spec (rd rs : Reg64) :
    ⦃ fun env rip s =>
        Q () env rip { s with machine := { s.machine with
            regs := s.machine.regs.set64 rd (((s.machine.regs.get64 rs)
              + (s.machine.regs.get64 rd) + BitVec.ofNat 64 s.machine.status.cf.toNat))
            status := StatusFlags.from_result ((s.machine.regs.get64 rs)
                + (s.machine.regs.get64 rd) + BitVec.ofNat 64 s.machine.status.cf.toNat)
              { cf := ((s.machine.regs.get64 rs) + (s.machine.regs.get64 rd)
                    + BitVec.ofNat 64 s.machine.status.cf.toNat).unsigned
                  != (s.machine.regs.get64 rs).unsigned + (s.machine.regs.get64 rd).unsigned
                    + s.machine.status.cf.toNat,
                af := (((s.machine.regs.get64 rs) + (s.machine.regs.get64 rd)
                    + BitVec.ofNat 64 s.machine.status.cf.toNat).take 4).unsigned
                  != ((s.machine.regs.get64 rs).take 4).unsigned
                    + ((s.machine.regs.get64 rd).take 4).unsigned + s.machine.status.cf.toNat,
                of := ((s.machine.regs.get64 rs) + (s.machine.regs.get64 rd)
                    + BitVec.ofNat 64 s.machine.status.cf.toNat).signed
                  != (s.machine.regs.get64 rs).signed + (s.machine.regs.get64 rd).signed
                    + s.machine.status.cf.toNat } } } ⦄
      Op.adc (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))) ⦃ Q; E ⦄ := by
  sym =>
    vcgen [Op.adc, modifyMachine]
    all_goals finish

@[spec] theorem Op.lea_spec (dst : Reg64) (ae : AddrExpr) :
    ⦃ fun env rip s =>
        Q () env rip { s with machine := { s.machine with
          regs := s.machine.regs.set64 dst ((AddrExpr.interp64 env.labels ae s.machine.regs (.mk rip (rip + Int64.ofNat env.curSize)))) } } ⦄
      Op.lea dst ae ⦃ Q; E ⦄ := by
  sym =>
    vcgen [Op.lea, evalAddr, getMachine, modifyMachine]
    all_goals finish

@[spec] theorem Op.xor_spec (dst : Dst .W64) (src : Operand .W64) :
    ⦃ fun _ _ s => E .undefinedFlags s ⦄ Op.xor dst src ⦃ Q; E ⦄ := by
  sym =>
    vcgen [Op.xor]
    all_goals finish

@[spec] theorem Op.push_reg_spec (r : Reg64) (v : Int) :
    ⦃ fun env rip s =>
        (Mem.loadInt s.machine.dmem ((s.machine.regs.get64 .rsp) - 8#64) 8 = some v) ⊓
        Q () env rip { s with machine := { s.machine with
          regs := s.machine.regs.set64 .rsp (((s.machine.regs.get64 .rsp) - 8#64))
          dmem := Mem.storeInt s.machine.dmem ((s.machine.regs.get64 .rsp) - 8#64) 8
            (s.machine.regs.get64 r).toInt } } ⦄
      Op.push (.regOrMem (.reg (.low r .W64))) ⦃ Q; E ⦄ := by
  sym =>
    vcgen [Op.push, getMachine, modifyMachine]
    all_goals finish

@[spec] theorem Op.pop_reg_spec (dst : Reg64) (v : Int) :
    ⦃ fun env rip s =>
        (Mem.loadInt s.machine.dmem (s.machine.regs.get64 .rsp) 8 = some v) ⊓
        Q () env rip { s with machine := { s.machine with
          regs := (s.machine.regs.set64 .rsp (((s.machine.regs.get64 .rsp) + 8#64))).set64 dst
            ((BitVec.ofInt 64 v)) } } ⦄
      Op.pop (.reg (.low dst .W64)) ⦃ Q; E ⦄ := by
  sym =>
    vcgen [Op.pop, getMachine, modifyMachine]
    all_goals finish

end

end Kraken
