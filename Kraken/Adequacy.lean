/-
Adequacy of the `Op.*` encoding against the baseline omni-semantics, in two
halves through the waypoint `Operation.interpM`, the straightline interpreter
over `MachineM`.

First half: a device-parameterized action `Op.foo` runs over `Sys D`, touching
only the `machine` component; `liftMachine` embeds a `MachineM` computation
into that component, and `liftBaseline` reads the label environment and `rip`.
Each deterministic `Op.foo` equals `liftBaseline` of the matching
`Operation.interpM` case at 64-bit operand and address size.

Second half: an `interpM` run's outcome transports into the baseline's
`Effects.All`, culminating in `Executable.straightlineM_adequate`: the monadic
straightline run's outcome is the strongest postcondition of the baseline's
`straightlineStep` judgment.

The proofs run against a characterizing API rather than by unfolding at the use
site: a `liftMachine` monad-morphism dictionary (`lm_*`) pushes the lift to the
X64M primitives, the memory bridges (`lm_load_bind`/`lm_store`) turn a lifted
access into the `match` shape the encoding uses, and the state-operation fusion
and discard laws (`gm_*`, `read_bind_const`, …) normalize both sides to one form.
The residual is closed by applying a state and reducing each primitive in one
step (`gm_apply`/`mm_apply`/…), so no whnf of the transformer stack ever runs.

The flag-nondeterministic family (`xor`, and the shifts and rotates once encoded)
throws `undefinedFlags` in both `Operation.interpM` and the encoding, since x86
leaves a flag such as `AF` undefined; adequacy is faithfulness to the reference,
so the encoding declines to commit a value there too.
-/
import Kraken.X64M

open Std.WP

set_option linter.unusedSimpArgs false

namespace Kraken

/-- Run a baseline `MachineM` computation on the `machine` component of a `Sys D`
state, threading the device state. -/
def liftMachine {D : Type} {α : Type} (c : MachineM α) : X64M D α :=
  liftM (m := SysM D) (fun s =>
    match c s.machine with
    | .ok a m => .ok a { s with machine := m }
    | .error e m => .error e { s with machine := m })

/-- Read the label environment and `rip`, then run the baseline `Operation.interpM`
of `op` at 64-bit address size over the position range `.mk rip (rip + curSize)`. -/
def liftBaseline {D : Type} (op : Operation .W64) : X64M D Unit := do
  let env ← read
  let rip ← getThe Int64
  liftMachine (Operation.interpM env.labels (.mk .W64) op (.mk rip (rip + Int64.ofNat env.curSize)))

/-! ## `liftMachine` monad-morphism dictionary -/

@[simp] theorem lm_pure {D α} (a : α) : (liftMachine (pure a) : X64M D α) = pure a := by
  funext env rip s; rfl
@[simp] theorem lm_bind {D α β} (x : MachineM α) (f : α → MachineM β) :
    (liftMachine (x >>= f) : X64M D β) = liftMachine x >>= fun a => liftMachine (f a) := by
  funext env rip s
  simp only [liftMachine, bind, liftM, monadLift, MonadLift.monadLift, ReaderT.bind, StateT.bind,
    StateT.lift, EStateM.bind, ReaderT.pure, StateT.pure, EStateM.pure]
  cases x s.machine <;> rfl
@[simp] theorem lm_ebind {D α β} (x : MachineM α) (f : α → MachineM β) :
    (liftMachine (EStateM.bind x f) : X64M D β) = liftMachine x >>= fun a => liftMachine (f a) :=
  lm_bind x f
@[simp] theorem lm_get {D} : (liftMachine (get : MachineM MachineData) : X64M D MachineData) = getMachine := by
  funext env rip s; rfl
@[simp] theorem lm_eget {D} : (liftMachine EStateM.get : X64M D MachineData) = getMachine := by
  funext env rip s; rfl
@[simp] theorem lm_modify {D} (f : MachineData → MachineData) :
    (liftMachine (modify f) : X64M D Unit) = modifyMachine f := by
  funext env rip s; rfl
@[simp] theorem lm_set {D} (m : MachineData) :
    (liftMachine (set m : MachineM Unit) : X64M D Unit) = modifyMachine (fun _ => m) := by
  funext env rip s; rfl
@[simp] theorem lm_throw {D α} (e : X64Exit) :
    (liftMachine (throw e) : X64M D α) = liftM (throw e : SysM D α) := by
  funext env rip s; rfl
@[simp] theorem lm_throw_bind {D α β} (e : X64Exit) (f : α → X64M D β) :
    ((liftM (throw e : SysM D α) : X64M D α) >>= f) = liftM (throw e : SysM D β) := by
  funext env rip s; rfl

/-- A lifted 8-byte load fused with its continuation: the mapped value feeds `k`,
an unmapped address faults, matching the encoding's inlined access. -/
@[simp] theorem lm_load_bind {D α} (addr : BitVec 64) (k : BitVec 64 → X64M D α) :
    ((liftMachine (MachineData.loadM addr .W64) : X64M D (BitVec 64)) >>= k)
      = getMachine >>= fun s => (match Mem.loadInt s.dmem addr 8 with
          | some i => k (BitVec.ofInt 64 i)
          | none => liftM (throw (.nonmemLoad s.dmem addr .W64) : SysM D α)) := by
  funext env rip s
  simp only [MachineData.loadM, liftMachine, getMachine, bind, pure, get, getThe, liftM, monadLift,
    MonadLift.monadLift, ReaderT.bind, ReaderT.pure, StateT.bind, StateT.pure, StateT.get,
    StateT.lift, MonadStateOf.get, EStateM.get, EStateM.bind, EStateM.pure, EStateM.throw, throw,
    throwThe, MonadExceptOf.throw, Width.bytes]
  cases Mem.loadInt s.machine.dmem addr 8 <;> rfl

/-- A lifted 8-byte store: a mapped address commits the write, an unmapped
address faults. The store is the last action of a memory-write instruction, so no
fused continuation is needed. -/
@[simp] theorem lm_store {D} (addr : BitVec 64) (v : BitVec 64) :
    (liftMachine (MachineData.storeM addr (w := .W64) v) : X64M D Unit)
      = getMachine >>= fun s => (match Mem.loadInt s.dmem addr 8 with
          | some _ => modifyMachine (fun m => { m with dmem := Mem.storeInt m.dmem addr 8 v.toInt })
          | none => liftM (throw (.nonmemStore s.dmem addr .W64) : SysM D Unit)) := by
  funext env rip s
  simp only [MachineData.storeM, liftMachine, getMachine, modifyMachine, bind, pure, get, set, getThe,
    liftM, monadLift, MonadLift.monadLift, ReaderT.bind, ReaderT.pure, StateT.bind, StateT.pure,
    StateT.get, StateT.lift, MonadStateOf.get, EStateM.get, MonadStateOf.set, EStateM.set,
    EStateM.bind, EStateM.pure, EStateM.throw, throw, throwThe, MonadExceptOf.throw, Width.bytes]
  cases Mem.loadInt s.machine.dmem addr 8 <;> rfl

/-! ## State-operation fusion and discard laws -/

@[simp] theorem gm_gm {D α} (f : MachineData → MachineData → X64M D α) :
    (getMachine >>= fun s => getMachine >>= fun s' => f s s' : X64M D α)
      = getMachine >>= fun s => f s s := by funext env rip s; rfl
@[simp] theorem gm_mm {D} (g : MachineData → MachineData → MachineData) :
    (getMachine >>= fun s => modifyMachine (g s) : X64M D Unit) = modifyMachine (fun m => g m m) := by
  funext env rip s; rfl
@[simp] theorem gm_mset {D} (g : MachineData → MachineData) :
    (getMachine >>= fun s => modifyMachine (fun _ => g s) : X64M D Unit) = modifyMachine g := by
  funext env rip s; rfl
@[simp] theorem mm_mm {D} (g h : MachineData → MachineData) :
    (modifyMachine g >>= fun _ => modifyMachine h : X64M D Unit) = modifyMachine (fun m => h (g m)) := by
  funext env rip s; rfl
@[simp] theorem gm_gt {D α} (k : MachineData → Int64 → X64M D α) :
    (getMachine >>= fun s => getThe Int64 >>= fun p => k s p : X64M D α)
      = getThe Int64 >>= fun p => getMachine >>= fun s => k s p := by funext env rip s; rfl
@[simp] theorem read_bind_const {D α} (k : X64M D α) :
    ((read : X64M D Env) >>= fun _ => k) = k := by funext env rip s; rfl
@[simp] theorem getThe_bind_const {D α} (k : X64M D α) :
    ((getThe Int64 : X64M D Int64) >>= fun _ => k) = k := by funext env rip s; rfl
@[simp] theorem read_read {D α} (k : Env → Env → X64M D α) :
    ((read : X64M D Env) >>= fun e => read >>= fun e' => k e e') = read >>= fun e => k e e := by
  funext env rip s; rfl
@[simp] theorem gt_gt {D α} (k : Int64 → Int64 → X64M D α) :
    ((getThe Int64 : X64M D Int64) >>= fun p => getThe Int64 >>= fun p' => k p p')
      = getThe Int64 >>= fun p => k p p := by funext env rip s; rfl
@[simp] theorem ze64 (x : BitVec 64) : BitVec.zeroExtend 64 x = x := BitVec.setWidth_64_64 x

/-! Single-step reductions of a primitive applied to a state. Each is a one-step
`rfl`, so using them keeps a goal that reaches an applied form propositional
instead of forcing a full whnf of the transformer stack. -/
theorem read_apply {D α} (k : Env → X64M D α) (env : Env) (rip : Int64) (s : Sys D) :
    ((read : X64M D Env) >>= k) env rip s = k env env rip s := rfl
theorem getThe_apply {D α} (k : Int64 → X64M D α) (env : Env) (rip : Int64) (s : Sys D) :
    ((getThe Int64 : X64M D Int64) >>= k) env rip s = k rip env rip s := rfl
theorem gm_apply {D α} (k : MachineData → X64M D α) (env : Env) (rip : Int64) (s : Sys D) :
    (getMachine >>= k) env rip s = k s.machine env rip s := rfl
theorem mm_apply {D} (f : MachineData → MachineData) (env : Env) (rip : Int64) (s : Sys D) :
    modifyMachine f env rip s = .ok ((), rip) { s with machine := f s.machine } := rfl
theorem throw_apply {D α} (e : X64Exit) (env : Env) (rip : Int64) (s : Sys D) :
    (liftM (throw e : SysM D α) : X64M D α) env rip s = .error e s := rfl
theorem pure_apply {D α} (a : α) (env : Env) (rip : Int64) (s : Sys D) :
    (pure a : X64M D α) env rip s = .ok (a, rip) s := rfl
theorem withReader_apply {D α} (f : Env → Env) (x : X64M D α) (env : Env) (rip : Int64) (s : Sys D) :
    (withReader f x : X64M D α) env rip s = x (f env) rip s := rfl

/-- The value a store commits is read at store time; reading it from the earlier
`getMachine` is the same, since nothing between modifies the state. This fuses the
baseline's early operand read into the encoding's store. -/
@[simp] theorem gm_store_fuse {D} (addr : BitVec 64) (val : MachineData → Int) :
    (getMachine >>= fun s => (match Mem.loadInt s.dmem addr 8 with
       | some _ => modifyMachine (fun m => { m with dmem := Mem.storeInt m.dmem addr 8 (val s) })
       | none => liftM (throw (.nonmemStore s.dmem addr .W64) : SysM D Unit)) : X64M D Unit)
      = getMachine >>= fun s => (match Mem.loadInt s.dmem addr 8 with
       | some _ => modifyMachine (fun m => { m with dmem := Mem.storeInt m.dmem addr 8 (val m) })
       | none => liftM (throw (.nonmemStore s.dmem addr .W64) : SysM D Unit)) := by
  funext env rip s
  simp only [gm_apply]
  cases Mem.loadInt s.machine.dmem addr 8 <;> simp only [mm_apply, throw_apply]

/-- Bind distributes over a `Mem.loadInt` dispatch: the continuation moves into
each branch, and the fault branch absorbs it. -/
@[simp] theorem match_bind {D γ α β} (o : Option γ) (some_br : γ → X64M D α)
    (e : X64Exit) (k : α → X64M D β) :
    ((match o with | some i => some_br i | none => liftM (throw e : SysM D α)) >>= k)
      = (match o with | some i => some_br i >>= k | none => liftM (throw e : SysM D β)) := by
  cases o <;> simp [lm_throw_bind]

/-- Unfold the encoding and the baseline and normalize both to one monadic form:
the dictionary pushes the lift to the leaves, `match_bind` and the store fuse the
memory access into the `match` shape the encoding uses, and the state-operation
fusion and discard laws align the reads and writes. -/
local macro "fw_simp" : tactic =>
  `(tactic| simp only [Op.exec, Op.mov, Op.dec, Op.add, Op.adc, Op.lea, Op.xor, Op.push, Op.pop, liftBaseline, Operation.interpM, Operand.interpM, RegOrMem.interpM, ConstExpr.interp, MachineData.setM, evalAddr, AddrExpr.interp64, lm_pure, lm_bind, lm_ebind, lm_get, lm_eget, lm_modify, lm_set, lm_throw, lm_throw_bind, lm_load_bind, lm_store, gm_gm, gm_mm, gm_mset, mm_mm, gm_gt, read_bind_const, getThe_bind_const, read_read, gt_gt, bind_assoc, pure_bind, bind_pure, match_bind, MachineData.setReg, Reg64s.get_low64, Reg64s.set_low64, Width.bytes, Width.bytesv, BitVec.ofInt_toInt, ze64, gm_store_fuse, BitVec.setWidth_64_64])

/-- For the register and load cases: normalize, then apply to a state and reduce
each primitive in one step, so the two matchers settle by a `rfl` over the small
residual rather than a whnf of the transformer stack. -/
local macro "adeq" : tactic =>
  `(tactic| (fw_simp; all_goals (funext env rip s; simp only [read_apply, getThe_apply, gm_apply, mm_apply, throw_apply, pure_apply]; try rfl)))

/-! ## Front-end dispatch adequacy

Each equation encodes one instruction shape against the baseline. `Op.exec` in
the `fw_simp` set reduces the dispatch to its primitive first, so `adeq` closes
the register and load cases; the memory-write, stack, and jump cases split the
mapped-ness or the branch by hand. -/

/-! ### Register moves -/

theorem Op.exec_mov_reg_imm_adequate {D} (r : Reg64) (i : Int64) :
    (Op.exec (.mov (.reg (.low r .W64)) (.imm (.int64 i))) : X64M D Unit)
      = liftBaseline (.mov (.reg (.low r .W64)) (.imm (.int64 i))) := by adeq

theorem Op.exec_mov_reg_reg_adequate {D} (rd rs : Reg64) :
    (Op.exec (.mov (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64)))) : X64M D Unit)
      = liftBaseline (.mov (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64)))) := by adeq

theorem Op.exec_mov_reg_mem_adequate {D} (rd : Reg64) (ae : AddrExpr) :
    (Op.exec (.mov (.reg (.low rd .W64)) (.regOrMem (.mem ae))) : X64M D Unit)
      = liftBaseline (.mov (.reg (.low rd .W64)) (.regOrMem (.mem ae))) := by adeq

/-- The memory-write cases commit a `Mem.storeInt`; a `rfl` over that record is
slow, so reduce the reads, split the mapped-ness, and reduce each branch. -/
theorem Op.exec_mov_mem_imm_adequate {D} (ae : AddrExpr) (i : Int64) :
    (Op.exec (.mov (.mem ae) (.imm (.int64 i))) : X64M D Unit)
      = liftBaseline (.mov (.mem ae) (.imm (.int64 i))) := by
  fw_simp
  funext env rip s
  simp only [read_apply, getThe_apply, gm_apply]
  cases Mem.loadInt s.machine.dmem (@AddrExpr.interp env.labels (.mk .W64) ae s.machine.regs (.mk rip (rip + Int64.ofNat env.curSize))) 8 <;>
    simp only [mm_apply, throw_apply]

theorem Op.exec_mov_mem_reg_adequate {D} (ae : AddrExpr) (rs : Reg64) :
    (Op.exec (.mov (.mem ae) (.regOrMem (.reg (.low rs .W64)))) : X64M D Unit)
      = liftBaseline (.mov (.mem ae) (.regOrMem (.reg (.low rs .W64)))) := by
  fw_simp
  funext env rip s
  simp only [read_apply, getThe_apply, gm_apply]
  cases Mem.loadInt s.machine.dmem (@AddrExpr.interp env.labels (.mk .W64) ae s.machine.regs (.mk rip (rip + Int64.ofNat env.curSize))) 8 <;>
    simp only [mm_apply, throw_apply]

/-! ### Arithmetic -/

theorem Op.exec_dec_reg_adequate {D} (r : Reg64) :
    (Op.exec (.dec (.reg (.low r .W64))) : X64M D Unit)
      = liftBaseline (.dec (.reg (.low r .W64))) := by adeq

theorem Op.exec_add_reg_imm_adequate {D} (r : Reg64) (i : Int64) :
    (Op.exec (.add (.reg (.low r .W64)) (.imm (.int64 i))) : X64M D Unit)
      = liftBaseline (.add (.reg (.low r .W64)) (.imm (.int64 i))) := by adeq

theorem Op.exec_add_reg_mem_adequate {D} (rd : Reg64) (ae : AddrExpr) :
    (Op.exec (.add (.reg (.low rd .W64)) (.regOrMem (.mem ae))) : X64M D Unit)
      = liftBaseline (.add (.reg (.low rd .W64)) (.regOrMem (.mem ae))) := by adeq

theorem Op.exec_adc_reg_reg_adequate {D} (rd rs : Reg64) :
    (Op.exec (.adc (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64)))) : X64M D Unit)
      = liftBaseline (.adc (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64)))) := by adeq

theorem Op.exec_lea_adequate {D} (rd : Reg64) (ae : AddrExpr) :
    (Op.exec (.lea (.low rd .W64) ae) : X64M D Unit)
      = liftBaseline (.lea (.low rd .W64) ae) := by adeq

/-! ### Flag-undefined family

`xor` (like the shifts and rotates) leaves a flag undefined, so both sides throw
`undefinedFlags` regardless of the operands. -/

theorem Op.exec_xor_adequate {D} (dst : Dst .W64) (src : Operand .W64) :
    (Op.exec (.xor dst src) : X64M D Unit) = liftBaseline (.xor dst src) := by fw_simp

/-! ### Stack -/

theorem Op.exec_push_reg_adequate {D} (r : Reg64) :
    (Op.exec (.push (.regOrMem (.reg (.low r .W64)))) : X64M D Unit)
      = liftBaseline (.push (.regOrMem (.reg (.low r .W64)))) := by
  fw_simp
  funext env rip s
  simp only [read_apply, getThe_apply, gm_apply]
  cases Mem.loadInt s.machine.dmem ((s.machine.regs.get64 .rsp) - 8#64) 8 <;>
    simp only [lm_throw_bind, mm_mm, mm_apply, throw_apply]

theorem Op.exec_pop_reg_adequate {D} (d : Reg64) :
    (Op.exec (.pop (.reg (.low d .W64))) : X64M D Unit)
      = liftBaseline (.pop (.reg (.low d .W64))) := by
  fw_simp
  funext env rip s
  simp only [read_apply, getThe_apply, gm_apply]
  cases Mem.loadInt s.machine.dmem (s.machine.regs.get64 .rsp) 8 <;>
    simp only [mm_apply, throw_apply]

/-! ### Conditional jump

`Op.exec` resolves the jump's `Label` against `env.labels`; the baseline resolves
it inside `Operation.interpM`. The two agree, so the equation holds unapplied. -/

theorem Op.exec_jcc_adequate {D} (cc : CondCode) (l : Label) :
    (Op.exec (.jcc cc l) : X64M D Unit) = liftBaseline (.jcc cc l) := by
  funext env rip s
  simp only [Op.exec, Op.jcc, liftBaseline, Operation.interpM, read_apply, getThe_apply,
    gm_apply, lm_bind, lm_ebind, lm_get, lm_eget, apply_ite, lm_throw, lm_pure, bind_assoc,
    pure_bind, throw_apply, pure_apply]

/-! ## Adequacy against the baseline omni-semantics

The half above ends at `Operation.interpM`, a reference we wrote; this half ties
that reference to the baseline. `MachineM.Outcomes` transports a run's outcome
onto the continuations of the CPS interpreter: a fall-through obligates `next`,
a jump obligates `jmp`, and any other exit obligates nothing (`False`), so a
lemma consumer closes impossible branches by the hypothesis itself. The
dictionary transports each memory and operand primitive, `Operation.interpM_All`
covers every instruction, and `Executable.straightlineM_adequate` concludes in
`Effects.All`, the body of the baseline's `straightlineStep` judgment: the
monadic run's outcome is the strongest postcondition of master's straightline
judgment. -/

section OmniAdequacy

variable {post : MachineState → Prop}

/-- Obligations a CPS interpreter's continuations inherit from a `MachineM`
run: the fall-through state obligates `next`, a jump target obligates `jmp`,
and every other exit is unreachable, so it obligates `False`. -/
def MachineM.Outcomes {α} (post : MachineState → Prop) (next : α → MachineData → Effects)
    (jmp : Int64 → MachineData → Effects) : EStateM.Result X64Exit MachineData α → Prop
  | .ok a s' => (next a s').All post
  | .error (.jump pc) s' => (jmp pc s').All post
  | .error _ _ => False

/-- Reduce a `MachineM` run in the hypothesis to a `match` over its primitive
sub-runs. -/
local macro "mrun" h:ident : tactic =>
  `(tactic| simp only [MachineM.Outcomes, bind, EStateM.bind, pure, EStateM.pure, get, getThe,
      MonadStateOf.get, EStateM.get, set, MonadStateOf.set, EStateM.set, modify, modifyGet,
      MonadStateOf.modifyGet, EStateM.modifyGet, throw, throwThe, MonadExceptOf.throw,
      EStateM.throw] at $h:ident)

/-! ### Primitive dictionary

Each lemma transports `Effects.All` from a run's outcome to the corresponding
CPS access. The proofs case on the actual behaviors (`Mem.loadInt`), so the
hypothesis arms for outcomes the primitive cannot produce are never consumed. -/

theorem MachineData.loadM_All {w : Width} {addr : BitVec 64} {s : MachineData}
    {ret : w.type → MachineData → Effects} {jmp}
    (h : MachineM.Outcomes post ret jmp (MachineData.loadM addr w s)) :
    (MachineData.load s addr w ret).All post := by
  unfold MachineData.loadM at h
  mrun h
  unfold MachineData.load
  simp only [Effects.All]
  cases hm : Mem.loadInt s.dmem addr w.bytes <;> simp only [hm] at h ⊢ <;> mrun h <;>
    first
      | exact h
      | exact h.elim

theorem MachineData.storeM_All {w : Width} {addr : BitVec 64} {v : w.type} {s : MachineData}
    {ret : MachineData → Effects} {jmp}
    (h : MachineM.Outcomes post (fun _ => ret) jmp (MachineData.storeM addr v s)) :
    (MachineData.store s addr v ret).All post := by
  unfold MachineData.storeM at h
  mrun h
  unfold MachineData.store
  simp only [Effects.All]
  cases hm : Mem.loadInt s.dmem addr w.bytes <;> simp only [hm] at h ⊢ <;> mrun h <;>
    first
      | exact h
      | exact h.elim

theorem RegOrMem.interpM_All {w} (labels : Labels) (address_size : AddressSize)
    {o : RegOrMem w} {s : MachineData} {p : Std.Rco Int64}
    {ret : w.type → MachineData → Effects} {jmp}
    (h : MachineM.Outcomes post ret jmp (RegOrMem.interpM labels address_size o p s)) :
    (@RegOrMem.interp w labels address_size o s p ret).All post := by
  cases o with
  | reg r =>
      simp only [RegOrMem.interpM] at h; mrun h
      simpa only [RegOrMem.interp] using h
  | mem a =>
      simp only [RegOrMem.interpM] at h; mrun h
      simp only [RegOrMem.interp]
      exact MachineData.loadM_All h

theorem Operand.interpM_All {w} (labels : Labels) (address_size : AddressSize)
    {o : Operand w} {s : MachineData} {p : Std.Rco Int64}
    {ret : w.type → MachineData → Effects} {jmp}
    (h : MachineM.Outcomes post ret jmp (Operand.interpM labels address_size o p s)) :
    (@Operand.interp w labels address_size o s p ret).All post := by
  cases o with
  | regOrMem rm =>
      simp only [Operand.interpM] at h
      simp only [Operand.interp]
      exact RegOrMem.interpM_All labels address_size h
  | imm v =>
      simp only [Operand.interpM] at h; mrun h
      simpa only [Operand.interp] using h

theorem RelRegOrMem.interpM_All (labels : Labels) (address_size : AddressSize)
    {o : RelRegOrMem} {s : MachineData} {p : Std.Rco Int64}
    {ret : BitVec 64 → MachineData → Effects} {jmp}
    (h : MachineM.Outcomes post ret jmp (RelRegOrMem.interpM labels address_size o p s)) :
    (@RelRegOrMem.interp labels address_size o s p ret).All post := by
  cases o with
  | rel c =>
      simp only [RelRegOrMem.interpM] at h; mrun h
      simpa only [RelRegOrMem.interp] using h
  | reg r =>
      simp only [RelRegOrMem.interpM] at h; mrun h
      simpa only [RelRegOrMem.interp] using h
  | mem a =>
      simp only [RelRegOrMem.interpM] at h; mrun h
      simp only [RelRegOrMem.interp]
      exact MachineData.loadM_All h

theorem MachineData.setM_All {w} (labels : Labels) (address_size : AddressSize)
    {d : Dst w} {v : w.type} {s : MachineData} {p : Std.Rco Int64}
    {ret : MachineData → Effects} {jmp}
    (h : MachineM.Outcomes post (fun _ => ret) jmp (MachineData.setM labels address_size d v p s)) :
    (@MachineData.set w labels address_size s d v p ret).All post := by
  cases d with
  | reg r =>
      simp only [MachineData.setM] at h; mrun h
      simpa only [MachineData.set] using h
  | mem a =>
      simp only [MachineData.setM] at h; mrun h
      simp only [MachineData.set]
      exact MachineData.storeM_All h

/-! ### Instruction-level transport -/

/-- Reduce one sub-run in both the hypothesis and the transported goal. -/
local macro "mstep" hx:ident h:ident : tactic =>
  `(tactic| simp only [MachineM.Outcomes, bind, EStateM.bind, pure, EStateM.pure, get, getThe,
      MonadStateOf.get, EStateM.get, set, MonadStateOf.set, EStateM.set, modify, modifyGet,
      MonadStateOf.modifyGet, EStateM.modifyGet, throw, throwThe, MonadExceptOf.throw,
      EStateM.throw, $hx:ident] at $h:ident ⊢)

/-- Close a failed sub-run: a jump outcome matches the transported jump arm,
any other error contradicts the hypothesis. -/
local macro "mdone" e:ident h:ident : tactic =>
  `(tactic| (cases $e:ident <;> first | exact $h:ident | exact ($h:ident).elim))

set_option maxHeartbeats 1000000 in
/-- Every instruction's `interpM` run transports into the baseline `Effects`
tree: the tree satisfies `All post` whenever the run's outcome obligates the
continuations accordingly. The under-approximating family (shifts, `mul`,
logic ops) exits with `undefinedFlags`, so its hypothesis is `False` and the
case closes by contradiction. -/
theorem Operation.interpM_All {w} (labels : Labels) (address_size : AddressSize)
    {op : Operation w} {p : Std.Rco Int64} {s : MachineData}
    {next : MachineData → Effects} {jmp : Int64 → MachineData → Effects}
    (h : MachineM.Outcomes post (fun (_ : Unit) s' => next s') jmp
      (Operation.interpM labels address_size op p s)) :
    (@Operation.interp labels address_size w op p s next jmp).All post := by
  cases op
  case mov dst src =>
    simp only [Operation.interpM] at h
    simp only [Operation.interp]
    apply Operand.interpM_All labels address_size
    cases hx : Operand.interpM labels address_size src p s with
    | ok v t => mstep hx h; exact MachineData.setM_All labels address_size h
    | error e t => mstep hx h; mdone e h
  case movsx dst src =>
    simp only [Operation.interpM] at h
    simp only [Operation.interp]
    apply RegOrMem.interpM_All labels address_size
    cases hx : RegOrMem.interpM labels address_size src p s with
    | ok v t => mstep hx h; exact MachineData.setM_All labels address_size h
    | error e t => mstep hx h; mdone e h
  case movzx dst src =>
    simp only [Operation.interpM] at h
    simp only [Operation.interp]
    apply RegOrMem.interpM_All labels address_size
    cases hx : RegOrMem.interpM labels address_size src p s with
    | ok v t => mstep hx h; exact MachineData.setM_All labels address_size h
    | error e t => mstep hx h; mdone e h
  case push src =>
    simp only [Operation.interpM] at h
    simp only [Operation.interp]
    apply Operand.interpM_All labels address_size
    cases hx : Operand.interpM labels address_size src p s with
    | ok v t =>
        mstep hx h
        apply MachineData.storeM_All
        cases hy : MachineData.storeM (t.regs.get64 .rsp - w.bytesv) v t with
        | ok u t' => mstep hy h; exact h
        | error e t' => mstep hy h; mdone e h
    | error e t => mstep hx h; mdone e h
  case pop dst =>
    simp only [Operation.interpM] at h
    simp only [Operation.interp]
    apply MachineData.loadM_All
    cases hx : MachineData.loadM (s.regs.get64 .rsp) w s with
    | ok v t => mstep hx h; exact MachineData.setM_All labels address_size h
    | error e t => mstep hx h; mdone e h
  case setcc cc dst =>
    simp only [Operation.interpM] at h; mrun h
    simp only [Operation.interp]
    exact MachineData.setM_All labels address_size h
  case cmovcc cc dst src =>
    simp only [Operation.interpM] at h
    simp only [Operation.interp]
    apply RegOrMem.interpM_All labels address_size
    cases hx : RegOrMem.interpM labels address_size src p s with
    | ok v t => mstep hx h; exact h
    | error e t => mstep hx h; mdone e h
  case lea dst src =>
    simp only [Operation.interpM] at h; mrun h
    simpa only [Operation.interp] using h
  case add dst src =>
    simp only [Operation.interpM] at h
    simp only [Operation.interp]
    apply Operand.interpM_All labels address_size
    cases hx : Operand.interpM labels address_size src p s with
    | ok a t =>
        mstep hx h
        apply RegOrMem.interpM_All labels address_size
        cases hy : RegOrMem.interpM labels address_size dst p t with
        | ok b u => mstep hy h; exact MachineData.setM_All labels address_size h
        | error e u => mstep hy h; mdone e h
    | error e t => mstep hx h; mdone e h
  case adc dst src =>
    simp only [Operation.interpM] at h
    simp only [Operation.interp]
    apply Operand.interpM_All labels address_size
    cases hx : Operand.interpM labels address_size src p s with
    | ok a t =>
        mstep hx h
        apply RegOrMem.interpM_All labels address_size
        cases hy : RegOrMem.interpM labels address_size dst p t with
        | ok b u => mstep hy h; exact MachineData.setM_All labels address_size h
        | error e u => mstep hy h; mdone e h
    | error e t => mstep hx h; mdone e h
  case adcx dst src =>
    simp only [Operation.interpM] at h
    simp only [Operation.interp]
    apply RegOrMem.interpM_All labels address_size
    cases hx : RegOrMem.interpM labels address_size src p s with
    | ok a t => mstep hx h; exact h
    | error e t => mstep hx h; mdone e h
  case adox dst src =>
    simp only [Operation.interpM] at h
    simp only [Operation.interp]
    apply RegOrMem.interpM_All labels address_size
    cases hx : RegOrMem.interpM labels address_size src p s with
    | ok a t => mstep hx h; exact h
    | error e t => mstep hx h; mdone e h
  case inc dst =>
    simp only [Operation.interpM] at h
    simp only [Operation.interp]
    apply RegOrMem.interpM_All labels address_size
    cases hx : RegOrMem.interpM labels address_size dst p s with
    | ok a t => mstep hx h; exact MachineData.setM_All labels address_size h
    | error e t => mstep hx h; mdone e h
  case dec dst =>
    simp only [Operation.interpM] at h
    simp only [Operation.interp]
    apply RegOrMem.interpM_All labels address_size
    cases hx : RegOrMem.interpM labels address_size dst p s with
    | ok a t => mstep hx h; exact MachineData.setM_All labels address_size h
    | error e t => mstep hx h; mdone e h
  case neg dst =>
    simp only [Operation.interpM] at h
    simp only [Operation.interp]
    apply RegOrMem.interpM_All labels address_size
    cases hx : RegOrMem.interpM labels address_size dst p s with
    | ok a t => mstep hx h; exact MachineData.setM_All labels address_size h
    | error e t => mstep hx h; mdone e h
  case sub dst src =>
    simp only [Operation.interpM] at h
    simp only [Operation.interp]
    apply Operand.interpM_All labels address_size
    cases hx : Operand.interpM labels address_size src p s with
    | ok a t =>
        mstep hx h
        apply RegOrMem.interpM_All labels address_size
        cases hy : RegOrMem.interpM labels address_size dst p t with
        | ok b u => mstep hy h; exact MachineData.setM_All labels address_size h
        | error e u => mstep hy h; mdone e h
    | error e t => mstep hx h; mdone e h
  case sbb dst src =>
    simp only [Operation.interpM] at h
    simp only [Operation.interp]
    apply Operand.interpM_All labels address_size
    cases hx : Operand.interpM labels address_size src p s with
    | ok a t =>
        mstep hx h
        apply RegOrMem.interpM_All labels address_size
        cases hy : RegOrMem.interpM labels address_size dst p t with
        | ok b u => mstep hy h; exact MachineData.setM_All labels address_size h
        | error e u => mstep hy h; mdone e h
    | error e t => mstep hx h; mdone e h
  case cmp a b =>
    simp only [Operation.interpM] at h
    simp only [Operation.interp]
    apply RegOrMem.interpM_All labels address_size
    cases hx : RegOrMem.interpM labels address_size a p s with
    | ok av t =>
        mstep hx h
        apply Operand.interpM_All labels address_size
        cases hy : Operand.interpM labels address_size b p t with
        | ok bv u => mstep hy h; exact h
        | error e u => mstep hy h; mdone e h
    | error e t => mstep hx h; mdone e h
  case mulx r_hi r_lo src1 =>
    simp only [Operation.interpM] at h
    simp only [Operation.interp]
    apply RegOrMem.interpM_All labels address_size
    cases hx : RegOrMem.interpM labels address_size src1 p s with
    | ok a t => mstep hx h; exact h
    | error e t => mstep hx h; mdone e h
  case not dst =>
    simp only [Operation.interpM] at h
    simp only [Operation.interp]
    apply RegOrMem.interpM_All labels address_size
    cases hx : RegOrMem.interpM labels address_size dst p s with
    | ok a t => mstep hx h; exact MachineData.setM_All labels address_size h
    | error e t => mstep hx h; mdone e h
  case bswap dst =>
    cases w <;> simp only [Operation.interpM] at h <;> mrun h
    case W32 => simpa only [Operation.interp] using h
    case W64 => simpa only [Operation.interp] using h
  case cltq =>
    simp only [Operation.interpM] at h; mrun h
    simpa only [Operation.interp] using h
  case cltd =>
    simp only [Operation.interpM] at h; mrun h
    simpa only [Operation.interp] using h
  case jcc cc l =>
    simp only [Operation.interpM] at h; mrun h
    simp only [Operation.interp]
    cases hcc : cc.interp s.status <;> simp only [hcc, Bool.false_eq_true, if_false, if_true,
      ite_true, ite_false, reduceIte] at h ⊢ <;> exact h
  case jmp tgt =>
    simp only [Operation.interpM] at h
    simp only [Operation.interp]
    apply RelRegOrMem.interpM_All labels address_size
    cases hx : RelRegOrMem.interpM labels address_size tgt p s with
    | ok a t => mstep hx h; exact h
    | error e t => mstep hx h; mdone e h
  case call tgt =>
    simp only [Operation.interpM] at h
    simp only [Operation.interp]
    apply RelRegOrMem.interpM_All labels address_size
    cases hx : RelRegOrMem.interpM labels address_size tgt p s with
    | ok a t =>
        mstep hx h
        apply MachineData.storeM_All
        cases hy : MachineData.storeM (t.regs.get64 .rsp - Width.W64.bytesv)
            (w := .W64) p.upper.toBitVec
            { t with regs := t.regs.set64 .rsp (t.regs.get64 .rsp - Width.W64.bytesv) } with
        | ok u t' => mstep hy h; exact h
        | error e t' => mstep hy h; mdone e h
    | error e t => mstep hx h; mdone e h
  case ret =>
    simp only [Operation.interpM] at h
    simp only [Operation.interp]
    apply MachineData.loadM_All
    cases hx : MachineData.loadM (s.regs.get64 .rsp) .W64 s with
    | ok ra t => mstep hx h; exact h
    | error e t => mstep hx h; mdone e h
  case nop sz =>
    simp only [Operation.interpM] at h; mrun h
    simpa only [Operation.interp] using h
  case nopalign a b =>
    simp only [Operation.interpM] at h; mrun h
    simpa only [Operation.interp] using h
  all_goals simp only [Operation.interpM] at h <;> mrun h

theorem Instr.interpM_All (labels : Labels) {i : Instr} {p : Std.Rco Int64} {s : MachineData}
    {next : MachineData → Effects} {jmp : Int64 → MachineData → Effects}
    (h : MachineM.Outcomes post (fun (_ : Unit) s' => next s') jmp (Instr.interpM labels i p s)) :
    (@Instr.interp labels i s p next jmp).All post := by
  unfold Instr.interp
  simp only [Effects.All]
  cases i with
  | regular addr_sz op_sz op =>
      simp only [Instr.interpM] at h
      exact Operation.interpM_All labels (.mk addr_sz) h
  | avx addr_sz op_sz op =>
      simp only [Instr.interpM] at h
      mrun h

theorem Directive.interpM_All (labels : Labels) {d : Directive} {p : Std.Rco Int64}
    {s : MachineData} {next : MachineData → Effects} {jmp : Int64 → MachineData → Effects}
    (h : MachineM.Outcomes post (fun (_ : Unit) s' => next s') jmp (Directive.interpM labels d p s)) :
    (@Directive.interp labels d s p next jmp).All post := by
  cases d with
  | label l =>
      simp only [Directive.interpM] at h; mrun h
      simpa only [Directive.interp] using h
  | instr i =>
      simp only [Directive.interpM] at h
      simp only [Directive.interp]
      exact Instr.interpM_All labels h
  | byteArray bs =>
      simp only [Directive.interpM] at h; mrun h

/-- The fold: a directive list's run transports directive by directive. The
baseline instantiates a directive's jump continuation with the list's return
continuation, so a taken jump on either side exits the fold into `ret`. -/
theorem Directives.interpM_All (labels : Labels) (ds : List (Directive × Nat))
    (s : MachineData) (pc : Int64) {ret : Int64 → MachineData → Effects}
    (h : MachineM.Outcomes post (fun pc' s' => ret pc' s') (fun pc' s' => ret pc' s')
      (Directives.interpM labels ds pc s)) :
    (@Directives.interp labels ds s pc ret).All post := by
  revert h
  fun_induction Directives.interp <;> intro h
  case case1 =>
    simp only [Directives.interpM] at h; mrun h; exact h
  case case2 =>
    rename_i s pc d sz ds ih
    apply Directive.interpM_All labels
    cases hx : Directive.interpM labels d (.mk pc (pc + .ofNat sz)) s with
    | ok u t =>
        simp only [Directives.interpM] at h
        mstep hx h
        exact ih t h
    | error e t =>
        simp only [Directives.interpM] at h
        mstep hx h
        mdone e h

/-- Outcome of a monadic straightline run: fall-through and jump both name the
next machine state; any other exit is not an outcome. -/
def MachineM.step? : EStateM.Result X64Exit MachineData Int64 → Option MachineState
  | .ok pc s => some (s, pc)
  | .error (.jump pc) s => some (s, pc)
  | _ => none

/-- The monadic straightline run's outcome is a valid postcondition of the
baseline's straightline judgment, stated as the body of `straightlineStep`:
every baseline behavior from `(s, pc)` equals the outcome. -/
theorem Executable.straightlineM_adequate (e : _root_.Executable) (s : MachineData) (pc : Int64)
    {st : MachineState} (h : MachineM.step? (e.straightlineM pc s) = some st) :
    (e.straightline (s, pc) .done).All (· = st) := by
  unfold Executable.straightlineM at h
  unfold Executable.straightline
  apply Directives.interpM_All
  cases hr : Directives.interpM e.labels (e.directivesFromAddress pc) pc s with
  | ok pc' s' =>
      simp only [MachineM.step?, hr] at h
      cases h
      simp only [MachineM.Outcomes, hr, Effects.All]
  | error ex s' =>
      cases ex <;> simp only [MachineM.step?, hr] at h <;> cases h <;>
        simp only [MachineM.Outcomes, hr, Effects.All]

/-- The single-step sibling of `straightlineM_adequate`, over the directives at
one address. -/
theorem Executable.stepM_adequate (e : _root_.Executable) (s : MachineData) (pc : Int64)
    {st : MachineState} (h : MachineM.step? (e.stepM pc s) = some st) :
    (e.step (s, pc) .done).All (· = st) := by
  unfold Executable.stepM at h
  unfold Executable.step
  apply Directives.interpM_All
  cases hr : Directives.interpM e.labels (e.directivesAtAddress pc) pc s with
  | ok pc' s' =>
      simp only [MachineM.step?, hr] at h
      cases h
      simp only [MachineM.Outcomes, hr, Effects.All]
  | error ex s' =>
      cases ex <;> simp only [MachineM.step?, hr] at h <;> cases h <;>
        simp only [MachineM.Outcomes, hr, Effects.All]

end OmniAdequacy

end Kraken
