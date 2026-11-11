/-
Memory-mapped devices over the denotational monad `X64M D`.

A non-memory load or store consults a `Device D` model instead of faulting. The
device state is the `device` component of `Sys D`, so it lives in the exception-
carrying machine state: a `jump` preserves it, exactly as it preserves the CPU
`MachineData`. A device handler sees and may return data memory alongside the
device state, so a load or store transitions the device and either can move
ownership of a memory range between `dmem` and the device.
-/
import Kraken.X64M

open Std.WP
open Std.WP.WPMonad
open Lean.Order

namespace Kraken

/-- A memory-mapped device. A load handler replies with a value and may hand back
data memory and a new device state; a store handler consumes the written value and
may likewise return data memory and a new device state. `none` means the address is
not a device register, so the access is a genuine non-memory fault. -/
structure Device (D : Type) where
  readStep : BitVec 64 → DataMem → D → Option (Int × DataMem × D)
  writeStep : BitVec 64 → Int → DataMem → D → Option (DataMem × D)

/-- Set both the data memory and the device state in one system-state update. -/
private def putMemDev {D : Type} (dmem : DataMem) (d : D) : X64M D Unit :=
  liftM (modify (fun s => { machine := { s.machine with dmem := dmem }, device := d }) : SysM D Unit)

/-- Read 8 bytes at `addr`: from `dmem` when mapped, otherwise from the device. -/
def Op.devLoad {D : Type} (dev : Device D) (addr : BitVec 64) : X64M D Int := do
  let s ← liftM (getThe (Sys D) : SysM D (Sys D))
  match Mem.loadInt s.machine.dmem addr 8 with
  | some i => pure i
  | none =>
    match dev.readStep addr s.machine.dmem s.device with
    | some (v, dmem', d') => putMemDev dmem' d'; pure v
    | none => liftM (throw (.nonmemLoad s.machine.dmem addr .W64) : SysM D Int)

/-- Write 8 bytes at `addr`: to `dmem` when mapped, otherwise to the device. -/
def Op.devStore {D : Type} (dev : Device D) (addr : BitVec 64) (v : Int) : X64M D Unit := do
  let s ← liftM (getThe (Sys D) : SysM D (Sys D))
  match Mem.loadInt s.machine.dmem addr 8 with
  | some _ => modifyMachine (fun m => { m with dmem := Mem.storeInt m.dmem addr 8 v })
  | none =>
    match dev.writeStep addr v s.machine.dmem s.device with
    | some (dmem', d') => putMemDev dmem' d'
    | none => liftM (throw (.nonmemStore s.machine.dmem addr .W64) : SysM D Unit)

section
variable {D : Type} (Q : Int → Env → Int64 → Sys D → Prop) (R : Unit → Env → Int64 → Sys D → Prop)
    (E : X64Exit → Sys D → Prop)

/-- Weakest precondition of a device-aware load: the mapped value under the `dmem`
reply, the device reply otherwise. `vcgen` splits on the address being mapped and
on the device accepting it. -/
@[spec] theorem Op.devLoad_spec (dev : Device D) (addr : BitVec 64) :
    ⦃ fun env rip s =>
        (∀ i, Mem.loadInt s.machine.dmem addr 8 = some i → Q i env rip s)
          ⊓ (Mem.loadInt s.machine.dmem addr 8 = none →
              (∀ v dmem' d', dev.readStep addr s.machine.dmem s.device = some (v, dmem', d') →
                  Q v env rip { machine := { s.machine with dmem := dmem' }, device := d' })
                ⊓ (dev.readStep addr s.machine.dmem s.device = none →
                    E (.nonmemLoad s.machine.dmem addr .W64) s)) ⦄
      Op.devLoad dev addr ⦃ Q; E ⦄ := by
  sym =>
    vcgen [Op.devLoad, putMemDev]
    all_goals finish

/-- Weakest precondition of a device-aware store: the `dmem` update when mapped,
the device transition otherwise. -/
@[spec] theorem Op.devStore_spec (dev : Device D) (addr : BitVec 64) (v : Int) :
    ⦃ fun env rip s =>
        (∀ i, Mem.loadInt s.machine.dmem addr 8 = some i →
            R () env rip { s with machine := { s.machine with
              dmem := Mem.storeInt s.machine.dmem addr 8 v } })
          ⊓ (Mem.loadInt s.machine.dmem addr 8 = none →
              (∀ dmem' d', dev.writeStep addr v s.machine.dmem s.device = some (dmem', d') →
                  R () env rip { machine := { s.machine with dmem := dmem' }, device := d' })
                ⊓ (dev.writeStep addr v s.machine.dmem s.device = none →
                    E (.nonmemStore s.machine.dmem addr .W64) s)) ⦄
      Op.devStore dev addr v ⦃ R; E ⦄ := by
  sym =>
    vcgen [Op.devStore, putMemDev, modifyMachine]
    all_goals finish

end

end Kraken
