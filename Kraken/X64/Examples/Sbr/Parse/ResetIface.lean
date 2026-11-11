import Kraken.X64.Examples.Sbr.Parse.ResetFoot

/-!
# `sbr_reset`: the interface entries shared by the shards
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

namespace Kraken.Examples.Sbr.Reset

variable [CodeEnv]

/-- The postcondition at the return. -/
abbrev Post' (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ s : MachineData) : Prop :=
  ResetPost k e a ra t₀ s

/-! ## Interface entries (shared by the shards)

The values are tied to `ParseModel`'s relations: `Master` (what `sbr_make_f_master` computed) at
`L2012`, and on the failure paths `Reset (spOf a) (lbN a) a.x st.x.turnoff` (the turnoff of the
current values is a result `Reset` allows). `reset_spec` turns `Reset` into `ResetOut`. -/

/-- The hidden spectrum parameters `Reset` reads. -/
abbrev spOf (a : RArgs) : Spec := ⟨u8 a.sp 0, u8 a.sp 2⟩

/-- `bs_limiter_bands` as `Reset` reads it. -/
abbrev lbN (a : RArgs) : Nat := a.lb.toNat

/-- `f_master` as `Master` states it. -/
abbrev fOf (st : St) : Nat → Nat := fun i => u16 st.fm i

/-- What the `n_q` computation reads besides the decoder values: `k[2] ≤ 64` (checked by
`sbr_make_f_master`) and the `log2f` hypothesis `NqOK`. -/
def NqIn (e : REnv) (st : St) : Prop := st.k2.toNat ≤ 64 ∧ NqOK e.lg

/-- At `L2012` (`sbr_make_f_derived`, after a successful `sbr_make_f_master`): `r12 = sbr`,
`r13 = n_master` (zero-extended), the low byte of `r14` is `bs_xover_band`, the frame slot
`rbp - 0x40` holds `ac`; only `k[0]` (and raw fields) of the decoder values written. -/
def AtDerived (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ s : MachineData) : Prop :=
  ResetCI a t₀ ∧ Base t₀ s ∧ s.regs.get64 .r12 = arg1 t₀
  ∧ ∃ (st : St) (fr : List UInt8) (nm : Nat) (k0 : Int),
    Master a.x.sampleRate.toInt (u8 a.sp 0) (u8 a.sp 2) (some k0) (some (nm, fOf st))
    ∧ st.x = { a.x with k0 := k0.toNat } ∧ st.sp = a.sp ∧ NqIn e st ∧ st.fm.length = 98 ∧ FrOk fr
    ∧ s.regs.get64 .r13 = BitVec.ofNat 64 nm
    ∧ (s.regs.get64 .r14).setWidth 8 = BitVec.ofNat 8 (u8 a.sp 2)
    ∧ frSlot64 fr 0x40 = arg0 t₀
    ∧ (s.dmem =⋆ Mm k e a ra t₀ st fr)

/-- On the failure paths, at `L1d31` (the last `av_log` and `sbr_turnoff`): `r12 = sbr`,
`r15 = ac`, and turning the current values off is a result `Reset` allows. -/
def AtFail (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ s : MachineData) : Prop :=
  ResetCI a t₀ ∧ Base t₀ s ∧ s.regs.get64 .r12 = arg1 t₀ ∧ s.regs.get64 .r15 = arg0 t₀
  ∧ ∃ (st : St) (fr : List UInt8), Reset (spOf a) (lbN a) a.x st.x.turnoff ∧ st.sp = a.sp
    ∧ st.fm.length = 98
    ∧ FrOk fr ∧ (s.dmem =⋆ Mm k e a ra t₀ st fr)

/-- `AtFail` before an `av_log` call (`rdi = avctx`). -/
def AtFailLog (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtFail k e a ra t₀ s ∧ s.regs.get64 .rdi = a.x.avctx

/-- At the epilogue `L1d95`: the result values. -/
def AtExit (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ s : MachineData) : Prop :=
  ResetCI a t₀ ∧ Base t₀ s
  ∧ ∃ (u : BitVec 32) (st : St) (fr : List UInt8), ResetOut a st.x st.sp u ∧ st.fm.length = 98
    ∧ FrOk fr ∧ (s.dmem =⋆ Mm k e { a with us := u } ra t₀ st fr)

/-! ## Cell access (shared) -/

section Access

variable {m : Mem 64} {addr : BitVec 64} {F : Mem 64 → Prop}

omit [CodeEnv] in
/-- A load of a whole byte cell `bs =@ addr` (the first `n ≤ |bs|` bytes) is defined. -/
theorem val_isSome {bs : List UInt8} (h : m =⋆ bs =@ addr ⋆ F) {n : Nat} (hn : n ≤ bs.length)
    (hw : bs.length < 2 ^ 64) : (m.loadInt addr n).isSome = true := by
  have := region_load (o := 0) (n := n) h (addr := addr) (BitVec.add_zero addr).symm
    (by omega) hw
  rw [this]; rfl

omit [CodeEnv] in
theorem c4_isSome {v : Nat} (h : m =⋆ c4 addr v ⋆ F) : (m.loadInt addr 4).isSome = true :=
  val_isSome h (by rw [Int.toBytes_length]; exact Nat.le_refl _) (by rw [Int.toBytes_length]; decide)

omit [CodeEnv] in
theorem c4_load {v : Nat} (h : m =⋆ c4 addr v ⋆ F) :
    m.loadInt addr 4 = some (Int.ofBytes (Int.toBytes 4 (v : Int))) :=
  loadInt_sep _ _ 4 F m h (Int.toBytes_length 4 _) (by omega)

omit [CodeEnv] in
theorem cell4_isSome {v : BitVec 32} (h : m =⋆ cell4 addr v ⋆ F) : (m.loadInt addr 4).isSome = true :=
  val_isSome h (by rw [Int.toBytes_length]; exact Nat.le_refl _) (by rw [Int.toBytes_length]; decide)

omit [CodeEnv] in
theorem c8_isSome {v : BitVec 64} (h : m =⋆ c8 addr v ⋆ F) : (m.loadInt addr 8).isSome = true :=
  val_isSome h (by rw [Int.toBytes_length]; exact Nat.le_refl _) (by rw [Int.toBytes_length]; decide)

omit [CodeEnv] in
/-- A store into a `c4` cell, the stored value read as the new `Nat` value `n`. -/
theorem c4_store {v : Nat} (h : m =⋆ c4 addr v ⋆ F) (w : Int) (n : Nat)
    (hw : Int.toBytes 4 w = Int.toBytes 4 (n : Int)) : m.storeInt addr 4 w =⋆ c4 addr n ⋆ F := by
  have := storeInt_sep addr 4 _ F m ⟨h, Int.toBytes_length 4 _⟩ w
  rw [hw] at this; exact this

omit [CodeEnv] in
theorem cell4_store' {v : BitVec 32} (h : m =⋆ cell4 addr v ⋆ F) (w : Int) (n : BitVec 32)
    (hw : Int.toBytes 4 w = Int.toBytes 4 n.toInt) : m.storeInt addr 4 w =⋆ cell4 addr n ⋆ F := by
  have := storeInt_sep addr 4 _ F m ⟨h, Int.toBytes_length 4 _⟩ w
  rw [hw] at this; exact this

end Access

/-- `sbr_turnoff`'s progress on the values `st0` (`L1d4d` → `L1d95`): `0` nothing, `1` `start`,
`ready` cleared, `2` also `kx[1] = 32`, `m[1] = 0`, `3` also `spectrum_params` all `0xff`. -/
def offSt : Nat → St → St
  | 0, st => st
  | 1, st => { st with x := { st.x with start := 0, ready := 0 } }
  | 2, st => { st with x := st.x.turnoff }
  | _, st => { st with x := st.x.turnoff, sp := List.replicate 6 0xff }

/-- The `usac` cell during `sbr_turnoff`: cleared from step `1` on. -/
def offA : Nat → RArgs → RArgs
  | 0, a => a
  | _, a => { a with us := 0 }

/-- Inside `sbr_turnoff` (after the last `av_log`): `r12 = sbr`, `rbx = &spectrum_params`. -/
def AtOff (j k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ s : MachineData) : Prop :=
  ResetCI a t₀ ∧ Base t₀ s ∧ s.regs.get64 .r12 = arg1 t₀ ∧ s.regs.get64 .rbx = arg1 t₀ + 0x1c#64
  ∧ ∃ (st : St) (fr : List UInt8), Reset (spOf a) (lbN a) a.x st.x.turnoff ∧ st.sp = a.sp
    ∧ st.fm.length = 98
    ∧ FrOk fr ∧ (s.dmem =⋆ Mm k e (offA j a) ra t₀ (offSt j st) fr)

end Kraken.Examples.Sbr.Reset
