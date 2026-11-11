import Kraken.X64.Examples.Sbr.Parse.HdrText
import Kraken.X64.Examples.Sbr.ParseModel

/-!
# `read_sbr_header`: the specification

`read_sbr_header(sbr, gb, is_usac)` (`libavcodec/aacsbr_template.c`, FFmpeg n8.1, l.188-247)
reads the SBR header from the bit reader `gb` into `*sbr` and returns the number of bits read.

* Logical variables `HArgs`: the caller's memory `R`, the fields of `*sbr` the routine reads or
  writes (`start`, `ready_for_dequant`, `reset`, `spectrum_params` as its 6 bytes,
  `bs_amp_res_header`, `bs_limiter_bands`, `bs_limiter_gains`, `bs_interpol_freq`,
  `bs_smoothing_mode`) and the bit reader `*gb` (`GetBitContext`: `buffer` at +0, `index` at
  +8, `size_in_bits` at +0xc, `size_in_bits_plus8` at +0x10) with the bytes
  `[buffer, buffer + L)` the caller owns.
* The bitstream contents are not constrained. The reader's precondition is
  `index ≤ size_in_bits_plus8 < 2^31` and `size_in_bits_plus8 / 8 + 4 ≤ L`.
* `sbr_make_f_tablelim(sbr)` is called when `bs_limiter_bands` changed and no reset is
  pending. Its contract `TlimSpec` is a hypothesis: it is given `bs_limiter_bands` and the
  footprint `TlT sbr`, and returns `TlT' lb sbr`; its side condition is `TlC lb sbr`.
* The values written are an `HSt`. The post (`HdrOut`) is what `Header` of `ParseModel`
  needs: `start = 1`, `ready_for_dequant = 0`, the field widths, `reset` set exactly when
  `spectrum_params` changed, the reader's `index` within `size_in_bits_plus8`, and the return
  value `index' - index`.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply

namespace Kraken.Examples.Sbr.Hdr

structure HArgs where
  R : Mem 64 → Prop
  start : BitVec 32
  ready : BitVec 32
  reset : BitVec 32
  sp : List UInt8
  amp : BitVec 32
  lb : BitVec 32
  lg : BitVec 32
  ip : BitVec 32
  sm : BitVec 32
  buf : BitVec 64
  idx : BitVec 32
  p8 : BitVec 32
  L : Nat

/-- The fields `read_sbr_header` writes, with the reader's `index`. -/
structure HSt where
  i : BitVec 32
  start : BitVec 32
  ready : BitVec 32
  reset : BitVec 32
  sp : List UInt8
  amp : BitVec 32
  lb : BitVec 32
  lg : BitVec 32
  ip : BitVec 32
  sm : BitVec 32

/-- The values at entry. -/
def HArgs.st (x : HArgs) : HSt :=
  ⟨x.idx, x.start, x.ready, x.reset, x.sp, x.amp, x.lb, x.lg, x.ip, x.sm⟩

variable [CodeEnv]

/-- The fields of `*sbr` at `s` (`usac` raw: the routine overwrites it with `is_usac`; `SbWu` has
it as a value). -/
abbrev SbW (s : BitVec 64) (st : HSt) : Mem 64 → Prop :=
  cell4 (s + 0x4#64) st.start ⋆ (cell4 (s + 0x8#64) st.ready ⋆ (4 ?@ (s + 0x10#64)
    ⋆ (cell4 (s + 0x18#64) st.reset ⋆ (st.sp =@ (s + 0x1c#64) ⋆ (cell4 (s + 0x24#64) st.amp
    ⋆ (cell4 (s + 0x2c#64) st.lb ⋆ (cell4 (s + 0x30#64) st.lg ⋆ (cell4 (s + 0x34#64) st.ip
    ⋆ cell4 (s + 0x38#64) st.sm))))))))

/-- `SbW` with `usac = u` (at the return, `u` is `is_usac`). -/
abbrev SbWu (s : BitVec 64) (u : BitVec 32) (st : HSt) : Mem 64 → Prop :=
  cell4 (s + 0x4#64) st.start ⋆ (cell4 (s + 0x8#64) st.ready ⋆ (cell4 (s + 0x10#64) u
    ⋆ (cell4 (s + 0x18#64) st.reset ⋆ (st.sp =@ (s + 0x1c#64) ⋆ (cell4 (s + 0x24#64) st.amp
    ⋆ (cell4 (s + 0x2c#64) st.lb ⋆ (cell4 (s + 0x30#64) st.lg ⋆ (cell4 (s + 0x34#64) st.ip
    ⋆ cell4 (s + 0x38#64) st.sm))))))))

/-- `*gb` at `g` with `index = i` (`size_in_bits` raw). -/
abbrev GbW (g : BitVec 64) (x : HArgs) (i : BitVec 32) : Mem 64 → Prop :=
  Int.toBytes 8 x.buf.toInt =@ g ⋆ (cell4 (g + 8#64) i ⋆ (4 ?@ (g + 0xc#64)
    ⋆ cell4 (g + 0x10#64) x.p8))

/-- The footprint at the values `st`, with `Tl` the part `sbr_make_f_tablelim` owns. -/
abbrev HF (x : HArgs) (t : MachineData) (st : HSt) (Tl : Mem 64 → Prop) : Mem 64 → Prop :=
  SbW (arg0 t) st ⋆ (GbW (arg1 t) x st.i ⋆ (Blocks [(x.buf, x.L)] ⋆ Tl))

/-- `HF` with `usac = u`. -/
abbrev HFu (x : HArgs) (u : BitVec 32) (t : MachineData) (st : HSt) (Tl : Mem 64 → Prop) :
    Mem 64 → Prop :=
  SbWu (arg0 t) u st ⋆ (GbW (arg1 t) x st.i ⋆ (Blocks [(x.buf, x.L)] ⋆ Tl))

/-- The contract assumed for `sbr_make_f_tablelim(sbr)`: it holds `bs_limiter_bands = lb`
(read only) and the footprint `TlT sbr`, which it leaves as `TlT' lb sbr`, under the side
condition `TlC lb sbr`. -/
abbrev TlimSpec (TlT : BitVec 64 → Mem 64 → Prop) (TlT' : BitVec 32 → BitVec 64 → Mem 64 → Prop)
    (TlC : BitVec 32 → BitVec 64 → Prop) (k : Nat) : Prop :=
  cenv.ProcSpec (entry "sbr_make_f_tablelim")
    (fun (y : (Mem 64 → Prop) × BitVec 32) ra t =>
      CallPre k (cell4 (arg0 t + 0x2c#64) y.2 ⋆ (TlT (arg0 t) ⋆ y.1)) ra t ∧ TlC y.2 (arg0 t))
    (fun y ra t s => CallPost k (cell4 (arg0 t + 0x2c#64) y.2 ⋆ (TlT' y.2 (arg0 t) ⋆ y.1)) ra t s)

/-- The side conditions: `spectrum_params` is 6 bytes, the reader's bounds, and the
callee's side condition on the path that calls it (no reset pending at entry, and then the
old `bs_start_freq` equals the new one, a 4-bit value). -/
def HdrC (TlC : BitVec 32 → BitVec 64 → Prop) (x : HArgs) (t : MachineData) : Prop :=
  x.sp.length = 6
  ∧ x.idx.toNat ≤ x.p8.toNat ∧ x.p8.toNat < 2 ^ 31 ∧ x.p8.toNat / 8 + 4 ≤ x.L ∧ x.L < 2 ^ 32
  ∧ (x.reset = 0#32 → u8 x.sp 0 < 16 → ∀ lb : BitVec 32, lb.toNat < 4 → lb ≠ x.lb →
      TlC lb (arg0 t))

/-- The stack: three pushes, 16 bytes of locals, the return slot of the call, the callee's
`k`. -/
abbrev hdrNeed (k : Nat) : Nat := 0x30 + k

/-- Whether the routine called `sbr_make_f_tablelim`. -/
abbrev HSt.called (x : HArgs) (st : HSt) : Prop := st.lb ≠ x.lb ∧ st.reset = 0#32

/-- The callee's part of the footprint after the routine. -/
abbrev TlOut (TlT : BitVec 64 → Mem 64 → Prop) (TlT' : BitVec 32 → BitVec 64 → Mem 64 → Prop)
    (x : HArgs) (t : MachineData) (st : HSt) : Mem 64 → Prop :=
  if st.called x then TlT' st.lb (arg0 t) else TlT (arg0 t)

abbrev HdrPre (k : Nat) (TlT : BitVec 64 → Mem 64 → Prop)
    (TlC : BitVec 32 → BitVec 64 → Prop) (x : HArgs) (ra : Int64) (t : MachineData) : Prop :=
  CallPre (hdrNeed k) (HF x t x.st (TlT (arg0 t)) ⋆ x.R) ra t ∧ HdrC TlC x t

/-- What a return leaves (`usac` is the third argument, `is_usac`; the post's footprint has
`sbr->usac = usac`, `HFu`). -/
def HdrOut (x : HArgs) (usac : BitVec 32) (st : HSt) (ret : BitVec 32) : Prop :=
  st.start = 1#32 ∧ st.ready = 0#32 ∧ st.sp.length = 6
  ∧ u8 st.sp 0 < 16 ∧ u8 st.sp 1 < 16
  ∧ (usac = 0#32 → u8 st.sp 2 < 8 ∧ st.amp.toNat < 2)
  ∧ (usac ≠ 0#32 → st.sp.getD 2 0 = x.sp.getD 2 0 ∧ st.amp = x.amp)
  ∧ u8 st.sp 3 < 4 ∧ u8 st.sp 4 < 2 ∧ u8 st.sp 5 < 4
  ∧ st.reset = (if st.sp = x.sp then x.reset else 1#32)
  ∧ st.lb.toNat < 4 ∧ st.lg.toNat < 4 ∧ st.ip.toNat < 2 ∧ st.sm.toNat < 2
  ∧ x.idx.toNat ≤ st.i.toNat ∧ st.i.toNat ≤ x.p8.toNat ∧ ret = st.i - x.idx

abbrev HdrPost (k : Nat) (TlT : BitVec 64 → Mem 64 → Prop)
    (TlT' : BitVec 32 → BitVec 64 → Mem 64 → Prop) (x : HArgs) (ra : Int64)
    (t s : MachineData) : Prop :=
  ∃ st, HdrOut x ((arg2 t).setWidth 32) st ((s.regs.get64 .rax).setWidth 32)
    ∧ CallPost (hdrNeed k)
      (HFu x ((arg2 t).setWidth 32) t st (TlOut TlT TlT' x t st) ⋆ x.R) ra t s

/-- The routine's contract (proved in `HdrProc`), given the callee's. -/
abbrev HdrSpec (k : Nat) (TlT : BitVec 64 → Mem 64 → Prop)
    (TlT' : BitVec 32 → BitVec 64 → Mem 64 → Prop) (TlC : BitVec 32 → BitVec 64 → Prop) :
    Prop :=
  cenv.ProcSpec (entry "read_sbr_header") (HdrPre k TlT TlC) (HdrPost k TlT TlT')

end Kraken.Examples.Sbr.Hdr
