import Kraken.X64.Examples.Sbr.Parse.GridText
import Kraken.X64.Examples.Sbr.Parse.LibGb
import Kraken.X64.Examples.Sbr.Parse.LibAbort
import Kraken.X64.Examples.Sbr.ApplySpec
import Kraken.X64.Examples.Sbr.SessionSpec

/-!
# `read_sbr_grid`: the specification

`read_sbr_grid(ac, sbr, gb, ch_data)` (`libavcodec/aacsbr_template.c`, FFmpeg n8.1) parses the
time/frequency grid of one channel from the bitstream reader `gb` into `*ch_data`.

* Logical variables `GArgs`: the caller's memory `R`, the values `v : DV` of `*ch_data`
  (`ApplySpec.lean`), `sbr->usac`, `sbr->bs_amp_res_header`, `ac->avctx`, and the bit reader
  `*gb` (`GetBitContext`: `buffer` at +0, `index` at +8, `size_in_bits` at +0xc,
  `size_in_bits_plus8` at +0x10) with the bytes `[buffer, buffer + L)` the caller owns.
* The bitstream contents are not constrained. The reader's precondition is
  `index ≤ size_in_bits_plus8 < 2^31` and `size_in_bits_plus8 / 8 + 4 ≤ L` (every read loads at
  most 4 bytes at `buffer + index / 8`; in the decoder `L` is the packet size plus
  `AV_INPUT_BUFFER_PADDING_SIZE`).
* The values between blocks are a `GSt` (the `int` fields as 32-bit cells).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply

namespace Kraken.Examples.Sbr.Grid

structure GArgs where
  R : Mem 64 → Prop
  v : DV
  usac : BitVec 32
  ampHdr : BitVec 32
  avctx : BitVec 64
  buf : BitVec 64
  idx : BitVec 32
  p8 : BitVec 32
  L : Nat

/-- The fields `read_sbr_grid` writes, with the reader's `index`: `index`, `bs_num_env`,
`bs_freq_res[9]`, `bs_num_noise`, `t_env[9]` with `t_env_num_env_old`, `t_q[3]`. -/
structure GSt where
  i : BitVec 32
  n : BitVec 32
  fr : List UInt8
  nn : BitVec 32
  te : List UInt8
  tq : List UInt8

/-- The state with the reader's index `i`. -/
abbrev GSt.withI (st : GSt) (i : BitVec 32) : GSt := { st with i := i }

/-- The state with `bs_num_env = n`. -/
abbrev GSt.withN (st : GSt) (n : BitVec 32) : GSt := { st with n := n }

/-- The state with `bs_num_noise = n`. -/
abbrev GSt.withNn (st : GSt) (n : BitVec 32) : GSt := { st with nn := n }

/-- The state with `bs_freq_res[j] = v`. -/
abbrev GSt.setFr (st : GSt) (j : Nat) (v : BitVec 8) : GSt :=
  { st with fr := st.fr.set j (UInt8.ofBitVec v) }

/-- The state with `t_env[j] = v` (`j = 9`: `t_env_num_env_old`). -/
abbrev GSt.setTe (st : GSt) (j : Nat) (v : BitVec 8) : GSt :=
  { st with te := st.te.set j (UInt8.ofBitVec v) }

/-- The state with `t_q[j] = v`. -/
abbrev GSt.setTq (st : GSt) (j : Nat) (v : BitVec 8) : GSt :=
  { st with tq := st.tq.set j (UInt8.ofBitVec v) }

/-- The values at entry. -/
def GArgs.st (x : GArgs) : GSt :=
  ⟨x.idx, BitVec.ofNat 32 x.v.nenv, x.v.freqRes, BitVec.ofNat 32 x.v.nnoise, x.v.te, x.v.tq⟩

/-- The `DV` a state describes (the fields `read_sbr_grid` does not write from `x.v`). -/
def GSt.dv (x : GArgs) (st : GSt) : DV :=
  { x.v with nenv := st.n.toNat, freqRes := st.fr, nnoise := st.nn.toNat, te := st.te,
             tq := st.tq }

variable [CodeEnv]

/-- `*ch_data` at `d`: `bs_frame_class` (+0, raw), `bs_num_env`, `bs_freq_res`, `bs_num_noise`,
`bs_amp_res` (+0x64, raw), `e_a[2]` (+0x3904, raw), `t_env` with `t_env_num_env_old`, `t_q`. -/
abbrev ChW (d : BitVec 64) (st : GSt) : Mem 64 → Prop :=
  4 ?@ d ⋆ (cell4 (d + 8#64) st.n ⋆ (st.fr =@ (d + 0xc#64) ⋆ (cell4 (d + 0x18#64) st.nn
    ⋆ (4 ?@ (d + 0x64#64) ⋆ (8 ?@ (d + 0x3904#64) ⋆ (st.te =@ (d + 0x15a9c#64)
    ⋆ st.tq =@ (d + 0x15aa6#64)))))))

/-- `*gb` at `g` with `index = i` (`size_in_bits` raw). -/
abbrev GbW (g : BitVec 64) (x : GArgs) (i : BitVec 32) : Mem 64 → Prop :=
  Int.toBytes 8 x.buf.toInt =@ g ⋆ (cell4 (g + 8#64) i ⋆ (4 ?@ (g + 0xc#64)
    ⋆ cell4 (g + 0x10#64) x.p8))

/-- What is only read: `sbr->usac`, `sbr->bs_amp_res_header`, `ac->avctx`, the bitstream
bytes, `ceil_log2`, the jump table, and `av_log`'s state `Ext`. -/
def InW (Ext : Mem 64 → Prop) (x : GArgs) (t : MachineData) : Mem 64 → Prop :=
  cell4 (arg1 t + 0x10#64) x.usac ⋆ (cell4 (arg1 t + 0x24#64) x.ampHdr
    ⋆ (Int.toBytes 8 x.avctx.toInt =@ (arg0 t + 8#64)
    ⋆ (Blocks [(x.buf, x.L), (lab "ceil_log2", 6)] ⋆ (JtW ⋆ Ext))))

/-- The footprint at the values `st`. -/
abbrev GF (Ext : Mem 64 → Prop) (x : GArgs) (t : MachineData) (st : GSt) : Mem 64 → Prop :=
  ChW (arg3 t) st ⋆ (GbW (arg2 t) x st.i ⋆ InW Ext x t)

/-- The side conditions. -/
def GridC (x : GArgs) : Prop :=
  DWF False x.v ∧ u8 x.v.te x.v.nenv ≤ 19
  ∧ x.idx.toNat ≤ x.p8.toNat ∧ x.p8.toNat < 2 ^ 31 ∧ x.p8.toNat / 8 + 4 ≤ x.L ∧ x.L < 2 ^ 32
  ∧ JtC

abbrev GridPre (k : Nat) (Ext : Mem 64 → Prop) (x : GArgs) (ra : Int64) (t : MachineData) : Prop :=
  CallPre (gridNeed k) (GF Ext x t x.st ⋆ x.R) ra t ∧ GridC x

/-- What a return leaves: the `DV` it describes keeps `DWF False` and the border invariant
(on every path, including the returns `-1` after stores), `0` is returned only for a live
grid, the reader's `index` stays within `size_in_bits_plus8`. -/
def GridOut (x : GArgs) (st : GSt) (ret : BitVec 32) : Prop :=
  DWF False (st.dv x) ∧ u8 st.te st.n.toNat ≤ 19
  ∧ (ret = 0#32 ∨ ret = 0xffffffff#32)
  ∧ (ret = 0#32 → 1 ≤ st.n.toNat ∧ (∀ e, e ≤ st.n.toNat → u8 st.te e ≤ 19)
      ∧ (∀ e, e < st.n.toNat → u8 st.te e < u8 st.te (e + 1)))
  ∧ st.i.toNat ≤ x.p8.toNat

abbrev GridPost (k : Nat) (Ext : Mem 64 → Prop) (x : GArgs) (ra : Int64) (t s : MachineData) :
    Prop :=
  ∃ st, GridOut x st ((s.regs.get64 .rax).setWidth 32)
    ∧ CallPost (gridNeed k) (GF Ext x t st ⋆ x.R) ra t s

end Kraken.Examples.Sbr.Grid
