import Kraken.X64.Examples.Sbr.Parse.DtdfText
import Kraken.X64.Examples.Sbr.Parse.Lib
import Kraken.X64.Examples.Sbr.ApplySpec

/-!
# `read_sbr_dtdf`: the specification

`read_sbr_dtdf(sbr, gb, ch_data, indep_flag)` (`libavcodec/aacsbr_template.c`, FFmpeg n8.1)
reads the delta-coding flags `bs_df_env[0..bs_num_env)` and `bs_df_noise[0..bs_num_noise)` of one
channel, one bit each (`get_bits1`). For USAC with `indep_flag` the first flag of each vector is
`0` and only the others are read.

* In the object the first argument is the value `sbr->usac` (the routine reads no other field of
  `*sbr`); `rdi`, `ecx` are not constrained.
* Logical variables `DArgs`: the caller's memory `R`, the values `v : DV` of `*ch_data`
  (`ApplySpec.lean`; only `bs_num_env` and `bs_num_noise` are read), and the bit reader `*gb`
  (`GetBitContext`: `buffer` at +0, `index` at +8, `size_in_bits` at +0xc, `size_in_bits_plus8`
  at +0x10) with the bytes `[buffer, buffer + L)` the caller owns.
* The flag arrays `bs_df_env[9] ++ bs_df_noise[2]` (11 bytes at `ch_data + 0x1c`) are owned as
  raw bytes: their values are not constrained before or after.
* The reader's precondition is the one of the grid parser: `index ≤ size_in_bits_plus8 < 2^31`,
  `size_in_bits_plus8 / 8 + 4 ≤ L`.
* The postcondition: the same footprint, with a reader index that stays within
  `size_in_bits_plus8`; no `DV` value is written (`ParseModel`'s `Elem`: the routine writes no
  field of `Args`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply

namespace Kraken.Examples.Sbr.Dtdf

structure DArgs where
  R : Mem 64 → Prop
  v : DV
  buf : BitVec 64
  idx : BitVec 32
  p8 : BitVec 32
  L : Nat

variable [CodeEnv]

/-- `*gb` at `g` with `index = i` (`size_in_bits` raw). -/
abbrev GbW (g : BitVec 64) (x : DArgs) (i : BitVec 32) : Mem 64 → Prop :=
  Int.toBytes 8 x.buf.toInt =@ g ⋆ (cell4 (g + 8#64) i ⋆ (4 ?@ (g + 0xc#64)
    ⋆ cell4 (g + 0x10#64) x.p8))

/-- The footprint with the reader index `i`: `bs_num_env`, `bs_num_noise`,
`bs_df_env ++ bs_df_noise` of `*ch_data` (`rdx`), `*gb` (`rsi`), the bitstream bytes. -/
abbrev DtdfF (x : DArgs) (t : MachineData) (i : BitVec 32) : Mem 64 → Prop :=
  c4 (arg2 t + 8#64) x.v.nenv ⋆ (c4 (arg2 t + 0x18#64) x.v.nnoise
    ⋆ (11 ?@ (arg2 t + 0x1c#64) ⋆ (GbW (arg1 t) x i ⋆ Blocks [(x.buf, x.L)])))

/-- The side conditions (`bs_num_env ≤ 8`, `bs_num_noise ≤ 2` are clauses of `DWF`). -/
def DtdfC (x : DArgs) : Prop :=
  x.v.nenv ≤ 8 ∧ x.v.nnoise ≤ 2
  ∧ x.idx.toNat ≤ x.p8.toNat ∧ x.p8.toNat < 2 ^ 31 ∧ x.p8.toNat / 8 + 4 ≤ x.L ∧ x.L < 2 ^ 32

abbrev DtdfPre (k : Nat) (x : DArgs) (ra : Int64) (t : MachineData) : Prop :=
  CallPre k (DtdfF x t x.idx ⋆ x.R) ra t ∧ DtdfC x

abbrev DtdfPost (k : Nat) (x : DArgs) (ra : Int64) (t s : MachineData) : Prop :=
  ∃ i : BitVec 32, i.toNat ≤ x.p8.toNat ∧ CallPost k (DtdfF x t i ⋆ x.R) ra t s

end Kraken.Examples.Sbr.Dtdf
