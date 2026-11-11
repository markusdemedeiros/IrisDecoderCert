import Kraken.X64.Examples.Sbr.Parse.NoiseText
import Kraken.X64.Examples.Sbr.Parse.EnvVlc
import Kraken.X64.Examples.Sbr.Parse.LibGb

/-!
# `read_sbr_noise`: the specification

`read_sbr_noise(ac, sbr, gb, ch_data, ch)` (`libavcodec/aacsbr_template.c`, FFmpeg n8.1) parses
the noise floor deltas of channel `ch` from the bitstream reader `gb` into
`ch_data->noise_facs_q[1..bs_num_noise]` (Huffman coded with `t_huff`/`f_huff` from
`ff_aac_sbr_vlc`, see `EnvVlc.lean`), then copies row `bs_num_noise` to row 0.

* Logical variables `NArgs`: the caller's memory `R`, `sbr->bs_coupling`, `sbr->n_q`,
  `ch_data->bs_num_noise`, `ac->avctx`, the bit reader (`buffer`, `index`,
  `size_in_bits_plus8`, the `L` bitstream bytes the caller owns), the ten VLC tables `v`.
* `bs_df_noise[2]` and `noise_facs_q[3][5]` are raw bytes: the values parsed are not
  constrained (the code checks each against 30 and fails with `AVERROR_INVALIDDATA`).
* The side conditions: `bs_num_noise ≤ 2`, `n_q ≤ 5` (`SbrWF`), the tables `VlcC`, the reader's
  bounds (`GbC`).
* The callee: `av_log` (`AvLogSpec`, with its state `Ext` in the footprint).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Vlc
open Kraken.Examples.Sbr.Parse (GbW)

namespace Kraken.Examples.Sbr.Noise

structure NArgs where
  R : Mem 64 → Prop
  cpl : BitVec 32
  nq : Nat
  nn : Nat
  avctx : BitVec 64
  buf : BitVec 64
  idx : BitVec 32
  p8 : BitVec 32
  L : Nat
  v : Nat → VlcTab

variable [CodeEnv]

/-- The footprint, with the reader's `index = i`: `sbr->bs_coupling` (`+0x3c`), `sbr->n_q`
(`+0x4c1e8`), `ch_data->bs_num_noise` (`+0x18`), `bs_df_noise[2]` (`+0x25`, raw),
`noise_facs_q[3][5]` (`+0x15a50`, raw), `ac->avctx`, `*gb`, the bitstream bytes,
`ff_aac_sbr_vlc` with its tables, `av_log`'s state `Ext`. -/
abbrev NoiseF (Ext : Mem 64 → Prop) (x : NArgs) (t : MachineData) (i : BitVec 32) :
    Mem 64 → Prop :=
  cell4 (arg1 t + 0x3c#64) x.cpl ⋆ (c4 (arg1 t + 0x4c1e8#64) x.nq
    ⋆ (c4 (arg3 t + 0x18#64) x.nn ⋆ (2 ?@ (arg3 t + 0x25#64) ⋆ (15 ?@ (arg3 t + 0x15a50#64)
    ⋆ (c8 (arg0 t + 8#64) x.avctx ⋆ (GbW (arg2 t) x.buf i x.p8 ⋆ (Blocks [(x.buf, x.L)]
    ⋆ (VlcW x.v ⋆ Ext))))))))

def NoiseC (x : NArgs) : Prop :=
  x.nn ≤ 2 ∧ x.nq ≤ 5 ∧ VlcC x.v
  ∧ x.idx.toNat ≤ x.p8.toNat ∧ x.p8.toNat < 2 ^ 31 ∧ x.p8.toNat / 8 + 4 ≤ x.L ∧ x.L < 2 ^ 32

/-- The stack: six pushes, `0x28` bytes of locals, the return slot of the `av_log` call, the
callee's `k`. -/
abbrev noiseNeed (k : Nat) : Nat := 0x60 + k

abbrev NoisePre (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t : MachineData) :
    Prop :=
  CallPre (noiseNeed k) (NoiseF Ext x t x.idx ⋆ x.R) ra t ∧ NoiseC x

/-- The return value is `0` or `AVERROR_INVALIDDATA`; the reader's `index` stays within
`size_in_bits_plus8`. -/
abbrev NoisePost (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t s : MachineData) :
    Prop :=
  ∃ i : BitVec 32, i.toNat ≤ x.p8.toNat
    ∧ ((s.regs.get64 .rax).setWidth 32 = 0#32 ∨ (s.regs.get64 .rax).setWidth 32 = 0xbebbb1b7#32)
    ∧ CallPost (noiseNeed k) (NoiseF Ext x t i ⋆ x.R) ra t s

abbrev NoiseSpec (k : Nat) (Ext : Mem 64 → Prop) : Prop :=
  cenv.ProcSpec (entry "read_sbr_noise") (NoisePre k Ext) (NoisePost k Ext)

end Kraken.Examples.Sbr.Noise
