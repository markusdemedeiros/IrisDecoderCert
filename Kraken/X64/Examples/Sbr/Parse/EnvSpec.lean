import Kraken.X64.Examples.Sbr.Parse.EnvText
import Kraken.X64.Examples.Sbr.Parse.EnvVlc

/-!
# `read_sbr_envelope`: the specification

`read_sbr_envelope(ac, sbr, gb, ch_data, ch)` (`libavcodec/aacsbr_template.c`, FFmpeg n8.1)
reads the envelope scale factors of one channel (`env_facs_q[1..bs_num_env]`, Huffman coded
in time or in frequency, `get_vlc2` inlined), the USAC `temp_shape`/`temp_shape_mode` flags,
and copies `env_facs_q[bs_num_env]` to `env_facs_q[0]`.

The model (`ParseModel.lean`, abstraction 6) gives the envelope reads no `Args` field and a
free outcome. So the specification is memory safety and the frame: the routine writes only
`env_facs_q`, `temp_shape`, `temp_shape_mode` (raw bytes here) and the reader's `index`, keeps
`index ≤ size_in_bits_plus8`, and returns `0` or `AVERROR_INVALIDDATA`. The grid fields it
reads (`bs_num_env`, `bs_freq_res`) are given back unchanged, so `DWF` and the border invariant
of the caller's values are kept.

* Logical variables `EArgs`: the caller's memory `R`; the channel values `v : DV`
  (`ApplySpec.lean`; `bs_num_env` and `bs_freq_res` are read); `sbr->n[0..1]`,
  `sbr->bs_coupling`, `ch_data->bs_amp_res`, `sbr->usac`, `sbr->inter_tes`; `ac->avctx`; the
  bit reader (`buffer`, `index`, `size_in_bits_plus8`, the `L` bytes the caller owns at
  `buffer`); the Huffman tables `vt` (`EnvVlc.lean`).
* Side conditions `EnvC`: `DWF False v` (so `bs_num_env ≤ 8` and `bs_freq_res[0..bs_num_env] ≤ 1`),
  `n[0] ≤ 24`, `n[1] ≤ 48` (`sbr_make_f_derived`'s bounds), the reader's bounds as for
  `read_sbr_grid`, the tables `VlcC`, and `ch_data` 32-byte aligned (the final copy uses
  `vmovaps`).
* Stop: `temp_shape[6]` is indexed by the envelope (with `usac` and `inter_tes` set); the
  compiled code's bounds check stops at the `ud1` for an index ≥ 6. That stop is an allowed
  outcome of the contract; every other trap is unreachable.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Vlc

namespace Kraken.Examples.Sbr.Env

structure EArgs where
  R : Mem 64 → Prop
  v : DV
  n0 : Nat
  n1 : Nat
  coupling : BitVec 32
  amp : BitVec 32
  usac : BitVec 32
  interTes : BitVec 32
  avctx : BitVec 64
  buf : BitVec 64
  idx : BitVec 32
  p8 : BitVec 32
  L : Nat
  vt : Nat → VlcTab

variable [CodeEnv]

/-- `*ch_data` at `d`: `bs_num_env`, `bs_freq_res[9]`, `bs_df_env[9]` (raw), `bs_amp_res`,
`env_facs_q[9][48]` (raw, written), `temp_shape[6]` with `temp_shape_mode[6]` (raw,
written). -/
def ChE (d : BitVec 64) (x : EArgs) : Mem 64 → Prop :=
  c4 (d + 8#64) x.v.nenv ⋆ (x.v.freqRes =@ (d + 0xc#64) ⋆ (9 ?@ (d + 0x1c#64)
    ⋆ (cell4 (d + 0x64#64) x.amp ⋆ (432 ?@ (d + 0x151e0#64) ⋆ 12 ?@ (d + 0x15ab4#64)))))

/-- `*sbr` at `s`: `usac`, `inter_tes`, `bs_coupling`, `n[0..1]` (read only). -/
def SbrE (s : BitVec 64) (x : EArgs) : Mem 64 → Prop :=
  cell4 (s + 0x10#64) x.usac ⋆ (cell4 (s + 0x14#64) x.interTes ⋆ (cell4 (s + 0x3c#64) x.coupling
    ⋆ (c4 (s + 0x4c1e0#64) x.n0 ⋆ c4 (s + 0x4c1e4#64) x.n1)))

/-- `*gb` at `g` with `index = i` (`size_in_bits` raw). -/
def GbE (g : BitVec 64) (x : EArgs) (i : BitVec 32) : Mem 64 → Prop :=
  c8 g x.buf ⋆ (cell4 (g + 8#64) i ⋆ (4 ?@ (g + 0xc#64) ⋆ cell4 (g + 0x10#64) x.p8))

/-- What is only read besides: `ac->avctx`, the bitstream bytes, the Huffman tables, and
`av_log`'s state `Ext`. -/
def InE (Ext : Mem 64 → Prop) (x : EArgs) (t : MachineData) : Mem 64 → Prop :=
  c8 (arg0 t + 8#64) x.avctx ⋆ (Blocks [(x.buf, x.L)] ⋆ (VlcW x.vt ⋆ Ext))

/-- The footprint, with the reader's index `i`. -/
abbrev EF (Ext : Mem 64 → Prop) (x : EArgs) (t : MachineData) (i : BitVec 32) :
    Mem 64 → Prop :=
  ChE (arg3 t) x ⋆ (SbrE (arg1 t) x ⋆ (GbE (arg2 t) x i ⋆ InE Ext x t))

/-- The side conditions. -/
def EnvC (x : EArgs) (t : MachineData) : Prop :=
  DWF False x.v ∧ x.n0 ≤ 24 ∧ x.n1 ≤ 48
  ∧ x.idx.toNat ≤ x.p8.toNat ∧ x.p8.toNat < 2 ^ 31 ∧ x.p8.toNat / 8 + 4 ≤ x.L ∧ x.L < 2 ^ 32
  ∧ VlcC x.vt ∧ (arg3 t).toNat % 32 = 0

/-- The stack: six pushes, the 0x78-byte frame, the return slot of the call, the callee's
`k`. -/
abbrev envNeed (k : Nat) : Nat := 0xb0 + k

abbrev EnvPre (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t : MachineData) :
    Prop :=
  CallPre (envNeed k) (EF Ext x t x.idx ⋆ x.R) ra t ∧ EnvC x t

/-- What a return leaves: the reader's index within `size_in_bits_plus8`, the result `0` or
`AVERROR_INVALIDDATA`. -/
def EnvOut (x : EArgs) (i : BitVec 32) (ret : BitVec 32) : Prop :=
  i.toNat ≤ x.p8.toNat ∧ (ret = 0#32 ∨ ret = 0xbebbb1b7#32)

abbrev EnvPost (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t s : MachineData) :
    Prop :=
  ∃ i, EnvOut x i ((s.regs.get64 .rax).setWidth 32)
    ∧ CallPost (envNeed k) (EF Ext x t i ⋆ x.R) ra t s

/-- The one allowed stop: the bounds trap (`ud1`) of `temp_shape[i]` for `i ≥ 6`, reached with
`usac` and `inter_tes` set and more than six envelopes. -/
abbrev envStops (a : Int64) : Prop :=
  a = (_root_.Executable.labels cenv).label "read_sbr_envelope.L60f9"

/-! ## Derived values -/

/-- `ch && sbr->bs_coupling`: the balance tables. -/
abbrev cpl (x : EArgs) (t : MachineData) : Prop :=
  (arg4 t).setWidth 32 ≠ 0#32 ∧ x.coupling ≠ 0#32

/-- The index of `t_huff` in `ff_aac_sbr_vlc` (`f_huff` is the next one). -/
abbrev kt (x : EArgs) (t : MachineData) : Nat :=
  if cpl x t then (if x.amp = 0#32 then 2 else 6) else (if x.amp = 0#32 then 0 else 4)

/-- `sbr->n[1] & 1`. -/
abbrev odd (x : EArgs) : Nat := x.n1 % 2

/-- `env_facs_q`. -/
abbrev EQ (t : MachineData) : BitVec 64 := arg3 t + 0x151e0#64

end Kraken.Examples.Sbr.Env
