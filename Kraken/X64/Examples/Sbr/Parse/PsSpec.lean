import Kraken.X64.Examples.Sbr.Parse.PsText
import Kraken.X64.Examples.Sbr.ApplySpec
import Kraken.X64.Examples.Sbr.SessionSpec

/-!
# `ff_ps_read_data`: the specification

`ff_ps_read_data(logctx, gb_host, ps, bits_left)` (`libavcodec/aacps_common.c`, FFmpeg n8.1)
parses one PS data block from the bit reader `*gb_host` into `ps` (a `PSCommonContext`, the
764 bytes `ps->common` of `PsWF`, see `Spec.lean`). It reads from a copy of the reader and
advances `*gb_host` once at the end (`skip_bits_long`) by the bits consumed, or by `bits_left`
on the error paths.

* Logical variables `PArgs`: the caller's memory `R`, the bytes `c` of `*ps`, the reader
  (`buffer`, `index`, `size_in_bits_plus8`, the bytes `[buffer, buffer + L)` the caller owns,
  as in `Grid.GArgs`), and the ten Huffman tables `vlc_ps[]` (`VlcTab`).
* The bitstream contents are not constrained; the reader's precondition is the one of
  `Grid.GridC`.
* Read only: the tables `num_env_tab`, `nr_iidicc_par_tab`, `nr_iidopd_par_tab`, `huff_iid`,
  `ff_log2_tab` (through its GOT slot, the label `ff_log2_tab_got`), the vector constants
  `LCPI0_28` and `LCPI0_30` (the fixed borders), and the Huffman tables with their pointer
  array `vlc_ps`.
* Postcondition, on every return: `PsWF`'s clauses on `ps->common` are kept (`PsWFb`, the row
  `psread_wf` of `ParseModel.lean`), the bounds `PsInv` that keep the array accesses inside
  their rows are kept, the reader's `index` stays within `size_in_bits_plus8`, and the result
  is in `[0, bits_left]`.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply

namespace Kraken.Examples.Sbr.Ps

/-! ## The Huffman tables

`vlc_ps[10]` holds pointers to ten `VLCElem` tables (`libavcodec/vlc.h`: `int16_t sym;
int16_t len;`, 4 bytes per entry), built by `ff_ps_init_common` with 9 index bits for the
tables `0..5` (`iid`, `icc`) and 5 for `6..9` (`ipd`, `opd`). The code inlines
`get_vlc2(gb, table, bits, max_depth)`: level 1 reads the entry at `show_bits(gb, bits)`; a
subtable entry (`len < 0`) sends the next window `w` to `(w >>> (len & 31)) + sym`. The table
contents are not constrained, except that every subtable index stays inside the table. -/

instance VWalk.dec (es : List UInt8) : ∀ d i, Decidable (VWalk es d i)
  | 0, _ => by unfold VWalk; exact inferInstance
  | d + 1, i => by
    unfold VWalk
    haveI := fun j => VWalk.dec es d j
    exact inferInstance

instance (nb d : Nat) (t : VlcTab) : Decidable (VlcOk nb d t) := by
  unfold VlcOk; exact inferInstance

variable [CodeEnv]

/-! ## The footprint -/

structure PArgs where
  R : Mem 64 → Prop
  c : List UInt8
  buf : BitVec 64
  idx : BitVec 32
  p8 : BitVec 32
  L : Nat
  v : Nat → VlcTab

/-- `*gb` at `g` with `index = i` (`size_in_bits` raw), as `Grid.GbW`. -/
abbrev GbW (g : BitVec 64) (x : PArgs) (i : BitVec 32) : Mem 64 → Prop :=
  Int.toBytes 8 x.buf.toInt =@ g ⋆ (cell4 (g + 8#64) i ⋆ (4 ?@ (g + 0xc#64)
    ⋆ cell4 (g + 0x10#64) x.p8))

/-- The footprint at the values `c` of `*ps` and the reader's `index` `i`: `*ps`, `*gb_host`,
the bitstream bytes, the read-only tables, and `av_log`'s state `Ext`. -/
abbrev PF (Ext : Mem 64 → Prop) (x : PArgs) (t : MachineData) (c : List UInt8) (i : BitVec 32) :
    Mem 64 → Prop :=
  c =@ arg2 t ⋆ (GbW (arg1 t) x i ⋆ (Blocks [(x.buf, x.L)] ⋆ (PsTabs x.v ⋆ Ext)))

/-! ## The invariants -/

/-- `PsWF`'s clauses on `ps->common` (`PsWF c h ↔ PsWFb c ∧` the clauses on `h`). -/
def PsWFb (c : List UInt8) : Prop :=
  c.length = 764
  ∧ (i32 c 756 = 0 ∨ i32 c 756 = 1)
  ∧ (0 ≤ i32 c 44 ∧ i32 c 44 ≤ 5) ∧ (0 ≤ i32 c 40 ∧ i32 c 40 ≤ 5)
  ∧ (i32 c 8 = 0 ∨ i32 c 8 = 1)
  ∧ (∀ e < 5, ∀ b < 34, 0 ≤ i8 c (246 + 34 * e + b) ∧ i8 c (246 + 34 * e + b) ≤ 7)
  ∧ (∀ e < 5, ∀ b < 34, 0 ≤ i8 c (416 + 34 * e + b) ∧ i8 c (416 + 34 * e + b) ≤ 7
      ∧ 0 ≤ i8 c (586 + 34 * e + b) ∧ i8 c (586 + 34 * e + b) ≤ 7)
  ∧ (i32 c 0 ≠ 0 →
      1 ≤ i32 c 44
      ∧ i32 c 52 = -1
      ∧ (∀ e : Nat, (e : Int) < i32 c 44 → i32 c (52 + 4 * e) ≤ i32 c (52 + 4 * (e + 1)))
      ∧ i32 c (52 + 4 * (i32 c 44).toNat) = 31
      ∧ (i32 c 4 ≠ 0 → i32 c 12 = 10 ∨ i32 c 12 = 20 ∨ i32 c 12 = 34)
      ∧ (∀ e : Nat, (e : Int) < i32 c 44 → ∀ b : Nat, b < 34 →
          (i32 c 4 = 0 ∨ (b : Int) < i32 c 12) →
          -(7 + 8 * i32 c 8) ≤ i8 c (76 + 34 * e + b)
            ∧ i8 c (76 + 34 * e + b) ≤ 7 + 8 * i32 c 8))

/-- `bits_left`, the low 32 bits of `rcx`. -/
abbrev bitsLeft (t : MachineData) : BitVec 32 := (arg3 t).setWidth 32

/-- The side conditions. -/
def PsC (x : PArgs) (t : MachineData) : Prop :=
  PsInv x.c ∧ VlcC x.v
  ∧ x.idx.toNat ≤ x.p8.toNat ∧ x.p8.toNat < 2 ^ 31 ∧ x.p8.toNat / 8 + 4 ≤ x.L ∧ x.L < 2 ^ 32
  ∧ 0 ≤ (bitsLeft t).toInt

/-- The stack: six pushes, `0x78` bytes of locals, the return slot of a call, the callee's
`k`. -/
abbrev psNeed (k : Nat) : Nat := 0xb0 + k

abbrev PsPre (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t : MachineData) :
    Prop :=
  CallPre (psNeed k) (PF Ext x t x.c x.idx ⋆ x.R) ra t ∧ PsC x t

/-- What a return leaves: `PsWFb` kept, `PsInv` kept, the reader's `index` within
`size_in_bits_plus8`, the result in `[0, bits_left]`. -/
def PsOut (x : PArgs) (t : MachineData) (c : List UInt8) (i : BitVec 32) (ret : BitVec 32) :
    Prop :=
  PsInv c ∧ (PsWFb x.c → PsWFb c)
  ∧ i.toNat ≤ x.p8.toNat
  ∧ 0 ≤ ret.toInt ∧ ret.toInt ≤ (bitsLeft t).toInt

abbrev PsPost (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t s : MachineData) :
    Prop :=
  ∃ c i, PsOut x t c i ((s.regs.get64 .rax).setWidth 32)
    ∧ CallPost (psNeed k) (PF Ext x t c i ⋆ x.R) ra t s

/-- The procedure's contract, given `av_log`'s and `memset`'s. -/
abbrev PsReadSpec (k : Nat) (Ext : Mem 64 → Prop) : Prop :=
  cenv.ProcSpec (entry "ff_ps_read_data") (PsPre k Ext) (PsPost k Ext)

/-- `PsWF` is `PsWFb` with the clauses on the phase histories. -/
theorem psWF_iff (c h : List UInt8) :
    PsWF c h ↔ PsWFb c ∧ h.length = 68
      ∧ (∀ b < 34, 0 ≤ i8 h b ∧ i8 h b ≤ 63 ∧ 0 ≤ i8 h (34 + b) ∧ i8 h (34 + b) ≤ 63) := by
  unfold PsWF PsWFb
  constructor
  · rintro ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩
    exact ⟨⟨a1, a3, a4, a5, a6, a7, a8, a10⟩, a2, a9⟩
  · rintro ⟨⟨a1, a3, a4, a5, a6, a7, a8, a10⟩, a2, a9⟩
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩

end Kraken.Examples.Sbr.Ps
