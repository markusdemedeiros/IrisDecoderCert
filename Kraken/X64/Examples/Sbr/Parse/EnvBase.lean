import Kraken.X64.Examples.Sbr.Parse.EnvSpec
import Kraken.X64.Examples.Sbr.Parse.EnvLib

/-!
# `read_sbr_envelope`: the block table

The memory at every label after the prologue is `T`: the six saved registers, the 0x78-byte
frame as cells (`FrW`, values `FV`; the slots whose values are never needed are raw), the
call slot and the callee's reservation, the footprint `EF` with the reader's index, the return
address and the caller's rest.

The frame slots (offsets from `rbp = rsp₀ - 8`): `-0x98` `f_huff`, `-0x90` `96 - odd`, `-0x88`
`odd`, `-0x80` `&env_facs_q[i][0]` (low-resolution path), `-0x78` `sbr`, `-0x70` `bits` (raw),
`-0x6c` `2 - odd`, `-0x68` `i`, `-0x60` `&env_facs_q[i + 1][1]`, `-0x58` `&env_facs_q[i + 1][0]`,
`-0x50` `ac`, `-0x48` `i + 1`, `-0x40` `&sbr->n[0]`, `-0x38` `ch_data`, `-0x30..-0x29` `-bits`
and `delta` (raw), `-0xa0` unused (raw).

The Huffman walks (five copies of the inlined `get_vlc2`) have the states `WIdx` (the reader's
index in a register, at most `size_in_bits_plus8`, and `size_in_bits_plus8` in another) and
`WEnt` (a subtable entry of the table: `sym` and `len` sign-extended in two registers, `len < 0`).

The variant: the envelope `i` (read from its frame slot `-0x68`, `fi`) dominates; inside the
four inner loops the band counter breaks ties.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Vlc

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.Env

/-- The frame values. -/
structure FV where
  f98 : BitVec 64
  f90 : BitVec 64
  f88 : BitVec 64
  f80 : BitVec 64
  f78 : BitVec 64
  f6c : BitVec 32
  f68 : BitVec 64
  f60 : BitVec 64
  f58 : BitVec 64
  f50 : BitVec 64
  f48 : BitVec 64
  f40 : BitVec 64
  f38 : BitVec 64

variable [CodeEnv]

/-- The frame below the saved registers (`r` the entry `rsp`). -/
def FrW (r : BitVec 64) (fv : FV) : Mem 64 → Prop :=
  8 ?@ (r - 0xa8#64) ⋆ (c8 (r - 0xa0#64) fv.f98 ⋆ (c8 (r - 0x98#64) fv.f90
    ⋆ (c8 (r - 0x90#64) fv.f88 ⋆ (c8 (r - 0x88#64) fv.f80 ⋆ (c8 (r - 0x80#64) fv.f78
    ⋆ (4 ?@ (r - 0x78#64) ⋆ (cell4 (r - 0x74#64) fv.f6c ⋆ (c8 (r - 0x70#64) fv.f68
    ⋆ (c8 (r - 0x68#64) fv.f60 ⋆ (c8 (r - 0x60#64) fv.f58 ⋆ (c8 (r - 0x58#64) fv.f50
    ⋆ (c8 (r - 0x50#64) fv.f48 ⋆ (c8 (r - 0x48#64) fv.f40 ⋆ (c8 (r - 0x40#64) fv.f38
    ⋆ 8 ?@ (r - 0x38#64)))))))))))))))

/-- The six pushed registers. -/
def Sv (t₀ : MachineData) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  c8 (r - 8#64) (t₀.regs.get64 .rbp) ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14) ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12) ⋆ c8 (r - 0x30#64) (t₀.regs.get64 .rbx)))))

def Rest (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) : Mem 64 → Prop :=
  RetCell ra (t₀.regs.get64 .rsp) ⋆ R

/-- The memory at every label after the prologue. -/
def T (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) (fv : FV)
    (i : BitVec 32) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  Sv t₀ ⋆ (FrW r fv ⋆ (8 ?@ (r - 0xb0#64) ⋆ (Reserve k (r - 0xb0#64)
    ⋆ (EF Ext x t₀ i ⋆ Rest x.R ra t₀))))

/-- The frame values that are fixed after the setup at `.L5893`. -/
def FrC (x : EArgs) (t₀ : MachineData) (fv : FV) : Prop :=
  fv.f98 = (x.vt (kt x t₀ + 1)).p ∧ fv.f90 = BitVec.ofNat 64 (96 - odd x)
  ∧ fv.f88 = BitVec.ofNat 64 (odd x) ∧ fv.f78 = arg1 t₀ ∧ fv.f6c = BitVec.ofNat 32 (2 - odd x)
  ∧ fv.f50 = arg0 t₀ ∧ fv.f40 = arg1 t₀ + 0x4c1e0#64 ∧ fv.f38 = arg3 t₀

/-- The row pointers of envelope `i`. -/
def LI (x : EArgs) (t₀ : MachineData) (fv : FV) (i : Nat) : Prop :=
  i < x.v.nenv ∧ fv.f58 = EQ t₀ + BitVec.ofNat 64 (48 * (i + 1))
  ∧ fv.f60 = EQ t₀ + BitVec.ofNat 64 (48 * (i + 1) + 1)

/-- The common part: side conditions, `rsp`, `rbp`, the reader's index, the memory. -/
def Cm (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ s : MachineData) (fv : FV)
    (i : BitVec 32) : Prop :=
  EnvC x t₀ ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0xa8#64
  ∧ s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64
  ∧ i.toNat ≤ x.p8.toNat ∧ (s.dmem =⋆ T k Ext x ra t₀ fv i)

/-- `Cm` with `gb` in `rdx`. -/
abbrev Cd (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ s : MachineData) (fv : FV)
    (i : BitVec 32) : Prop :=
  Cm k Ext x ra t₀ s fv i ∧ s.regs.get64 .rdx = arg2 t₀

/-- `Cd` after the frame setup, inside envelope `i` (`i` in its slot), with `t_huff` in
`r13`. -/
def Lp (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ s : MachineData) (fv : FV)
    (gi : BitVec 32) (i : Nat) : Prop :=
  Cd k Ext x ra t₀ s fv gi ∧ FrC x t₀ fv ∧ LI x t₀ fv i ∧ fv.f68 = BitVec.ofNat 64 i
  ∧ s.regs.get64 .r13 = (x.vt (kt x t₀)).p

/-- `&sbr->n[0]` in `r12`. -/
abbrev R12 (t₀ s : MachineData) : Prop := s.regs.get64 .r12 = arg1 t₀ + 0x4c1e0#64

/-- A walk register state: the index in `ri` (low 32 bits) within `size_in_bits_plus8`, which
is in `rp` (low 32 bits). -/
abbrev WIdx (x : EArgs) (s : MachineData) (ri rp : Reg64) : Prop :=
  ((s.regs.get64 ri).setWidth 32).toNat ≤ x.p8.toNat ∧ (s.regs.get64 rp).setWidth 32 = x.p8

/-- A subtable entry of `t` with a walk of `d + 1` levels from it: `sym` in `rs`, `len < 0`
in `rl` (low 32 bits, sign-extended). -/
abbrev WEnt (t : VlcTab) (d : Nat) (s : MachineData) (rs rl : Reg64) : Prop :=
  ∃ e, VWalk t.es (d + 1) e ∧ (s.regs.get64 rs).setWidth 32 = (vsym t.es e).signExtend 32
    ∧ (s.regs.get64 rl).setWidth 32 = (vlen t.es e).signExtend 32 ∧ (vlen t.es e).msb = true

/-- A walk at level 2 (`d = 2`) or 3 (`d = 1`): index/limit registers, buffer and table
registers, an entry. -/
abbrev WL (x : EArgs) (t : VlcTab) (d : Nat) (s : MachineData) (ri rp rb rt rs rl : Reg64) :
    Prop :=
  WIdx x s ri rp ∧ s.regs.get64 rb = x.buf ∧ s.regs.get64 rt = t.p ∧ WEnt t d s rs rl

/-- `t_huff`, `f_huff`. -/
abbrev tH (x : EArgs) (t₀ : MachineData) : VlcTab := x.vt (kt x t₀)
abbrev fH (x : EArgs) (t₀ : MachineData) : VlcTab := x.vt (kt x t₀ + 1)

/-- `bs_freq_res[e]` as a register value. -/
abbrev fr (x : EArgs) (e : Nat) : BitVec 64 := BitVec.ofNat 64 (u8 x.v.freqRes e)

/-- `sbr->n[bs_freq_res[e]]`. -/
abbrev nf (x : EArgs) (e : Nat) : Nat := if u8 x.v.freqRes e = 0 then x.n0 else x.n1

/-- Copy A (`.L5940`, time delta, same resolution): `j` in `rsi`, `i + 1` in its slot. -/
abbrev JA (s : MachineData) (fv : FV) (i j : Nat) : Prop :=
  fv.f48 = BitVec.ofNat 64 (i + 1) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 j ∧ j < 48

/-- Copy B (`.L5ad0`, frequency delta): band `j + 1` with `j` in `r9`, `i + 1` in `rbx`. -/
abbrev JB (x : EArgs) (s : MachineData) (i j : Nat) : Prop :=
  s.regs.get64 .rbx = BitVec.ofNat 64 (i + 1) ∧ s.regs.get64 .r9 = BitVec.ofNat 64 j
  ∧ s.regs.get64 .r14 = BitVec.ofNat 64 (j + 1) ∧ j + 1 < nf x (i + 1)

/-- The low-resolution path (`bs_freq_res[i + 1] = 0`): `&env_facs_q[i][0]` in its slot. -/
abbrev JD (x : EArgs) (t₀ : MachineData) (fv : FV) (i : Nat) : Prop :=
  fv.f48 = BitVec.ofNat 64 (i + 1) ∧ u8 x.v.freqRes (i + 1) = 0
  ∧ fv.f80 = EQ t₀ + BitVec.ofNat 64 (48 * i) ∧ 0 < x.n0

/-- Copy D (`.L5e70`): band `j + 1` with `j` in `r9`, `k = 2 (j + 1) - odd` in `rsi`. -/
abbrev JD' (x : EArgs) (s : MachineData) (j : Nat) : Prop :=
  s.regs.get64 .r9 = BitVec.ofNat 64 j ∧ s.regs.get64 .r14 = BitVec.ofNat 64 (j + 1)
  ∧ j + 1 < x.n0 ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (2 * (j + 1) - odd x)

/-- Copy C (`.L5cd0`, high resolution after low): `&env_facs_q[i][0]` in `r15`, `j` in `rsi`. -/
abbrev JC (x : EArgs) (t₀ : MachineData) (s : MachineData) (fv : FV) (i j : Nat) : Prop :=
  fv.f48 = BitVec.ofNat 64 (i + 1) ∧ u8 x.v.freqRes (i + 1) = 1
  ∧ s.regs.get64 .r15 = EQ t₀ + BitVec.ofNat 64 (48 * i) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 j

/-- The result register at the return: `0` or `AVERROR_INVALIDDATA`. -/
abbrev RetV (s : MachineData) : Prop :=
  (s.regs.get64 .rax).setWidth 32 = 0#32 ∨ (s.regs.get64 .rax).setWidth 32 = 0xbebbb1b7#32

/-- The assertions at the labels. -/
def table (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    Label → MachineData → Prop
  | "read_sbr_envelope", s => s = t₀ ∧ EnvC x t₀
      ∧ (t₀.dmem =⋆ RetCell ra (t₀.regs.get64 .rsp)
          ⋆ (Reserve (envNeed k) (t₀.regs.get64 .rsp) ⋆ (EF Ext x t₀ x.idx ⋆ x.R)))
  -- after the prologue
  | "read_sbr_envelope.L57c1", s => ∃ fv, Cd k Ext x ra t₀ s fv x.idx
      ∧ s.regs.get64 .rdi = arg0 t₀ ∧ s.regs.get64 .rsi = arg1 t₀ ∧ s.regs.get64 .rcx = arg3 t₀
      ∧ s.regs.get64 .r8 = arg4 t₀
  | "read_sbr_envelope.L57c9", s => ∃ fv, Cd k Ext x ra t₀ s fv x.idx
      ∧ s.regs.get64 .rdi = arg0 t₀ ∧ s.regs.get64 .rsi = arg1 t₀ ∧ s.regs.get64 .r15 = arg3 t₀
      ∧ (arg4 t₀).setWidth 32 ≠ 0#32
  | "read_sbr_envelope.L57ef", s => ∃ fv, Cd k Ext x ra t₀ s fv x.idx
      ∧ s.regs.get64 .rdi = arg0 t₀ ∧ s.regs.get64 .rsi = arg1 t₀ ∧ s.regs.get64 .r15 = arg3 t₀
      ∧ cpl x t₀ ∧ R12 t₀ s ∧ s.regs.get64 .r14 = BitVec.ofNat 64 (odd x)
  | "read_sbr_envelope.L5834", s => ∃ fv, Cd k Ext x ra t₀ s fv x.idx
      ∧ s.regs.get64 .rdi = arg0 t₀ ∧ s.regs.get64 .rsi = arg1 t₀ ∧ s.regs.get64 .r15 = arg3 t₀
      ∧ (arg4 t₀).setWidth 32 = 0#32
  | "read_sbr_envelope.L584c", s => ∃ fv, Cd k Ext x ra t₀ s fv x.idx
      ∧ s.regs.get64 .rdi = arg0 t₀ ∧ s.regs.get64 .rsi = arg1 t₀ ∧ s.regs.get64 .r15 = arg3 t₀
      ∧ ¬ cpl x t₀ ∧ R12 t₀ s ∧ s.regs.get64 .r14 = BitVec.ofNat 64 (odd x)
  -- the frame setup
  | "read_sbr_envelope.L5893", s => ∃ fv, Cd k Ext x ra t₀ s fv x.idx
      ∧ s.regs.get64 .rdi = arg0 t₀ ∧ s.regs.get64 .rsi = arg1 t₀ ∧ s.regs.get64 .r15 = arg3 t₀
      ∧ R12 t₀ s ∧ s.regs.get64 .r14 = BitVec.ofNat 64 (odd x)
      ∧ s.regs.get64 .rcx = VA + BitVec.ofNat 64 (8 * kt x t₀)
      ∧ s.regs.get64 .r9 = VA + BitVec.ofNat 64 (8 * (kt x t₀ + 1)) ∧ 0 < x.v.nenv
  | "read_sbr_envelope.L58a4", s => ∃ fv, Cd k Ext x ra t₀ s fv x.idx
      ∧ s.regs.get64 .rsi = arg1 t₀ ∧ s.regs.get64 .r15 = arg3 t₀
      ∧ R12 t₀ s ∧ s.regs.get64 .r14 = BitVec.ofNat 64 (odd x)
      ∧ s.regs.get64 .r13 = (tH x t₀).p ∧ 0 < x.v.nenv
      ∧ fv.f50 = arg0 t₀ ∧ fv.f98 = (fH x t₀).p
  | "read_sbr_envelope.L58c5", s => ∃ fv, Cd k Ext x ra t₀ s fv x.idx
      ∧ s.regs.get64 .rsi = arg1 t₀ ∧ s.regs.get64 .r15 = arg3 t₀
      ∧ R12 t₀ s ∧ s.regs.get64 .r14 = BitVec.ofNat 64 (odd x)
      ∧ s.regs.get64 .r13 = (tH x t₀).p ∧ 0 < x.v.nenv
      ∧ fv.f50 = arg0 t₀ ∧ fv.f98 = (fH x t₀).p
      ∧ fv.f90 = BitVec.ofNat 64 (96 - odd x) ∧ fv.f88 = BitVec.ofNat 64 (odd x)
  | "read_sbr_envelope.L58e6", s => ∃ fv, Cd k Ext x ra t₀ s fv x.idx
      ∧ s.regs.get64 .rsi = arg1 t₀ ∧ s.regs.get64 .r15 = arg3 t₀
      ∧ R12 t₀ s ∧ s.regs.get64 .r13 = (tH x t₀).p
      ∧ fv.f50 = arg0 t₀ ∧ fv.f98 = (fH x t₀).p
      ∧ fv.f90 = BitVec.ofNat 64 (96 - odd x) ∧ fv.f88 = BitVec.ofNat 64 (odd x)
      ∧ fv.f6c = BitVec.ofNat 32 (2 - odd x) ∧ LI x t₀ fv 0
  | "read_sbr_envelope.L58f1", s => ∃ fv, Cd k Ext x ra t₀ s fv x.idx
      ∧ s.regs.get64 .r15 = arg3 t₀ ∧ s.regs.get64 .r9 = 0#64
      ∧ R12 t₀ s ∧ s.regs.get64 .r13 = (tH x t₀).p
      ∧ fv.f50 = arg0 t₀ ∧ fv.f98 = (fH x t₀).p
      ∧ fv.f90 = BitVec.ofNat 64 (96 - odd x) ∧ fv.f88 = BitVec.ofNat 64 (odd x)
      ∧ fv.f6c = BitVec.ofNat 32 (2 - odd x) ∧ LI x t₀ fv 0 ∧ fv.f78 = arg1 t₀
  -- the envelope loop
  | "read_sbr_envelope.L58fd", s => ∃ fv gi i, Cd k Ext x ra t₀ s fv gi ∧ FrC x t₀ fv
      ∧ LI x t₀ fv i ∧ s.regs.get64 .r9 = BitVec.ofNat 64 i ∧ s.regs.get64 .r15 = arg3 t₀
      ∧ s.regs.get64 .r13 = (tH x t₀).p ∧ R12 t₀ s
  | "read_sbr_envelope.L590d", s => ∃ fv gi i, Lp k Ext x ra t₀ s fv gi i ∧ R12 t₀ s
      ∧ s.regs.get64 .r9 = BitVec.ofNat 64 i ∧ s.regs.get64 .r15 = arg3 t₀
  | "read_sbr_envelope.L5930", s => ∃ fv gi i, Lp k Ext x ra t₀ s fv gi i ∧ R12 t₀ s
      ∧ fv.f48 = BitVec.ofNat 64 (i + 1) ∧ s.regs.get64 .rax = fr x (i + 1)
  -- copy A: time delta, same resolution
  | "read_sbr_envelope.L5940", s => ∃ fv gi i j, Lp k Ext x ra t₀ s fv gi i ∧ R12 t₀ s
      ∧ fv.f48 = BitVec.ofNat 64 (i + 1) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 j ∧ j ≤ 48
      ∧ s.regs.get64 .rax = fr x (i + 1)
  | "read_sbr_envelope.L595a", s => ∃ fv gi i j, Lp k Ext x ra t₀ s fv gi i ∧ R12 t₀ s
      ∧ JA s fv i j
  | "read_sbr_envelope.L5998", s => ∃ fv gi i j, Lp k Ext x ra t₀ s fv gi i ∧ R12 t₀ s
      ∧ JA s fv i j ∧ WL x (tH x t₀) 2 s .r14 .rdi .r8 .r13 .rax .r10
  | "read_sbr_envelope.L59d8", s => ∃ fv gi i j, Lp k Ext x ra t₀ s fv gi i ∧ R12 t₀ s
      ∧ JA s fv i j ∧ WL x (tH x t₀) 1 s .r14 .rdi .r8 .r13 .rax .r11
  | "read_sbr_envelope.L5a0d", s => ∃ fv gi i j, Lp k Ext x ra t₀ s fv gi i ∧ R12 t₀ s
      ∧ JA s fv i j ∧ WIdx x s .r14 .rdi
  | "read_sbr_envelope.L5a11", s => ∃ fv gi i j, Lp k Ext x ra t₀ s fv gi i ∧ R12 t₀ s
      ∧ JA s fv i j ∧ WIdx x s .r14 .rdi
  | "read_sbr_envelope.L5a38", s => ∃ fv gi i j, Lp k Ext x ra t₀ s fv gi i ∧ R12 t₀ s
      ∧ JA s fv i j ∧ s.regs.get64 .rcx = arg3 t₀
  -- frequency delta
  | "read_sbr_envelope.L5a60", s => ∃ fv gi i, Lp k Ext x ra t₀ s fv gi i ∧ R12 t₀ s
      ∧ s.regs.get64 .r9 = BitVec.ofNat 64 i ∧ s.regs.get64 .r15 = arg3 t₀
  | "read_sbr_envelope.L5a95", s => ∃ fv gi i, Lp k Ext x ra t₀ s fv gi i ∧ R12 t₀ s
      ∧ s.regs.get64 .r9 = BitVec.ofNat 64 i ∧ s.regs.get64 .r15 = arg3 t₀
  -- copy B
  | "read_sbr_envelope.L5ad0", s => ∃ fv gi i j, Lp k Ext x ra t₀ s fv gi i ∧ R12 t₀ s
      ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (i + 1) ∧ s.regs.get64 .r9 = BitVec.ofNat 64 j
      ∧ j ≤ 47 ∧ s.regs.get64 .rax = fr x (i + 1)
  | "read_sbr_envelope.L5ae4", s => ∃ fv gi i j, Lp k Ext x ra t₀ s fv gi i ∧ R12 t₀ s
      ∧ JB x s i j
  | "read_sbr_envelope.L5b25", s => ∃ fv gi i j, Lp k Ext x ra t₀ s fv gi i
      ∧ JB x s i j ∧ WL x (fH x t₀) 2 s .rdi .r8 .r12 .rsi .rax .r10
  | "read_sbr_envelope.L5b61", s => ∃ fv gi i j, Lp k Ext x ra t₀ s fv gi i
      ∧ JB x s i j ∧ WL x (fH x t₀) 1 s .rdi .r8 .r12 .rsi .rax .r11
  | "read_sbr_envelope.L5b93", s => ∃ fv gi i j, Lp k Ext x ra t₀ s fv gi i
      ∧ JB x s i j ∧ WIdx x s .rdi .r8
  | "read_sbr_envelope.L5b97", s => ∃ fv gi i j, Lp k Ext x ra t₀ s fv gi i
      ∧ JB x s i j ∧ WIdx x s .rdi .r8
  | "read_sbr_envelope.L5bc7", s => ∃ fv gi i j, Lp k Ext x ra t₀ s fv gi i ∧ R12 t₀ s
      ∧ JB x s i j
  -- time delta, different resolutions
  | "read_sbr_envelope.L5be0", s => ∃ fv gi i, Lp k Ext x ra t₀ s fv gi i ∧ R12 t₀ s
      ∧ fv.f48 = BitVec.ofNat 64 (i + 1) ∧ s.regs.get64 .rax = fr x (i + 1)
  | "read_sbr_envelope.L5bf6", s => ∃ fv gi i, Lp k Ext x ra t₀ s fv gi i ∧ R12 t₀ s
      ∧ fv.f48 = BitVec.ofNat 64 (i + 1) ∧ u8 x.v.freqRes (i + 1) = 0 ∧ 0 < x.n0
  | "read_sbr_envelope.L5c26", s => ∃ fv gi i, Lp k Ext x ra t₀ s fv gi i ∧ R12 t₀ s
      ∧ JD x t₀ fv i ∧ s.regs.get64 .rsi = EQ t₀ + BitVec.ofNat 64 (48 * (i + 1))
  | "read_sbr_envelope.L5c5e", s => ∃ fv gi i, Lp k Ext x ra t₀ s fv gi i ∧ R12 t₀ s
      ∧ JD x t₀ fv i ∧ s.regs.get64 .rsi = EQ t₀ + BitVec.ofNat 64 (48 * (i + 1))
      ∧ WL x (tH x t₀) 2 s .r9 .rdi .r8 .r13 .rax .r10
  | "read_sbr_envelope.L5ca5", s => ∃ fv gi i, Lp k Ext x ra t₀ s fv gi i ∧ R12 t₀ s
      ∧ fv.f48 = BitVec.ofNat 64 (i + 1) ∧ s.regs.get64 .rax = fr x (i + 1)
      ∧ u8 x.v.freqRes (i + 1) ≠ 0
  -- copy C: high resolution after low
  | "read_sbr_envelope.L5cd0", s => ∃ fv gi i j, Lp k Ext x ra t₀ s fv gi i ∧ R12 t₀ s
      ∧ JC x t₀ s fv i j ∧ j ≤ 48 ∧ (s.regs.get64 .rax).setWidth 8 = 1#8
  | "read_sbr_envelope.L5ced", s => ∃ fv gi i j, Lp k Ext x ra t₀ s fv gi i ∧ R12 t₀ s
      ∧ JC x t₀ s fv i j ∧ j < x.n1
  | "read_sbr_envelope.L5cfd", s => ∃ fv gi i j, Lp k Ext x ra t₀ s fv gi i ∧ R12 t₀ s
      ∧ JC x t₀ s fv i j ∧ j < x.n1
  | "read_sbr_envelope.L5d35", s => ∃ fv gi i j, Lp k Ext x ra t₀ s fv gi i ∧ R12 t₀ s
      ∧ JC x t₀ s fv i j ∧ j < x.n1 ∧ WL x (tH x t₀) 2 s .r14 .rdi .rax .r13 .r8 .r10
  | "read_sbr_envelope.L5d75", s => ∃ fv gi i j, Lp k Ext x ra t₀ s fv gi i ∧ R12 t₀ s
      ∧ JC x t₀ s fv i j ∧ j < x.n1 ∧ WL x (tH x t₀) 1 s .r14 .rdi .rax .r13 .r8 .r11
  | "read_sbr_envelope.L5da6", s => ∃ fv gi i j, Lp k Ext x ra t₀ s fv gi i ∧ R12 t₀ s
      ∧ JC x t₀ s fv i j ∧ j < x.n1 ∧ WIdx x s .r14 .rdi
  | "read_sbr_envelope.L5daa", s => ∃ fv gi i j, Lp k Ext x ra t₀ s fv gi i ∧ R12 t₀ s
      ∧ JC x t₀ s fv i j ∧ j < x.n1 ∧ WIdx x s .r14 .rdi
  | "read_sbr_envelope.L5dd7", s => ∃ fv gi i j, Lp k Ext x ra t₀ s fv gi i ∧ R12 t₀ s
      ∧ JC x t₀ s fv i j ∧ j < x.n1
  -- the first band of the low-resolution path
  | "read_sbr_envelope.L5df4", s => ∃ fv gi i, Lp k Ext x ra t₀ s fv gi i ∧ R12 t₀ s
      ∧ JD x t₀ fv i ∧ s.regs.get64 .rsi = EQ t₀ + BitVec.ofNat 64 (48 * (i + 1))
      ∧ WL x (tH x t₀) 1 s .r9 .rdi .r8 .r13 .rax .r11
  | "read_sbr_envelope.L5e29", s => ∃ fv gi i, Lp k Ext x ra t₀ s fv gi i ∧ R12 t₀ s
      ∧ JD x t₀ fv i ∧ s.regs.get64 .rsi = EQ t₀ + BitVec.ofNat 64 (48 * (i + 1))
      ∧ WIdx x s .r9 .rdi
  | "read_sbr_envelope.L5e2d", s => ∃ fv gi i, Lp k Ext x ra t₀ s fv gi i ∧ R12 t₀ s
      ∧ JD x t₀ fv i ∧ s.regs.get64 .rsi = EQ t₀ + BitVec.ofNat 64 (48 * (i + 1))
      ∧ WIdx x s .r9 .rdi
  | "read_sbr_envelope.L5e4b", s => ∃ fv gi i, Lp k Ext x ra t₀ s fv gi i ∧ R12 t₀ s
      ∧ JD x t₀ fv i
  -- copy D: low resolution
  | "read_sbr_envelope.L5e70", s => ∃ fv gi i j, Lp k Ext x ra t₀ s fv gi i ∧ R12 t₀ s
      ∧ JD x t₀ fv i ∧ s.regs.get64 .r9 = BitVec.ofNat 64 j ∧ j ≤ 23
      ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (2 * (j + 1) - odd x) ∧ s.regs.get64 .rax = 0#64
  | "read_sbr_envelope.L5e8d", s => ∃ fv gi i j, Lp k Ext x ra t₀ s fv gi i ∧ R12 t₀ s
      ∧ JD x t₀ fv i ∧ JD' x s j
  | "read_sbr_envelope.L5eca", s => ∃ fv gi i j, Lp k Ext x ra t₀ s fv gi i
      ∧ JD x t₀ fv i ∧ JD' x s j ∧ WL x (tH x t₀) 2 s .rdi .r8 .r12 .r13 .rax .r10
  | "read_sbr_envelope.L5f07", s => ∃ fv gi i j, Lp k Ext x ra t₀ s fv gi i
      ∧ JD x t₀ fv i ∧ JD' x s j ∧ WL x (tH x t₀) 1 s .rdi .r8 .r12 .r13 .rax .r11
  | "read_sbr_envelope.L5f3a", s => ∃ fv gi i j, Lp k Ext x ra t₀ s fv gi i
      ∧ JD x t₀ fv i ∧ JD' x s j ∧ WIdx x s .rdi .r8
  | "read_sbr_envelope.L5f3e", s => ∃ fv gi i j, Lp k Ext x ra t₀ s fv gi i
      ∧ JD x t₀ fv i ∧ JD' x s j ∧ WIdx x s .rdi .r8
  | "read_sbr_envelope.L5f6e", s => ∃ fv gi i j, Lp k Ext x ra t₀ s fv gi i ∧ R12 t₀ s
      ∧ JD x t₀ fv i ∧ JD' x s j
  -- the end of envelope `i`: the USAC flags, the loop step
  | "read_sbr_envelope.L5f90", s => ∃ fv gi i, Lp k Ext x ra t₀ s fv gi i ∧ R12 t₀ s
  | "read_sbr_envelope.L5fac", s => ∃ fv gi i, Lp k Ext x ra t₀ s fv gi i ∧ R12 t₀ s
      ∧ s.regs.get64 .r9 = BitVec.ofNat 64 i ∧ s.regs.get64 .r15 = arg3 t₀
      ∧ x.usac ≠ 0#32 ∧ x.interTes ≠ 0#32
  | "read_sbr_envelope.L5fdd", s => ∃ fv gi i, Lp k Ext x ra t₀ s fv gi i ∧ R12 t₀ s
      ∧ s.regs.get64 .r9 = BitVec.ofNat 64 i ∧ s.regs.get64 .r15 = arg3 t₀ ∧ i < 6
  | "read_sbr_envelope.L5fe9", s => ∃ fv gi i, Lp k Ext x ra t₀ s fv gi i ∧ R12 t₀ s
      ∧ s.regs.get64 .r9 = BitVec.ofNat 64 i ∧ s.regs.get64 .r15 = arg3 t₀ ∧ i < 6
  | "read_sbr_envelope.L6019", s => ∃ fv gi i, Lp k Ext x ra t₀ s fv gi i ∧ R12 t₀ s
      ∧ s.regs.get64 .r9 = BitVec.ofNat 64 i ∧ s.regs.get64 .r15 = arg3 t₀
  -- the error return
  | "read_sbr_envelope.L603e", s => ∃ fv gi, Cm k Ext x ra t₀ s fv gi ∧ fv.f50 = arg0 t₀
  | "read_sbr_envelope.L6044", s => ∃ fv gi, Cm k Ext x ra t₀ s fv gi ∧ fv.f50 = arg0 t₀
  | "read_sbr_envelope.L6048", s => ∃ fv gi, Cm k Ext x ra t₀ s fv gi ∧ fv.f50 = arg0 t₀
  | "read_sbr_envelope.L6063", s => ∃ fv gi, Cm k Ext x ra t₀ s fv gi
  -- the copy of `env_facs_q[bs_num_env]`
  | "read_sbr_envelope.L606a", s => ∃ fv gi, Cm k Ext x ra t₀ s fv gi
      ∧ s.regs.get64 .r8 = BitVec.ofNat 64 x.v.nenv ∧ s.regs.get64 .r15 = arg3 t₀
  | "read_sbr_envelope.L6075", s => ∃ fv gi, Cm k Ext x ra t₀ s fv gi
      ∧ s.regs.get64 .r8 = BitVec.ofNat 64 x.v.nenv ∧ s.regs.get64 .r15 = arg3 t₀
      ∧ s.regs.get64 .rax = 0#64
  -- the epilogue
  | "read_sbr_envelope.L60a6", s => ∃ fv gi, Cm k Ext x ra t₀ s fv gi ∧ RetV s
  | "read_sbr_envelope.done", s => s.regs.get64 .rsp = t₀.regs.get64 .rsp
      ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp ∧ SavedRegs t₀ s ∧ RetV s
      ∧ ∃ fv gi, gi.toNat ≤ x.p8.toNat ∧ (s.dmem =⋆ T k Ext x ra t₀ fv gi)
  | _, _ => False

/-- The envelope counter in its frame slot (`rbp - 0x68`). -/
def fi (s : MachineData) : Nat :=
  (BitVec.ofInt 64 ((s.dmem.loadInt (s.regs.get64 .rbp - 0x68#64) 8).getD 0)).toNat

/-- The variant. -/
def var : Label → MachineData → Nat
  | "read_sbr_envelope", _ | "read_sbr_envelope.L57c1", _ | "read_sbr_envelope.L57c9", _
  | "read_sbr_envelope.L57ef", _ | "read_sbr_envelope.L5834", _ | "read_sbr_envelope.L584c", _
  | "read_sbr_envelope.L5893", _ | "read_sbr_envelope.L58a4", _ | "read_sbr_envelope.L58c5", _
  | "read_sbr_envelope.L58e6", _ | "read_sbr_envelope.L58f1", _ => 5000
  | "read_sbr_envelope.L58fd", s => 100 * (10 - (s.regs.get64 .r9).toNat) + 99
  | "read_sbr_envelope.L590d", s | "read_sbr_envelope.L5930", s | "read_sbr_envelope.L5a60", s
  | "read_sbr_envelope.L5a95", s | "read_sbr_envelope.L5be0", s | "read_sbr_envelope.L5bf6", s
  | "read_sbr_envelope.L5c26", s | "read_sbr_envelope.L5c5e", s | "read_sbr_envelope.L5ca5", s
  | "read_sbr_envelope.L5df4", s | "read_sbr_envelope.L5e29", s | "read_sbr_envelope.L5e2d", s
  | "read_sbr_envelope.L5e4b", s => 100 * (10 - fi s) + 99
  | "read_sbr_envelope.L5940", s | "read_sbr_envelope.L595a", s | "read_sbr_envelope.L5998", s
  | "read_sbr_envelope.L59d8", s | "read_sbr_envelope.L5a0d", s | "read_sbr_envelope.L5a11", s
  | "read_sbr_envelope.L5a38", s
  | "read_sbr_envelope.L5cd0", s | "read_sbr_envelope.L5ced", s | "read_sbr_envelope.L5cfd", s
  | "read_sbr_envelope.L5d35", s | "read_sbr_envelope.L5d75", s | "read_sbr_envelope.L5da6", s
  | "read_sbr_envelope.L5daa", s | "read_sbr_envelope.L5dd7", s =>
      100 * (10 - fi s) + (60 - (s.regs.get64 .rsi).toNat)
  | "read_sbr_envelope.L5ad0", s | "read_sbr_envelope.L5ae4", s | "read_sbr_envelope.L5b25", s
  | "read_sbr_envelope.L5b61", s | "read_sbr_envelope.L5b93", s | "read_sbr_envelope.L5b97", s
  | "read_sbr_envelope.L5bc7", s
  | "read_sbr_envelope.L5e70", s | "read_sbr_envelope.L5e8d", s | "read_sbr_envelope.L5eca", s
  | "read_sbr_envelope.L5f07", s | "read_sbr_envelope.L5f3a", s | "read_sbr_envelope.L5f3e", s
  | "read_sbr_envelope.L5f6e", s =>
      100 * (10 - fi s) + (60 - (s.regs.get64 .r9).toNat)
  | "read_sbr_envelope.L5f90", s | "read_sbr_envelope.L5fac", s | "read_sbr_envelope.L5fdd", s
  | "read_sbr_envelope.L5fe9", s | "read_sbr_envelope.L6019", s => 100 * (10 - fi s)
  | _, _ => 0

/-- What a return leaves, with the footprint as the code used it. -/
abbrev Post' (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  let r := t₀.regs.get64 .rsp
  ∃ gi, EnvOut x gi ((s.regs.get64 .rax).setWidth 32)
    ∧ s.regs.get64 .rsp = r + 8 ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp ∧ SavedRegs t₀ s
    ∧ ∃ fv, (s.dmem =⋆ 8 ?@ r ⋆ (Sv t₀ ⋆ (FrW r fv ⋆ (8 ?@ (r - 0xb0#64)
      ⋆ (Reserve k (r - 0xb0#64) ⋆ (EF Ext x t₀ gi ⋆ x.R))))))

abbrev BlockOb (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData)
    (l : Label) : Prop :=
  ∀ blk, Program.blockAt body l = some blk → ∀ n : Nat,
    ⦃ fun s => table k Ext x ra t₀ l s ∧ var l s = n ⦄ blk.body
    ⦃ (match blk.next with
       | some l' => fun _ s => table k Ext x ra t₀ l' s ∧ var l' s ≤ n
       | none => fun _ _ => False);
      fun a s => Table.ofLabels (fun l' s => (Program.blockAt body l').isSome
          ∧ table k Ext x ra t₀ l' s ∧ Program.EdgeLt body var l n l' s) a s
        ∨ ((a = ra ∧ Post' k Ext x ra t₀ s) ∨ envStops a) ⦄

end Kraken.Examples.Sbr.Env
