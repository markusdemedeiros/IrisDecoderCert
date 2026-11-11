import Kraken.X64.Examples.Sbr.Parse.PsCore

/-!
# `ff_ps_read_data`: the assertions at the labels of the extension (`ipd`/`opd` parameters, `0xcba`–`0x1062`)

`q<off>` is the assertion at `ff_ps_read_data.L<off>` (see `PsBase.table`).

The extension (`ps_read_extension_data` and `read_ipdopd_data` inlined): `cnt = get_bits(4)`
(`+ get_bits(8)` when `15`), times 8; while `cnt > 7`: a 2-bit id; for id `0`,
`enable_ipdopd = get_bits1` and, when set, for each envelope `e < num_env` a `dt` bit and a row
of `ipd_par[e]` (table `vlc_ps[6 + dt]`), a `dt` bit and a row of `opd_par[e]` (`vlc_ps[8 +
dt]`), then the reserved bit; `cnt -= 2 + bits read after the id`. Finally `cnt < 0` is an error
(`0x1459`), else `cnt` bits are skipped.

The locals the loop adds (offset in the locals `f`):

| slot | offset | contents |
|---|---|---|
| `rbp - 0x50` | `0x50` | `&ipd_par[0]` (8) |
| `rbp - 0x58` | `0x48` | `num_env`, the envelope loop bound (8) |
| `rbp - 0x78` | `0x28` | `&opd_par[0]` (8) |
| `rbp - 0x80` | `0x20` | `cnt` (4) |

Registers: `r8` the reader's index after the id (it stays fixed in an iteration), the running
index in `edx`/`esi`/`edi` (`XJ`), `r15` the envelope, `r11`/`r9` the `ipd`/`opd` rows of `r15`,
`ebx` `nr_ipdopd_par`, `r14`/`r10` the band, `rdx`/`rsi` the table.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Parse

namespace Kraken.Examples.Sbr.Ps

variable [CodeEnv]

/-- What every label of the extension knows about `*ps` and the locals: the slots, the
`enable_icc` slot, the clauses for a `PsWFb` input. -/
def XI (t₀ : MachineData) (x : PArgs) (c f : List UInt8) : Prop :=
  LSlots t₀ c f ∧ BitVec.ofInt 32 (rd f 0x1c 4) = BitVec.ofInt 32 (i32 c 20)
  ∧ (PsWFb x.c → Rng c ∧ Hdr c ∧ IidS c (rd f 0x18 4) ∧ IidB c (ne c) ∧ IidZ c)

/-- The frame, the reader's registers and `XI`. -/
def XB (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData)
    (c f : List UInt8) : Prop :=
  Cm k Ext x ra t₀ s c f ∧ Rdr x s ∧ XI t₀ x c f

/-- The registers outside the loop body: the index `r8`, `r10 = num_env`, `rbx = ps`. -/
def XR (x : PArgs) (t₀ s : MachineData) (c : List UInt8) : Prop :=
  Ix x (s.regs.get64 .r8) ∧ (s.regs.get64 .r10).toNat = (ne c).toNat
  ∧ s.regs.get64 .rbx = arg2 t₀

/-- The row bases `&ipd_par[0]`, `&opd_par[0]` (set at `0xd25`). -/
def XL2 (t₀ : MachineData) (f : List UInt8) : Prop :=
  BitVec.ofInt 64 (rd f 0x50 8) = arg2 t₀ + 0x1a0#64
  ∧ BitVec.ofInt 64 (rd f 0x28 8) = arg2 t₀ + 0x24a#64

/-- `XL2` and the envelope loop bound (set at `0xd3b`). -/
def XL (t₀ : MachineData) (c f : List UInt8) : Prop :=
  XL2 t₀ f ∧ BitVec.ofInt 64 (rd f 0x48 8) = BitVec.ofNat 64 (ne c).toNat

/-- The count slot: the loop condition `cnt > 7` held at the top of the iteration. -/
def XN (f : List UInt8) : Prop := 8 ≤ (BitVec.ofInt 32 (rd f 0x20 4)).toInt

/-- The running index `cur`: a reader index, at least `r8` (the index at the top of the
iteration body). -/
def XJ (x : PArgs) (s : MachineData) (cur : BitVec 64) : Prop :=
  Ix x (s.regs.get64 .r8) ∧ Ix x cur ∧ (s.regs.get64 .r8).toNat ≤ cur.toNat

/-- The envelope loop: `ebx = nr_ipdopd_par` (zero-extended, at most 34), `r15 < num_env`,
`r11`/`r9` the rows `ipd_par[r15]`, `opd_par[r15]`. -/
def XP (t₀ s : MachineData) (c : List UInt8) : Prop :=
  (s.regs.get64 .rbx).toNat < 2 ^ 32 ∧ ((s.regs.get64 .rbx).setWidth 32).toInt ≤ 34
  ∧ (s.regs.get64 .r15).toNat < (ne c).toNat
  ∧ s.regs.get64 .r11 = arg2 t₀ + BitVec.ofNat 64 (416 + 34 * (s.regs.get64 .r15).toNat)
  ∧ s.regs.get64 .r9 = arg2 t₀ + BitVec.ofNat 64 (586 + 34 * (s.regs.get64 .r15).toNat)

/-- One of the `ipd`/`opd` tables `vlc_ps[6..9]`. -/
def XT (x : PArgs) (p : BitVec 64) : Prop := ∃ k, 6 ≤ k ∧ k < 10 ∧ p = (x.v k).p

/-- A band loop: `b < nr_ipdopd_par ≤ 34`. -/
def XBd (s : MachineData) (b : BitVec 64) : Prop :=
  (s.regs.get64 .rbx).toNat ≤ 34 ∧ b.toNat < (s.regs.get64 .rbx).toNat

/-- The previous row `par[e_prev]` of a `dt` row: `p = base + 34 * j` with `j = e_prev + 1`. -/
def XQ (t₀ : MachineData) (base : Nat) (p : BitVec 64) : Prop :=
  ∃ j, 1 ≤ j ∧ j ≤ 5 ∧ p = arg2 t₀ + BitVec.ofNat 64 (base + 34 * j)

def qcba (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  AtIcc k Ext x ra t₀ s

/-- `enable_ext` set: `get_bits(4)`. -/
def qcc8 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, XB k Ext x ra t₀ s c f ∧ XR x t₀ s c

def qce0 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, XB k Ext x ra t₀ s c f ∧ XR x t₀ s c ∧ (s.regs.get64 .rdx).toNat < 16

def qcf0 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, XB k Ext x ra t₀ s c f ∧ XR x t₀ s c

def qd08 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, XB k Ext x ra t₀ s c f ∧ XR x t₀ s c ∧ (s.regs.get64 .rdx).toNat < 256

/-- `cnt` (before `* 8`) in `edx`. -/
def qd16 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, XB k Ext x ra t₀ s c f ∧ XR x t₀ s c ∧ (s.regs.get64 .rdx).toNat < 271

/-- `cnt = 8 * edx ≥ 8` in `eax`. -/
def qd25 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, XB k Ext x ra t₀ s c f ∧ XR x t₀ s c ∧ 8 ≤ ((s.regs.get64 .rax).setWidth 32).toInt

def qd3b (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, XB k Ext x ra t₀ s c f ∧ XR x t₀ s c ∧ XL2 t₀ f
    ∧ 8 ≤ ((s.regs.get64 .rax).setWidth 32).toInt

/-- `while (cnt > 7)`: in the loop body with `cnt - (2 + bits read)` in `eax + ecx`. -/
def qd50 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, XB k Ext x ra t₀ s c f ∧ XL t₀ c f ∧ XN f ∧ XJ x s (s.regs.get64 .rdx)

def qd70 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, XB k Ext x ra t₀ s c f ∧ XR x t₀ s c ∧ XL t₀ c f

/-- The loop head: `cnt > 7` in `eax`. -/
def qd7b (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, XB k Ext x ra t₀ s c f ∧ XR x t₀ s c ∧ XL t₀ c f
    ∧ 8 ≤ ((s.regs.get64 .rax).setWidth 32).toInt

/-- The id in `edx`. -/
def qd93 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, XB k Ext x ra t₀ s c f ∧ XR x t₀ s c ∧ XL t₀ c f
    ∧ 8 ≤ ((s.regs.get64 .rax).setWidth 32).toInt

/-- id `0`: `get_bits1` for `enable_ipdopd`. -/
def qda7 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, XB k Ext x ra t₀ s c f ∧ XR x t₀ s c ∧ XL t₀ c f
    ∧ 8 ≤ ((s.regs.get64 .rax).setWidth 32).toInt

def qdc6 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, XB k Ext x ra t₀ s c f ∧ XR x t₀ s c ∧ XL t₀ c f
    ∧ 8 ≤ ((s.regs.get64 .rax).setWidth 32).toInt ∧ XJ x s (s.regs.get64 .rdx)

/-- `enable_ipdopd` set. -/
def qdd8 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, XB k Ext x ra t₀ s c f ∧ XR x t₀ s c ∧ XL t₀ c f ∧ XN f ∧ XJ x s (s.regs.get64 .rdx)

/-- The envelope loop latch (index in `edx`). -/
def qe00 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, XB k Ext x ra t₀ s c f ∧ XL t₀ c f ∧ XN f ∧ XJ x s (s.regs.get64 .rdx) ∧ XP t₀ s c

/-- The envelope loop head (index in `edx`): the `dt` bit of `ipd`. -/
def qe15 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, XB k Ext x ra t₀ s c f ∧ XL t₀ c f ∧ XN f ∧ XJ x s (s.regs.get64 .rdx) ∧ XP t₀ s c

/-- The `ipd` table choice (index in `esi`). -/
def qe32 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, XB k Ext x ra t₀ s c f ∧ XL t₀ c f ∧ XN f ∧ XJ x s (s.regs.get64 .rsi) ∧ XP t₀ s c

/-- `ipd`, `dt = 0` (table in `rdx`). -/
def qe4c (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, XB k Ext x ra t₀ s c f ∧ XL t₀ c f ∧ XN f ∧ XJ x s (s.regs.get64 .rsi) ∧ XP t₀ s c
    ∧ XT x (s.regs.get64 .rdx)

def qe60 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, XB k Ext x ra t₀ s c f ∧ XL t₀ c f ∧ XN f ∧ XJ x s (s.regs.get64 .rsi) ∧ XP t₀ s c
    ∧ XT x (s.regs.get64 .rdx) ∧ XBd s (s.regs.get64 .r14)

def qe80 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, XB k Ext x ra t₀ s c f ∧ XL t₀ c f ∧ XN f ∧ XJ x s (s.regs.get64 .rsi) ∧ XP t₀ s c
    ∧ XT x (s.regs.get64 .rdx) ∧ XBd s (s.regs.get64 .r14) ∧ (s.regs.get64 .rdi).toNat < 32

/-- `ipd`, `dt = 1`. -/
def qeb0 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, XB k Ext x ra t₀ s c f ∧ XL t₀ c f ∧ XN f ∧ XJ x s (s.regs.get64 .rsi) ∧ XP t₀ s c
    ∧ XT x (s.regs.get64 .rdx)

/-- `e_prev + 1` in `ecx`. -/
def qec9 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, XB k Ext x ra t₀ s c f ∧ XL t₀ c f ∧ XN f ∧ XJ x s (s.regs.get64 .rsi) ∧ XP t₀ s c
    ∧ XT x (s.regs.get64 .rdx) ∧ 1 ≤ (s.regs.get64 .rbx).toNat ∧ (s.regs.get64 .rbx).toNat ≤ 34
    ∧ 1 ≤ (s.regs.get64 .rcx).toNat ∧ (s.regs.get64 .rcx).toNat ≤ 5

/-- The `dt` band loop of `ipd` (index in `edi`, `r14 = &ipd_par[e_prev + 1]`). -/
def qee0 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, XB k Ext x ra t₀ s c f ∧ XL t₀ c f ∧ XN f ∧ XJ x s (s.regs.get64 .rdi) ∧ XP t₀ s c
    ∧ XT x (s.regs.get64 .rdx) ∧ XBd s (s.regs.get64 .r10) ∧ XQ t₀ 416 (s.regs.get64 .r14)

def qf06 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, XB k Ext x ra t₀ s c f ∧ XL t₀ c f ∧ XN f ∧ XJ x s (s.regs.get64 .rdi) ∧ XP t₀ s c
    ∧ XT x (s.regs.get64 .rdx) ∧ XBd s (s.regs.get64 .r10) ∧ XQ t₀ 416 (s.regs.get64 .r14)
    ∧ (s.regs.get64 .rsi).toNat < 32

/-- `opd`: the `dt` bit (index in `esi`). -/
def qf29 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, XB k Ext x ra t₀ s c f ∧ XL t₀ c f ∧ XN f ∧ XJ x s (s.regs.get64 .rsi) ∧ XP t₀ s c

/-- The `opd` table choice (index in `edx`). -/
def qf46 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, XB k Ext x ra t₀ s c f ∧ XL t₀ c f ∧ XN f ∧ XJ x s (s.regs.get64 .rdx) ∧ XP t₀ s c

/-- `opd`, `dt = 0` (table in `rsi`). -/
def qf5e (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, XB k Ext x ra t₀ s c f ∧ XL t₀ c f ∧ XN f ∧ XJ x s (s.regs.get64 .rdx) ∧ XP t₀ s c
    ∧ XT x (s.regs.get64 .rsi)

def qf70 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, XB k Ext x ra t₀ s c f ∧ XL t₀ c f ∧ XN f ∧ XJ x s (s.regs.get64 .rdx) ∧ XP t₀ s c
    ∧ XT x (s.regs.get64 .rsi) ∧ XBd s (s.regs.get64 .r14)

def qf90 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, XB k Ext x ra t₀ s c f ∧ XL t₀ c f ∧ XN f ∧ XJ x s (s.regs.get64 .rdx) ∧ XP t₀ s c
    ∧ XT x (s.regs.get64 .rsi) ∧ XBd s (s.regs.get64 .r14) ∧ (s.regs.get64 .rdi).toNat < 32

/-- `opd`, `dt = 1`. -/
def qfc0 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, XB k Ext x ra t₀ s c f ∧ XL t₀ c f ∧ XN f ∧ XJ x s (s.regs.get64 .rdx) ∧ XP t₀ s c
    ∧ XT x (s.regs.get64 .rsi)

/-- `e_prev + 1` in `eax`. -/
def qfdd (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, XB k Ext x ra t₀ s c f ∧ XL t₀ c f ∧ XN f ∧ XJ x s (s.regs.get64 .rdx) ∧ XP t₀ s c
    ∧ XT x (s.regs.get64 .rsi) ∧ 1 ≤ (s.regs.get64 .rbx).toNat ∧ (s.regs.get64 .rbx).toNat ≤ 34
    ∧ 1 ≤ (s.regs.get64 .rax).toNat ∧ (s.regs.get64 .rax).toNat ≤ 5

/-- The `dt` band loop of `opd` (index in `edi`, `r14 = &opd_par[e_prev + 1]`). -/
def q1000 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, XB k Ext x ra t₀ s c f ∧ XL t₀ c f ∧ XN f ∧ XJ x s (s.regs.get64 .rdi) ∧ XP t₀ s c
    ∧ XT x (s.regs.get64 .rsi) ∧ XBd s (s.regs.get64 .r10) ∧ XQ t₀ 586 (s.regs.get64 .r14)

def q1026 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, XB k Ext x ra t₀ s c f ∧ XL t₀ c f ∧ XN f ∧ XJ x s (s.regs.get64 .rdi) ∧ XP t₀ s c
    ∧ XT x (s.regs.get64 .rsi) ∧ XBd s (s.regs.get64 .r10) ∧ XQ t₀ 586 (s.regs.get64 .r14)
    ∧ (s.regs.get64 .rdx).toNat < 32

/-- After the loop: `cnt ≤ 7` in `eax` (negative: the error). -/
def q104e (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, XB k Ext x ra t₀ s c f ∧ XR x t₀ s c ∧ ((s.regs.get64 .rax).setWidth 32).toInt ≤ 7

end Kraken.Examples.Sbr.Ps
