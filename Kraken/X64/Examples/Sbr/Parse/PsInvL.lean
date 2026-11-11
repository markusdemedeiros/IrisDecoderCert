import Kraken.X64.Examples.Sbr.Parse.PsCore

/-!
# `ff_ps_read_data`: the assertions at the labels of the `iid` and `icc` parameters (`0x715`–`0xcb9`)

`q<off>` is the assertion at `ff_ps_read_data.L<off>` (see `PsBase.table`).

The `iid` loop (`0x760`–`0xa1d`) runs over the envelopes `e < num_env` (`rbx = e`, `r14` the
row `iid_par[e]`), the `icc` loop (`0xa90`–`0xc79`) likewise (`r9 = e`, `rbx` the row
`icc_par[e]`); each reads one value per band `b < nr_*_par` (`r10 = b`, resp. `r11 = b`) with an
inlined `get_vlc2` (3 levels for `iid`, 2 for `icc`), in a delta-frequency (`dt = 0`) or a
delta-time (`dt = 1`, from the row `e_prev`) variant. The value is stored before its check.

The locals of this region (offset in `f`):

| slot | offset | contents |
|---|---|---|
| `rbp - 0x50` | `0x50` | `iid_quant` (`iid` loop); `&icc_par[0]` (`icc` loop) |
| `rbp - 0x58` | `0x48` | the row `iid_par[e]` (`iid`, `dt = 1`); `num_env` (`icc` loop bound) |
| `rbp - 0x78` | `0x28` | `num_env` (`iid` loop bound) |
| `rbp - 0x80` | `0x20` | `&iid_par[0]` |
| `rbp - 0x84` | `0x1c` | `enable_icc` |
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Parse

namespace Kraken.Examples.Sbr.Ps

variable [CodeEnv]

/-! ## Building blocks -/

/-- The `ipd`/`opd` clause of `Rng`. -/
def RngPO (c : List UInt8) : Prop :=
  ∀ e < 5, ∀ b < 34, 0 ≤ i8 c (416 + 34 * e + b) ∧ i8 c (416 + 34 * e + b) ≤ 7
      ∧ 0 ≤ i8 c (586 + 34 * e + b) ∧ i8 c (586 + 34 * e + b) ≤ 7

/-- The `icc` clause of `Rng`, except at the byte offset `o` (the value just stored, not yet
checked). -/
def RngCx (c : List UInt8) (o : Nat) : Prop :=
  ∀ e < 5, ∀ b < 34, 246 + 34 * e + b ≠ o → 0 ≤ i8 c (246 + 34 * e + b) ∧ i8 c (246 + 34 * e + b) ≤ 7

/-- The bytes `[lo, hi)` of `c` are zero. -/
def Zr (c : List UInt8) (lo hi : Nat) : Prop :=
  ∀ o, lo ≤ o → o < hi → c.getD o 0 = 0

/-- The `iid` bounds of the bands `b' < b` of row `e`. -/
def IidR (c : List UInt8) (e b : Nat) : Prop :=
  ∀ b' : Nat, b' < b →
    -(7 + 8 * i32 c 8) ≤ i8 c (76 + 34 * e + b') ∧ i8 c (76 + 34 * e + b') ≤ 7 + 8 * i32 c 8

/-- The `PsWFb` facts in the `iid` loop: rows `< e` and the bands `< b` of row `e` are read. -/
def WI (c f : List UInt8) (e b : Nat) : Prop :=
  Rng c ∧ Hdr c ∧ IidS c (rd f 0x18 4) ∧ IidB c e ∧ IidR c e b

/-- The `PsWFb` facts after the `iid` parameters (`AtIid`). -/
def WC (c f : List UInt8) : Prop :=
  Rng c ∧ Hdr c ∧ IidS c (rd f 0x18 4) ∧ IidB c (ne c) ∧ IidZ c

/-- `WC`, the `icc` clause except at the offset `o`. -/
def WCx (c f : List UInt8) (o : Nat) : Prop :=
  Rng0 c ∧ RngCx c o ∧ RngPO c ∧ Hdr c ∧ IidS c (rd f 0x18 4) ∧ IidB c (ne c) ∧ IidZ c

/-- What every label from `0x71b` on keeps: the frame, the reader, the slots of the header. -/
def LB (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData)
    (c f : List UInt8) : Prop :=
  Cm k Ext x ra t₀ s c f ∧ Rdr x s ∧ Ix x (s.regs.get64 .r8) ∧ LSlots t₀ c f

/-- A VLC table pointer: `vlc_ps[j]`. -/
abbrev Tb (x : PArgs) (v : BitVec 64) (j : Nat) : Prop := v = (x.v j).p

/-- A 32-bit register value that is a sign-extended `len` `≥ 0` (the last level of a walk). -/
abbrev LenP (v : BitVec 64) : Prop :=
  ∃ l : BitVec 16, l.msb = false ∧ v.setWidth 32 = l.signExtend 32

/-- A 32-bit register value that is a sign-extended `len < 0` (a subtable entry). -/
abbrev LenN (v : BitVec 64) : Prop :=
  ∃ l : BitVec 16, l.msb = true ∧ v.setWidth 32 = l.signExtend 32

/-- The walk in table `j` is at the subtable entry `i` with `d` more levels allowed; `rl` holds
its `len`, `rs` its `sym` (sign-extended, 32-bit). -/
abbrev Wk (x : PArgs) (j d i : Nat) (rl rs : BitVec 64) : Prop :=
  VWalk (x.v j).es (d + 1) i ∧ (vlen (x.v j).es i).msb = true
  ∧ rl.setWidth 32 = (vlen (x.v j).es i).signExtend 32
  ∧ rs.setWidth 32 = (vsym (x.v j).es i).signExtend 32

/-- As `Wk`, with `sym` zero-extended in `rs` (`movzwl`). -/
abbrev WkZ (x : PArgs) (j d i : Nat) (rl rs : BitVec 64) : Prop :=
  VWalk (x.v j).es (d + 1) i ∧ (vlen (x.v j).es i).msb = true
  ∧ rl.setWidth 32 = (vlen (x.v j).es i).signExtend 32
  ∧ rs.setWidth 16 = vsym (x.v j).es i

/-! ## The `iid` loop -/

/-- The slots of the `iid` loop. -/
def IS (t₀ : MachineData) (c f : List UInt8) : Prop :=
  i32 c 4 ≠ 0 ∧ rd f 0x28 8 = ne c ∧ BitVec.ofInt 64 (rd f 0x20 8) = arg2 t₀ + 0x4c#64
  ∧ BitVec.ofInt 64 (rd f 0x50 8) = BitVec.ofInt 64 (i32 c 8)

/-- The `iid` loop at envelope `e`. -/
def IE (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData)
    (c f : List UInt8) (e : Nat) : Prop :=
  LB k Ext x ra t₀ s c f ∧ IS t₀ c f
  ∧ (s.regs.get64 .r9).setWidth 32 = BitVec.ofInt 32 (7 + 8 * i32 c 8)
  ∧ (e : Int) < ne c ∧ s.regs.get64 .rbx = BitVec.ofNat 64 e
  ∧ s.regs.get64 .r14 = arg2 t₀ + BitVec.ofNat 64 (76 + 34 * e)

/-- The `iid` band loop with `dt = 0`, at band `b` (`r10`), the count in `rn` (`r11`, or
`rdi` where the code parks it). -/
def IB0 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData)
    (c f : List UInt8) (e b j : Nat) : Prop :=
  IE k Ext x ra t₀ s c f e ∧ s.regs.get64 .r11 = BitVec.ofNat 64 (i32 c 12).toNat
  ∧ 0 < i32 c 12 ∧ s.regs.get64 .r10 = BitVec.ofNat 64 b ∧ (b : Int) < i32 c 12
  ∧ Tb x (s.regs.get64 .r15) j ∧ j < 4
  ∧ (PsWFb x.c → WI c f e b)

/-- The `iid` band loop with `dt = 1`: `rdx` the row `iid_par[ep - 1]`, `1 ≤ ep ≤ 5`; the row
`iid_par[e]` also saved at `rbp - 0x58`. -/
def IB1 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData)
    (c f : List UInt8) (e b j ep : Nat) : Prop :=
  IB0 k Ext x ra t₀ s c f e b j ∧ 1 ≤ ep ∧ ep ≤ 5
  ∧ s.regs.get64 .rdx = arg2 t₀ + BitVec.ofNat 64 (76 + 34 * ep)
  ∧ BitVec.ofInt 64 (rd f 0x48 8) = arg2 t₀ + BitVec.ofNat 64 (76 + 34 * e)

/-- `IB1` while the code parks `r14 ← rdx`, `rdi ← r11`, `r11d ← r9d` (`0x96f`–`0x9cd`). -/
def IB1p (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData)
    (c f : List UInt8) (e b j ep : Nat) : Prop :=
  LB k Ext x ra t₀ s c f ∧ IS t₀ c f
  ∧ (s.regs.get64 .r11).setWidth 32 = BitVec.ofInt 32 (7 + 8 * i32 c 8)
  ∧ (e : Int) < ne c ∧ s.regs.get64 .rbx = BitVec.ofNat 64 e
  ∧ s.regs.get64 .rdi = BitVec.ofNat 64 (i32 c 12).toNat
  ∧ 0 < i32 c 12 ∧ s.regs.get64 .r10 = BitVec.ofNat 64 b ∧ (b : Int) < i32 c 12
  ∧ Tb x (s.regs.get64 .r15) j ∧ j < 4
  ∧ 1 ≤ ep ∧ ep ≤ 5 ∧ s.regs.get64 .r14 = arg2 t₀ + BitVec.ofNat 64 (76 + 34 * ep)
  ∧ BitVec.ofInt 64 (rd f 0x48 8) = arg2 t₀ + BitVec.ofNat 64 (76 + 34 * e)
  ∧ (PsWFb x.c → WI c f e b)

/-! ## The `icc` loop -/

/-- The `icc` loop at envelope `e` (`r9`), the row in `rbx`, the count `nr_icc_par` in `rsi`. -/
def CE (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData)
    (c f : List UInt8) (e : Nat) : Prop :=
  LB k Ext x ra t₀ s c f ∧ BitVec.ofInt 32 (rd f 0x1c 4) = BitVec.ofInt 32 (i32 c 20)
  ∧ rd f 0x48 8 = ne c ∧ BitVec.ofInt 64 (rd f 0x50 8) = arg2 t₀ + 0xf6#64
  ∧ (e : Int) < ne c ∧ s.regs.get64 .r9 = BitVec.ofNat 64 e
  ∧ s.regs.get64 .rbx = arg2 t₀ + BitVec.ofNat 64 (246 + 34 * e)
  ∧ s.regs.get64 .rsi = (BitVec.ofInt 32 (i32 c 28)).setWidth 64

/-- The `icc` band loop at band `b` (`r11`), table `j` in `r14`. -/
def CB (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData)
    (c f : List UInt8) (e b j : Nat) : Prop :=
  CE k Ext x ra t₀ s c f e ∧ 0 < i32 c 28 ∧ s.regs.get64 .r11 = BitVec.ofNat 64 b
  ∧ (b : Int) < i32 c 28 ∧ Tb x (s.regs.get64 .r14) j ∧ (j = 4 ∨ j = 5)

/-- `CB` with `dt = 1`: `r15` the row `icc_par[ep - 1]`. -/
def CB1 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData)
    (c f : List UInt8) (e b j ep : Nat) : Prop :=
  CB k Ext x ra t₀ s c f e b j ∧ 1 ≤ ep ∧ ep ≤ 5
  ∧ s.regs.get64 .r15 = arg2 t₀ + BitVec.ofNat 64 (246 + 34 * ep)

/-! ## The assertions -/

def q715 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  AtHdr k Ext x ra t₀ s

/-- `enable_iid` loaded into `eax` and its slot. -/
def q71b (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, Cm k Ext x ra t₀ s c f ∧ Rdr x s ∧ s.regs.get64 .rbx = arg2 t₀
    ∧ Ix x (s.regs.get64 .r8) ∧ HSlots c f ∧ (s.regs.get64 .r10).toNat = (ne c).toNat
    ∧ BitVec.ofInt 32 (rd f 0x34 4) = BitVec.ofInt 32 (i32 c 4)
    ∧ (s.regs.get64 .rax).setWidth 32 = BitVec.ofInt 32 (i32 c 4)
    ∧ (PsWFb x.c → Rng c ∧ Hdr c ∧ IidS c (rd f 0x18 4))

/-- `enable_iid ≠ 0`, `num_env > 0` (in `rax`). -/
def q737 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, LB k Ext x ra t₀ s c f ∧ s.regs.get64 .rbx = arg2 t₀ ∧ i32 c 4 ≠ 0 ∧ 0 < ne c
    ∧ s.regs.get64 .rax = BitVec.ofInt 64 (ne c)
    ∧ (PsWFb x.c → Rng c ∧ Hdr c ∧ IidS c (rd f 0x18 4))

/-- `iid_quant` in its slot, `r14 = iid_par`, `r9d = 7 + 8 iid_quant`. -/
def q74a (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, LB k Ext x ra t₀ s c f ∧ i32 c 4 ≠ 0 ∧ 0 < ne c
    ∧ s.regs.get64 .rax = BitVec.ofInt 64 (ne c)
    ∧ s.regs.get64 .r14 = arg2 t₀ + 0x4c#64
    ∧ BitVec.ofInt 64 (rd f 0x50 8) = BitVec.ofInt 64 (i32 c 8)
    ∧ (s.regs.get64 .r9).setWidth 32 = BitVec.ofInt 32 (7 + 8 * i32 c 8)
    ∧ (PsWFb x.c → Rng c ∧ Hdr c ∧ IidS c (rd f 0x18 4))

/-- The end of envelope `e` of the `iid` loop. -/
def q760 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f e, IE k Ext x ra t₀ s c f e ∧ (PsWFb x.c → WI c f (e + 1) 0)

/-- The head of envelope `e` of the `iid` loop. -/
def q775 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f e, IE k Ext x ra t₀ s c f e ∧ (PsWFb x.c → WI c f e 0)

/-- `dt` read (`eax`), the reader's increment pending in `sil`, `edx = 0`. -/
def q798 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f e, IE k Ext x ra t₀ s c f e ∧ (PsWFb x.c → WI c f e 0)
    ∧ (s.regs.get64 .rax).toNat < 2 ∧ s.regs.get64 .rdx = 0#64
    ∧ (s.regs.get64 .r8).toNat + ((s.regs.get64 .rsi).setWidth 8).toNat ≤ x.p8.toNat

/-- `ecx = 2 dt + iid_quant < 4`. -/
def q7a8 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f e, IE k Ext x ra t₀ s c f e ∧ (PsWFb x.c → WI c f e 0)
    ∧ (s.regs.get64 .rax).toNat < 2 ∧ s.regs.get64 .rdx = 0#64
    ∧ (s.regs.get64 .r8).toNat + ((s.regs.get64 .rsi).setWidth 8).toNat ≤ x.p8.toNat
    ∧ (s.regs.get64 .rcx).toNat < 4

/-- `dt = 0`: `r11 = nr_iid_par`, `r15` the table. -/
def q7d5 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f e j, IE k Ext x ra t₀ s c f e ∧ (PsWFb x.c → WI c f e 0)
    ∧ s.regs.get64 .r11 = (BitVec.ofInt 32 (i32 c 12)).setWidth 64
    ∧ Tb x (s.regs.get64 .r15) j ∧ j < 4

/-- The band loop, `dt = 0`. -/
def q7e0 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f e b j, IB0 k Ext x ra t₀ s c f e b j

/-- Level 1: the 9-bit window in `eax`. -/
def q7f8 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f e b j, IB0 k Ext x ra t₀ s c f e b j ∧ (s.regs.get64 .rax).toNat < 512

/-- Level 2: a subtable entry. -/
def q809 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f e b j i, IB0 k Ext x ra t₀ s c f e b j
    ∧ Wk x j 2 i (s.regs.get64 .rax) (s.regs.get64 .rsi)

def q829 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  q809 k Ext x ra t₀ s

/-- Level 3: a subtable entry; `eax` the level-1 `len`. -/
def q842 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f e b j i, IB0 k Ext x ra t₀ s c f e b j
    ∧ Wk x j 1 i (s.regs.get64 .rdx) (s.regs.get64 .rsi) ∧ LenN (s.regs.get64 .rax)

/-- Level 3, the window loaded (in `eax`, so the level-1 `len` is gone). -/
def q861 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f e b j i, IB0 k Ext x ra t₀ s c f e b j
    ∧ Wk x j 1 i (s.regs.get64 .rdx) (s.regs.get64 .rsi)

/-- The walk's end: `eax = len ≥ 0`, `esi = sym`. -/
def q880 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f e b j, IB0 k Ext x ra t₀ s c f e b j ∧ LenP (s.regs.get64 .rax)

/-- `iid_par[e][b] = dil` stored, not yet checked. -/
def q8a4 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f e b j, IB0 k Ext x ra t₀ s c f e b j
    ∧ i8 c (76 + 34 * e + b) = ((s.regs.get64 .rdi).setWidth 8).toInt

/-- Band `b` checked. -/
def q8bb (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f e b j, IB0 k Ext x ra t₀ s c f e b j ∧ (PsWFb x.c → IidR c e (b + 1))

/-- `dt = 1`. -/
def q8d0 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  q7d5 k Ext x ra t₀ s

/-- `eax = e_prev + 1` (`e ? e : num_env_old`, at least 1). -/
def q8ed (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f e j ep, IE k Ext x ra t₀ s c f e ∧ (PsWFb x.c → WI c f e 0)
    ∧ s.regs.get64 .r11 = BitVec.ofNat 64 (i32 c 12).toNat ∧ 0 < i32 c 12
    ∧ Tb x (s.regs.get64 .r15) j ∧ j < 4
    ∧ 1 ≤ ep ∧ ep ≤ 5 ∧ s.regs.get64 .rax = BitVec.ofNat 64 ep

/-- The band loop, `dt = 1`. -/
def q910 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f e b j ep, IB1 k Ext x ra t₀ s c f e b j ep

def q938 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f e b j ep, IB1 k Ext x ra t₀ s c f e b j ep ∧ (s.regs.get64 .rax).toNat < 512

def q94d (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f e b j ep i, IB1 k Ext x ra t₀ s c f e b j ep
    ∧ WkZ x j 2 i (s.regs.get64 .rax) (s.regs.get64 .rcx)

def q96f (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f e b j ep i, IB1p k Ext x ra t₀ s c f e b j ep
    ∧ Wk x j 2 i (s.regs.get64 .rax) (s.regs.get64 .rdx)

/-- Level 2 entry `i` in `r9`; `eax` still the level-1 `len` (`0x996` advances by it). -/
def q983 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f e b j ep, IB1p k Ext x ra t₀ s c f e b j ep
    ∧ VWalk (x.v j).es 2 (s.regs.get64 .r9).toNat ∧ (s.regs.get64 .r9).toNat < 2 ^ 32
    ∧ LenN (s.regs.get64 .rax)

def q996 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f e b j ep i, IB1p k Ext x ra t₀ s c f e b j ep
    ∧ WkZ x j 1 i (s.regs.get64 .rdx) (s.regs.get64 .rcx) ∧ LenN (s.regs.get64 .rax)

def q9b1 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f e b j ep i, IB1p k Ext x ra t₀ s c f e b j ep
    ∧ Wk x j 1 i (s.regs.get64 .rdx) (s.regs.get64 .rax)

def q9cd (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f e b j ep, IB1p k Ext x ra t₀ s c f e b j ep ∧ LenP (s.regs.get64 .rax)

def q9da (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f e b j ep, IB1 k Ext x ra t₀ s c f e b j ep ∧ LenP (s.regs.get64 .rax)

def q9f5 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f e b j ep, IB1 k Ext x ra t₀ s c f e b j ep
    ∧ i8 c (76 + 34 * e + b) = ((s.regs.get64 .rsi).setWidth 8).toInt

/-! ### `enable_iid = 0`: `memset(iid_par, 0, …)` -/

/-- What the clearing keeps. -/
def ZI (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData)
    (c f : List UInt8) : Prop :=
  LB k Ext x ra t₀ s c f ∧ s.regs.get64 .rbx = arg2 t₀
    ∧ (s.regs.get64 .r10).toNat = (ne c).toNat
    ∧ (PsWFb x.c → Rng c ∧ Hdr c ∧ IidS c (rd f 0x18 4))

def qa1e (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, ZI k Ext x ra t₀ s c f

def qa32 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, ZI k Ext x ra t₀ s c f ∧ s.zmms.get (AvxReg.ymm .mm0) = 0 ∧ Zr c 0xcc 0xf6

def qa42 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, ZI k Ext x ra t₀ s c f ∧ s.zmms.get (AvxReg.ymm .mm0) = 0 ∧ Zr c 0x8c 0xf6

/-- After the `iid` parameters. -/
def qa4c (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  AtIid k Ext x ra t₀ s

/-! ## The `icc` parameters -/

/-- `AtIid`, `enable_icc` in its slot, `rax = ps`. -/
def AI (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData)
    (c f : List UInt8) : Prop :=
  LB k Ext x ra t₀ s c f ∧ (s.regs.get64 .r10).toNat = (ne c).toNat
    ∧ BitVec.ofInt 32 (rd f 0x1c 4) = BitVec.ofInt 32 (i32 c 20)
    ∧ s.regs.get64 .rax = arg2 t₀

/-- `enable_icc ≠ 0`, `num_env > 0`. -/
def qa6a (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, AI k Ext x ra t₀ s c f ∧ 0 < ne c ∧ (PsWFb x.c → WC c f)

/-- The end of envelope `e` of the `icc` loop. -/
def qa90 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f e, CE k Ext x ra t₀ s c f e ∧ (PsWFb x.c → WC c f)

/-- The head of envelope `e` of the `icc` loop. -/
def qaa5 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  qa90 k Ext x ra t₀ s

/-- `get_bits1`: the byte offset in `eax`, the mask in `edx`, `r8` advanced. -/
def qac5 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f e, CE k Ext x ra t₀ s c f e ∧ (PsWFb x.c → WC c f)
    ∧ (s.regs.get64 .rax).toNat ≤ x.p8.toNat / 8

/-- `dt = 1`: the table in `r14`. -/
def qaec (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f e j, CE k Ext x ra t₀ s c f e ∧ (PsWFb x.c → WC c f) ∧ 0 < i32 c 28
    ∧ Tb x (s.regs.get64 .r14) j ∧ (j = 4 ∨ j = 5)

/-- `eax = e_prev + 1`. -/
def qb01 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f e j ep, CE k Ext x ra t₀ s c f e ∧ (PsWFb x.c → WC c f) ∧ 0 < i32 c 28
    ∧ Tb x (s.regs.get64 .r14) j ∧ (j = 4 ∨ j = 5)
    ∧ 1 ≤ ep ∧ ep ≤ 5 ∧ s.regs.get64 .rax = BitVec.ofNat 64 ep

/-- The band loop, `dt = 1`. -/
def qb20 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f e b j ep, CB1 k Ext x ra t₀ s c f e b j ep ∧ (PsWFb x.c → WC c f)

def qb48 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f e b j ep, CB1 k Ext x ra t₀ s c f e b j ep ∧ (PsWFb x.c → WC c f)
    ∧ (s.regs.get64 .rax).toNat < 512

def qb59 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f e b j ep i, CB1 k Ext x ra t₀ s c f e b j ep ∧ (PsWFb x.c → WC c f)
    ∧ WkZ x j 1 i (s.regs.get64 .rax) (s.regs.get64 .rcx)

def qb75 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f e b j ep i, CB1 k Ext x ra t₀ s c f e b j ep ∧ (PsWFb x.c → WC c f)
    ∧ Wk x j 1 i (s.regs.get64 .rax) (s.regs.get64 .r10)

def qb8f (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f e b j ep, CB1 k Ext x ra t₀ s c f e b j ep ∧ (PsWFb x.c → WC c f)
    ∧ LenP (s.regs.get64 .rax)

/-- `icc_par[e][b] = dl` stored, not yet checked. -/
def qba9 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f e b j ep, CB1 k Ext x ra t₀ s c f e b j ep
    ∧ (PsWFb x.c → WCx c f (246 + 34 * e + b))
    ∧ i8 c (246 + 34 * e + b) = ((s.regs.get64 .rdx).setWidth 8).toInt

/-- `dt = 0`. -/
def qbc3 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f e j, CE k Ext x ra t₀ s c f e ∧ (PsWFb x.c → WC c f)
    ∧ Tb x (s.regs.get64 .r14) j ∧ (j = 4 ∨ j = 5)

/-- The band loop, `dt = 0` (`r15d` the running value). -/
def qbe0 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f e b j, CB k Ext x ra t₀ s c f e b j ∧ (PsWFb x.c → WC c f)

def qbf8 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f e b j, CB k Ext x ra t₀ s c f e b j ∧ (PsWFb x.c → WC c f)
    ∧ (s.regs.get64 .rax).toNat < 512

def qc09 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f e b j i, CB k Ext x ra t₀ s c f e b j ∧ (PsWFb x.c → WC c f)
    ∧ Wk x j 1 i (s.regs.get64 .rax) (s.regs.get64 .rdx)

def qc29 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  qc09 k Ext x ra t₀ s

def qc3a (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f e b j, CB k Ext x ra t₀ s c f e b j ∧ (PsWFb x.c → WC c f)
    ∧ LenP (s.regs.get64 .rax)

/-- `icc_par[e][b] = r15b` stored, not yet checked. -/
def qc5f (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f e b j, CB k Ext x ra t₀ s c f e b j
    ∧ (PsWFb x.c → WCx c f (246 + 34 * e + b))
    ∧ i8 c (246 + 34 * e + b) = ((s.regs.get64 .r15).setWidth 8).toInt

/-- An `iid` value out of range: the error path. -/
def qc7a (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  AtErrS k Ext x ra t₀ s

/-! ### `enable_icc = 0`: `memset(icc_par, 0, …)` -/

def qc86 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, AI k Ext x ra t₀ s c f ∧ (PsWFb x.c → WC c f)

def qc9a (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, AI k Ext x ra t₀ s c f ∧ s.zmms.get (AvxReg.ymm .mm0) = 0 ∧ Zr c 0x176 0x1a0
    ∧ (PsWFb x.c → Rng0 c ∧ RngPO c ∧ Hdr c ∧ IidS c (rd f 0x18 4) ∧ IidB c (ne c) ∧ IidZ c)

def qcaa (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, AI k Ext x ra t₀ s c f ∧ s.zmms.get (AvxReg.ymm .mm0) = 0 ∧ Zr c 0x136 0x1a0
    ∧ (PsWFb x.c → Rng0 c ∧ RngPO c ∧ Hdr c ∧ IidS c (rd f 0x18 4) ∧ IidB c (ne c) ∧ IidZ c)

end Kraken.Examples.Sbr.Ps
