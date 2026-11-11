import Kraken.X64.Examples.Sbr.Parse.PsCore

/-!
# `ff_ps_read_data`: the assertions at the labels of the header, the frame class and the borders (`0x0`–`0x714`)

`q<off>` is the assertion at `ff_ps_read_data.L<off>` (see `PsBase.table`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Parse

namespace Kraken.Examples.Sbr.Ps

variable [CodeEnv]

/-- The six slots the prologue pushes into, before the pushes. -/
abbrev Sv0 (t₀ : MachineData) : Mem 64 → Prop :=
  8 ?@ (rsp0 t₀ - 8#64) ⋆ (8 ?@ (rsp0 t₀ - 0x10#64) ⋆ (8 ?@ (rsp0 t₀ - 0x18#64)
  ⋆ (8 ?@ (rsp0 t₀ - 0x20#64) ⋆ (8 ?@ (rsp0 t₀ - 0x28#64) ⋆ 8 ?@ (rsp0 t₀ - 0x30#64)))))

/-- The stack at the entry, cut into the frame's pieces (`PsPre`'s reservation split). -/
abbrev Fr0 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    Mem 64 → Prop :=
  0x78 ?@ (rsp0 t₀ - 0xa8#64) ⋆ (Sv0 t₀ ⋆ (8 ?@ (rsp0 t₀ - 0xb0#64)
    ⋆ (Reserve k (rsp0 t₀ - 0xb0#64) ⋆ (PF Ext x t₀ x.c x.idx ⋆ (RetCell ra (rsp0 t₀) ⋆ x.R)))))

/-- The argument registers. -/
abbrev Args (t₀ s : MachineData) : Prop :=
  s.regs.get64 .rdi = arg0 t₀ ∧ s.regs.get64 .rsi = arg1 t₀ ∧ s.regs.get64 .rdx = arg2 t₀

/-- The entry, with the reservation cut. -/
def qEntry (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  s = t₀ ∧ PsC x t₀ ∧ (t₀.dmem =⋆ Fr0 k Ext x ra t₀)

/-! ## The header region's own facts -/

/-- `*ps` outside `[4, 0x4c)` is as at the entry (the header code writes only there). -/
def Kp (x : PArgs) (c : List UInt8) : Prop :=
  c.take 4 = x.c.take 4 ∧ c.drop 0x4c = x.c.drop 0x4c

/-- The header fields `[4, 0x24)` are as at the entry (no header was read). -/
def K24 (x : PArgs) (c : List UInt8) : Prop :=
  (c.drop 4).take 0x20 = (x.c.drop 4).take 0x20

/-- The `iid` table width, once the header set it. -/
def IidH (c : List UInt8) : Prop :=
  i32 c 4 ≠ 0 → i32 c 12 = 10 ∨ i32 c 12 = 20 ∨ i32 c 12 = 34

/-- What the header bit (`rbp - 0x88`) says about the header fields. -/
def HdrOk (x : PArgs) (c f : List UInt8) : Prop :=
  (rd f 0x18 4 = 0 → K24 x c) ∧ (rd f 0x18 4 ≠ 0 → IidH c)

/-- The frame, the reader registers, `rbx = ps`, `*ps` outside the header fields. -/
def HB (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData)
    (c f : List UInt8) : Prop :=
  Cm k Ext x ra t₀ s c f ∧ Rdr x s ∧ s.regs.get64 .rbx = arg2 t₀ ∧ Kp x c

/-- `num_env_old` and its slot `rbp - 0x68`. -/
abbrev S38 (c f : List UInt8) : Prop :=
  BitVec.ofInt 64 (rd f 0x38 8) = BitVec.ofInt 64 (i32 c 40)

/-- The borders `0..j` as read so far. -/
def BordTo (c : List UInt8) (j : Nat) : Prop :=
  bord c 0 = -1 ∧ (∀ e : Nat, e < j → bord c e ≤ bord c (e + 1)) ∧ (∀ e : Nat, e ≤ j → bord c e ≤ 31)

/-- After `num_env` is stored (`0x216`): `num_env = v` in `*ps`, in `r10` and in `rbp - 0x48`,
`border[0] = -1`, the reader index in `r8`. -/
def BS (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData)
    (c f : List UInt8) (v : Nat) : Prop :=
  HB k Ext x ra t₀ s c f ∧ HdrOk x c f ∧ S38 c f ∧ v ≤ 4 ∧ ne c = v
    ∧ rd f 0x58 8 = v ∧ (s.regs.get64 .r10).toNat = v ∧ bord c 0 = -1 ∧ Ix x (s.regs.get64 .r8)

/-- The fixed borders of class 0: `border[e] = (e << 5 >> log2 v) - 1` for `1 ≤ e < j`. -/
def Fixed (c : List UInt8) (lg j : Nat) : Prop :=
  ∀ e : Nat, 1 ≤ e → e < j → bord c e = (((e * 32) >>> lg : Nat) : Int) - 1

/-- After the prologue. -/
def q11 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  PsC x t₀ ∧ s.regs.get64 .rsp = rsp0 t₀ - 0xa8#64 ∧ s.regs.get64 .rbp = rsp0 t₀ - 8#64
    ∧ Args t₀ s ∧ s.regs.get64 .rcx = arg3 t₀
    ∧ ∃ f, f.length = 0x78 ∧ (s.dmem =⋆ Fr k Ext x ra t₀ f x.c x.idx)

/-- After the reader copy is loaded: `ecx = index`, `bits_left` stored. -/
def q2c (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  PsC x t₀ ∧ s.regs.get64 .rsp = rsp0 t₀ - 0xa8#64 ∧ s.regs.get64 .rbp = rsp0 t₀ - 8#64
    ∧ s.regs.get64 .rsi = arg1 t₀ ∧ s.regs.get64 .rbx = arg2 t₀ ∧ Rdr x s
    ∧ s.regs.get64 .rcx = x.idx.setWidth 64
    ∧ ∃ f, f.length = 0x78 ∧ BitVec.ofInt 32 (rd f 0x74 4) = bitsLeft t₀
      ∧ (s.dmem =⋆ Fr k Ext x ra t₀ f x.c x.idx)

/-- The first header bit read: `eax` the next index, the entry index stored. -/
def q3c (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  PsC x t₀ ∧ s.regs.get64 .rsp = rsp0 t₀ - 0xa8#64 ∧ s.regs.get64 .rbp = rsp0 t₀ - 8#64
    ∧ s.regs.get64 .rsi = arg1 t₀ ∧ s.regs.get64 .rbx = arg2 t₀ ∧ Rdr x s
    ∧ s.regs.get64 .rcx = x.idx.setWidth 64 ∧ Ix x (s.regs.get64 .rax)
    ∧ ∃ f, f.length = 0x78 ∧ BitVec.ofInt 32 (rd f 0x74 4) = bitsLeft t₀
      ∧ BitVec.ofInt 32 (rd f 0x14 4) = x.idx ∧ (s.dmem =⋆ Fr k Ext x ra t₀ f x.c x.idx)

/-- A header (`rbp - 0x88 ≠ 0`); `*ps` as at the entry. -/
def q5b (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ f, HB k Ext x ra t₀ s x.c f ∧ rd f 0x18 4 ≠ 0 ∧ Ix x (s.regs.get64 .rax)

def q70 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ f, HB k Ext x ra t₀ s x.c f ∧ rd f 0x18 4 ≠ 0 ∧ Ix x (s.regs.get64 .rdx)

/-- `enable_iid` set. -/
def q85 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, HB k Ext x ra t₀ s c f ∧ rd f 0x18 4 ≠ 0 ∧ Ix x (s.regs.get64 .rdx)

/-- `iid_mode` out of range. -/
def qaa (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  AtErr k Ext x ra t₀ s

/-- No header. -/
def qb6 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ f, HB k Ext x ra t₀ s x.c f ∧ rd f 0x18 4 = 0 ∧ Ix x (s.regs.get64 .rax)

/-- `iid_mode ≤ 5` (the `ja` reads the flags of `cmp $5`). -/
def qbf (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, HB k Ext x ra t₀ s c f ∧ rd f 0x18 4 ≠ 0 ∧ Ix x (s.regs.get64 .rdx)
    ∧ (s.regs.get64 .rax).toNat ≤ 5 ∧ (s.status.cf = true ∨ s.status.zf = true)

/-- `nr_iid_par` set from the table. -/
def qd7 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, HB k Ext x ra t₀ s c f ∧ rd f 0x18 4 ≠ 0 ∧ Ix x (s.regs.get64 .rdx)
    ∧ (s.regs.get64 .rax).toNat ≤ 5 ∧ s.regs.get64 .rcx = s.regs.get64 .rax
    ∧ (i32 c 12 = 10 ∨ i32 c 12 = 20 ∨ i32 c 12 = 34)

/-- The `iid` fields done. -/
def qf3 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, HB k Ext x ra t₀ s c f ∧ rd f 0x18 4 ≠ 0 ∧ Ix x (s.regs.get64 .rdx) ∧ IidH c

def q10b (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, HB k Ext x ra t₀ s c f ∧ rd f 0x18 4 ≠ 0 ∧ Ix x (s.regs.get64 .r8) ∧ IidH c

def q11d (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, HB k Ext x ra t₀ s c f ∧ rd f 0x18 4 ≠ 0 ∧ Ix x (s.regs.get64 .r8) ∧ IidH c

def q135 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, HB k Ext x ra t₀ s c f ∧ rd f 0x18 4 ≠ 0 ∧ Ix x (s.regs.get64 .r8) ∧ IidH c
    ∧ (s.regs.get64 .rax).toNat < 8

/-- `icc_mode` out of range. -/
def q148 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  AtErr k Ext x ra t₀ s

/-- `icc_mode < 6` (the `jae` reads the flags of `cmp $6`). -/
def q154 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, HB k Ext x ra t₀ s c f ∧ rd f 0x18 4 ≠ 0 ∧ Ix x (s.regs.get64 .r8) ∧ IidH c
    ∧ (s.regs.get64 .rax).toNat < 6 ∧ s.status.cf = true

def q16a (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, HB k Ext x ra t₀ s c f ∧ rd f 0x18 4 ≠ 0 ∧ Ix x (s.regs.get64 .r8) ∧ IidH c

def q185 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, HB k Ext x ra t₀ s c f ∧ rd f 0x18 4 ≠ 0 ∧ Ix x (s.regs.get64 .rax) ∧ IidH c

/-- The common part: the frame class, `num_env`. -/
def q197 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, HB k Ext x ra t₀ s c f ∧ HdrOk x c f ∧ Ix x (s.regs.get64 .rax)

def q1b0 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, HB k Ext x ra t₀ s c f ∧ HdrOk x c f ∧ Ix x (s.regs.get64 .rax)
    ∧ (s.regs.get64 .rdi).toNat ≤ 1 ∧ Ix x (s.regs.get64 .rdx)
    ∧ (s.regs.get64 .rdx).toNat = (s.regs.get64 .rax).toNat + (s.regs.get64 .rdi).toNat

def q1be (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, HB k Ext x ra t₀ s c f ∧ HdrOk x c f ∧ Ix x (s.regs.get64 .rax)
    ∧ (s.regs.get64 .rdi).toNat ≤ 1 ∧ Ix x (s.regs.get64 .rdx)
    ∧ (s.regs.get64 .rdx).toNat = (s.regs.get64 .rax).toNat + (s.regs.get64 .rdi).toNat
    ∧ (s.regs.get64 .rsi).toNat ≤ 1

def q1c8 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, HB k Ext x ra t₀ s c f ∧ HdrOk x c f ∧ S38 c f ∧ Ix x (s.regs.get64 .rax)
    ∧ (s.regs.get64 .rdi).toNat ≤ 1 ∧ Ix x (s.regs.get64 .rdx)
    ∧ (s.regs.get64 .rdx).toNat = (s.regs.get64 .rax).toNat + (s.regs.get64 .rdi).toNat
    ∧ (s.regs.get64 .rsi).toNat ≤ 1

def q1e1 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, HB k Ext x ra t₀ s c f ∧ HdrOk x c f ∧ S38 c f ∧ Ix x (s.regs.get64 .rax)
    ∧ (s.regs.get64 .rdi).toNat ≤ 1
    ∧ (s.regs.get64 .rax).toNat + (s.regs.get64 .rdi).toNat ≤ x.p8.toNat
    ∧ (s.regs.get64 .rsi).toNat ≤ 1 ∧ (s.regs.get64 .r9).toNat < 4

def q1fa (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, HB k Ext x ra t₀ s c f ∧ HdrOk x c f ∧ S38 c f ∧ Ix x (s.regs.get64 .r8)
    ∧ (s.regs.get64 .rsi).toNat ≤ 1 ∧ (s.regs.get64 .r9).toNat < 4

/-- `num_env` from `num_env_tab[frame_class][bits]` in `eax`, `r10`, `rbp - 0x48`. -/
def q216 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, HB k Ext x ra t₀ s c f ∧ HdrOk x c f ∧ S38 c f ∧ Ix x (s.regs.get64 .r8)
    ∧ (s.regs.get64 .rsi).toNat ≤ 1 ∧ (s.regs.get64 .rax).toNat ≤ 4
    ∧ s.regs.get64 .r10 = s.regs.get64 .rax ∧ rd f 0x58 8 = (s.regs.get64 .rax).toNat
    ∧ ((s.regs.get64 .rsi).toNat = 0 → (s.regs.get64 .rax).toNat ≠ 3)
    ∧ ((s.regs.get64 .rsi).toNat = 1 → 1 ≤ (s.regs.get64 .rax).toNat)

/-- Class 0 (fixed borders), `num_env ∈ {1, 2, 4}`. -/
def q22d (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f v, BS k Ext x ra t₀ s c f v ∧ 1 ≤ v ∧ v ≠ 3

/-- `num_env = 4`: the vector loop. -/
def q259 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, BS k Ext x ra t₀ s c f 4 ∧ s.regs.get64 .rcx = 2#64 ∧ s.regs.get64 .rdx = 1#64

/-- Class 1 (variable borders). -/
def q26e (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f v, BS k Ext x ra t₀ s c f v ∧ 1 ≤ v

def q277 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f v, BS k Ext x ra t₀ s c f v ∧ 1 ≤ v

/-- A border decreases. -/
def q297 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  AtErr k Ext x ra t₀ s

def q2b3 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f v, BS k Ext x ra t₀ s c f v ∧ 1 ≤ v ∧ BordTo c 1
    ∧ (s.regs.get64 .rdx).toNat = (bord c 1).toNat

def q2cd (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f v, BS k Ext x ra t₀ s c f v ∧ 2 ≤ v ∧ (s.regs.get64 .rax).toNat = v + 1
    ∧ BordTo c 1 ∧ (s.regs.get64 .rdx).toNat = (bord c 1).toNat

def q2ec (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f v, BS k Ext x ra t₀ s c f v ∧ 2 ≤ v ∧ (s.regs.get64 .rax).toNat = v + 1
    ∧ BordTo c 2 ∧ (s.regs.get64 .rsi).toNat = (bord c 2).toNat

def q300 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f v, BS k Ext x ra t₀ s c f v ∧ 3 ≤ v ∧ (s.regs.get64 .rax).toNat = v + 1
    ∧ BordTo c 2 ∧ (s.regs.get64 .rsi).toNat = (bord c 2).toNat

def q323 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f v, BS k Ext x ra t₀ s c f v ∧ 3 ≤ v ∧ (s.regs.get64 .rax).toNat = v + 1
    ∧ BordTo c 3 ∧ (s.regs.get64 .rdx).toNat = (bord c 3).toNat

def q337 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f v, BS k Ext x ra t₀ s c f v ∧ 4 ≤ v ∧ (s.regs.get64 .rax).toNat = v + 1
    ∧ BordTo c 3 ∧ (s.regs.get64 .rdx).toNat = (bord c 3).toNat

def q35a (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f v, BS k Ext x ra t₀ s c f v ∧ 4 ≤ v ∧ (s.regs.get64 .rax).toNat = v + 1
    ∧ BordTo c 4

def q36e (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  False

def q3aa (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  False

def q689 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  False

/-- The vector loop setup (`num_env = 4`). -/
def q69c (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, BS k Ext x ra t₀ s c f 4 ∧ s.regs.get64 .rax = 0#64 ∧ s.regs.get64 .rdx = 1#64
    ∧ s.zmms.get (.xmm .mm0) = 2#128

/-- The vector loop: one iteration, borders `7, 15, 23, 31`. -/
def q6d0 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, BS k Ext x ra t₀ s c f 4 ∧ s.regs.get64 .rax = 0#64 ∧ s.regs.get64 .rsi = 4#64
    ∧ s.zmms.get (.xmm .mm0) = 2#128 ∧ s.zmms.get (.xmm .mm1) = 0x00000004000000030000000200000001#128
    ∧ s.zmms.get (.xmm .mm2) = BitVec.allOnes 128

/-- The scalar loop setup (`num_env ∈ {1, 2}`, `cl = log2 num_env`). -/
def q6f5 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f v, BS k Ext x ra t₀ s c f v ∧ (v = 1 ∨ v = 2) ∧ s.regs.get64 .rdx = 1#64
    ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (v - 1)

/-- The scalar loop: borders `1..rdx-1` written. -/
def q700 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f v, BS k Ext x ra t₀ s c f v ∧ (v = 1 ∨ v = 2)
    ∧ (s.regs.get64 .rax).toNat = v + 1 ∧ 1 ≤ (s.regs.get64 .rdx).toNat
    ∧ (s.regs.get64 .rdx).toNat ≤ v
    ∧ (s.regs.get64 .rsi).toNat = 32 * (s.regs.get64 .rdx).toNat
    ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (v - 1) ∧ Fixed c (v - 1) (s.regs.get64 .rdx).toNat

end Kraken.Examples.Sbr.Ps
