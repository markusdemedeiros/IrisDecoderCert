import Kraken.X64.Examples.Sbr.Parse.PsLib
import Kraken.X64.Examples.Sbr.Parse.Lib
import Kraken.Rules.LexVar

/-!
# `ff_ps_read_data`: the frame and the invariants shared by the block table

After the prologue (`rbp = rsp₀ - 8`, six pushes, `sub $0x78`) the stack holds, from the top:
the return address at `rsp₀`, the six saved registers (`Sv`), the `0x78` bytes of locals at
`rsp₀ - 0xa8` (one list cell `f`), the return slot of a call at `rsp₀ - 0xb0` and the callee's
reservation below it. `*ps` is one list cell `c` (`PF`).

The locals the invariants mention (offset in `f` = `0xa0 - d` for the slot `rbp - d`):

| slot | offset | contents |
|---|---|---|
| `rbp - 0x2c` | `0x74` | `bits_left` (4) |
| `rbp - 0x38` | `0x68` | `ps` (8) |
| `rbp - 0x40` | `0x60` | `logctx` (8) |
| `rbp - 0x48` | `0x58` | `num_env` as read (8) |
| `rbp - 0x60` | `0x40` | `num_env` (8, the loop bound) |
| `rbp - 0x68` | `0x38` | `num_env_old` (8) |
| `rbp - 0x6c` | `0x34` | `enable_iid` (4) |
| `rbp - 0x84` | `0x1c` | `enable_icc` (4) |
| `rbp - 0x88` | `0x18` | the header bit (4) |
| `rbp - 0x8c` | `0x14` | the reader's index at entry (4) |
| `rbp - 0x98` | `0x08` | `gb_host` (8) |

The invariants come in two parts: what holds on every path (`PsInv`, the frame, the reader's
index within `[index₀, size_in_bits_plus8]`), and what holds when the input satisfies `PsWFb`
(`PsWFb x.c → …`): the range clauses (`Rng`), the header (`Hdr`), the `iid` bounds (`IidB`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Parse

namespace Kraken.Examples.Sbr.Ps

variable [CodeEnv]

abbrev rsp0 (t₀ : MachineData) : BitVec 64 := t₀.regs.get64 .rsp

/-- The six saved registers, as the prologue pushed them. -/
abbrev Sv (t₀ : MachineData) : Mem 64 → Prop :=
  cell8 (rsp0 t₀ - 8#64) (t₀.regs.get64 .rbp) ⋆ (cell8 (rsp0 t₀ - 0x10#64) (t₀.regs.get64 .r15)
  ⋆ (cell8 (rsp0 t₀ - 0x18#64) (t₀.regs.get64 .r14)
  ⋆ (cell8 (rsp0 t₀ - 0x20#64) (t₀.regs.get64 .r13)
  ⋆ (cell8 (rsp0 t₀ - 0x28#64) (t₀.regs.get64 .r12)
  ⋆ cell8 (rsp0 t₀ - 0x30#64) (t₀.regs.get64 .rbx)))))

/-- The memory at every label after the prologue: the locals `f`, the saved registers, the
call slot and the callee's reservation, the footprint at `*ps = c` and reader index `i`, the
return address and the caller's memory. -/
abbrev Fr (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData)
    (f c : List UInt8) (i : BitVec 32) : Mem 64 → Prop :=
  f =@ (rsp0 t₀ - 0xa8#64) ⋆ (Sv t₀ ⋆ (8 ?@ (rsp0 t₀ - 0xb0#64)
    ⋆ (Reserve k (rsp0 t₀ - 0xb0#64) ⋆ (PF Ext x t₀ c i ⋆ (RetCell ra (rsp0 t₀) ⋆ x.R)))))

/-- The frame registers and the locals every label after the entry block knows. A slot is
stated as the bit vector a load gives (`rd` reads the bytes unsigned). -/
def Bs (x : PArgs) (t₀ s : MachineData) (c f : List UInt8) : Prop :=
  s.regs.get64 .rsp = rsp0 t₀ - 0xa8#64 ∧ s.regs.get64 .rbp = rsp0 t₀ - 8#64
  ∧ f.length = 0x78 ∧ PsInv c
  ∧ BitVec.ofInt 32 (rd f 0x74 4) = bitsLeft t₀ ∧ BitVec.ofInt 64 (rd f 0x08 8) = arg1 t₀
  ∧ BitVec.ofInt 32 (rd f 0x14 4) = x.idx

/-- The side conditions, the frame, the memory. -/
def Cm (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData)
    (c f : List UInt8) : Prop :=
  PsC x t₀ ∧ Bs x t₀ s c f ∧ (s.dmem =⋆ Fr k Ext x ra t₀ f c x.idx)

/-- The reader's registers until `0x1073`: `r13 = buffer`, `r12 = size_in_bits_plus8`. -/
abbrev Rdr (x : PArgs) (s : MachineData) : Prop :=
  s.regs.get64 .r13 = x.buf ∧ s.regs.get64 .r12 = x.p8.setWidth 64

/-- A reader index (in a register): between the index at entry and `size_in_bits_plus8`. -/
abbrev Ix (x : PArgs) (v : BitVec 64) : Prop :=
  x.idx.toNat ≤ v.toNat ∧ v.toNat ≤ x.p8.toNat

/-! ## The clauses that hold for a `PsWFb` input -/

/-- `num_env` (offset 44). -/
abbrev ne (c : List UInt8) : Int := i32 c 44

/-- `border_position[e]` (offset `52 + 4 e`). -/
abbrev bord (c : List UInt8) (e : Nat) : Int := i32 c (52 + 4 * e)

/-- The range clauses of `PsWFb` that do not depend on the header: `is34bands`, `iid_quant`,
the `icc`, `ipd`, `opd` entries. -/
def Rng (c : List UInt8) : Prop :=
  (i32 c 756 = 0 ∨ i32 c 756 = 1) ∧ (i32 c 8 = 0 ∨ i32 c 8 = 1)
  ∧ (∀ e < 5, ∀ b < 34, 0 ≤ i8 c (246 + 34 * e + b) ∧ i8 c (246 + 34 * e + b) ≤ 7)
  ∧ (∀ e < 5, ∀ b < 34, 0 ≤ i8 c (416 + 34 * e + b) ∧ i8 c (416 + 34 * e + b) ≤ 7
      ∧ 0 ≤ i8 c (586 + 34 * e + b) ∧ i8 c (586 + 34 * e + b) ≤ 7)

/-- What the error path needs (it clears the four arrays): `is34bands`, `iid_quant`. -/
def Rng0 (c : List UInt8) : Prop :=
  (i32 c 756 = 0 ∨ i32 c 756 = 1) ∧ (i32 c 8 = 0 ∨ i32 c 8 = 1)

/-- The `iid` table width, once `start` is set or a header was read (`hdr` the header bit). -/
def IidS (c : List UInt8) (hdr : Int) : Prop :=
  (i32 c 0 ≠ 0 ∨ hdr ≠ 0) → i32 c 4 ≠ 0 → i32 c 12 = 10 ∨ i32 c 12 = 20 ∨ i32 c 12 = 34

/-- The borders as read: `num_env ≤ 4`, `border[0] = -1`, nondecreasing, at most `31`. -/
def Hdr (c : List UInt8) : Prop :=
  0 ≤ ne c ∧ ne c ≤ 4 ∧ bord c 0 = -1
  ∧ (∀ e : Nat, (e : Int) < ne c → bord c e ≤ bord c (e + 1))
  ∧ (∀ e : Nat, (e : Int) ≤ ne c → bord c e ≤ 31)

/-- The `iid` bounds for the envelopes `e < n`. -/
def IidB (c : List UInt8) (n : Int) : Prop :=
  ∀ e : Nat, (e : Int) < n → ∀ b : Nat, b < 34 → (i32 c 4 = 0 ∨ (b : Int) < i32 c 12) →
    -(7 + 8 * i32 c 8) ≤ i8 c (76 + 34 * e + b) ∧ i8 c (76 + 34 * e + b) ≤ 7 + 8 * i32 c 8

/-- With `iid` disabled, every `iid` row is in range (the routine clears the table then). -/
def IidZ (c : List UInt8) : Prop :=
  i32 c 4 = 0 → IidB c 5

/-! ## The region boundaries -/

/-- The slots written by the header code: `num_env` as read (`rbp - 0x48`), `num_env_old`
(`rbp - 0x68`). -/
def HSlots (c f : List UInt8) : Prop :=
  0 ≤ ne c ∧ ne c ≤ 4 ∧ rd f 0x58 8 = ne c ∧ BitVec.ofInt 64 (rd f 0x38 8) = BitVec.ofInt 64 (i32 c 40)

/-- `HSlots` and the slots written at `0x715`: `enable_iid`, `ps`, `num_env` (loop bound). -/
def LSlots (t₀ : MachineData) (c f : List UInt8) : Prop :=
  HSlots c f ∧ BitVec.ofInt 32 (rd f 0x34 4) = BitVec.ofInt 32 (i32 c 4)
  ∧ BitVec.ofInt 64 (rd f 0x68 8) = arg2 t₀ ∧ rd f 0x40 8 = ne c

/-- `0x715`: the header, the frame class and the borders are read. -/
def AtHdr (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) : Prop :=
  ∃ c f, Cm k Ext x ra t₀ s c f ∧ Rdr x s ∧ s.regs.get64 .rbx = arg2 t₀
    ∧ Ix x (s.regs.get64 .r8) ∧ HSlots c f ∧ (s.regs.get64 .r10).toNat = (ne c).toNat
    ∧ (PsWFb x.c → Rng c ∧ Hdr c ∧ IidS c (rd f 0x18 4))

/-- `0xa4c`: the `iid` parameters are read (or cleared). -/
def AtIid (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) : Prop :=
  ∃ c f, Cm k Ext x ra t₀ s c f ∧ Rdr x s
    ∧ Ix x (s.regs.get64 .r8) ∧ LSlots t₀ c f ∧ (s.regs.get64 .r10).toNat = (ne c).toNat
    ∧ (PsWFb x.c → Rng c ∧ Hdr c ∧ IidS c (rd f 0x18 4) ∧ IidB c (ne c) ∧ IidZ c)

/-- `0xcba`: the `icc` parameters are read (or cleared). -/
def AtIcc (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) : Prop :=
  ∃ c f, Cm k Ext x ra t₀ s c f ∧ Rdr x s
    ∧ Ix x (s.regs.get64 .r8) ∧ LSlots t₀ c f ∧ BitVec.ofInt 32 (rd f 0x1c 4) = BitVec.ofInt 32 (i32 c 20)
    ∧ (s.regs.get64 .r10).toNat = (ne c).toNat
    ∧ (PsWFb x.c → Rng c ∧ Hdr c ∧ IidS c (rd f 0x18 4) ∧ IidB c (ne c) ∧ IidZ c)

/-- `0x1063`: the extension is read (or there is none). -/
def AtExt (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) : Prop :=
  ∃ c f, Cm k Ext x ra t₀ s c f ∧ s.regs.get64 .rbx = arg2 t₀
    ∧ Ix x (s.regs.get64 .r8) ∧ LSlots t₀ c f ∧ BitVec.ofInt 32 (rd f 0x1c 4) = BitVec.ofInt 32 (i32 c 20)
    ∧ (s.regs.get64 .r10).toNat = (ne c).toNat
    ∧ (PsWFb x.c → Rng c ∧ Hdr c ∧ IidS c (rd f 0x18 4) ∧ IidB c (ne c) ∧ IidZ c)

/-- The error path, before the `av_log` call at `0x1464` (format in `rdx`, value in `eax`). -/
def AtErr (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) : Prop :=
  ∃ c f, Cm k Ext x ra t₀ s c f ∧ s.regs.get64 .rbx = arg2 t₀ ∧ (PsWFb x.c → Rng0 c)

/-- The error path where `rbx` is not `ps` (reloaded from `rbp - 0x38` after the message). -/
def AtErrS (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, Cm k Ext x ra t₀ s c f ∧ BitVec.ofInt 64 (rd f 0x68 8) = arg2 t₀ ∧ (PsWFb x.c → Rng0 c)

/-- `0x1479`: the error path after the message, `r15d = bits_left`. -/
def AtErr2 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  AtErr k Ext x ra t₀ s ∧ (s.regs.get64 .r15).setWidth 32 = bitsLeft t₀

end Kraken.Examples.Sbr.Ps
