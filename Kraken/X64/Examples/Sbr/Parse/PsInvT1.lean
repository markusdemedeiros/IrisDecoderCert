import Kraken.X64.Examples.Sbr.Parse.PsCore

/-!
# `ff_ps_read_data`: the assertions at the labels of the fix-ups (`0x1063`–`0x13ed`)

`q<off>` is the assertion at `ff_ps_read_data.L<off>` (see `PsBase.table`).

The fix-ups after the extension (`aacps_common.c`, the "Fix up envelopes" part): when
`num_env = 0` or `border_position[num_env] < 31`, a fake envelope `N = num_env` is made by
copying the rows `iid`/`icc`/`ipd`/`opd` of the source envelope `S` (`num_env - 1`, or
`num_env_old - 1` without envelopes; only if `S ≥ 0` and `S ≠ N`), checking row `N` of `iid`
(`|iid_par[N][b]| ≤ 7 + 8 iid_quant` for `b < nr_iid_par`, `0x1252`, unrolled by 4) and of `icc`
(`icc_par[N][b] ≤ 7`, `0x12ff` and the loop at `0x14ec` of the next region), then
`num_env = N + 1`, `border_position[N + 1] = 31`. Then `is34bands_old = is34bands`, the new
`is34bands`, and the `ipd`/`opd` arrays are cleared when `enable_ipdopd = 0` (`0x1395`–`0x13f5`).

The ghost `N` is `num_env` as the header code read it (`rbp - 0x48`, also the loop bound slot
`rbp - 0x60`); `ne c = N` until `0x1349`, `ne c = N + 1` after. The `PsWFb` facts grow along
the path: `T1W0` (as at `0x1063`), `T1W1` (row `N` of `iid` checked), `T1W2` (the borders fixed:
what `PsOut` needs). `IidZ` (`AtExt`) covers the
fake envelope when `enable_iid = 0` (row `N` is neither copied nor checked then).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Parse

namespace Kraken.Examples.Sbr.Ps

variable [CodeEnv]

/-! ## Building blocks -/

/-- The `iid` bounds of the bands `b < m` of row `e`. -/
def T1Row (c : List UInt8) (e m : Nat) : Prop :=
  ∀ b : Nat, b < m →
    -(7 + 8 * i32 c 8) ≤ i8 c (76 + 34 * e + b) ∧ i8 c (76 + 34 * e + b) ≤ 7 + 8 * i32 c 8

/-- `Hdr` up to the ghost `N` (not reading `num_env`). -/
def T1H (c : List UInt8) (N : Nat) : Prop :=
  bord c 0 = -1 ∧ (∀ e : Nat, e < N → bord c e ≤ bord c (e + 1)) ∧ (∀ e : Nat, e ≤ N → bord c e ≤ 31)

/-- The `PsWFb` facts at `0x1063`. -/
def T1W0 (c f : List UInt8) (N : Nat) : Prop :=
  Rng c ∧ T1H c N ∧ IidS c (rd f 0x18 4) ∧ IidB c N ∧ IidZ c

/-- Row `N` of `iid` checked. -/
def T1W1 (c f : List UInt8) (N : Nat) : Prop :=
  Rng c ∧ T1H c N ∧ IidS c (rd f 0x18 4) ∧ IidB c (N + 1)

/-- The borders fixed: `PsWFb`'s `start ≠ 0` clauses except the `nr_iid_par` one (in `IidS`). -/
def T1Fix (c : List UInt8) : Prop :=
  1 ≤ ne c ∧ ne c ≤ 5 ∧ bord c 0 = -1 ∧ (∀ e : Nat, (e : Int) < ne c → bord c e ≤ bord c (e + 1))
  ∧ bord c (ne c).toNat = 31 ∧ IidB c (ne c)

def T1W2 (c f : List UInt8) : Prop :=
  Rng c ∧ IidS c (rd f 0x18 4) ∧ T1Fix c

/-- What every label after `0x1063` knows: the frame, the reader's index (`r8`), `bits_left`
(`r15`), the slots `ps` and the loop bound `N`. -/
def T1B (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData)
    (c f : List UInt8) (N : Nat) : Prop :=
  Cm k Ext x ra t₀ s c f ∧ Ix x (s.regs.get64 .r8)
  ∧ (s.regs.get64 .r15).setWidth 32 = bitsLeft t₀
  ∧ N ≤ 4 ∧ rd f 0x40 8 = N ∧ BitVec.ofInt 64 (rd f 0x68 8) = arg2 t₀

/-- Before the increment: `num_env = N = r12`. -/
def T1N (x : PArgs) (s : MachineData) (c : List UInt8) (N : Nat) : Prop :=
  ne c = N ∧ s.regs.get64 .r12 = BitVec.ofNat 64 N

/-- `r10d = enable_iid`. -/
abbrev T1I (s : MachineData) (c : List UInt8) : Prop :=
  (s.regs.get64 .r10).setWidth 32 = BitVec.ofInt 32 (i32 c 4)

/-- The source envelope `S` (`r9 = S + 1`). -/
def T1S (s : MachineData) (N S : Nat) : Prop :=
  (s.regs.get64 .r9).setWidth 32 = BitVec.ofNat 32 (S + 1) ∧ S < 5 ∧ S ≠ N

/-- The copy blocks: `rbx = ps`, `rcx = S`. -/
def T1C (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData)
    (c f : List UInt8) (N S : Nat) : Prop :=
  T1B k Ext x ra t₀ s c f N ∧ T1N x s c N ∧ s.regs.get64 .rbx = arg2 t₀ ∧ T1I s c ∧ T1S s N S
  ∧ s.regs.get64 .rcx = BitVec.ofNat 64 S ∧ (PsWFb x.c → T1W0 c f N)

/-- The `iid` check loop: `rcx = nr_iid_par`, `rdi = &iid_par[N][3]`, `r11 = b` (a multiple of
4), `rsi`, `r9`, `r10` = `rcx - 3`, `- 2`, `- 1`, `edx = 7 + 8 iid_quant`; the bands `< b + j`
are checked. -/
def T1L (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) (j : Nat) :
    Prop :=
  ∃ c f N b, T1B k Ext x ra t₀ s c f N ∧ T1N x s c N ∧ i32 c 4 ≠ 0
    ∧ 0 < i32 c 12 ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (i32 c 12).toNat
    ∧ s.regs.get64 .rdi = arg2 t₀ + BitVec.ofNat 64 (34 * N + 0x4f)
    ∧ s.regs.get64 .rsi = s.regs.get64 .rcx - 3#64 ∧ s.regs.get64 .r9 = s.regs.get64 .rcx - 2#64
    ∧ s.regs.get64 .r10 = s.regs.get64 .rcx - 1#64
    ∧ (s.regs.get64 .rdx).setWidth 32 = BitVec.ofInt 32 (7 + 8 * i32 c 8)
    ∧ s.regs.get64 .r11 = BitVec.ofNat 64 b ∧ b % 4 = 0 ∧ (b + j : Int) < i32 c 12
    ∧ (PsWFb x.c → T1W0 c f N ∧ T1Row c N (b + j))

/-- After the `iid` check (or none needed). -/
def T1A (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData)
    (c f : List UInt8) (N : Nat) : Prop :=
  T1B k Ext x ra t₀ s c f N ∧ (PsWFb x.c → T1W1 c f N)

/-- After the fix-ups: `rbx = ps`. -/
def T1D (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) : Prop :=
  ∃ c f N, T1B k Ext x ra t₀ s c f N ∧ s.regs.get64 .rbx = arg2 t₀ ∧ (PsWFb x.c → T1W2 c f)

/-! ## The interface with the next region -/

/-- `0x13f5` (the next region's entry): the fix-ups are done. -/
def a13f5 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) : Prop :=
  T1D k Ext x ra t₀ s

/-- `0x14ec` (the next region's `icc` loop): `icc_par[N][0] ≤ 7`; `ecx = nr_iid_par > 0`,
`rdx = &icc_par[N][0]`. -/
def a14ec (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) : Prop :=
  ∃ c f N, T1A k Ext x ra t₀ s c f N ∧ T1N x s c N ∧ s.regs.get64 .rbx = arg2 t₀
    ∧ 0 < i32 c 12 ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (i32 c 12).toNat
    ∧ s.regs.get64 .rdx = arg2 t₀ + BitVec.ofNat 64 (34 * N + 0xf6)

/-! ## The assertions -/

def q1063 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  AtExt k Ext x ra t₀ s

/-- `num_env = N ≠ 0`; `r10d = enable_iid` is loaded here. -/
def q1084 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f N, T1B k Ext x ra t₀ s c f N ∧ T1N x s c N ∧ 1 ≤ N ∧ s.regs.get64 .rbx = arg2 t₀
    ∧ BitVec.ofInt 32 (rd f 0x34 4) = BitVec.ofInt 32 (i32 c 4) ∧ (PsWFb x.c → T1W0 c f N)

/-- No fix-up (`border_position[num_env] = 31`), or after it: `is34bands` from
`nr_iid_par`/`nr_icc_par`. -/
def q10b4 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  T1D k Ext x ra t₀ s

/-- The `iid` check failed (format in `rdx`). -/
def q10cf (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  AtErrS k Ext x ra t₀ s

def q10d6 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  AtErrS k Ext x ra t₀ s

/-- `num_env = 0`: `r9 = num_env_old`. -/
def q10f6 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, T1B k Ext x ra t₀ s c f 0 ∧ T1N x s c 0 ∧ s.regs.get64 .rbx = arg2 t₀
    ∧ s.regs.get64 .r9 = BitVec.ofInt 64 (i32 c 40)
    ∧ BitVec.ofInt 32 (rd f 0x34 4) = BitVec.ofInt 32 (i32 c 4) ∧ (PsWFb x.c → T1W0 c f 0)

/-- A fake envelope with source `S = r9 - 1`. -/
def q1104 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f N S, T1B k Ext x ra t₀ s c f N ∧ T1N x s c N ∧ s.regs.get64 .rbx = arg2 t₀ ∧ T1I s c
    ∧ T1S s N S ∧ (PsWFb x.c → T1W0 c f N)

/-- Copy row `S` of `iid` to row `N` (`enable_iid ≠ 0`). -/
def q1119 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f N S, T1C k Ext x ra t₀ s c f N S ∧ i32 c 4 ≠ 0

def q1148 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f N S, T1C k Ext x ra t₀ s c f N S

/-- Copy row `S` of `icc`. -/
def q1157 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f N S, T1C k Ext x ra t₀ s c f N S

def q1192 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f N S, T1C k Ext x ra t₀ s c f N S

/-- Copy row `S` of `ipd`. -/
def q11a0 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f N S, T1C k Ext x ra t₀ s c f N S

/-- Copy row `S` of `opd` (`rcx = 34 S`, `rdx = 34 N`). -/
def q11db (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f N S, T1B k Ext x ra t₀ s c f N ∧ T1N x s c N ∧ s.regs.get64 .rbx = arg2 t₀ ∧ T1I s c
    ∧ S < 5 ∧ S ≠ N
    ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (34 * S) ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (34 * N)
    ∧ (PsWFb x.c → T1W0 c f N)

/-- The copies done: check row `N` of `iid` if `enable_iid ≠ 0`. -/
def q11fd (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f N, T1B k Ext x ra t₀ s c f N ∧ T1N x s c N ∧ T1I s c ∧ (PsWFb x.c → T1W0 c f N)

/-- The `iid` check, `rcx = nr_iid_par > 0`. -/
def q121f (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f N, T1B k Ext x ra t₀ s c f N ∧ T1N x s c N ∧ i32 c 4 ≠ 0
    ∧ 0 < i32 c 12 ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (i32 c 12).toNat
    ∧ (PsWFb x.c → T1W0 c f N)

/-- `rdi = N`, `r10 = ps`, `edx = 7 + 8 iid_quant`, `rsi = rcx - 3`, `r9 = rdi`. -/
def q1238 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f N, T1B k Ext x ra t₀ s c f N ∧ T1N x s c N ∧ i32 c 4 ≠ 0
    ∧ 0 < i32 c 12 ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (i32 c 12).toNat
    ∧ s.regs.get64 .rdi = BitVec.ofNat 64 N ∧ s.regs.get64 .r9 = BitVec.ofNat 64 N
    ∧ s.regs.get64 .r10 = arg2 t₀ ∧ s.regs.get64 .rsi = s.regs.get64 .rcx - 3#64
    ∧ (s.regs.get64 .rdx).setWidth 32 = BitVec.ofInt 32 (7 + 8 * i32 c 8)
    ∧ (PsWFb x.c → T1W0 c f N)

def q1252 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  T1L k Ext x ra t₀ s 0

def q1275 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  T1L k Ext x ra t₀ s 1

def q1298 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  T1L k Ext x ra t₀ s 2

def q12c5 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  T1L k Ext x ra t₀ s 3

/-- Row `N` of `iid` checked: check row `N` of `icc` if `enable_icc ≠ 0`. -/
def q12ef (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f N, T1A k Ext x ra t₀ s c f N ∧ T1N x s c N

/-- The `icc` check, `rbx = ps`, `ecx = nr_iid_par > 0` (the code bounds `icc` by
`nr_iid_par`). -/
def q12ff (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f N, T1A k Ext x ra t₀ s c f N ∧ T1N x s c N ∧ s.regs.get64 .rbx = arg2 t₀
    ∧ 0 < i32 c 12 ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (i32 c 12).toNat

/-- The `icc` check of the extra envelope failed (`r15` is not reloaded before `0x1479`). -/
def q132a (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  AtErr2 k Ext x ra t₀ s

/-- `num_env = N + 1`. -/
def q1349 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f N, T1A k Ext x ra t₀ s c f N ∧ T1N x s c N ∧ s.regs.get64 .rbx = arg2 t₀

/-- `num_env = N + 1` is stored (also from `0x14f1` of the next region): `border[N + 1] = 31`. -/
def q135c (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f N, T1A k Ext x ra t₀ s c f N ∧ ne c = N + 1
    ∧ (s.regs.get64 .r12).setWidth 32 = BitVec.ofNat 32 (N + 1) ∧ s.regs.get64 .rbx = arg2 t₀

def q1380 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  T1D k Ext x ra t₀ s

def q1385 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  T1D k Ext x ra t₀ s

/-- `cl` is the new `is34bands`. -/
def q138c (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  T1D k Ext x ra t₀ s ∧ (s.regs.get64 .rcx).setWidth 8 ≤ 1#8

/-- Clear `ipd`/`opd` if `enable_ipdopd = 0`. -/
def q1395 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  T1D k Ext x ra t₀ s

/-- The clearing of `ipd`/`opd` (`ymm0 = 0`). -/
def q13ad (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  T1D k Ext x ra t₀ s ∧ BitVec.setWidth 256 (s.zmms.get (AvxReg.ymm RegMm.mm0)) = 0#256

def q13bd (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  T1D k Ext x ra t₀ s ∧ BitVec.setWidth 256 (s.zmms.get (AvxReg.ymm RegMm.mm0)) = 0#256

def q13cd (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  T1D k Ext x ra t₀ s ∧ BitVec.setWidth 256 (s.zmms.get (AvxReg.ymm RegMm.mm0)) = 0#256

def q13dd (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  T1D k Ext x ra t₀ s ∧ BitVec.setWidth 256 (s.zmms.get (AvxReg.ymm RegMm.mm0)) = 0#256

def q13ed (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  T1D k Ext x ra t₀ s ∧ BitVec.setWidth 256 (s.zmms.get (AvxReg.ymm RegMm.mm0)) = 0#256

end Kraken.Examples.Sbr.Ps
