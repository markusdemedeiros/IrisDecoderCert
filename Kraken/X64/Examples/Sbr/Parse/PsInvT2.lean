import Kraken.X64.Examples.Sbr.Parse.PsInvT1

/-!
# `ff_ps_read_data`: the assertions at the labels of the checks, the error path and the return (`0x13f5`–)

`q<off>` is the assertion at `ff_ps_read_data.L<off>` (see `PsBase.table`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Parse

namespace Kraken.Examples.Sbr.Ps

variable [CodeEnv]

/-! ## Building blocks -/

/-- After the fix-ups (from `0x1404` on): the frame, `bits_left` in `r15d`, `PsWFb` kept. -/
def T2P (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData)
    (c f : List UInt8) : Prop :=
  Cm k Ext x ra t₀ s c f ∧ (s.regs.get64 .r15).setWidth 32 = bitsLeft t₀ ∧ (PsWFb x.c → PsWFb c)

/-- The bits read `r = index - index₀` (low half of the register): within the buffer and at most
`bits_left`. -/
def T2R (x : PArgs) (t₀ : MachineData) (r : BitVec 64) : Prop :=
  (r.setWidth 32).toNat ≤ x.p8.toNat - x.idx.toNat ∧ (r.setWidth 32).toInt ≤ (bitsLeft t₀).toInt

/-- The clamp of `skip_bits_long`, second half: `eax = index`, `edx = -index`, `rsi = gb_host`,
`ecx` at most `size_in_bits_plus8 - index`. -/
def T2G (x : PArgs) (t₀ s : MachineData) : Prop :=
  (s.regs.get64 .rax).setWidth 32 = x.idx ∧ (s.regs.get64 .rdx).setWidth 32 = 0#32 - x.idx
  ∧ s.regs.get64 .rsi = arg1 t₀ ∧ ((s.regs.get64 .rcx).setWidth 32).toNat ≤ x.p8.toNat - x.idx.toNat

/-- The `icc` check of the extra envelope `N` (`0x14ec` on): as `a14ec`, with
`nr_iid_par > b`. (The bytes compared need no fact: a `PsWFb` input has them in range, `Rng`.) -/
def T2C (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) (b : Nat) :
    Prop :=
  ∃ c f N, T1A k Ext x ra t₀ s c f N ∧ T1N x s c N ∧ s.regs.get64 .rbx = arg2 t₀
    ∧ (b : Int) < i32 c 12 ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (i32 c 12).toNat
    ∧ s.regs.get64 .rdx = arg2 t₀ + BitVec.ofNat 64 (34 * N + 0xf6)

/-! ## The assertions -/

def q13f5 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  a13f5 k Ext x ra t₀ s

/-- `start` set (when a header was read): the result `index - index₀` is checked against `bits_left`. -/
def q1404 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, T2P k Ext x ra t₀ s c f ∧ Ix x (s.regs.get64 .r8) ∧ s.regs.get64 .rbx = arg2 t₀

/-- `r8d = index - index₀ ≤ bits_left`: skip it in `*gb_host` (clamped). -/
def q142f (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, T2P k Ext x ra t₀ s c f ∧ T2R x t₀ (s.regs.get64 .r8)

/-- The clamp, second half (`rax = index`, `rdx = -index`, `rsi = gb_host`). -/
def q1449 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, T2P k Ext x ra t₀ s c f ∧ T2R x t₀ (s.regs.get64 .r8) ∧ T2G x t₀ s

/-- The extension overran its size. -/
def q1459 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  AtErr k Ext x ra t₀ s

/-- The `av_log` call of the error path (format in `rdx`). -/
def q1464 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  AtErr k Ext x ra t₀ s

def q1475 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  AtErr k Ext x ra t₀ s

/-- The error path: `start = 0`, skip `bits_left`, clear the arrays. -/
def q1479 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  AtErr2 k Ext x ra t₀ s

/-- The error path: `start = 0`; the clamp of `bits_left`, second half; then `memset` of the arrays. -/
def q1499 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f, Cm k Ext x ra t₀ s c f ∧ s.regs.get64 .rbx = arg2 t₀
    ∧ (s.regs.get64 .r15).setWidth 32 = bitsLeft t₀ ∧ i32 c 0 = 0 ∧ (PsWFb x.c → Rng0 c) ∧ T2G x t₀ s

/-- The epilogue: the result in `r15d`. -/
def q14b7 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c i f, PsOut x t₀ c i ((s.regs.get64 .r15).setWidth 32) ∧ f.length = 0x78
    ∧ s.regs.get64 .rsp = rsp0 t₀ - 0xa8#64 ∧ s.regs.get64 .rbp = rsp0 t₀ - 8#64
    ∧ (s.dmem =⋆ Fr k Ext x ra t₀ f c i)

/-- The return. -/
def qdone (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c i f, PsOut x t₀ c i ((s.regs.get64 .rax).setWidth 32) ∧ f.length = 0x78
    ∧ s.regs.get64 .rsp = rsp0 t₀ ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp ∧ SavedRegs t₀ s
    ∧ (s.dmem =⋆ Fr k Ext x ra t₀ f c i)

/-- The `iid` check of the extra envelope failed (`r15d = bits_left` is still loaded: the
block jumps to `0x1479` without reloading it). -/
def q14cc (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  AtErrS k Ext x ra t₀ s ∧ (s.regs.get64 .r15).setWidth 32 = bitsLeft t₀

def q14ec (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  a14ec k Ext x ra t₀ s

/-- Row `N` of `icc` checked: `num_env = N + 1`. -/
def q14f1 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c f N, T1A k Ext x ra t₀ s c f N ∧ T1N x s c N ∧ s.regs.get64 .rbx = arg2 t₀

/-- The `icc` check from band 1 on (`nr_iid_par > 1`). -/
def q14fd (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  T2C k Ext x ra t₀ s 1

/-- The `icc` check from band 4 on (`nr_iid_par > 4`). -/
def q152a (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  T2C k Ext x ra t₀ s 4

/-- The `icc` check from band 7 on (`nr_iid_par > 7`). -/
def q1557 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  T2C k Ext x ra t₀ s 7

/-- The `icc` check from band 10 on (`nr_iid_par > 10`). -/
def q158c (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  T2C k Ext x ra t₀ s 10

/-- The `icc` check from band 13 on (`nr_iid_par > 13`). -/
def q15c5 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  T2C k Ext x ra t₀ s 13

/-- The `icc` check from band 16 on (`nr_iid_par > 16`). -/
def q15fe (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  T2C k Ext x ra t₀ s 16

/-- The `icc` check from band 19 on (`nr_iid_par > 19`). -/
def q1637 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  T2C k Ext x ra t₀ s 19

/-- The `icc` check from band 22 on (`nr_iid_par > 22`). -/
def q1670 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  T2C k Ext x ra t₀ s 22

/-- The `icc` check from band 25 on (`nr_iid_par > 25`). -/
def q16a9 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  T2C k Ext x ra t₀ s 25

/-- The `icc` check from band 28 on (`nr_iid_par > 28`). -/
def q16e2 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  T2C k Ext x ra t₀ s 28

/-- The `icc` check from band 31 on (`nr_iid_par > 31`). -/
def q171b (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  T2C k Ext x ra t₀ s 31

def q1759 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  False

def q175e (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  False

def q1763 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  False

def q1768 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  False

def q176d (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  False

def q1772 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  False

def q1777 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  False

def q177c (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  False

def q1781 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  False

def q1786 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  False

def q178b (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  False

def q1790 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  False

def q1795 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  False

def q179a (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  False

def q179f (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  False

def q17a4 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  False

def q17a9 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  False

def q17ae (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  False

def q17b3 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  False

def q17b8 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  False

def q17bd (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  False

def q17c2 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  False

def q17c7 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  False

def q17cc (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  False

def q17d1 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  False

end Kraken.Examples.Sbr.Ps
