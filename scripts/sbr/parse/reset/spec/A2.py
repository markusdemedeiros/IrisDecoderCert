# Entries of shard A2 (owner: rsA2): bs_freq_scale > 0 of sbr_make_f_master: log2f/powf,
# make_bands into vk0 / vk1 (stack arrays), the AV_QSORTs, array_min (vpminsd), the `change`
# step, the prefix sums, check_n_master and the memcpys into f_master, and the error exits.
#
# The arrays are int16 views of the frame region `fr`: `vk0` at offset 0x400 (rbp - 0x170),
# `vk1` at offset 0x480 (rbp - 0xf0); `fv fr o j` is element `j`.

LEMMAS = r"""
/-! ## Shard A2: `bs_freq_scale > 0` -/

namespace A2

/-- `k[1]`: `2 k[0]` with two regions (`49 k[2] > 110 k[0]`), else `k[2]`. -/
abbrev k1Of (k0 k2 : Nat) : Nat := if 110 * k0 < 49 * k2 then 2 * k0 else k2

/-- The `int16` element `j` of the frame array at byte offset `o`. -/
abbrev fv (fr : List UInt8) (o j : Nat) : Int :=
  (BitVec.ofInt 16 (Int.ofBytes (Parse.slice fr (o + 2 * j) 2))).toInt

/-- `(float)n`. -/
abbrev fl (n : Nat) : BitVec 32 := BitVec.sitof32 (BitVec.ofNat 32 n)

/-- `7 - bs_freq_scale` as a float (`.LCPI` free: `vcvtsi2ss`). -/
abbrev h0Of (a : RArgs) : BitVec 32 := fl (7 - u8 a.sp 3)

/-- The factor of the second band count: `h0 * invwarp`. -/
abbrev h1Of (a : RArgs) : BitVec 32 := BitVec.f32mul (h0Of a) (invwarp (u8 a.sp 4))

/-- `base = powf(stop / start, 1 / nb)` of `make_bands`. -/
abbrev bOf (pw : BitVec 32 → BitVec 32 → BitVec 32) (start stop nb : Nat) : BitVec 32 :=
  pw (BitVec.f32div (fl stop) (fl start)) (BitVec.f32div f1 (fl nb))

/-- `lrintf(prod)` after `j` steps of `make_bands`; `start` at `j = 0`. -/
def pv (b : BitVec 32) (start j : Nat) : Int :=
  if j = 0 then start else (BitVec.f32toi64 (chain b (fl start) j)).toInt

/-- What `make_bands` writes at the 1-based index `i` (`bands[i - 1]`). -/
def mb (b : BitVec 32) (start stop nb i : Nat) : Int :=
  if i < nb then pv b start i - pv b start (i - 1) else stop - pv b start (nb - 1)

/-- `Σ_{1 ≤ i ≤ n} A i`. -/
def ssum (A : Nat → Int) : Nat → Int
  | 0 => 0
  | n + 1 => ssum A n + A (n + 1)

/-- The first band count and its `make_bands` base. -/
abbrev n0I (e : REnv) (a : RArgs) (k0 k2 : Nat) : Int := nbOf e.lg k0 (k1Of k0 k2) (h0Of a)
abbrev n0N (e : REnv) (a : RArgs) (k0 k2 : Nat) : Nat := (n0I e a k0 k2).toNat
abbrev b0 (e : REnv) (a : RArgs) (k0 k2 : Nat) : BitVec 32 :=
  bOf e.pw k0 (k1Of k0 k2) (n0N e a k0 k2)

/-- The second band count (two regions) and its base. -/
abbrev n1I (e : REnv) (a : RArgs) (k0 k2 : Nat) : Int := nbOf e.lg (k1Of k0 k2) k2 (h1Of a)
abbrev n1N (e : REnv) (a : RArgs) (k0 k2 : Nat) : Nat := (n1I e a k0 k2).toNat
abbrev b1 (e : REnv) (a : RArgs) (k0 k2 : Nat) : BitVec 32 :=
  bOf e.pw (k1Of k0 k2) k2 (n1N e a k0 k2)

/-- `vk[1 ..= j]` hold the `make_bands` values. -/
def MB (fr : List UInt8) (o : Nat) (b : BitVec 32) (start stop nb j : Nat) : Prop :=
  ∀ i, 1 ≤ i → i ≤ j → fv fr o i = mb b start stop nb i

/-- `vk[1 ..= n]` is a list `A` with entries in `[-B, B]` summing to `tot`. -/
def Arr (fr : List UInt8) (o n : Nat) (B : Int) (tot : Int) : Prop :=
  ∃ A : Nat → Int, (∀ i, 1 ≤ i → i ≤ n → fv fr o i = A i ∧ -B ≤ A i ∧ A i ≤ B) ∧ ssum A n = tot

/-- The prefix sums done below `j`: `vk[i] = v0 + Σ_{l ≤ i} A l` for `i < j` (each `A l > 0`),
`vk[i] = A i` for `j ≤ i ≤ n`; `A` in `[-B, B]`, summing to `tot`. -/
def Pfx (fr : List UInt8) (o n j : Nat) (B v0 tot : Int) (A : Nat → Int) : Prop :=
  (∀ i, 1 ≤ i → i ≤ n → -B ≤ A i ∧ A i ≤ B) ∧ ssum A n = tot
  ∧ (∀ i, i < j → fv fr o i = v0 + ssum A i) ∧ (∀ i, 1 ≤ i → i < j → 0 < A i)
  ∧ (∀ i, j ≤ i → i ≤ n → fv fr o i = A i)

/-- `vk[0 ..= n]` strictly increasing from `v0` to `v1`. -/
def Inc (fr : List UInt8) (o n : Nat) (v0 v1 : Int) : Prop :=
  fv fr o 0 = v0 ∧ fv fr o n = v1 ∧ ∀ i, i < n → fv fr o i < fv fr o (i + 1)

/-- Inside the `bs_freq_scale > 0` part: `AtMaster`'s facts, `bs_freq_scale ≠ 0`, `k[1]`
stored, `P k0 k2 st fr` on the rest. -/
def S (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ s : MachineData)
    (P : Nat → Nat → St → List UInt8 → Prop) : Prop :=
  ∃ (row k2 : Nat), rateRow (srI a) = some row ∧ k2 ≤ 64 ∧ k0N a row ≤ k2
    ∧ (k2 : Int) - k0A a row ≤ maxQ (srI a) ∧ 1 ≤ u8 a.sp 3
    ∧ A1S k e a ra t₀ s (xk0 a row) (fun st fr => st.k2 = BitVec.ofNat 32 k2
        ∧ st.k1 = BitVec.ofNat 32 (k1Of (k0N a row) k2) ∧ P (k0N a row) k2 st fr)

/-- The failure exits inside A2 before `ac` is reloaded: `r12 = sbr`, `ac` in the frame. -/
def F (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ s : MachineData) : Prop :=
  ∃ row, rateRow (srI a) = some row
    ∧ A1S k e a ra t₀ s (xk0 a row) (fun _ fr => frSlot64 fr 0x40 = arg0 t₀)
    ∧ s.regs.get64 .r12 = arg1 t₀

/-! ### Frame slots -/

/-- After `L1684`: `-0x80 = 49 k[2]`, `-0x88 = 110 k[0]`. -/
abbrev SA (fr : List UInt8) (k0 k2 : Nat) : Prop :=
  frSlot32 fr 0x80 = BitVec.ofNat 32 (49 * k2) ∧ frSlot32 fr 0x88 = BitVec.ofNat 32 (110 * k0)

/-- After `L16b7`: also `-0x38 = (float)(7 - bs_freq_scale)`. -/
abbrev SB (fr : List UInt8) (a : RArgs) (k0 k2 : Nat) : Prop :=
  SA fr k0 k2 ∧ frSlot32 fr 0x38 = h0Of a

/-- After `L16db`: also `2 * low32(-0x50) = num_bands_0`, `-0x40 = ac`. -/
abbrev SC (fr : List UInt8) (e : REnv) (a : RArgs) (t₀ : MachineData) (k0 k2 : Nat) : Prop :=
  SB fr a k0 k2 ∧ frSlot32 fr 0x50 + frSlot32 fr 0x50 = BitVec.ofNat 32 (n0N e a k0 k2)
  ∧ frSlot64 fr 0x40 = arg0 t₀

/-- After `L16f8`: also `-0x30 = sbr`. -/
abbrev SD (fr : List UInt8) (e : REnv) (a : RArgs) (t₀ : MachineData) (k0 k2 : Nat) : Prop :=
  SC fr e a t₀ k0 k2 ∧ frSlot64 fr 0x30 = arg1 t₀

/-- After `L171d`: also the low lane of `-0x100` is `(float)k[0]`. -/
abbrev SE (fr : List UInt8) (e : REnv) (a : RArgs) (t₀ : MachineData) (k0 k2 : Nat) : Prop :=
  SD fr e a t₀ k0 k2 ∧ frSlot32 fr 0x100 = fl k0

/-- After `L173b`: also `-0x48 = num_bands_0`. -/
abbrev SF (fr : List UInt8) (e : REnv) (a : RArgs) (t₀ : MachineData) (k0 k2 : Nat) : Prop :=
  SE fr e a t₀ k0 k2 ∧ frSlot64 fr 0x48 = BitVec.ofNat 64 (n0N e a k0 k2)

/-- `num_bands_0` in range (`BandsOK`), the loop facts of the first `make_bands`. -/
abbrev N0 (e : REnv) (a : RArgs) (k0 k2 : Nat) : Prop :=
  0 < n0I e a k0 k2 ∧ n0I e a k0 k2 ≤ 48 ∧ n0N e a k0 k2 % 2 = 0

/-- The two-region part: `-0x40 = ac`, `-0x48 = nb0`, `-0x88 = nb0 + 1`, `-0x50 = vdk0_max`. -/
abbrev TA (fr : List UInt8) (t₀ : MachineData) (n0 : Nat) (vm : Int) : Prop :=
  frSlot64 fr 0x40 = arg0 t₀ ∧ frSlot64 fr 0x48 = BitVec.ofNat 64 n0
  ∧ frSlot64 fr 0x88 = BitVec.ofNat 64 (n0 + 1) ∧ frSlot32 fr 0x50 = BitVec.ofInt 32 vm

/-- `num_bands_1` in range (`BandsOK`). -/
abbrev N1 (e : REnv) (a : RArgs) (k0 k2 : Nat) : Prop :=
  2 ≤ n1I e a k0 k2 ∧ n1I e a k0 k2 ≤ 48 ∧ n1N e a k0 k2 % 2 = 0

/-- After `L1cb9`: also the low lane of `-0x80` is `(float)k[1]`, `-0x38 = nb1`,
`-0x100 = nb1 - 1`, `-0x30 = sbr`. -/
abbrev TB (fr : List UInt8) (t₀ : MachineData) (k1 n0 n1 : Nat) (vm : Int) : Prop :=
  TA fr t₀ n0 vm ∧ frSlot32 fr 0x80 = fl k1 ∧ frSlot64 fr 0x38 = BitVec.ofNat 64 n1
  ∧ frSlot64 fr 0x100 = BitVec.ofNat 64 (n1 - 1)

end A2
"""

# ---------------------------------------------------------------------------------------------
# helpers producing Lean text

def S(body):
  return f"A2.S k e a ra t₀ s (fun k0 k2 st fr => {body})"

def r(reg, v):
  return f"s.regs.get64 .{reg} = {v}"

def n64(v):
  return f"BitVec.ofNat 64 ({v})"

R12 = "s.regs.get64 .r12 = arg1 t₀"
R15 = "s.regs.get64 .r15 = arg0 t₀"
K1 = "(A2.k1Of k0 k2)"
N0 = "(A2.n0N e a k0 k2)"
N1 = "(A2.n1N e a k0 k2)"
B0 = "(A2.b0 e a k0 k2)"
B1 = "(A2.b1 e a k0 k2)"
R13K0 = r("r13", n64("k0"))
R14K1 = r("r14", n64(K1))
LO0 = "lo32 s .mm0"
LO1 = "lo32 s .mm1"
SB = "A2.SB fr a k0 k2"
SC = "A2.SC fr e a t₀ k0 k2"
SD = "A2.SD fr e a t₀ k0 k2"
SE = "A2.SE fr e a t₀ k0 k2"
SF = "A2.SF fr e a t₀ k0 k2"
NB0 = "A2.N0 e a k0 k2"
RBP = "s.regs.get64 .rbp"

def ch0(j):
  return f"chain {B0} (A2.fl k0) ({j})"

def lrint0(j):
  return f"BitVec.f32toi64 ({ch0(j)})"

def lo32reg(reg, v):
  return f"(s.regs.get64 .{reg}).setWidth 32 = BitVec.ofInt 32 ({v})"

def lo16reg(reg, v):
  return f"(s.regs.get64 .{reg}).setWidth 16 = BitVec.ofInt 16 ({v})"

def pv0(j):
  return f"A2.pv {B0} k0 ({j})"

def mb0(i):
  return f"A2.mb {B0} k0 ({K1}) ({N0}) ({i})"

def MB0(j):
  return f"A2.MB fr 0x400 {B0} k0 ({K1}) ({N0}) ({j})"

# the unrolled loop of the first make_bands: d = rdx, a multiple of 8
L0 = (f"{SF} ∧ {NB0} ∧ 9 ≤ {N0} ∧ {R14K1} ∧ {r('rax', n64(N0 + ' - 1'))} "
      f"∧ {r('rcx', n64('(' + N0 + ' - 1) % 8'))} "
      f"∧ {r('rsi', n64('(' + N0 + ' - 1) / 8 * 8'))} ∧ {LO0} = {B0}")

def UL0(body):
  return S(f"{L0} ∧ ∃ d, {r('rdx', n64('d'))} ∧ d % 8 = 0 ∧ d + 8 ≤ ({N0} - 1) / 8 * 8 ∧ {body}")

ENTRIES = {
    # from A1 (the interface A1 -> A2)
    "L1684": "AtMaster k e a ra t₀ s",
    # bs_freq_scale != 0: k[1], -0x80 = 49 k2, -0x88 = 110 k0 (A1S, AtMaster facts, k1 not yet stored)
    "L16b7": "∃ (row k2 : Nat), rateRow (srI a) = some row ∧ k2 ≤ 64 ∧ k0N a row ≤ k2 "
             "∧ (k2 : Int) - k0A a row ≤ maxQ (srI a) ∧ 1 ≤ u8 a.sp 3 "
             "∧ A1S k e a ra t₀ s (xk0 a row) (fun st fr => st.k2 = BitVec.ofNat 32 k2 "
             "∧ A2.SA fr (k0N a row) k2) "
             f"∧ {R12} ∧ {R15} ∧ {r('r13', n64('k0N a row'))} "
             f"∧ {r('r14', n64('A2.k1Of (k0N a row) k2'))} "
             f"∧ {r('rcx', n64('7 - u8 a.sp 3'))}",
    "L16d6": S(f"{R12} ∧ {R15} ∧ {R13K0} ∧ {R14K1} ∧ {SB} "
               f"∧ {LO0} = BitVec.f32div (A2.fl ({K1})) (A2.fl k0)"),
    "L16db": S(f"{R12} ∧ {R15} ∧ {R13K0} ∧ {R14K1} ∧ {SB} "
               f"∧ {LO0} = e.lg (BitVec.f32div (A2.fl ({K1})) (A2.fl k0))"),
    "L16f8": S(f"{R12} ∧ {R15} ∧ {R13K0} ∧ {R14K1} ∧ {SC} ∧ {NB0} ∧ {r('rcx', n64(N0))}"),
    "L171d": S(f"{R15} ∧ {R13K0} ∧ {R14K1} ∧ {SD} ∧ {NB0} ∧ {r('rcx', n64(N0))} "
               f"∧ (s.zmms.get (AvxReg.xmm .mm0)).dw 0 = A2.fl ({K1}) "
               f"∧ (s.zmms.get (AvxReg.xmm .mm0)).dw 1 = f1 "
               f"∧ lo32 s .mm2 = A2.fl k0 ∧ {LO1} = A2.fl ({N0})"),
    "L1736": S(f"{R15} ∧ {R13K0} ∧ {R14K1} ∧ {SE} ∧ {NB0} ∧ {r('rbx', n64(N0))} "
               f"∧ {LO0} = BitVec.f32div (A2.fl ({K1})) (A2.fl k0) "
               f"∧ {LO1} = BitVec.f32div f1 (A2.fl ({N0}))"),
    "L173b": S(f"{R15} ∧ {R13K0} ∧ {R14K1} ∧ {SE} ∧ {NB0} ∧ {r('rbx', n64(N0))} ∧ {LO0} = {B0}"),
    "L1830": S(f"{R13K0} ∧ {R14K1} ∧ {SF} ∧ {NB0} ∧ 9 ≤ {N0} "
               f"∧ {r('rax', n64(N0 + ' - 1'))} ∧ {r('rcx', n64('(' + N0 + ' - 1) % 8'))} "
               f"∧ {LO0} = {B0}"),
    # the unrolled loop (8 steps per iteration)
    "L1850": UL0(f"{lo32reg('r13', pv0('d'))} ∧ {LO1} = {ch0('d')} ∧ {MB0('d')}"),
    "L1886": UL0(f"{lo32reg('r13', pv0('d'))} ∧ {LO1} = {ch0('d + 6')} ∧ {MB0('d')} "
                 f"∧ {r('rdi', lrint0('d + 1'))} ∧ {r('r8', lrint0('d + 2'))} "
                 f"∧ {r('r9', lrint0('d + 3'))} ∧ {r('r10', lrint0('d + 4'))} "
                 f"∧ {r('r11', lrint0('d + 5'))} ∧ {r('rbx', lrint0('d + 6'))}"),
    "L18b8": UL0(f"{lo32reg('r12', pv0('d + 7'))} ∧ {LO1} = {ch0('d + 7')} ∧ {MB0('d + 2')} "
                 f"∧ {lo16reg('r9', mb0('d + 3'))} ∧ {lo16reg('r10', mb0('d + 4'))} "
                 f"∧ {lo16reg('r11', mb0('d + 5'))} ∧ {lo16reg('rbx', mb0('d + 6'))} "
                 f"∧ {lo16reg('r15', mb0('d + 7'))}"),
    "L18ca": UL0(f"{lo32reg('r12', pv0('d + 7'))} ∧ {LO1} = {ch0('d + 7')} ∧ {MB0('d + 4')} "
                 f"∧ {lo16reg('r11', mb0('d + 5'))} ∧ {lo16reg('rbx', mb0('d + 6'))} "
                 f"∧ {lo16reg('r15', mb0('d + 7'))}"),
    "L18db": UL0(f"{lo32reg('r12', pv0('d + 7'))} ∧ {LO1} = {ch0('d + 7')} ∧ {MB0('d + 6')} "
                 f"∧ {lo16reg('r15', mb0('d + 7'))}"),
    # the remainder loop
    "L1908": S(f"{SF} ∧ {NB0} ∧ {R14K1} ∧ {r('rax', n64(N0 + ' - 1'))} "
               f"∧ {r('rcx', n64('(' + N0 + ' - 1) % 8'))} ∧ {LO0} = {B0} "
               f"∧ {r('rdx', n64('(' + N0 + ' - 1) / 8 * 8'))} "
               f"∧ {lo32reg('r13', pv0('(' + N0 + ' - 1) / 8 * 8'))} "
               f"∧ {LO1} = {ch0('(' + N0 + ' - 1) / 8 * 8')} ∧ {MB0('(' + N0 + ' - 1) / 8 * 8')}"),
    "L1920": S(f"{SF} ∧ {NB0} ∧ {R14K1} ∧ {r('rax', n64(N0 + ' - 1'))} "
               f"∧ {r('rcx', n64('(' + N0 + ' - 1) % 8'))} ∧ {LO0} = {B0} "
               f"∧ {r('rsi', RBP + ' - 0x16e#64')} "
               f"∧ {r('rdx', RBP + ' - 0x16e#64 + ' + n64('2 * ((' + N0 + ' - 1) / 8 * 8)'))} "
               f"∧ ∃ i, {r('rdi', n64('i'))} ∧ i < ({N0} - 1) % 8 "
               f"∧ {lo32reg('r13', pv0('(' + N0 + ' - 1) / 8 * 8 + i'))} "
               f"∧ {LO1} = {ch0('(' + N0 + ' - 1) / 8 * 8 + i')} "
               f"∧ {MB0('(' + N0 + ' - 1) / 8 * 8 + i')}"),
    "L194b": S(f"{SF} ∧ {NB0} ∧ {r('rax', n64(N0 + ' - 1'))} ∧ {r('rsi', RBP + ' - 0x16e#64')} "
               f"∧ {MB0(N0)}"),
    # after the first AV_QSORT: vk0[1 ..= nb0] a permutation (entries in [-64, 64], sum k1 - k0)
    "L1bbd": S(f"{SF} ∧ {NB0} ∧ {R12} ∧ {R15} ∧ {r('rax', n64(N0))} "
               f"∧ A2.Arr fr 0x400 ({N0}) 64 (({K1} : Nat) - (k0 : Int))"),
    # the prefix sums of vk0
    "L1bf0": S(f"{SF} ∧ {NB0} ∧ {R12} ∧ {R15} ∧ {r('rax', f'BitVec.ofInt 64 (-(({N0} : Nat) : Int))')} "
               f"∧ {r('rsi', n64(N0 + ' + 1'))} "
               f"∧ ∃ j A, {r('rcx', n64('j'))} ∧ 1 ≤ j ∧ j ≤ {N0} "
               f"∧ A2.Pfx fr 0x400 ({N0}) j 64 k0 (({K1} : Nat) - (k0 : Int)) A "
               f"∧ {lo32reg('rdi', 'A (' + N0 + ')')}"),
    # one region: k1 = k2
    "L1da7": S(f"{SF} ∧ {NB0} ∧ {R12} ∧ {R15} ∧ ¬ 110 * k0 < 49 * k2 "
               f"∧ A2.Inc fr 0x400 ({N0}) k0 k2"),
    "L1dd9": S(f"{R12} ∧ {R15} ∧ {NB0} ∧ frSlot64 fr 0x40 = arg0 t₀ ∧ ¬ 110 * k0 < 49 * k2 "
               f"∧ A2.Inc fr 0x400 ({N0}) k0 k2 ∧ st.nm = BitVec.ofNat 32 ({N0}) "
               f"∧ {r('r13', n64(N0))} ∧ (s.regs.get64 .r14).setWidth 8 = BitVec.ofNat 8 (u8 a.sp 2) "
               f"∧ u8 a.sp 2 < {N0} ∧ {r('rdi', 'arg1 t₀ + 0x4c1f0#64')} "
               f"∧ {r('rsi', RBP + ' - 0x170#64')} ∧ {r('rdx', n64('2 * (' + N0 + ' + 1)'))}"),
    "L1dde": S(f"{R12} ∧ {NB0} ∧ frSlot64 fr 0x40 = arg0 t₀ ∧ ¬ 110 * k0 < 49 * k2 "
               f"∧ A2.Inc fr 0x400 ({N0}) k0 k2 ∧ st.nm = BitVec.ofNat 32 ({N0}) "
               f"∧ {r('r13', n64(N0))} ∧ (s.regs.get64 .r14).setWidth 8 = BitVec.ofNat 8 (u8 a.sp 2) "
               f"∧ u8 a.sp 2 < {N0} "
               f"∧ ∀ i, i ≤ {N0} → (u16 st.fm i : Int) = A2.fv fr 0x400 i"),
    "L1e00": "AtFail k e a ra t₀ s",
    # failure exits
    "L29ad": "AtFailLog k e a ra t₀ s",
    "L29b9": "AtFailLog k e a ra t₀ s",
    "L29cd": "A2.F k e a ra t₀ s",
    "L29d3": "A2.F k e a ra t₀ s",
    "L29d9": "A2.F k e a ra t₀ s",
    "L29dc": "A2.F k e a ra t₀ s",
}

VARS = {
    "L1850": "[(s.regs.get64 .rsi).toNat - (s.regs.get64 .rdx).toNat, 0, 0]",
    "L1886": "[(s.regs.get64 .rsi).toNat - (s.regs.get64 .rdx).toNat, 0, 0]",
    "L18b8": "[(s.regs.get64 .rsi).toNat - (s.regs.get64 .rdx).toNat, 0, 0]",
    "L18ca": "[(s.regs.get64 .rsi).toNat - (s.regs.get64 .rdx).toNat, 0, 0]",
    "L18db": "[(s.regs.get64 .rsi).toNat - (s.regs.get64 .rdx).toNat, 0, 0]",
    "L1920": "[(s.regs.get64 .rcx).toNat - (s.regs.get64 .rdi).toNat, 0, 0]",
    "L1bf0": "[(s.regs.get64 .rsi).toNat - (s.regs.get64 .rcx).toNat, 0, 0]",
}

# ---------------------------------------------------------------------------------------------
# two regions (110 k0 < 49 k2, so k1 = 2 k0)

INC0 = f"A2.Inc fr 0x400 {N0} k0 {K1}"
TWO = f"110 * k0 < 49 * k2 ∧ {INC0} ∧ {NB0}"
S30 = "frSlot64 fr 0x30 = arg1 t₀"
R13K1 = r("r13", n64(K1))
R14K2 = r("r14", n64("k2"))
R15N1 = (f"(s.regs.get64 .r15).setWidth 32 + (s.regs.get64 .r15).setWidth 32 "
         f"= BitVec.ofNat 32 {N1}")
NB1 = "A2.N1 e a k0 k2"
VM = "-64 ≤ vm ∧ vm ≤ 64"

def TAx(extra):
  return f"∃ vm, {VM} ∧ A2.TA fr t₀ {N0} vm ∧ {extra}"

def TBx(extra):
  return f"∃ vm, {VM} ∧ A2.TB fr t₀ {K1} {N0} {N1} vm ∧ {extra}"

def ch1(j):
  return f"chain {B1} (A2.fl {K1}) ({j})"

def lrint1(j):
  return f"BitVec.f32toi64 ({ch1(j)})"

def pv1(j):
  return f"A2.pv {B1} {K1} ({j})"

def mb1(i):
  return f"A2.mb {B1} {K1} k2 {N1} ({i})"

def MB1(j):
  return f"A2.MB fr 0x480 {B1} {K1} k2 {N1} ({j})"

L1base = f"{TWO} ∧ {NB1} ∧ {R15N1} ∧ {R14K2} ∧ {LO0} = {B1}"

def UL1(body):
  return S(f"{L1base} ∧ 9 ≤ {N1} ∧ {r('rsi', n64('(' + N1 + ' - 1) / 8 * 8'))} "
           f"∧ {r('rcx', n64('(' + N1 + ' - 1) % 8'))} "
           f"∧ " + TBx(f"{S30} ∧ ∃ d, {r('rdx', n64('d'))} ∧ d % 8 = 0 "
                       f"∧ d + 8 ≤ ({N1} - 1) / 8 * 8 ∧ {body}"))

D1 = '(' + N1 + ' - 1) / 8 * 8'

# array_min: only memory safety and termination (the result only picks a branch)
AM0 = f"{TWO} ∧ {NB1} ∧ {R15N1} ∧ {MB1(N1)} ∧ {r('r13', n64(N1))} ∧ {r('rax', n64(N1))} ∧ " + TBx(S30)
AM = f"{TWO} ∧ {NB1} ∧ {R15N1} ∧ {MB1(N1)} ∧ {R12} ∧ {r('r13', n64(N1))} ∧ {r('rax', n64(N1))} ∧ " + TBx(S30)
AMX = f"{TWO} ∧ {NB1} ∧ {R15N1} ∧ {MB1(N1)} ∧ {R12} ∧ {r('r13', n64(N1))} ∧ " + TBx(S30)
QX = f"{TWO} ∧ {NB1} ∧ {R15N1} ∧ {R12} ∧ {r('r13', n64(N1))}"
TOT1 = f"((k2 : Nat) : Int) - (({K1} : Nat) : Int)"

ENTRIES.update({
    "L1c33": S(f"{SF} ∧ {TWO} ∧ {R12} ∧ {R15} ∧ {r('rsi', n64(N0 + ' + 1'))} "
               f"∧ ∃ vm, {VM} ∧ {lo32reg('rdi', 'vm')}"),
    "L1c59": S(f"{TWO} ∧ {R12} ∧ {R15} ∧ {S30} ∧ {LO0} = A2.h1Of a ∧ " + TAx("True")),
    "L1c76": S(f"{TWO} ∧ {R12} ∧ {R15} ∧ {S30} ∧ frSlot32 fr 0x38 = A2.h1Of a ∧ {R13K1} ∧ {R14K2} "
               f"∧ {LO0} = BitVec.f32div (A2.fl k2) (A2.fl {K1}) ∧ " + TAx("True")),
    "L1c7b": S(f"{TWO} ∧ {R12} ∧ {R15} ∧ {S30} ∧ frSlot32 fr 0x38 = A2.h1Of a ∧ {R13K1} ∧ {R14K2} "
               f"∧ {LO0} = e.lg (BitVec.f32div (A2.fl k2) (A2.fl {K1})) ∧ " + TAx("True")),
    "L1cb4": S(f"{TWO} ∧ {NB1} ∧ {R12} ∧ {S30} ∧ {R13K1} ∧ {R14K2} ∧ {R15N1} "
               f"∧ {r('rbx', n64(N1))} ∧ frSlot32 fr 0x80 = A2.fl {K1} "
               f"∧ {LO0} = BitVec.f32div (A2.fl k2) (A2.fl {K1}) "
               f"∧ {LO1} = BitVec.f32div f1 (A2.fl {N1}) ∧ " + TAx("True")),
    "L1cb9": S(f"{TWO} ∧ {NB1} ∧ {R12} ∧ {S30} ∧ {R13K1} ∧ {R14K2} ∧ {R15N1} "
               f"∧ {r('rbx', n64(N1))} ∧ frSlot32 fr 0x80 = A2.fl {K1} ∧ {LO0} = {B1} ∧ " + TAx("True")),
    "L1de3": "False",
    "L1cea": S(f"{L1base} ∧ {R13K1} ∧ {N1} ≤ 8 ∧ {r('rax', n64(N1 + ' - 1'))} "
               f"∧ {r('rcx', n64('(' + N1 + ' - 1) % 8'))} ∧ {r('rdx', n64('0'))} ∧ " + TBx(S30)),
    "L2112": S(f"{L1base} ∧ {R13K1} ∧ 9 ≤ {N1} ∧ {r('rax', n64(N1 + ' - 1'))} "
               f"∧ {r('rcx', n64('(' + N1 + ' - 1) % 8'))} ∧ " + TBx(S30)),
    "L2130": UL1(f"{lo32reg('r13', pv1('d'))} ∧ {LO1} = {ch1('d')} ∧ {MB1('d')}"),
    "L2166": UL1(f"{lo32reg('r13', pv1('d'))} ∧ {LO1} = {ch1('d + 6')} ∧ {MB1('d')} "
                 f"∧ {r('rdi', lrint1('d + 1'))} ∧ {r('r8', lrint1('d + 2'))} "
                 f"∧ {r('r9', lrint1('d + 3'))} ∧ {r('r10', lrint1('d + 4'))} "
                 f"∧ {r('r11', lrint1('d + 5'))} ∧ {r('rbx', lrint1('d + 6'))}"),
    "L2197": UL1(f"{lo32reg('r12', pv1('d + 7'))} ∧ {LO1} = {ch1('d + 7')} ∧ {MB1('d + 2')} "
                 f"∧ {lo16reg('r9', mb1('d + 3'))} ∧ {lo16reg('r10', mb1('d + 4'))} "
                 f"∧ {lo16reg('r11', mb1('d + 5'))} ∧ {lo16reg('rbx', mb1('d + 6'))} "
                 f"∧ {lo16reg('rax', mb1('d + 7'))}"),
    "L21a9": UL1(f"{lo32reg('r12', pv1('d + 7'))} ∧ {LO1} = {ch1('d + 7')} ∧ {MB1('d + 4')} "
                 f"∧ {lo16reg('r11', mb1('d + 5'))} ∧ {lo16reg('rbx', mb1('d + 6'))} "
                 f"∧ {lo16reg('rax', mb1('d + 7'))}"),
    "L21ba": UL1(f"{lo32reg('r12', pv1('d + 7'))} ∧ {LO1} = {ch1('d + 7')} ∧ {MB1('d + 6')} "
                 f"∧ {lo16reg('rax', mb1('d + 7'))}"),
    "L21e6": S(f"{L1base} ∧ {r('rcx', n64('(' + N1 + ' - 1) % 8'))} ∧ {r('rdx', n64(D1))} "
               f"∧ {lo32reg('r13', pv1(D1))} ∧ {LO1} = {ch1(D1)} ∧ " + TBx(f"{S30} ∧ {MB1(D1)}")),
    "L2200": S(f"{L1base} ∧ {r('rcx', n64('(' + N1 + ' - 1) % 8'))} "
               f"∧ {r('rdx', RBP + ' - 0xee#64 + ' + n64('2 * (' + D1 + ')'))} "
               f"∧ ∃ i, {r('rsi', n64('i'))} ∧ i < ({N1} - 1) % 8 "
               f"∧ {lo32reg('r13', pv1(D1 + ' + i'))} ∧ {LO1} = {ch1(D1 + ' + i')} "
               f"∧ " + TBx(f"{S30} ∧ {MB1(D1 + ' + i')}")),
    "L2230": S(f"{TWO} ∧ {NB1} ∧ {R15N1} ∧ {MB1(N1)} ∧ " + TBx(S30)),
    "L2252": S(f"{AM0} ∧ 5 ≤ {N1}"),
    "L2267": S(f"{AM} ∧ 17 ≤ {N1} ∧ {r('rdx', n64(N1 + ' - 1'))}"),
    "L2289": S(f"{AM} ∧ 17 ≤ {N1} ∧ {r('rdx', n64(N1 + ' - 1'))} "
               f"∧ {r('rsi', n64('(' + N1 + ' - 1) / 16 * 16'))} "
               f"∧ {r('rcx', n64('(' + N1 + ' - 1) / 16 * 16 + 1'))} "
               f"∧ ∃ i, {r('rdi', n64('i'))} ∧ i % 16 = 0 ∧ i < ({N1} - 1) / 16 * 16"),
    "L22d3": S(f"{AM} ∧ 17 ≤ {N1} ∧ {r('rdx', n64(N1 + ' - 1'))} "
               f"∧ {r('rsi', n64('(' + N1 + ' - 1) / 16 * 16'))} "
               f"∧ {r('rcx', n64('(' + N1 + ' - 1) / 16 * 16 + 1'))}"),
    "L22fa": S(f"{AM} ∧ {r('rdx', n64(N1 + ' - 1'))} "
               f"∧ ∃ i, {r('rsi', n64('i'))} ∧ i % 4 = 0 ∧ i + 4 ≤ {N1} - 1"),
    "L2310": S(f"{AM} ∧ {r('rdx', n64('(' + N1 + ' - 1) / 4 * 4'))} "
               f"∧ {r('rcx', n64('(' + N1 + ' - 1) / 4 * 4 + 1'))} "
               f"∧ ∃ i, {r('rsi', n64('i'))} ∧ i % 4 = 0 ∧ i < ({N1} - 1) / 4 * 4"),
    "L2340": S(f"{AM} ∧ ∃ c, {r('rcx', n64('c'))} ∧ 1 ≤ c ∧ c < {N1}"),
    "L2357": S(AM),
    "L25ca": S(f"{AMX} ∧ {r('rax', RBP + ' - 0xee#64')}"),
    # after the second AV_QSORT, the change step
    "L25cf": S(f"{QX} ∧ ∃ vm, {VM} ∧ A2.TA fr t₀ {N0} vm ∧ frSlot64 fr 0x30 = {n64(N1)} "
               f"∧ A2.Arr fr 0x480 {N1} 64 ({TOT1})"),
    "L25fc": S(f"{QX} ∧ ∃ vm, {VM} ∧ A2.TA fr t₀ {N0} vm ∧ frSlot64 fr 0x30 = {n64(N1)} "
               f"∧ {r('rsi', n64(N1))} ∧ ∃ A : Nat → Int, "
               f"(∀ i, 1 ≤ i → i ≤ {N1} → A2.fv fr 0x480 i = A i ∧ -64 ≤ A i ∧ A i ≤ 64) "
               f"∧ A2.ssum A {N1} = {TOT1} "
               f"∧ {lo32reg('rax', 'A 1')} ∧ {lo32reg('rcx', 'A ' + N1)} "
               f"∧ {lo32reg('rdx', 'min (vm - A 1) ((A ' + N1 + ' - A 1) / 2)')}"),
    "L2619": S(f"{QX} ∧ ∃ vm, A2.TA fr t₀ {N0} vm ∧ {r('rax', RBP + ' - 0xee#64')} "
               f"∧ {r('rcx', n64(N1))} ∧ A2.Arr fr 0x480 {N1} 256 ({TOT1})"),
    # after the third AV_QSORT: the prefix sums of vk1
    "L287a": S(f"{QX} ∧ ∃ vm, A2.TA fr t₀ {N0} vm ∧ frSlot64 fr 0x30 = {n64(N1)} "
               f"∧ A2.Arr fr 0x480 {N1} 256 ({TOT1})"),
    "L289b": S(f"{TWO} ∧ {NB1} ∧ {R12} ∧ {r('r13', n64(N1))} "
               f"∧ {r('r15', f'BitVec.ofInt 64 (-(({N1} : Nat) : Int))')} "
               f"∧ ∃ vm, A2.TA fr t₀ {N0} vm ∧ frSlot64 fr 0x30 = {n64(N1)} "
               f"∧ ∃ c A, {r('rcx', n64('c'))} ∧ c % 4 = 0 ∧ 4 ≤ c ∧ c ≤ {N1} + 2 "
               f"∧ A2.Pfx fr 0x480 {N1} (c - 3) 256 {K1} ({TOT1}) A"),
    "L28e7": S(f"{TWO} ∧ {NB1} ∧ {R12} ∧ {r('r13', n64(N1))} "
               f"∧ {r('r15', f'BitVec.ofInt 64 (-(({N1} : Nat) : Int))')} "
               f"∧ ∃ vm, A2.TA fr t₀ {N0} vm ∧ frSlot64 fr 0x30 = {n64(N1)} "
               f"∧ ∃ c A, {r('rcx', n64('c'))} ∧ c % 4 = 0 ∧ 4 ≤ c ∧ c ≤ {N1} + 2 "
               f"∧ A2.Pfx fr 0x480 {N1} (c - 1) 256 {K1} ({TOT1}) A"),
    "L292b": S(f"{TWO} ∧ {NB1} ∧ {R12} ∧ {r('r13', n64(N1))} "
               f"∧ {r('r15', f'BitVec.ofInt 64 (-(({N1} : Nat) : Int))')} "
               f"∧ ∃ vm, A2.TA fr t₀ {N0} vm ∧ frSlot64 fr 0x30 = {n64(N1)} "
               f"∧ ∃ c A, {r('rcx', n64('c'))} ∧ c % 4 = 0 ∧ 4 ≤ c ∧ c ≤ {N1} "
               f"∧ A2.Pfx fr 0x480 {N1} c 256 {K1} ({TOT1}) A ∧ 0 < A c "
               f"∧ {lo16reg('rax', K1 + ' + A2.ssum A c')}"),
    "L2949": S(f"{TWO} ∧ {NB1} ∧ {R12} ∧ {r('r13', n64(N1))} "
               f"∧ ∃ vm, A2.TA fr t₀ {N0} vm ∧ frSlot64 fr 0x30 = {n64(N1)} "
               f"∧ A2.Inc fr 0x480 {N1} {K1} k2"),
    # check_n_master, the two memcpys
    "L297e": S(f"{TWO} ∧ {NB1} ∧ {R12} ∧ {R15} ∧ frSlot64 fr 0x40 = arg0 t₀ "
               f"∧ frSlot64 fr 0x30 = {n64(N1)} ∧ A2.Inc fr 0x480 {N1} {K1} k2 "
               f"∧ st.nm = BitVec.ofNat 32 ({N0} + {N1}) ∧ {r('r13', n64(N0 + ' + ' + N1))} "
               f"∧ (s.regs.get64 .r14).setWidth 8 = BitVec.ofNat 8 (u8 a.sp 2) ∧ u8 a.sp 2 < {N0} + {N1} "
               f"∧ {r('rdi', 'arg1 t₀ + 0x4c1f0#64')} ∧ {r('rbx', n64(N0 + ' + 1'))} "
               f"∧ {r('rdx', n64('2 * (' + N0 + ' + 1)'))}"),
    "L298a": S(f"{TWO} ∧ {NB1} ∧ {R12} ∧ frSlot64 fr 0x40 = arg0 t₀ "
               f"∧ frSlot64 fr 0x30 = {n64(N1)} ∧ A2.Inc fr 0x480 {N1} {K1} k2 "
               f"∧ st.nm = BitVec.ofNat 32 ({N0} + {N1}) ∧ {r('r13', n64(N0 + ' + ' + N1))} "
               f"∧ (s.regs.get64 .r14).setWidth 8 = BitVec.ofNat 8 (u8 a.sp 2) ∧ u8 a.sp 2 < {N0} + {N1} "
               f"∧ {r('rbx', n64(N0 + ' + 1'))} "
               f"∧ ∀ i, i ≤ {N0} → (u16 st.fm i : Int) = A2.fv fr 0x400 i"),
    "L29a3": S(f"{TWO} ∧ {NB1} ∧ {R12} ∧ frSlot64 fr 0x40 = arg0 t₀ "
               f"∧ A2.Inc fr 0x480 {N1} {K1} k2 "
               f"∧ st.nm = BitVec.ofNat 32 ({N0} + {N1}) ∧ {r('r13', n64(N0 + ' + ' + N1))} "
               f"∧ (s.regs.get64 .r14).setWidth 8 = BitVec.ofNat 8 (u8 a.sp 2) ∧ u8 a.sp 2 < {N0} + {N1} "
               f"∧ (∀ i, i ≤ {N0} → (u16 st.fm i : Int) = A2.fv fr 0x400 i) "
               f"∧ {r('rdi', 'arg1 t₀ + 0x4c1f0#64 + ' + n64('2 * (' + N0 + ' + 1)'))} "
               f"∧ {r('rsi', RBP + ' - 0xee#64')} ∧ {r('rdx', n64('2 * ' + N1))}"),
    "L29a8": S(f"{TWO} ∧ {NB1} ∧ {R12} ∧ frSlot64 fr 0x40 = arg0 t₀ "
               f"∧ A2.Inc fr 0x480 {N1} {K1} k2 "
               f"∧ st.nm = BitVec.ofNat 32 ({N0} + {N1}) ∧ {r('r13', n64(N0 + ' + ' + N1))} "
               f"∧ (s.regs.get64 .r14).setWidth 8 = BitVec.ofNat 8 (u8 a.sp 2) ∧ u8 a.sp 2 < {N0} + {N1} "
               f"∧ (∀ i, i ≤ {N0} → (u16 st.fm i : Int) = A2.fv fr 0x400 i) "
               f"∧ (∀ i, 1 ≤ i → i ≤ {N1} → (u16 st.fm ({N0} + i) : Int) = A2.fv fr 0x480 i)"),
})

for l in ["L2130", "L2166", "L2197", "L21a9", "L21ba"]:
  VARS[l] = "[(s.regs.get64 .rsi).toNat - (s.regs.get64 .rdx).toNat, 0, 0]"
VARS["L2200"] = "[(s.regs.get64 .rcx).toNat - (s.regs.get64 .rsi).toNat, 0, 0]"
VARS["L2289"] = "[(s.regs.get64 .rsi).toNat - (s.regs.get64 .rdi).toNat, 0, 0]"
VARS["L2310"] = "[(s.regs.get64 .rdx).toNat - (s.regs.get64 .rsi).toNat, 0, 0]"
VARS["L2340"] = "[(s.regs.get64 .rax).toNat - (s.regs.get64 .rcx).toNat, 0, 0]"
for l in ["L289b", "L28e7", "L292b"]:
  VARS[l] = "[0x40 - (s.regs.get64 .rcx).toNat, 0, 0]"
