import Kraken.X64.Parser
import Kraken.MachineWP
import Kraken.Rules.IndirectCall
import Kraken.Rules.IntMisc
import Kraken.Rules.PackedSse
import Kraken.Rules.ScalarFloat
import Kraken.Rules.CallFrame
import Kraken.Rules.CfgList
import Kraken.Rules.LeafLemmas
import Kraken.Rules.FrameLemmas
import Kraken.Rules.HelperLemmas
import Kraken.X64.Examples.Sbr.Spec
import Kraken.X64.Examples.Sbr.XGenText

/-!
# `sbr_x_gen` as a `ProcSpec`

FFmpeg `sbr_x_gen` (`libavcodec/aacsbr_template.c:1524-1558`, gcc -O2), memory
safety as a `ProcSpec` (`XGenSpec k`, stated in `Spec.lean`): from `XGenPre` (the SysV `CallPre` with
`0x60 + k` bytes of stack, the four arrays `X`, `X_high`, `X_low`, `Y0/Y1` of
`XGenData`, the read-only decoder fields of `XGenSbrL`, and the `SbrWF`
clauses `XGenC`) every run returns with `XGenPost` (the `CallPost`: the same
footprint, the saved registers and `rbp` restored), with no fault.

* Proof: `ProcSpec.of_cfg_post` over the 49-block CFG; one `blk_<label>`
  lemma per block, each with its own `maxHeartbeats`. The table (`table`)
  carries the loop invariants (`ALoop`, `BLoop`, `CLoop`, `DLoop`); the frame
  shapes `FrEL`/`FrE1L`/`FrML`/`FrBL` describe the ten stack slots at each
  stage.
* `SbrWF` clauses needed (all justified by the decoder, `aacsbr_template.c`):
  `ch < 2`; `kx[0], kx[1] ≤ 32`; `kx[i] + m[i] ≤ 64`;
  `t_env_num_env_old ≤ 19` (so `i_Temp = 2 te - 32 ∈ {0,2,4,6}` when
  `te ≥ 17`, `aacsbr_template.c:681` bounds `te` by the envelope count).
  Dropping `te ≤ 19` breaks `blk_e1`'s `i_Temp` table entry (and the loop
  bounds downstream).
* Assumed callee: `memset` (`MemsetSpec k`: writes `dst[n]`, nothing else,
  `k` bytes of stack).
* Kernel pitfall: a `simp [toNat_*]; omega` over a goal with a negative
  64-bit literal (`18446744073709551584#64`, from `lea -0x20`) exhausts
  memory (>12 GB) at elaboration/kernel; `xg_lea_iT` does it by cases and
  `decide` in milliseconds. Likewise `exact True.intro`/`grind` against the
  seven-store prologue memory goal times out at `isDefEq`; `blk_entry`
  threads `Block.storeInt_val` explicitly.
* The same blow-up in `blk_d3`: facts over `(m + 4294967295) % 4294967296`
  (the 32-bit `lea -1`/`add $4` of the row counter) and a `toInt` proved by
  `toNat`/`simp` and `omega` exceeded 12 GB. The row `m` takes eight values
  (`m ≤ 28`, `4 ∣ 32 - m`), so each fact is `rcases … <;> decide`. The `Int`
  hypothesis `↑m + 3 < 31` that `CondCode.interp_l_cmp_toInt32` leaves was not
  usable by `omega` (the cast stayed an atom); it is converted the same way.
* `grind` side conditions: extra `toNat` facts in the context (e.g.
  `(ofNat (256 m)).toNat = 256 m`) make `grind` fail on the store goals of
  `blk_Lbe00`/`blk_d2`; they are introduced only in the exit goal and cleared
  before `grind`. `assumption` inside a `first` chain can hit `maxRecDepth`
  (defeq on shifted literals); `exact hm`/`omega` go first.
* Field loads: `*sbr` fields sit behind `XGenData` in `T`, so `m[1]` at
  `+0x60` is four `Split.right` deep; a wrong depth shows up as a `whnf`
  heartbeat timeout, not a type error.
-/

open Kraken.X64.Parser
open Kraken
open Kraken.SysV
open Std.WP
open Mem
open MachineWP

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Local lemmas

The general lemmas first written here (the `cmp` flag readings
`BitVec.sub_cf_eq_decide_lt`, `BitVec.sub_beq_zero`, …, the `BitVec.ofNat`
offset folding, `Mem.Val.loadInt_prefix`, `Int.toBytes8_take1`,
`Mem.Blocks.Inside.of_sub2`, the `inc` and `shl $i, %r64` rules) are in
`Kraken.Rules.HelperLemmas`. -/

/-- 32-bit `dec` of a small even value, zero-extended twice (sbr_x_gen Lb9cc). -/
theorem BitVec.zext32_twice_ofNat_add_neg_one (n : Nat) (h : n = 2 ∨ n = 4 ∨ n = 6) :
    BitVec.setWidth 64
      (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 n + (-1 : Int64).toBitVec)))) =
    BitVec.ofNat 64 (n - 1) := by
  rcases h with rfl | rfl | rfl <;> rfl

theorem BitVec.zext32_twice_64 :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (64#64)))) = 64#64 := by
  rfl


namespace Kraken.Examples.Sbr.XGen

open scoped Kraken.LeafLemmas.Offset Kraken.HelperLemmas.Offset2

variable [CodeEnv]

abbrev K (n : Nat) : BitVec 64 := BitVec.ofNat 64 n

abbrev c8 (a v : BitVec 64) : Mem 64 → Prop := Int.toBytes 8 v.toInt =@ a

/-- The caller's memory behind the footprint: the return address and `R`. -/
def Rest (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) : Mem 64 → Prop :=
  RetCell ra (t₀.regs.get64 .rsp) ⋆ R

/-- The six saved registers (`rbp` at the top). -/
abbrev Sv (t₀ : MachineData) (K : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ K)))))

/-- The frame at entry: all ten slots blank. -/
abbrev FrEL (t₀ : MachineData) (K : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x50#64) ⋆ (8 ?@ (r - 0x48#64) ⋆ (8 ?@ (r - 0x40#64) ⋆ (8 ?@ (r - 0x38#64)
    ⋆ (8 ?@ (r - 0x30#64) ⋆ (8 ?@ (r - 0x28#64) ⋆ (8 ?@ (r - 0x20#64) ⋆ (8 ?@ (r - 0x18#64)
    ⋆ (8 ?@ (r - 0x10#64) ⋆ (8 ?@ (r - 0x8#64) ⋆ K)))))))))

/-- The frame after the prologue: `Y1` spilled, the registers saved. -/
abbrev FrE1L (t₀ : MachineData) (K : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x50#64) ⋆ (8 ?@ (r - 0x48#64) ⋆ (c8 (r - 0x40#64) (arg3 t₀) ⋆ (8 ?@ (r - 0x38#64)
    ⋆ Sv t₀ K)))

/-- The frame from the `memset` call on: `X` and `Y1` spilled. -/
abbrev FrML (t₀ : MachineData) (K : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x50#64) ⋆ (8 ?@ (r - 0x48#64) ⋆ (c8 (r - 0x40#64) (arg3 t₀) ⋆ (c8 (r - 0x38#64) (arg1 t₀)
    ⋆ Sv t₀ K)))

/-- The frame in the second loop: also `i_Temp` and `4 kx[0]` spilled. -/
abbrev FrBL (x : XGenArgs) (t₀ : MachineData) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  c8 (r - 0x50#64) (K (xgIT x)) ⋆ (c8 (r - 0x48#64) (K (4 * x.kx0.toNat))
    ⋆ (c8 (r - 0x40#64) (arg3 t₀) ⋆ (c8 (r - 0x38#64) (arg1 t₀) ⋆ Sv t₀ Kt)))

/-- Opaque regions (one atom each for `grind`), opened by the `_open` lemmas. -/
def SbrW (x : XGenArgs) (t₀ : MachineData) : Mem 64 → Prop := XGenSbrL x t₀ Std.ExtHashMap.emp
def FrMW (t₀ : MachineData) : Mem 64 → Prop := FrML t₀ Std.ExtHashMap.emp
def FrBW (x : XGenArgs) (t₀ : MachineData) : Mem 64 → Prop := FrBL x t₀ Std.ExtHashMap.emp

omit [CodeEnv] in
theorem SbrW_open (x : XGenArgs) (t₀ : MachineData) (K : Mem 64 → Prop) :
    SbrW x t₀ ⋆ K = XGenSbrL x t₀ K := by
  simp only [SbrW, XGenSbrL, Std.ExtHashMap.sep_assoc, Std.ExtHashMap.emp_sep]

omit [CodeEnv] in
theorem FrMW_open (t₀ : MachineData) (K : Mem 64 → Prop) : FrMW t₀ ⋆ K = FrML t₀ K := by
  simp only [FrMW, FrML, Sv, Std.ExtHashMap.sep_assoc, Std.ExtHashMap.emp_sep]

omit [CodeEnv] in
theorem FrBW_open (x : XGenArgs) (t₀ : MachineData) (K : Mem 64 → Prop) :
    FrBW x t₀ ⋆ K = FrBL x t₀ K := by
  simp only [FrBW, FrBL, Sv, Std.ExtHashMap.sep_assoc, Std.ExtHashMap.emp_sep]

/-- The memory at every label: the arrays, the fields, the slot of `memset`'s
return address and its reservation, the free slot at `rsp`, the frame `FR`
in front of the caller's memory. -/
abbrev T (x : XGenArgs) (k : Nat) (ra : Int64) (t₀ : MachineData)
    (FR : (Mem 64 → Prop) → Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  XGenData t₀ ⋆ (SbrW x t₀ ⋆ (8 ?@ (r - 0x60#64) ⋆ (Reserve k (r - 0x60#64)
    ⋆ (8 ?@ (r - 0x58#64) ⋆ FR (Rest x.R ra t₀)))))

abbrev kx0n (x : XGenArgs) : Nat := x.kx0.toNat
abbrev kx1n (x : XGenArgs) : Nat := x.kx1.toNat
abbrev m0n (x : XGenArgs) : Nat := x.m0.toNat
abbrev m1n (x : XGenArgs) : Nat := x.m1.toNat

/-- `rsp`, `rbp`, `rbx = sbr` in the body. -/
abbrev Base (t₀ s : MachineData) : Prop :=
  s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x58#64 ∧ s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64
    ∧ s.regs.get64 .rbx = arg0 t₀

/-- The first loop (`k < kx[0]`, rows `i < i_Temp` of `X_low`). -/
abbrev ALoop (x : XGenArgs) (t₀ s : MachineData) : Prop :=
  let k := (s.regs.get64 .rsi).toNat
  let iT := xgIT x
  Base t₀ s ∧ s.regs.get64 .r12 = arg4 t₀ ∧ s.regs.get64 .r13 = arg2 t₀
    ∧ s.regs.get64 .r14 = K iT ∧ 2 ≤ iT ∧ k < kx0n x
    ∧ s.regs.get64 .rcx = arg1 t₀ + K (0x2800 + 4 * k)
    ∧ s.regs.get64 .rdx = arg4 t₀ + K (0x24 + 320 * k)
    ∧ s.regs.get64 .rax = K (256 * iT) ∧ s.regs.get64 .rdi = K (256 * iT - 512)
    ∧ s.regs.get64 .r8 = K (256 * iT - 256)

/-- Its inner loop at row `3 j`. -/
abbrev AIn (x : XGenArgs) (t₀ s : MachineData) (d : Nat) : Prop :=
  let k := (s.regs.get64 .rsi).toNat
  let j := (s.regs.get64 .r10).toNat / 0x300
  ALoop x t₀ s ∧ s.regs.get64 .r10 = K (0x300 * j) ∧ 3 * j + d < xgIT x
    ∧ s.regs.get64 .r9 = arg4 t₀ + K (0x24 + 320 * k + 24 * j)

/-- The second loop (`kx[0] ≤ k < kx[0] + m[0]`, rows `i < i_Temp` of `Y0`). -/
abbrev BLoop (x : XGenArgs) (t₀ s : MachineData) : Prop :=
  let k := (s.regs.get64 .rsi).toNat
  let iT := xgIT x
  Base t₀ s ∧ s.regs.get64 .r12 = arg4 t₀ ∧ s.regs.get64 .r14 = K iT ∧ 2 ≤ iT
    ∧ kx0n x ≤ k ∧ k < kx0n x + m0n x
    ∧ s.regs.get64 .rax = K (iT - 1) ∧ s.regs.get64 .rcx = K 64 ∧ s.regs.get64 .rdi = K (iT / 4 * 4)
    ∧ s.regs.get64 .r9 = arg1 t₀ + K (0x2900 + 4 * (k - kx0n x))
    ∧ s.regs.get64 .r10 = arg1 t₀ + K (4 * k)
    ∧ s.regs.get64 .r11 = arg2 t₀ + K (0x4000 + 8 * k)
    ∧ s.regs.get64 .r13 = arg2 t₀ + K (0x4604 + 8 * (k - kx0n x))

/-- The third loop (`k < kx[1]`, rows `i_Temp ≤ i < 38` of `X_low`). -/
abbrev CLoop (x : XGenArgs) (t₀ s : MachineData) : Prop :=
  let k := (s.regs.get64 .rax).toNat
  let iT := xgIT x
  Base t₀ s ∧ s.regs.get64 .r14 = K iT ∧ k < kx1n x
    ∧ s.regs.get64 .rcx = K iT ∧ s.regs.get64 .rdx = 2#64 - K iT ∧ s.regs.get64 .rsi = K iT - 35#64
    ∧ s.regs.get64 .rdi = arg1 t₀ + K (256 * iT + 0x2600 + 4 * k)
    ∧ s.regs.get64 .r8 = arg4 t₀ + K (0x14 + 320 * k)
    ∧ s.regs.get64 .r9 = K (if iT % 4 = 0 then 0x40 else 0)
    ∧ s.regs.get64 .r10 = arg1 t₀ + K (4 * k)
    ∧ s.regs.get64 .r12 = arg4 t₀ + K (320 * k)

/-- `(-i_Temp) & 2`: 2 when the 32 - i_Temp rows of the fourth loop leave a
remainder of 2. -/
abbrev xgE (x : XGenArgs) : Nat := if xgIT x % 4 = 2 then 2 else 0

/-- The fourth loop (`kx[1] ≤ k < kx[1] + m[1]`, rows `i_Temp ≤ i < 32` of `Y1`). -/
abbrev DLoop (x : XGenArgs) (t₀ s : MachineData) : Prop :=
  let k := (s.regs.get64 .rax).toNat
  let iT := xgIT x
  Base t₀ s ∧ kx1n x ≤ k ∧ k < kx1n x + m1n x
    ∧ s.regs.get64 .rcx = K 64 ∧ s.regs.get64 .rdx = K iT ∧ s.regs.get64 .rsi = K (xgE x)
    ∧ s.regs.get64 .r14 = K (iT + 4294967267)
    ∧ s.regs.get64 .rdi = arg1 t₀ + K (256 * iT + 4 * k + 0x2600)
    ∧ s.regs.get64 .r8 = arg3 t₀ + K (512 * iT + 8 * k + 4)
    ∧ s.regs.get64 .r9 = K (256 * xgE x)
    ∧ (xgE x = 2 → s.regs.get64 .r10 = K (iT + 2))
    ∧ s.regs.get64 .r11 = arg1 t₀ + K (4 * k)
    ∧ s.regs.get64 .r15 = arg3 t₀ + K (8 * k + 0x604)

abbrev FM (t₀ : MachineData) : (Mem 64 → Prop) → Mem 64 → Prop := fun K => FrMW t₀ ⋆ K
abbrev FB (x : XGenArgs) (t₀ : MachineData) : (Mem 64 → Prop) → Mem 64 → Prop :=
  fun K => FrBW x t₀ ⋆ K

omit [CodeEnv] in
theorem xgIT_cases (x : XGenArgs) (h : x.te.toNat ≤ 19) :
    xgIT x = 0 ∨ xgIT x = 2 ∨ xgIT x = 4 ∨ xgIT x = 6 := by
  simp only [xgIT]; split <;> omega

/-- The table. -/
abbrev table (k : Nat) (x : XGenArgs) (ra : Int64) (t₀ : MachineData) :
    Label → MachineData → Prop
  | "sbr_x_gen", s => s = t₀ ∧ XGenC x t₀ ∧ (t₀.dmem =⋆ T x k ra t₀ (FrEL t₀))
  | "sbr_x_gen.e1", s => XGenC x t₀
      ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x58#64 ∧ s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64
      ∧ s.regs.get64 .rdi = arg0 t₀ ∧ s.regs.get64 .rsi = arg1 t₀ ∧ s.regs.get64 .rdx = arg2 t₀
      ∧ s.regs.get64 .r8 = arg4 t₀ ∧ s.regs.get64 .r9 = arg5 t₀
      ∧ (s.dmem =⋆ T x k ra t₀ (FrE1L t₀))
  | "sbr_x_gen.e2", s => XGenC x t₀ ∧ Base t₀ s
      ∧ s.regs.get64 .r12 = arg4 t₀ ∧ s.regs.get64 .r13 = arg2 t₀ ∧ s.regs.get64 .rsi = arg1 t₀
      ∧ s.regs.get64 .r15 = 0#64 ∧ s.regs.get64 .r14 = K (xgIT x)
      ∧ (s.dmem =⋆ T x k ra t₀ (FrE1L t₀))
  | "sbr_x_gen.m1", s => XGenC x t₀ ∧ Base t₀ s
      ∧ s.regs.get64 .r12 = arg4 t₀ ∧ s.regs.get64 .r13 = arg2 t₀
      ∧ s.regs.get64 .r15 = 0#64 ∧ s.regs.get64 .r14 = K (xgIT x)
      ∧ (s.dmem =⋆ T x k ra t₀ (FM t₀))
  | "sbr_x_gen.a0", s => XGenC x t₀ ∧ Base t₀ s
      ∧ s.regs.get64 .r12 = arg4 t₀ ∧ s.regs.get64 .r13 = arg2 t₀
      ∧ s.regs.get64 .r14 = K (xgIT x) ∧ 2 ≤ xgIT x ∧ 0 < kx0n x
      ∧ (s.dmem =⋆ T x k ra t₀ (FM t₀))
  | "sbr_x_gen.Lb910", s => XGenC x t₀ ∧ ALoop x t₀ s ∧ (s.dmem =⋆ T x k ra t₀ (FM t₀))
  | "sbr_x_gen.Lb920", s => XGenC x t₀ ∧ AIn x t₀ s 0 ∧ (s.dmem =⋆ T x k ra t₀ (FM t₀))
  | "sbr_x_gen.a2", s => XGenC x t₀ ∧ AIn x t₀ s 1 ∧ (s.dmem =⋆ T x k ra t₀ (FM t₀))
  | "sbr_x_gen.a3", s => XGenC x t₀ ∧ AIn x t₀ s 2 ∧ (s.dmem =⋆ T x k ra t₀ (FM t₀))
  | "sbr_x_gen.Lb9a6", s => XGenC x t₀ ∧ ALoop x t₀ s ∧ (s.dmem =⋆ T x k ra t₀ (FM t₀))
  | "sbr_x_gen.Lb9cc", s => XGenC x t₀ ∧ Base t₀ s
      ∧ s.regs.get64 .r12 = arg4 t₀ ∧ s.regs.get64 .r13 = arg2 t₀
      ∧ s.regs.get64 .r14 = K (xgIT x)
      ∧ s.regs.get64 .rsi = K (kx0n x) ∧ s.regs.get64 .r15 = K (kx0n x)
      ∧ (s.dmem =⋆ T x k ra t₀ (FM t₀))
  | "sbr_x_gen.b0", s => XGenC x t₀ ∧ Base t₀ s
      ∧ s.regs.get64 .r12 = arg4 t₀ ∧ s.regs.get64 .r13 = arg2 t₀
      ∧ s.regs.get64 .r14 = K (xgIT x) ∧ 2 ≤ xgIT x
      ∧ s.regs.get64 .rsi = K (kx0n x) ∧ 0 < m0n x
      ∧ s.regs.get64 .rax = K (xgIT x - 1) ∧ s.regs.get64 .rcx = K 64
      ∧ (s.dmem =⋆ T x k ra t₀ (FM t₀))
  | "sbr_x_gen.Lba50", s => XGenC x t₀ ∧ BLoop x t₀ s ∧ (s.dmem =⋆ T x k ra t₀ (FB x t₀))
  | "sbr_x_gen.Lba70", s => XGenC x t₀ ∧ BLoop x t₀ s ∧ 4 ≤ xgIT x
      ∧ (s.dmem =⋆ T x k ra t₀ (FB x t₀))
  | "sbr_x_gen.Lba80", s => XGenC x t₀ ∧ BLoop x t₀ s ∧ 4 ≤ xgIT x
      ∧ s.regs.get64 .r15 = 0#64 ∧ s.regs.get64 .r8 = K (4 * kx0n x)
      ∧ (s.dmem =⋆ T x k ra t₀ (FB x t₀))
  | "sbr_x_gen.b2", s => XGenC x t₀ ∧ BLoop x t₀ s ∧ 4 ≤ xgIT x
      ∧ s.regs.get64 .r15 = 0#64 ∧ s.regs.get64 .r8 = K (4 * kx0n x)
      ∧ (s.dmem =⋆ T x k ra t₀ (FB x t₀))
  | "sbr_x_gen.b3", s => XGenC x t₀ ∧ BLoop x t₀ s ∧ 4 ≤ xgIT x
      ∧ s.regs.get64 .r15 = 0#64 ∧ s.regs.get64 .r8 = K (4 * kx0n x)
      ∧ (s.dmem =⋆ T x k ra t₀ (FB x t₀))
  | "sbr_x_gen.Lbb30", s => XGenC x t₀ ∧ BLoop x t₀ s ∧ xgIT x % 4 = 2
      ∧ s.regs.get64 .r15 = K (xgIT x - 2)
      ∧ (s.dmem =⋆ T x k ra t₀ (FB x t₀))
  | "sbr_x_gen.Lbb50", s => XGenC x t₀ ∧ BLoop x t₀ s ∧ xgIT x % 4 = 2
      ∧ s.regs.get64 .rdx = K (256 * ((s.regs.get64 .rdx).toNat / 256))
      ∧ (s.regs.get64 .rdx).toNat / 256 < 2
      ∧ s.regs.get64 .r8 = arg1 t₀ + K (4 * (s.regs.get64 .rsi).toNat + 256 * (xgIT x - 2))
      ∧ s.regs.get64 .r15 = arg2 t₀ + K (0x4000 + 8 * (s.regs.get64 .rsi).toNat + 512 * (xgIT x - 2))
      ∧ (s.dmem =⋆ T x k ra t₀ (FB x t₀))
  | "sbr_x_gen.Lbb7d", s => XGenC x t₀ ∧ BLoop x t₀ s ∧ (s.dmem =⋆ T x k ra t₀ (FB x t₀))
  | "sbr_x_gen.Lbba9", s => XGenC x t₀ ∧ Base t₀ s
      ∧ s.regs.get64 .r12 = arg4 t₀ ∧ s.regs.get64 .r14 = K (xgIT x)
      ∧ (s.dmem =⋆ T x k ra t₀ (FM t₀))
  | "sbr_x_gen.c0", s => XGenC x t₀ ∧ Base t₀ s
      ∧ s.regs.get64 .r12 = arg4 t₀ ∧ s.regs.get64 .r14 = K (xgIT x) ∧ 0 < kx1n x
      ∧ (s.dmem =⋆ T x k ra t₀ (FM t₀))
  | "sbr_x_gen.Lbc00", s => XGenC x t₀ ∧ CLoop x t₀ s ∧ (s.dmem =⋆ T x k ra t₀ (FM t₀))
  | "sbr_x_gen.Lbc10", s => XGenC x t₀ ∧ CLoop x t₀ s ∧ xgIT x % 4 = 0
      ∧ s.regs.get64 .r15 = K (32 * ((s.regs.get64 .r15).toNat / 32))
      ∧ (s.regs.get64 .r15).toNat / 32 < 2
      ∧ s.regs.get64 .r11 = K (xgIT x + (s.regs.get64 .r15).toNat / 32)
      ∧ (s.dmem =⋆ T x k ra t₀ (FM t₀))
  | "sbr_x_gen.Lbc39", s => XGenC x t₀ ∧ CLoop x t₀ s
      ∧ s.regs.get64 .r11 = K (xgIT x + (if xgIT x % 4 = 0 then 2 else 0))
      ∧ (s.dmem =⋆ T x k ra t₀ (FM t₀))
  | "sbr_x_gen.Lbc50", s => XGenC x t₀ ∧ CLoop x t₀ s
      ∧ s.regs.get64 .r15 = K ((s.regs.get64 .r15).toNat) ∧ xgIT x + 5 ≤ (s.regs.get64 .r15).toNat
      ∧ (s.regs.get64 .r15).toNat + 4 ≤ 43 ∧ (43 - (s.regs.get64 .r15).toNat) % 4 = 0
      ∧ s.regs.get64 .r11 = arg1 t₀ + K (4 * (s.regs.get64 .rax).toNat + 256 * ((s.regs.get64 .r15).toNat - 5))
      ∧ (s.dmem =⋆ T x k ra t₀ (FM t₀))
  | "sbr_x_gen.c2", s => XGenC x t₀ ∧ CLoop x t₀ s
      ∧ xgIT x + 5 ≤ (s.regs.get64 .r15).toNat
      ∧ (s.regs.get64 .r15).toNat + 4 ≤ 43 ∧ (43 - (s.regs.get64 .r15).toNat) % 4 = 0
      ∧ s.regs.get64 .r11 = arg1 t₀ + K (4 * (s.regs.get64 .rax).toNat + 256 * ((s.regs.get64 .r15).toNat - 5))
      ∧ (s.dmem =⋆ T x k ra t₀ (FM t₀))
  | "sbr_x_gen.c3", s => XGenC x t₀ ∧ CLoop x t₀ s
      ∧ xgIT x + 5 ≤ (s.regs.get64 .r15).toNat
      ∧ (s.regs.get64 .r15).toNat + 4 ≤ 43 ∧ (43 - (s.regs.get64 .r15).toNat) % 4 = 0
      ∧ s.regs.get64 .r11 = arg1 t₀ + K (4 * (s.regs.get64 .rax).toNat + 256 * ((s.regs.get64 .r15).toNat - 5))
      ∧ (s.dmem =⋆ T x k ra t₀ (FM t₀))
  | "sbr_x_gen.Lbce0", s => XGenC x t₀ ∧ CLoop x t₀ s ∧ (s.dmem =⋆ T x k ra t₀ (FM t₀))
  | "sbr_x_gen.Lbd11", s => XGenC x t₀ ∧ Base t₀ s ∧ s.regs.get64 .r14 = K (xgIT x) ∧ kx1n x = 0
      ∧ (s.dmem =⋆ T x k ra t₀ (FM t₀))
  | "sbr_x_gen.Lbd16", s => XGenC x t₀ ∧ Base t₀ s ∧ s.regs.get64 .r14 = K (xgIT x)
      ∧ s.regs.get64 .rax = K (kx1n x) ∧ s.regs.get64 .r11 = K (kx1n x)
      ∧ (s.dmem =⋆ T x k ra t₀ (FM t₀))
  | "sbr_x_gen.d0", s => XGenC x t₀ ∧ Base t₀ s ∧ s.regs.get64 .r14 = K (xgIT x)
      ∧ s.regs.get64 .rax = K (kx1n x) ∧ 0 < m1n x ∧ s.regs.get64 .rcx = K 64
      ∧ (s.dmem =⋆ T x k ra t₀ (FM t₀))
  | "sbr_x_gen.d1", s => XGenC x t₀ ∧ Base t₀ s
      ∧ s.regs.get64 .rax = K (kx1n x) ∧ 0 < m1n x ∧ s.regs.get64 .rcx = K 64
      ∧ s.regs.get64 .rdx = K (xgIT x) ∧ s.regs.get64 .rsi = K (xgE x)
      ∧ s.regs.get64 .r14 = K (xgIT x + 4294967267)
      ∧ s.regs.get64 .rdi = arg1 t₀ + K (256 * xgIT x + 4 * kx1n x + 0x2600)
      ∧ s.regs.get64 .r11 = arg1 t₀
      ∧ (s.dmem =⋆ T x k ra t₀ (FM t₀))
  | "sbr_x_gen.Lbdb0", s => XGenC x t₀ ∧ DLoop x t₀ s ∧ (s.dmem =⋆ T x k ra t₀ (FM t₀))
  | "sbr_x_gen.Lbdc0", s => XGenC x t₀ ∧ DLoop x t₀ s ∧ xgE x = 2
      ∧ s.regs.get64 .r12 = K (256 * ((s.regs.get64 .r12).toNat / 256))
      ∧ (s.regs.get64 .r12).toNat / 256 < 2
      ∧ (s.dmem =⋆ T x k ra t₀ (FM t₀))
  | "sbr_x_gen.Lbdec", s => XGenC x t₀ ∧ DLoop x t₀ s ∧ s.regs.get64 .r12 = K (xgIT x + xgE x)
      ∧ (s.dmem =⋆ T x k ra t₀ (FM t₀))
  | "sbr_x_gen.Lbe00", s => XGenC x t₀ ∧ DLoop x t₀ s
      ∧ s.regs.get64 .r12 = K (256 * ((s.regs.get64 .r12).toNat / 256))
      ∧ xgIT x ≤ (s.regs.get64 .r12).toNat / 256 ∧ (s.regs.get64 .r12).toNat / 256 + 4 ≤ 32
      ∧ (32 - (s.regs.get64 .r12).toNat / 256) % 4 = 0
      ∧ s.regs.get64 .r13 = K (((s.regs.get64 .r12).toNat / 256 + 4294967295) % 4294967296)
      ∧ (s.dmem =⋆ T x k ra t₀ (FM t₀))
  | "sbr_x_gen.d2", s => XGenC x t₀ ∧ DLoop x t₀ s
      ∧ s.regs.get64 .r12 = K (256 * ((s.regs.get64 .r12).toNat / 256))
      ∧ xgIT x ≤ (s.regs.get64 .r12).toNat / 256 ∧ (s.regs.get64 .r12).toNat / 256 + 4 ≤ 32
      ∧ (32 - (s.regs.get64 .r12).toNat / 256) % 4 = 0
      ∧ s.regs.get64 .r13 = K (((s.regs.get64 .r12).toNat / 256 + 4294967295) % 4294967296)
      ∧ (s.dmem =⋆ T x k ra t₀ (FM t₀))
  | "sbr_x_gen.d3", s => XGenC x t₀ ∧ DLoop x t₀ s
      ∧ s.regs.get64 .r12 = K (256 * ((s.regs.get64 .r12).toNat / 256))
      ∧ xgIT x ≤ (s.regs.get64 .r12).toNat / 256 ∧ (s.regs.get64 .r12).toNat / 256 + 4 ≤ 32
      ∧ (32 - (s.regs.get64 .r12).toNat / 256) % 4 = 0
      ∧ s.regs.get64 .r13 = K (((s.regs.get64 .r12).toNat / 256 + 4294967295) % 4294967296)
      ∧ (s.dmem =⋆ T x k ra t₀ (FM t₀))
  | "sbr_x_gen.Lbeaa", s => XGenC x t₀ ∧ DLoop x t₀ s ∧ (s.dmem =⋆ T x k ra t₀ (FM t₀))
  | "sbr_x_gen.Lbed8", s =>
      s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x58#64 ∧ s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64
      ∧ (s.dmem =⋆ T x k ra t₀ (FM t₀))
  | "sbr_x_gen.done", s =>
      s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp
      ∧ SavedRegs t₀ s ∧ (s.dmem =⋆ T x k ra t₀ (FM t₀))
  | _, _ => False

/-- The variant: a phase base (the four loops, later ones lower), then
`64 * (64 - k)` for the column `k`, then the row part (63 before the inner
loop, decreasing along it, 0 at the latch); 0 at the exit. -/
abbrev var : Label → MachineData → Nat
  | "sbr_x_gen", _ => 5 * 8192
  | "sbr_x_gen.e1", _ => 5 * 8192
  | "sbr_x_gen.e2", _ => 5 * 8192
  | "sbr_x_gen.m1", _ => 5 * 8192
  | "sbr_x_gen.a0", _ => 5 * 8192
  | "sbr_x_gen.Lb910", s => 4 * 8192 + 64 * (64 - (s.regs.get64 .rsi).toNat) + 63
  | "sbr_x_gen.Lb920", s => 4 * 8192 + 64 * (64 - (s.regs.get64 .rsi).toNat) + 62
      - (s.regs.get64 .r10).toNat / 0x300 * 3
  | "sbr_x_gen.a2", s => 4 * 8192 + 64 * (64 - (s.regs.get64 .rsi).toNat) + 62
      - (s.regs.get64 .r10).toNat / 0x300 * 3
  | "sbr_x_gen.a3", s => 4 * 8192 + 64 * (64 - (s.regs.get64 .rsi).toNat) + 62
      - (s.regs.get64 .r10).toNat / 0x300 * 3
  | "sbr_x_gen.Lb9a6", s => 4 * 8192 + 64 * (64 - (s.regs.get64 .rsi).toNat)
  | "sbr_x_gen.Lb9cc", _ => 3 * 8192 + 64 * 64 + 63
  | "sbr_x_gen.b0", _ => 3 * 8192 + 64 * 64 + 63
  | "sbr_x_gen.Lba50", s => 3 * 8192 + 64 * (64 - (s.regs.get64 .rsi).toNat) + 63
  | "sbr_x_gen.Lba70", s => 3 * 8192 + 64 * (64 - (s.regs.get64 .rsi).toNat) + 63
  | "sbr_x_gen.Lba80", s => 3 * 8192 + 64 * (64 - (s.regs.get64 .rsi).toNat) + 62
      - (s.regs.get64 .r15).toNat
  | "sbr_x_gen.b2", s => 3 * 8192 + 64 * (64 - (s.regs.get64 .rsi).toNat) + 62
      - (s.regs.get64 .r15).toNat
  | "sbr_x_gen.b3", s => 3 * 8192 + 64 * (64 - (s.regs.get64 .rsi).toNat) + 62
      - (s.regs.get64 .r15).toNat
  | "sbr_x_gen.Lbb30", s => 3 * 8192 + 64 * (64 - (s.regs.get64 .rsi).toNat) + 50
  | "sbr_x_gen.Lbb50", s => 3 * 8192 + 64 * (64 - (s.regs.get64 .rsi).toNat) + 49
      - (s.regs.get64 .rdx).toNat / 256
  | "sbr_x_gen.Lbb7d", s => 3 * 8192 + 64 * (64 - (s.regs.get64 .rsi).toNat)
  | "sbr_x_gen.Lbba9", _ => 2 * 8192 + 64 * 64 + 63
  | "sbr_x_gen.c0", _ => 2 * 8192 + 64 * 64 + 63
  | "sbr_x_gen.Lbc00", s => 2 * 8192 + 64 * (64 - (s.regs.get64 .rax).toNat) + 63
  | "sbr_x_gen.Lbc10", s => 2 * 8192 + 64 * (64 - (s.regs.get64 .rax).toNat) + 62
      - (s.regs.get64 .r15).toNat / 32
  | "sbr_x_gen.Lbc39", s => 2 * 8192 + 64 * (64 - (s.regs.get64 .rax).toNat) + 55
  | "sbr_x_gen.Lbc50", s => 2 * 8192 + 64 * (64 - (s.regs.get64 .rax).toNat) + 50
      - (s.regs.get64 .r15).toNat
  | "sbr_x_gen.c2", s => 2 * 8192 + 64 * (64 - (s.regs.get64 .rax).toNat) + 50
      - (s.regs.get64 .r15).toNat
  | "sbr_x_gen.c3", s => 2 * 8192 + 64 * (64 - (s.regs.get64 .rax).toNat) + 50
      - (s.regs.get64 .r15).toNat
  | "sbr_x_gen.Lbce0", s => 2 * 8192 + 64 * (64 - (s.regs.get64 .rax).toNat)
  | "sbr_x_gen.Lbd11", _ => 8192 + 64 * 64 + 63
  | "sbr_x_gen.Lbd16", _ => 8192 + 64 * 64 + 63
  | "sbr_x_gen.d0", _ => 8192 + 64 * 64 + 63
  | "sbr_x_gen.d1", _ => 8192 + 64 * 64 + 63
  | "sbr_x_gen.Lbdb0", s => 8192 + 64 * (64 - (s.regs.get64 .rax).toNat) + 63
  | "sbr_x_gen.Lbdc0", s => 8192 + 64 * (64 - (s.regs.get64 .rax).toNat) + 62
      - (s.regs.get64 .r12).toNat / 256
  | "sbr_x_gen.Lbdec", s => 8192 + 64 * (64 - (s.regs.get64 .rax).toNat) + 55
  | "sbr_x_gen.Lbe00", s => 8192 + 64 * (64 - (s.regs.get64 .rax).toNat) + 50
      - (s.regs.get64 .r12).toNat / 256
  | "sbr_x_gen.d2", s => 8192 + 64 * (64 - (s.regs.get64 .rax).toNat) + 50
      - (s.regs.get64 .r12).toNat / 256
  | "sbr_x_gen.d3", s => 8192 + 64 * (64 - (s.regs.get64 .rax).toNat) + 50
      - (s.regs.get64 .r12).toNat / 256
  | "sbr_x_gen.Lbeaa", s => 8192 + 64 * (64 - (s.regs.get64 .rax).toNat)
  | "sbr_x_gen.Lbed8", _ => 0
  | "sbr_x_gen.done", _ => 0
  | _, _ => 2 ^ 64

/-- What the exit block leaves. -/
abbrev Post' (k : Nat) (x : XGenArgs) (_ra : Int64) (t₀ s : MachineData) : Prop :=
  let r := t₀.regs.get64 .rsp
  s.regs.get64 .rsp = r + 8 ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp ∧ SavedRegs t₀ s
  ∧ (s.dmem =⋆ XGenData t₀ ⋆ (SbrW x t₀ ⋆ (8 ?@ (r - 0x60#64) ⋆ (Reserve k (r - 0x60#64)
    ⋆ (8 ?@ (r - 0x58#64) ⋆ (FrMW t₀ ⋆ (8 ?@ r ⋆ x.R)))))))

omit [CodeEnv] in
/-- `lea -0x20(%rax,%rax)` on `te ∈ [17, 19]`: `i_Temp = 2 te - 32` (by cases: `omega`
on the `toNat` form exhausts memory on the literal `2^64 - 32`). -/
theorem xg_lea_iT (t : BitVec 8) (h1 : 17 ≤ t.toNat) (h2 : t.toNat ≤ 19) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32
      (BitVec.setWidth 64 (BitVec.setWidth 32 t) + BitVec.setWidth 64 (BitVec.setWidth 32 t) +
        18446744073709551584#64)))) = BitVec.ofNat 64 (2 * t.toNat - 32) := by
  have : t = 17#8 ∨ t = 18#8 ∨ t = 19#8 := by
    rcases (by omega : t.toNat = 17 ∨ t.toNat = 18 ∨ t.toNat = 19) with h|h|h
    · exact Or.inl (BitVec.eq_of_toNat_eq h)
    · exact Or.inr (Or.inl (BitVec.eq_of_toNat_eq h))
    · exact Or.inr (Or.inr (BitVec.eq_of_toNat_eq h))
  rcases this with rfl|rfl|rfl <;> decide

omit [CodeEnv] in
/-- `mov %r14d,%eax; shl $8,%rax` then an offset, folded. -/
theorem xg_shl8_add (n d : Nat) (hn : n < 2 ^ 24) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 n)) <<< 8 + BitVec.ofNat 64 d
      = BitVec.ofNat 64 (256 * n + d) := by
  apply BitVec.eq_of_toNat_eq
  simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_shiftLeft,
    Nat.shiftLeft_eq]
  omega

omit [CodeEnv] in
omit [CodeEnv] in
/-- `memset(X, 0, 0x4c00)` carves `X` off the data. -/
theorem XGenData_carve_memset (t : MachineData) (a : BitVec 64) (n : Nat) (ha : a = arg1 t)
    (hn : n = 0x4c00) : ∃ H, XGenData t = Blocks [(a, n)] ⋆ H :=
  ⟨Blocks [(arg4 t, 10240), (arg2 t, 19456), (arg3 t, 19456)], by
    subst ha hn; simp only [XGenData, Blocks]⟩

omit [CodeEnv] in
theorem xg_toNat_one64 : (1 : BitVec 64).toNat = 1 := rfl

/-- A register equation by the values: both sides' `toNat`, then `omega`. -/
macro "xg_bvext" : tactic =>
  `(tactic| (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_ofNat,
      xg_toNat_one64, BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
      Nat.reducePow, Nat.reduceMod] <;> omega))

/-- A `Nat` goal over register values: expand `toNat` of sums, then `omega`. -/
macro "xg_nat" : tactic =>
  `(tactic| (simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_ofNat, xg_toNat_one64,
      BitVec.toNat_setWidth, Nat.reducePow]; omega))

omit [CodeEnv] in
/-- `movslq %r14d,%rcx` of a small value. -/
theorem xg_sext32 (v : BitVec 64) (n : Nat) (h : v = BitVec.ofNat 64 n) (hn : n < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.setWidth 32 v) = BitVec.ofNat 64 n := by
  subst h
  rw [BitVec.signExtend_eq_setWidth_of_msb_false]
  · apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  · rw [BitVec.msb_eq_decide]; simp -implicitDefEqProofs only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; simp; omega

omit [CodeEnv] in
/-- A left shift of a small literal value. -/
theorem xg_shl_ofNat (n k : Nat) (h : n * 2 ^ k < 2 ^ 64) :
    BitVec.ofNat 64 n <<< k = BitVec.ofNat 64 (n * 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp -implicitDefEqProofs only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (a := n) (by
    have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have : n ≤ n * 2 ^ k := Nat.le_mul_of_pos_right n this
    omega)]

/-- `grind_cells` without model-based theory combination. -/
macro "grind_cells'" : tactic =>
  `(tactic| (
      repeat (with_reducible apply Mem.loadInt_isSome_storeInt)
      grind (ematch := 400) (gen := 400) (instances := 20000) (mbtc := false)
      [-BitVec.toInt_eq_toNat_of_msb, -BitVec.toInt_eq_toNat_bmod]))

/-- A store chain into the array blocks at the head of the frame: peel each store with
`Mem.Blocks.storeInt` (the `Blocks` atom is the tree's head), then close the base with the
frame hypothesis and the `Inside` side goals with `grind_cells'`. -/
macro "xg_bstore" : tactic =>
  `(tactic| (
      refine Mem.Blocks.storeInt ?_ ?_ _
      repeat (refine Mem.Blocks.storeInt ?_ ?_ _)
      all_goals (first | with_reducible assumption | grind_cells')))

/-- The block obligation of `ProcSpec.of_cfg_post` at label `l` of `body`. -/
abbrev BlockOb (k : Nat) (x : XGenArgs) (ra : Int64) (t₀ : MachineData) (l : Label) : Prop :=
  ∀ blk, Program.blockAt body l = some blk → ∀ n : Nat,
    ⦃ fun s => table k x ra t₀ l s ∧ var l s = n ⦄ blk.body
    ⦃ (match blk.next with
       | some l' => fun _ s => table k x ra t₀ l' s ∧ var l' s ≤ n
       | none => fun _ _ => False);
      fun a s => Table.ofLabels (fun l' s => (Program.blockAt body l').isSome
          ∧ table k x ra t₀ l' s ∧ Program.EdgeLt body var l n l' s) a s
        ∨ (a = ra ∧ Post' k x ra t₀ s) ⦄

theorem blk_entry (k : Nat) (hk : k ≤ 2 ^ 32) (hms : MemsetSpec k) (x : XGenArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_x_gen" := by
  cfg_block
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨⟨rfl, hC, hm⟩, hn⟩ := hs₀
  clear hms
  vcgen
  all_goals try subst_vars
  all_goals try dsimp only at *
  all_goals call_simp
  all_goals try simp only [AddrIndex.offset64, Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm,
    BitVec.add_zero, Nat.reducePow, Nat.reduceMod, Nat.reduceSub] at *
  all_goals try simp (disch := omega) only [BitVec.sub_ofNat_sub_ofNat64, BitVec.sub_ofNat_add_ofNat64,
    Nat.reduceAdd, Nat.reduceSub, Nat.reducePow, BitVec.setWidth_eq]
  case vc1 => grind_cells'
  case vc2 => grind_cells'
  case vc3 => grind_cells'
  case vc4 => grind_cells'
  case vc5 => grind_cells'
  case vc6 => grind_cells'
  case vc7 => grind_cells'
  case vc8 =>
    exfalso
    rename_i hf
    simp only [CondCode.interp_nc, CondCode.interp_c, StatusFlags.cf_from_result, BitVec.unsigned_eq,
      BitVec.sub_cf32_eq_decide_lt, BitVec.sub_cf64_eq_decide_lt, Bool.not_eq_true', Bool.not_eq_false',
      decide_eq_true_eq, decide_eq_false_iff_not] at hf
    simp -implicitDefEqProofs only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hf
    omega
  case vc9 =>
    obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6⟩ := hC
    and_intros
    · exact hc1
    · exact hc2
    · exact hc3
    · exact hc4
    · exact hc5
    · exact hc6
    iterate 7 exact True.intro
    · clear hc1 hc2 hc3 hc4 hc5 hc6
      have h1 := Mem.Block.storeInt_val hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _)
        (‹MachineData›.regs.get64 .rbp).toInt
      have h2 := Mem.Block.storeInt_val h1 (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _)
        (‹MachineData›.regs.get64 .r15).toInt
      have h3 := Mem.Block.storeInt_val h2 (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _)
        (‹MachineData›.regs.get64 .r14).toInt
      have h4 := Mem.Block.storeInt_val h3 (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _)
        (‹MachineData›.regs.get64 .r13).toInt
      have h5 := Mem.Block.storeInt_val h4 (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _)
        (‹MachineData›.regs.get64 .r12).toInt
      have h6 := Mem.Block.storeInt_val h5 (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _)
        (‹MachineData›.regs.get64 .rbx).toInt
      have h7 := Mem.Block.storeInt_val h6 (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _)
        (‹MachineData›.regs.get64 .rcx).toInt
      exact Mem.ac h7
    · exact Nat.le_refl _

theorem blk_e1 (k : Nat) (hk : k ≤ 2 ^ 32) (hms : MemsetSpec k) (x : XGenArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_x_gen.e1" := by
  cfg_block
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨⟨hC, hsp, hbp, hdi, hsi, hdx, h8, h9, hm⟩, hn⟩ := hs₀
  have hl : ∀ a : BitVec 64, a = xgTe t₀ →
      Mem.loadInt s₀.dmem a 1 = some (Int.ofBytes (Int.toBytes 1 x.te.toInt)) := by
    rintro a rfl
    have hm' := hm
    simp only [T, SbrW_open] at hm'
    exact Mem.Val.loadInt hm' (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right
      (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
  have hv8 : BitVec.ofInt 8 (Int.ofBytes (Int.toBytes 1 x.te.toInt)) = x.te := by
    rw [BitVec.ofInt_ofBytes_toBytes_eq 8 1 rfl, BitVec.ofInt_toInt]
  have haddr : t₀.regs.get64 .rdi + BitVec.setWidth 64 (BitVec.setWidth 32 (t₀.regs.get64 .r9)) * 88768#64
      + 88869#64 = xgTe t₀ := by
    simp only [xgTe, xgCh, arg0, arg5]; xg_bvext
  have hl' := hl _ rfl
  clear hl
  clear hms
  vcgen
  all_goals try subst_vars
  all_goals try dsimp only at *
  all_goals call_simp
  all_goals try simp only [AddrIndex.offset64, Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm,
    BitVec.add_zero, Nat.reducePow, Nat.reduceMod, Nat.reduceSub] at *
  all_goals try simp only [hdi, h9, h8, hdx, hsi] at *
  all_goals call_simp
  all_goals try simp only [Width.bytes, BitVec.mul_one, BitVec.setWidth_eq] at *
  all_goals try simp only [haddr] at *
  all_goals try simp only [hl', Option.isSome_some, Option.some.injEq] at *
  all_goals try subst_vars
  all_goals try simp only [hv8, BitVec.setWidth_eq] at *
  case vc2 =>
    refine ⟨⟨hC, ⟨hsp, hbp, True.intro⟩, True.intro, True.intro, True.intro, ?_, ?_, hm⟩, Nat.le_refl _⟩
    · simp only [BitVec.xor_self, BitVec.setWidth_zero]
    · simp only [BitVec.xor_self, BitVec.setWidth_zero, xgIT]
      have := hC.2.2.2.2.2
      split <;> split <;> rename_i h1 h2 <;>
        simp only [CondCode.interp_c, StatusFlags.cf_from_result, BitVec.unsigned_eq,
          BitVec.sub_cf32_eq_decide_lt, decide_eq_true_eq, Bool.not_eq_true, decide_eq_false_iff_not] at h1 <;>
        simp -implicitDefEqProofs only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h1
      · exfalso; omega
      · simp only [BitVec.setWidth_zero]
      · exact xg_lea_iT x.te h2 this
      · exfalso; omega

theorem blk_e2 (k : Nat) (hk : k ≤ 2 ^ 32) (hms : MemsetSpec k) (x : XGenArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_x_gen.e2" := by
  cfg_block
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨⟨hC, ⟨hsp, hbp, hbx⟩, h12, h13, hsi, h15, h14, hm⟩, hn⟩ := hs₀
  vcgen [MachineWP.call_proc_spec_at (XGenData t₀, SbrW x t₀ ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x58#64)
    ⋆ (FrMW t₀ ⋆ Rest x.R ra t₀))) "memset"
    (Kraken.Executable.ProcSpec.widen (k := k) hms (Nat.le_refl k) (by omega))]
  clear hms
  all_goals try call_simp
  all_goals try subst_vars
  all_goals try dsimp only at *
  all_goals try simp only [AddrIndex.offset64, Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm,
    BitVec.add_zero, Nat.reducePow, Nat.reduceMod, Nat.reduceSub] at *
  all_goals try simp (disch := omega) only [hbp, hsp, BitVec.sub_ofNat_add_ofNat64,
    BitVec.sub_ofNat_sub_ofNat64, Nat.reduceAdd, Nat.reduceSub, Nat.reducePow]
  case vc1 => grind_cells'
  case vc2 =>
    refine ⟨fun ra => ⟨⟨?_, ?_, ?_⟩, fun s' hpost => ?_⟩, ?_⟩
    · refine Mem.push_slot_res (b := t₀.regs.get64 .rsp - 0x60#64) ?_ (by first | rfl | xg_bvext) _
      simp only [FrMW_open]
      grind_cells'
    · exact True.intro
    · apply XGenData_carve_memset <;> grind_cells'
    · vcgen
      all_goals try simp only [FrMW_open] at *
      all_goals grind_cells'
    · grind_cells'

theorem blk_m1 (k : Nat) (hk : k ≤ 2 ^ 32) (hms : MemsetSpec k) (x : XGenArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_x_gen.m1" := by
  cfg_block
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨⟨hC, ⟨hsp, hbp, hbx⟩, h12, h13, h15, h14, hm⟩, hn⟩ := hs₀
  have hI := xgIT_cases x hC.2.2.2.2.2
  have hl : Mem.loadInt s₀.dmem (s₀.regs.get64 .rbx + 84#64) 4
      = some (Int.ofBytes (Int.toBytes 4 x.kx0.toInt)) := by
    have hm' := hm
    simp only [T, SbrW_open] at hm'
    rw [hbx]
    exact Mem.Val.loadInt hm' (Mem.Split.right (Mem.Split.here _ _) _) (Int.toBytes_length _ _)
      (by decide)
  have hv : BitVec.setWidth 64 (BitVec.ofInt 32 (Int.ofBytes (Int.toBytes 4 x.kx0.toInt)))
      = BitVec.ofNat 64 x.kx0.toNat := by
    rw [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt_toInt]
    apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  clear hms
  vcgen
  all_goals try subst_vars
  all_goals try dsimp only at *
  all_goals call_simp
  all_goals try simp only [AddrIndex.offset64, Int64.toBitVec_ofNat_norm, BitVec.add_zero] at *
  all_goals try simp only [hl, Option.isSome_some, Option.some.injEq] at *
  all_goals try subst_vars
  all_goals try simp only [hv] at *
  case vc2 =>
    rename_i hf
    simp -implicitDefEqProofs (disch := omega) only [CondCode.interp_z, CondCode.interp_le, StatusFlags.zf_from_result,
      StatusFlags.sf_from_result, StatusFlags.of_from_result, BitVec.and_self, BitVec.beq_zero_eq_decide,
      BitVec.msb_eq_decide, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
      Nat.reduceSub, Bool.not_eq_true', Bool.not_eq_false', bne_iff_ne, ne_eq, Bool.or_eq_true,
      decide_eq_true_eq, decide_eq_false_iff_not, h14] at hf
    left
    refine Table.ofLabels_at (l := "sbr_x_gen.Lb9cc") ⟨by decide, ?_⟩
    simp only [table]
    call_simp
    and_intros
    all_goals first | with_reducible assumption | rfl | omega | trivial | xg_bvext | xg_nat | xg_bstore | grind_cells'
  case vc3 =>
    rename_i hf
    simp -implicitDefEqProofs (disch := omega) only [CondCode.interp_z, CondCode.interp_le, StatusFlags.zf_from_result,
      StatusFlags.sf_from_result, StatusFlags.of_from_result, BitVec.and_self, BitVec.beq_zero_eq_decide,
      BitVec.msb_eq_decide, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
      Nat.reduceSub, Bool.not_eq_true', Bool.not_eq_false', bne_iff_ne, ne_eq, Bool.or_eq_true,
      decide_eq_true_eq, decide_eq_false_iff_not, h14] at hf
    left
    refine Table.ofLabels_at (l := "sbr_x_gen.Lb9cc") ⟨by decide, ?_⟩
    simp only [table]
    call_simp
    and_intros
    all_goals first | with_reducible assumption | rfl | omega | trivial | xg_bvext | xg_nat | xg_bstore | grind_cells'
  case vc4 =>
    rename_i hf
    simp -implicitDefEqProofs (disch := omega) only [CondCode.interp_z, CondCode.interp_le, StatusFlags.zf_from_result,
      StatusFlags.sf_from_result, StatusFlags.of_from_result, BitVec.and_self, BitVec.beq_zero_eq_decide,
      BitVec.msb_eq_decide, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
      Nat.reduceSub, Bool.not_eq_true', Bool.not_eq_false', bne_iff_ne, ne_eq, Bool.or_eq_true,
      decide_eq_true_eq, decide_eq_false_iff_not, h14] at hf
    try simp only [table]
    call_simp
    and_intros
    all_goals first | with_reducible assumption | rfl | omega | trivial | xg_bvext | xg_nat | xg_bstore | grind_cells'

theorem blk_a0 (k : Nat) (hk : k ≤ 2 ^ 32) (hms : MemsetSpec k) (x : XGenArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_x_gen.a0" := by
  cfg_block
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨⟨hC, ⟨hsp, hbp, hbx⟩, h12, h13, h14, hi2, hk0, hm⟩, hn⟩ := hs₀
  have hI := xgIT_cases x hC.2.2.2.2.2
  clear hms
  vcgen
  all_goals try subst_vars
  all_goals try dsimp only at *
  all_goals call_simp
  all_goals try simp only [AddrIndex.offset64, Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm,
    BitVec.add_zero, Nat.reducePow, Nat.reduceMod, Nat.reduceSub] at *
  all_goals try simp only [table]
  all_goals call_simp
  all_goals try simp only [FrMW_open] at *
  all_goals try simp -implicitDefEqProofs only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, ↓reduceIte,
    Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
  all_goals try simp (disch := omega) only [h14, xg_shl8_add, BitVec.ofNat64_add_wrap, Nat.reduceSub,
    Nat.reducePow, Nat.reduceAdd]
  all_goals try and_intros
  all_goals first | with_reducible assumption | omega | (congr 1; omega) | xg_bstore | grind_cells'

theorem blk_Lb910 (k : Nat) (hk : k ≤ 2 ^ 32) (hms : MemsetSpec k) (x : XGenArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_x_gen.Lb910" := by
  cfg_block
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨⟨hC, ⟨⟨hsp, hbp, hbx⟩, h12, h13, h14, hi2, hk, hcx, hdx, hax, hdi, h8⟩, hm⟩, hn⟩ := hs₀
  clear hms
  vcgen
  all_goals try subst_vars
  all_goals try dsimp only at *
  all_goals call_simp
  all_goals try simp only [BitVec.xor_self, BitVec.setWidth_zero, BitVec.toNat_zero, Nat.zero_div,
    Nat.mul_zero, Nat.add_zero]
  and_intros
  all_goals first | with_reducible assumption | rfl | omega | trivial | grind_cells'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000 in
theorem blk_Lb920 (k : Nat) (hk : k ≤ 2 ^ 32) (hms : MemsetSpec k) (x : XGenArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_x_gen.Lb920" := by
  cfg_block
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨⟨hC, ⟨⟨⟨hsp, hbp, hbx⟩, h12, h13, h14, hi2, hk, hcx, hdx, hax, hdi, h8⟩, h10, hj, h9⟩, hm⟩, hn⟩ := hs₀
  have hI := xgIT_cases x hC.2.2.2.2.2
  generalize (s₀.regs.get64 .r10).toNat / 768 = j at *
  have hj1 : j ≤ 1 := by rcases hI with h | h | h | h <;> omega
  have h768 : (BitVec.ofNat 64 (768 * j)).toNat = 768 * j := by
    simp -implicitDefEqProofs only [BitVec.toNat_ofNat]; omega
  have hd : 768 * j / 768 = j := by omega
  clear hms
  vcgen
  all_goals try subst_vars
  all_goals try dsimp only at *
  all_goals opaque_stores
  all_goals try simp only [AddrIndex.offset64, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat,
    BitVec.add_zero, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd] at *
  all_goals try simp only [h9, hcx, h10, Width.bytes, BitVec.mul_one, BitVec.add_assoc,
    Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reducePow, Nat.reduceMod,
    Nat.reduceSub]
  all_goals try simp only [← BitVec.ofNat_add, ← Nat.add_assoc]
  all_goals try simp (disch := omega) only [BitVec.ofNat64_add_wrap, Nat.reduceSub, Nat.reducePow,
    Nat.reduceAdd]
  case vc1 | vc2 | vc3 | vc4 => grind_cells'
  case vc5 =>
    left
    refine Table.ofLabels_at (l := "sbr_x_gen.Lb9a6") ⟨by decide, ?_⟩
    simp only [table]; and_intros <;> first | with_reducible assumption | grind_cells'
  case vc6 =>
    simp (disch := omega) only [CondCode.interp_z, StatusFlags.zf_from_result, h8, h10,
      BitVec.ofNat64_sub_beq_zero, decide_eq_true_eq] at *
    simp only [h768, hd]
    and_intros
    all_goals first | with_reducible assumption | rfl | omega | trivial | grind_cells'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_a2 (k : Nat) (hk : k ≤ 2 ^ 32) (hms : MemsetSpec k) (x : XGenArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_x_gen.a2" := by
  cfg_block
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨⟨hC, ⟨⟨⟨hsp, hbp, hbx⟩, h12, h13, h14, hi2, hk, hcx, hdx, hax, hdi, h8⟩, h10, hj, h9⟩, hm⟩, hn⟩ := hs₀
  have hI := xgIT_cases x hC.2.2.2.2.2
  generalize (s₀.regs.get64 .r10).toNat / 768 = j at *
  have hj1 : j ≤ 1 := by rcases hI with h | h | h | h <;> omega
  have h768 : (BitVec.ofNat 64 (768 * j)).toNat = 768 * j := by
    simp -implicitDefEqProofs only [BitVec.toNat_ofNat]; omega
  have hd : 768 * j / 768 = j := by omega
  clear hms
  vcgen
  all_goals try subst_vars
  all_goals try dsimp only at *
  all_goals opaque_stores
  all_goals try simp only [AddrIndex.offset64, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat,
    BitVec.add_zero, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd] at *
  all_goals try simp only [h9, hcx, h10, Width.bytes, BitVec.mul_one, BitVec.add_assoc,
    Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reducePow, Nat.reduceMod,
    Nat.reduceSub]
  all_goals try simp only [← BitVec.ofNat_add, ← Nat.add_assoc]
  all_goals try simp (disch := omega) only [BitVec.ofNat64_add_wrap, Nat.reduceSub, Nat.reducePow,
    Nat.reduceAdd]
  case vc1 | vc2 | vc3 | vc4 => grind_cells'
  case vc5 =>
    left
    refine Table.ofLabels_at (l := "sbr_x_gen.Lb9a6") ⟨by decide, ?_⟩
    simp only [table]; and_intros <;> first | with_reducible assumption | grind_cells'
  case vc6 =>
    exfalso
    simp (disch := omega) only [CondCode.interp_z, StatusFlags.zf_from_result, hdi, h10,
      BitVec.ofNat64_sub_beq_zero, BitVec.ofNat64_sub_lit_beq_zero, BitVec.setWidth_eq, decide_eq_true_eq,
      decide_eq_false_iff_not] at *
    omega
  case vc7 =>
    simp (disch := omega) only [CondCode.interp_z, StatusFlags.zf_from_result, hdi, h10,
      BitVec.ofNat64_sub_beq_zero, BitVec.ofNat64_sub_lit_beq_zero, BitVec.setWidth_eq, decide_eq_true_eq,
      decide_eq_false_iff_not] at *
    simp only [h768, hd]
    and_intros
    all_goals first | with_reducible assumption | rfl | omega | trivial | grind_cells'

set_option maxHeartbeats 300000 in
theorem blk_a3 (k : Nat) (hk : k ≤ 2 ^ 32) (hms : MemsetSpec k) (x : XGenArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_x_gen.a3" := by
  cfg_block
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨⟨hC, ⟨⟨⟨hsp, hbp, hbx⟩, h12, h13, h14, hi2, hk, hcx, hdx, hax, hdi, h8⟩, h10, hj, h9⟩, hm⟩, hn⟩ := hs₀
  have hI := xgIT_cases x hC.2.2.2.2.2
  generalize (s₀.regs.get64 .r10).toNat / 768 = j at *
  have hj1 : j ≤ 1 := by rcases hI with h | h | h | h <;> omega
  have h768 : (BitVec.ofNat 64 (768 * j)).toNat = 768 * j := by
    simp -implicitDefEqProofs only [BitVec.toNat_ofNat]; omega
  have hd : 768 * j / 768 = j := by omega
  clear hms
  vcgen
  all_goals try subst_vars
  all_goals try dsimp only at *
  all_goals opaque_stores
  all_goals try simp only [AddrIndex.offset64, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat,
    BitVec.add_zero, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd] at *
  all_goals try simp only [h9, hcx, h10, Width.bytes, BitVec.mul_one, BitVec.add_assoc,
    Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reducePow, Nat.reduceMod,
    Nat.reduceSub]
  all_goals try simp only [← BitVec.ofNat_add, ← Nat.add_assoc]
  all_goals try simp (disch := omega) only [BitVec.ofNat64_add_wrap, Nat.reduceSub, Nat.reducePow,
    Nat.reduceAdd]
  case vc1 | vc2 | vc3 | vc4 => grind_cells'
  case vc5 =>
    rename_i hf
    simp (disch := omega) only [CondCode.interp_z, CondCode.interp_nz, StatusFlags.zf_from_result, hax, h10,
      ← BitVec.ofNat_add, Bool.not_eq_true', Bool.not_eq_false',
      BitVec.ofNat64_sub_beq_zero, BitVec.setWidth_eq, decide_eq_true_eq,
      decide_eq_false_iff_not] at hf
    left
    refine Table.ofLabels_at (l := "sbr_x_gen.Lb920") ⟨by decide, ?_⟩
    simp only [table]
    call_simp
    simp -implicitDefEqProofs (disch := omega) only [h10, h9, BitVec.ofNat64_lit_shift, ← BitVec.ofNat_add,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    and_intros
    all_goals first | with_reducible assumption | rfl | omega | trivial | (congr 1; omega) | (congr 2; omega) | grind_cells'
  case vc6 =>
    rename_i hf
    simp (disch := omega) only [CondCode.interp_z, CondCode.interp_nz, StatusFlags.zf_from_result, hax, h10,
      ← BitVec.ofNat_add, Bool.not_eq_true', Bool.not_eq_false',
      BitVec.ofNat64_sub_beq_zero, BitVec.setWidth_eq, decide_eq_true_eq,
      decide_eq_false_iff_not] at hf
    try simp only [table]
    call_simp
    and_intros
    all_goals first | with_reducible assumption | rfl | omega | trivial | grind_cells'

set_option maxHeartbeats 300000 in
theorem blk_Lb9a6 (k : Nat) (hk : k ≤ 2 ^ 32) (hms : MemsetSpec k) (x : XGenArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_x_gen.Lb9a6" := by
  cfg_block
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨⟨hC, ⟨⟨hsp, hbp, hbx⟩, h12, h13, h14, hi2, hk, hcx, hdx, hax, hdi, h8⟩, hm⟩, hn⟩ := hs₀
  have hl : Mem.loadInt s₀.dmem (s₀.regs.get64 .rbx + 84#64) 4
      = some (Int.ofBytes (Int.toBytes 4 x.kx0.toInt)) := by
    have hm' := hm
    simp only [T, SbrW_open] at hm'
    rw [hbx]
    exact Mem.Val.loadInt hm' (Mem.Split.right (Mem.Split.here _ _) _) (Int.toBytes_length _ _)
      (by decide)
  have hv : BitVec.setWidth 64 (BitVec.ofInt 32 (Int.ofBytes (Int.toBytes 4 x.kx0.toInt)))
      = BitVec.ofNat 64 x.kx0.toNat := by
    rw [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt_toInt]
    apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  clear hms
  vcgen
  all_goals try subst_vars
  all_goals try dsimp only at *
  all_goals call_simp
  all_goals try simp only [AddrIndex.offset64, Int64.toBitVec_ofNat_norm, BitVec.add_zero] at *
  all_goals try simp only [hl, Option.isSome_some, Option.some.injEq] at *
  all_goals try subst_vars
  all_goals try simp only [hv, BitVec.setWidth_eq, CondCode.interp_nc, CondCode.interp_nz,
    CondCode.interp_z, StatusFlags.cf_from_result, StatusFlags.zf_from_result, BitVec.unsigned_eq,
    BitVec.sub_cf64_eq_decide_lt, BitVec.sub64_beq_zero, Bool.not_eq_true', Bool.not_eq_false',
    decide_eq_true_eq, decide_eq_false_iff_not] at *
  all_goals try simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_ofNat, xg_toNat_one64,
    Nat.reducePow, Nat.reduceMod] at *
  case vc2 =>
    left
    refine Table.ofLabels_at (l := "sbr_x_gen.Lb9cc") ⟨by decide, ?_⟩
    simp only [table]
    call_simp
    and_intros
    all_goals first | with_reducible assumption | rfl | omega | ((try simp only [hcx, hdx]); xg_bvext) | xg_nat | xg_bstore | grind_cells'
  case vc3 =>
    left
    refine Table.ofLabels_at (l := "sbr_x_gen.Lb910") ⟨by decide, ?_⟩
    simp only [table]
    call_simp
    and_intros
    all_goals first | with_reducible assumption | rfl | omega | ((try simp only [hcx, hdx]); xg_bvext) | xg_nat | xg_bstore | grind_cells'
  case vc4 =>
    exfalso
    omega

theorem blk_t1 (k : Nat) (hk : k ≤ 2 ^ 32) (hms : MemsetSpec k) (x : XGenArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_x_gen.t1" := by
  cfg_block
  intro n
  exact Triple.intro fun s hs => hs.1.elim

theorem blk_Lb9cc (k : Nat) (hk : k ≤ 2 ^ 32) (hms : MemsetSpec k) (x : XGenArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_x_gen.Lb9cc" := by
  cfg_block
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨⟨hC, ⟨hsp, hbp, hbx⟩, h12, h13, h14, hsi, h15, hm⟩, hn⟩ := hs₀
  have hI := xgIT_cases x hC.2.2.2.2.2
  have hl : Mem.loadInt s₀.dmem (s₀.regs.get64 .rbx + 92#64) 4
      = some (Int.ofBytes (Int.toBytes 4 x.m0.toInt)) := by
    have hm' := hm
    simp only [T, SbrW_open] at hm'
    rw [hbx]
    exact Mem.Val.loadInt hm' (Mem.Split.right (Mem.Split.right (Mem.Split.right
      (Mem.Split.here _ _) _) _) _) (Int.toBytes_length _ _) (by decide)
  have hv : BitVec.ofInt 32 (Int.ofBytes (Int.toBytes 4 x.m0.toInt)) = x.m0 := by
    rw [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt_toInt]
  clear hms
  vcgen
  all_goals try subst_vars
  all_goals try dsimp only at *
  all_goals call_simp
  all_goals try simp only [AddrIndex.offset64, Int64.toBitVec_ofNat_norm, Int64.toBitVec_zero, BitVec.ofNat_eq_ofNat,
    BitVec.add_zero] at *
  all_goals try simp only [hl, Option.isSome_some, Option.some.injEq] at *
  all_goals try subst_vars
  all_goals try simp only [hv] at *
  case vc2 | vc3 =>
    left
    refine Table.ofLabels_at (l := "sbr_x_gen.Lbba9") ⟨by decide, ?_⟩
    simp only [table]
    call_simp
    and_intros
    all_goals first | with_reducible assumption | rfl | omega | trivial | grind_cells'
  case vc4 =>
    exfalso
    rename_i h1 h2 h3
    simp only [hsi, h15, h14] at h1 h2 h3
    simp only [CondCode.interp_nc, CondCode.interp_le, CondCode.interp_a, CondCode.interp_c,
      StatusFlags.cf_from_result, StatusFlags.zf_from_result, StatusFlags.sf_from_result,
      StatusFlags.of_from_result, BitVec.unsigned_eq, BitVec.sub_cf_eq_decide_lt, BitVec.sub_beq_zero,
      BitVec.and_self, BitVec.beq_zero_eq_decide, BitVec.msb_eq_decide, Bool.not_eq_true',
      Bool.not_eq_false', Bool.bne_false, bne_iff_ne, ne_eq, Bool.or_eq_true, Bool.or_eq_false_iff,
      Bool.and_eq_true, decide_eq_true_eq, decide_eq_false_iff_not] at *
    simp -implicitDefEqProofs only [Int64.toBitVec_neg_ofNat_norm, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      BitVec.toNat_add, BitVec.toNat_sub, Nat.reducePow, Nat.reduceMod, Nat.reduceSub] at *
    omega
  case vc5 =>
    rename_i h1 h2 h3
    simp only [hsi, h15, h14] at h1 h2 h3 ⊢
    simp only [CondCode.interp_nc, CondCode.interp_le, CondCode.interp_a, CondCode.interp_c,
      StatusFlags.cf_from_result, StatusFlags.zf_from_result, StatusFlags.sf_from_result,
      StatusFlags.of_from_result, BitVec.unsigned_eq, BitVec.sub_cf_eq_decide_lt, BitVec.sub_beq_zero,
      BitVec.and_self, BitVec.beq_zero_eq_decide, BitVec.msb_eq_decide, Bool.not_eq_true',
      Bool.not_eq_false', Bool.bne_false, bne_iff_ne, ne_eq, Bool.or_eq_true, Bool.or_eq_false_iff,
      Bool.and_eq_true, decide_eq_true_eq, decide_eq_false_iff_not] at h1 h2 h3
    simp -implicitDefEqProofs only [Int64.toBitVec_neg_ofNat_norm, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      BitVec.toNat_add, BitVec.toNat_sub, Nat.reducePow, Nat.reduceMod, Nat.reduceSub] at h1 h2 h3
    rw [if_pos (c := CondCode.c.interp _ = true) ?hc, if_neg (c := CondCode.nc.interp _ = true) ?hnc]
    case hc =>
      rcases hI with h|h|h|h
      · exfalso; simp [h] at h1
      all_goals (rw [h]; first | rfl | decide)
    case hnc =>
      simp only [CondCode.interp_nc, CondCode.interp_le, CondCode.interp_a, CondCode.interp_c,
      StatusFlags.cf_from_result, StatusFlags.zf_from_result, StatusFlags.sf_from_result,
      StatusFlags.of_from_result, BitVec.unsigned_eq, BitVec.sub_cf_eq_decide_lt, BitVec.sub_beq_zero,
      BitVec.and_self, BitVec.beq_zero_eq_decide, BitVec.msb_eq_decide, Bool.not_eq_true',
      Bool.not_eq_false', Bool.bne_false, bne_iff_ne, ne_eq, Bool.or_eq_true, Bool.or_eq_false_iff,
      Bool.and_eq_true, decide_eq_true_eq, decide_eq_false_iff_not]
      simp -implicitDefEqProofs only [Int64.toBitVec_neg_ofNat_norm, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      BitVec.toNat_add, BitVec.toNat_sub, Nat.reducePow, Nat.reduceMod, Nat.reduceSub]
      omega
    and_intros
    all_goals first | exact True.intro | with_reducible exact BitVec.zext32_twice_64 | (with_reducible apply BitVec.zext32_twice_ofNat_add_neg_one; refine hI.resolve_left fun h0 => ?_; simp [h0] at h1) | omega | xg_bvext | xg_nat | (simp only [Int64.toBitVec_neg_ofNat_norm]; xg_bvext) | (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [BitVec.toNat_setWidth]; rfl) | with_reducible assumption | grind_cells'

theorem blk_b0 (k : Nat) (hk : k ≤ 2 ^ 32) (hms : MemsetSpec k) (x : XGenArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_x_gen.b0" := by
  cfg_block
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨⟨hC, ⟨hsp, hbp, hbx⟩, h12, h13, h14, hi2, hsi, hm0, hax, hcx, hm⟩, hn⟩ := hs₀
  have hI := xgIT_cases x hC.2.2.2.2.2
  simp only [T, FM, FrMW_open] at hm
  have e14 : BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 (xgIT x)))
      = BitVec.ofNat 64 (xgIT x) := by xg_bvext
  have esi : BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 x.kx0.toNat))
      = BitVec.ofNat 64 x.kx0.toNat := by xg_bvext
  have e4 : BitVec.ofNat 64 x.kx0.toNat * BitVec.ofNat 64 4 = BitVec.ofNat 64 (4 * x.kx0.toNat) := by
    apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [BitVec.toNat_mul, BitVec.toNat_ofNat]; omega
  have e8 : BitVec.ofNat 64 x.kx0.toNat * 8#64 = BitVec.ofNat 64 (8 * x.kx0.toNat) := by
    apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [BitVec.toNat_mul, BitVec.toNat_ofNat]; omega
  have eand : BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 (xgIT x)) &&&
      BitVec.setWidth 32 2147483644#64) = BitVec.ofNat 64 (xgIT x / 4 * 4) := by
    rcases hI with h | h | h | h <;> rw [h] <;> decide
  clear hms
  vcgen
  all_goals try subst_vars
  all_goals try dsimp only at *
  all_goals call_simp
  all_goals try simp only [AddrIndex.offset64, Int64.toBitVec_ofNat_norm, Int64.toBitVec_zero,
    BitVec.ofNat_eq_ofNat, BitVec.add_zero] at *
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
  all_goals try simp only [hbp, hsi, h14, h13, Int64.toBitVec_neg_ofNat_norm, Width.bytes,
    Nat.reducePow, Nat.reduceMod, Nat.reduceSub, e14, esi, e4, e8, eand]
  all_goals try simp (disch := omega) only [BitVec.sub_ofNat_add_ofNat64, Nat.reduceAdd,
    Nat.reduceSub, Nat.reducePow]
  case vc1 | vc2 | vc3 => grind_cells'
  case vc4 =>
    rename_i v hv
    simp only [hbp, Int64.toBitVec_neg_ofNat_norm, Nat.reducePow, Nat.reduceMod, Nat.reduceSub] at hv
    simp (disch := omega) only [BitVec.sub_ofNat_add_ofNat64, Nat.reduceAdd, Nat.reduceSub,
      Nat.reducePow] at hv
    rw [Mem.loadInt_storeInt_of_above _ _ _ _ _ _ (by bv_omega) (by bv_omega),
      Mem.loadInt_storeInt_of_above _ _ _ _ _ _ (by bv_omega) (by bv_omega)] at hv
    rw [Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _)
      (Int.toBytes_length _ _) (by decide)] at hv
    simp only [Option.some.injEq] at hv
    subst hv
    simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, FrBW_open]
    and_intros
    all_goals first | exact True.intro | with_reducible assumption | omega | xg_bvext | xg_nat | (congr 1; xg_bvext) | (simp only [FrBL, Sv]; grind_cells')

theorem blk_Lba50 (k : Nat) (hk : k ≤ 2 ^ 32) (hms : MemsetSpec k) (x : XGenArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_x_gen.Lba50" := by
  cfg_block
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨⟨hC, ⟨⟨hsp, hbp, hbx⟩, h12, h14, hi2, hk1, hk2, hax, hcx, hdi, h9, h10, h11, h13⟩, hm⟩,
    hn⟩ := hs₀
  have hI := xgIT_cases x hC.2.2.2.2.2
  clear hms
  vcgen
  all_goals try subst_vars
  all_goals try dsimp only at *
  all_goals call_simp
  all_goals try simp only [BitVec.xor_self, BitVec.setWidth_zero]
  case vc1 =>
    exfalso
    rename_i hz
    simp only [hax] at hz
    simp only [CondCode.interp_nc, CondCode.interp_z, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
      BitVec.unsigned_eq, BitVec.sub_cf_eq_decide_lt, BitVec.sub_beq_zero, Bool.not_eq_true',
      Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not] at hz
    simp -implicitDefEqProofs only [Int64.toBitVec_ofNat_norm, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
      Nat.reduceSub] at hz
    omega
  case vc2 =>
    rename_i hz hnc
    simp only [h14] at hnc
    simp only [CondCode.interp_nc, CondCode.interp_z, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
      BitVec.unsigned_eq, BitVec.sub_cf_eq_decide_lt, BitVec.sub_beq_zero, Bool.not_eq_true',
      Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not] at hnc
    simp -implicitDefEqProofs only [Int64.toBitVec_ofNat_norm, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
      Nat.reduceSub] at hnc
    left
    refine Table.ofLabels_at (l := "sbr_x_gen.Lba70") ⟨by decide, ?_⟩
    simp only [table]
    call_simp
    and_intros
    all_goals first | exact True.intro | with_reducible assumption | omega | xg_bvext | xg_nat | xg_bstore | grind_cells'
  case vc3 =>
    rename_i hz hnc _
    simp only [h14] at hnc
    simp only [CondCode.interp_nc, CondCode.interp_z, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
      BitVec.unsigned_eq, BitVec.sub_cf_eq_decide_lt, BitVec.sub_beq_zero, Bool.not_eq_true',
      Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not] at hnc
    simp -implicitDefEqProofs only [Int64.toBitVec_ofNat_norm, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
      Nat.reduceSub] at hnc
    left
    refine Table.ofLabels_at (l := "sbr_x_gen.Lbb30") ⟨by decide, ?_⟩
    simp only [table]
    call_simp
    and_intros
    all_goals first | exact True.intro | with_reducible assumption | omega | xg_bvext | xg_nat | xg_bstore | grind_cells'

theorem blk_Lba70 (k : Nat) (hk : k ≤ 2 ^ 32) (hms : MemsetSpec k) (x : XGenArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_x_gen.Lba70" := by
  cfg_block
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨⟨hC, ⟨⟨hsp, hbp, hbx⟩, h12, h14, hi2, hk1, hk2, hax, hcx, hdi, h9, h10, h11, h13⟩, hi4,
    hm⟩, hn⟩ := hs₀
  have hm' := hm
  simp only [T, FB, FrBW_open] at hm'
  clear hms
  vcgen
  all_goals try subst_vars
  all_goals try dsimp only at *
  all_goals call_simp
  all_goals try simp only [AddrIndex.offset64, Int64.toBitVec_ofNat_norm, Int64.toBitVec_zero,
    BitVec.ofNat_eq_ofNat, BitVec.add_zero] at *
  all_goals try simp only [BitVec.xor_self, BitVec.setWidth_zero]
  case vc1 =>
    simp only [hbp, Int64.toBitVec_neg_ofNat_norm, Nat.reducePow, Nat.reduceMod, Nat.reduceSub]
    simp (disch := omega) only [BitVec.sub_ofNat_add_ofNat64, Nat.reduceAdd, Nat.reduceSub,
      Nat.reducePow]
    grind_cells'
  case vc2 =>
    rename_i v _ hv
    simp only [hbp, Int64.toBitVec_neg_ofNat_norm, Nat.reducePow, Nat.reduceMod, Nat.reduceSub] at hv
    simp (disch := omega) only [BitVec.sub_ofNat_add_ofNat64, Nat.reduceAdd, Nat.reduceSub,
      Nat.reducePow] at hv
    rw [Mem.Val.loadInt hm' (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _)
      (Int.toBytes_length _ _) (by decide)] at hv
    simp only [Option.some.injEq] at hv
    subst hv
    simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, BitVec.toNat_zero]
    and_intros
    all_goals first | exact True.intro | with_reducible assumption | omega | xg_bvext | xg_nat | xg_bstore | grind_cells'

theorem blk_Lba80 (k : Nat) (hk : k ≤ 2 ^ 32) (hms : MemsetSpec k) (x : XGenArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_x_gen.Lba80" := by
  cfg_block
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨⟨hC, ⟨⟨hsp, hbp, hbx⟩, h12, h14, hi2, hk1, hk2, hax, hcx, hdi, h9, h10, h11, h13⟩, hi4,
    h15, h8, hm⟩, hn⟩ := hs₀
  clear hms
  vcgen
  all_goals try subst_vars
  all_goals try dsimp only at *
  all_goals opaque_stores
  all_goals try simp only [AddrIndex.offset64, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat,
    BitVec.add_zero, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd] at *
  all_goals try simp only [h9, h13, h8, Width.bytes, BitVec.mul_one, BitVec.add_assoc,
    Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reducePow, Nat.reduceMod,
    Nat.reduceSub]
  all_goals try simp only [BitVec.ofNat64_mul_ofNat, BitVec.ofNat64_mul_lit, ← BitVec.ofNat_add,
    ← Nat.add_assoc]
  all_goals try simp (disch := omega) only [BitVec.ofNat64_add_wrap, Nat.reduceSub, Nat.reducePow,
    Nat.reduceAdd]
  case vc1 | vc2 | vc3 | vc4 | vc5 | vc6 | vc7 | vc8 => grind_cells'
  case vc9 =>
    and_intros
    all_goals first | exact True.intro | with_reducible assumption | omega | grind_cells'

theorem blk_b2 (k : Nat) (hk : k ≤ 2 ^ 32) (hms : MemsetSpec k) (x : XGenArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_x_gen.b2" := by
  cfg_block
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨⟨hC, ⟨⟨hsp, hbp, hbx⟩, h12, h14, hi2, hk1, hk2, hax, hcx, hdi, h9, h10, h11, h13⟩, hi4,
    h15, h8, hm⟩, hn⟩ := hs₀
  clear hms
  vcgen
  all_goals try subst_vars
  all_goals try dsimp only at *
  all_goals opaque_stores
  all_goals try simp only [AddrIndex.offset64, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat,
    BitVec.add_zero, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd] at *
  all_goals try simp only [h9, h13, h8, Width.bytes, BitVec.mul_one, BitVec.add_assoc,
    Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reducePow, Nat.reduceMod,
    Nat.reduceSub]
  all_goals try simp only [BitVec.ofNat64_mul_ofNat, BitVec.ofNat64_mul_lit, ← BitVec.ofNat_add,
    ← Nat.add_assoc]
  all_goals try simp (disch := omega) only [BitVec.ofNat64_add_wrap, Nat.reduceSub, Nat.reducePow,
    Nat.reduceAdd]
  case vc1 | vc2 | vc3 | vc4 | vc5 | vc6 | vc7 | vc8 => grind_cells'
  case vc9 =>
    and_intros
    all_goals first | exact True.intro | with_reducible assumption | omega | grind_cells'

theorem blk_b3 (k : Nat) (hk : k ≤ 2 ^ 32) (hms : MemsetSpec k) (x : XGenArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_x_gen.b3" := by
  cfg_block
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨⟨hC, ⟨⟨hsp, hbp, hbx⟩, h12, h14, hi2, hk1, hk2, hax, hcx, hdi, h9, h10, h11, h13⟩, hi4,
    h15, h8, hm⟩, hn⟩ := hs₀
  have hI := xgIT_cases x hC.2.2.2.2.2
  have hm' := hm
  simp only [T, FB, FrBW_open] at hm'
  have hl : Mem.loadInt s₀.dmem (t₀.regs.get64 .rsp - 80#64) 1
      = some (Int.ofBytes (Int.toBytes 1 (BitVec.ofNat 64 (xgIT x)).toInt)) := by
    rw [← Int.toBytes8_take1]
    exact Mem.Val.loadInt_prefix hm' (Mem.Split.right (Mem.Split.right (Mem.Split.right
      (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _)
      (by simp only [Int.toBytes_length]; omega) (by simp only [Int.toBytes_length]; omega)
  clear hms
  vcgen
  all_goals try subst_vars
  all_goals try dsimp only at *
  all_goals call_simp
  all_goals try simp only [AddrIndex.offset64, Int64.toBitVec_ofNat_norm, Int64.toBitVec_zero,
    BitVec.ofNat_eq_ofNat, BitVec.add_zero] at *
  case vc1 =>
    exfalso
    rename_i hnz
    simp only [hdi, h15] at hnz
    simp only [CondCode.interp_nz, CondCode.interp_z, StatusFlags.zf_from_result, BitVec.sub64_beq_zero,
      BitVec.beq_zero_eq_decide, Bool.not_eq_true', Bool.not_eq_false', decide_eq_true_eq,
      decide_eq_false_iff_not] at hnz
    simp -implicitDefEqProofs only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth,
      BitVec.toNat_zero, Nat.reducePow, Nat.reduceMod] at hnz
    rcases hI with h | h | h | h <;> rw [h] at hnz hi4 <;> omega
  case vc2 =>
    simp only [hbp, Int64.toBitVec_neg_ofNat_norm, Nat.reducePow, Nat.reduceMod, Nat.reduceSub]
    simp (disch := omega) only [BitVec.sub_ofNat_add_ofNat64, Nat.reduceAdd, Nat.reduceSub,
      Nat.reducePow]
    simp only [hl, Option.isSome_some]
  case vc3 =>
    left
    refine Table.ofLabels_at (l := "sbr_x_gen.Lbb7d") ⟨by decide, ?_⟩
    simp only [table]
    call_simp
    and_intros
    all_goals first | exact True.intro | with_reducible assumption | omega | grind_cells'
  case vc4 =>
    rename_i v _ hz hnz hv
    simp only [hbp, Int64.toBitVec_neg_ofNat_norm, Nat.reducePow, Nat.reduceMod, Nat.reduceSub] at hv
    simp (disch := omega) only [BitVec.sub_ofNat_add_ofNat64, Nat.reduceAdd, Nat.reduceSub,
      Nat.reducePow] at hv
    rw [hl, Option.some.injEq] at hv
    subst hv
    have hz6 : xgIT x = 6 := by
      simp only [CondCode.interp_z, StatusFlags.zf_from_result] at hz
      rcases hI with h | h | h | h <;> (try omega) <;> (try exact h) <;>
        (rw [h] at hz; exact absurd hz (by decide))
    simp only [h15]
    and_intros
    all_goals first | exact True.intro | with_reducible assumption | omega | xg_bvext | grind_cells'

theorem blk_Lbb30 (k : Nat) (hk : k ≤ 2 ^ 32) (hms : MemsetSpec k) (x : XGenArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_x_gen.Lbb30" := by
  cfg_block
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨⟨hC, ⟨⟨hsp, hbp, hbx⟩, h12, h14, hi2, hk1, hk2, hax, hcx, hdi, h9, h10, h11, h13⟩, hi4,
    h15, hm⟩, hn⟩ := hs₀
  have hI := xgIT_cases x hC.2.2.2.2.2
  clear hms
  vcgen
  all_goals try subst_vars
  all_goals try dsimp only at *
  all_goals call_simp
  simp -implicitDefEqProofs (config := {decide := true}) only [Int64.toBitVec_ofNat_norm, BitVec.toNat_ofNat,
    Nat.reducePow, Nat.reduceMod, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    BitVec.xor_self, BitVec.setWidth_zero, BitVec.toNat_zero, Nat.zero_div, Nat.mul_zero,
    Nat.add_zero, h10, h11, h15]
  and_intros
  all_goals first | exact True.intro | with_reducible assumption | omega | (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_setWidth, Nat.reducePow]; omega) | grind_cells'

set_option maxHeartbeats 300000 in
theorem blk_Lbb50 (k : Nat) (hk : k ≤ 2 ^ 32) (hms : MemsetSpec k) (x : XGenArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_x_gen.Lbb50" := by
  cfg_block
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨⟨hC, ⟨⟨hsp, hbp, hbx⟩, h12, h14, hi2, hk1, hk2, hax, hcx, hdi, h9, h10, h11, h13⟩, hi4,
    hdx, hj, h8, h15, hm⟩, hn⟩ := hs₀
  have hI := xgIT_cases x hC.2.2.2.2.2
  generalize (s₀.regs.get64 .rdx).toNat / 256 = j at *
  have h256 : (BitVec.ofNat 64 (256 * j)).toNat = 256 * j := by
    simp -implicitDefEqProofs only [BitVec.toNat_ofNat]; omega
  have hd : 256 * j / 256 = j := by omega
  clear hms
  vcgen
  all_goals try subst_vars
  all_goals try dsimp only at *
  all_goals opaque_stores
  all_goals try simp only [AddrIndex.offset64, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat,
    BitVec.add_zero, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd] at *
  all_goals try simp only [h8, h15, hdx, Width.bytes, BitVec.mul_one, BitVec.add_assoc,
    Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reducePow, Nat.reduceMod,
    Nat.reduceSub]
  all_goals try simp only [BitVec.ofNat64_mul_ofNat, BitVec.ofNat64_mul_lit, ← BitVec.ofNat_add,
    ← Nat.add_assoc]
  all_goals try simp (disch := omega) only [BitVec.ofNat64_add_wrap, Nat.reduceSub, Nat.reducePow,
    Nat.reduceAdd]
  case vc1 | vc2 | vc3 | vc4 => grind_cells'
  case vc5 =>
    rename_i _ _ hf _ _ _ _
    try simp only [hdx] at hf
    simp only [CondCode.interp_nz, StatusFlags.zf_from_result, BitVec.sub64_beq_zero,
      Bool.not_eq_true', Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not] at hf
    simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_add,
      BitVec.toNat_ofNat, BitVec.toNat_setWidth, Nat.reducePow, Nat.reduceMod] at hf
    left
    refine Table.ofLabels_at (l := "sbr_x_gen.Lbb50") ⟨by decide, ?_⟩
    simp only [table]
    call_simp
    and_intros
    all_goals first | exact True.intro | with_reducible assumption | omega | xg_bvext | xg_nat | xg_bstore | grind_cells'
  case vc6 =>
    rename_i _ _ hf _ _ _ _
    try simp only [hdx] at hf
    simp only [CondCode.interp_nz, StatusFlags.zf_from_result, BitVec.sub64_beq_zero,
      Bool.not_eq_true', Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not] at hf
    simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_add,
      BitVec.toNat_ofNat, BitVec.toNat_setWidth, Nat.reducePow, Nat.reduceMod] at hf
    try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
    and_intros
    all_goals first | exact True.intro | with_reducible assumption | omega | xg_bvext | xg_nat | xg_bstore | grind_cells'

set_option maxHeartbeats 300000 in
theorem blk_Lbb7d (k : Nat) (hk : k ≤ 2 ^ 32) (hms : MemsetSpec k) (x : XGenArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_x_gen.Lbb7d" := by
  cfg_block
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨⟨hC, ⟨⟨hsp, hbp, hbx⟩, h12, h14, hi2, hk1, hk2, hax, hcx, hdi, h9, h10, h11, h13⟩, hm⟩,
    hn⟩ := hs₀
  have hI := xgIT_cases x hC.2.2.2.2.2
  have hl0 : Mem.loadInt s₀.dmem (s₀.regs.get64 .rbx + 84#64) 4
      = some (Int.ofBytes (Int.toBytes 4 x.kx0.toInt)) := by
    have hm' := hm
    simp only [T, SbrW_open] at hm'
    rw [hbx]
    exact Mem.Val.loadInt hm' (Mem.Split.right (Mem.Split.here _ _) _) (Int.toBytes_length _ _)
      (by decide)
  have hl1 : Mem.loadInt s₀.dmem (s₀.regs.get64 .rbx + 92#64) 4
      = some (Int.ofBytes (Int.toBytes 4 x.m0.toInt)) := by
    have hm' := hm
    simp only [T, SbrW_open] at hm'
    rw [hbx]
    exact Mem.Val.loadInt hm' (Mem.Split.right (Mem.Split.right (Mem.Split.right
      (Mem.Split.here _ _) _) _) _) (Int.toBytes_length _ _) (by decide)
  have hv0 : BitVec.ofInt 32 (Int.ofBytes (Int.toBytes 4 x.kx0.toInt)) = x.kx0 := by
    rw [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt_toInt]
  have hv1 : BitVec.ofInt 32 (Int.ofBytes (Int.toBytes 4 x.m0.toInt)) = x.m0 := by
    rw [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt_toInt]
  clear hms
  vcgen
  all_goals try subst_vars
  all_goals try dsimp only at *
  all_goals call_simp
  all_goals try simp only [AddrIndex.offset64, Int64.toBitVec_ofNat_norm, Int64.toBitVec_zero,
    BitVec.ofNat_eq_ofNat, BitVec.add_zero] at *
  all_goals try simp only [hl0, hl1, Option.isSome_some, Option.some.injEq] at *
  all_goals try subst_vars
  all_goals try simp only [hv0, hv1] at *
  case vc3 =>
    left
    refine Table.ofLabels_at (l := "sbr_x_gen.Lbba9") ⟨by decide, ?_⟩
    simp only [table]
    call_simp
    and_intros
    all_goals first | exact True.intro | with_reducible assumption | omega | (simp only [FrMW_open, FrBW_open] at hm ⊢; grind_cells')
  case vc4 =>
    rename_i hnz hnc
    simp only [hcx] at hnz
    simp only [CondCode.interp_nc, CondCode.interp_nz, StatusFlags.cf_from_result,
      StatusFlags.zf_from_result, BitVec.unsigned_eq, BitVec.sub_cf_eq_decide_lt, BitVec.sub_beq_zero,
      Bool.not_eq_true', Bool.not_eq_false', bne_iff_ne, ne_eq, decide_eq_true_eq,
      decide_eq_false_iff_not] at hnz hnc
    simp -implicitDefEqProofs only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_add, xg_toNat_one64,
      Nat.reducePow, Nat.reduceMod] at hnz hnc
    left
    refine Table.ofLabels_at (l := "sbr_x_gen.Lba50") ⟨by decide, ?_⟩
    simp only [table]
    call_simp
    and_intros
    all_goals first | exact True.intro | with_reducible assumption | omega | ((try simp only [h9, h10, h11, h13]); xg_bvext) | xg_nat | xg_bstore | grind_cells'
  case vc5 =>
    exfalso
    rename_i hnz hnc
    simp only [hcx] at hnz
    simp only [CondCode.interp_nc, CondCode.interp_nz, StatusFlags.cf_from_result,
      StatusFlags.zf_from_result, BitVec.unsigned_eq, BitVec.sub_cf_eq_decide_lt, BitVec.sub_beq_zero,
      Bool.not_eq_true', Bool.not_eq_false', bne_iff_ne, ne_eq, decide_eq_true_eq,
      decide_eq_false_iff_not] at hnz hnc
    simp -implicitDefEqProofs only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_add, xg_toNat_one64,
      Nat.reducePow, Nat.reduceMod] at hnz hnc
    omega

theorem blk_Lbba4 (k : Nat) (hk : k ≤ 2 ^ 32) (hms : MemsetSpec k) (x : XGenArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_x_gen.Lbba4" := by
  cfg_block
  intro n
  exact Triple.intro fun s hs => hs.1.elim

theorem blk_Lbba9 (k : Nat) (hk : k ≤ 2 ^ 32) (hms : MemsetSpec k) (x : XGenArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_x_gen.Lbba9" := by
  cfg_block
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨⟨hC, ⟨hsp, hbp, hbx⟩, h12, h14, hm⟩, hn⟩ := hs₀
  have hI := xgIT_cases x hC.2.2.2.2.2
  have hl : Mem.loadInt s₀.dmem (s₀.regs.get64 .rbx + 88#64) 4
      = some (Int.ofBytes (Int.toBytes 4 x.kx1.toInt)) := by
    have hm' := hm
    simp only [T, SbrW_open] at hm'
    rw [hbx]
    exact Mem.Val.loadInt hm' (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _)
      (Int.toBytes_length _ _) (by decide)
  have hv32 : BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.ofInt 32 (Int.ofBytes (Int.toBytes 4 x.kx1.toInt))))
      = x.kx1 := by
    rw [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt_toInt]
    apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [BitVec.toNat_setWidth]; omega
  have hv : BitVec.setWidth 64 (BitVec.ofInt 32 (Int.ofBytes (Int.toBytes 4 x.kx1.toInt)))
      = BitVec.ofNat 64 x.kx1.toNat := by
    rw [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt_toInt]
    apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have hv64 : BitVec.setWidth 64 x.kx1 = BitVec.ofNat 64 x.kx1.toNat := by
    apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have hg : BitVec.toInt (BitVec.setWidth 32 (s₀.regs.get64 .r14)) ≤ 37 := by
    rw [h14]; rcases hI with h | h | h | h <;> rw [h] <;> decide
  have h37 : (BitVec.setWidth 32 (37#64)).toInt = 37 := by decide
  clear hms
  vcgen
  all_goals try subst_vars
  all_goals try dsimp only at *
  all_goals call_simp
  all_goals try simp only [AddrIndex.offset64, Int64.toBitVec_ofNat_norm, BitVec.add_zero] at *
  all_goals try simp only [hl, Option.isSome_some, Option.some.injEq] at *
  all_goals try subst_vars
  all_goals try simp only [hv32] at *
  all_goals try simp only [hv, hv64] at *
  all_goals try simp only [CondCode.interp_z, StatusFlags.zf_from_result, BitVec.and_self,
    BitVec.beq_zero_eq_decide, CondCode.interp_g_cmp_toInt32, h37, decide_eq_true_eq,
    decide_eq_false_iff_not, Bool.not_eq_true', Bool.not_eq_false', not_lt] at *
  · left
    refine Table.ofLabels_at (l := "sbr_x_gen.Lbd11") ⟨by decide, ?_⟩
    simp only [table]
    call_simp
    and_intros
    all_goals first | with_reducible assumption | rfl | omega | trivial | xg_bvext | xg_nat | xg_bstore | grind_cells'
  · exfalso; rename_i hf hz; simp only [CondCode.interp_g_cmp_toInt32, h37, decide_eq_true_eq] at hf; omega
  · try simp only [table]
    call_simp
    and_intros
    all_goals first | with_reducible assumption | rfl | omega | trivial | xg_bvext | xg_nat | xg_bstore | grind_cells'

-- `shl $i, %r64`: `MachineWP.shl_reg64_imm_spec` (`Kraken.Rules.HelperLemmas`), from here on.
open scoped Kraken.HelperLemmas.Shl64

theorem blk_c0 (k : Nat) (hk : k ≤ 2 ^ 32) (hms : MemsetSpec k) (x : XGenArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_x_gen.c0" := by
  cfg_block
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨⟨hC, ⟨hsp, hbp, hbx⟩, h12, h14, hk1, hm⟩, hn⟩ := hs₀
  have hI := xgIT_cases x hC.2.2.2.2.2
  have hcx := xg_sext32 _ _ h14 (by omega)
  have hsi : BitVec.ofNat 64 (xgIT x) + 18446744073709551581#64 = BitVec.ofNat 64 (xgIT x) - 35#64 := by
    rw [BitVec.sub_eq_add_neg]; rfl
  have hsh : BitVec.ofNat 64 (xgIT x) <<< 8 = BitVec.ofNat 64 (256 * xgIT x) := by
    rcases hI with h | h | h | h <;> rw [h] <;> rfl
  have hx0 : ∀ v : BitVec 32, BitVec.setWidth 64 (v ^^^ v) = 0#64 := by
    intro v; simp
  have hr9 : BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32
      (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 2#64)
        - BitVec.ofNat 64 (xgIT x)))) <<< 5)) &&& BitVec.setWidth 32 64#64)
      = BitVec.ofNat 64 (if xgIT x % 4 = 0 then 64 else 0) := by
    rcases hI with h | h | h | h <;> rw [h] <;> rfl
  have hl : Mem.loadInt s₀.dmem (s₀.regs.get64 .rbp + 0 + 18446744073709551568#64) 8
      = some (Int.ofBytes (Int.toBytes 8 (arg1 t₀).toInt)) := by
    have hm' := hm
    simp only [T, FM, FrMW_open, FrML] at hm'
    have ha : s₀.regs.get64 .rbp + 0 + 18446744073709551568#64 = t₀.regs.get64 .rsp - 56#64 := by
      rw [hbp, BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.add_assoc]; rfl
    rw [ha]
    exact Mem.Val.loadInt hm' (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _)
      (Int.toBytes_length _ _) (by decide)
  have hv : BitVec.ofInt 64 (Int.ofBytes (Int.toBytes 8 (arg1 t₀).toInt)) = arg1 t₀ := by
    rw [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]
  clear hms
  vcgen
  all_goals try subst_vars
  all_goals try dsimp only at *
  all_goals call_simp
  all_goals try simp only [AddrIndex.offset64, Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm,
    Nat.reducePow, Nat.reduceMod, Nat.reduceSub] at *
  all_goals try simp only [hl, Option.isSome_some, Option.some.injEq] at *
  all_goals try subst_vars
  all_goals try simp only [hv] at *
  all_goals try simp only [table]
  all_goals call_simp
  all_goals try simp only [FrMW_open] at *
  all_goals try simp -implicitDefEqProofs only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, ↓reduceIte,
    Reg64s.get64_set64, Reg64s.get_low32, reduceCtorEq, ite_true, ite_false]
  all_goals try simp -implicitDefEqProofs only [hcx, hsi, hsh, hx0, hr9, h12, BitVec.toNat_ofNat, Nat.zero_mod, Nat.mul_zero,
    Nat.add_zero, Nat.sub_zero, Width.bytes, BitVec.mul_one, BitVec.setWidth_eq, BitVec.ofNat_add, BitVec.add_zero]
  all_goals try and_intros
  all_goals first | exact trivial | exact not_false | exact hm | (apply congrArg (· - BitVec.ofNat 64 (xgIT x)); rfl) | ac_rfl | with_reducible assumption | omega

theorem blk_Lbc00 (k : Nat) (hk : k ≤ 2 ^ 32) (hms : MemsetSpec k) (x : XGenArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_x_gen.Lbc00" := by
  cfg_block
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨⟨hC, ⟨⟨hsp, hbp, hbx⟩, h14, hk, hcx, hdx, hsi, hdi, h8, h9, h10, h12⟩, hm⟩, hn⟩ := hs₀
  have hI := xgIT_cases x hC.2.2.2.2.2
  have hx0 : ∀ v : BitVec 32, BitVec.setWidth 64 (v ^^^ v) = 0#64 := by
    intro v; simp
  clear hms
  vcgen
  all_goals try subst_vars
  all_goals try dsimp only at *
  all_goals call_simp
  all_goals try simp only [AddrIndex.offset64, Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm,
    Nat.reducePow, Nat.reduceMod, Nat.reduceSub] at *
  all_goals try simp only [CondCode.interp_z, CondCode.interp_nz, StatusFlags.zf_from_result,
    Reg64s.get_low8, Reg64s.get_low32] at *
  · rename_i hf
    rw [hdx] at hf
    have hE : xgIT x % 4 = 2 := by
      rcases hI with h | h | h | h <;> rw [h] at hf ⊢ <;> first | rfl | (revert hf; decide)
    left
    refine Table.ofLabels_at (l := "sbr_x_gen.Lbc39") ⟨by decide, ?_⟩
    simp only [table]
    call_simp
    simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hE, ↓reduceIte, Nat.add_zero]
    and_intros
    all_goals first | exact trivial | with_reducible assumption | omega | (rw [h9]; simp [hE])
  · rename_i hf
    rw [hdx] at hf
    have hE : xgIT x % 4 = 0 := by
      rcases hI with h | h | h | h <;> rw [h] at hf ⊢ <;> first | rfl | (revert hf; decide)
    try simp only [table]
    call_simp
    simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hE, ↓reduceIte, Nat.add_zero, hx0,
      BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_div, Nat.mul_zero]
    and_intros
    all_goals first | exact trivial | with_reducible assumption | omega | (rw [h9]; simp [hE])

set_option maxHeartbeats 300000 in
theorem blk_Lbc10 (k : Nat) (hk : k ≤ 2 ^ 32) (hms : MemsetSpec k) (x : XGenArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_x_gen.Lbc10" := by
  cfg_block
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨⟨hC, ⟨⟨hsp, hbp, hbx⟩, h14, hk, hcx, hdx, hsi, hdi, h8, h9, h10, h12⟩, hE, h15, hj, h11, hm⟩, hn⟩ := hs₀
  have hI := xgIT_cases x hC.2.2.2.2.2
  generalize (s₀.regs.get64 .r15).toNat / 32 = j at *
  simp only [hE, ↓reduceIte] at h9
  have hj0 : (BitVec.ofNat 64 (32 * j)).toNat = 32 * j := by
    simp -implicitDefEqProofs only [BitVec.toNat_ofNat]; omega
  have hj1 : (BitVec.ofNat 64 (32 * j + 32)).toNat = 32 * j + 32 := by
    simp -implicitDefEqProofs only [BitVec.toNat_ofNat]; omega
  have hj2 : (BitVec.ofNat 64 (32 + 32 * j)).toNat = 32 + 32 * j := by
    simp -implicitDefEqProofs only [BitVec.toNat_ofNat]; omega
  clear hms
  vcgen
  all_goals try subst_vars
  all_goals try dsimp only at *
  all_goals opaque_stores
  all_goals try simp only [AddrIndex.offset64, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat,
    BitVec.add_zero, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd] at *
  all_goals try simp only [h8, h11, hdi, h15, Width.bytes, BitVec.mul_one, BitVec.add_assoc,
    Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reducePow, Nat.reduceMod,
    Nat.reduceSub]
  all_goals try simp only [← BitVec.ofNat_add, ← BitVec.ofNat_mul, ← Nat.add_assoc]
  all_goals try simp (disch := omega) only [BitVec.ofNat64_add_wrap, Nat.reduceSub, Nat.reducePow,
    Nat.reduceAdd]
  case vc1 => grind_cells'
  case vc2 => grind_cells'
  case vc3 => grind_cells'
  case vc4 =>
    repeat (with_reducible apply Mem.loadInt_isSome_storeInt)
    grind (ematch := 400) (gen := 400) (instances := 20000) (splits := 40) (mbtc := false)
      [-BitVec.toInt_eq_toNat_of_msb, -BitVec.toInt_eq_toNat_bmod]
  all_goals rename_i hf _ _ _
  all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ↓reduceIte, h9, h15,
    BitVec.setWidth_eq, ← BitVec.ofNat_add] at hf
  all_goals try simp (disch := omega) only [CondCode.interp_nz, CondCode.interp_z, StatusFlags.zf_from_result,
    h9, h15, BitVec.setWidth_eq, ← BitVec.ofNat_add, Bool.not_eq_true', Bool.not_eq_false',
    BitVec.ofNat64_sub_beq_zero, BitVec.ofNat64_sub_lit_beq_zero, decide_eq_true_eq,
    decide_eq_false_iff_not] at hf
  case vc5 =>
    left
    refine Table.ofLabels_at (l := "sbr_x_gen.Lbc10") ⟨by decide, ?_⟩
    simp only [table]
    call_simp
    simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ↓reduceIte, h15, h9,
      BitVec.setWidth_eq, ← BitVec.ofNat_add, hj2, hE]
    and_intros
    all_goals first | exact trivial | with_reducible assumption | omega | (congr 1; omega) | xg_bstore | (grind (ematch := 400) (gen := 400) (instances := 20000) (splits := 40) (mbtc := false) [-BitVec.toInt_eq_toNat_of_msb, -BitVec.toInt_eq_toNat_bmod])
  case vc6 =>
    try simp only [table]
    call_simp
    simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ↓reduceIte, h15, h9,
      BitVec.setWidth_eq, ← BitVec.ofNat_add, hj2, hE]
    and_intros
    all_goals first | exact trivial | with_reducible assumption | omega | (congr 1; omega) | xg_bstore | (grind (ematch := 400) (gen := 400) (instances := 20000) (splits := 40) (mbtc := false) [-BitVec.toInt_eq_toNat_of_msb, -BitVec.toInt_eq_toNat_bmod])

theorem blk_Lbc39 (k : Nat) (hk : k ≤ 2 ^ 32) (hms : MemsetSpec k) (x : XGenArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_x_gen.Lbc39" := by
  cfg_block
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨⟨hC, ⟨⟨hsp, hbp, hbx⟩, h14, hk, hcx, hdx, hsi, hdi, h8, h9, h10, h12⟩, h11, hm⟩, hn⟩ := hs₀
  have hI := xgIT_cases x hC.2.2.2.2.2
  generalize he : (if xgIT x % 4 = 0 then 2 else 0) = e at *
  have he2 : (xgIT x % 4 = 0 ∧ e = 2) ∨ (xgIT x % 4 = 2 ∧ e = 0) := by
    split at he <;> omega
  have he' : e = 0 ∨ e = 2 := by omega
  have hsh : BitVec.ofNat 64 (xgIT x + e) <<< 8 = BitVec.ofNat 64 (256 * (xgIT x + e)) := by
    rcases hI with h | h | h | h <;> rcases he' with h' | h' <;> rw [h, h'] <;> rfl
  have hr : (BitVec.ofNat 64 (xgIT x + e + 5)).toNat = xgIT x + e + 5 := by
    simp -implicitDefEqProofs only [BitVec.toNat_ofNat]; omega
  clear hms
  vcgen
  all_goals try subst_vars
  all_goals try dsimp only at *
  all_goals call_simp
  all_goals try simp only [AddrIndex.offset64, Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm,
    Nat.reducePow, Nat.reduceMod, Nat.reduceSub] at *
  case vc1 =>
    exfalso
    rename_i hf
    rw [hsi] at hf
    rcases hI with h | h | h | h <;> rw [h] at hf <;> revert hf <;> decide
  case vc2 => decide
  case vc3 =>
    try simp only [table]
    call_simp
    simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ↓reduceIte, h11, h10, hsh,
      BitVec.setWidth_eq, ← BitVec.ofNat_add, hr, Nat.add_sub_cancel]
    and_intros
    all_goals try (first | exact trivial | with_reducible assumption | omega | (congr 1; omega))
    all_goals (simp -implicitDefEqProofs only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, hsh]; simp only [BitVec.ofNat_add]; ac_rfl)

set_option maxHeartbeats 400000 in
theorem blk_Lbc50 (k : Nat) (hk : k ≤ 2 ^ 32) (hms : MemsetSpec k) (x : XGenArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_x_gen.Lbc50" := by
  cfg_block
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨⟨hC, ⟨⟨hsp, hbp, hbx⟩, h14, hk, hcx, hdx, hsi, hdi, h8, h9, h10, h12⟩, h15, hm5, hm43, hm4, h11, hm⟩, hn⟩ := hs₀
  have hI := xgIT_cases x hC.2.2.2.2.2
  generalize (s₀.regs.get64 .r15).toNat = m at *
  clear hms
  vcgen
  all_goals try subst_vars
  all_goals try dsimp only at *
  all_goals opaque_stores
  all_goals try simp only [AddrIndex.offset64, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat,
    BitVec.add_zero, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd] at *
  all_goals try simp only [h12, h11, h15, Width.bytes, BitVec.mul_one, BitVec.add_assoc,
    Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reducePow, Nat.reduceMod,
    Nat.reduceSub]
  all_goals try simp only [← BitVec.ofNat_add, ← BitVec.ofNat_mul, ← Nat.add_assoc]
  all_goals try simp (disch := omega) only [BitVec.ofNat64_add_wrap, Nat.reduceSub, Nat.reducePow,
    Nat.reduceAdd]
  case vc1 | vc2 | vc3 | vc4 | vc5 | vc6 | vc7 | vc8 =>
    (repeat (with_reducible apply Mem.loadInt_isSome_storeInt))
    (grind (ematch := 400) (gen := 400) (instances := 20000) (splits := 40) (mbtc := false) [-BitVec.toInt_eq_toNat_of_msb, -BitVec.toInt_eq_toNat_bmod])
  case vc9 =>
    try simp only [table]
    call_simp
    try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ↓reduceIte]
    and_intros
    all_goals first | exact trivial | with_reducible assumption | omega | (congr 1; omega) | xg_bstore | (grind (ematch := 400) (gen := 400) (instances := 20000) (splits := 40) (mbtc := false) [-BitVec.toInt_eq_toNat_of_msb, -BitVec.toInt_eq_toNat_bmod])

theorem blk_c2 (k : Nat) (hk : k ≤ 2 ^ 32) (hms : MemsetSpec k) (x : XGenArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_x_gen.c2" := by
  cfg_block
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨⟨hC, ⟨⟨hsp, hbp, hbx⟩, h14, hk, hcx, hdx, hsi, hdi, h8, h9, h10, h12⟩, hm5, hm43, hm4, h11, hm⟩, hn⟩ := hs₀
  have h15 : s₀.regs.get64 .r15 = BitVec.ofNat 64 (s₀.regs.get64 .r15).toNat := by simp
  have hI := xgIT_cases x hC.2.2.2.2.2
  generalize (s₀.regs.get64 .r15).toNat = m at *
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 5 := ⟨m - 5, by omega⟩
  clear hms
  vcgen
  all_goals try subst_vars
  all_goals try dsimp only at *
  all_goals opaque_stores
  all_goals try simp only [AddrIndex.offset64, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat,
    BitVec.add_zero, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd] at *
  all_goals try simp only [h12, h11, h15, Width.bytes, BitVec.mul_one, BitVec.add_assoc,
    Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reducePow, Nat.reduceMod,
    Nat.reduceSub]
  all_goals try simp only [← BitVec.ofNat_add, ← BitVec.ofNat_mul, ← Nat.add_assoc]
  all_goals try simp (disch := omega) only [BitVec.ofNat64_add_wrap, Nat.reduceSub, Nat.reducePow,
    Nat.reduceAdd]
  all_goals try simp only [Nat.add_sub_cancel, Nat.add_mul, Nat.mul_add, Nat.add_assoc] at *
  all_goals try simp (disch := omega) only [Nat.add_sub_assoc, Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd] at *
  case vc1 | vc2 | vc3 | vc4 | vc5 | vc6 | vc7 | vc8 =>
    (repeat (with_reducible apply Mem.loadInt_isSome_storeInt))
    (grind (ematch := 400) (gen := 400) (instances := 20000) (splits := 40) (mbtc := false) [-BitVec.toInt_eq_toNat_of_msb, -BitVec.toInt_eq_toNat_bmod])
  case vc9 =>
    try simp only [table]
    call_simp
    try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ↓reduceIte]
    and_intros
    all_goals first | exact trivial | with_reducible assumption | omega | (congr 1; omega) | xg_bstore | (grind (ematch := 400) (gen := 400) (instances := 20000) (splits := 40) (mbtc := false) [-BitVec.toInt_eq_toNat_of_msb, -BitVec.toInt_eq_toNat_bmod])

theorem blk_c3 (k : Nat) (hk : k ≤ 2 ^ 32) (hms : MemsetSpec k) (x : XGenArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_x_gen.c3" := by
  cfg_block
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨⟨hC, ⟨⟨hsp, hbp, hbx⟩, h14, hk, hcx, hdx, hsi, hdi, h8, h9, h10, h12⟩, hm5, hm43, hm4, h11, hm⟩, hn⟩ := hs₀
  have h15 : s₀.regs.get64 .r15 = BitVec.ofNat 64 (s₀.regs.get64 .r15).toNat := by simp
  have hI := xgIT_cases x hC.2.2.2.2.2
  generalize (s₀.regs.get64 .r15).toNat = m at *
  have hm4' : (BitVec.ofNat 64 (m + 4)).toNat = m + 4 := by
    simp -implicitDefEqProofs only [BitVec.toNat_ofNat]; omega
  clear hms
  vcgen
  all_goals try subst_vars
  all_goals try dsimp only at *
  all_goals call_simp
  all_goals try simp only [AddrIndex.offset64, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat,
    Nat.reducePow, Nat.reduceMod, Nat.reduceSub] at *
  case vc1 =>
    rename_i hf
    have hne : m + 4 ≠ 43 := by
      intro h
      have h39 : m = 39 := by omega
      subst h39
      rw [h15] at hf
      revert hf
      decide
    have e4 : (4#64 : BitVec 64) + BitVec.ofNat 64 m = BitVec.ofNat 64 (m + 4) := by
      rw [BitVec.add_comm, ← BitVec.ofNat_add]
    have hmK : (BitVec.ofNat 64 m).toNat = m := by
      simp -implicitDefEqProofs only [BitVec.toNat_ofNat]; omega
    left
    refine Table.ofLabels_at (l := "sbr_x_gen.Lbc50") ⟨by decide, ?_⟩
    try simp only [table]
    call_simp
    try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ↓reduceIte, h15, h11,
      BitVec.setWidth_eq]
    refine ⟨⟨hC, ?_⟩, ?_⟩
    and_intros
    all_goals try simp only [e4, hm4', hmK]
    all_goals try (first | exact trivial | with_reducible assumption | omega)
    all_goals first
      | (rw [BitVec.add_comm, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega)
      | (left; omega)
  case vc2 =>
    refine ⟨⟨hC, ⟨⟨hsp, hbp, hbx⟩, h14, hk, hcx, hdx, hsi, hdi, h8, h9, h10, h12⟩, hm⟩, ?_⟩
    rw [h15]; simp -implicitDefEqProofs only [BitVec.toNat_ofNat]; omega

set_option maxHeartbeats 300000 in
theorem blk_Lbce0 (k : Nat) (hk : k ≤ 2 ^ 32) (hms : MemsetSpec k) (x : XGenArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_x_gen.Lbce0" := by
  cfg_block
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨⟨hC, ⟨⟨hsp, hbp, hbx⟩, h14, hk, hcx, hdx, hsi, hdi, h8, h9, h10, h12⟩, hm⟩, hn⟩ := hs₀
  have hl : Mem.loadInt s₀.dmem (s₀.regs.get64 .rbx + 88#64) 4
      = some (Int.ofBytes (Int.toBytes 4 x.kx1.toInt)) := by
    have hm' := hm
    simp only [T, SbrW_open] at hm'
    rw [hbx]
    exact Mem.Val.loadInt hm' (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _)
      (Int.toBytes_length _ _) (by decide)
  have hv : BitVec.setWidth 64 (BitVec.ofInt 32 (Int.ofBytes (Int.toBytes 4 x.kx1.toInt)))
      = BitVec.ofNat 64 x.kx1.toNat := by
    rw [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt_toInt]
    apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  clear hms
  vcgen
  all_goals try subst_vars
  all_goals try dsimp only at *
  all_goals call_simp
  all_goals try simp only [AddrIndex.offset64, Int64.toBitVec_ofNat_norm, BitVec.add_zero] at *
  all_goals try simp only [hl, Option.isSome_some, Option.some.injEq] at *
  all_goals try subst_vars
  all_goals try simp only [hv, BitVec.setWidth_eq, CondCode.interp_nc, CondCode.interp_nz,
    CondCode.interp_z, StatusFlags.cf_from_result, StatusFlags.zf_from_result, BitVec.unsigned_eq,
    BitVec.sub_cf64_eq_decide_lt, BitVec.sub64_beq_zero, Bool.not_eq_true', Bool.not_eq_false',
    decide_eq_true_eq, decide_eq_false_iff_not] at *
  all_goals try simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_ofNat, xg_toNat_one64,
    Nat.reducePow, Nat.reduceMod] at *
  case vc2 =>
    left
    refine Table.ofLabels_at (l := "sbr_x_gen.Lbd16") ⟨by decide, ?_⟩
    simp only [table]
    call_simp
    and_intros
    all_goals first | with_reducible assumption | rfl | omega | ((try simp only [hdi, h8, h10, h12]); xg_bvext) | xg_nat | xg_bstore | grind_cells'
  case vc3 =>
    left
    refine Table.ofLabels_at (l := "sbr_x_gen.Lbc00") ⟨by decide, ?_⟩
    simp only [table]
    call_simp
    and_intros
    all_goals first | with_reducible assumption | rfl | omega | ((try simp only [hdi, h8, h10, h12]); xg_bvext) | xg_nat | xg_bstore | grind_cells'
  case vc4 =>
    exfalso
    omega

theorem blk_t2 (k : Nat) (hk : k ≤ 2 ^ 32) (hms : MemsetSpec k) (x : XGenArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_x_gen.t2" := by
  cfg_block
  intro n
  exact Triple.intro fun s hs => hs.1.elim

theorem blk_Lbd11 (k : Nat) (hk : k ≤ 2 ^ 32) (hms : MemsetSpec k) (x : XGenArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_x_gen.Lbd11" := by
  cfg_block
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨⟨hC, ⟨hsp, hbp, hbx⟩, h14, hk1, hm⟩, hn⟩ := hs₀
  clear hms
  vcgen
  all_goals try subst_vars
  all_goals try dsimp only at *
  all_goals call_simp
  all_goals try simp only [BitVec.xor_self, BitVec.setWidth_zero, BitVec.toNat_zero, kx1n, hk1]
  and_intros
  all_goals first | exact True.intro | omega | rfl | with_reducible assumption | grind_cells'

set_option maxHeartbeats 300000 in
theorem blk_Lbd16 (k : Nat) (hk : k ≤ 2 ^ 32) (hms : MemsetSpec k) (x : XGenArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_x_gen.Lbd16" := by
  cfg_block
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨⟨hC, ⟨hsp, hbp, hbx⟩, h14, hax, h11, hm⟩, hn⟩ := hs₀
  have hI := xgIT_cases x hC.2.2.2.2.2
  have hl : Mem.loadInt s₀.dmem (s₀.regs.get64 .rbx + 96#64) 4
      = some (Int.ofBytes (Int.toBytes 4 x.m1.toInt)) := by
    have hm' := hm
    simp only [T, SbrW_open] at hm'
    rw [hbx]
    exact Mem.Val.loadInt hm' (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right
      (Mem.Split.here _ _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
  have hv : BitVec.ofInt 32 (Int.ofBytes (Int.toBytes 4 x.m1.toInt)) = x.m1 := by
    rw [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt_toInt]
  clear hms
  vcgen
  all_goals try subst_vars
  all_goals try dsimp only at *
  all_goals call_simp
  all_goals try simp only [AddrIndex.offset64, Int64.toBitVec_ofNat_norm, Int64.toBitVec_zero,
    BitVec.ofNat_eq_ofNat, BitVec.add_zero] at *
  all_goals try simp only [hl, Option.isSome_some, Option.some.injEq] at *
  all_goals try subst_vars
  all_goals try simp only [hv] at *
  case vc2 =>
    left
    refine Table.ofLabels_at (l := "sbr_x_gen.Lbed8") ⟨by decide, ?_⟩
    simp only [table]
    call_simp
    and_intros
    all_goals first | exact True.intro | with_reducible assumption | omega | grind_cells'
  case vc3 =>
    left
    refine Table.ofLabels_at (l := "sbr_x_gen.Lbed8") ⟨by decide, ?_⟩
    simp only [table]
    call_simp
    and_intros
    all_goals first | exact True.intro | with_reducible assumption | omega | grind_cells'
  case vc4 =>
    exfalso
    rename_i _ ha _
    simp only [hax, CondCode.interp_a, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
      BitVec.unsigned_eq, BitVec.sub_cf_eq_decide_lt, BitVec.sub_beq_zero, Bool.and_eq_true,
      Bool.not_eq_true', Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not] at ha
    simp -implicitDefEqProofs only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at ha
    omega
  case vc5 =>
    rename_i _ _ hnc
    simp only [hax, h11, CondCode.interp_nc, StatusFlags.cf_from_result,
      BitVec.unsigned_eq, BitVec.sub_cf_eq_decide_lt, Bool.not_eq_true', Bool.not_eq_false',
      decide_eq_true_eq, decide_eq_false_iff_not] at hnc
    simp -implicitDefEqProofs only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_add, Nat.reducePow,
      Nat.reduceMod] at hnc
    have h65 : x.kx1.toNat < 65 := by omega
    try simp only [table]
    simp only [hax, CondCode.interp_nc, StatusFlags.cf_from_result,
      BitVec.unsigned_eq, BitVec.sub_cf_eq_decide_lt, Bool.not_eq_true', Bool.not_eq_false',
      decide_eq_true_eq, decide_eq_false_iff_not]
    simp -implicitDefEqProofs only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    have hC' := hC
    obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6⟩ := hC'
    and_intros
    all_goals first | exact True.intro | with_reducible assumption | omega | rfl | (rw [if_neg (by omega)]; rfl) | grind_cells'

theorem blk_d0 (k : Nat) (hk : k ≤ 2 ^ 32) (hms : MemsetSpec k) (x : XGenArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_x_gen.d0" := by
  cfg_block
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨⟨hC, ⟨hsp, hbp, hbx⟩, h14, hax, hm1, hcx, hm⟩, hn⟩ := hs₀
  have hI := xgIT_cases x hC.2.2.2.2.2
  have hl : Mem.loadInt s₀.dmem (s₀.regs.get64 .rbp + 0 + 18446744073709551568#64) 8
      = some (Int.ofBytes (Int.toBytes 8 (arg1 t₀).toInt)) := by
    have hm' := hm
    simp only [T, FM, FrMW_open, FrML] at hm'
    have ha : s₀.regs.get64 .rbp + 0 + 18446744073709551568#64 = t₀.regs.get64 .rsp - 56#64 := by
      rw [hbp, BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.add_assoc]; rfl
    rw [ha]
    exact Mem.Val.loadInt hm' (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _)
      (Int.toBytes_length _ _) (by decide)
  have hv : BitVec.ofInt 64 (Int.ofBytes (Int.toBytes 8 (arg1 t₀).toInt)) = arg1 t₀ := by
    rw [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]
  clear hms
  vcgen
  all_goals try subst_vars
  all_goals try dsimp only at *
  all_goals call_simp
  all_goals try simp only [AddrIndex.offset64, Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm,
    Nat.reducePow, Nat.reduceMod, Nat.reduceSub] at *
  all_goals try simp only [hl, Option.isSome_some, Option.some.injEq] at *
  all_goals try subst_vars
  all_goals try simp only [hv] at *
  all_goals try simp only [table]
  all_goals call_simp
  all_goals try simp -implicitDefEqProofs only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, ↓reduceIte,
    Reg64s.get64_set64, Reg64s.get_low32, reduceCtorEq, ite_true, ite_false]
  all_goals try simp only [h14, hax, hcx]
  all_goals try and_intros
  all_goals first | exact trivial | exact not_false | exact hm | with_reducible assumption | omega | (rcases hI with h | h | h | h <;> simp only [h] <;> decide) | ((try simp only [Width.bytes]); xg_bvext)

theorem blk_d1 (k : Nat) (hk : k ≤ 2 ^ 32) (hms : MemsetSpec k) (x : XGenArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_x_gen.d1" := by
  cfg_block
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨⟨hC, ⟨hsp, hbp, hbx⟩, hax, hm1, hcx, hdx, hsi, h14, hdi, h11, hm⟩, hn⟩ := hs₀
  have hI := xgIT_cases x hC.2.2.2.2.2
  have hl : Mem.loadInt s₀.dmem (s₀.regs.get64 .rbp + 0 + 18446744073709551560#64) 8
      = some (Int.ofBytes (Int.toBytes 8 (arg3 t₀).toInt)) := by
    have hm' := hm
    simp only [T, FM, FrMW_open, FrML] at hm'
    have ha : s₀.regs.get64 .rbp + 0 + 18446744073709551560#64 = t₀.regs.get64 .rsp - 64#64 := by
      rw [hbp, BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.add_assoc]; rfl
    rw [ha]
    exact Mem.Val.loadInt hm' (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _)
      (Int.toBytes_length _ _) (by decide)
  have hv : BitVec.ofInt 64 (Int.ofBytes (Int.toBytes 8 (arg3 t₀).toInt)) = arg3 t₀ := by
    rw [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]
  clear hms
  vcgen
  all_goals try subst_vars
  all_goals try dsimp only at *
  all_goals call_simp
  all_goals try simp only [AddrIndex.offset64, Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm,
    Nat.reducePow, Nat.reduceMod, Nat.reduceSub] at *
  all_goals try simp only [hl, Option.isSome_some, Option.some.injEq] at *
  all_goals try subst_vars
  all_goals try simp only [hv] at *
  all_goals try simp only [table]
  all_goals call_simp
  all_goals try simp -implicitDefEqProofs only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, ↓reduceIte,
    Reg64s.get64_set64, Reg64s.get_low32, reduceCtorEq, ite_true, ite_false]
  all_goals try simp only [h14, hax, hcx, hdx, hsi, hdi, h11]
  all_goals try and_intros
  all_goals first | exact trivial | exact not_false | exact hm | with_reducible assumption | omega | (rcases hI with h | h | h | h <;> simp only [h] <;> decide) | ((try simp only [Width.bytes]); xg_bvext) | xg_nat

theorem blk_Lbdb0 (k : Nat) (hk : k ≤ 2 ^ 32) (hms : MemsetSpec k) (x : XGenArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_x_gen.Lbdb0" := by
  cfg_block
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨⟨hC, ⟨⟨hsp, hbp, hbx⟩, hk1, hk2, hcx, hdx, hsi, h14, hdi, h8, h9, h10, h11, h15⟩, hm⟩, hn⟩ := hs₀
  have hI := xgIT_cases x hC.2.2.2.2.2
  clear hms
  vcgen
  all_goals try subst_vars
  all_goals try dsimp only at *
  all_goals call_simp
  all_goals try simp only [BitVec.xor_self, BitVec.setWidth_zero]
  case vc1 =>
    rename_i hf
    simp only [hsi, CondCode.interp_z, StatusFlags.zf_from_result, BitVec.and_self,
      BitVec.beq_zero_eq_decide, decide_eq_true_eq] at hf
    left
    refine Table.ofLabels_at (l := "sbr_x_gen.Lbdec") ⟨by decide, ?_⟩
    simp only [table]
    call_simp
    and_intros
    all_goals first | exact True.intro | with_reducible assumption | omega | decide | (have hE : (if xgIT x % 4 = 2 then 2 else 0) = 0 := (by rcases hI with h | h | h | h <;> simp only [h] at hf ⊢ <;> revert hf <;> decide); rw [hE, Nat.add_zero]; exact hdx)
  case vc2 =>
    rename_i hf
    simp only [hsi, CondCode.interp_z, StatusFlags.zf_from_result, BitVec.and_self,
      BitVec.beq_zero_eq_decide, decide_eq_true_eq, Bool.not_eq_true, decide_eq_false_iff_not] at hf
    try simp only [table]
    call_simp
    and_intros
    all_goals first | exact True.intro | with_reducible assumption | omega | decide | (rcases hI with h | h | h | h <;> simp only [h] at hf ⊢ <;> revert hf <;> decide)

set_option maxHeartbeats 300000 in
theorem blk_Lbdc0 (k : Nat) (hk : k ≤ 2 ^ 32) (hms : MemsetSpec k) (x : XGenArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_x_gen.Lbdc0" := by
  cfg_block
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨⟨hC, ⟨⟨hsp, hbp, hbx⟩, hk1, hk2, hcx, hdx, hsi, h14, hdi, h8, h9, h10, h11, h15⟩, hE, h12, hj, hm⟩, hn⟩ := hs₀
  have hI := xgIT_cases x hC.2.2.2.2.2
  generalize (s₀.regs.get64 .r12).toNat / 256 = j at *
  simp only [hE, Nat.reduceMul, forall_const] at h9 h10 hsi
  have hj0 : (BitVec.ofNat 64 (256 * j)).toNat = 256 * j := by
    simp -implicitDefEqProofs only [BitVec.toNat_ofNat]; omega
  have hj1 : (BitVec.ofNat 64 (256 * j + 256)).toNat = 256 * j + 256 := by
    simp -implicitDefEqProofs only [BitVec.toNat_ofNat]; omega
  clear hms
  vcgen
  all_goals try subst_vars
  all_goals try dsimp only at *
  all_goals opaque_stores
  all_goals try simp only [AddrIndex.offset64, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat,
    BitVec.add_zero, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd] at *
  all_goals try simp only [h8, h12, hdi, Width.bytes, BitVec.mul_one, BitVec.add_assoc,
    Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reducePow, Nat.reduceMod,
    Nat.reduceSub]
  all_goals try simp only [BitVec.ofNat64_mul_ofNat, BitVec.ofNat64_mul_lit, ← BitVec.ofNat_add,
    ← Nat.add_assoc]
  all_goals try simp (disch := omega) only [BitVec.ofNat64_add_wrap, Nat.reduceSub, Nat.reducePow,
    Nat.reduceAdd]
  case vc1 | vc2 | vc3 | vc4 => grind_cells'
  all_goals rename_i hf _ _ _
  all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ↓reduceIte, h9, h12,
    BitVec.setWidth_eq, ← BitVec.ofNat_add] at hf
  all_goals simp only [CondCode.interp_nz, StatusFlags.zf_from_result, BitVec.sub_beq_zero,
    Bool.not_eq_true', Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not] at hf
  all_goals simp -implicitDefEqProofs only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hf
  case vc5 =>
    left
    refine Table.ofLabels_at (l := "sbr_x_gen.Lbdc0") ⟨by decide, ?_⟩
    simp only [table]
    call_simp
    simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ↓reduceIte, h12,
      BitVec.setWidth_eq, ← BitVec.ofNat_add, hj1, hE]
    and_intros
    all_goals first | exact trivial | with_reducible assumption | omega | (congr 1; omega) | xg_bstore | grind_cells'
  case vc6 =>
    try simp only [table]
    call_simp
    simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ↓reduceIte, h12,
      BitVec.setWidth_eq, ← BitVec.ofNat_add, hj1, hE]
    and_intros
    all_goals first | exact trivial | with_reducible assumption | omega | (congr 1; omega) | xg_bstore | grind_cells'

theorem blk_Lbdec (k : Nat) (hk : k ≤ 2 ^ 32) (hms : MemsetSpec k) (x : XGenArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_x_gen.Lbdec" := by
  cfg_block
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨⟨hC, ⟨⟨hsp, hbp, hbx⟩, hk1, hk2, hcx, hdx, hsi, h14, hdi, h8, h9, h10, h11, h15⟩, h12, hm⟩, hn⟩ := hs₀
  have hI := xgIT_cases x hC.2.2.2.2.2
  clear hms
  vcgen
  all_goals try subst_vars
  all_goals try dsimp only at *
  all_goals call_simp
  all_goals try simp only [Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, Nat.reducePow,
    Nat.reduceMod, Nat.reduceSub, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, h12, h14]
  case vc1 =>
    exfalso
    rename_i hf
    simp only [h14, Int64.toBitVec_ofNat_norm, CondCode.interp_c, StatusFlags.cf_from_result,
      BitVec.unsigned_eq, BitVec.sub_cf_eq_decide_lt, decide_eq_true_eq] at hf
    simp -implicitDefEqProofs only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hf
    omega
  case vc2 => decide
  case vc3 =>
    try simp only [table]
    and_intros
    all_goals first | exact trivial | exact hm | omega | (rcases hI with h | h | h | h <;> simp only [h, AddrIndex.offset64] <;> decide)

theorem blk_Lbe00 (k : Nat) (hk : k ≤ 2 ^ 32) (hms : MemsetSpec k) (x : XGenArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_x_gen.Lbe00" := by
  cfg_block
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨⟨hC, ⟨⟨hsp, hbp, hbx⟩, hk1, hk2, hcx, hdx, hsi, h14, hdi, h8, h9, h10, h11, h15⟩, h12, hmi, hm4, hm32, h13, hm⟩, hn⟩ := hs₀
  have hI := xgIT_cases x hC.2.2.2.2.2
  generalize (s₀.regs.get64 .r12).toNat / 256 = m at *
  clear hms
  vcgen
  all_goals try subst_vars
  all_goals try dsimp only at *
  all_goals opaque_stores
  all_goals try simp only [AddrIndex.offset64, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat,
    BitVec.add_zero, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd] at *
  all_goals try simp only [h12, h11, h15, Width.bytes, BitVec.mul_one, BitVec.add_assoc,
    Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reducePow, Nat.reduceMod,
    Nat.reduceSub]
  all_goals try simp only [BitVec.ofNat64_mul_ofNat, BitVec.ofNat64_mul_lit, ← BitVec.ofNat_add,
    ← Nat.add_assoc]
  all_goals try simp (disch := omega) only [BitVec.ofNat64_add_wrap, Nat.reduceSub, Nat.reducePow,
    Nat.reduceAdd]
  case vc1 | vc2 | vc3 | vc4 | vc5 | vc6 | vc7 | vc8 => grind_cells'
  case vc9 =>
    have h256 : (BitVec.ofNat 64 (256 * m)).toNat = 256 * m := by
      simp -implicitDefEqProofs only [BitVec.toNat_ofNat]; omega
    have hd : 256 * m / 256 = m := by omega
    try simp only [table]
    call_simp
    try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ↓reduceIte, h256, hd]
    and_intros
    all_goals first | exact trivial | exact hm | exact h13 | omega | (clear h256 hd; grind_cells')

theorem blk_d2 (k : Nat) (hk : k ≤ 2 ^ 32) (hms : MemsetSpec k) (x : XGenArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_x_gen.d2" := by
  cfg_block
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨⟨hC, ⟨⟨hsp, hbp, hbx⟩, hk1, hk2, hcx, hdx, hsi, h14, hdi, h8, h9, h10, h11, h15⟩, h12, hmi, hm4, hm32, h13, hm⟩, hn⟩ := hs₀
  have hI := xgIT_cases x hC.2.2.2.2.2
  generalize (s₀.regs.get64 .r12).toNat / 256 = m at *
  clear hms
  vcgen
  all_goals try subst_vars
  all_goals try dsimp only at *
  all_goals opaque_stores
  all_goals try simp only [AddrIndex.offset64, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat,
    BitVec.add_zero, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd] at *
  all_goals try simp only [h12, h11, h15, Width.bytes, BitVec.mul_one, BitVec.add_assoc,
    Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reducePow, Nat.reduceMod,
    Nat.reduceSub]
  all_goals try simp only [BitVec.ofNat64_mul_ofNat, BitVec.ofNat64_mul_lit, ← BitVec.ofNat_add,
    ← Nat.add_assoc]
  all_goals try simp (disch := omega) only [BitVec.ofNat64_add_wrap, Nat.reduceSub, Nat.reducePow,
    Nat.reduceAdd]
  case vc1 | vc2 | vc3 | vc4 | vc5 | vc6 | vc7 | vc8 => grind_cells'
  case vc9 =>
    have h256 : (BitVec.ofNat 64 (256 * m)).toNat = 256 * m := by
      simp -implicitDefEqProofs only [BitVec.toNat_ofNat]; omega
    have hd : 256 * m / 256 = m := by omega
    try simp only [table]
    call_simp
    try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ↓reduceIte, h256, hd]
    and_intros
    all_goals first | exact trivial | exact hm | exact h13 | omega | (clear h256 hd; grind_cells')

theorem blk_d3 (k : Nat) (hk : k ≤ 2 ^ 32) (hms : MemsetSpec k) (x : XGenArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_x_gen.d3" := by
  cfg_block
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨⟨hC, ⟨⟨hsp, hbp, hbx⟩, hk1, hk2, hcx, hdx, hsi, h14, hdi, h8, h9, h10, h11, h15⟩, h12, hmi, hm4, hm32, h13, hm⟩, hn⟩ := hs₀
  have hI := xgIT_cases x hC.2.2.2.2.2
  generalize (s₀.regs.get64 .r12).toNat / 256 = m at *
  have hmc : m = 0 ∨ m = 4 ∨ m = 8 ∨ m = 12 ∨ m = 16 ∨ m = 20 ∨ m = 24 ∨ m = 28 := by omega
  have hr13 : BitVec.setWidth 64 (BitVec.setWidth 32 4#64
      + BitVec.setWidth 32 (BitVec.ofNat 64 ((m + 4294967295) % 4294967296))) = BitVec.ofNat 64 (m + 3) := by
    rcases hmc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hr12 : BitVec.setWidth 64 1024#64 + BitVec.ofNat 64 (256 * m) = BitVec.ofNat 64 (256 * (m + 4)) := by
    rcases hmc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hlt : (BitVec.setWidth 32 (BitVec.ofNat 64 (m + 3))).toInt = m + 3 := by
    rcases hmc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have h31 : (BitVec.setWidth 32 31#64).toInt = 31 := by decide
  clear hms
  vcgen
  all_goals try subst_vars
  all_goals try dsimp only at *
  all_goals call_simp
  all_goals try simp only [Int64.toBitVec_ofNat_norm, Nat.reducePow, Nat.reduceMod, Reg64s.get64_set64,
    reduceCtorEq, ite_true, ite_false, h12, h13, BitVec.ofNat_eq_ofNat] at *
  case vc1 =>
    rename_i hf
    simp only [hr13] at hf
    simp only [CondCode.interp_l_cmp_toInt32, hlt, h31, decide_eq_true_eq] at hf
    have hf' : m < 28 := by revert hf; rcases hmc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    clear hf
    have hT : (BitVec.ofNat 64 (256 * (m + 4))).toNat = 256 * (m + 4) := by
      simp -implicitDefEqProofs only [BitVec.toNat_ofNat]; omega
    have hd : 256 * (m + 4) / 256 = m + 4 := by omega
    have he : (m + 4 + 4294967295) % 4294967296 = m + 3 := by omega
    have hT0 : (BitVec.ofNat 64 (256 * m)).toNat = 256 * m := by
      simp -implicitDefEqProofs only [BitVec.toNat_ofNat]; omega
    left
    refine Table.ofLabels_at (l := "sbr_x_gen.Lbe00") ⟨by decide, ?_⟩
    simp only [table]
    call_simp
    simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hr12, hr13, hT, hd, he, hT0]
    and_intros
    all_goals first | exact trivial | exact hm | omega | (left; omega) | (rcases hmc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
  case vc2 =>
    have hT0 : (BitVec.ofNat 64 (256 * m)).toNat = 256 * m := by
      simp -implicitDefEqProofs only [BitVec.toNat_ofNat]; omega
    try simp only [table]
    call_simp
    simp only [hT0]
    and_intros
    all_goals first | exact trivial | exact hm | omega | with_reducible assumption

set_option maxHeartbeats 300000 in
theorem blk_Lbeaa (k : Nat) (hk : k ≤ 2 ^ 32) (hms : MemsetSpec k) (x : XGenArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_x_gen.Lbeaa" := by
  cfg_block
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨⟨hC, ⟨⟨hsp, hbp, hbx⟩, hk1, hk2, hcx, hdx, hsi, h14, hdi, h8, h9, h10, h11, h15⟩, hm⟩, hn⟩ := hs₀
  have hI := xgIT_cases x hC.2.2.2.2.2
  have hl0 : Mem.loadInt s₀.dmem (s₀.regs.get64 .rbx + 88#64) 4
      = some (Int.ofBytes (Int.toBytes 4 x.kx1.toInt)) := by
    have hm' := hm
    simp only [T, SbrW_open] at hm'
    rw [hbx]
    exact Mem.Val.loadInt hm' (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) (Int.toBytes_length _ _)
      (by decide)
  have hl1 : Mem.loadInt s₀.dmem (s₀.regs.get64 .rbx + 96#64) 4
      = some (Int.ofBytes (Int.toBytes 4 x.m1.toInt)) := by
    have hm' := hm
    simp only [T, SbrW_open] at hm'
    rw [hbx]
    exact Mem.Val.loadInt hm' (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right
      (Mem.Split.here _ _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
  have hv0 : BitVec.ofInt 32 (Int.ofBytes (Int.toBytes 4 x.kx1.toInt)) = x.kx1 := by
    rw [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt_toInt]
  have hv1 : BitVec.ofInt 32 (Int.ofBytes (Int.toBytes 4 x.m1.toInt)) = x.m1 := by
    rw [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt_toInt]
  clear hms
  vcgen
  all_goals try subst_vars
  all_goals try dsimp only at *
  all_goals call_simp
  all_goals try simp only [AddrIndex.offset64, Int64.toBitVec_ofNat_norm, Int64.toBitVec_zero,
    BitVec.ofNat_eq_ofNat, BitVec.add_zero] at *
  all_goals try simp only [hl0, hl1, Option.isSome_some, Option.some.injEq] at *
  all_goals try subst_vars
  all_goals try simp only [hv0, hv1] at *
  case vc3 =>
    left
    refine Table.ofLabels_at (l := "sbr_x_gen.Lbed8") ⟨by decide, ?_⟩
    simp only [table]
    call_simp
    and_intros
    all_goals first | exact True.intro | with_reducible assumption | omega | (simp only [FrMW_open, FrBW_open] at hm ⊢; grind_cells')
  case vc4 =>
    rename_i hnz hnc
    simp only [hcx] at hnz
    simp only [CondCode.interp_nc, CondCode.interp_nz, StatusFlags.cf_from_result,
      StatusFlags.zf_from_result, BitVec.unsigned_eq, BitVec.sub_cf_eq_decide_lt, BitVec.sub_beq_zero,
      Bool.not_eq_true', Bool.not_eq_false', bne_iff_ne, ne_eq, decide_eq_true_eq,
      decide_eq_false_iff_not] at hnz hnc
    simp -implicitDefEqProofs only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_add, xg_toNat_one64,
      Nat.reducePow, Nat.reduceMod] at hnz hnc
    left
    refine Table.ofLabels_at (l := "sbr_x_gen.Lbdb0") ⟨by decide, ?_⟩
    simp only [table]
    call_simp
    and_intros
    all_goals first | exact True.intro | with_reducible assumption | omega | ((try simp only [hdi, h8, h11, h15]); xg_bvext) | xg_nat | xg_bstore | grind_cells'
  case vc5 =>
    exfalso
    rename_i hnz hnc
    simp only [hcx] at hnz
    simp only [CondCode.interp_nc, CondCode.interp_nz, StatusFlags.cf_from_result,
      StatusFlags.zf_from_result, BitVec.unsigned_eq, BitVec.sub_cf_eq_decide_lt, BitVec.sub_beq_zero,
      Bool.not_eq_true', Bool.not_eq_false', bne_iff_ne, ne_eq, decide_eq_true_eq,
      decide_eq_false_iff_not] at hnz hnc
    simp -implicitDefEqProofs only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_add, xg_toNat_one64,
      Nat.reducePow, Nat.reduceMod] at hnz hnc
    omega

theorem blk_Lbed3 (k : Nat) (hk : k ≤ 2 ^ 32) (hms : MemsetSpec k) (x : XGenArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_x_gen.Lbed3" := by
  cfg_block
  intro n
  exact Triple.intro fun s hs => hs.1.elim

set_option maxHeartbeats 300000 in
theorem blk_Lbed8 (k : Nat) (hk : k ≤ 2 ^ 32) (hms : MemsetSpec k) (x : XGenArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_x_gen.Lbed8" := by
  cfg_block
  intro n
  vcgen
  all_goals simp only [FrMW_open] at *
  all_goals call_simp
  all_goals grind_cells'

theorem blk_done (k : Nat) (hk : k ≤ 2 ^ 32) (hms : MemsetSpec k) (x : XGenArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_x_gen.done" := by
  cfg_block
  intro n
  vcgen
  all_goals simp only [Rest] at *
  all_goals call_simp
  all_goals grind_cells'

theorem blk_Lbee9 (k : Nat) (hk : k ≤ 2 ^ 32) (hms : MemsetSpec k) (x : XGenArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_x_gen.Lbee9" := by
  cfg_block
  intro n
  exact Triple.intro fun s hs => hs.1.elim

theorem blk_Lbeee (k : Nat) (hk : k ≤ 2 ^ 32) (hms : MemsetSpec k) (x : XGenArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_x_gen.Lbeee" := by
  cfg_block
  intro n
  exact Triple.intro fun s hs => hs.1.elim

theorem blk_Lbef3 (k : Nat) (hk : k ≤ 2 ^ 32) (hms : MemsetSpec k) (x : XGenArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_x_gen.Lbef3" := by
  cfg_block
  intro n
  exact Triple.intro fun s hs => hs.1.elim

omit [CodeEnv] in
/-- The entry reservation `0x60 + k`: the `memset` return slot, `memset`'s `k`,
and the own `0x58` bytes. -/
theorem xg_reserve_frame (k : Nat) {r : BitVec 64} (hw : 0x60 + k ≤ r.toNat) (K : Mem 64 → Prop) :
    Reserve (0x60 + k) r ⋆ K
      = 8 ?@ (r - 0x60#64) ⋆ (Reserve k (r - 0x60#64) ⋆ (0x58 ?@ (r - 0x58#64) ⋆ K)) :=
  Reserve_split_frame 0x60 k (by decide) r (by omega) K

omit [CodeEnv] in
/-- An `m = n + 8`-byte block below `r` is its bottom 8 bytes and the `n` above. -/
theorem xg_split8 (r : BitVec 64) (m n : Nat) (h : m = n + 8) (hm : m < 2 ^ 32)
    (K : Mem 64 → Prop) :
    m ?@ (r - BitVec.ofNat 64 m) ⋆ K
      = 8 ?@ (r - BitVec.ofNat 64 m) ⋆ (n ?@ (r - BitVec.ofNat 64 n) ⋆ K) := by
  subst h
  rw [Nat.add_comm, Mem.Block.split _ 8 n (by omega), Std.ExtHashMap.sep_assoc]
  rw [show r - BitVec.ofNat 64 (8 + n) + BitVec.ofNat 64 8 = r - BitVec.ofNat 64 n by xg_bvext]

omit [CodeEnv] in
/-- The own `0x58` bytes as eleven 8-byte slots. -/
theorem xg_frame_cells (r : BitVec 64) (K : Mem 64 → Prop) :
    0x58 ?@ (r - 0x58#64) ⋆ K
      = 8 ?@ (r - 0x58#64) ⋆ (8 ?@ (r - 0x50#64) ⋆ (8 ?@ (r - 0x48#64) ⋆ (8 ?@ (r - 0x40#64)
        ⋆ (8 ?@ (r - 0x38#64) ⋆ (8 ?@ (r - 0x30#64) ⋆ (8 ?@ (r - 0x28#64) ⋆ (8 ?@ (r - 0x20#64)
        ⋆ (8 ?@ (r - 0x18#64) ⋆ (8 ?@ (r - 0x10#64) ⋆ (8 ?@ (r - 0x8#64) ⋆ K)))))))))) := by
  rw [xg_split8 r 0x58 0x50 rfl (by decide), xg_split8 r 0x50 0x48 rfl (by decide),
    xg_split8 r 0x48 0x40 rfl (by decide), xg_split8 r 0x40 0x38 rfl (by decide),
    xg_split8 r 0x38 0x30 rfl (by decide), xg_split8 r 0x30 0x28 rfl (by decide),
    xg_split8 r 0x28 0x20 rfl (by decide), xg_split8 r 0x20 0x18 rfl (by decide),
    xg_split8 r 0x18 0x10 rfl (by decide), xg_split8 r 0x10 0x8 rfl (by decide)]

omit [CodeEnv] in
/-- The frame at the exit, its contents forgotten. -/
theorem xg_FrMW_blank (t₀ : MachineData) (K : Mem 64 → Prop) :
    Mem.Entails (FrMW t₀ ⋆ K) (FrEL t₀ K) := by
  rw [FrMW_open]
  exact Mem.Entails.sep_left (Mem.Entails.sep_left (Mem.Entails.forget8 _ _
    (Mem.Entails.forget8 _ _ (Mem.Entails.forget8 _ _ (Mem.Entails.forget8 _ _
    (Mem.Entails.forget8 _ _ (Mem.Entails.forget8 _ _ (Mem.Entails.forget8 _ _
    (Mem.Entails.forget8 _ _ (Mem.Entails.refl _))))))))))

theorem spec (hpl : Program.PlacedIn body) (k : Nat) (hk : k ≤ 2 ^ 32) (hms : MemsetSpec k) :
    XGenSpec k := by
  refine Kraken.Executable.ProcSpec.of_cfg_post_pre (p := body) (table k)
    (Post' k) var (hblocks := ?_) (hpre := ?_) (hpost := ?_)
  · intro x ra t₀ _ l blk hblk
    have hmem := Program.isSome_blockAt body l
    cfg_view hblk as hview
    rw [hblk, hview] at hmem
    replace hmem := hmem.symm
    clear hview
    simp only [Option.isSome_some, List.map_cons, List.map_nil, List.contains_cons,
      List.contains_nil, Bool.or_false, Bool.or_eq_true, beq_iff_eq] at hmem
    obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl := hmem
    · exact blk_entry k hk hms x ra t₀ blk hblk
    · exact blk_e1 k hk hms x ra t₀ blk hblk
    · exact blk_e2 k hk hms x ra t₀ blk hblk
    · exact blk_m1 k hk hms x ra t₀ blk hblk
    · exact blk_a0 k hk hms x ra t₀ blk hblk
    · exact blk_Lb910 k hk hms x ra t₀ blk hblk
    · exact blk_Lb920 k hk hms x ra t₀ blk hblk
    · exact blk_a2 k hk hms x ra t₀ blk hblk
    · exact blk_a3 k hk hms x ra t₀ blk hblk
    · exact blk_Lb9a6 k hk hms x ra t₀ blk hblk
    · exact blk_t1 k hk hms x ra t₀ blk hblk
    · exact blk_Lb9cc k hk hms x ra t₀ blk hblk
    · exact blk_b0 k hk hms x ra t₀ blk hblk
    · exact blk_Lba50 k hk hms x ra t₀ blk hblk
    · exact blk_Lba70 k hk hms x ra t₀ blk hblk
    · exact blk_Lba80 k hk hms x ra t₀ blk hblk
    · exact blk_b2 k hk hms x ra t₀ blk hblk
    · exact blk_b3 k hk hms x ra t₀ blk hblk
    · exact blk_Lbb30 k hk hms x ra t₀ blk hblk
    · exact blk_Lbb50 k hk hms x ra t₀ blk hblk
    · exact blk_Lbb7d k hk hms x ra t₀ blk hblk
    · exact blk_Lbba4 k hk hms x ra t₀ blk hblk
    · exact blk_Lbba9 k hk hms x ra t₀ blk hblk
    · exact blk_c0 k hk hms x ra t₀ blk hblk
    · exact blk_Lbc00 k hk hms x ra t₀ blk hblk
    · exact blk_Lbc10 k hk hms x ra t₀ blk hblk
    · exact blk_Lbc39 k hk hms x ra t₀ blk hblk
    · exact blk_Lbc50 k hk hms x ra t₀ blk hblk
    · exact blk_c2 k hk hms x ra t₀ blk hblk
    · exact blk_c3 k hk hms x ra t₀ blk hblk
    · exact blk_Lbce0 k hk hms x ra t₀ blk hblk
    · exact blk_t2 k hk hms x ra t₀ blk hblk
    · exact blk_Lbd11 k hk hms x ra t₀ blk hblk
    · exact blk_Lbd16 k hk hms x ra t₀ blk hblk
    · exact blk_d0 k hk hms x ra t₀ blk hblk
    · exact blk_d1 k hk hms x ra t₀ blk hblk
    · exact blk_Lbdb0 k hk hms x ra t₀ blk hblk
    · exact blk_Lbdc0 k hk hms x ra t₀ blk hblk
    · exact blk_Lbdec k hk hms x ra t₀ blk hblk
    · exact blk_Lbe00 k hk hms x ra t₀ blk hblk
    · exact blk_d2 k hk hms x ra t₀ blk hblk
    · exact blk_d3 k hk hms x ra t₀ blk hblk
    · exact blk_Lbeaa k hk hms x ra t₀ blk hblk
    · exact blk_Lbed3 k hk hms x ra t₀ blk hblk
    · exact blk_Lbed8 k hk hms x ra t₀ blk hblk
    · exact blk_done k hk hms x ra t₀ blk hblk
    · exact blk_Lbee9 k hk hms x ra t₀ blk hblk
    · exact blk_Lbeee k hk hms x ra t₀ blk hblk
    · exact blk_Lbef3 k hk hms x ra t₀ blk hblk
  · -- hpre
    rintro x ra t ⟨hm, hC⟩
    refine ⟨rfl, hC, ?_⟩
    have hw := CallPre.le hm
    simp only [CallPre, xgNeed, XGenF] at hm
    rw [xg_reserve_frame k hw, xg_frame_cells] at hm
    simp only [T, FrEL, Rest, SbrW]
    exact Mem.ac hm
  · -- hpost
    rintro x ra t₀ s ⟨h0, -⟩ ⟨h1, h2, h3, hm⟩
    refine ⟨h1, h2, h3, ?_⟩
    have hm' := Mem.Entails.sep_left (Mem.Entails.sep_left (Mem.Entails.sep_left
      (Mem.Entails.sep_left (Mem.Entails.sep_left (xg_FrMW_blank t₀ _))))) _ hm
    simp only [FrEL] at hm'
    rw [← xg_frame_cells] at hm'
    simp only [XGenF, xgNeed, SbrW] at hm' ⊢
    rw [xg_reserve_frame k (CallPre.le h0)]
    exact Mem.ac hm'

end Kraken.Examples.Sbr.XGen
