import Kraken.X64.Examples.Sbr.Parse.TlimLib
import Kraken.X64.Examples.Sbr.Parse.LibQsort

/-!
# `sbr_make_f_tablelim`: the block table

The memory at every label (`T`): the routine's own cells (`f_tablelim`, `n_lim`, the
`AV_QSORT` stack, `patch_borders`) as list cells, the read-only fields of `*sbr` and
`bands_warped` as one group `RO`, the frame (pushed registers, spill slots), the caller's
memory. The assertions at the labels and the variant `var` (a `Nat` read off the machine
state: the region, then inside `AV_QSORT` the pending intervals' `phi` read from the stack in
memory, then a per-phase inner measure; in the compaction loop `n_lim - out`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse.Qsort

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.Tlim

variable [CodeEnv]

/-- The values of the routine's own cells. -/
structure TSt where
  fl : List UInt8
  nl : Nat
  stk : List UInt8
  pb : List UInt8

abbrev rS (t₀ : MachineData) : BitVec 64 := t₀.regs.get64 .rsp
abbrev sA (t₀ : MachineData) : BitVec 64 := arg0 t₀
/-- `f_tablelim`. -/
abbrev pA (t₀ : MachineData) : BitVec 64 := arg0 t₀ + 0x4c2f2#64

/-- What is only read: `bs_limiter_bands`, `kx[1]`, `n[0]`, `f_tablelow`, `num_patches`,
`patch_num_subbands`, `bands_warped`. -/
def RO (x : TArgs) (t₀ : MachineData) : Mem 64 → Prop :=
  let s := sA t₀
  cell4 (s + 0x2c#64) x.lb ⋆ (c4 (s + 0x58#64) x.a.kx1 ⋆ (c4 (s + 0x4c1e0#64) x.a.n0
    ⋆ (x.a.ftLow =@ (s + 0x4c252#64) ⋆ (c4 (s + 0x4c330#64) x.a.npatch
    ⋆ (x.a.pnum =@ (s + 0x4c334#64) ⋆ Blocks [(BW, 12)])))))

/-- The locals not tracked: `[rbp-0x40, rbp-0x34)`, the spill of `xmm0` at `rbp-0x34`,
`[rbp-0x30, rbp-0x2e)`. -/
def Junk (r : BitVec 64) : Mem 64 → Prop :=
  12 ?@ (r - 0x48#64) ⋆ (4 ?@ (r - 0x3c#64) ⋆ 2 ?@ (r - 0x38#64))

def Rest (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) : Mem 64 → Prop :=
  RetCell ra (t₀.regs.get64 .rsp) ⋆ R

abbrev Saved (t₀ : MachineData) (K : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  c8 (r - 0x28#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ K))))

abbrev BlankS (r : BitVec 64) (K : Mem 64 → Prop) : Mem 64 → Prop :=
  8 ?@ (r - 0x28#64) ⋆ (8 ?@ (r - 0x20#64) ⋆ (8 ?@ (r - 0x18#64) ⋆ (8 ?@ (r - 0x10#64)
    ⋆ (8 ?@ (r - 0x8#64) ⋆ K))))

/-- The memory at every label. -/
abbrev T (k : Nat) (x : TArgs) (ra : Int64) (t₀ : MachineData)
    (FR : (Mem 64 → Prop) → Mem 64 → Prop) (st : TSt) : Mem 64 → Prop :=
  let r := rS t₀
  8 ?@ (r - 0x450#64) ⋆ (Reserve k (r - 0x450#64) ⋆ (st.fl =@ pA t₀
    ⋆ (c4 (sA t₀ + 0x4c1ec#64) st.nl ⋆ (st.stk =@ (r - 0x448#64) ⋆ (st.pb =@ (r - 0x36#64)
    ⋆ (Junk r ⋆ (RO x t₀ ⋆ FR (Rest x.R ra t₀))))))))

/-! ## Logical values -/

/-- The number of elements sorted. -/
abbrev NN (x : TArgs) : Nat := x.a.n0 + x.a.npatch

/-- The array the sort starts from (`ParseModel.limIn`). -/
abbrev A0 (x : TArgs) : Nat → Nat := limIn x.a

/-- The array a list of bytes holds. -/
abbrev AV (l : List UInt8) : Nat → Nat := fun q => u16 l q

/-- `patch_borders[k] = kx[1] + Σ_{i<k} patch_num_subbands[i]` for `k < i`. -/
def PBto (x : TArgs) (pb : List UInt8) (i : Nat) : Prop :=
  ∀ k, k < i → u16 pb k = x.a.kx1 + psum x.a.pnum k

/-- The lengths of the routine's cells. -/
def Lens (st : TSt) : Prop := st.fl.length = 60 ∧ st.stk.length = 1024 ∧ st.pb.length = 14

/-- The stack in memory holds the pending intervals `S` (pointers into the array at `p`). -/
def StkRel (p : BitVec 64) (stk : List UInt8) (S : List Iv) : Prop :=
  ∀ j (h : j < S.length), w8 stk (2 * j) = p + BitVec.ofNat 64 (2 * S[j].1)
    ∧ w8 stk (2 * j + 1) = p + BitVec.ofNat 64 (2 * S[j].2) - 2#64

/-- The registers kept after the prologue. -/
abbrev Regs0 (t₀ s : MachineData) : Prop :=
  s.regs.get64 .rsp = rS t₀ - 0x448#64 ∧ s.regs.get64 .rbp = rS t₀ - 8#64
    ∧ s.regs.get64 .r13 = t₀.regs.get64 .r13

abbrev Regs (t₀ s : MachineData) : Prop := Regs0 t₀ s ∧ s.regs.get64 .rbx = sA t₀

/-- The state before the copies: `f_tablelim`, `n_lim` as given. -/
abbrev st0 (x : TArgs) (stk pb : List UInt8) : TSt := ⟨x.a.ftLim, x.a.nlim, stk, pb⟩

/-- Before the copies, with `patch_borders` up to `i`. -/
abbrev Pre0 (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) (i : Nat) : Prop :=
  ∃ stk pb, Lens (st0 x stk pb) ∧ PBto x pb i ∧ (s.dmem =⋆ T k x ra t₀ (Saved t₀) (st0 x stk pb))

/-- After the copies and inside the sort: the array `fl`, the stack, `patch_borders` complete. -/
abbrev Mid (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData)
    (P : List UInt8 → List UInt8 → Prop) : Prop :=
  ∃ fl stk pb, Lens ⟨fl, x.a.nlim, stk, pb⟩ ∧ PBto x pb (x.a.npatch + 1) ∧ P fl stk
    ∧ (s.dmem =⋆ T k x ra t₀ (Saved t₀) ⟨fl, x.a.nlim, stk, pb⟩)

/-- The registers inside the sort. -/
abbrev QR (x : TArgs) (t₀ s : MachineData) : Prop :=
  TlimC x.lb x.a t₀ ∧ Regs t₀ s ∧ s.regs.get64 .r14 = pA t₀
    ∧ s.regs.get64 .rax = pA t₀ + 2#64 ∧ 1 ≤ NN x ∧ x.lb ≠ 0#32

/-- Between partitions: the stack `S` (`sp = |S|` in `rcx`). -/
abbrev QPop (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) : Prop :=
  QR x t₀ s ∧ ∃ S : List Iv, s.regs.get64 .rcx = BitVec.ofNat 64 S.length ∧ Depth (NN x) S
    ∧ Mid k x ra t₀ s (fun fl stk => StkRel (pA t₀) stk S ∧ QI (NN x) (AV fl) (A0 x) S)

/-- The facts on the current interval `[lo, hi1)` (`start` in `rsi`, `end` in `rdx`). -/
abbrev CurF (x : TArgs) (t₀ s : MachineData) (S : List Iv) (lo hi1 : Nat) (A : Nat → Nat) :
    Prop :=
  s.regs.get64 .rcx = BitVec.ofNat 64 S.length ∧ Depth (NN x) S
    ∧ (hi1 - lo) * 2 ^ S.length ≤ NN x
    ∧ s.regs.get64 .rsi = pA t₀ + BitVec.ofNat 64 (2 * lo)
    ∧ s.regs.get64 .rdx = pA t₀ + BitVec.ofNat 64 (2 * hi1) - 2#64
    ∧ QI (NN x) A (A0 x) (S ++ [(lo, hi1)])

/-- On the current interval, with the array in memory `fl` and the facts `P`. -/
abbrev QCur (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData)
    (P : List Iv → Nat → Nat → List UInt8 → Prop) : Prop :=
  QR x t₀ s ∧ ∃ S lo hi1, Mid k x ra t₀ s (fun fl stk => StkRel (pA t₀) stk S
    ∧ CurF x t₀ s S lo hi1 (AV fl) ∧ P S lo hi1 fl)

abbrev v64 (n : Nat) : BitVec 64 := BitVec.ofNat 64 n

/-- The median position. -/
abbrev mid (lo e : Nat) : Nat := lo + (e - lo) / 2

/-- The partition invariant on `[lo, e]` with `left = l`, `right = rt` and the pivot `pv` at
`e - 1`. -/
def PInv (A : Nat → Nat) (lo e l rt pv : Nat) : Prop :=
  lo + 1 ≤ l ∧ l ≤ rt + 2 ∧ rt + 2 ≤ e ∧ l + 1 ≤ e ∧ A (e - 1) = pv
    ∧ (∀ q, lo ≤ q → q < l → A q ≤ pv) ∧ (∀ q, rt < q → q ≤ e → pv ≤ A q)

/-- After the pivot is placed at `l`. -/
def PDone (A : Nat → Nat) (lo e l rt : Nat) : Prop :=
  lo + 1 ≤ l ∧ l ≤ rt + 2 ∧ rt < l ∧ l + 1 ≤ e
    ∧ (∀ q, lo ≤ q → q ≤ l → A q ≤ A l) ∧ (∀ q, rt < q → q ≤ e → A l ≤ A q)

/-- The partition registers: `left`, `right`, the slot `end - 1` in `r8`. -/
abbrev PR (t₀ s : MachineData) (e l rt : Nat) : Prop :=
  s.regs.get64 .r10 = pA t₀ + v64 (2 * l) ∧ s.regs.get64 .r9 = pA t₀ + v64 (2 * rt)
    ∧ s.regs.get64 .r8 = pA t₀ + v64 (2 * (e - 1))

/-- In the compaction loop: the sorted array `sa`, `in = i`, `out = o`, `n_lim = L` (in
memory), the `Compact` path from the start. -/
abbrev CmpF (x : TArgs) (t₀ s : MachineData) (sa : Nat → Nat) (fl : List UInt8) (i o L : Nat) :
    Prop :=
  Sorted (NN x) (A0 x) sa ∧ L + 1 ≤ NN x ∧ o ≤ L ∧ i = o + 1 + (NN x - 1 - L)
    ∧ s.regs.get64 .rcx = pA t₀ + v64 (2 * o) ∧ s.regs.get64 .rax = pA t₀ + v64 (2 * i)
    ∧ (∀ r R, Compact (AV fl) i o L r R → Compact sa 1 0 (NN x - 1) r R)

abbrev QC (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData)
    (P : Nat → Nat → Nat → List UInt8 → Prop) : Prop :=
  TlimC x.lb x.a t₀ ∧ Regs t₀ s ∧ s.regs.get64 .r14 = pA t₀ ∧ 1 ≤ NN x ∧ x.lb ≠ 0#32
    ∧ ∃ sa fl stk pb i o L, Lens ⟨fl, L, stk, pb⟩ ∧ PBto x pb (x.a.npatch + 1)
    ∧ CmpF x t₀ s sa fl i o L ∧ P i o L fl
    ∧ (s.dmem =⋆ T k x ra t₀ (Saved t₀) ⟨fl, L, stk, pb⟩)

/-- Before the `drop` step at `L4370`: `CmpF` with the path condition for the step taken next
(`in + 1`, `n_lim - 1`). -/
abbrev CmpD (x : TArgs) (t₀ s : MachineData) (sa : Nat → Nat) (fl : List UInt8) (i o L : Nat) :
    Prop :=
  Sorted (NN x) (A0 x) sa ∧ L + 1 ≤ NN x ∧ o ≤ L ∧ i = o + 1 + (NN x - 1 - L)
    ∧ s.regs.get64 .rcx = pA t₀ + v64 (2 * o) ∧ s.regs.get64 .rax = pA t₀ + v64 (2 * i)
    ∧ (∀ r R, Compact (AV fl) (i + 1) o (L - 1) r R → Compact sa 1 0 (NN x - 1) r R)

/-- At the exit: the values of a `Tablelim` successor. -/
abbrev Fin (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) : Prop :=
  TlimC x.lb x.a t₀ ∧ Regs0 t₀ s ∧ ∃ y stk pb, Tablelim x.lb.toNat x.a y
    ∧ y = { x.a with ftLim := y.ftLim, nlim := y.nlim } ∧ Lens ⟨y.ftLim, y.nlim, stk, pb⟩
    ∧ (s.dmem =⋆ T k x ra t₀ (Saved t₀) ⟨y.ftLim, y.nlim, stk, pb⟩)

abbrev L (s : String) : String := "sbr_make_f_tablelim." ++ s

def table (k : Nat) (x : TArgs) (ra : Int64) (t₀ : MachineData) :
    Label → MachineData → Prop
  | "sbr_make_f_tablelim", s => s = t₀ ∧ TlimC x.lb x.a t₀
      ∧ ∃ stk pb, Lens (st0 x stk pb) ∧ (t₀.dmem =⋆ T k x ra t₀ (BlankS (rS t₀)) (st0 x stk pb))
  | "sbr_make_f_tablelim.L3f22", s => TlimC x.lb x.a t₀ ∧ Regs0 t₀ s
      ∧ s.regs.get64 .rdi = sA t₀ ∧ Pre0 k x ra t₀ s 0
  | "sbr_make_f_tablelim.L3f31", s => TlimC x.lb x.a t₀ ∧ Regs t₀ s
      ∧ s.regs.get64 .rax = x.lb.setWidth 64 ∧ x.lb ≠ 0#32 ∧ Pre0 k x ra t₀ s 0
  | "sbr_make_f_tablelim.L3f3a", s => TlimC x.lb x.a t₀ ∧ Regs t₀ s
      ∧ s.regs.get64 .rax = x.lb.setWidth 64 ∧ x.lb ≠ 0#32 ∧ Pre0 k x ra t₀ s 0
  | "sbr_make_f_tablelim.L3f59", s => TlimC x.lb x.a t₀ ∧ Regs t₀ s ∧ x.lb ≠ 0#32
      ∧ s.regs.get64 .rax = v64 x.a.kx1 ∧ s.regs.get64 .rcx = v64 x.a.npatch ∧ x.a.npatch ≠ 0
      ∧ Pre0 k x ra t₀ s 1
  | "sbr_make_f_tablelim.L3f65", s => Chain k x ra t₀ s 0
  | "sbr_make_f_tablelim.L3f77", s => Chain k x ra t₀ s 1
  | "sbr_make_f_tablelim.L3f89", s => Chain k x ra t₀ s 2
  | "sbr_make_f_tablelim.L3f9b", s => Chain k x ra t₀ s 3
  | "sbr_make_f_tablelim.L3fad", s => Chain k x ra t₀ s 4
  | "sbr_make_f_tablelim.L3fbf", s => Chain k x ra t₀ s 5
  | "sbr_make_f_tablelim.L3fcc", s => TlimC x.lb x.a t₀ ∧ Regs t₀ s ∧ x.lb ≠ 0#32
      ∧ Pre0 k x ra t₀ s (x.a.npatch + 1)
  | "sbr_make_f_tablelim.L3ff5", s => Cp k x ra t₀ s
  | "sbr_make_f_tablelim.L4000", s => Cp k x ra t₀ s ∧ s.regs.get64 .rdx = v64 x.a.npatch
      ∧ 2 ≤ x.a.npatch
  | "sbr_make_f_tablelim.L400a", s => Cp k x ra t₀ s ∧ s.regs.get64 .rdx = v64 x.a.npatch
      ∧ 2 ≤ x.a.npatch
  | "sbr_make_f_tablelim.L4020", s => Cp2 k x ra t₀ s
  | "sbr_make_f_tablelim.L4026", s => Cp2 k x ra t₀ s ∧ s.regs.get64 .rdx = v64 x.a.npatch
  | "sbr_make_f_tablelim.L403f", s => TlimC x.lb x.a t₀ ∧ Regs t₀ s ∧ x.lb ≠ 0#32
      ∧ s.regs.get64 .r14 = pA t₀ ∧ s.regs.get64 .r15 = v64 (NN x)
      ∧ Mid k x ra t₀ s (fun fl stk => (∀ q, AV fl q = A0 x q) ∧ w8 stk 0 = pA t₀)
  | "sbr_make_f_tablelim.L4060", s => QPop k x ra t₀ s
  | "sbr_make_f_tablelim.L4068", s => QPop k x ra t₀ s ∧ s.regs.get64 .rcx ≠ 0#64
  | "sbr_make_f_tablelim.L4090", s => QCur k x ra t₀ s (fun _ _ _ _ => True)
  | "sbr_make_f_tablelim.L4280", s => QCur k x ra t₀ s (fun _ lo hi1 _ => hi1 = lo + 2)
  | "sbr_make_f_tablelim.L40c3", s => QCur k x ra t₀ s (fun _ lo hi1 fl =>
      Med x t₀ s lo (hi1 - 1) fl ∧ AV fl (hi1 - 1) < AV fl lo)
  | "sbr_make_f_tablelim.L40c9", s => QCur k x ra t₀ s (fun _ lo hi1 fl =>
      Med x t₀ s lo (hi1 - 1) fl ∧ AV fl (hi1 - 1) < AV fl lo
      ∧ AV fl (hi1 - 1) ≤ AV fl (mid lo (hi1 - 1)))
  | "sbr_make_f_tablelim.L40e0", s => QCur k x ra t₀ s (fun _ lo hi1 fl =>
      Med x t₀ s lo (hi1 - 1) fl ∧ AV fl lo ≤ AV fl (hi1 - 1))
  | "sbr_make_f_tablelim.L40ec", s => QCur k x ra t₀ s (fun _ lo hi1 fl =>
      Med0 x t₀ s lo (hi1 - 1) ∧ s.regs.get64 .r10 = v64 (AV fl lo)
      ∧ s.regs.get64 .r9 = v64 (AV fl (mid lo (hi1 - 1)))
      ∧ (AV fl (mid lo (hi1 - 1)) < AV fl lo ∧ AV fl lo ≤ AV fl (hi1 - 1)
        ∨ AV fl (mid lo (hi1 - 1)) < AV fl (hi1 - 1) ∧ AV fl (hi1 - 1) < AV fl lo))
  | "sbr_make_f_tablelim.L40f0", s => QR x t₀ s ∧ ∃ S lo hi1 A pos,
      Mid k x ra t₀ s (fun fl stk => StkRel (pA t₀) stk S ∧ CurF x t₀ s S lo hi1 A
        ∧ lo + 2 ≤ hi1 - 1 ∧ (pos = mid lo (hi1 - 1) ∨ pos = hi1 - 1)
        ∧ (∀ q, AV fl q = Parse.Qsort.upd A pos (A lo) q) ∧ s.regs.get64 .r9 = v64 (A pos)
        ∧ s.regs.get64 .rdi = pA t₀ + v64 (2 * mid lo (hi1 - 1))
        ∧ s.regs.get64 .r8 = pA t₀ + v64 (2 * (hi1 - 2))
        ∧ (pos = mid lo (hi1 - 1) → A pos < A lo ∧ A lo ≤ A (hi1 - 1)
            ∨ A pos < A (hi1 - 1) ∧ A (hi1 - 1) < A lo)
        ∧ (pos = hi1 - 1 → A pos < A lo ∧ A pos ≤ A (mid lo (hi1 - 1))))
  | "sbr_make_f_tablelim.L40f7", s => QCur k x ra t₀ s (fun _ lo hi1 fl =>
      Med0 x t₀ s lo (hi1 - 1) ∧ AV fl lo ≤ AV fl (mid lo (hi1 - 1))
      ∧ AV fl lo ≤ AV fl (hi1 - 1))
  | "sbr_make_f_tablelim.L4105", s => QCur k x ra t₀ s (fun _ lo hi1 fl =>
      Med0 x t₀ s lo (hi1 - 1) ∧ AV fl lo ≤ AV fl (hi1 - 1)
      ∧ AV fl (hi1 - 1) < AV fl (mid lo (hi1 - 1))
      ∧ s.regs.get64 .r9 = v64 (AV fl (mid lo (hi1 - 1)))
      ∧ s.regs.get64 .r15 = v64 (AV fl (hi1 - 1)))
  | "sbr_make_f_tablelim.L4110", s => QCur k x ra t₀ s (fun _ lo hi1 fl => Med3 x t₀ s lo hi1 fl)
  | "sbr_make_f_tablelim.L4120", s => QCur k x ra t₀ s (fun _ lo hi1 fl =>
      Med0 x t₀ s lo (hi1 - 1) ∧ AV fl lo ≤ AV fl (mid lo (hi1 - 1))
      ∧ AV fl (mid lo (hi1 - 1)) ≤ AV fl (hi1 - 1)
      ∧ s.regs.get64 .r9 = v64 (AV fl (mid lo (hi1 - 1))))
  | "sbr_make_f_tablelim.L4130", s => QCur k x ra t₀ s (fun _ lo hi1 fl =>
      Med3 x t₀ s lo hi1 fl ∧ lo + 3 ≤ hi1 - 1
      ∧ s.regs.get64 .r9 = pA t₀ + v64 (2 * (hi1 - 3)))
  | "sbr_make_f_tablelim.L4150", s => QPart k x ra t₀ s (fun A e l rt pv =>
      l ≤ rt ∧ pv ≤ A l ∧ A rt ≤ pv ∧ s.regs.get64 .r12 = v64 (A rt))
  | "sbr_make_f_tablelim.L4164", s => QPart k x ra t₀ s (fun _ _ _ _ _ => True)
  | "sbr_make_f_tablelim.L4169", s => QPart k x ra t₀ s (fun _ _ l rt _ => l ≤ rt)
  | "sbr_make_f_tablelim.L4170", s => QPart k x ra t₀ s (fun _ _ l rt pv =>
      l ≤ rt ∧ s.regs.get64 .r15 = v64 pv)
  | "sbr_make_f_tablelim.L4190", s => QPart k x ra t₀ s (fun A _ l rt pv =>
      l ≤ rt ∧ pv ≤ A l ∧ pv < A rt ∧ s.regs.get64 .r15 = v64 pv)
  | "sbr_make_f_tablelim.L4194", s => QPart k x ra t₀ s (fun A _ l rt pv =>
      l ≤ rt + 1 ∧ (l ≤ rt → pv ≤ A l) ∧ s.regs.get64 .r15 = v64 pv)
  | "sbr_make_f_tablelim.L4199", s => QPart k x ra t₀ s (fun A _ l rt pv =>
      l ≤ rt ∧ pv ≤ A l ∧ s.regs.get64 .r15 = v64 pv)
  | "sbr_make_f_tablelim.L41b0", s => QPart k x ra t₀ s (fun _ _ l rt _ => rt < l)
  | "sbr_make_f_tablelim.L41b4", s => QPart k x ra t₀ s (fun _ _ l rt pv =>
      rt < l ∧ s.regs.get64 .r15 = v64 pv)
  | "sbr_make_f_tablelim.L41ca", s => QDone k x ra t₀ s (fun _ _ _ _ => True)
  | "sbr_make_f_tablelim.L41d3", s => QDone k x ra t₀ s (fun _ _ _ _ => True)
  | "sbr_make_f_tablelim.L41e0", s => QDone k x ra t₀ s (fun A lo e _ =>
      ∃ m, lo ≤ m ∧ m ≤ e ∧ s.regs.get64 .r8 = pA t₀ + v64 (2 * m)
        ∧ ∀ q, lo ≤ q → q < m → A q ≤ A (q + 1))
  | "sbr_make_f_tablelim.L41f7", s => QDone k x ra t₀ s (fun A lo e _ =>
      ∃ m, lo ≤ m ∧ m ≤ e ∧ s.regs.get64 .rdi = pA t₀ + v64 (2 * m)
        ∧ ∀ q, lo ≤ q → q < m → A q ≤ A (q + 1))
  | "sbr_make_f_tablelim.L4200", s => QDone k x ra t₀ s (fun _ _ _ _ => True)
  | "sbr_make_f_tablelim.L4211", s => QDone k x ra t₀ s (fun _ lo e l => e - l < l - lo)
  | "sbr_make_f_tablelim.L421b", s => QDone k x ra t₀ s (fun _ lo e l => e - l < l - lo)
  | "sbr_make_f_tablelim.L4250", s => QDone k x ra t₀ s (fun _ lo e l => l - lo ≤ e - l)
  | "sbr_make_f_tablelim.L425a", s => QDone k x ra t₀ s (fun _ lo e l => l - lo ≤ e - l)
  | "sbr_make_f_tablelim.L429d", s => QR x t₀ s
      ∧ Mid k x ra t₀ s (fun fl _ => Sorted (NN x) (A0 x) (AV fl))
  | "sbr_make_f_tablelim.L42b6", s => TlimC x.lb x.a t₀ ∧ Regs t₀ s ∧ s.regs.get64 .r14 = pA t₀
      ∧ s.regs.get64 .rax = pA t₀ + 2#64 ∧ 1 ≤ NN x ∧ x.lb ≠ 0#32 ∧ s.regs.get64 .rdx = v64 (NN x - 1)
      ∧ CondCode.a.interp s.status = false
      ∧ ∃ fl stk pb, Lens ⟨fl, NN x - 1, stk, pb⟩ ∧ PBto x pb (x.a.npatch + 1)
        ∧ Sorted (NN x) (A0 x) (AV fl)
        ∧ (s.dmem =⋆ T k x ra t₀ (Saved t₀) ⟨fl, NN x - 1, stk, pb⟩)
  | "sbr_make_f_tablelim.L42bc", s => TlimC x.lb x.a t₀ ∧ Regs t₀ s ∧ s.regs.get64 .r14 = pA t₀
      ∧ s.regs.get64 .rax = pA t₀ + 2#64 ∧ 1 ≤ NN x ∧ x.lb ≠ 0#32 ∧ s.regs.get64 .rdx = v64 (NN x - 1)
      ∧ ∃ fl stk pb, Lens ⟨fl, NN x - 1, stk, pb⟩ ∧ PBto x pb (x.a.npatch + 1)
        ∧ Sorted (NN x) (A0 x) (AV fl)
        ∧ (s.dmem =⋆ T k x ra t₀ (Saved t₀) ⟨fl, NN x - 1, stk, pb⟩)
  | "sbr_make_f_tablelim.L42eb", s => QC k x ra t₀ s (fun _ _ L _ => s.regs.get64 .rdx = v64 L)
  | "sbr_make_f_tablelim.L42fa", s => QC k x ra t₀ s (fun _ o L _ => o < L ∧ s.regs.get64 .rdx = v64 L)
  | "sbr_make_f_tablelim.L4312", s => QC k x ra t₀ s (fun i o L fl => o < L ∧ s.regs.get64 .rdx = v64 L
      ∧ s.regs.get64 .rsi = v64 (AV fl i) ∧ s.regs.get64 .rdi = v64 (AV fl o))
  | "sbr_make_f_tablelim.L4317", s => QC k x ra t₀ s (fun i o L fl => o < L ∧ s.regs.get64 .rdx = v64 L
      ∧ s.regs.get64 .rsi = v64 (AV fl i))
  | "sbr_make_f_tablelim.L4323", s => QC k x ra t₀ s (fun i o L fl => o < L ∧ s.regs.get64 .rdx = v64 L
      ∧ s.regs.get64 .rsi = v64 (AV fl i) ∧ s.regs.get64 .r8 = v64 x.a.npatch)
  | "sbr_make_f_tablelim.L4330", s => QC k x ra t₀ s (fun i o L fl => o < L ∧ s.regs.get64 .rdx = v64 L
      ∧ s.regs.get64 .rsi = v64 (AV fl i) ∧ s.regs.get64 .r8 = v64 (x.a.npatch + 1)
      ∧ ∃ j, j ≤ x.a.npatch ∧ s.regs.get64 .r9 = v64 j)
  | "sbr_make_f_tablelim.L4338", s => QC k x ra t₀ s (fun i o L fl => o < L ∧ s.regs.get64 .rdx = v64 L
      ∧ s.regs.get64 .rsi = v64 (AV fl i) ∧ s.regs.get64 .r8 = v64 (x.a.npatch + 1)
      ∧ ∃ j, j ≤ x.a.npatch ∧ s.regs.get64 .r9 = v64 j)
  | "sbr_make_f_tablelim.L4340", s => QC k x ra t₀ s (fun _ o L _ => o < L ∧ s.regs.get64 .rdx = v64 L)
  | "sbr_make_f_tablelim.L4342", s => QC k x ra t₀ s (fun i o L fl => o < L
      ∧ s.regs.get64 .rsi = v64 (AV fl i) ∧ s.regs.get64 .r8 = v64 (x.a.npatch + 1))
  | "sbr_make_f_tablelim.L4350", s => QC k x ra t₀ s (fun i o L fl => o < L
      ∧ s.regs.get64 .rsi = v64 (AV fl i) ∧ s.regs.get64 .r8 = v64 (x.a.npatch + 1)
      ∧ ∃ j, j ≤ x.a.npatch ∧ s.regs.get64 .rdx = v64 j)
  | "sbr_make_f_tablelim.L435b", s => QC k x ra t₀ s (fun i o L fl => o < L
      ∧ s.regs.get64 .rsi = v64 (AV fl i) ∧ s.regs.get64 .r8 = v64 (x.a.npatch + 1)
      ∧ ∃ j, j ≤ x.a.npatch ∧ s.regs.get64 .rdx = v64 j)
  | "sbr_make_f_tablelim.L4363", s => QC k x ra t₀ s (fun i o L fl => o < L
      ∧ s.regs.get64 .rsi = v64 (AV fl i))
  | "sbr_make_f_tablelim.L4370", s => TlimC x.lb x.a t₀ ∧ Regs t₀ s ∧ s.regs.get64 .r14 = pA t₀
      ∧ 1 ≤ NN x ∧ x.lb ≠ 0#32
      ∧ ∃ sa fl stk pb i o L, Lens ⟨fl, L, stk, pb⟩ ∧ PBto x pb (x.a.npatch + 1)
        ∧ CmpD x t₀ s sa fl i o L ∧ o < L ∧ s.regs.get64 .rdx = v64 L
        ∧ (s.dmem =⋆ T k x ra t₀ (Saved t₀) ⟨fl, L, stk, pb⟩)
  | "sbr_make_f_tablelim.L42d0", s => QC k x ra t₀ s (fun i o L fl => o < L
      ∧ s.regs.get64 .rsi = v64 (AV fl i))
  | "sbr_make_f_tablelim.L438a", s => TlimC x.lb x.a t₀ ∧ Regs t₀ s ∧ x.lb = 0#32
      ∧ Pre0 k x ra t₀ s 0
  | "sbr_make_f_tablelim.L4398", s => TlimC x.lb x.a t₀ ∧ Regs t₀ s ∧ x.lb = 0#32
      ∧ ∃ stk pb, Lens (st0 x stk pb)
        ∧ (s.dmem =⋆ T k x ra t₀ (Saved t₀) ⟨setW2 x.a.ftLim 0 (u16 x.a.ftLow 0), x.a.nlim, stk, pb⟩)
  | "sbr_make_f_tablelim.L43a4", s => TlimC x.lb x.a t₀ ∧ Regs t₀ s ∧ x.lb = 0#32
      ∧ s.regs.get64 .rax = v64 x.a.n0
      ∧ ∃ stk pb, Lens (st0 x stk pb)
        ∧ (s.dmem =⋆ T k x ra t₀ (Saved t₀) ⟨setW2 x.a.ftLim 0 (u16 x.a.ftLow 0), x.a.nlim, stk, pb⟩)
  | "sbr_make_f_tablelim.L43bd", s => Fin k x ra t₀ s
  | "sbr_make_f_tablelim.done", s => TlimC x.lb x.a t₀ ∧ s.regs.get64 .rsp = rS t₀
      ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp ∧ SavedRegs t₀ s
      ∧ ∃ y stk pb, Tablelim x.lb.toNat x.a y
        ∧ y = { x.a with ftLim := y.ftLim, nlim := y.nlim } ∧ Lens ⟨y.ftLim, y.nlim, stk, pb⟩
        ∧ (s.dmem =⋆ T k x ra t₀ (Saved t₀) ⟨y.ftLim, y.nlim, stk, pb⟩)
  | _, _ => False
where
  /-- In the patch-border chain at step `i`: `eax = patch_borders[i]`, `ecx = num_patches`. -/
  Chain (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) (i : Nat) : Prop :=
    TlimC x.lb x.a t₀ ∧ Regs t₀ s ∧ x.lb ≠ 0#32
      ∧ s.regs.get64 .rax = v64 (x.a.kx1 + psum x.a.pnum i)
      ∧ s.regs.get64 .rcx = v64 x.a.npatch ∧ i < x.a.npatch ∧ Pre0 k x ra t₀ s (i + 1)
  /-- After the first copy: `f_tablelim[0..n[0]] = f_tablelow[0..n[0]]`. -/
  Cp (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) : Prop :=
    TlimC x.lb x.a t₀ ∧ Regs t₀ s ∧ x.lb ≠ 0#32 ∧ s.regs.get64 .r14 = pA t₀
      ∧ s.regs.get64 .r15 = v64 x.a.n0
      ∧ Mid k x ra t₀ s (fun fl _ => ∀ q, AV fl q = if q ≤ x.a.n0 then u16 x.a.ftLow q
          else u16 x.a.ftLim q)
  /-- After both copies: the array is `limIn`. -/
  Cp2 (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) : Prop :=
    TlimC x.lb x.a t₀ ∧ Regs t₀ s ∧ x.lb ≠ 0#32 ∧ s.regs.get64 .r14 = pA t₀
      ∧ s.regs.get64 .r15 = v64 x.a.n0 ∧ Mid k x ra t₀ s (fun fl _ => ∀ q, AV fl q = A0 x q)
  /-- The median-of-three registers (values loaded). -/
  Med (x : TArgs) (t₀ s : MachineData) (lo e : Nat) (fl : List UInt8) : Prop :=
    lo + 2 ≤ e ∧ s.regs.get64 .rdi = pA t₀ + v64 (2 * mid lo e)
      ∧ s.regs.get64 .r8 = pA t₀ + v64 (2 * (e - 1))
      ∧ s.regs.get64 .r10 = v64 (AV fl lo) ∧ s.regs.get64 .r11 = v64 (AV fl e)
      ∧ s.regs.get64 .r9 = v64 (AV fl (mid lo e))
  Med0 (x : TArgs) (t₀ s : MachineData) (lo e : Nat) : Prop :=
    lo + 2 ≤ e ∧ s.regs.get64 .rdi = pA t₀ + v64 (2 * mid lo e)
      ∧ s.regs.get64 .r8 = pA t₀ + v64 (2 * (e - 1))
  /-- After the median of three: `A lo ≤ A mid ≤ A e`, the pivot value in `r15`. -/
  Med3 (x : TArgs) (t₀ s : MachineData) (lo hi1 : Nat) (fl : List UInt8) : Prop :=
    Med0 x t₀ s lo (hi1 - 1) ∧ AV fl lo ≤ AV fl (mid lo (hi1 - 1))
      ∧ AV fl (mid lo (hi1 - 1)) ≤ AV fl (hi1 - 1)
      ∧ s.regs.get64 .r15 = v64 (AV fl (mid lo (hi1 - 1)))
  /-- Inside the partition loop. -/
  QPart (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData)
      (P : (Nat → Nat) → Nat → Nat → Nat → Nat → Prop) : Prop :=
    QR x t₀ s ∧ ∃ S lo hi1 l rt pv, Mid k x ra t₀ s (fun fl stk => StkRel (pA t₀) stk S
      ∧ CurF x t₀ s S lo hi1 (AV fl) ∧ PInv (AV fl) lo (hi1 - 1) l rt pv
      ∧ PR t₀ s (hi1 - 1) l rt ∧ P (AV fl) (hi1 - 1) l rt pv)
  /-- After the partition (the pivot at `l`). -/
  QDone (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData)
      (P : (Nat → Nat) → Nat → Nat → Nat → Prop) : Prop :=
    QR x t₀ s ∧ ∃ S lo hi1 l rt, Mid k x ra t₀ s (fun fl stk => StkRel (pA t₀) stk S
      ∧ CurF x t₀ s S lo hi1 (AV fl) ∧ PDone (AV fl) lo (hi1 - 1) l rt
      ∧ s.regs.get64 .r10 = pA t₀ + v64 (2 * l) ∧ s.regs.get64 .r9 = pA t₀ + v64 (2 * rt)
      ∧ P (AV fl) lo (hi1 - 1) l)

/-! ## The variant -/

/-- An 8-byte word of memory (0 if not loadable). -/
noncomputable def ld8 (s : MachineData) (a : BitVec 64) : BitVec 64 :=
  BitVec.ofInt 64 ((s.dmem.loadInt a 8).getD 0)

/-- A 4-byte cell of memory as a `Nat`. -/
noncomputable def ld4 (s : MachineData) (a : BitVec 64) : Nat :=
  ((s.dmem.loadInt a 4).getD 0).toNat

/-- The weight of an interval given by its `start`/`end` pointers (`wt` in bytes). -/
def wB (a b : BitVec 64) : Nat := if a.toNat ≤ b.toNat then b.toNat - a.toNat + 3 else 1

/-- `phi` of the stack in memory, `n` entries. -/
noncomputable def stkPhi (s : MachineData) (n : Nat) : Nat :=
  ((List.range n).map fun j =>
    wB (ld8 s (s.regs.get64 .rbp - 0x440#64 + v64 (16 * j)))
      (ld8 s (s.regs.get64 .rbp - 0x440#64 + v64 (16 * j) + 8#64))).sum

abbrev rN (s : MachineData) (r : Reg64) : Nat := (s.regs.get64 r).toNat

/-- `phi` with the current interval (`rsi`, `rdx`). -/
noncomputable def phiC (s : MachineData) : Nat :=
  stkPhi s (rN s .rcx) + wB (s.regs.get64 .rsi) (s.regs.get64 .rdx)

abbrev QV (Φ inner : Nat) : Nat := 2 ^ 40 + Φ * 4096 + inner

/-- The partition distance `right + 2 - left` (elements). -/
abbrev dP (s : MachineData) : Nat := (rN s .r9 + 4 - rN s .r10) / 2

abbrev lle (s : MachineData) : Prop := rN s .r10 ≤ rN s .r9

/-- In the compaction loop: `n_lim - out`. -/
noncomputable abbrev mu (s : MachineData) : Nat :=
  ld4 s (s.regs.get64 .rbx + 0x4c1ec#64) - (rN s .rcx - rN s .r14) / 2

noncomputable def var : Label → MachineData → Nat
  | "sbr_make_f_tablelim.L4060", s => QV (stkPhi s (rN s .rcx)) 3500
  | "sbr_make_f_tablelim.L4068", s => QV (stkPhi s (rN s .rcx)) 3500
  | "sbr_make_f_tablelim.L4090", s => QV (phiC s) 3000
  | "sbr_make_f_tablelim.L4280", s => QV (phiC s) 3000
  | "sbr_make_f_tablelim.L40c3", s => QV (phiC s) 3000
  | "sbr_make_f_tablelim.L40c9", s => QV (phiC s) 3000
  | "sbr_make_f_tablelim.L40e0", s => QV (phiC s) 3000
  | "sbr_make_f_tablelim.L40ec", s => QV (phiC s) 3000
  | "sbr_make_f_tablelim.L40f0", s => QV (phiC s) 3000
  | "sbr_make_f_tablelim.L40f7", s => QV (phiC s) 3000
  | "sbr_make_f_tablelim.L4105", s => QV (phiC s) 3000
  | "sbr_make_f_tablelim.L4110", s => QV (phiC s) 3000
  | "sbr_make_f_tablelim.L4120", s => QV (phiC s) 3000
  | "sbr_make_f_tablelim.L4130", s => QV (phiC s) 3000
  | "sbr_make_f_tablelim.L4150", s => QV (phiC s) (1000 + 4 * dP s)
  | "sbr_make_f_tablelim.L4164", s => QV (phiC s) (if lle s then 1000 + 4 * dP s + 3 else 1000)
  | "sbr_make_f_tablelim.L4169", s => QV (phiC s) (1000 + 4 * dP s + 3)
  | "sbr_make_f_tablelim.L4170", s => QV (phiC s) (1000 + 4 * dP s + 3)
  | "sbr_make_f_tablelim.L4190", s => QV (phiC s) (1000 + 4 * dP s + 1)
  | "sbr_make_f_tablelim.L4194", s => QV (phiC s) (if lle s then 1000 + 4 * dP s + 2 else 1001)
  | "sbr_make_f_tablelim.L4199", s => QV (phiC s) (1000 + 4 * dP s + 2)
  | "sbr_make_f_tablelim.L41b0", s => QV (phiC s) 900
  | "sbr_make_f_tablelim.L41b4", s => QV (phiC s) 900
  | "sbr_make_f_tablelim.L41ca", s => QV (phiC s) 900
  | "sbr_make_f_tablelim.L41d3", s => QV (phiC s) 900
  | "sbr_make_f_tablelim.L41e0", s => QV (phiC s) (500 + (rN s .rdx - rN s .r8) / 2)
  | "sbr_make_f_tablelim.L41f7", s => QV (phiC s) 400
  | "sbr_make_f_tablelim.L4200", s => QV (phiC s) 300
  | "sbr_make_f_tablelim.L4211", s => QV (phiC s) 300
  | "sbr_make_f_tablelim.L421b", s => QV (phiC s) 300
  | "sbr_make_f_tablelim.L4250", s => QV (phiC s) 300
  | "sbr_make_f_tablelim.L425a", s => QV (phiC s) 300
  | "sbr_make_f_tablelim.L429d", _ => 2 ^ 20
  | "sbr_make_f_tablelim.L42b6", _ => 2 ^ 20
  | "sbr_make_f_tablelim.L42bc", _ => 2 ^ 20
  | "sbr_make_f_tablelim.L42eb", s => 64 * mu s + 63
  | "sbr_make_f_tablelim.L42fa", s => 64 * mu s + 62
  | "sbr_make_f_tablelim.L4312", s => 64 * mu s + 61
  | "sbr_make_f_tablelim.L4317", s => 64 * mu s + 60
  | "sbr_make_f_tablelim.L4323", s => 64 * mu s + 59
  | "sbr_make_f_tablelim.L4330", s => 64 * mu s + 40 + 2 * (rN s .r8 - rN s .r9)
  | "sbr_make_f_tablelim.L4338", s => 64 * mu s + 39 + 2 * (rN s .r8 - rN s .r9)
  | "sbr_make_f_tablelim.L4340", s => 64 * mu s + 38
  | "sbr_make_f_tablelim.L4342", s => 64 * mu s + 37
  | "sbr_make_f_tablelim.L4350", s => 64 * mu s + 20 + 2 * (rN s .r8 - rN s .rdx)
  | "sbr_make_f_tablelim.L435b", s => 64 * mu s + 19 + 2 * (rN s .r8 - rN s .rdx)
  | "sbr_make_f_tablelim.L4363", s => 64 * mu s + 2
  | "sbr_make_f_tablelim.L4370", s => 64 * mu s + 1
  | "sbr_make_f_tablelim.L42d0", s => 64 * mu s
  | "sbr_make_f_tablelim.L438a", _ => 0
  | "sbr_make_f_tablelim.L4398", _ => 0
  | "sbr_make_f_tablelim.L43a4", _ => 0
  | "sbr_make_f_tablelim.L43bd", _ => 0
  | "sbr_make_f_tablelim.done", _ => 0
  | _, _ => 2 ^ 50

/-! ## The obligations -/

/-- What a return leaves, with the footprint as the routine's cells. -/
abbrev Post' (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) : Prop :=
  let r := rS t₀
  ∃ y stk pb, Tablelim x.lb.toNat x.a y ∧ y = { x.a with ftLim := y.ftLim, nlim := y.nlim }
    ∧ Lens ⟨y.ftLim, y.nlim, stk, pb⟩
    ∧ s.regs.get64 .rsp = r + 8 ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp ∧ SavedRegs t₀ s
    ∧ (s.dmem =⋆ T k x ra t₀ (fun _ => Saved t₀ (8 ?@ r ⋆ x.R)) ⟨y.ftLim, y.nlim, stk, pb⟩)

abbrev BlockOb (k : Nat) (x : TArgs) (ra : Int64) (t₀ : MachineData) (l : Label) : Prop :=
  ∀ blk, Program.blockAt body l = some blk → ∀ n : Nat,
    ⦃ fun s => table k x ra t₀ l s ∧ var l s = n ⦄ blk.body
    ⦃ (match blk.next with
       | some l' => fun _ s => table k x ra t₀ l' s ∧ var l' s ≤ n
       | none => fun _ _ => False);
      fun a s => Table.ofLabels (fun l' s => (Program.blockAt body l').isSome
          ∧ table k x ra t₀ l' s ∧ Program.EdgeLt body var l n l' s) a s
        ∨ (a = ra ∧ Post' k x ra t₀ s) ⦄

end Kraken.Examples.Sbr.Tlim
