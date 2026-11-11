import Kraken.X64.Examples.Sbr.Parse.TlimBase

/-!
# `sbr_make_f_tablelim`: the table entry at each label

`table` at a literal label, as an `Iff.rfl` lemma (unfolding the string match inside a block is
expensive).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse.Qsort

namespace Kraken.Examples.Sbr.Tlim

variable [CodeEnv]

theorem tab_entry (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim" s ↔
    s = t₀ ∧ TlimC x.lb x.a t₀
        ∧ ∃ stk pb, Lens (st0 x stk pb) ∧ (t₀.dmem =⋆ T k x ra t₀ (BlankS (rS t₀)) (st0 x stk pb)) := Iff.rfl

theorem tab_L3f22 (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L3f22" s ↔
    TlimC x.lb x.a t₀ ∧ Regs0 t₀ s
        ∧ s.regs.get64 .rdi = sA t₀ ∧ Pre0 k x ra t₀ s 0 := Iff.rfl

theorem tab_L3f31 (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L3f31" s ↔
    TlimC x.lb x.a t₀ ∧ Regs t₀ s
        ∧ s.regs.get64 .rax = x.lb.setWidth 64 ∧ x.lb ≠ 0#32 ∧ Pre0 k x ra t₀ s 0 := Iff.rfl

theorem tab_L3f3a (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L3f3a" s ↔
    TlimC x.lb x.a t₀ ∧ Regs t₀ s
        ∧ s.regs.get64 .rax = x.lb.setWidth 64 ∧ x.lb ≠ 0#32 ∧ Pre0 k x ra t₀ s 0 := Iff.rfl

theorem tab_L3f59 (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L3f59" s ↔
    TlimC x.lb x.a t₀ ∧ Regs t₀ s ∧ x.lb ≠ 0#32
        ∧ s.regs.get64 .rax = v64 x.a.kx1 ∧ s.regs.get64 .rcx = v64 x.a.npatch ∧ x.a.npatch ≠ 0
        ∧ Pre0 k x ra t₀ s 1 := Iff.rfl

theorem tab_L3f65 (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L3f65" s ↔
    table.Chain k x ra t₀ s 0 := Iff.rfl

theorem tab_L3f77 (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L3f77" s ↔
    table.Chain k x ra t₀ s 1 := Iff.rfl

theorem tab_L3f89 (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L3f89" s ↔
    table.Chain k x ra t₀ s 2 := Iff.rfl

theorem tab_L3f9b (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L3f9b" s ↔
    table.Chain k x ra t₀ s 3 := Iff.rfl

theorem tab_L3fad (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L3fad" s ↔
    table.Chain k x ra t₀ s 4 := Iff.rfl

theorem tab_L3fbf (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L3fbf" s ↔
    table.Chain k x ra t₀ s 5 := Iff.rfl

theorem tab_L3fcc (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L3fcc" s ↔
    TlimC x.lb x.a t₀ ∧ Regs t₀ s ∧ x.lb ≠ 0#32
        ∧ Pre0 k x ra t₀ s (x.a.npatch + 1) := Iff.rfl

theorem tab_L3ff5 (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L3ff5" s ↔
    table.Cp k x ra t₀ s := Iff.rfl

theorem tab_L4000 (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L4000" s ↔
    table.Cp k x ra t₀ s ∧ s.regs.get64 .rdx = v64 x.a.npatch
        ∧ 2 ≤ x.a.npatch := Iff.rfl

theorem tab_L400a (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L400a" s ↔
    table.Cp k x ra t₀ s ∧ s.regs.get64 .rdx = v64 x.a.npatch
        ∧ 2 ≤ x.a.npatch := Iff.rfl

theorem tab_L4020 (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L4020" s ↔
    table.Cp2 k x ra t₀ s := Iff.rfl

theorem tab_L4026 (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L4026" s ↔
    table.Cp2 k x ra t₀ s ∧ s.regs.get64 .rdx = v64 x.a.npatch := Iff.rfl

theorem tab_L403f (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L403f" s ↔
    TlimC x.lb x.a t₀ ∧ Regs t₀ s ∧ x.lb ≠ 0#32
        ∧ s.regs.get64 .r14 = pA t₀ ∧ s.regs.get64 .r15 = v64 (NN x)
        ∧ Mid k x ra t₀ s (fun fl stk => (∀ q, AV fl q = A0 x q) ∧ w8 stk 0 = pA t₀) := Iff.rfl

theorem tab_L4060 (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L4060" s ↔
    QPop k x ra t₀ s := Iff.rfl

theorem tab_L4068 (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L4068" s ↔
    QPop k x ra t₀ s ∧ s.regs.get64 .rcx ≠ 0#64 := Iff.rfl

theorem tab_L4090 (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L4090" s ↔
    QCur k x ra t₀ s (fun _ _ _ _ => True) := Iff.rfl

theorem tab_L4280 (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L4280" s ↔
    QCur k x ra t₀ s (fun _ lo hi1 _ => hi1 = lo + 2) := Iff.rfl

theorem tab_L40c3 (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L40c3" s ↔
    QCur k x ra t₀ s (fun _ lo hi1 fl =>
        table.Med x t₀ s lo (hi1 - 1) fl ∧ AV fl (hi1 - 1) < AV fl lo) := Iff.rfl

theorem tab_L40c9 (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L40c9" s ↔
    QCur k x ra t₀ s (fun _ lo hi1 fl =>
        table.Med x t₀ s lo (hi1 - 1) fl ∧ AV fl (hi1 - 1) < AV fl lo
        ∧ AV fl (hi1 - 1) ≤ AV fl (mid lo (hi1 - 1))) := Iff.rfl

theorem tab_L40e0 (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L40e0" s ↔
    QCur k x ra t₀ s (fun _ lo hi1 fl =>
        table.Med x t₀ s lo (hi1 - 1) fl ∧ AV fl lo ≤ AV fl (hi1 - 1)) := Iff.rfl

theorem tab_L40ec (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L40ec" s ↔
    QCur k x ra t₀ s (fun _ lo hi1 fl =>
      table.Med0 x t₀ s lo (hi1 - 1) ∧ s.regs.get64 .r10 = v64 (AV fl lo)
      ∧ s.regs.get64 .r9 = v64 (AV fl (mid lo (hi1 - 1)))
      ∧ (AV fl (mid lo (hi1 - 1)) < AV fl lo ∧ AV fl lo ≤ AV fl (hi1 - 1)
        ∨ AV fl (mid lo (hi1 - 1)) < AV fl (hi1 - 1) ∧ AV fl (hi1 - 1) < AV fl lo)) := Iff.rfl

theorem tab_L40f0 (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L40f0" s ↔
    QR x t₀ s ∧ ∃ S lo hi1 A pos,
        Mid k x ra t₀ s (fun fl stk => StkRel (pA t₀) stk S ∧ CurF x t₀ s S lo hi1 A
          ∧ lo + 2 ≤ hi1 - 1 ∧ (pos = mid lo (hi1 - 1) ∨ pos = hi1 - 1)
          ∧ (∀ q, AV fl q = Parse.Qsort.upd A pos (A lo) q) ∧ s.regs.get64 .r9 = v64 (A pos)
          ∧ s.regs.get64 .rdi = pA t₀ + v64 (2 * mid lo (hi1 - 1))
          ∧ s.regs.get64 .r8 = pA t₀ + v64 (2 * (hi1 - 2))
          ∧ (pos = mid lo (hi1 - 1) → A pos < A lo ∧ A lo ≤ A (hi1 - 1)
              ∨ A pos < A (hi1 - 1) ∧ A (hi1 - 1) < A lo)
          ∧ (pos = hi1 - 1 → A pos < A lo ∧ A pos ≤ A (mid lo (hi1 - 1)))) := Iff.rfl

theorem tab_L40f7 (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L40f7" s ↔
    QCur k x ra t₀ s (fun _ lo hi1 fl =>
        table.Med0 x t₀ s lo (hi1 - 1) ∧ AV fl lo ≤ AV fl (mid lo (hi1 - 1))
        ∧ AV fl lo ≤ AV fl (hi1 - 1)) := Iff.rfl

theorem tab_L4105 (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L4105" s ↔
    QCur k x ra t₀ s (fun _ lo hi1 fl =>
        table.Med0 x t₀ s lo (hi1 - 1) ∧ AV fl lo ≤ AV fl (hi1 - 1)
        ∧ AV fl (hi1 - 1) < AV fl (mid lo (hi1 - 1))
        ∧ s.regs.get64 .r9 = v64 (AV fl (mid lo (hi1 - 1)))
        ∧ s.regs.get64 .r15 = v64 (AV fl (hi1 - 1))) := Iff.rfl

theorem tab_L4110 (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L4110" s ↔
    QCur k x ra t₀ s (fun _ lo hi1 fl => table.Med3 x t₀ s lo hi1 fl) := Iff.rfl

theorem tab_L4120 (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L4120" s ↔
    QCur k x ra t₀ s (fun _ lo hi1 fl =>
        table.Med0 x t₀ s lo (hi1 - 1) ∧ AV fl lo ≤ AV fl (mid lo (hi1 - 1))
        ∧ AV fl (mid lo (hi1 - 1)) ≤ AV fl (hi1 - 1)
        ∧ s.regs.get64 .r9 = v64 (AV fl (mid lo (hi1 - 1)))) := Iff.rfl

theorem tab_L4130 (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L4130" s ↔
    QCur k x ra t₀ s (fun _ lo hi1 fl =>
        table.Med3 x t₀ s lo hi1 fl ∧ lo + 3 ≤ hi1 - 1
        ∧ s.regs.get64 .r9 = pA t₀ + v64 (2 * (hi1 - 3))) := Iff.rfl

theorem tab_L4150 (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L4150" s ↔
    table.QPart k x ra t₀ s (fun A e l rt pv =>
        l ≤ rt ∧ pv ≤ A l ∧ A rt ≤ pv ∧ s.regs.get64 .r12 = v64 (A rt)) := Iff.rfl

theorem tab_L4164 (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L4164" s ↔
    table.QPart k x ra t₀ s (fun _ _ _ _ _ => True) := Iff.rfl

theorem tab_L4169 (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L4169" s ↔
    table.QPart k x ra t₀ s (fun _ _ l rt _ => l ≤ rt) := Iff.rfl

theorem tab_L4170 (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L4170" s ↔
    table.QPart k x ra t₀ s (fun _ _ l rt pv =>
        l ≤ rt ∧ s.regs.get64 .r15 = v64 pv) := Iff.rfl

theorem tab_L4190 (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L4190" s ↔
    table.QPart k x ra t₀ s (fun A _ l rt pv =>
        l ≤ rt ∧ pv ≤ A l ∧ pv < A rt ∧ s.regs.get64 .r15 = v64 pv) := Iff.rfl

theorem tab_L4194 (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L4194" s ↔
    table.QPart k x ra t₀ s (fun A _ l rt pv =>
        l ≤ rt + 1 ∧ (l ≤ rt → pv ≤ A l) ∧ s.regs.get64 .r15 = v64 pv) := Iff.rfl

theorem tab_L4199 (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L4199" s ↔
    table.QPart k x ra t₀ s (fun A _ l rt pv =>
        l ≤ rt ∧ pv ≤ A l ∧ s.regs.get64 .r15 = v64 pv) := Iff.rfl

theorem tab_L41b0 (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L41b0" s ↔
    table.QPart k x ra t₀ s (fun _ _ l rt _ => rt < l) := Iff.rfl

theorem tab_L41b4 (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L41b4" s ↔
    table.QPart k x ra t₀ s (fun _ _ l rt pv =>
        rt < l ∧ s.regs.get64 .r15 = v64 pv) := Iff.rfl

theorem tab_L41ca (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L41ca" s ↔
    table.QDone k x ra t₀ s (fun _ _ _ _ => True) := Iff.rfl

theorem tab_L41d3 (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L41d3" s ↔
    table.QDone k x ra t₀ s (fun _ _ _ _ => True) := Iff.rfl

theorem tab_L41e0 (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L41e0" s ↔
    table.QDone k x ra t₀ s (fun A lo e _ =>
        ∃ m, lo ≤ m ∧ m ≤ e ∧ s.regs.get64 .r8 = pA t₀ + v64 (2 * m)
          ∧ ∀ q, lo ≤ q → q < m → A q ≤ A (q + 1)) := Iff.rfl

theorem tab_L41f7 (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L41f7" s ↔
    table.QDone k x ra t₀ s (fun A lo e _ =>
        ∃ m, lo ≤ m ∧ m ≤ e ∧ s.regs.get64 .rdi = pA t₀ + v64 (2 * m)
          ∧ ∀ q, lo ≤ q → q < m → A q ≤ A (q + 1)) := Iff.rfl

theorem tab_L4200 (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L4200" s ↔
    table.QDone k x ra t₀ s (fun _ _ _ _ => True) := Iff.rfl

theorem tab_L4211 (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L4211" s ↔
    table.QDone k x ra t₀ s (fun _ lo e l => e - l < l - lo) := Iff.rfl

theorem tab_L421b (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L421b" s ↔
    table.QDone k x ra t₀ s (fun _ lo e l => e - l < l - lo) := Iff.rfl

theorem tab_L4250 (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L4250" s ↔
    table.QDone k x ra t₀ s (fun _ lo e l => l - lo ≤ e - l) := Iff.rfl

theorem tab_L425a (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L425a" s ↔
    table.QDone k x ra t₀ s (fun _ lo e l => l - lo ≤ e - l) := Iff.rfl

theorem tab_L429d (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L429d" s ↔
    QR x t₀ s
        ∧ Mid k x ra t₀ s (fun fl _ => Sorted (NN x) (A0 x) (AV fl)) := Iff.rfl

theorem tab_L42b6 (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L42b6" s ↔
    TlimC x.lb x.a t₀ ∧ Regs t₀ s ∧ s.regs.get64 .r14 = pA t₀
        ∧ s.regs.get64 .rax = pA t₀ + 2#64 ∧ 1 ≤ NN x ∧ x.lb ≠ 0#32 ∧ s.regs.get64 .rdx = v64 (NN x - 1)
        ∧ CondCode.a.interp s.status = false
        ∧ ∃ fl stk pb, Lens ⟨fl, NN x - 1, stk, pb⟩ ∧ PBto x pb (x.a.npatch + 1)
          ∧ Sorted (NN x) (A0 x) (AV fl)
          ∧ (s.dmem =⋆ T k x ra t₀ (Saved t₀) ⟨fl, NN x - 1, stk, pb⟩) := Iff.rfl

theorem tab_L42bc (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L42bc" s ↔
    TlimC x.lb x.a t₀ ∧ Regs t₀ s ∧ s.regs.get64 .r14 = pA t₀
        ∧ s.regs.get64 .rax = pA t₀ + 2#64 ∧ 1 ≤ NN x ∧ x.lb ≠ 0#32 ∧ s.regs.get64 .rdx = v64 (NN x - 1)
        ∧ ∃ fl stk pb, Lens ⟨fl, NN x - 1, stk, pb⟩ ∧ PBto x pb (x.a.npatch + 1)
          ∧ Sorted (NN x) (A0 x) (AV fl)
          ∧ (s.dmem =⋆ T k x ra t₀ (Saved t₀) ⟨fl, NN x - 1, stk, pb⟩) := Iff.rfl

theorem tab_L42eb (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L42eb" s ↔
    QC k x ra t₀ s (fun _ _ L _ => s.regs.get64 .rdx = v64 L) := Iff.rfl

theorem tab_L42fa (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L42fa" s ↔
    QC k x ra t₀ s (fun _ o L _ => o < L ∧ s.regs.get64 .rdx = v64 L) := Iff.rfl

theorem tab_L4312 (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L4312" s ↔
    QC k x ra t₀ s (fun i o L fl => o < L ∧ s.regs.get64 .rdx = v64 L
        ∧ s.regs.get64 .rsi = v64 (AV fl i) ∧ s.regs.get64 .rdi = v64 (AV fl o)) := Iff.rfl

theorem tab_L4317 (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L4317" s ↔
    QC k x ra t₀ s (fun i o L fl => o < L ∧ s.regs.get64 .rdx = v64 L
        ∧ s.regs.get64 .rsi = v64 (AV fl i)) := Iff.rfl

theorem tab_L4323 (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L4323" s ↔
    QC k x ra t₀ s (fun i o L fl => o < L ∧ s.regs.get64 .rdx = v64 L
        ∧ s.regs.get64 .rsi = v64 (AV fl i) ∧ s.regs.get64 .r8 = v64 x.a.npatch) := Iff.rfl

theorem tab_L4330 (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L4330" s ↔
    QC k x ra t₀ s (fun i o L fl => o < L ∧ s.regs.get64 .rdx = v64 L
        ∧ s.regs.get64 .rsi = v64 (AV fl i) ∧ s.regs.get64 .r8 = v64 (x.a.npatch + 1)
        ∧ ∃ j, j ≤ x.a.npatch ∧ s.regs.get64 .r9 = v64 j) := Iff.rfl

theorem tab_L4338 (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L4338" s ↔
    QC k x ra t₀ s (fun i o L fl => o < L ∧ s.regs.get64 .rdx = v64 L
        ∧ s.regs.get64 .rsi = v64 (AV fl i) ∧ s.regs.get64 .r8 = v64 (x.a.npatch + 1)
        ∧ ∃ j, j ≤ x.a.npatch ∧ s.regs.get64 .r9 = v64 j) := Iff.rfl

theorem tab_L4340 (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L4340" s ↔
    QC k x ra t₀ s (fun _ o L _ => o < L ∧ s.regs.get64 .rdx = v64 L) := Iff.rfl

theorem tab_L4342 (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L4342" s ↔
    QC k x ra t₀ s (fun i o L fl => o < L
        ∧ s.regs.get64 .rsi = v64 (AV fl i) ∧ s.regs.get64 .r8 = v64 (x.a.npatch + 1)) := Iff.rfl

theorem tab_L4350 (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L4350" s ↔
    QC k x ra t₀ s (fun i o L fl => o < L
        ∧ s.regs.get64 .rsi = v64 (AV fl i) ∧ s.regs.get64 .r8 = v64 (x.a.npatch + 1)
        ∧ ∃ j, j ≤ x.a.npatch ∧ s.regs.get64 .rdx = v64 j) := Iff.rfl

theorem tab_L435b (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L435b" s ↔
    QC k x ra t₀ s (fun i o L fl => o < L
        ∧ s.regs.get64 .rsi = v64 (AV fl i) ∧ s.regs.get64 .r8 = v64 (x.a.npatch + 1)
        ∧ ∃ j, j ≤ x.a.npatch ∧ s.regs.get64 .rdx = v64 j) := Iff.rfl

theorem tab_L4363 (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L4363" s ↔
    QC k x ra t₀ s (fun i o L fl => o < L
        ∧ s.regs.get64 .rsi = v64 (AV fl i)) := Iff.rfl

theorem tab_L4370 (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L4370" s ↔
    TlimC x.lb x.a t₀ ∧ Regs t₀ s ∧ s.regs.get64 .r14 = pA t₀
      ∧ 1 ≤ NN x ∧ x.lb ≠ 0#32
      ∧ ∃ sa fl stk pb i o L, Lens ⟨fl, L, stk, pb⟩ ∧ PBto x pb (x.a.npatch + 1)
        ∧ CmpD x t₀ s sa fl i o L ∧ o < L ∧ s.regs.get64 .rdx = v64 L
        ∧ (s.dmem =⋆ T k x ra t₀ (Saved t₀) ⟨fl, L, stk, pb⟩) := Iff.rfl

theorem tab_L42d0 (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L42d0" s ↔
    QC k x ra t₀ s (fun i o L fl => o < L
        ∧ s.regs.get64 .rsi = v64 (AV fl i)) := Iff.rfl

theorem tab_L438a (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L438a" s ↔
    TlimC x.lb x.a t₀ ∧ Regs t₀ s ∧ x.lb = 0#32
        ∧ Pre0 k x ra t₀ s 0 := Iff.rfl

theorem tab_L4398 (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L4398" s ↔
    TlimC x.lb x.a t₀ ∧ Regs t₀ s ∧ x.lb = 0#32
        ∧ ∃ stk pb, Lens (st0 x stk pb)
          ∧ (s.dmem =⋆ T k x ra t₀ (Saved t₀) ⟨setW2 x.a.ftLim 0 (u16 x.a.ftLow 0), x.a.nlim, stk, pb⟩) := Iff.rfl

theorem tab_L43a4 (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L43a4" s ↔
    TlimC x.lb x.a t₀ ∧ Regs t₀ s ∧ x.lb = 0#32
        ∧ s.regs.get64 .rax = v64 x.a.n0
        ∧ ∃ stk pb, Lens (st0 x stk pb)
          ∧ (s.dmem =⋆ T k x ra t₀ (Saved t₀) ⟨setW2 x.a.ftLim 0 (u16 x.a.ftLow 0), x.a.nlim, stk, pb⟩) := Iff.rfl

theorem tab_L43bd (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.L43bd" s ↔
    Fin k x ra t₀ s := Iff.rfl

theorem tab_done (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :
    table k x ra t₀ "sbr_make_f_tablelim.done" s ↔
    TlimC x.lb x.a t₀ ∧ s.regs.get64 .rsp = rS t₀
        ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp ∧ SavedRegs t₀ s
        ∧ ∃ y stk pb, Tablelim x.lb.toNat x.a y
          ∧ y = { x.a with ftLim := y.ftLim, nlim := y.nlim } ∧ Lens ⟨y.ftLim, y.nlim, stk, pb⟩
          ∧ (s.dmem =⋆ T k x ra t₀ (Saved t₀) ⟨y.ftLim, y.nlim, stk, pb⟩) := Iff.rfl

end Kraken.Examples.Sbr.Tlim
