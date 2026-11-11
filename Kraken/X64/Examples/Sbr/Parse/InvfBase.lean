import Kraken.X64.Examples.Sbr.Parse.InvfSpec

/-!
# `read_sbr_invf`: the block table

The assertions at the labels of `body`. After the copy `bs_invf_mode[1] = bs_invf_mode[0]`
and `k` reads, the array is `invfMid k x.inv vals`; `invfMid x.nq` is the post's `invfNew`.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.Invf

open Kraken.Examples.Sbr.ParseModel (mk old)

variable [CodeEnv]

/-- The array after the copy and `k` reads. -/
def invfMid (k : Nat) (inv : List UInt8) (vals : Nat → Nat) : List UInt8 :=
  mk 10 (fun i => if i < 5 then (if i < k then UInt8.ofNat (vals i % 4) else old inv i)
    else old inv (i - 5))

omit [CodeEnv] in
theorem invfMid_nq (nq : Nat) (inv : List UInt8) (vals : Nat → Nat) :
    invfMid nq inv vals = invfNew nq inv vals := rfl

def Rest (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) : Mem 64 → Prop :=
  RetCell ra (t₀.regs.get64 .rsp) ⋆ (Reserve 0 (t₀.regs.get64 .rsp) ⋆ R)

/-- The array, opaque. -/
def InvB (d : BitVec 64) (inv : List UInt8) : Mem 64 → Prop := inv =@ (d + 0x27#64)

/-- The memory at every label. -/
abbrev T (x : IArgs) (ra : Int64) (t₀ : MachineData) (inv : List UInt8) (i : BitVec 32) :
    Mem 64 → Prop :=
  c4 (arg0 t₀ + 0x4c1e8#64) x.nq ⋆ (InvB (arg2 t₀) inv ⋆ (GbW (arg1 t₀) x i
    ⋆ (Blocks [(x.buf, x.L)] ⋆ Rest x.R ra t₀)))

/-- The argument registers and the stack pointer. -/
abbrev Regs (t₀ s : MachineData) : Prop :=
  s.regs.get64 .rdi = arg0 t₀ ∧ s.regs.get64 .rsi = arg1 t₀ ∧ s.regs.get64 .rdx = arg2 t₀
  ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp
  ∧ SavedRegs t₀ s

/-- Before read `k` (`k < n_q`). -/
abbrev Mid (k : Nat) (x : IArgs) (ra : Int64) (t₀ s : MachineData) : Prop :=
  InvfC x ∧ Regs t₀ s ∧ k < x.nq
  ∧ ∃ (vals : Nat → Nat) (i : BitVec 32), x.idx.toNat ≤ i.toNat ∧ i.toNat ≤ x.p8.toNat
    ∧ (s.dmem =⋆ T x ra t₀ (invfMid k x.inv vals) i)

/-- After the last read. -/
abbrev Fin (x : IArgs) (ra : Int64) (t₀ s : MachineData) : Prop :=
  InvfC x ∧ Regs t₀ s
  ∧ ∃ (vals : Nat → Nat) (i : BitVec 32), x.idx.toNat ≤ i.toNat ∧ i.toNat ≤ x.p8.toNat
    ∧ (s.dmem =⋆ T x ra t₀ (invfMid x.nq x.inv vals) i)

abbrev table (x : IArgs) (ra : Int64) (t₀ : MachineData) : Label → MachineData → Prop
  | "read_sbr_invf", s => s = t₀ ∧ InvfC x ∧ (t₀.dmem =⋆ T x ra t₀ x.inv x.idx)
  | "read_sbr_invf.L564a", s => Mid 0 x ra t₀ s
  | "read_sbr_invf.L5693", s => Mid 1 x ra t₀ s
  | "read_sbr_invf.L56d5", s => Mid 2 x ra t₀ s
  | "read_sbr_invf.L5713", s => Mid 3 x ra t₀ s
  | "read_sbr_invf.L5751", s => Mid 4 x ra t₀ s
  | "read_sbr_invf.L578f", s => Fin x ra t₀ s
  | "read_sbr_invf.done", s => Fin x ra t₀ s
  | _, _ => False

abbrev var : Label → MachineData → Nat
  | _, _ => 0

/-- What a return leaves. -/
abbrev Post' (x : IArgs) (ra : Int64) (t₀ s : MachineData) : Prop :=
  let r := t₀.regs.get64 .rsp
  ∃ (vals : Nat → Nat) (i : BitVec 32), x.idx.toNat ≤ i.toNat ∧ i.toNat ≤ x.p8.toNat
    ∧ s.regs.get64 .rsp = r + 8 ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp ∧ SavedRegs t₀ s
    ∧ (s.dmem =⋆ c4 (arg0 t₀ + 0x4c1e8#64) x.nq ⋆ (InvB (arg2 t₀) (invfNew x.nq x.inv vals)
      ⋆ (GbW (arg1 t₀) x i ⋆ (Blocks [(x.buf, x.L)]
      ⋆ (8 ?@ r ⋆ (Reserve 0 r ⋆ x.R))))))

abbrev BlockOb (x : IArgs) (ra : Int64) (t₀ : MachineData) (l : Label) : Prop :=
  ∀ blk, Program.blockAt body l = some blk → ∀ n : Nat,
    ⦃ fun s => table x ra t₀ l s ∧ var l s = n ⦄ blk.body
    ⦃ (match blk.next with
       | some l' => fun _ s => table x ra t₀ l' s ∧ var l' s ≤ n
       | none => fun _ _ => False);
      fun a s => Table.ofLabels (fun l' s => (Program.blockAt body l').isSome
          ∧ table x ra t₀ l' s ∧ Program.EdgeLt body var l n l' s) a s
        ∨ (a = ra ∧ Post' x ra t₀ s) ⦄

end Kraken.Examples.Sbr.Invf
