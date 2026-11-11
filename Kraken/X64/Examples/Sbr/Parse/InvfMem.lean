import Kraken.X64.Examples.Sbr.Parse.InvfBase
import Kraken.X64.Examples.Sbr.Parse.HdrLib

/-!
# `read_sbr_invf`: footprint access lemmas

Each access brings its cell to the front of `T` with an AC equation and uses a lemma proved
once: the array `bs_invf_mode` is one byte region, accessed through `loadInt_slice` /
`storeInt_slice`.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.Invf

open Kraken.Examples.Sbr.ParseModel (mk old)
open Kraken.Examples.Sbr.HdrLib

variable [CodeEnv]

/-! ## The footprint's atoms -/

/-- `T` without the array. -/
abbrev TxInv (x : IArgs) (ra : Int64) (t₀ : MachineData) (i : BitVec 32) : Mem 64 → Prop :=
  c4 (arg0 t₀ + 0x4c1e8#64) x.nq ⋆ (GbW (arg1 t₀) x i ⋆ (Blocks [(x.buf, x.L)] ⋆ Rest x.R ra t₀))

omit [CodeEnv] in
theorem T_inv (x : IArgs) (ra : Int64) (t₀ : MachineData) (inv : List UInt8) (i : BitVec 32) :
    T x ra t₀ inv i = inv =@ (arg2 t₀ + 0x27#64) ⋆ TxInv x ra t₀ i := by
  simp only [T, TxInv, InvB]; ac_rfl

/-- `T` without the reader's index. -/
abbrev TxI (x : IArgs) (ra : Int64) (t₀ : MachineData) (inv : List UInt8) : Mem 64 → Prop :=
  c4 (arg0 t₀ + 0x4c1e8#64) x.nq ⋆ (InvB (arg2 t₀) inv ⋆ ((Int.toBytes 8 x.buf.toInt =@ arg1 t₀
    ⋆ (4 ?@ (arg1 t₀ + 0xc#64) ⋆ cell4 (arg1 t₀ + 0x10#64) x.p8))
    ⋆ (Blocks [(x.buf, x.L)] ⋆ Rest x.R ra t₀)))

omit [CodeEnv] in
theorem T_i (x : IArgs) (ra : Int64) (t₀ : MachineData) (inv : List UInt8) (i : BitVec 32) :
    T x ra t₀ inv i = cell4 (arg1 t₀ + 8#64) i ⋆ TxI x ra t₀ inv := by
  simp only [T, TxI, GbW]; ac_rfl

omit [CodeEnv] in
theorem T_storeI {m : Mem 64} {x : IArgs} {ra : Int64} {t₀ : MachineData} {inv : List UInt8}
    {i : BitVec 32} (h : m =⋆ T x ra t₀ inv i) (v : BitVec 32) :
    m.storeInt (arg1 t₀ + 8#64) 4 v.toInt =⋆ T x ra t₀ inv v := by
  rw [T_i] at h ⊢
  exact storeInt_sep _ 4 _ _ m ⟨h, Int.toBytes_length 4 _⟩ v.toInt

omit [CodeEnv] in
theorem T_gb {m : Mem 64} {x : IArgs} {ra : Int64} {t₀ : MachineData} {inv : List UInt8}
    {i : BitVec 32} (h : m =⋆ T x ra t₀ inv i) : ∃ F, m =⋆ GbW (arg1 t₀) x i ⋆ F :=
  ⟨_, by rw [show T x ra t₀ inv i = GbW (arg1 t₀) x i ⋆ (c4 (arg0 t₀ + 0x4c1e8#64) x.nq
      ⋆ (InvB (arg2 t₀) inv ⋆ (Blocks [(x.buf, x.L)] ⋆ Rest x.R ra t₀))) by
        simp only [T]; ac_rfl] at h; exact h⟩

omit [CodeEnv] in
theorem T_load_nq {m : Mem 64} {x : IArgs} {ra : Int64} {t₀ : MachineData} {inv : List UInt8}
    {i : BitVec 32} (h : m =⋆ T x ra t₀ inv i) :
    m.loadInt (arg0 t₀ + 0x4c1e8#64) 4 = some (Int.ofBytes (Int.toBytes 4 (x.nq : Int))) :=
  loadInt_sep _ _ 4 _ m h (Int.toBytes_length 4 _) (by omega)

omit [CodeEnv] in
theorem T_buf_load {m : Mem 64} {x : IArgs} {ra : Int64} {t₀ : MachineData} {inv : List UInt8}
    {i : BitVec 32} (h : m =⋆ T x ra t₀ inv i) (off : BitVec 64) (n : Nat)
    (hin : off.toNat + n ≤ x.L) : (m.loadInt (x.buf + off) n).isSome = true := by
  have h' : m =⋆ Blocks [(x.buf, x.L)] ⋆ (c4 (arg0 t₀ + 0x4c1e8#64) x.nq
      ⋆ (InvB (arg2 t₀) inv ⋆ (GbW (arg1 t₀) x i ⋆ Rest x.R ra t₀))) := by
    rw [show (Blocks [(x.buf, x.L)] ⋆ (c4 (arg0 t₀ + 0x4c1e8#64) x.nq
      ⋆ (InvB (arg2 t₀) inv ⋆ (GbW (arg1 t₀) x i ⋆ Rest x.R ra t₀)))) = T x ra t₀ inv i by
        simp only [T]; ac_rfl]; exact h
  exact Blocks.loadInt_isSome h' (Blocks.Inside.base_add hin)

omit [CodeEnv] in
/-- A load from the array. -/
theorem T_load_inv {m : Mem 64} {x : IArgs} {ra : Int64} {t₀ : MachineData} {inv : List UInt8}
    {i : BitVec 32} (h : m =⋆ T x ra t₀ inv i) (o n : Nat) (hin : o + n ≤ inv.length)
    (hl : inv.length < 2 ^ 32) :
    m.loadInt (arg2 t₀ + 0x27#64 + BitVec.ofNat 64 o) n
      = some (Int.ofBytes ((inv.drop o).take n)) := by
  rw [T_inv] at h; exact val_load h o n hin hl

omit [CodeEnv] in
/-- A store into the array. -/
theorem T_store_inv {m : Mem 64} {x : IArgs} {ra : Int64} {t₀ : MachineData} {inv : List UInt8}
    {i : BitVec 32} (h : m =⋆ T x ra t₀ inv i) (o n : Nat) (hin : o + n ≤ inv.length)
    (hl : inv.length < 2 ^ 32) (v : Int) :
    m.storeInt (arg2 t₀ + 0x27#64 + BitVec.ofNat 64 o) n v
      =⋆ T x ra t₀ (inv.take o ++ Int.toBytes n v ++ inv.drop (o + n)) i := by
  rw [T_inv] at h ⊢; exact val_store h o n hin hl v

/-! ## The array's values -/

omit [CodeEnv] in
theorem invfMid_length (k : Nat) (inv : List UInt8) (vals : Nat → Nat) :
    (invfMid k inv vals).length = 10 := mk_length _ _

omit [CodeEnv] in
/-- Read `k` stores its value at index `k`. -/
theorem invfMid_set (k : Nat) (hk : k < 5) (inv : List UInt8) (vals : Nat → Nat)
    (b : BitVec 8) (hb : b.toNat < 4) :
    (invfMid k inv vals).set k (UInt8.ofBitVec b)
      = invfMid (k + 1) inv (fun j => if j = k then b.toNat else vals j) := by
  rw [invfMid, mk_set, invfMid]
  congr 1; funext j
  by_cases h : j = k
  · subst h; simp only [↓reduceIte, hk, Nat.lt_succ_self]
    apply UInt8.toNat_inj.mp
    simp [UInt8.toNat_ofNat']; omega
  · simp only [h, ↓reduceIte]
    split
    · by_cases h2 : j < k
      · simp [h2, show j < k + 1 by omega]
      · simp [h2, show ¬ j < k + 1 by omega]
    · rfl

omit [CodeEnv] in
theorem T_load_i {m : Mem 64} {x : IArgs} {ra : Int64} {t₀ : MachineData} {inv : List UInt8}
    {i : BitVec 32} (h : m =⋆ T x ra t₀ inv i) :
    m.loadInt (arg1 t₀ + 8#64) 4 = some (Int.ofBytes (Int.toBytes 4 i.toInt)) := by
  rw [T_i] at h; exact loadInt_sep _ _ 4 _ m h (Int.toBytes_length 4 _) (by omega)

omit [CodeEnv] in
theorem T_load_p8 {m : Mem 64} {x : IArgs} {ra : Int64} {t₀ : MachineData} {inv : List UInt8}
    {i : BitVec 32} (h : m =⋆ T x ra t₀ inv i) :
    m.loadInt (arg1 t₀ + 0x10#64) 4 = some (Int.ofBytes (Int.toBytes 4 x.p8.toInt)) := by
  rw [show T x ra t₀ inv i = cell4 (arg1 t₀ + 0x10#64) x.p8 ⋆ (c4 (arg0 t₀ + 0x4c1e8#64) x.nq
      ⋆ (InvB (arg2 t₀) inv ⋆ ((Int.toBytes 8 x.buf.toInt =@ arg1 t₀ ⋆ (cell4 (arg1 t₀ + 8#64) i
      ⋆ 4 ?@ (arg1 t₀ + 0xc#64))) ⋆ (Blocks [(x.buf, x.L)] ⋆ Rest x.R ra t₀)))) by
        simp only [T, GbW]; ac_rfl] at h
  exact loadInt_sep _ _ 4 _ m h (Int.toBytes_length 4 _) (by omega)

omit [CodeEnv] in
theorem T_load_buf {m : Mem 64} {x : IArgs} {ra : Int64} {t₀ : MachineData} {inv : List UInt8}
    {i : BitVec 32} (h : m =⋆ T x ra t₀ inv i) :
    m.loadInt (arg1 t₀) 8 = some (Int.ofBytes (Int.toBytes 8 x.buf.toInt)) := by
  rw [show T x ra t₀ inv i = (Int.toBytes 8 x.buf.toInt =@ arg1 t₀) ⋆ (c4 (arg0 t₀ + 0x4c1e8#64) x.nq
      ⋆ (InvB (arg2 t₀) inv ⋆ ((cell4 (arg1 t₀ + 8#64) i ⋆ (4 ?@ (arg1 t₀ + 0xc#64)
      ⋆ cell4 (arg1 t₀ + 0x10#64) x.p8)) ⋆ (Blocks [(x.buf, x.L)] ⋆ Rest x.R ra t₀)))) by
        simp only [T, GbW]; ac_rfl] at h
  exact loadInt_sep _ _ 8 _ m h (Int.toBytes_length 8 _) (by omega)

/-! ## One read -/

omit [CodeEnv] in
theorem invfMid0 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : UInt8) (vals : Nat → Nat) :
    invfMid 0 [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9] vals
      = [a0, a1, a2, a3, a4, a0, a1, a2, a3, a4] := by
  simp [invfMid, mk, List.range_succ]

omit [CodeEnv] in
/-- `cmpl $c` on `n_q`: the zero flag. -/
theorem nq_z (nq c : Nat) (h : nq ≤ 5) (hc : c ≤ 5) :
    ((BitVec.ofInt 32 (nq : Int) - BitVec.setWidth 32 (BitVec.ofNat 64 c) == BitVec.zero 32) = true)
      ↔ nq = c := by
  simp only [beq_iff_eq, BitVec.ofInt_natCast]
  constructor
  · intro e; have := congrArg BitVec.toNat e; simp [BitVec.toNat_sub] at this; omega
  · rintro rfl; simp

omit [CodeEnv] in
/-- `cmpl $c` on `n_q`: `jbe`. -/
theorem nq_le (nq c : Nat) (h : nq ≤ 5) (hc : c ≤ 5) :
    ((decide ((BitVec.ofInt 32 (nq : Int)).toNat < (BitVec.ofNat 32 c).toNat)
      || BitVec.ofInt 32 (nq : Int) - BitVec.ofNat 32 c == BitVec.zero 32) = true) ↔ nq ≤ c := by
  simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, BitVec.ofInt_natCast, BitVec.toNat_ofNat]
  constructor
  · rintro (e | e)
    · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at e; omega
    · have := congrArg BitVec.toNat e; simp [BitVec.toNat_sub] at this; omega
  · intro e
    rcases Nat.lt_or_eq_of_le e with e | rfl
    · left; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
    · right; simp

omit [CodeEnv] in
/-- `cmpl $c` on `n_q`: `jb`. -/
theorem nq_lt (nq c : Nat) (h : nq ≤ 5) (hc : c ≤ 5) :
    (decide ((BitVec.ofInt 32 (nq : Int)).toNat < (BitVec.ofNat 32 c).toNat) = true) ↔ nq < c := by
  simp only [decide_eq_true_eq, BitVec.ofInt_natCast, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

omit [CodeEnv] in
/-- `cmpl $c` on `n_q`: `ja`, not taken when `n_q ≤ c`. -/
theorem nq_ja (nq c : Nat) (h : nq ≤ c) (hc : c ≤ 5) :
    (!decide ((BitVec.ofInt 32 (nq : Int)).toNat < (BitVec.ofNat 32 c).toNat)
      && !(BitVec.ofInt 32 (nq : Int) - BitVec.ofNat 32 c == BitVec.zero 32)) = false := by
  rcases Nat.lt_or_eq_of_le h with e | rfl
  · rw [(nq_lt nq c (by omega) hc).mpr e]; rfl
  · simp

omit [CodeEnv] in
/-- The 2-bit field. -/
theorem b30_lt (w : BitVec 64) :
    (BitVec.setWidth 8 ((BitVec.setWidth 32 w).ushiftRight 30)).toNat < 4 := by
  have := shr30_lt (BitVec.setWidth 32 w)
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; exact this

omit [CodeEnv] in
/-- One read: the index store and the byte store at `0x27 + k`. -/
theorem invf_step {m : Mem 64} {x : IArgs} {ra : Int64} {t₀ : MachineData} {k : Nat}
    {vals : Nat → Nat} {i : BitVec 32} (hm : m =⋆ T x ra t₀ (invfMid k x.inv vals) i)
    (hk : k < 5) (i' : BitVec 32) (b : BitVec 8) (hb : b.toNat < 4) :
    (m.storeInt (arg1 t₀ + 8#64) 4 i'.toInt).storeInt (arg2 t₀ + BitVec.ofNat 64 (0x27 + k)) 1 b.toInt
      =⋆ T x ra t₀ (invfMid (k + 1) x.inv (fun j => if j = k then b.toNat else vals j)) i' := by
  have h := T_store_inv (T_storeI hm i') k 1 (by simp [invfMid_length]; omega)
    (by simp [invfMid_length]) b.toInt
  rw [slice1_set _ _ _ (by simp [invfMid_length]; omega), BitVec.ofInt_toInt,
    invfMid_set k hk _ _ b hb, BitVec.add_assoc, ← BitVec.ofNat_add] at h
  exact h

omit [CodeEnv] in
/-- The last read (`n_q = k + 1`). -/
theorem invf_step_fin {m : Mem 64} {x : IArgs} {ra : Int64} {t₀ : MachineData} {k : Nat}
    {vals : Nat → Nat} {i : BitVec 32} (hm : m =⋆ T x ra t₀ (invfMid k x.inv vals) i)
    (hk : k < 5) (hq : x.nq = k + 1) (i' : BitVec 32) (b : BitVec 8) (hb : b.toNat < 4) :
    (m.storeInt (arg1 t₀ + 8#64) 4 i'.toInt).storeInt (arg2 t₀ + BitVec.ofNat 64 (0x27 + k)) 1 b.toInt
      =⋆ T x ra t₀ (invfMid x.nq x.inv (fun j => if j = k then b.toNat else vals j)) i' := by
  rw [show invfMid x.nq x.inv _ = invfMid (k + 1) x.inv _ by rw [hq]]
  exact invf_step hm hk i' b hb

end Kraken.Examples.Sbr.Invf
