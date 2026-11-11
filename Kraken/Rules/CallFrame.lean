import Kraken.SysV
import Kraken.SepCells

/-!
# Calling a procedure on part of the caller's memory

A procedure's contract (`CallPre need (F t ⋆ R)` / `CallPost need (F t ⋆ R)`,
the form of every `ProcSpec` under `Kraken.SysV`) names the exact blocks the
callee touches: `Blocks [(arg0 t, 256), …]`. A caller seldom owns those blocks
as cells of its own: it owns a larger array the argument points into
(`v0[2304]` for `v = v0 + v_off`), and it may call with more stack than the
callee needs. Carving the callee's blocks out of the caller's tree at every
call site, and gluing them back after it, is a separation-logic chore the
`grind` cell rules do not do (they match a block only at its exact base).

`ProcSpec.widen` turns a contract into one that takes a *container* `G` (any
part of the caller's memory, typically a whole subtree of its invariant) with
a proof that `G` is the callee's footprint `F t` next to some leftover `H`,
and any reservation `k ≥ need`. The caller then passes `(G, R')` with `G` and
`R'` subtrees of its own memory fact, so the memory side of the call is a
reassociation, and the carving is the pure equation `G = F t ⋆ H`, proved once
per call shape with `Block.carve`/`Block.carve2`.
-/

open Kraken Kraken.SysV Mem Std.ExtHashMap

namespace Mem

/-- The `n` bytes at `b` inside the `len` bytes at `a`: the block is the inner
block, the part before it and the part after it. -/
theorem Block.carve {a b : BitVec 64} {len n : Nat} (h : (b - a).toNat + n ≤ len)
    (hw : len ≤ 2 ^ 64) :
    len ?@ a = n ?@ b ⋆ ((b - a).toNat ?@ a ⋆ (len - (b - a).toNat - n) ?@ (b + .ofNat 64 n)) := by
  have e1 : a + BitVec.ofNat 64 (b - a).toNat = b := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega
  rw [Block.split_at a len (b - a).toNat (by omega) hw, e1,
    Block.split_at b (len - (b - a).toNat) n (by omega) (by omega)]
  rw [show len - (b - a).toNat - n = len - (b - a).toNat - n from rfl]
  ac_rfl

/-- `carve` with the leftover existential. -/
theorem Block.carve_ex {a b : BitVec 64} {len n : Nat} (h : (b - a).toNat + n ≤ len)
    (hw : len ≤ 2 ^ 64) : ∃ H, len ?@ a = n ?@ b ⋆ H :=
  ⟨_, Block.carve h hw⟩

/-- Two disjoint blocks inside one, the first below the second. -/
theorem Block.carve2_ex {a b₁ b₂ : BitVec 64} {len n₁ n₂ : Nat}
    (h₁ : (b₁ - a).toNat + n₁ ≤ (b₂ - a).toNat) (h₂ : (b₂ - a).toNat + n₂ ≤ len)
    (hw : len ≤ 2 ^ 64) : ∃ H, len ?@ a = n₁ ?@ b₁ ⋆ (n₂ ?@ b₂ ⋆ H) := by
  have hb : (b₂ - (b₁ + BitVec.ofNat 64 n₁)).toNat = (b₂ - a).toNat - (b₁ - a).toNat - n₁ := by
    have e : b₂ - (b₁ + BitVec.ofNat 64 n₁)
        = (b₂ - a) - ((b₁ - a) + BitVec.ofNat 64 n₁) := by bv_omega
    have hn : n₁ < 2 ^ 64 := by omega
    have hs : ((b₁ - a) + BitVec.ofNat 64 n₁).toNat = (b₁ - a).toNat + n₁ := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (by omega)]
    rw [e, BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hs]; omega), hs]
    omega
  have c1 := Block.carve (a := a) (b := b₁) (n := n₁) (len := len) (by omega) hw
  have c2 := Block.carve (a := b₁ + BitVec.ofNat 64 n₁) (b := b₂) (n := n₂)
    (len := len - (b₁ - a).toNat - n₁) (by omega) (by omega)
  rw [c1, c2]
  exact ⟨(b₁ - a).toNat ?@ a ⋆ ((b₂ - (b₁ + BitVec.ofNat 64 n₁)).toNat ?@ (b₁ + BitVec.ofNat 64 n₁)
    ⋆ (len - (b₁ - a).toNat - n₁ - (b₂ - (b₁ + BitVec.ofNat 64 n₁)).toNat - n₂)
      ?@ (b₂ + BitVec.ofNat 64 n₂)), by ac_rfl⟩

/-- The `call`'s push into the caller's free slot at the head of its tree:
the slot holds the stored word, the rest of the tree is untouched. Stated
directly, so that a call site with a large frame need not walk its tree. -/
theorem push_slot {m : Mem 64} {a : BitVec 64} {R : Mem 64 → Prop} (h : m =⋆ 8 ?@ a ⋆ R)
    (v : Int) : m.storeInt a 8 v =⋆ Int.toBytes 8 v =@ a ⋆ R :=
  Block.storeInt_val_at h (Split.here_block a 8 R) v

/-- `push_slot` at a reservation below the slot, the slot's address given up
to an equation (the pushed `rsp` against the address in the caller's tree). -/
theorem push_slot_res {m : Mem 64} {a b : BitVec 64} {k : Nat} {G : Mem 64 → Prop}
    (h : m =⋆ 8 ?@ b ⋆ (Kraken.SysV.Reserve k b ⋆ G)) (hab : a = b) (v : Int) :
    m.storeInt a 8 v =⋆ Int.toBytes 8 v =@ a ⋆ (Kraken.SysV.Reserve k a ⋆ G) := by
  subst hab; exact push_slot h v

/-- Bytes stored, read back as an integer, stored again: the same bytes. -/
@[grind =] theorem _root_.Int.toBytes_ofBytes_toBytes (n : Nat) (v : Int) :
    Int.toBytes n (Int.ofBytes (Int.toBytes n v)) = Int.toBytes n v := by
  rw [ofBytes_toBytes, Int.toBytes_emod]

end Mem

section Align
open Kraken

/-- An aligned address plus a multiple of the alignment (which divides
`2 ^ 64`) is aligned. -/
theorem isAligned_add {n : Nat} (hn : n ∣ 2 ^ 64) {a b : BitVec 64}
    (ha : isAligned n a = true) (hb : b.toNat % n = 0) : isAligned n (a + b) = true := by
  simp only [isAligned, beq_iff_eq] at *
  rw [BitVec.toNat_add, Nat.mod_mod_of_dvd _ hn, Nat.add_mod, ha, hb]
  simp

/-- An address a multiple of the alignment above an aligned base is aligned. -/
theorem isAligned_of_sub {n : Nat} (hn : n ∣ 2 ^ 64) {a b : BitVec 64}
    (hb : isAligned n b = true) (h : (a - b).toNat % n = 0) : isAligned n a = true := by
  have e : a = b + (a - b) := by bv_omega
  rw [e]
  exact isAligned_add hn hb h

end Align

/-- A contract in the `CallPre`/`CallPost` form, called on a container `G` of
its footprint and with `k ≥ need` bytes of stack: the leftover of `G` and the
excess stack join the caller's frame for the call. -/
theorem Kraken.Executable.ProcSpec.widen [CodeEnv] {f : Int64} {need k : Nat}
    {F : MachineData → Mem 64 → Prop} {C : MachineData → Prop}
    (h : cenv.ProcSpec f (fun R ra t => CallPre need (F t ⋆ R) ra t ∧ C t)
        (fun R ra t s => CallPost need (F t ⋆ R) ra t s))
    (hk : need ≤ k) (_hk' : k ≤ 2 ^ 64) :
    cenv.ProcSpec f
      (fun (x : (Mem 64 → Prop) × (Mem 64 → Prop)) ra t =>
        CallPre k (x.1 ⋆ x.2) ra t ∧ C t ∧ ∃ H, x.1 = F t ⋆ H)
      (fun x ra t s => CallPost k (x.1 ⋆ x.2) ra t s) := by
  rintro ⟨G, R⟩ ra t ⟨hpre, hC, H, hG⟩
  dsimp only at hG hpre ⊢
  subst hG
  have e := Reserve.excess need k (t.regs.get64 .rsp) hk (CallPre.le hpre)
  refine eventually_weaken _ _ _ _ ?_
    (h (H ⋆ ((k - need) ?@ (t.regs.get64 .rsp - .ofNat 64 k) ⋆ R)) ra t ⟨?_, hC⟩)
  · rintro st ⟨hra, h1, h2, h3, hm⟩
    refine ⟨hra, h1, h2, h3, ?_⟩
    rw [e]
    exact Mem.ac hm
  · unfold CallPre at hpre ⊢
    rw [e] at hpre
    exact Mem.ac hpre
