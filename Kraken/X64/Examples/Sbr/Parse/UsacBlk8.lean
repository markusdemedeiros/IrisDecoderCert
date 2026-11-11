import Kraken.X64.Examples.Sbr.Parse.UsacBlk7
open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse
set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true
/-! # `ff_aac_sbr_decode_usac_data`: the set-up and exits of the `bs_add_harmonic` loops

The loops read `n[1]` bits (`n[1] ≤ 48` by `Scal`); the paired body runs to `n[1] & ~1`, the last
odd bit after it. The bit facts are decided over `n[1] ≤ 48`. -/
namespace Kraken.Examples.Sbr.Usac
variable [CodeEnv]

omit [CodeEnv] in
/-- `n[1] ≤ 48` (`Scal`). -/
theorem n1_le {st : USt} (h : Fin st) : st.x.n1 ≤ 48 := h.1.1.1.2.2.2.2.2.2.2.2.1

omit [CodeEnv] in
/-- The loop set-up: `n[1] & 0x7ffffffe` is `n[1] / 2 * 2`; the counter `0` is below it. -/
theorem lp_init (st : USt) (r : BitVec 64) (hr : r = n1v st) (h2 : 2 ≤ st.x.n1)
    (h48 : st.x.n1 ≤ 48) :
    Lp st (BitVec.setWidth 64 0#32)
      (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 r))
        &&& BitVec.setWidth 32 (Int64.toBitVec 2147483646))) r := by
  subst hr
  have key : ∀ n, n ≤ 48 → 2 ≤ n →
      BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32
        (BitVec.ofNat 64 n))) &&& BitVec.setWidth 32 (Int64.toBitVec 2147483646))
        = BitVec.ofNat 64 (n / 2 * 2) ∧ (BitVec.setWidth 64 0#32).toNat % 2 = 0
      ∧ (BitVec.setWidth 64 0#32).toNat < (BitVec.ofNat 64 (n / 2 * 2)).toNat := by decide
  obtain ⟨k1, k2, k3⟩ := key _ h48 h2
  exact ⟨rfl, k1, k2, k1 ▸ k3⟩

omit [CodeEnv] in
/-- A loop rank `c + (bound - counter)` below the rank `d` of its set-up. -/
theorem vlt {c d : Nat} (b : BitVec 64) (h : c + 2 ^ 64 ≤ d) : c + b.toNat ≤ d := by
  have := b.isLt; omega

/-- The paired loop's set-up: bound `n[1] & ~1`, counter `0`. -/
theorem blk_L3ca2 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L3ca2" := by
  cfg_block
  measure_hb "L3ca2"
    intro n
    simp only [tbl_L3ca2, var_L3ca2]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨h, rfl⟩ := hs₀
    obtain ⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, ⟨hfin, hsi, hn1⟩, hm⟩, hax⟩ := h
    vcgen
    all_goals try subst_vars
    refine ⟨?_, by rw [var_L3cac]; exact vlt _ (by decide)⟩
    rw [tbl_L3cac]
    refine ⟨⟨hF, ⟨(by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact hsp),
      (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact hbp),
      (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact h12),
      (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact hbx),
      (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact h14)⟩,
      (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact h13),
      st, hI, ⟨hfin, ?_⟩, hm⟩,
      (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact hax)⟩
    simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.xor_self]
    exact lp_init st _ hsi hn1 (n1_le hfin)

/-- The first harmonic loop's set-up: bound `n[1] & ~1`, counter `0`. -/
theorem blk_L3ad4 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L3ad4" := by
  cfg_block
  measure_hb "L3ad4"
    intro n
    simp only [tbl_L3ad4, var_L3ad4]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨h, rfl⟩ := hs₀
    obtain ⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, ⟨hfin, hsi, hn1⟩, hm⟩, hax⟩ := h
    vcgen
    all_goals try subst_vars
    refine ⟨?_, by rw [var_L3ae0]; exact vlt _ (by decide)⟩
    rw [tbl_L3ae0]
    refine ⟨⟨hF, ⟨(by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact hsp),
      (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact hbp),
      (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact h12),
      (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact hbx),
      (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact h14)⟩,
      (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact h13),
      st, hI, ⟨hfin, ?_⟩, hm⟩,
      (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact hax)⟩
    simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.xor_self]
    exact lp_init st _ hsi hn1 (n1_le hfin)

/-- The single-channel loop's set-up: bound `n[1] & ~1`, counter `0`. -/
theorem blk_L3b98 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L3b98" := by
  cfg_block
  measure_hb "L3b98"
    intro n
    simp only [tbl_L3b98, var_L3b98]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨h, rfl⟩ := hs₀
    obtain ⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, ⟨hfin, hsi, hn1⟩, hm⟩ := h
    vcgen
    all_goals try subst_vars
    refine ⟨?_, by rw [var_L3ba2]; exact vlt _ (by decide)⟩
    rw [tbl_L3ba2]
    refine ⟨hF, ⟨(by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact hsp),
      (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact hbp),
      (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact h12),
      (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact hbx),
      (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact h14)⟩,
      (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact h13),
      st, hI, ⟨hfin, ?_⟩, hm⟩
    simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.xor_self]
    exact lp_init st _ hsi hn1 (n1_le hfin)

/-- The coupled loop's set-up: bound `n[1] & ~1`, counter `0`. -/
theorem blk_L3d64 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L3d64" := by
  cfg_block
  measure_hb "L3d64"
    intro n
    simp only [tbl_L3d64, var_L3d64]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨h, rfl⟩ := hs₀
    obtain ⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, ⟨hfin, hsi, hn1⟩, hm⟩ := h
    vcgen
    all_goals try subst_vars
    refine ⟨?_, by rw [var_L3d6e]; exact vlt _ (by decide)⟩
    rw [tbl_L3d6e]
    refine ⟨hF, ⟨(by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact hsp),
      (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact hbp),
      (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact h12),
      (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact hbx),
      (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact h14)⟩,
      (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact h13),
      st, hI, ⟨hfin, ?_⟩, hm⟩
    simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.xor_self]
    exact lp_init st _ hsi hn1 (n1_le hfin)

/-- `n[1] = 1`: the odd bit only, counter `0`. -/
theorem blk_L3c9b (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L3c9b" := by
  cfg_block
  measure_hb "L3c9b"
    intro n
    simp only [tbl_L3c9b, var_L3c9b]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨h, rfl⟩ := hs₀
    obtain ⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, ⟨hfin, hn1⟩, hm⟩, hax⟩ := h
    vcgen
    all_goals try subst_vars
    left; apply Table.ofLabels_at
    refine ⟨by decide, ?_, ?_⟩
    rotate_left
    · first
        | exact Or.inl (by rw [var_L3d2d]; decide)
        | exact Or.inr ⟨by rw [var_L3d2d], by decide⟩
    · rw [tbl_L3d2d]
      refine ⟨⟨hF, ⟨(by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact hsp),
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact hbp),
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact h12),
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact hbx),
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact h14)⟩,
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact h13),
      st, hI, ⟨hfin, ?_⟩, hm⟩,
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact hax)⟩
      simp only [Reg64s.get64_set64, ite_true, BitVec.xor_self]
      show (0#64).toNat + 1 = st.x.n1
      rw [hn1]; rfl

omit [CodeEnv] in
/-- `n[1]` odd (`test $1`): the counter `n[1] / 2 * 2` is `n[1] - 1`. -/
theorem lo_odd (n : Nat) (h48 : n ≤ 48)
    (h : ((BitVec.setWidth 8 (BitVec.ofNat 64 n) &&& BitVec.setWidth 8 (Int64.toBitVec 1))
      == BitVec.zero 8) = false) : (BitVec.ofNat 64 (n / 2 * 2)).toNat + 1 = n := by
  have key : ∀ n, n ≤ 48 → ((BitVec.setWidth 8 (BitVec.ofNat 64 n)
      &&& BitVec.setWidth 8 (Int64.toBitVec 1)) == BitVec.zero 8) = false
      → (BitVec.ofNat 64 (n / 2 * 2)).toNat + 1 = n := by decide
  exact key n h48 h

/-- The paired loop's exit: `n[1]` even → done; odd → the last bit. -/
theorem blk_L3d23 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L3d23" := by
  cfg_block
  measure_hb "L3d23"
    intro n
    simp only [tbl_L3d23, var_L3d23]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨h, rfl⟩ := hs₀
    obtain ⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, ⟨hfin, hsi, hdx⟩, hm⟩, hax⟩ := h
    vcgen
    all_goals try subst_vars
    case vc1 =>
      left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, Or.inl (by rw [var_L36c0]; decide)⟩
      rw [tbl_L36c0]
      exact ⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, hfin, hm⟩
    case vc2 af hs =>
      simp only [CondCode.interp_z, StatusFlags.zf_from_result, hsi] at hs
      refine ⟨?_, by rw [var_L3d2d]; decide⟩
      rw [tbl_L3d2d]
      exact ⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, ⟨hfin,
        (congrArg (·.toNat + 1) hdx).trans (lo_odd _ (n1_le hfin) hs)⟩, hm⟩, hax⟩

end Kraken.Examples.Sbr.Usac
