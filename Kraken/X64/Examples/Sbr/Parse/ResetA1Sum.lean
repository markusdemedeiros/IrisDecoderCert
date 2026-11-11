import Kraken.X64.Examples.Sbr.Parse.ResetA1Mem

/-!
# `sbr_reset`: the `stop_dk` sum (shard A1)

`L1523` .. `L15fb`: `k[2] += stop_dk[i]` for `i < bs_stop_freq`, unrolled; `k[2]` is a scratch
cell here (only the clamp at `L1622` fixes its meaning). The `ud1` after the 14th term is
unreachable: `bs_stop_freq ≤ 13` on this path.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Reset

variable [CodeEnv]

omit [CodeEnv] in
/-- `rbp + (-n)` as a subtraction (the frame addresses of `vcgen`). -/
theorem a1_noff (r : BitVec 64) (n : Nat) :
    r + (-(no_index (OfNat.ofNat n) : Int64)).toBitVec = r - BitVec.ofNat 64 n := by
  rw [Int64.toBitVec_neg, BitVec.sub_eq_add_neg]
  rfl

omit [CodeEnv] in
theorem a1_add0 (r : BitVec 64) : r + (0 : BitVec 64) = r := BitVec.add_zero r

/-- The simp set of the sum blocks (registers, frame addresses). -/
local macro "a1ss" : tactic => `(tactic| simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
  AddrIndex.offset64_none, BitVec.add_zero, a1_add0, a1_noff, Int64.toBitVec_ofNat_norm,
  BitVec.ofNat_eq_ofNat] at *)

/-- Reload `sbr`, `ac`, `bs_stop_freq`; `0` → `L1618`; else the first term(s). -/
theorem blk_L1523 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1523" ⟨"sbr_reset.L1523", B.L1523, some "sbr_reset.L1555"⟩ := by
  info_off
  measure_hb "L1523"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, hr, hsp1, ⟨hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF, ⟨h40, h30, -⟩, hm⟩⟩ :=
      T.L1523.mp hs
    clear hs
    have hl : st.sp.length = 6 := hsp ▸ hC.1
    have hlen : 1 < st.sp.length := by omega
    have ld30 := fr_load (d := 0x30) (n := 8) hm hF (by omega) (by omega)
    have ld40 := fr_load (d := 0x40) (n := 8) hm hF (by omega) (by omega)
    have ldsp : loadInt s₀.dmem (arg1 t₀ + 29#64) 1 = some (((a.sp.getD 1 0).toNat : Nat) : Int) := by
      have := a1_sp_load hm hl (i := 1) (by omega)
      rw [a1_slice_one hlen, a1_ofBytes_one, hsp] at this; exact this
    have ld70 := fr_load (d := 0x70) (n := 2) hm hF (by omega) (by omega)
    have ldk2 := a1_k2_isSome hm
    have hst := fun v => a1_k2_store hm v
    have ld6e : ∀ v : BitVec 32, ((s₀.dmem.storeInt (arg1 t₀ + 0x48#64) 4 v.toInt).loadInt
        (s₀.regs.get64 .rbp - BitVec.ofNat 64 0x6e) 2).isSome = true := fun v => by
      rw [hrbp, fr_load (d := 0x6e) (n := 2) (a1_k2_store hm v) hF (by omega) (by omega)]; rfl
    have hP : PLift (frSlot64 fr 0x40 = arg0 t₀ ∧ frSlot64 fr 0x30 = arg1 t₀) := ⟨⟨h40, h30⟩⟩
    have hv30 : BitVec.ofInt 64 (Int.ofBytes (slice fr (1392 - 0x30) 8)) = arg1 t₀ := h30
    have hv40 : BitVec.ofInt 64 (Int.ofBytes (slice fr (1392 - 0x40) 8)) = arg0 t₀ := h40
    rw [← hrbp] at ld30 ld40 ld70
    simp only [B.L1523]
    vcgen
    all_goals try subst s₀
    all_goals try subst n
    all_goals try a1ss
    all_goals try simp only [ld30, ld40, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [hv30, hv40, ldsp, ld70, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [ldk2, Option.isSome_some, a1_zx_byte]
    all_goals try generalize Int.ofBytes (slice fr (1392 - 112) 2) = w70 at *
    · refine Or.inl (Table.ofLabels_at ⟨S.L1618, T.L1618.mpr ⟨row, hr, ⟨hC, hBO, ⟨?_, ?_⟩, st, fr,
        hx, hsp, hfm, hF, trivial, hm⟩, ?_, ?_⟩, by edge_step⟩)
      all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp]
    · refine Or.inl (Table.ofLabels_at ⟨S.L1622, ?_, by left; var_step⟩)
      refine T.L1622.mpr ⟨row, hr, ⟨hC, hBO, ⟨?_, ?_⟩, { st with k2 := ?_ }, fr, hx, hsp, hfm, hF,
        trivial, ?_⟩, ?_, ?_⟩
      all_goals try (simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp]; done)
      all_goals try (dsimp only; with_reducible exact hst _)
    · exact ld6e _
    · refine ⟨T.L1555.mpr ?_, by var_step⟩
      refine ⟨⟨row, hr, hsp1, hC, hBO, ⟨?_, ?_⟩, { st with k2 := ?_ }, fr, hx, hsp,
        hfm, hF, ⟨hP.down.1, hP.down.2, trivial⟩, ?_⟩, ?_, ?_, ?_⟩
      all_goals try (simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp]; done)
      all_goals try rfl
      all_goals try (dsimp only; with_reducible exact hst _)

/-- `k[2] += stop_dk[2]` (if `3 ≤ bs_stop_freq`), `k[2] += stop_dk[3]` (if `3 < bs_stop_freq`). -/
theorem blk_L1555 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1555" ⟨"sbr_reset.L1555", B.L1555, some "sbr_reset.L157b"⟩ := by
  info_off
  measure_hb "L1555"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨⟨row, hr, hsp1, ⟨hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF, ⟨h40, h30, -⟩, hm⟩⟩,
      h12, h15, hax⟩ := T.L1555.mp hs
    clear hs
    have hst := fun v => a1_k2_store hm v
    have hst2 : ∀ v w : BitVec 32, Mm k e a ra t₀ { st with k2 := w } fr
        ((s₀.dmem.storeInt (arg1 t₀ + 0x48#64) 4 v.toInt).storeInt (arg1 t₀ + 0x48#64) 4 w.toInt) :=
      fun v w => a1_k2_store (a1_k2_store hm v) w
    have ldA : ∀ v : BitVec 32, ((s₀.dmem.storeInt (arg1 t₀ + 0x48#64) 4 v.toInt).loadInt
        (s₀.regs.get64 .rbp - BitVec.ofNat 64 0x6c) 2).isSome = true := fun v => by
      rw [hrbp, fr_load (d := 0x6c) (n := 2) (a1_k2_store hm v) hF (by omega) (by omega)]; rfl
    have ldB : ∀ v w : BitVec 32, (((s₀.dmem.storeInt (arg1 t₀ + 0x48#64) 4 v.toInt).storeInt
        (arg1 t₀ + 0x48#64) 4 w.toInt).loadInt (s₀.regs.get64 .rbp - BitVec.ofNat 64 0x6a) 2).isSome
        = true := fun v w => by
      rw [hrbp, fr_load (d := 0x6a) (n := 2) (a1_k2_store (a1_k2_store hm v) w) hF (by omega)
        (by omega)]; rfl
    have hP : PLift (frSlot64 fr 0x40 = arg0 t₀ ∧ frSlot64 fr 0x30 = arg1 t₀) := ⟨⟨h40, h30⟩⟩
    simp only [B.L1555]
    vcgen
    all_goals try subst s₀
    all_goals try subst n
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
      BitVec.add_zero, a1_add0, a1_noff, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, h12]
    all_goals first
      | (with_reducible exact a1_k2_isSome hm)
      | (with_reducible exact a1_k2_isSome (hst _))
      | (with_reducible exact ldA _)
      | (with_reducible exact ldB _ _)
      | (refine Or.inl (Table.ofLabels_at ⟨S.L1622, ?_, by left; var_step⟩)
         refine T.L1622.mpr ⟨row, hr, ⟨hC, hBO, ⟨?_, ?_⟩, { st with k2 := ?_ }, fr, hx, hsp, hfm,
           hF, trivial, ?_⟩, ?_, ?_⟩
         all_goals try (simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15]; done)
         all_goals try (dsimp only; with_reducible exact hst _)
         all_goals try (dsimp only; with_reducible exact hst2 _ _)
         done)
      | (refine ⟨T.L157b.mpr ?_, by var_step⟩
         refine ⟨⟨row, hr, hsp1, hC, hBO, ⟨?_, ?_⟩, { st with k2 := ?_ }, fr, hx, hsp,
           hfm, hF, ⟨hP.down.1, hP.down.2, trivial⟩, ?_⟩, ?_, ?_, ?_⟩
         all_goals try (simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15, hax]; done)
         all_goals try rfl
         all_goals try (dsimp only; with_reducible exact hst2 _ _)
         done)

/-- `k[2] += stop_dk[4]` (if `5 ≤ bs_stop_freq`), `k[2] += stop_dk[5]` (if `5 < bs_stop_freq`). -/
theorem blk_L157b (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L157b" ⟨"sbr_reset.L157b", B.L157b, some "sbr_reset.L15a1"⟩ := by
  info_off
  measure_hb "L157b"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨⟨row, hr, hsp1, ⟨hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF, ⟨h40, h30, -⟩, hm⟩⟩,
      h12, h15, hax⟩ := T.L157b.mp hs
    clear hs
    have hst := fun v => a1_k2_store hm v
    have hst2 : ∀ v w : BitVec 32, Mm k e a ra t₀ { st with k2 := w } fr
        ((s₀.dmem.storeInt (arg1 t₀ + 0x48#64) 4 v.toInt).storeInt (arg1 t₀ + 0x48#64) 4 w.toInt) :=
      fun v w => a1_k2_store (a1_k2_store hm v) w
    have ldA : ∀ v : BitVec 32, ((s₀.dmem.storeInt (arg1 t₀ + 0x48#64) 4 v.toInt).loadInt
        (s₀.regs.get64 .rbp - BitVec.ofNat 64 0x68) 2).isSome = true := fun v => by
      rw [hrbp, fr_load (d := 0x68) (n := 2) (a1_k2_store hm v) hF (by omega) (by omega)]; rfl
    have ldB : ∀ v w : BitVec 32, (((s₀.dmem.storeInt (arg1 t₀ + 0x48#64) 4 v.toInt).storeInt
        (arg1 t₀ + 0x48#64) 4 w.toInt).loadInt (s₀.regs.get64 .rbp - BitVec.ofNat 64 0x66) 2).isSome
        = true := fun v w => by
      rw [hrbp, fr_load (d := 0x66) (n := 2) (a1_k2_store (a1_k2_store hm v) w) hF (by omega)
        (by omega)]; rfl
    have hP : PLift (frSlot64 fr 0x40 = arg0 t₀ ∧ frSlot64 fr 0x30 = arg1 t₀) := ⟨⟨h40, h30⟩⟩
    simp only [B.L157b]
    vcgen
    all_goals try subst s₀
    all_goals try subst n
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
      BitVec.add_zero, a1_add0, a1_noff, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, h12]
    all_goals first
      | (with_reducible exact a1_k2_isSome hm)
      | (with_reducible exact a1_k2_isSome (hst _))
      | (with_reducible exact ldA _)
      | (with_reducible exact ldB _ _)
      | (refine Or.inl (Table.ofLabels_at ⟨S.L1622, ?_, by left; var_step⟩)
         refine T.L1622.mpr ⟨row, hr, ⟨hC, hBO, ⟨?_, ?_⟩, { st with k2 := ?_ }, fr, hx, hsp, hfm,
           hF, trivial, ?_⟩, ?_, ?_⟩
         all_goals try (simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15]; done)
         all_goals try (dsimp only; with_reducible exact hst _)
         all_goals try (dsimp only; with_reducible exact hst2 _ _)
         done)
      | (refine ⟨T.L15a1.mpr ?_, by var_step⟩
         refine ⟨⟨row, hr, hsp1, hC, hBO, ⟨?_, ?_⟩, { st with k2 := ?_ }, fr, hx, hsp,
           hfm, hF, ⟨hP.down.1, hP.down.2, trivial⟩, ?_⟩, ?_, ?_, ?_⟩
         all_goals try (simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15, hax]; done)
         all_goals try rfl
         all_goals try (dsimp only; with_reducible exact hst2 _ _)
         done)

/-- `k[2] += stop_dk[6]` (if `7 ≤ bs_stop_freq`), `k[2] += stop_dk[7]` (if `7 < bs_stop_freq`). -/
theorem blk_L15a1 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L15a1" ⟨"sbr_reset.L15a1", B.L15a1, some "sbr_reset.L15bf"⟩ := by
  info_off
  measure_hb "L15a1"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨⟨row, hr, hsp1, ⟨hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF, ⟨h40, h30, -⟩, hm⟩⟩,
      h12, h15, hax⟩ := T.L15a1.mp hs
    clear hs
    have hst := fun v => a1_k2_store hm v
    have hst2 : ∀ v w : BitVec 32, Mm k e a ra t₀ { st with k2 := w } fr
        ((s₀.dmem.storeInt (arg1 t₀ + 0x48#64) 4 v.toInt).storeInt (arg1 t₀ + 0x48#64) 4 w.toInt) :=
      fun v w => a1_k2_store (a1_k2_store hm v) w
    have ldA : ∀ v : BitVec 32, ((s₀.dmem.storeInt (arg1 t₀ + 0x48#64) 4 v.toInt).loadInt
        (s₀.regs.get64 .rbp - BitVec.ofNat 64 0x64) 2).isSome = true := fun v => by
      rw [hrbp, fr_load (d := 0x64) (n := 2) (a1_k2_store hm v) hF (by omega) (by omega)]; rfl
    have ldB : ∀ v w : BitVec 32, (((s₀.dmem.storeInt (arg1 t₀ + 0x48#64) 4 v.toInt).storeInt
        (arg1 t₀ + 0x48#64) 4 w.toInt).loadInt (s₀.regs.get64 .rbp - BitVec.ofNat 64 0x62) 2).isSome
        = true := fun v w => by
      rw [hrbp, fr_load (d := 0x62) (n := 2) (a1_k2_store (a1_k2_store hm v) w) hF (by omega)
        (by omega)]; rfl
    have hP : PLift (frSlot64 fr 0x40 = arg0 t₀ ∧ frSlot64 fr 0x30 = arg1 t₀) := ⟨⟨h40, h30⟩⟩
    simp only [B.L15a1]
    vcgen
    all_goals try subst s₀
    all_goals try subst n
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
      BitVec.add_zero, a1_add0, a1_noff, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, h12]
    all_goals first
      | (with_reducible exact a1_k2_isSome hm)
      | (with_reducible exact a1_k2_isSome (hst _))
      | (with_reducible exact ldA _)
      | (with_reducible exact ldB _ _)
      | (refine Or.inl (Table.ofLabels_at ⟨S.L1622, ?_, by left; var_step⟩)
         refine T.L1622.mpr ⟨row, hr, ⟨hC, hBO, ⟨?_, ?_⟩, { st with k2 := ?_ }, fr, hx, hsp, hfm,
           hF, trivial, ?_⟩, ?_, ?_⟩
         all_goals try (simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15]; done)
         all_goals try (dsimp only; with_reducible exact hst _)
         all_goals try (dsimp only; with_reducible exact hst2 _ _)
         done)
      | (refine ⟨T.L15bf.mpr ?_, by var_step⟩
         refine ⟨⟨row, hr, hsp1, hC, hBO, ⟨?_, ?_⟩, { st with k2 := ?_ }, fr, hx, hsp,
           hfm, hF, ⟨hP.down.1, hP.down.2, trivial⟩, ?_⟩, ?_, ?_, ?_⟩
         all_goals try (simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15, hax]; done)
         all_goals try rfl
         all_goals try (dsimp only; with_reducible exact hst2 _ _)
         done)

/-- `k[2] += stop_dk[8]` (if `9 ≤ bs_stop_freq`), `k[2] += stop_dk[9]` (if `9 < bs_stop_freq`). -/
theorem blk_L15bf (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L15bf" ⟨"sbr_reset.L15bf", B.L15bf, some "sbr_reset.L15dd"⟩ := by
  info_off
  measure_hb "L15bf"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨⟨row, hr, hsp1, ⟨hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF, ⟨h40, h30, -⟩, hm⟩⟩,
      h12, h15, hax⟩ := T.L15bf.mp hs
    clear hs
    have hst := fun v => a1_k2_store hm v
    have hst2 : ∀ v w : BitVec 32, Mm k e a ra t₀ { st with k2 := w } fr
        ((s₀.dmem.storeInt (arg1 t₀ + 0x48#64) 4 v.toInt).storeInt (arg1 t₀ + 0x48#64) 4 w.toInt) :=
      fun v w => a1_k2_store (a1_k2_store hm v) w
    have ldA : ∀ v : BitVec 32, ((s₀.dmem.storeInt (arg1 t₀ + 0x48#64) 4 v.toInt).loadInt
        (s₀.regs.get64 .rbp - BitVec.ofNat 64 0x60) 2).isSome = true := fun v => by
      rw [hrbp, fr_load (d := 0x60) (n := 2) (a1_k2_store hm v) hF (by omega) (by omega)]; rfl
    have ldB : ∀ v w : BitVec 32, (((s₀.dmem.storeInt (arg1 t₀ + 0x48#64) 4 v.toInt).storeInt
        (arg1 t₀ + 0x48#64) 4 w.toInt).loadInt (s₀.regs.get64 .rbp - BitVec.ofNat 64 0x5e) 2).isSome
        = true := fun v w => by
      rw [hrbp, fr_load (d := 0x5e) (n := 2) (a1_k2_store (a1_k2_store hm v) w) hF (by omega)
        (by omega)]; rfl
    have hP : PLift (frSlot64 fr 0x40 = arg0 t₀ ∧ frSlot64 fr 0x30 = arg1 t₀) := ⟨⟨h40, h30⟩⟩
    simp only [B.L15bf]
    vcgen
    all_goals try subst s₀
    all_goals try subst n
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
      BitVec.add_zero, a1_add0, a1_noff, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, h12]
    all_goals first
      | (with_reducible exact a1_k2_isSome hm)
      | (with_reducible exact a1_k2_isSome (hst _))
      | (with_reducible exact ldA _)
      | (with_reducible exact ldB _ _)
      | (refine Or.inl (Table.ofLabels_at ⟨S.L1622, ?_, by left; var_step⟩)
         refine T.L1622.mpr ⟨row, hr, ⟨hC, hBO, ⟨?_, ?_⟩, { st with k2 := ?_ }, fr, hx, hsp, hfm,
           hF, trivial, ?_⟩, ?_, ?_⟩
         all_goals try (simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15]; done)
         all_goals try (dsimp only; with_reducible exact hst _)
         all_goals try (dsimp only; with_reducible exact hst2 _ _)
         done)
      | (refine ⟨T.L15dd.mpr ?_, by var_step⟩
         refine ⟨⟨row, hr, hsp1, hC, hBO, ⟨?_, ?_⟩, { st with k2 := ?_ }, fr, hx, hsp,
           hfm, hF, ⟨hP.down.1, hP.down.2, trivial⟩, ?_⟩, ?_, ?_, ?_⟩
         all_goals try (simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15, hax]; done)
         all_goals try rfl
         all_goals try (dsimp only; with_reducible exact hst2 _ _)
         done)

/-- `k[2] += stop_dk[10]` (if `11 ≤ bs_stop_freq`), `k[2] += stop_dk[11]` (if `11 < bs_stop_freq`). -/
theorem blk_L15dd (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L15dd" ⟨"sbr_reset.L15dd", B.L15dd, some "sbr_reset.L15fb"⟩ := by
  info_off
  measure_hb "L15dd"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨⟨row, hr, hsp1, ⟨hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF, ⟨h40, h30, -⟩, hm⟩⟩,
      h12, h15, hax⟩ := T.L15dd.mp hs
    clear hs
    have hst := fun v => a1_k2_store hm v
    have hst2 : ∀ v w : BitVec 32, Mm k e a ra t₀ { st with k2 := w } fr
        ((s₀.dmem.storeInt (arg1 t₀ + 0x48#64) 4 v.toInt).storeInt (arg1 t₀ + 0x48#64) 4 w.toInt) :=
      fun v w => a1_k2_store (a1_k2_store hm v) w
    have ldA : ∀ v : BitVec 32, ((s₀.dmem.storeInt (arg1 t₀ + 0x48#64) 4 v.toInt).loadInt
        (s₀.regs.get64 .rbp - BitVec.ofNat 64 0x5c) 2).isSome = true := fun v => by
      rw [hrbp, fr_load (d := 0x5c) (n := 2) (a1_k2_store hm v) hF (by omega) (by omega)]; rfl
    have ldB : ∀ v w : BitVec 32, (((s₀.dmem.storeInt (arg1 t₀ + 0x48#64) 4 v.toInt).storeInt
        (arg1 t₀ + 0x48#64) 4 w.toInt).loadInt (s₀.regs.get64 .rbp - BitVec.ofNat 64 0x5a) 2).isSome
        = true := fun v w => by
      rw [hrbp, fr_load (d := 0x5a) (n := 2) (a1_k2_store (a1_k2_store hm v) w) hF (by omega)
        (by omega)]; rfl
    have hP : PLift (frSlot64 fr 0x40 = arg0 t₀ ∧ frSlot64 fr 0x30 = arg1 t₀) := ⟨⟨h40, h30⟩⟩
    simp only [B.L15dd]
    vcgen
    all_goals try subst s₀
    all_goals try subst n
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
      BitVec.add_zero, a1_add0, a1_noff, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, h12]
    all_goals first
      | (with_reducible exact a1_k2_isSome hm)
      | (with_reducible exact a1_k2_isSome (hst _))
      | (with_reducible exact ldA _)
      | (with_reducible exact ldB _ _)
      | (refine Or.inl (Table.ofLabels_at ⟨S.L1622, ?_, by left; var_step⟩)
         refine T.L1622.mpr ⟨row, hr, ⟨hC, hBO, ⟨?_, ?_⟩, { st with k2 := ?_ }, fr, hx, hsp, hfm,
           hF, trivial, ?_⟩, ?_, ?_⟩
         all_goals try (simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15]; done)
         all_goals try (dsimp only; with_reducible exact hst _)
         all_goals try (dsimp only; with_reducible exact hst2 _ _)
         done)
      | (refine ⟨T.L15fb.mpr ?_, by var_step⟩
         refine ⟨⟨row, hr, hsp1, hC, hBO, ⟨?_, ?_⟩, { st with k2 := ?_ }, fr, hx, hsp,
           hfm, hF, ⟨hP.down.1, hP.down.2, trivial⟩, ?_⟩, ?_, ?_, ?_⟩
         all_goals try (simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15, hax]; done)
         all_goals try rfl
         all_goals try (dsimp only; with_reducible exact hst2 _ _)
         done)

/-- `k[2] += stop_dk[12]` (if `13 ≤ bs_stop_freq`), `k[2] += stop_dk[13]` (if `13 < bs_stop_freq`). -/
theorem blk_L15fb (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L15fb" ⟨"sbr_reset.L15fb", B.L15fb, some "sbr_reset.L1618"⟩ := by
  info_off
  measure_hb "L15fb"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨⟨row, hr, hsp1, ⟨hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF, ⟨h40, h30, -⟩, hm⟩⟩,
      h12, h15, hax⟩ := T.L15fb.mp hs
    clear hs
    have hst := fun v => a1_k2_store hm v
    have hst2 : ∀ v w : BitVec 32, Mm k e a ra t₀ { st with k2 := w } fr
        ((s₀.dmem.storeInt (arg1 t₀ + 0x48#64) 4 v.toInt).storeInt (arg1 t₀ + 0x48#64) 4 w.toInt) :=
      fun v w => a1_k2_store (a1_k2_store hm v) w
    have ldA : ∀ v : BitVec 32, ((s₀.dmem.storeInt (arg1 t₀ + 0x48#64) 4 v.toInt).loadInt
        (s₀.regs.get64 .rbp - BitVec.ofNat 64 0x58) 2).isSome = true := fun v => by
      rw [hrbp, fr_load (d := 0x58) (n := 2) (a1_k2_store hm v) hF (by omega) (by omega)]; rfl
    simp only [B.L15fb]
    vcgen
    all_goals try subst s₀
    all_goals try subst n
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
      BitVec.add_zero, a1_add0, a1_noff, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, h12]
    all_goals first
      | (with_reducible exact a1_k2_isSome hm)
      | (with_reducible exact a1_k2_isSome (hst _))
      | (with_reducible exact ldA _)
      | (refine Or.inl (Table.ofLabels_at ⟨S.L1622, ?_, by left; var_step⟩)
         refine T.L1622.mpr ⟨row, hr, ⟨hC, hBO, ⟨?_, ?_⟩, { st with k2 := ?_ }, fr, hx, hsp, hfm,
           hF, trivial, ?_⟩, ?_, ?_⟩
         all_goals try (simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15]; done)
         all_goals try (dsimp only; with_reducible exact hst _)
         all_goals try (dsimp only; with_reducible exact hst2 _ _)
         done)
      | (have hb := (a.sp.getD 1 0).toNat_lt
         simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, Int64.toBitVec_ofNat_norm,
           BitVec.ofNat_eq_ofNat, cc_c_sub, cc_z_sub, hax, u8, decide_eq_false_iff_not,
           decide_eq_true_eq, BitVec.toNat_eq, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at *
         omega)

end Kraken.Examples.Sbr.Reset
