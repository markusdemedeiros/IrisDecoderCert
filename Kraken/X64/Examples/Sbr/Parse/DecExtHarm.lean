import Kraken.X64.Examples.Sbr.Parse.DecExtSce2

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

/-!
# `ff_aac_sbr_decode_extension`: `bs_add_harmonic` of `data[0]` (single channel element)

`L43d` loads `n[1]`; `L7de`–`L85b` the loop unrolled by four (`HL`), `L898`/`L8b0` the rest.
Each element is one bit of the reader into `bs_add_harmonic[i]`, a byte of the unowned
`48 ?@ (data[0] + 0x31)` of `DataF`: the values `DS` do not change. The reader's index stays in
`eax`/`edx` (`RegI`) and is stored back at `Lb1a`.
-/

namespace Kraken.Examples.Sbr.DecExt

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

omit [CodeEnv] in
theorem sext_all : ∀ n : Nat, n < 49 →
    BitVec.signExtend 64 (BitVec.ofInt 32 (n : Int)) = BitVec.ofNat 64 n := by
  decide

omit [CodeEnv] in
theorem sext_n {n : Nat} (h : n ≤ 48) :
    BitVec.signExtend 64 (BitVec.ofInt 32 (n : Int)) = BitVec.ofNat 64 n :=
  sext_all n (by omega)

omit [CodeEnv] in
/-- `test %r9,%r9; jle` on `n ≤ 48`. -/
theorem le_all : ∀ n : Nat, n < 49 → ∀ af : Bool, CondCode.le.interp (StatusFlags.from_result
    (BitVec.ofNat 64 n &&& BitVec.ofNat 64 n) { cf := false, af := af, of := false })
    = decide (n = 0) := by
  decide

omit [CodeEnv] in
/-- `cmp $0x4,%r9d; jae` on `n ≤ 48`. -/
theorem nc_all : ∀ n : Nat, n < 49 → CondCode.nc.interp (StatusFlags.from_result
    (BitVec.setWidth 32 (BitVec.ofNat 64 n) - BitVec.setWidth 32 (Int64.toBitVec 4))
    { cf := (BitVec.setWidth 32 (BitVec.ofNat 64 n) - BitVec.setWidth 32 (Int64.toBitVec 4)).unsigned
          != (BitVec.setWidth 32 (BitVec.ofNat 64 n)).unsigned
            - (BitVec.setWidth 32 (Int64.toBitVec 4)).unsigned,
      af := ((BitVec.setWidth 32 (BitVec.ofNat 64 n) - BitVec.setWidth 32 (Int64.toBitVec 4)).take 4).unsigned
          != ((BitVec.setWidth 32 (BitVec.ofNat 64 n)).take 4).unsigned
            - ((BitVec.setWidth 32 (Int64.toBitVec 4)).take 4).unsigned,
      of := (BitVec.setWidth 32 (BitVec.ofNat 64 n) - BitVec.setWidth 32 (Int64.toBitVec 4)).signed
          != (BitVec.setWidth 32 (BitVec.ofNat 64 n)).signed
            - (BitVec.setWidth 32 (Int64.toBitVec 4)).signed })
    = decide (4 ≤ n) := by
  decide

omit [CodeEnv] in
/-- `mov %r9d,%r8d; and $0x3,%r8d` on `n ≤ 48`. -/
theorem and3_all : ∀ n : Nat, n < 49 →
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 n)))
      &&& BitVec.setWidth 32 (Int64.toBitVec 3)) = BitVec.ofNat 64 (n % 4) := by
  decide

omit [CodeEnv] in
/-- `and $0x7ffffffc,%r9d` on `n ≤ 48`. -/
theorem mask_all : ∀ n : Nat, n < 49 →
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 n) &&& BitVec.setWidth 32 (Int64.toBitVec 2147483644))
      = BitVec.ofNat 64 (n / 4 * 4) := by
  decide

omit [CodeEnv] in
/-- `test %r8,%r8; je` on `r8 = n & 3`. -/
theorem z_all : ∀ n : Nat, n < 49 → ∀ af : Bool, CondCode.z.interp (StatusFlags.from_result
    (BitVec.ofNat 64 (n % 4) &&& BitVec.ofNat 64 (n % 4)) { cf := false, af := af, of := false })
    = decide (n % 4 = 0) := by
  decide

omit [CodeEnv] in
theorem add4_toNat (r : BitVec 64) (n : Nat) (hn : n ≤ 48) (h : r.toNat + 4 ≤ n / 4 * 4) :
    (BitVec.setWidth 64 4#64 + r).toNat = r.toNat + 4 := by
  rw [BitVec.toNat_add, BitVec.setWidth_eq]; simp only [BitVec.toNat_ofNat]; omega

omit [CodeEnv] in
/-- `add $0x4,%r10; cmp %r10,%r9; jne` in the unrolled loop. -/
theorem nz_hl (r9 r10 : BitVec 64) (n : Nat) (hn : n ≤ 48) (h9 : r9 = BitVec.ofNat 64 (n / 4 * 4))
    (hb : r10.toNat + 4 ≤ n / 4 * 4) (f : StatusFlags.from_result.Remaining) :
    CondCode.nz.interp (StatusFlags.from_result (r9 - (BitVec.setWidth 64 4#64 + r10)) f)
      = decide (r10.toNat + 4 ≠ n / 4 * 4) := by
  rw [CondCode.interp_nz, StatusFlags.zf_from_result_sub]
  subst h9
  have e := add4_toNat r10 n hn hb
  have e9 : (BitVec.ofNat 64 (n / 4 * 4)).toNat = n / 4 * 4 := by
    simp only [BitVec.toNat_ofNat]; omega
  by_cases h : r10.toNat + 4 = n / 4 * 4
  · have : BitVec.ofNat 64 (n / 4 * 4) = BitVec.setWidth 64 4#64 + r10 :=
      BitVec.eq_of_toNat_eq (by omega)
    rw [this, beq_self_eq_true]; simp [h]
  · have : BitVec.ofNat 64 (n / 4 * 4) ≠ BitVec.setWidth 64 4#64 + r10 := fun hh =>
      h (by have := congrArg BitVec.toNat hh; omega)
    rw [beq_eq_false_iff_ne.mpr this]; simp [h]

omit [CodeEnv] in
theorem inc_toNat (r : BitVec 64) (h : r.toNat < 4) : (r + 1).toNat = r.toNat + 1 := by
  rw [BitVec.toNat_add]; have : (1 : BitVec 64).toNat = 1 := rfl; omega

omit [CodeEnv] in
/-- `inc %r9; cmp %r9,%r8; jne` in the rest loop. -/
theorem nz_inc (r8 r9 : BitVec 64) (h : r9.toNat < r8.toNat) (h4 : r8.toNat < 4)
    (f : StatusFlags.from_result.Remaining) :
    CondCode.nz.interp (StatusFlags.from_result (r8 - (r9 + 1)) f)
      = decide (r9.toNat + 1 ≠ r8.toNat) := by
  rw [CondCode.interp_nz, StatusFlags.zf_from_result_sub]
  have e := inc_toNat r9 (by omega)
  by_cases hh : r9.toNat + 1 = r8.toNat
  · have : r8 = r9 + 1 := BitVec.eq_of_toNat_eq (by omega)
    rw [beq_iff_eq.mpr this, Bool.not_true]; exact (decide_eq_false (by omega)).symm
  · have : r8 ≠ r9 + 1 := fun h' => hh (by have := congrArg BitVec.toNat h'; omega)
    rw [beq_eq_false_iff_ne.mpr this, Bool.not_false]; exact (decide_eq_true (by omega)).symm

set_option hygiene false in
/-- `L43d`: the loaded `n[1]` (`hx` the load, `v` its value) is the cell's value. -/
macro "ld_n1" : tactic => `(tactic| (
  have hv : v = Int.ofBytes (Int.toBytes 4 (d.a.n1 : Int)) := by
    have hmu := p_h0.down
    simp only [T, DecF, SbrF, TabF, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd] at hmu
    simp only [h14, AddrIndex.offset64_none, BitVec.add_zero, Int64.toBitVec_ofNat_norm,
      BitVec.add_assoc, BitVec.reduceAdd] at hx
    sep_vals hmu
    first | rfl | (simp only [Option.some.injEq] at hx; exact hx.symm)
  subst hv
  simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    BitVec.ofInt32_ofBytes_toBytes4, sext_n hn48] at *))

theorem blk_L43d (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L43d" := by
  cfg_block
  measure_hb "L43d"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, hE, hrb, hm⟩, hR⟩, hn⟩ := hs₀
    var_n hn
    have p_h0 : PLift _ := ⟨hm⟩
    clear hm
    have hn48 : d.a.n1 ≤ 48 := hE.1.1.1.2.2.2.2.2.2.2.2.1
    vcgen
    all_goals subst s₀
    case vc1 =>
      have hmu := p_h0.down
      simp only [DecF, SbrF, TabF, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd] at hmu
      simp only [h14, AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm,
        BitVec.add_assoc, BitVec.reduceAdd]
      sep_mem hmu
      all_goals simp [Int.toBytes_length]
    case vc2 =>
      rename_i v hx _ hc1
      ld_n1
      left; apply Table.ofLabels_at
      rw [table.match_1.eq_25]
      refine ⟨by decide, ⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, gi, d, ih, hE, hrb, p_h0.down⟩, ?_⟩, ?_⟩
      all_goals first
        | edge_ok var_Lb1a
        | (simp only [RegB, Reg64s.get64_set64, reduceCtorEq, ite_false] at hR ⊢
           all_goals first | assumption | exact hR)
    case vc3 =>
      rename_i v hx _ hc1 _ hc2
      ld_n1
      rw [le_all d.a.n1 (by omega)] at hc1
      rw [nc_all d.a.n1 (by omega)] at hc2
      simp only [decide_eq_false_iff_not, decide_eq_true_eq] at hc1 hc2
      left; apply Table.ofLabels_at
      rw [table.match_1.eq_39]
      refine ⟨by decide, ⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, gi, d, ih, ⟨hE, ?_, ?_, hc2⟩, hrb, p_h0.down⟩,
        ?_⟩, ?_⟩
      all_goals first
        | edge_ok var_L7de
        | (simp only [RegI, RegB, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
            and3_all d.a.n1 (by omega)] at hR ⊢
           all_goals first | assumption | exact hR | rfl)
    case vc4 =>
      rename_i v hx _ hc1 _ hc2 _
      ld_n1
      rw [le_all d.a.n1 (by omega)] at hc1
      rw [nc_all d.a.n1 (by omega)] at hc2
      simp only [decide_eq_false_iff_not] at hc1 hc2
      left; apply Table.ofLabels_at
      rw [table.match_1.eq_44]
      refine ⟨by decide, ⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, gi, d, ih, ⟨hE, ?_, ?_, ?_⟩, hrb, p_h0.down⟩,
        ?_⟩, ?_⟩
      all_goals first
        | edge_ok var_L898
        | (simp only [RegI, RegB, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
            and3_all d.a.n1 (by omega), BitVec.xor_self, BitVec.setWidth_zero,
            BitVec.toNat_ofNat] at hR ⊢
           all_goals first | assumption | exact hR | rfl | omega)

theorem blk_L7de (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L7de" := by
  cfg_block
  measure_hb "L7de"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, ⟨hE, h9, h8, h4⟩, hrb, hm⟩, hR⟩, hn⟩ := hs₀
    var_n hn
    have hn48 : d.a.n1 ≤ 48 := hE.1.1.1.2.2.2.2.2.2.2.2.1
    have p_h0 : PLift _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals subst s₀
    refine ⟨⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, gi, d, ih, ⟨hE, ?_⟩, hrb, p_h0.down⟩, ?_⟩, ?_⟩
    all_goals simp only [HL, RegI, var_L7e8, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      h9, h8, mask_all d.a.n1 (by omega), BitVec.xor_self, BitVec.setWidth_zero,
      BitVec.toNat_ofNat, true_and, Nat.zero_mod] at hR ⊢
    all_goals first | assumption | exact hR | omega

theorem blk_L7e8 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L7e8" := by
  cfg_block
  measure_hb "L7e8"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, ⟨hE, hL⟩, hrb, hm⟩, hR⟩, hn⟩ := hs₀
    var_n hn
    have hn48 : d.a.n1 ≤ 48 := hE.1.1.1.2.2.2.2.2.2.2.2.1
    obtain ⟨h9, h8, h10m, h10b⟩ := hL
    obtain ⟨hax, hsi, hdi⟩ := hR
    simp only [T, DecF, LocW, GbR, GbW, SbrF, DataF, sbrA, arg1, BitVec.add_assoc,
      BitVec.reduceAdd] at hm
    try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen [shl_cl32_havoc]
    all_goals have hm := p_hm.down; clear p_hm
    all_goals subst s₀
    dx_run hm [hbp, hsp, h14, hdi, BitVec.add_assoc, BitVec.reduceAdd]
    all_goals try simp only [Width.bytes, BitVec.mul_one, Nat.mul_one] at *
    all_goals try (rw [show ∀ a b : BitVec 64, a + b - a = b from fun a b => by bv_omega, sw32_64]
                   exact rd_off1 _ _ _ hax hC.2.2.2.1.2.2.1)
    all_goals try ((try simp only [Nat.zero_add]); omega)
    refine ⟨⟨⟨hC, ⟨trivial, trivial, trivial⟩, i0, gi, d, ih, ⟨hE, ?_⟩, hrb, ?_⟩, ?_⟩, ?_⟩
    · simp only [HL, Reg64s.get64_set64, reduceCtorEq, ite_false]
      exact ⟨h9, h8, h10m, h10b⟩
    · simp only [DecF, SbrF, DataF, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd]
      sep_close hm
    · simp only [RegI, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, sw32_64]
      refine ⟨?_, hsi, hdi⟩
      rw [← hsi]
      exact setl_inc _ _ _ _ _ (hsi ▸ hax) (hsi ▸ hC.2.2.2.1.2.1)
    · simp only [var_L80e, Reg64s.get64_set64, reduceCtorEq, ite_false, Nat.le_refl]

theorem blk_L80e (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L80e" := by
  cfg_block
  measure_hb "L80e"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, ⟨hE, hL⟩, hrb, hm⟩, hR⟩, hn⟩ := hs₀
    var_n hn
    have hn48 : d.a.n1 ≤ 48 := hE.1.1.1.2.2.2.2.2.2.2.2.1
    obtain ⟨h9, h8, h10m, h10b⟩ := hL
    obtain ⟨hdx, hsi, hdi⟩ := hR
    simp only [T, DecF, LocW, GbR, GbW, SbrF, DataF, sbrA, arg1, BitVec.add_assoc,
      BitVec.reduceAdd] at hm
    try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen [shl_cl32_havoc]
    all_goals have hm := p_hm.down; clear p_hm
    all_goals subst s₀
    dx_run hm [hbp, hsp, h14, hdi, BitVec.add_assoc, BitVec.reduceAdd]
    all_goals try simp only [Width.bytes, BitVec.mul_one, Nat.mul_one] at *
    all_goals try (rw [show ∀ a b : BitVec 64, a + b - a = b from fun a b => by bv_omega, sw32_64]
                   exact rd_off1 _ _ _ hdx hC.2.2.2.1.2.2.1)
    all_goals try ((try simp only [Nat.zero_add]); omega)
    refine ⟨⟨⟨hC, ⟨trivial, trivial, trivial⟩, i0, gi, d, ih, ⟨hE, ?_⟩, hrb, ?_⟩, ?_⟩, ?_⟩
    · simp only [HL, Reg64s.get64_set64, reduceCtorEq, ite_false]
      exact ⟨h9, h8, h10m, h10b⟩
    · simp only [DecF, SbrF, DataF, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd]
      sep_close hm
    · simp only [RegI, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, sw32_64]
      refine ⟨?_, hsi, hdi⟩
      rw [← hsi]
      exact setl_inc _ _ _ _ _ (hsi ▸ hdx) (hsi ▸ hC.2.2.2.1.2.1)
    · simp only [var_L835, Reg64s.get64_set64, reduceCtorEq, ite_false, Nat.le_refl]

theorem blk_L835 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L835" := by
  cfg_block
  measure_hb "L835"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, ⟨hE, hL⟩, hrb, hm⟩, hR⟩, hn⟩ := hs₀
    var_n hn
    have hn48 : d.a.n1 ≤ 48 := hE.1.1.1.2.2.2.2.2.2.2.2.1
    obtain ⟨h9, h8, h10m, h10b⟩ := hL
    obtain ⟨hax, hsi, hdi⟩ := hR
    simp only [T, DecF, LocW, GbR, GbW, SbrF, DataF, sbrA, arg1, BitVec.add_assoc,
      BitVec.reduceAdd] at hm
    try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen [shl_cl32_havoc]
    all_goals have hm := p_hm.down; clear p_hm
    all_goals subst s₀
    dx_run hm [hbp, hsp, h14, hdi, BitVec.add_assoc, BitVec.reduceAdd]
    all_goals try simp only [Width.bytes, BitVec.mul_one, Nat.mul_one] at *
    all_goals try (rw [show ∀ a b : BitVec 64, a + b - a = b from fun a b => by bv_omega, sw32_64]
                   exact rd_off1 _ _ _ hax hC.2.2.2.1.2.2.1)
    all_goals try ((try simp only [Nat.zero_add]); omega)
    refine ⟨⟨⟨hC, ⟨trivial, trivial, trivial⟩, i0, gi, d, ih, ⟨hE, ?_⟩, hrb, ?_⟩, ?_⟩, ?_⟩
    · simp only [HL, Reg64s.get64_set64, reduceCtorEq, ite_false]
      exact ⟨h9, h8, h10m, h10b⟩
    · simp only [DecF, SbrF, DataF, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd]
      sep_close hm
    · simp only [RegI, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, sw32_64]
      refine ⟨?_, hsi, hdi⟩
      rw [← hsi]
      exact setl_inc _ _ _ _ _ (hsi ▸ hax) (hsi ▸ hC.2.2.2.1.2.1)
    · simp only [var_L85b, Reg64s.get64_set64, reduceCtorEq, ite_false, Nat.le_refl]

theorem blk_L85b (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L85b" := by
  cfg_block
  measure_hb "L85b"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, ⟨hE, hL⟩, hrb, hm⟩, hR⟩, hn⟩ := hs₀
    var_n hn
    have hn48 : d.a.n1 ≤ 48 := hE.1.1.1.2.2.2.2.2.2.2.2.1
    obtain ⟨h9, h8, h10m, h10b⟩ := hL
    obtain ⟨hdx, hsi, hdi⟩ := hR
    simp only [T, DecF, LocW, GbR, GbW, SbrF, DataF, sbrA, arg1, BitVec.add_assoc,
      BitVec.reduceAdd] at hm
    try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen [shl_cl32_havoc]
    all_goals subst s₀
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, Int64.toBitVec_ofNat_norm,
      BitVec.reduceToNat, Nat.reduceMod, ite_true, ite_false] at *
    case' vc3 => left; apply Table.ofLabels_at; rw [table.match_1.eq_40]
    case' vc4 => left; apply Table.ofLabels_at; rw [table.match_1.eq_25]
    all_goals have hm := p_hm.down; clear p_hm
    dx_run hm [hbp, hsp, h14, hdi, BitVec.add_assoc, BitVec.reduceAdd]
    all_goals try simp only [Width.bytes, BitVec.mul_one, Nat.mul_one] at *
    all_goals try (rw [show ∀ a b : BitVec 64, a + b - a = b from fun a b => by bv_omega, sw32_64]
                   exact rd_off1 _ _ _ hdx hC.2.2.2.1.2.2.1)
    all_goals try ((try simp only [Nat.zero_add]); omega)
    case vc3 =>
      rename_i hnz _
      rw [nz_hl _ _ _ hn48 h9 h10b] at hnz
      simp only [ne_eq, decide_eq_true_eq] at hnz
      have e := add4_toNat _ _ hn48 h10b
      refine ⟨by decide, ⟨⟨hC, ⟨trivial, trivial, trivial⟩, i0, gi, d, ih, ⟨hE, ?_⟩, hrb, ?_⟩, ?_⟩, ?_⟩
      · simp only [HL, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, e]
        exact ⟨h9, h8, by omega, by omega⟩
      · simp only [DecF, SbrF, DataF, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd]
        sep_close hm
      · simp only [RegI, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, sw32_64]
        refine ⟨?_, hsi, hdi⟩
        rw [← hsi]
        exact setl_inc _ _ _ _ _ (hsi ▸ hdx) (hsi ▸ hC.2.2.2.1.2.1)
      · left
        simp only [var_L7e8, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, e, h9,
          BitVec.toNat_ofNat]
        omega
    case vc4 =>
      rename_i hnz hz _
      rw [h8, z_all _ (by omega)] at hz
      refine ⟨by decide, ⟨⟨hC, ⟨trivial, trivial, trivial⟩, i0, gi, d, ih, hE, hrb, ?_⟩, ?_⟩, ?_⟩
      · simp only [DecF, SbrF, DataF, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd]
        sep_close hm
      · simp only [RegB, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, sw32_64]
        refine ⟨?_, hsi, hdi⟩
        rw [← hsi]
        exact setl_inc _ _ _ _ _ (hsi ▸ hdx) (hsi ▸ hC.2.2.2.1.2.1)
      · rw [var_Lb1a]; exact Or.inl (by omega)
    case vc5 =>
      rename_i hnz hz _
      rw [h8, z_all _ (by omega)] at hz
      rw [nz_hl _ _ _ hn48 h9 h10b] at hnz
      simp only [ne_eq, decide_eq_false_iff_not, Decidable.not_not] at hnz hz
      have e := add4_toNat _ _ hn48 h10b
      refine ⟨⟨⟨hC, ⟨trivial, trivial, trivial⟩, i0, gi, d, ih, ⟨hE, ?_⟩, hrb, ?_⟩, ?_⟩, ?_⟩
      · simp only [e, h8, BitVec.toNat_ofNat]
        omega
      · simp only [DecF, SbrF, DataF, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd]
        sep_close hm
      · simp only [RegI, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, sw32_64]
        refine ⟨?_, hsi, hdi⟩
        rw [← hsi]
        exact setl_inc _ _ _ _ _ (hsi ▸ hdx) (hsi ▸ hC.2.2.2.1.2.1)
      · simp only [var_L898]; omega

omit [CodeEnv] in
theorem rdx_b (a r : BitVec 64) :
    BitVec.setWidth 64 166353#64 + (r + a * BitVec.ofNat 64 Width.W8.bytes + 0#64)
      = a + 166176#64 + 177#64 + BitVec.ofNat 64 r.toNat := by
  simp only [Width.bytes, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_zero]
  bv_omega

theorem blk_L898 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L898" := by
  cfg_block
  measure_hb "L898"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, ⟨hE, h108, h80, h84⟩, hrb, hm⟩, hR⟩, hn⟩ := hs₀
    var_n hn
    have p_h0 : PLift _ := ⟨hm⟩
    clear hm
    obtain ⟨b, hb⟩ : ∃ b, b = (s₀.regs.get64 .r10).toNat := ⟨_, rfl⟩
    vcgen
    all_goals subst s₀
    refine ⟨⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, gi, d, ih, ⟨hE, ⟨b, ?_, ?_, ?_, ?_⟩⟩, hrb,
      p_h0.down⟩, ?_⟩, ?_⟩
    all_goals simp only [RegI, var_L8b0, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      AddrIndex.offset64, h14, Int64.toBitVec_ofNat_norm, BitVec.xor_self, BitVec.setWidth_zero,
      BitVec.toNat_zero] at hR ⊢
    all_goals first | assumption | exact hR | omega | (subst hb; exact rdx_b _ _)

theorem blk_L8b0 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L8b0" := by
  cfg_block
  measure_hb "L8b0"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, ⟨hE, b, hdx, hb8, h98, h84⟩, hrb, hm⟩, hR⟩, hn⟩ :=
      hs₀
    var_n hn
    have hn48 : d.a.n1 ≤ 48 := hE.1.1.1.2.2.2.2.2.2.2.2.1
    obtain ⟨hax, hsi, hdi⟩ := hR
    simp only [T, DecF, LocW, GbR, GbW, SbrF, DataF, sbrA, arg1, BitVec.add_assoc,
      BitVec.reduceAdd] at hm
    try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen [shl_cl32_havoc]
    all_goals subst s₀
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, Int64.toBitVec_ofNat_norm,
      BitVec.reduceToNat, Nat.reduceMod, ite_true, ite_false] at *
    case' vc3 => left; apply Table.ofLabels_at; rw [table.match_1.eq_45]
    case' vc4 => left; apply Table.ofLabels_at; rw [table.match_1.eq_25]
    all_goals have hm := p_hm.down; clear p_hm
    dx_run hm [hbp, hsp, h14, hdi, hdx, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd]
    all_goals try simp only [Width.bytes, BitVec.mul_one, Nat.mul_one] at *
    all_goals try (rw [show ∀ a b : BitVec 64, a + b - a = b from fun a b => by bv_omega, sw32_64]
                   exact rd_off1 _ _ _ hax hC.2.2.2.1.2.2.1)
    all_goals try ((try simp only [Nat.zero_add]); omega)
    case vc3 =>
      rename_i hnz _
      rw [nz_inc _ _ h98 h84] at hnz
      simp only [ne_eq, decide_eq_true_eq] at hnz
      have e := inc_toNat _ (Nat.lt_trans h98 h84)
      refine ⟨by decide, ⟨⟨hC, ⟨trivial, trivial, trivial⟩, i0, gi, d, ih, ⟨hE, b, ?_, ?_, ?_, ?_⟩,
        hrb, ?_⟩, ?_⟩, ?_⟩
      iterate 4
        · first
            | exact hdx
            | omega
            | (rw [e]; omega)
            | rfl
      · simp only [DecF, SbrF, DataF, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd]
        sep_close hm
      · simp only [RegI, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, sw32_64]
        refine ⟨?_, hsi, hdi⟩
        rw [← hsi]
        exact setl_inc _ _ _ _ _ (hsi ▸ hax) (hsi ▸ hC.2.2.2.1.2.1)
      · left
        simp only [var_L8b0, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, e]
        omega
    case vc4 =>
      refine ⟨by decide, ⟨⟨hC, ⟨trivial, trivial, trivial⟩, i0, gi, d, ih, hE, hrb, ?_⟩, ?_⟩, ?_⟩
      · simp only [DecF, SbrF, DataF, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd]
        sep_close hm
      · simp only [RegB, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, sw32_64]
        refine ⟨?_, hsi, hdi⟩
        rw [← hsi]
        exact setl_inc _ _ _ _ _ (hsi ▸ hax) (hsi ▸ hC.2.2.2.1.2.1)
      · rw [var_Lb1a]; exact Or.inl (by omega)

end Kraken.Examples.Sbr.DecExt
