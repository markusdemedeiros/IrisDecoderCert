import Kraken.X64.Examples.Sbr.Parse.TlimAcc

/-!
# `sbr_make_f_tablelim`: `bands_warped`, the patch borders (`L3f3a` .. `L3fbf`)
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Tlim

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

omit [CodeEnv] in
theorem zx16 (u : Nat) (hu : u < 65536) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofInt 16 (u : Int))) = BitVec.ofNat 64 u := by
  apply BitVec.eq_of_toNat_eq
  simp
  omega

omit [CodeEnv] in
theorem sw16_nat (u : Nat) (hu : u < 65536) :
    (BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 16 u)))).toInt
      % 65536 = (u : Int) % 65536 := by
  have : BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 16 u)))
      = BitVec.ofNat 16 u := by
    apply BitVec.eq_of_toNat_eq
    simp
  rw [this, BitVec.toInt_eq_toNat_bmod]
  simp [Int.bmod]
  omega

omit [CodeEnv] in
theorem addb (a b : Nat) (ha : a < 256) (hb : b + a < 2 ^ 32) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32
      (BitVec.ofInt 8 (a : Int)))) + BitVec.setWidth 32 (BitVec.ofNat 64 b))
      = BitVec.ofNat 64 (b + a) := by
  apply BitVec.eq_of_toNat_eq
  simp
  omega

omit [CodeEnv] in
theorem sw16_64 (u : Nat) (hu : u < 65536) :
    (BitVec.setWidth 16 (BitVec.ofNat 64 u)).toInt % 65536 = (u : Int) % 65536 := by
  have : BitVec.setWidth 16 (BitVec.ofNat 64 u) = BitVec.ofNat 16 u := by
    apply BitVec.eq_of_toNat_eq
    simp
  rw [this, BitVec.toInt_eq_toNat_bmod]
  simp [Int.bmod]
  omega

omit [CodeEnv] in
theorem zcmp (n c : Nat) (hn : n < 2 ^ 31) (hc : c < 2 ^ 31) :
    (BitVec.setWidth 32 (BitVec.ofNat 64 n) - BitVec.setWidth 32 (BitVec.ofNat 64 c)
      == BitVec.zero 32) = decide (n = c) := by
  by_cases h : n = c
  · subst h; simp
  · have : BitVec.setWidth 32 (BitVec.ofNat 64 n) - BitVec.setWidth 32 (BitVec.ofNat 64 c)
        ≠ BitVec.zero 32 := by
      intro e; apply h; have := congrArg BitVec.toNat e; simp at this; omega
    simp only [beq_eq_false_iff_ne.mpr this, h, decide_false]

omit [CodeEnv] in
theorem pb_set (x : TArgs) (pb : List UInt8) (hpb : pb.length = 14) (i : Nat) (hi : i < 7)
    (hP : PBto x pb i) (V : Int) (hV : V % 65536 = ((x.a.kx1 + psum x.a.pnum i : Nat) : Int) % 65536)
    (hlt : x.a.kx1 + psum x.a.pnum i < 65536) :
    PBto x (setW2 pb i V) (i + 1) := by
  intro q hq
  rw [u16_setW2 _ _ _ (by omega)]
  by_cases e : q = i
  · subst e; simp only [↓reduceIte]; omega
  · simp only [e, ↓reduceIte]; exact hP q (by omega)

theorem blk_L3f3a (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L3f3a" := by
  cfg_block
  measure_hb "L3f3a"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨⟨hsp, hbp, h13⟩, hbx⟩, hax, hlb0, stk, pb, hL, hP, hm⟩, hn⟩ := hs₀
    rw [var_L3f3a] at hn
    subst hn
    have hC' := hC
    obtain ⟨hl3, -, hnp6, -, -, -, -, -, -, hkx64, -⟩ := hC'
    obtain ⟨hL1, hL2, hL3⟩ := id hL
    replace hL1 : x.a.ftLim.length = 60 := hL1
    replace hL2 : stk.length = 1024 := hL2
    replace hL3 : pb.length = 14 := hL3
    have hro := focus (T_ro k x ra t₀ (Saved t₀) _) hm
    have hkx := RO_kx1h hro
    rw [show sA t₀ = s₀.regs.get64 .rbx from hbx.symm] at hkx
    have hbw : (s₀.dmem.loadInt (BW + x.lb.setWidth 64 * 4#64 + 18446744073709551612#64) 4).isSome
        = true := by
      rw [BitVec.add_assoc]; exact RO_bw hro (by bv_omega)
    have hpbm := focus (T_pb k x ra t₀ (Saved t₀) (st0 x stk pb)) hm
    have hl2 := ld16 hpbm 0 (addr := s₀.regs.get64 .rbp + 18446744073709551570#64)
      (by rw [hbp]; simp only [rS]; bv_omega) (by simp only; omega) (by simp only; omega)
    have hs2 : ∀ v, s₀.dmem.storeInt (s₀.regs.get64 .rbp + 18446744073709551570#64) 2 v =⋆
        T k x ra t₀ (Saved t₀) ⟨x.a.ftLim, x.a.nlim, stk, setW2 pb 0 v⟩ := fun v =>
      focus (T_pb k x ra t₀ (Saved t₀) ⟨x.a.ftLim, x.a.nlim, stk, setW2 pb 0 v⟩).symm
        (st16 hpbm 0 (by rw [hbp]; simp only [rS]; bv_omega) (by simp only; omega)
          (by simp only; omega) v)
    have hnp : ∀ v, (s₀.dmem.storeInt (s₀.regs.get64 .rbp + 18446744073709551570#64) 2 v).loadInt
        (s₀.regs.get64 .rbx + 312112#64) 4 = some (Int.ofBytes (Int.toBytes 4 (x.a.npatch : Int))) :=
      fun v => by
        have := RO_np (focus (T_ro k x ra t₀ (Saved t₀) _) (hs2 v))
        rw [show sA t₀ = s₀.regs.get64 .rbx from hbx.symm] at this
        exact this
    have hsH : Hide _ := hs2
    have hkxl : x.a.kx1 < 65536 := by omega
    have hPB := pb_set x pb hL3 0 (by omega) hP
      (BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 16 x.a.kx1)))).toInt
      (by simpa [psum] using sw16_nat x.a.kx1 hkxl) (by simp [psum]; omega)
    have hPH : Hide _ := hPB
    clear hPB
    clear hm hro hpbm hs2
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals simp only [AddrIndex.offset64_none, AddrIndex.offset64_scale4, BitVec.add_zero,
      Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, Nat.reduceSub, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte,
      BitVec.ofNat_eq_ofNat, hkx, hnp, hl2, hax, hbw, Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl, BitVec.ofInt_toInt,
      BitVec.ofInt_natCast, zx_small _ (show x.a.npatch < 2 ^ 31 by omega),
      Nat.mod_eq_of_lt hkxl, CondCode.interp_z, StatusFlags.zf_from_result, BitVec.and_self] at *
    · left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, Or.inr ⟨by rw [var_L3fcc], by decide⟩⟩
      rw [tab_L3fcc]
      rename_i hz
      have hz0 : x.a.npatch = 0 := by simp at hz; bv_omega
      refine ⟨hC, ⟨⟨?_, ?_, ?_⟩, ?_⟩, hlb0, stk, _, ⟨hL1, hL2, ?_⟩, by rw [hz0]; exact hPH, hsH _⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hsp, hbp, h13, hbx]
      exact (setW2_length pb 0 _ (by omega)).trans hL3
    · rw [tab_L3f59, var_L3f59]
      rename_i hz
      refine ⟨⟨hC, ⟨⟨?_, ?_, ?_⟩, ?_⟩, hlb0, ?_, ?_, ?_, stk, _, ⟨hL1, hL2, ?_⟩, hPH, hsH _⟩,
        Nat.le_refl _⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hsp, hbp, h13, hbx]
      · apply BitVec.eq_of_toNat_eq; simp; omega
      · simp at hz; bv_omega
      · exact (setW2_length pb 0 _ (by omega)).trans hL3

theorem blk_L3f59 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L3f59" := by
  cfg_block
  measure_hb "L3f59"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨⟨hsp, hbp, h13⟩, hbx⟩, hlb0, hax, hcx, hnp0, stk, pb, hL, hP, hm⟩, hn⟩ := hs₀
    rw [var_L3f59] at hn
    subst hn
    have hC' := hC
    obtain ⟨-, -, hnp6, -⟩ := hC'
    vcgen
    all_goals try call_simp
    all_goals rename_i hs _
    all_goals subst hs
    all_goals simp only [Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.toNat_ofNat,
      Nat.reduceMod, Nat.reducePow, Nat.reduceSub, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte,
      BitVec.ofNat_eq_ofNat] at *
    · exfalso; rename_i hc
      simp only [AddrIndex.offset64_none, BitVec.add_zero] at hc
      rw [hcx] at hc
      obtain h | h | h | h | h | h : x.a.npatch = 1 ∨ x.a.npatch = 2 ∨ x.a.npatch = 3
          ∨ x.a.npatch = 4 ∨ x.a.npatch = 5 ∨ x.a.npatch = 6 := by omega
      all_goals rw [h] at hc; revert hc; decide
    · rw [tab_L3f65, var_L3f65]
      refine ⟨⟨hC, ⟨⟨?_, ?_, ?_⟩, ?_⟩, hlb0, ?_, ?_, by omega, stk, pb, hL, hP, hm⟩, Nat.le_refl _⟩
      all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hsp, hbp, h13, hbx, hax,
        hcx, psum, List.range_zero, List.foldl_nil, Nat.add_zero, v64]

theorem blk_L3f65 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L3f65" := by
  cfg_block
  measure_hb "L3f65"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨⟨hsp, hbp, h13⟩, hbx⟩, hlb0, hax, hcx, hi, stk, pb, hL, hP, hm⟩, hn⟩ := hs₀
    rw [var_L3f65] at hn
    subst hn
    have hC' := hC
    obtain ⟨-, -, hnp6, -, -, -, hpn6, -, hps, hkx64, -⟩ := hC'
    obtain ⟨hL1, hL2, hL3⟩ := id hL
    replace hL1 : x.a.ftLim.length = 60 := hL1
    replace hL2 : stk.length = 1024 := hL2
    replace hL3 : pb.length = 14 := hL3
    have hro := focus (T_ro k x ra t₀ (Saved t₀) _) hm
    have hld := RO_pnum hro hpn6 0 (by omega) (addr := s₀.regs.get64 .rbx + 312116#64)
      (by rw [hbx]; simp only [sA]; bv_omega)
    have hpbm := focus (T_pb k x ra t₀ (Saved t₀) (st0 x stk pb)) hm
    have hs2 : ∀ v, s₀.dmem.storeInt (s₀.regs.get64 .rbp + 18446744073709551572#64) 2 v =⋆
        T k x ra t₀ (Saved t₀) ⟨x.a.ftLim, x.a.nlim, stk, setW2 pb (0 + 1) v⟩ := fun v =>
      focus (T_pb k x ra t₀ (Saved t₀) ⟨x.a.ftLim, x.a.nlim, stk, setW2 pb (0 + 1) v⟩).symm
        (st16 hpbm (0 + 1) (by rw [hbp]; simp only [rS]; bv_omega) (by simp only; omega)
          (by simp only; omega) v)
    have hl2 := ld16 hpbm (0 + 1) (addr := s₀.regs.get64 .rbp + 18446744073709551572#64)
      (by rw [hbp]; simp only [rS]; bv_omega) (by simp only; omega) (by simp only; omega)
    have hsH : Hide _ := hs2
    have hps1 := psum_mono x.a.pnum (show 0 + 1 ≤ x.a.npatch by omega)
    rw [psum_succ] at hps1
    have hu8 := UInt8.toNat_lt (x.a.pnum.getD 0 0)
    have hadd := addb (x.a.pnum.getD 0 0).toNat (x.a.kx1 + psum x.a.pnum 0) hu8
      (by unfold u8 at hps1; omega)
    have hPB := pb_set x pb hL3 (0 + 1) (by omega) hP
      (BitVec.setWidth 16 (BitVec.ofNat 64 (x.a.kx1 + psum x.a.pnum 0 + (x.a.pnum.getD 0 0).toNat))).toInt
      (by rw [psum_succ x.a.pnum 0, sw16_64 _ (by unfold u8 at hps1; omega)]; unfold u8; omega)
      (by rw [psum_succ x.a.pnum 0]; omega)
    have hPH : Hide _ := hPB
    clear hPB
    clear hm hro hpbm hs2
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals simp only [AddrIndex.offset64_none, BitVec.add_zero,
      Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, Nat.reduceSub, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte,
      BitVec.ofNat_eq_ofNat, hld, hl2, hax, Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals simp only [BitVec.ofInt_natCast, hadd, CondCode.interp_z, StatusFlags.zf_from_result] at *
    · left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, Or.inr ⟨by rw [var_L3fcc], by decide⟩⟩
      rw [tab_L3fcc]
      rename_i hz
      rw [hcx, zcmp _ _ (by omega) (by omega), decide_eq_true_eq] at hz
      refine ⟨hC, ⟨⟨?_, ?_, ?_⟩, ?_⟩, hlb0, stk, _, ⟨hL1, hL2, ?_⟩, by rw [hz]; exact hPH, hsH _⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hsp, hbp, h13, hbx]
      exact (setW2_length pb (0 + 1) _ (by omega)).trans hL3
    · rw [tab_L3f77, var_L3f77]
      rename_i hz
      rw [hcx, zcmp _ _ (by omega) (by omega), decide_eq_false_iff_not] at hz
      refine ⟨⟨hC, ⟨⟨?_, ?_, ?_⟩, ?_⟩, hlb0, ?_, ?_, by omega, stk, _, ⟨hL1, hL2, ?_⟩, hPH, hsH _⟩,
        Nat.le_refl _⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hsp, hbp, h13, hbx, hcx]
      · simp only [v64, psum_succ]; unfold u8; congr 1; omega
      · exact (setW2_length pb (0 + 1) _ (by omega)).trans hL3


theorem blk_L3f77 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L3f77" := by
  cfg_block
  measure_hb "L3f77"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨⟨hsp, hbp, h13⟩, hbx⟩, hlb0, hax, hcx, hi, stk, pb, hL, hP, hm⟩, hn⟩ := hs₀
    rw [var_L3f77] at hn
    subst hn
    have hC' := hC
    obtain ⟨-, -, hnp6, -, -, -, hpn6, -, hps, hkx64, -⟩ := hC'
    obtain ⟨hL1, hL2, hL3⟩ := id hL
    replace hL1 : x.a.ftLim.length = 60 := hL1
    replace hL2 : stk.length = 1024 := hL2
    replace hL3 : pb.length = 14 := hL3
    have hro := focus (T_ro k x ra t₀ (Saved t₀) _) hm
    have hld := RO_pnum hro hpn6 1 (by omega) (addr := s₀.regs.get64 .rbx + 312117#64)
      (by rw [hbx]; simp only [sA]; bv_omega)
    have hpbm := focus (T_pb k x ra t₀ (Saved t₀) (st0 x stk pb)) hm
    have hs2 : ∀ v, s₀.dmem.storeInt (s₀.regs.get64 .rbp + 18446744073709551574#64) 2 v =⋆
        T k x ra t₀ (Saved t₀) ⟨x.a.ftLim, x.a.nlim, stk, setW2 pb (1 + 1) v⟩ := fun v =>
      focus (T_pb k x ra t₀ (Saved t₀) ⟨x.a.ftLim, x.a.nlim, stk, setW2 pb (1 + 1) v⟩).symm
        (st16 hpbm (1 + 1) (by rw [hbp]; simp only [rS]; bv_omega) (by simp only; omega)
          (by simp only; omega) v)
    have hl2 := ld16 hpbm (1 + 1) (addr := s₀.regs.get64 .rbp + 18446744073709551574#64)
      (by rw [hbp]; simp only [rS]; bv_omega) (by simp only; omega) (by simp only; omega)
    have hsH : Hide _ := hs2
    have hps1 := psum_mono x.a.pnum (show 1 + 1 ≤ x.a.npatch by omega)
    rw [psum_succ] at hps1
    have hu8 := UInt8.toNat_lt (x.a.pnum.getD 1 0)
    have hadd := addb (x.a.pnum.getD 1 0).toNat (x.a.kx1 + psum x.a.pnum 1) hu8
      (by unfold u8 at hps1; omega)
    have hPB := pb_set x pb hL3 (1 + 1) (by omega) hP
      (BitVec.setWidth 16 (BitVec.ofNat 64 (x.a.kx1 + psum x.a.pnum 1 + (x.a.pnum.getD 1 0).toNat))).toInt
      (by rw [psum_succ x.a.pnum 1, sw16_64 _ (by unfold u8 at hps1; omega)]; unfold u8; omega)
      (by rw [psum_succ x.a.pnum 1]; omega)
    have hPH : Hide _ := hPB
    clear hPB
    clear hm hro hpbm hs2
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals simp only [AddrIndex.offset64_none, BitVec.add_zero,
      Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, Nat.reduceSub, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte,
      BitVec.ofNat_eq_ofNat, hld, hl2, hax, Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals simp only [BitVec.ofInt_natCast, hadd, CondCode.interp_z, StatusFlags.zf_from_result] at *
    · left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, Or.inr ⟨by rw [var_L3fcc], by decide⟩⟩
      rw [tab_L3fcc]
      rename_i hz
      rw [hcx, zcmp _ _ (by omega) (by omega), decide_eq_true_eq] at hz
      refine ⟨hC, ⟨⟨?_, ?_, ?_⟩, ?_⟩, hlb0, stk, _, ⟨hL1, hL2, ?_⟩, by rw [hz]; exact hPH, hsH _⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hsp, hbp, h13, hbx]
      exact (setW2_length pb (1 + 1) _ (by omega)).trans hL3
    · rw [tab_L3f89, var_L3f89]
      rename_i hz
      rw [hcx, zcmp _ _ (by omega) (by omega), decide_eq_false_iff_not] at hz
      refine ⟨⟨hC, ⟨⟨?_, ?_, ?_⟩, ?_⟩, hlb0, ?_, ?_, by omega, stk, _, ⟨hL1, hL2, ?_⟩, hPH, hsH _⟩,
        Nat.le_refl _⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hsp, hbp, h13, hbx, hcx]
      · simp only [v64, psum_succ]; unfold u8; congr 1; omega
      · exact (setW2_length pb (1 + 1) _ (by omega)).trans hL3


theorem blk_L3f89 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L3f89" := by
  cfg_block
  measure_hb "L3f89"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨⟨hsp, hbp, h13⟩, hbx⟩, hlb0, hax, hcx, hi, stk, pb, hL, hP, hm⟩, hn⟩ := hs₀
    rw [var_L3f89] at hn
    subst hn
    have hC' := hC
    obtain ⟨-, -, hnp6, -, -, -, hpn6, -, hps, hkx64, -⟩ := hC'
    obtain ⟨hL1, hL2, hL3⟩ := id hL
    replace hL1 : x.a.ftLim.length = 60 := hL1
    replace hL2 : stk.length = 1024 := hL2
    replace hL3 : pb.length = 14 := hL3
    have hro := focus (T_ro k x ra t₀ (Saved t₀) _) hm
    have hld := RO_pnum hro hpn6 2 (by omega) (addr := s₀.regs.get64 .rbx + 312118#64)
      (by rw [hbx]; simp only [sA]; bv_omega)
    have hpbm := focus (T_pb k x ra t₀ (Saved t₀) (st0 x stk pb)) hm
    have hs2 : ∀ v, s₀.dmem.storeInt (s₀.regs.get64 .rbp + 18446744073709551576#64) 2 v =⋆
        T k x ra t₀ (Saved t₀) ⟨x.a.ftLim, x.a.nlim, stk, setW2 pb (2 + 1) v⟩ := fun v =>
      focus (T_pb k x ra t₀ (Saved t₀) ⟨x.a.ftLim, x.a.nlim, stk, setW2 pb (2 + 1) v⟩).symm
        (st16 hpbm (2 + 1) (by rw [hbp]; simp only [rS]; bv_omega) (by simp only; omega)
          (by simp only; omega) v)
    have hl2 := ld16 hpbm (2 + 1) (addr := s₀.regs.get64 .rbp + 18446744073709551576#64)
      (by rw [hbp]; simp only [rS]; bv_omega) (by simp only; omega) (by simp only; omega)
    have hsH : Hide _ := hs2
    have hps1 := psum_mono x.a.pnum (show 2 + 1 ≤ x.a.npatch by omega)
    rw [psum_succ] at hps1
    have hu8 := UInt8.toNat_lt (x.a.pnum.getD 2 0)
    have hadd := addb (x.a.pnum.getD 2 0).toNat (x.a.kx1 + psum x.a.pnum 2) hu8
      (by unfold u8 at hps1; omega)
    have hPB := pb_set x pb hL3 (2 + 1) (by omega) hP
      (BitVec.setWidth 16 (BitVec.ofNat 64 (x.a.kx1 + psum x.a.pnum 2 + (x.a.pnum.getD 2 0).toNat))).toInt
      (by rw [psum_succ x.a.pnum 2, sw16_64 _ (by unfold u8 at hps1; omega)]; unfold u8; omega)
      (by rw [psum_succ x.a.pnum 2]; omega)
    have hPH : Hide _ := hPB
    clear hPB
    clear hm hro hpbm hs2
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals simp only [AddrIndex.offset64_none, BitVec.add_zero,
      Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, Nat.reduceSub, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte,
      BitVec.ofNat_eq_ofNat, hld, hl2, hax, Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals simp only [BitVec.ofInt_natCast, hadd, CondCode.interp_z, StatusFlags.zf_from_result] at *
    · left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, Or.inr ⟨by rw [var_L3fcc], by decide⟩⟩
      rw [tab_L3fcc]
      rename_i hz
      rw [hcx, zcmp _ _ (by omega) (by omega), decide_eq_true_eq] at hz
      refine ⟨hC, ⟨⟨?_, ?_, ?_⟩, ?_⟩, hlb0, stk, _, ⟨hL1, hL2, ?_⟩, by rw [hz]; exact hPH, hsH _⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hsp, hbp, h13, hbx]
      exact (setW2_length pb (2 + 1) _ (by omega)).trans hL3
    · rw [tab_L3f9b, var_L3f9b]
      rename_i hz
      rw [hcx, zcmp _ _ (by omega) (by omega), decide_eq_false_iff_not] at hz
      refine ⟨⟨hC, ⟨⟨?_, ?_, ?_⟩, ?_⟩, hlb0, ?_, ?_, by omega, stk, _, ⟨hL1, hL2, ?_⟩, hPH, hsH _⟩,
        Nat.le_refl _⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hsp, hbp, h13, hbx, hcx]
      · simp only [v64, psum_succ]; unfold u8; congr 1; omega
      · exact (setW2_length pb (2 + 1) _ (by omega)).trans hL3


theorem blk_L3f9b (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L3f9b" := by
  cfg_block
  measure_hb "L3f9b"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨⟨hsp, hbp, h13⟩, hbx⟩, hlb0, hax, hcx, hi, stk, pb, hL, hP, hm⟩, hn⟩ := hs₀
    rw [var_L3f9b] at hn
    subst hn
    have hC' := hC
    obtain ⟨-, -, hnp6, -, -, -, hpn6, -, hps, hkx64, -⟩ := hC'
    obtain ⟨hL1, hL2, hL3⟩ := id hL
    replace hL1 : x.a.ftLim.length = 60 := hL1
    replace hL2 : stk.length = 1024 := hL2
    replace hL3 : pb.length = 14 := hL3
    have hro := focus (T_ro k x ra t₀ (Saved t₀) _) hm
    have hld := RO_pnum hro hpn6 3 (by omega) (addr := s₀.regs.get64 .rbx + 312119#64)
      (by rw [hbx]; simp only [sA]; bv_omega)
    have hpbm := focus (T_pb k x ra t₀ (Saved t₀) (st0 x stk pb)) hm
    have hs2 : ∀ v, s₀.dmem.storeInt (s₀.regs.get64 .rbp + 18446744073709551578#64) 2 v =⋆
        T k x ra t₀ (Saved t₀) ⟨x.a.ftLim, x.a.nlim, stk, setW2 pb (3 + 1) v⟩ := fun v =>
      focus (T_pb k x ra t₀ (Saved t₀) ⟨x.a.ftLim, x.a.nlim, stk, setW2 pb (3 + 1) v⟩).symm
        (st16 hpbm (3 + 1) (by rw [hbp]; simp only [rS]; bv_omega) (by simp only; omega)
          (by simp only; omega) v)
    have hl2 := ld16 hpbm (3 + 1) (addr := s₀.regs.get64 .rbp + 18446744073709551578#64)
      (by rw [hbp]; simp only [rS]; bv_omega) (by simp only; omega) (by simp only; omega)
    have hsH : Hide _ := hs2
    have hps1 := psum_mono x.a.pnum (show 3 + 1 ≤ x.a.npatch by omega)
    rw [psum_succ] at hps1
    have hu8 := UInt8.toNat_lt (x.a.pnum.getD 3 0)
    have hadd := addb (x.a.pnum.getD 3 0).toNat (x.a.kx1 + psum x.a.pnum 3) hu8
      (by unfold u8 at hps1; omega)
    have hPB := pb_set x pb hL3 (3 + 1) (by omega) hP
      (BitVec.setWidth 16 (BitVec.ofNat 64 (x.a.kx1 + psum x.a.pnum 3 + (x.a.pnum.getD 3 0).toNat))).toInt
      (by rw [psum_succ x.a.pnum 3, sw16_64 _ (by unfold u8 at hps1; omega)]; unfold u8; omega)
      (by rw [psum_succ x.a.pnum 3]; omega)
    have hPH : Hide _ := hPB
    clear hPB
    clear hm hro hpbm hs2
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals simp only [AddrIndex.offset64_none, BitVec.add_zero,
      Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, Nat.reduceSub, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte,
      BitVec.ofNat_eq_ofNat, hld, hl2, hax, Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals simp only [BitVec.ofInt_natCast, hadd, CondCode.interp_z, StatusFlags.zf_from_result] at *
    · left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, Or.inr ⟨by rw [var_L3fcc], by decide⟩⟩
      rw [tab_L3fcc]
      rename_i hz
      rw [hcx, zcmp _ _ (by omega) (by omega), decide_eq_true_eq] at hz
      refine ⟨hC, ⟨⟨?_, ?_, ?_⟩, ?_⟩, hlb0, stk, _, ⟨hL1, hL2, ?_⟩, by rw [hz]; exact hPH, hsH _⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hsp, hbp, h13, hbx]
      exact (setW2_length pb (3 + 1) _ (by omega)).trans hL3
    · rw [tab_L3fad, var_L3fad]
      rename_i hz
      rw [hcx, zcmp _ _ (by omega) (by omega), decide_eq_false_iff_not] at hz
      refine ⟨⟨hC, ⟨⟨?_, ?_, ?_⟩, ?_⟩, hlb0, ?_, ?_, by omega, stk, _, ⟨hL1, hL2, ?_⟩, hPH, hsH _⟩,
        Nat.le_refl _⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hsp, hbp, h13, hbx, hcx]
      · simp only [v64, psum_succ]; unfold u8; congr 1; omega
      · exact (setW2_length pb (3 + 1) _ (by omega)).trans hL3


theorem blk_L3fad (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L3fad" := by
  cfg_block
  measure_hb "L3fad"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨⟨hsp, hbp, h13⟩, hbx⟩, hlb0, hax, hcx, hi, stk, pb, hL, hP, hm⟩, hn⟩ := hs₀
    rw [var_L3fad] at hn
    subst hn
    have hC' := hC
    obtain ⟨-, -, hnp6, -, -, -, hpn6, -, hps, hkx64, -⟩ := hC'
    obtain ⟨hL1, hL2, hL3⟩ := id hL
    replace hL1 : x.a.ftLim.length = 60 := hL1
    replace hL2 : stk.length = 1024 := hL2
    replace hL3 : pb.length = 14 := hL3
    have hro := focus (T_ro k x ra t₀ (Saved t₀) _) hm
    have hld := RO_pnum hro hpn6 4 (by omega) (addr := s₀.regs.get64 .rbx + 312120#64)
      (by rw [hbx]; simp only [sA]; bv_omega)
    have hpbm := focus (T_pb k x ra t₀ (Saved t₀) (st0 x stk pb)) hm
    have hs2 : ∀ v, s₀.dmem.storeInt (s₀.regs.get64 .rbp + 18446744073709551580#64) 2 v =⋆
        T k x ra t₀ (Saved t₀) ⟨x.a.ftLim, x.a.nlim, stk, setW2 pb (4 + 1) v⟩ := fun v =>
      focus (T_pb k x ra t₀ (Saved t₀) ⟨x.a.ftLim, x.a.nlim, stk, setW2 pb (4 + 1) v⟩).symm
        (st16 hpbm (4 + 1) (by rw [hbp]; simp only [rS]; bv_omega) (by simp only; omega)
          (by simp only; omega) v)
    have hl2 := ld16 hpbm (4 + 1) (addr := s₀.regs.get64 .rbp + 18446744073709551580#64)
      (by rw [hbp]; simp only [rS]; bv_omega) (by simp only; omega) (by simp only; omega)
    have hsH : Hide _ := hs2
    have hps1 := psum_mono x.a.pnum (show 4 + 1 ≤ x.a.npatch by omega)
    rw [psum_succ] at hps1
    have hu8 := UInt8.toNat_lt (x.a.pnum.getD 4 0)
    have hadd := addb (x.a.pnum.getD 4 0).toNat (x.a.kx1 + psum x.a.pnum 4) hu8
      (by unfold u8 at hps1; omega)
    have hPB := pb_set x pb hL3 (4 + 1) (by omega) hP
      (BitVec.setWidth 16 (BitVec.ofNat 64 (x.a.kx1 + psum x.a.pnum 4 + (x.a.pnum.getD 4 0).toNat))).toInt
      (by rw [psum_succ x.a.pnum 4, sw16_64 _ (by unfold u8 at hps1; omega)]; unfold u8; omega)
      (by rw [psum_succ x.a.pnum 4]; omega)
    have hPH : Hide _ := hPB
    clear hPB
    clear hm hro hpbm hs2
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals simp only [AddrIndex.offset64_none, BitVec.add_zero,
      Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, Nat.reduceSub, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte,
      BitVec.ofNat_eq_ofNat, hld, hl2, hax, Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals simp only [BitVec.ofInt_natCast, hadd, CondCode.interp_z, StatusFlags.zf_from_result] at *
    · left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, Or.inr ⟨by rw [var_L3fcc], by decide⟩⟩
      rw [tab_L3fcc]
      rename_i hz
      rw [hcx, zcmp _ _ (by omega) (by omega), decide_eq_true_eq] at hz
      refine ⟨hC, ⟨⟨?_, ?_, ?_⟩, ?_⟩, hlb0, stk, _, ⟨hL1, hL2, ?_⟩, by rw [hz]; exact hPH, hsH _⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hsp, hbp, h13, hbx]
      exact (setW2_length pb (4 + 1) _ (by omega)).trans hL3
    · rw [tab_L3fbf, var_L3fbf]
      rename_i hz
      rw [hcx, zcmp _ _ (by omega) (by omega), decide_eq_false_iff_not] at hz
      refine ⟨⟨hC, ⟨⟨?_, ?_, ?_⟩, ?_⟩, hlb0, ?_, ?_, by omega, stk, _, ⟨hL1, hL2, ?_⟩, hPH, hsH _⟩,
        Nat.le_refl _⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hsp, hbp, h13, hbx, hcx]
      · simp only [v64, psum_succ]; unfold u8; congr 1; omega
      · exact (setW2_length pb (4 + 1) _ (by omega)).trans hL3


theorem blk_L3fbf (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L3fbf" := by
  cfg_block
  measure_hb "L3fbf"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨⟨hsp, hbp, h13⟩, hbx⟩, hlb0, hax, hcx, hi, stk, pb, hL, hP, hm⟩, hn⟩ := hs₀
    rw [var_L3fbf] at hn
    subst hn
    have hC' := hC
    obtain ⟨-, -, hnp6, -, -, -, hpn6, -, hps, hkx64, -⟩ := hC'
    obtain ⟨hL1, hL2, hL3⟩ := id hL
    replace hL1 : x.a.ftLim.length = 60 := hL1
    replace hL2 : stk.length = 1024 := hL2
    replace hL3 : pb.length = 14 := hL3
    have hro := focus (T_ro k x ra t₀ (Saved t₀) _) hm
    have hld := RO_pnum hro hpn6 5 (by omega) (addr := s₀.regs.get64 .rbx + 312121#64)
      (by rw [hbx]; simp only [sA]; bv_omega)
    have hpbm := focus (T_pb k x ra t₀ (Saved t₀) (st0 x stk pb)) hm
    have hs2 : ∀ v, s₀.dmem.storeInt (s₀.regs.get64 .rbp + 18446744073709551582#64) 2 v =⋆
        T k x ra t₀ (Saved t₀) ⟨x.a.ftLim, x.a.nlim, stk, setW2 pb (5 + 1) v⟩ := fun v =>
      focus (T_pb k x ra t₀ (Saved t₀) ⟨x.a.ftLim, x.a.nlim, stk, setW2 pb (5 + 1) v⟩).symm
        (st16 hpbm (5 + 1) (by rw [hbp]; simp only [rS]; bv_omega) (by simp only; omega)
          (by simp only; omega) v)
    have hl2 := ld16 hpbm (5 + 1) (addr := s₀.regs.get64 .rbp + 18446744073709551582#64)
      (by rw [hbp]; simp only [rS]; bv_omega) (by simp only; omega) (by simp only; omega)
    have hsH : Hide _ := hs2
    have hps1 := psum_mono x.a.pnum (show 5 + 1 ≤ x.a.npatch by omega)
    rw [psum_succ] at hps1
    have hu8 := UInt8.toNat_lt (x.a.pnum.getD 5 0)
    have hadd := addb (x.a.pnum.getD 5 0).toNat (x.a.kx1 + psum x.a.pnum 5) hu8
      (by unfold u8 at hps1; omega)
    have hPB := pb_set x pb hL3 (5 + 1) (by omega) hP
      (BitVec.setWidth 16 (BitVec.ofNat 64 (x.a.kx1 + psum x.a.pnum 5 + (x.a.pnum.getD 5 0).toNat))).toInt
      (by rw [psum_succ x.a.pnum 5, sw16_64 _ (by unfold u8 at hps1; omega)]; unfold u8; omega)
      (by rw [psum_succ x.a.pnum 5]; omega)
    have hPH : Hide _ := hPB
    clear hPB
    clear hm hro hpbm hs2
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals simp only [AddrIndex.offset64_none, BitVec.add_zero,
      Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, Nat.reduceSub, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte,
      BitVec.ofNat_eq_ofNat, hld, hl2, hax, Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals simp only [BitVec.ofInt_natCast, hadd, CondCode.interp_z, StatusFlags.zf_from_result] at *
    rw [tab_L3fcc, var_L3fcc]
    have h6 : x.a.npatch = 5 + 1 := by omega
    refine ⟨⟨hC, ⟨⟨?_, ?_, ?_⟩, ?_⟩, hlb0, stk, _, ⟨hL1, hL2, ?_⟩, by rw [h6]; exact hPH, hsH _⟩,
      Nat.le_refl _⟩
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hsp, hbp, h13, hbx]
    exact (setW2_length pb (5 + 1) _ (by omega)).trans hL3

end Kraken.Examples.Sbr.Tlim
