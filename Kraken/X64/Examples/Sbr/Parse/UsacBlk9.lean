import Kraken.X64.Examples.Sbr.Parse.UsacBlk8
open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse
set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true
/-! # `ff_aac_sbr_decode_usac_data`: the dispatch on `n[1]` before the `bs_add_harmonic` loops

`movslq n[1]`; `n[1] ≤ 0` skips the loop, `n[1] = 1` reads the odd bit only, `n[1] ≥ 2` sets up
the paired loop. -/
namespace Kraken.Examples.Sbr.Usac
variable [CodeEnv]

omit [CodeEnv] in
/-- `movslq` of `n[1] ≤ 48`. -/
theorem n1_sx (n : Nat) (h : n ≤ 48) :
    BitVec.signExtend 64 (BitVec.ofInt 32 (Int.ofBytes (Int.toBytes 4 (n : Int))))
      = BitVec.ofNat 64 n := by
  rw [BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl]
  revert n; decide

omit [CodeEnv] in
/-- The dispatch on `n[1]` (`test`; `jle`; `cmp $1`; `jne`), decided over `n[1] ≤ 48`. -/
theorem n1_disp (n : Nat) (h : n ≤ 48)
    (hle : ((BitVec.ofNat 64 n).msb != false || BitVec.ofNat 64 n == BitVec.zero 64) = false) :
    ((!BitVec.setWidth 32 (BitVec.ofNat 64 n) - BitVec.setWidth 32 (Int64.toBitVec 1)
        == BitVec.zero 32) = true → 2 ≤ n)
    ∧ ((!BitVec.setWidth 32 (BitVec.ofNat 64 n) - BitVec.setWidth 32 (Int64.toBitVec 1)
        == BitVec.zero 32) = false → n = 1) := by
  revert n; decide

/-- A register of the frame, through the block's register writes. -/
local macro "rg " h:term : term =>
  `(by first | exact $h | (simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact $h))

/-- The dispatch of the single-channel loop. -/
theorem blk_L3913 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L3913" := by
  cfg_block
  measure_hb "L3913"
    intro n
    simp only [tbl_L3913, var_L3913]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨h, rfl⟩ := hs₀
    obtain ⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, ⟨hfin, -⟩, hm⟩ := h
    have hm2 := hm
    simp only [UM, UF, TWc, sA, BitVec.add_assoc, BitVec.reduceAdd] at hm2
    have l1 : s₀.dmem.loadInt (A.1.c + 477956#64) 4
        = some (Int.ofBytes (Int.toBytes 4 (st.x.n1 : Int))) := by sep_mem hm2 <;> rfl
    clear hm2
    have l1' : s₀.dmem.loadInt (s₀.regs.get64 .rbx + AddrIndex.offset64 none s₀.regs
        + Int64.toBitVec 477956) 4 = some (Int.ofBytes (Int.toBytes 4 (st.x.n1 : Int))) := by
      simp only [AddrIndex.offset64_none, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
        Int64.toBitVec_ofNat_norm, hbx]
      exact l1
    clear l1
    vcgen
    all_goals try subst_vars
    all_goals simp only [l1', Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals simp only [n1_sx _ (n1_le hfin), Reg64s.get64_set64, reduceCtorEq, ite_true,
      ite_false, CondCode.interp_le, CondCode.interp_nz, StatusFlags.sf_from_result,
      StatusFlags.of_from_result, StatusFlags.zf_from_result, BitVec.and_self] at *
    case vc2 =>
      left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, Or.inl (by rw [var_L3c4b]; decide)⟩
      rw [tbl_L3c4b]
      exact ⟨hF, ⟨rg hsp, rg hbp, rg h12, rg hbx, rg h14⟩, rg h13, st, hI, ⟨hfin, trivial⟩, hm⟩
    case vc3 _ hle hnz =>
      left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, Or.inl (by rw [var_L3b98]; decide)⟩
      rw [tbl_L3b98]
      exact ⟨hF, ⟨rg hsp, rg hbp, rg h12, rg hbx, rg h14⟩, rg h13, st, hI, ⟨hfin, ⟨rfl,
        (n1_disp _ (n1_le hfin) hle).1 hnz⟩⟩, hm⟩
    case vc4 _ _ hle hnz =>
      left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, Or.inl (by rw [var_L3c1c]; decide)⟩
      rw [tbl_L3c1c]
      exact ⟨hF, ⟨rg hsp, rg hbp, rg h12, rg hbx, rg h14⟩, rg h13, st, hI, ⟨hfin, by
        show (_ : BitVec 64).toNat + 1 = st.x.n1
        rw [(n1_disp _ (n1_le hfin) hle).2 hnz]
        simp only [Reg64s.get64_set64, ite_true, BitVec.xor_self]; rfl⟩, hm⟩


/-- The dispatch of the coupled loop. -/
theorem blk_L3a8c (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L3a8c" := by
  cfg_block
  measure_hb "L3a8c"
    intro n
    simp only [tbl_L3a8c, var_L3a8c]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨h, rfl⟩ := hs₀
    obtain ⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, ⟨hfin, -⟩, hm⟩ := h
    have hm2 := hm
    simp only [UM, UF, TWc, sA, BitVec.add_assoc, BitVec.reduceAdd] at hm2
    have l1 : s₀.dmem.loadInt (A.1.c + 477956#64) 4
        = some (Int.ofBytes (Int.toBytes 4 (st.x.n1 : Int))) := by sep_mem hm2 <;> rfl
    clear hm2
    have l1' : s₀.dmem.loadInt (s₀.regs.get64 .rbx + AddrIndex.offset64 none s₀.regs
        + Int64.toBitVec 477956) 4 = some (Int.ofBytes (Int.toBytes 4 (st.x.n1 : Int))) := by
      simp only [AddrIndex.offset64_none, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
        Int64.toBitVec_ofNat_norm, hbx]
      exact l1
    clear l1
    vcgen
    all_goals try subst_vars
    all_goals simp only [l1', Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals simp only [n1_sx _ (n1_le hfin), Reg64s.get64_set64, reduceCtorEq, ite_true,
      ite_false, CondCode.interp_le, CondCode.interp_nz, StatusFlags.sf_from_result,
      StatusFlags.of_from_result, StatusFlags.zf_from_result, BitVec.and_self] at *
    case vc2 =>
      left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, Or.inl (by rw [var_L3e17]; decide)⟩
      rw [tbl_L3e17]
      exact ⟨hF, ⟨rg hsp, rg hbp, rg h12, rg hbx, rg h14⟩, rg h13, st, hI, ⟨hfin, trivial⟩, hm⟩
    case vc3 _ hle hnz =>
      left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, Or.inl (by rw [var_L3d64]; decide)⟩
      rw [tbl_L3d64]
      exact ⟨hF, ⟨rg hsp, rg hbp, rg h12, rg hbx, rg h14⟩, rg h13, st, hI, ⟨hfin, ⟨rfl,
        (n1_disp _ (n1_le hfin) hle).1 hnz⟩⟩, hm⟩
    case vc4 _ _ hle hnz =>
      left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, Or.inl (by rw [var_L3de8]; decide)⟩
      rw [tbl_L3de8]
      exact ⟨hF, ⟨rg hsp, rg hbp, rg h12, rg hbx, rg h14⟩, rg h13, st, hI, ⟨hfin, by
        show (_ : BitVec 64).toNat + 1 = st.x.n1
        rw [(n1_disp _ (n1_le hfin) hle).2 hnz]
        simp only [Reg64s.get64_set64, ite_true, BitVec.xor_self]; rfl⟩, hm⟩


/-- The dispatch of the coupled pair's second loop. -/
theorem blk_L3c84 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L3c84" := by
  cfg_block
  measure_hb "L3c84"
    intro n
    simp only [tbl_L3c84, var_L3c84]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨h, rfl⟩ := hs₀
    obtain ⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, ⟨hfin, -⟩, hm⟩, hax⟩ := h
    have hm2 := hm
    simp only [UM, UF, TWc, sA, BitVec.add_assoc, BitVec.reduceAdd] at hm2
    have l1 : s₀.dmem.loadInt (A.1.c + 477956#64) 4
        = some (Int.ofBytes (Int.toBytes 4 (st.x.n1 : Int))) := by sep_mem hm2 <;> rfl
    clear hm2
    have l1' : s₀.dmem.loadInt (s₀.regs.get64 .rbx + AddrIndex.offset64 none s₀.regs
        + Int64.toBitVec 477956) 4 = some (Int.ofBytes (Int.toBytes 4 (st.x.n1 : Int))) := by
      simp only [AddrIndex.offset64_none, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
        Int64.toBitVec_ofNat_norm, hbx]
      exact l1
    clear l1
    vcgen
    all_goals try subst_vars
    all_goals simp only [l1', Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals simp only [n1_sx _ (n1_le hfin), Reg64s.get64_set64, reduceCtorEq, ite_true,
      ite_false, CondCode.interp_le, CondCode.interp_nz, StatusFlags.sf_from_result,
      StatusFlags.of_from_result, StatusFlags.zf_from_result, BitVec.and_self] at *
    case vc2 =>
      left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, Or.inl (by rw [var_L3ef1]; decide)⟩
      rw [tbl_L3ef1]
      exact ⟨hF, rg hsp, st, by unfold UsacOut; exact ⟨hfin.1, fun _ => hfin.2, hI⟩, hm⟩
    case vc3 _ hle hnz =>
      left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, Or.inl (by rw [var_L3ca2]; decide)⟩
      rw [tbl_L3ca2]
      exact ⟨⟨hF, ⟨rg hsp, rg hbp, rg h12, rg hbx, rg h14⟩, rg h13, st, hI, ⟨hfin, rfl,
        (n1_disp _ (n1_le hfin) hle).1 hnz⟩, hm⟩, (by first | rfl | simp only [Reg64s.get64_set64,
        ite_true, BitVec.xor_self, sw6432])⟩
    case vc4 _ _ hle hnz =>
      refine ⟨?_, by rw [var_L3c9b]; decide⟩
      rw [tbl_L3c9b]
      exact ⟨⟨hF, ⟨rg hsp, rg hbp, rg h12, rg hbx, rg h14⟩, rg h13, st, hI, ⟨hfin,
        (n1_disp _ (n1_le hfin) hle).2 hnz⟩, hm⟩, (by first | rfl | simp only [Reg64s.get64_set64,
        ite_true, BitVec.xor_self, sw6432])⟩

/-- The dispatch of the first loop. -/
theorem blk_L3ab1 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L3ab1" := by
  cfg_block
  measure_hb "L3ab1"
    intro n
    simp only [tbl_L3ab1, var_L3ab1]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨h, rfl⟩ := hs₀
    obtain ⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, ⟨hfin, -⟩, hm⟩ := h
    have hm2 := hm
    simp only [UM, UF, TWc, sA, BitVec.add_assoc, BitVec.reduceAdd] at hm2
    have l1 : s₀.dmem.loadInt (A.1.c + 477956#64) 4
        = some (Int.ofBytes (Int.toBytes 4 (st.x.n1 : Int))) := by sep_mem hm2 <;> rfl
    clear hm2
    have l1' : s₀.dmem.loadInt (s₀.regs.get64 .rbx + AddrIndex.offset64 none s₀.regs
        + Int64.toBitVec 477956) 4 = some (Int.ofBytes (Int.toBytes 4 (st.x.n1 : Int))) := by
      simp only [AddrIndex.offset64_none, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
        Int64.toBitVec_ofNat_norm, hbx]
      exact l1
    clear l1
    vcgen
    all_goals try subst_vars
    all_goals simp only [l1', Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals simp only [n1_sx _ (n1_le hfin), Reg64s.get64_set64, reduceCtorEq, ite_true,
      ite_false, CondCode.interp_le, CondCode.interp_nz, StatusFlags.sf_from_result,
      StatusFlags.of_from_result, StatusFlags.zf_from_result, BitVec.and_self] at *
    case vc2 =>
      left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, Or.inl (by rw [var_L3ef1]; decide)⟩
      rw [tbl_L3ef1]
      exact ⟨hF, rg hsp, st, by unfold UsacOut; exact ⟨hfin.1, fun _ => hfin.2, hI⟩, hm⟩
    case vc3 _ hle hnz =>
      left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, Or.inl (by rw [var_L3ad4]; decide)⟩
      rw [tbl_L3ad4]
      exact ⟨⟨hF, ⟨rg hsp, rg hbp, rg h12, rg hbx, rg h14⟩, rg h13, st, hI, ⟨hfin, rfl,
        (n1_disp _ (n1_le hfin) hle).1 hnz⟩, hm⟩, (by first | rfl | simp only [Reg64s.get64_set64,
        ite_true, BitVec.xor_self, sw6432])⟩
    case vc4 _ _ hle hnz =>
      left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, Or.inl (by rw [var_L3b61]; decide)⟩
      rw [tbl_L3b61]
      exact ⟨⟨hF, ⟨rg hsp, rg hbp, rg h12, rg hbx, rg h14⟩, rg h13, st, hI, ⟨hfin, by
        show (_ : BitVec 64).toNat + 1 = st.x.n1
        rw [(n1_disp _ (n1_le hfin) hle).2 hnz]
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.xor_self]; rfl⟩,
          hm⟩, (by first | rfl | simp only [Reg64s.get64_set64, ite_true, BitVec.xor_self,
          sw6432])⟩

end Kraken.Examples.Sbr.Usac
