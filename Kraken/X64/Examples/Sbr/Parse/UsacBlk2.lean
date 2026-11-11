import Kraken.X64.Examples.Sbr.Parse.UsacBlk1
import Kraken.X64.Examples.Sbr.Parse.UsacTbl2
import Kraken.X64.Examples.Sbr.Parse.UsacTbl3

/-!
# `ff_aac_sbr_decode_usac_data`: the stores after the header

`L35b5` (`start = 1`), `L35bf` (`kx[0]`, `m[0]` from `kx[1]`, `m[1]`), `L35d7`
(`kx_and_m_pushed = 1`, the `reset` test), `L35f5` (`ready_for_dequant = 1`, the `sbr_ch` test)
and `L36c0` (the return of `0`). The footprint is split into the scalar fields of `*sbr`
(`SHW`) and one `Mem.Hid` atom for the rest (`uf_split`); the stores leave that atom alone
(`UFo` of the new values is `UFo` of the old ones by `rfl`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true
-- the shared `simp` sets of the block proofs name lemmas some goals do not need
set_option linter.unusedSimpArgs false

namespace Kraken.Examples.Sbr.Usac
variable [CodeEnv]

/-- `UF` past the scalar fields of `*sbr`. -/
def UFo (q : UQ) (st : USt) : Mem 64 → Prop :=
  TWc q.c st.x ⋆ (DSc q.c 0 st.x.d0 ⋆ (DRaw q.c 0 ⋆ (DSc q.c 1 st.x.d1
    ⋆ (DRaw q.c 1 ⋆ (AcU q.a st.x ⋆ (GbU q st.i ⋆ RdU q))))))

theorem uf_split (q : UQ) (st : USt) : UF q st = SHW q.c st ⋆ Mem.Hid (UFo q st) := rfl

/-- `L35b5`: `sbr->start = 1`. -/
theorem blk_L35b5 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L35b5" := by
  cfg_block
  measure_hb "L35b5"
    intro n
    simp only [tbl_L35b5, var_L35b5, tbl_L35bf, var_L35bf]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, hP, hm⟩, h15⟩, rfl⟩ := hs₀
    simp only [UM, uf_split, SHW, sA, BitVec.add_assoc, BitVec.reduceAdd] at hm
    simp only [T_L35bf, AtI, At, UM, uf_split, SHW, sA, BitVec.add_assoc, BitVec.reduceAdd]
    vcgen
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true,
      ite_false, Int64.toBitVec_ofNat_norm, AddrIndex.offset64_none, BitVec.add_zero,
      hsp, hbp, h12, hbx, h14, h13]
    all_goals try sep_mem hm
    case vc2 =>
      refine ⟨⟨⟨hF, ⟨trivial, trivial, trivial, trivial, trivial⟩, trivial,
        { st with x := { st.x with start := 1#32 } }, hI, hP, ?_⟩, h15⟩, Nat.le_refl _⟩
      rw [show UFo A.1 { st with x := { st.x with start := 1#32 } } = UFo A.1 st from rfl]
      simp only [BitVec.reduceSetWidth] at hm ⊢
      sep_close hm

/-- `L36c0`: `xor %eax,%eax; jmp L3ef1`, the return of `0`. -/
theorem blk_L36c0 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L36c0" := by
  cfg_block
  measure_hb "L36c0"
    intro n
    simp only [tbl_L36c0, var_L36c0]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, hP, hm⟩, rfl⟩ := hs₀
    vcgen
    all_goals try subst_vars
    left; apply Table.ofLabels_at
    refine ⟨by decide, ?_, Or.inl (by rw [var_L3ef1]; decide)⟩
    rw [tbl_L3ef1]
    simp only [T_L3ef1, AtX, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
    exact ⟨hF, hsp, st, out_fin hI hP, hm⟩

omit [CodeEnv] in
theorem mi_of_hi {s : St} (h : HI s) (hr : s.1.reset = 0) : MI s := by
  obtain ⟨b1, b2, -, b4, b5, b6, b7, i1⟩ := h
  exact ⟨⟨b1, b2 hr, b4, b5, b6, b7⟩, i1⟩

omit [CodeEnv] in
theorem tb4i (v : Int) :
    Int.toBytes 4 (BitVec.ofInt 32 (Int.ofBytes (Int.toBytes 4 v))).toInt = Int.toBytes 4 v := by
  rw [BitVec.toInt_ofInt, ← Int.toBytes_emod]
  have h : (Int.ofBytes (Int.toBytes 4 v)).bmod (2 ^ 32) % (2 ^ (8 * 4) : Int)
      = Int.ofBytes (Int.toBytes 4 v) % 2 ^ (8 * 4) := Int.bmod_emod
  rw [show ((Int.ofBytes (Int.toBytes 4 v)).bmod (2 ^ 32)).take (8 * 4)
      = (Int.ofBytes (Int.toBytes 4 v)).bmod (2 ^ 32) % 2 ^ (8 * 4) from rfl, h,
    show Int.ofBytes (Int.toBytes 4 v) % 2 ^ (8 * 4) = (Int.ofBytes (Int.toBytes 4 v)).take (8 * 4)
      from rfl, Int.toBytes_emod, Int.toBytes_ofBytes_toBytes]

/-- `L35bf`: `kx[0] = kx[1]`, `m[0] = m[1]`. -/
theorem blk_L35bf (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L35bf" := by
  cfg_block
  measure_hb "L35bf"
    intro n
    simp only [tbl_L35bf, var_L35bf, tbl_L35d7, var_L35d7]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, hP, hm⟩, h15⟩, rfl⟩ := hs₀
    simp only [UM, uf_split, SHW, sA, BitVec.add_assoc, BitVec.reduceAdd] at hm
    have l1 : s₀.dmem.loadInt (A.1.c + 166264#64) 4
        = some (Int.ofBytes (Int.toBytes 4 (st.x.kx1 : Int))) := by sep_mem hm <;> rfl
    have l2 : s₀.dmem.loadInt (A.1.c + 166272#64) 4
        = some (Int.ofBytes (Int.toBytes 4 (st.x.m1 : Int))) := by sep_mem hm <;> rfl
    simp only [T_L35d7, AtI, At, UM, uf_split, SHW, sA, BitVec.add_assoc, BitVec.reduceAdd]
    vcgen
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true,
      ite_false, Int64.toBitVec_ofNat_norm, AddrIndex.offset64_none, BitVec.add_zero,
      hsp, hbp, h12, hbx, h14, h13, l1, l2, Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try sep_mem hm
    case vc5 =>
      simp only [sw6432, tb4i] at hm ⊢
      refine ⟨⟨⟨hF, ⟨trivial, trivial, trivial, trivial, trivial⟩, trivial,
        { st with x := { st.x with kx0 := st.x.kx1, m0 := st.x.m1 } }, hI,
        ⟨hi_kxm hP.1, hP.2.1, hP.2.2.1, hP.2.2.2⟩, ?_⟩, h15⟩, Nat.le_refl _⟩
      rw [show UFo A.1 { st with x := { st.x with kx0 := st.x.kx1, m0 := st.x.m1 } } = UFo A.1 st
        from rfl]
      sep_close hm

/-- `L35d7`: `sbr->kx_and_m_pushed = 1`; `reset` decides the call of `sbr_reset`. -/
theorem blk_L35d7 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L35d7" := by
  cfg_block
  measure_hb "L35d7"
    intro n
    simp only [tbl_L35d7, var_L35d7, tbl_L35ea, var_L35ea]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, hP, hm⟩, h15⟩, rfl⟩ := hs₀
    simp only [UM, uf_split, SHW, sA, BitVec.add_assoc, BitVec.reduceAdd] at hm
    simp only [T_L35ea, AtI, At, UM, uf_split, SHW, sA, BitVec.add_assoc, BitVec.reduceAdd]
    vcgen
    all_goals try subst_vars
    case vc1 | vc2 =>
      simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true,
        ite_false, Int64.toBitVec_ofNat_norm, AddrIndex.offset64_none, BitVec.add_zero,
        hsp, hbp, h12, hbx, h14, h13]
      sep_mem hm
    case vc3 =>
      rename_i x hx hz
      revert hx
      simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true,
        ite_false, Int64.toBitVec_ofNat_norm, AddrIndex.offset64_none, BitVec.add_zero,
        hsp, hbp, h12, hbx, h14, h13]
      sep_mem hm
      intro hx
      simp only [Option.some.injEq] at hx
      subst hx
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hbx,
        Int64.toBitVec_ofNat_norm, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.reduceSetWidth,
        CondCode.interp_z, StatusFlags.zf_from_result_sub, beq_iff_eq, BitVec.sub_zero,
        StatusFlags.zf_from_result, show BitVec.zero 32 = 0#32 from rfl] at hz
      left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, Or.inr ⟨by rw [var_L35f5], by decide⟩⟩
      rw [tbl_L35f5]
      simp only [T_L35f5, AtI, At, UM, uf_split, SHW, sA, BitVec.add_assoc, BitVec.reduceAdd,
        Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
      refine ⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13,
        { st with x := { st.x with pushed := 1#32 } }, hI,
        ⟨mi_of_hi (hi_pushed hP.1) hz, hP.2.1, Or.inl hP.2.2.1⟩, ?_⟩, h15⟩
      rw [show UFo A.1 { st with x := { st.x with pushed := 1#32 } } = UFo A.1 st from rfl]
      simp only [BitVec.reduceSetWidth] at hm ⊢
      sep_close hm
    case vc4 =>
      rename_i x hx hz
      revert hx
      simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true,
        ite_false, Int64.toBitVec_ofNat_norm, AddrIndex.offset64_none, BitVec.add_zero,
        hsp, hbp, h12, hbx, h14, h13]
      sep_mem hm
      intro hx
      simp only [Option.some.injEq] at hx
      subst hx
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hbx,
        Int64.toBitVec_ofNat_norm, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.reduceSetWidth,
        CondCode.interp_z, StatusFlags.zf_from_result_sub, beq_iff_eq, BitVec.sub_zero,
        StatusFlags.zf_from_result, show BitVec.zero 32 = 0#32 from rfl] at hz
      have hz' : st.x.reset ≠ 0#32 := by simpa using hz
      refine ⟨⟨⟨hF, ⟨trivial, trivial, trivial, trivial, trivial⟩, trivial,
        { st with x := { st.x with pushed := 1#32 } }, hI,
        ⟨⟨hi_pushed hP.1, hP.2.1, hP.2.2.1, hP.2.2.2⟩, hz'⟩, ?_⟩, h15⟩, Nat.le_refl _⟩
      rw [show UFo A.1 { st with x := { st.x with pushed := 1#32 } } = UFo A.1 st from rfl]
      simp only [BitVec.reduceSetWidth] at hm ⊢
      sep_close hm

/-- `L35f5`: `sbr->ready_for_dequant = 1`; `sbr_ch` picks the element. -/
theorem blk_L35f5 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L35f5" := by
  cfg_block
  measure_hb "L35f5"
    intro n
    simp only [tbl_L35f5, var_L35f5, tbl_L3609, var_L3609]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, hP, hm⟩, h15⟩, rfl⟩ := hs₀
    simp only [UM, uf_split, SHW, sA, BitVec.add_assoc, BitVec.reduceAdd] at hm
    simp only [T_L3609, AtI, At, UM, uf_split, SHW, sA, BitVec.add_assoc, BitVec.reduceAdd]
    vcgen
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true,
      ite_false, Int64.toBitVec_ofNat_norm, AddrIndex.offset64_none, BitVec.add_zero,
      hsp, hbp, h12, hbx, h14, h13]
    all_goals try sep_mem hm
    case vc2 =>
      rename_i hz
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, Int64.toBitVec_ofNat_norm,
        BitVec.reduceSetWidth, CondCode.interp_nz, StatusFlags.zf_from_result_sub, h15,
        Bool.not_eq_true', Bool.not_eq_false', beq_iff_eq, beq_eq_false_iff_ne] at hz
      left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, Or.inr ⟨by rw [var_L36c7], by decide⟩⟩
      rw [tbl_L36c7]
      simp only [T_L36c7, AtI, At, UM, uf_split, SHW, sA, BitVec.add_assoc, BitVec.reduceAdd,
        Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
      refine ⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, { st with x := { st.x with ready := 1#32 } }, hI,
        ⟨mi_ready hP.1, hP.2.1, hP.2.2⟩, ?_⟩, hz⟩
      rw [show UFo A.1 { st with x := { st.x with ready := 1#32 } } = UFo A.1 st from rfl]
      simp only [BitVec.reduceSetWidth] at hm ⊢
      sep_close hm
    case vc3 =>
      rename_i hz
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, Int64.toBitVec_ofNat_norm,
        BitVec.reduceSetWidth, CondCode.interp_nz, StatusFlags.zf_from_result_sub, h15,
        Bool.not_eq_true', Bool.not_eq_false', beq_iff_eq, beq_eq_false_iff_ne] at hz
      refine ⟨⟨⟨hF, ⟨trivial, trivial, trivial, trivial, trivial⟩, trivial,
        { st with x := { st.x with ready := 1#32 } }, hI,
        ⟨mi_ready hP.1, hP.2.1, hP.2.2⟩, ?_⟩, hz⟩, Nat.le_refl _⟩
      rw [show UFo A.1 { st with x := { st.x with ready := 1#32 } } = UFo A.1 st from rfl]
      simp only [BitVec.reduceSetWidth] at hm ⊢
      sep_close hm

end Kraken.Examples.Sbr.Usac
