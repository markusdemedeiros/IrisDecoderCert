import Kraken.X64.Examples.Sbr.Parse.UsacBlk24
open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse
set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true
/-! # `ff_aac_sbr_decode_usac_data`: the test of `bs_limiter_bands` after the default header

The default header with its change test is a `Header true` step of the model (`hdr_spec`):
`HI` with `start = 1` at `L35b5`. -/
namespace Kraken.Examples.Sbr.Usac
variable [CodeEnv]

omit [CodeEnv] in
theorem dsp_getD0 (q : UQ) (st : USt) (hl : st.sp.length = 6) :
    (dsp q st).getD 0 0 = q.uev.getD 1 0 := by
  simp [dsp, List.getD_eq_getElem?_getD, hl]

omit [CodeEnv] in
theorem dsp_getD2 (q : UQ) (st : USt) (hl : st.sp.length = 6) :
    (dsp q st).getD 2 0 = st.sp.getD 2 0 := by
  simp [dsp, List.getD_eq_getElem?_getD, hl]

omit [CodeEnv] in
/-- The values after the default header and the change test keep `Inv`. -/
theorem inv_dhR {A : UA} {st : USt} (hI : Inv A st) (hU : UeC A.1) : Inv A (dhR A.1 st) := by
  have hl := hI.2.1.1
  refine ⟨hI.1, ⟨by simp [dhR, dh, dsp, hl], ?_, ?_, ?_, hI.2.1.2.2.2.2⟩, hI.2.2⟩
  · show ((dsp A.1 st).getD 0 0).toNat = u8 A.1.uev 1
    rw [dsp_getD0 _ _ hl]
  · show ((dsp A.1 st).getD 2 0).toNat = st.h.xover
    rw [dsp_getD2 _ _ hl]; exact hI.2.1.2.2.1
  · show u8 A.1.uev 6 ≤ 3
    have := hU.2.2.1; omega

omit [CodeEnv] in
theorem dsp_getD3 (q : UQ) (st : USt) (hl : st.sp.length = 6) :
    (dsp q st).getD 3 0 = q.uev.getD 3 0 := by
  simp [dsp, List.getD_eq_getElem?_getD, hl]

omit [CodeEnv] in
theorem dsp_getD4 (q : UQ) (st : USt) (hl : st.sp.length = 6) :
    (dsp q st).getD 4 0 = q.uev.getD 4 0 &&& 1 := by
  simp [dsp, List.getD_eq_getElem?_getD, hl]

omit [CodeEnv] in
/-- The default header's `bs_freq_scale`, `bs_alter_scale` are 2- and 1-bit values. -/
theorem spw_dhR {A : UA} {st : USt} (hI : Inv A st) (hU : UeC A.1) : SpW (dhR A.1 st) := by
  intro _
  have hl := hI.2.1.1
  refine ⟨?_, ?_⟩
  · show ((dsp A.1 st).getD 3 0).toNat ≤ 3
    rw [dsp_getD3 _ _ hl]; exact hU.2.2.2.2
  · show ((dsp A.1 st).getD 4 0).toNat ≤ 1
    rw [dsp_getD4 _ _ hl, UInt8.toNat_and]
    exact Nat.and_le_right

omit [CodeEnv] in
/-- The default header with the change test is a `Header true` step: `HI` with `start = 1`,
if `bs_limiter_bands` is unchanged or a reset is pending (no `sbr_make_f_tablelim`). -/
theorem hi_dhR {A : UA} {t₀ : MachineData} {st : USt} (hI : Inv A st) (hS : S1 t₀ st)
    (hU : UeC A.1) (hk : u8 A.1.uev 6 = st.h.lb ∨ (dhR A.1 st).x.reset ≠ 0#32) :
    HI ({ (dhR A.1 st).x with start := 1#32 }, (dhR A.1 st).h) := by
  have hm : MI (st.x, st.h) := hS.1.1
  have hr : st.x.reset = 0 := hS.1.2.1
  have hl := hI.2.1.1
  by_cases he : dsp A.1 st = st.sp
  · have hlb : u8 A.1.uev 6 = st.h.lb := hk.elim id (fun h => absurd (by
      unfold dhR; rw [ite_eq_left_of_eq_true _ _ (eq_true he)]) h)
    have hs : u8 A.1.uev 1 = st.h.start := by
      rw [← hI.2.1.2.1]
      show (A.1.uev.getD 1 0).toNat = (st.sp.getD 0 0).toNat
      rw [← dsp_getD0 _ _ hl, he]
    have hh := Header.mk (usac := true) (x := st.x) (h := st.h) (u8 A.1.uev 1) st.h.xover
      (u8 A.1.uev 6) (u8 A.1.uev 7) st.x.ready (BitVec.ofNat 32 (u8 A.1.uev 8 % 2))
      (BitVec.ofNat 32 (u8 A.1.uev 8 / 2 % 2)) false hU.2.1 (fun h => Bool.noConfusion h)
      (fun _ => rfl) hU.2.2.1 hU.2.2.2.1 (Or.inr rfl) (fun hne => absurd hs hne)
      (HdrLim.keep (Or.inl hlb))
    have := (hdr_spec hm hr (Or.inr hh)).1
    rw [dhR_eq _ _ he hr]
    exact this
  · have hh := Header.mk (usac := true) (x := st.x) (h := st.h) (u8 A.1.uev 1) st.h.xover
      (u8 A.1.uev 6) (u8 A.1.uev 7) st.x.ready (BitVec.ofNat 32 (u8 A.1.uev 8 % 2))
      (BitVec.ofNat 32 (u8 A.1.uev 8 / 2 % 2)) true hU.2.1 (fun h => Bool.noConfusion h)
      (fun _ => rfl) hU.2.2.1 hU.2.2.2.1 (Or.inr rfl) (fun _ => rfl)
      (HdrLim.keep (Or.inr (by show (1#32 : BitVec 32) ≠ 0; decide)))
    have := (hdr_spec hm hr (Or.inr hh)).1
    have e : dhR A.1 st = { dh A.1 st with x := { (dh A.1 st).x with reset := 1#32 } } := by
      unfold dhR; rw [ite_eq_right_of_eq_false _ _ (eq_false he)]
    rw [e]
    exact this

omit [CodeEnv] in
/-- `cmp %ecx, %eax; je`: the new `bs_limiter_bands` against the old. -/
theorem lbz (a b : Nat) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32)
    (f : StatusFlags.from_result.Remaining) :
    CondCode.z.interp (StatusFlags.from_result (BitVec.setWidth 32 (BitVec.setWidth 64
      (BitVec.ofNat 32 a)) - BitVec.setWidth 32 (BitVec.ofNat 64 b)) f) = true ↔ b = a := by
  simp only [CondCode.interp, StatusFlags.from_result, beq_iff_eq, BitVec.zero_eq]
  constructor
  · intro h; bv_omega
  · rintro rfl; simp

omit [CodeEnv] in
/-- `cmpl $0, reset; jne`. -/
theorem rz (v : BitVec 32) (f : StatusFlags.from_result.Remaining) :
    CondCode.nz.interp (StatusFlags.from_result (BitVec.ofInt 32 v.toInt - BitVec.setWidth 32 0#64)
      f) = true ↔ v ≠ 0#32 := by
  simp only [CondCode.interp, StatusFlags.from_result, BitVec.ofInt_toInt, BitVec.zero_eq]
  simp

set_option maxRecDepth 20000 in
/-- `bs_limiter_bands` unchanged or a reset pending: on to `start = 1`; else
`sbr_make_f_tablelim`. -/
theorem blk_L358e (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L358e" := by
  cfg_block
  measure_hb "L358e"
    intro n
    simp only [tbl_L358e, var_L358e]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, hcx, st, hI, hS, hax, hm⟩, h15⟩ := hs₀.1
    obtain rfl := hs₀.2
    have hU : UeC A.1 := hF.1.2.2.2.2.1
    have hm2 := hm
    simp only [UM, UF, SHW] at hm2
    have lr : s₀.dmem.loadInt (A.1.c + 166200#64) 4
        = some (Int.ofBytes (Int.toBytes 4 (dhR A.1 st).x.reset.toInt)) := by
      rw [show A.1.c + 166200#64 = sA A.1.c + 0x18#64 by simp only [sA]; bv_omega]
      sep_mem hm2 <;> rfl
    clear hm2
    have hmc : PLift (s₀.dmem =⋆ UM k A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) (Sv t₀)
      (dhR A.1 st)) := ⟨hm⟩
    have hbxc : PLift (s₀.regs.get64 .rbx = A.1.c) := ⟨hbx⟩
    have hlb32 : st.h.lb < 2 ^ 32 := by have := hI.2.1.2.2.2.1; omega
    have h6 : u8 A.1.uev 6 < 4 := hU.2.2.1
    generalize UM k A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) (Sv t₀) (dhR A.1 st) = P at hm
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ofNat_eq_ofNat, BitVec.add_zero, hbxc.down, hax, hcx] at *
    all_goals try simp only [lr, Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt32_ofBytes_toBytes4] at *
    · rename_i hc
      have hlb := (lbz _ _ hlb32 (by omega) _).1 hc
      left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, ?_⟩
      · rw [tbl_L35b5]
        refine ⟨⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, dhR A.1 st, inv_dhR hI hU,
          ⟨hi_dhR hI hS hU (Or.inl hlb), hS.2, hS.1.2.2, spw_dhR hI hU⟩, hmc.down⟩, ?_⟩
        all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]
        all_goals first
          | exact hsp | exact hbp | exact h12 | exact h14 | exact hbxc.down
          | exact h13 | exact h15
      · first
          | exact Or.inr ⟨by simp only [var_L35b5], by decide⟩
          | exact Or.inl (by simp only [var_L35b5]; omega)
    · rename_i hz hc
      have hr := (rz _ _).1 hc
      left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, ?_⟩
      · rw [tbl_L35b5]
        refine ⟨⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, dhR A.1 st, inv_dhR hI hU,
          ⟨hi_dhR hI hS hU (Or.inr hr), hS.2, hS.1.2.2, spw_dhR hI hU⟩, hmc.down⟩, ?_⟩
        all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]
        all_goals first
          | exact hsp | exact hbp | exact h12 | exact h14 | exact hbxc.down
          | exact h13 | exact h15
      · first
          | exact Or.inr ⟨by simp only [var_L35b5], by decide⟩
          | exact Or.inl (by simp only [var_L35b5]; omega)
    · rename_i hz hc
      have hr : (dhR A.1 st).x.reset = 0#32 := by
        apply Classical.byContradiction; intro hne
        rw [(rz _ _).2 hne] at hc
        exact Bool.noConfusion hc
      have hlb : u8 A.1.uev 6 ≠ st.h.lb := by
        intro he
        rw [(lbz _ _ hlb32 (by omega) _).2 he] at hz
        exact Bool.noConfusion hz
      refine ⟨?_, by simp only [var_L359b]; omega⟩
      rw [tbl_L359b]
      refine ⟨⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, st, hI, hS, hr, hlb, hmc.down⟩, ?_⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]
      all_goals first
        | exact hsp | exact hbp | exact h12 | exact h14 | exact hbxc.down
        | exact h13 | exact h15

end Kraken.Examples.Sbr.Usac
