import Kraken.InfoOff
import Kraken.X64.Examples.Sbr.Parse.ResetA1F4
import Kraken.X64.Examples.Sbr.Parse.ResetA1W
import Kraken.X64.Examples.Sbr.Parse.ResetA1Avx
import Kraken.X64.Examples.Sbr.Parse.ResetA2Lane

/-!
# `sbr_reset`: `bs_freq_scale = 0`, the negative `k2diff` correction `L1ed8` (shard A1)

`f_master[1] -= 1`, and `f_master[2] -= 1` when `k2diff < -1`, as one 32-bit `vpaddw` of
`(-1, -(k2diff ≠ -1))` into `f_master[1..2]`.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Reset

variable [CodeEnv]

set_option linter.unusedSimpArgs false in
omit [CodeEnv] in
theorem ln16_pk (op : BitVec 16 → BitVec 16 → BitVec 16) (a b : BitVec 128) :
    (BitVec.packedBinOp 16 op a b).extractLsb' 0 16 = op (a.extractLsb' 0 16) (b.extractLsb' 0 16)
    ∧ (BitVec.packedBinOp 16 op a b).extractLsb' 16 16
      = op (a.extractLsb' 16 16) (b.extractLsb' 16 16) := by
  simp (disch := decide) only [ln_pk_step, ln_pk_base, BitVec.take, BitVec.drop]
  simp (disch := omega) only [ln_ex_ex]
  simp only [Nat.reduceAdd, Nat.reduceSub]
  constructor
  · apply BitVec.eq_of_getLsbD_eq; intro j hj
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, BitVec.append_eq,
      BitVec.getLsbD_append, hj, decide_true, Bool.true_and]
    simp (disch := omega) only [ite_eq_left, ite_eq_right, decide_eq_true, Bool.true_and, Nat.reduceMul,
      Nat.sub_sub, Nat.reduceAdd, Nat.add_sub_cancel_left, Nat.zero_add]
  · apply BitVec.eq_of_getLsbD_eq; intro j hj
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, BitVec.append_eq,
      BitVec.getLsbD_append, hj, decide_true, Bool.true_and]
    simp (disch := omega) only [ite_eq_left, ite_eq_right, decide_eq_true, Bool.true_and, Nat.reduceMul,
      Nat.sub_sub, Nat.reduceAdd, Nat.add_sub_cancel_left, Nat.zero_add]

set_option linter.unusedSimpArgs false in
omit [CodeEnv] in
theorem ln16_pki (op : Nat → BitVec 16 → BitVec 16 → BitVec 16) (a b : BitVec 128) :
    (BitVec.packedBinOpIdx 16 op a b).extractLsb' 0 16 = op 0 (a.extractLsb' 0 16) (b.extractLsb' 0 16)
    ∧ (BitVec.packedBinOpIdx 16 op a b).extractLsb' 16 16
      = op 1 (a.extractLsb' 16 16) (b.extractLsb' 16 16) := by
  simp (disch := decide) only [ln_pki_step, ln_pki_base, BitVec.take, BitVec.drop]
  simp (disch := omega) only [ln_ex_ex]
  simp only [Nat.reduceAdd, Nat.reduceSub]
  constructor
  · apply BitVec.eq_of_getLsbD_eq; intro j hj
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, BitVec.append_eq,
      BitVec.getLsbD_append, hj, decide_true, Bool.true_and]
    simp (disch := omega) only [ite_eq_left, ite_eq_right, decide_eq_true, Bool.true_and, Nat.reduceMul,
      Nat.sub_sub, Nat.reduceAdd, Nat.add_sub_cancel_left, Nat.zero_add]
  · apply BitVec.eq_of_getLsbD_eq; intro j hj
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, BitVec.append_eq,
      BitVec.getLsbD_append, hj, decide_true, Bool.true_and]
    simp (disch := omega) only [ite_eq_left, ite_eq_right, decide_eq_true, Bool.true_and, Nat.reduceMul,
      Nat.sub_sub, Nat.reduceAdd, Nat.add_sub_cancel_left, Nat.zero_add]

omit [CodeEnv] in
theorem a1_sw32_lanes (x : BitVec 128) :
    (x.setWidth 32).toNat % 65536 = (x.extractLsb' 0 16).toNat
    ∧ (x.setWidth 32).toNat / 65536 % 65536 = (x.extractLsb' 16 16).toNat := by
  simp only [BitVec.toNat_setWidth, BitVec.extractLsb'_toNat]
  omega

omit [CodeEnv] in
theorem a1_ofBytes_slice4 (l : List UInt8) (h : 6 ≤ l.length) :
    Int.ofBytes (slice l 2 4) = (u16 l 1 : Int) + 65536 * (u16 l 2 : Int) := by
  have e : slice l 2 4 = [l[2], l[3], l[4], l[5]] := by
    apply List.ext_getElem (by simp only [slice, List.length_take, List.length_drop,
      List.length_cons, List.length_nil]; omega)
    intro j h1 h2
    simp only [List.length_cons, List.length_nil] at h2
    simp only [slice, List.getElem_take, List.getElem_drop]
    rcases j with _ | _ | _ | _ | j
    · rfl
    · rfl
    · rfl
    · rfl
    · omega
  rw [e, Int.ofBytes_cons, Int.ofBytes_cons, Int.ofBytes_cons, Int.ofBytes_cons]
  unfold u16 u8
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show 2 < l.length by omega),
    List.getElem?_eq_getElem (show 3 < l.length by omega), List.getElem?_eq_getElem (show 4 < l.length by omega),
    List.getElem?_eq_getElem (show 5 < l.length by omega), Option.getD_some,
    show Int.ofBytes [] = 0 from rfl, Nat.reduceMul, Nat.reduceAdd]
  omega

section Mem4

variable {k : Nat} {e : REnv} {a : RArgs} {ra : Int64} {t₀ : MachineData} {st : St}
  {fr : List UInt8} {m : Mem 64}

theorem a1_lcpi8_load (hm : m =⋆ Mm k e a ra t₀ st fr) :
    m.loadInt (lab "LCPI5_8") 4 = some (Int.ofBytes (Int.toBytes 4 (0xffffffff#32 : BitVec 32).toInt)) := by
  have h := focus (Mm_cst ..) hm
  simp only [CstR] at h
  obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_lr h
  obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_lr h
  obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_ll h
  exact loadInt_sep _ _ 4 _ m h (Int.toBytes_length 4 _) (by omega)

theorem a1_fm4_load (hm : m =⋆ Mm k e a ra t₀ st fr) (hl : st.fm.length = 98) :
    m.loadInt (arg1 t₀ + 311794#64) 4 = some ((u16 st.fm 1 : Int) + 65536 * (u16 st.fm 2 : Int)) := by
  rw [region_load (focus (Mm_fm ..) hm) (o := 2) (n := 4) (by simp only [arg1]; bv_omega) (by omega)
    (by omega), a1_ofBytes_slice4 _ (by omega)]

theorem a1_fm4_store (hm : m =⋆ Mm k e a ra t₀ st fr) (hl : st.fm.length = 98) (v : Int) :
    m.storeInt (arg1 t₀ + 311794#64) 4 v =⋆ Mm k e a ra t₀ { st with fm := wr st.fm (2 * 1) (Int.toBytes (2 * 2) v) } fr :=
  Mm_upd_fm .. ▸ region_store (focus (Mm_fm ..) hm) (o := 2) (by simp only [arg1]; bv_omega) (by omega)
    (by omega) v

end Mem4

omit [CodeEnv] in
/-- `xor; cmp $-1; setne; neg` of `L1ed8`, low word: `-(k2diff ≠ -1)`. -/
theorem a1_neg_setne {D : Int} (hD : D = -1 ∨ D = -2) (f : StatusFlags.from_result.Remaining) :
    BitVec.setWidth 16 (BitVec.setWidth 32 (BitVec.setWidth 64 (-BitVec.setWidth 32
      ((BitVec.setWidth 64 0#32).replaceLow (BitVec.ofNat 8 (CondCode.nz.interp
        (StatusFlags.from_result (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.ofInt 32 D))
          - BitVec.setWidth 32 4294967295#64) f)).toNat)))))
      = if D = -1 then 0#16 else 65535#16 := by
  rw [CondCode.interp_nz, StatusFlags.zf_from_result]
  rcases hD with rfl | rfl <;> decide

set_option linter.unusedSimpArgs false in
omit [CodeEnv] in
/-- `f_master[1..=nm]` after the `vpaddw` of `L1ed8`. -/
theorem a1_ed8_stepped {fm : List UInt8} {dk N : Nat} {D : Int} (hl : fm.length = 98) (hN2 : 2 ≤ N)
    (hN : N ≤ 48) (hdk1 : 1 ≤ dk) (hdk : dk ≤ 2) (hD : D = -1 ∨ D = -2) (hfil : Filled fm dk (N + 1)) :
    Stepped (wr fm (2 * 1) (Int.toBytes (2 * 2) (BitVec.setWidth 32 (BitVec.packedBinOp 16 HAdd.hAdd
      (BitVec.setWidth 128 (BitVec.ofInt 32 ((u16 fm 1 : Int) + 65536 * (u16 fm 2 : Int))))
      (BitVec.packedBinOpIdx 16
        (fun i x _ => if i = UInt8.toNat 1 % 8 then (if D = -1 then 0#16 else 65535#16) else x)
        (BitVec.packedBinOp 32 (fun _ _ => 4294967295#32) 0#128 0#128)
        (BitVec.packedBinOp 32 (fun _ _ => 4294967295#32) 0#128 0#128)))).toInt)) dk N D := by
  generalize hX0 : BitVec.packedBinOp 32 (fun _ _ => 4294967295#32) 0#128 0#128 = X0
  have hX0a : X0.extractLsb' 0 16 = 65535#16 := by
    have := ln_ex_ex X0 0 32 0 16 (by omega)
    simp only [Nat.add_zero] at this
    rw [← this, ← hX0, ln_pk_l0]; decide
  have hX0b : X0.extractLsb' 16 16 = 65535#16 := by
    have := ln_ex_ex X0 0 32 16 16 (by omega)
    simp only [Nat.zero_add] at this
    rw [← this, ← hX0, ln_pk_l0]; decide
  have hi0 : (0 = UInt8.toNat 1 % 8) = False := by decide
  have hi1 : (1 = UInt8.toNat 1 % 8) = True := by decide
  have hq := ln16_pki (fun i x _ => if i = UInt8.toNat 1 % 8 then (if D = -1 then 0#16 else 65535#16) else x)
    X0 X0
  simp only [hi0, hi1, ite_false, ite_true, hX0a] at hq
  generalize hX1 : BitVec.setWidth 128 (BitVec.ofInt 32 ((u16 fm 1 : Int) + 65536 * (u16 fm 2 : Int))) = X1
  have hb : ∀ i, u16 fm i < 65536 := fun i => by
    unfold u16 u8; have := (fm.getD (2 * i) 0).toNat_lt; have := (fm.getD (2 * i + 1) 0).toNat_lt; omega
  have hb1 := hb 1
  have hb2 := hb 2
  have hX1a : (X1.extractLsb' 0 16).toNat = u16 fm 1 := by
    rw [← hX1]
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, BitVec.toNat_ofInt]
    omega
  have hX1b : (X1.extractLsb' 16 16).toNat = u16 fm 2 := by
    rw [← hX1]
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, BitVec.toNat_ofInt]
    omega
  have hp := ln16_pk HAdd.hAdd X1 (BitVec.packedBinOpIdx 16
    (fun i x _ => if i = UInt8.toNat 1 % 8 then (if D = -1 then 0#16 else 65535#16) else x) X0 X0)
  rw [hq.1, hq.2] at hp
  generalize hV : BitVec.setWidth 32 (BitVec.packedBinOp 16 HAdd.hAdd X1 (BitVec.packedBinOpIdx 16
    (fun i x _ => if i = UInt8.toNat 1 % 8 then (if D = -1 then 0#16 else 65535#16) else x) X0 X0)) = V
  have hl2 := a1_sw32_lanes (BitVec.packedBinOp 16 HAdd.hAdd X1 (BitVec.packedBinOpIdx 16
    (fun i x _ => if i = UInt8.toNat 1 % 8 then (if D = -1 then 0#16 else 65535#16) else x) X0 X0))
  rw [hV, hp.1, hp.2, BitVec.toNat_add, BitVec.toNat_add, hX1a, hX1b] at hl2
  have hK : (if D = -1 then 0#16 else 65535#16).toNat = if D = -1 then 0 else 65535 := by
    split <;> rfl
  rw [hK] at hl2
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hl2
  have hVn : V.toInt % 4294967296 = (V.toNat : Int) := by
    rw [BitVec.toInt_eq_toNat_cond]; have := V.isLt; simp only [Nat.reducePow] at this ⊢
    split <;> omega
  have hT : Int.toBytes (2 * 2) V.toInt = Int.toBytes (2 * 2) (V.toNat : Int) := by
    rw [← Int.toBytes_emod (2 * 2) V.toInt]; simp only [Int.take, Nat.reduceMul, Int.reducePow, hVn]
  rw [hT]
  have hw0 := a1_u16_wr_words 2 (l := fm) (j := 1) (V.toNat : Int) (by omega) 0 (by omega)
  have hw1 := a1_u16_wr_words 2 (l := fm) (j := 1) (V.toNat : Int) (by omega) 1 (by omega)
  simp only [Int.reducePow, Int.ediv_one] at hw0 hw1
  have hVl := V.isLt
  simp only [Nat.reducePow] at hVl
  intro i h1 h2
  rcases (show i = 1 ∨ i = 2 ∨ 3 ≤ i by omega) with rfl | rfl | h3
  · rw [hw0]
    have hf := hfil 1 (by omega) (by omega)
    unfold stepOf
    rw [ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
    omega
  · rw [hw1]
    have hf := hfil 2 (by omega) (by omega)
    unfold stepOf
    rw [ite_eq_right (show ¬(D < 0 ∧ 2 = 1) by omega)]
    rw [ite_eq_right (show ¬(0 < D ∧ 2 = N) by omega)]
    by_cases hD1 : D = -1
    · rw [ite_eq_right (by omega)]
      simp only [hD1, ite_true] at hl2
      omega
    · rw [ite_eq_left (by omega)]
      simp only [hD1, ite_false] at hl2
      omega
  · have hb : (Int.toBytes (2 * 2) (V.toNat : Int)).length = 4 := Int.toBytes_length ..
    rw [a1_u16_wr_ne (by rw [hb]; omega) (by rw [hb]; omega), hfil i (by omega) (by omega)]
    unfold stepOf
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
    omega

theorem blk_L1ed8 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1ed8" ⟨"sbr_reset.L1ed8", B.L1ed8, some "sbr_reset.L1f08"⟩ := by
  info_off
  measure_hb "L1ed8"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hr, hk2, hle, hq, h3, ⟨hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2s, ⟨h2, hxo, hnm, hdx⟩, h13, hcx, hneg, hsi, hfil⟩, hm⟩, h12, h15⟩ := T.L1ed8.mp hs
    clear hs
    have h48 := f0_nm_48 hr hC.2.1 hq
    have hA4 : u8 a.sp 4 ≤ 1 := hC.2.2.2.1
    have hdb := a1_diff_bounds (k0 := k0N a row) (k2 := k2) hle hA4
    generalize hNdef : nmOf (k2 - k0N a row) (u8 a.sp 4) = N at *
    generalize hD : diffOf (k0N a row) k2 N (u8 a.sp 4 + 1) = D at *
    have hu1 : u16 st.fm 1 = u8 a.sp 4 + 1 := hfil 1 (by omega) (by omega)
    have hu2 : u16 st.fm 2 = u8 a.sp 4 + 1 := hfil 2 (by omega) (by omega)
    have hlc := a1_lcpi8_load hm
    have hld := a1_fm4_load hm hfm
    have hst := a1_fm4_store hm hfm
    simp only [arg1] at hld hst
    simp only [B.L1ed8]
    vcgen
    all_goals try subst s₀
    all_goals try subst n
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hdx, hcx,
      hsi, h13, AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat,
      BitVec.add_zero]
    · exact (show (loadInt _ (lab "LCPI5_8") 4).isSome = true by rw [hlc]; rfl)
    · rw [hld]; rfl
    · rw [hld]; rfl
    · rename_i b c hc mv hmv
      rw [show ((_root_.Executable.labels cenv).label "LCPI5_8").toBitVec = lab "LCPI5_8" from rfl,
        hlc] at hc
      obtain rfl := Option.some.inj hc
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, AddrIndex.offset64_none,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at hmv
      rw [hld] at hmv
      obtain rfl := Option.some.inj hmv
      rw [BitVec.ofInt_ofBytes_toBytes 32 4 rfl]
      have hDc : D = -1 ∨ D = -2 := by omega
      simp only [BitVec.xor_self, a1_neg_setne hDc]
      subst hNdef
      refine ⟨T.L1f08.mpr ⟨row, k2, hr, hk2, hle, hq, h3, ⟨hC, hBO, ⟨?_, ?_⟩,
        { st with fm := wr st.fm (2 * 1) (Int.toBytes (2 * 2) _) }, fr, hx, hsp, ?_, hF,
        ⟨hk2s, ⟨h2, hxo, hnm, ?_⟩, ?_, ?_, ?_⟩, hst _⟩, ?_, ?_⟩, by var_step⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15, hdx,
        hcx, h13]
      · show (wr _ _ _).length = 98
        rw [wr_length (by rw [Int.toBytes_length, hfm]; omega), hfm]
      · simp only [RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne, ne_eq, reduceCtorEq,
          not_false_eq_true]
        have hS := a1_ed8_stepped hfm (by omega) h48 (by omega) (by (try simp only [u8] at hA4); omega) hDc hfil
        simp only [diffOf, k0N, k0A, srI, u8, u16] at hS ⊢
        rw [hD]
        exact hS

end Kraken.Examples.Sbr.Reset
