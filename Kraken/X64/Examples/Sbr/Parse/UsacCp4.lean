import Kraken.X64.Examples.Sbr.Parse.UsacCp3
open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse
set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true
set_option linter.unusedSimpArgs false
/-! # `ff_aac_sbr_decode_usac_data`: the two `memcpy` of `bs_invf_mode` (`L382e`, `L3847`)

`bs_invf_mode[1]` of channel 1 from its `bs_invf_mode[0]` (`invfShift`), then its
`bs_invf_mode[0]` from channel 0's (`invfCouple`). -/
namespace Kraken.Examples.Sbr.Usac
variable [CodeEnv]

/-- Lengths of the spliced `bs_invf_mode`. -/
syntax "lenT " term : term
macro_rules | `(lenT $h) => `((by simp [Int.toBytes_length, $h:term] <;> omega))

omit [CodeEnv] in
theorem l10 (l : List UInt8) (h : l.length = 10) :
    l = [l[0], l[1], l[2], l[3], l[4], l[5], l[6], l[7], l[8], l[9]] := by
  apply List.ext_getElem
  · simp [h]
  · intro i h₁ h₂
    simp only [List.length_cons, List.length_nil] at h₂
    match i, h₂ with
    | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl
    | 5, _ => rfl | 6, _ => rfl | 7, _ => rfl | 8, _ => rfl | 9, _ => rfl

omit [CodeEnv] in
theorem shift_list (I : List UInt8) (h : I.length = 10) :
    List.take 5 (List.take 9 I ++ (I.drop 4).take 1 ++ List.drop (9 + 1) I)
      ++ (I.drop 0).take 4
      ++ List.drop (5 + 4) (List.take 9 I ++ (I.drop 4).take 1 ++ List.drop (9 + 1) I)
    = mk 10 (fun i => if i < 5 then old I i else old I (i - 5)) := by
  rw [l10 I h]; rfl

omit [CodeEnv] in
theorem shift_take4 (I : List UInt8) (h : I.length = 10) (bs : List UInt8) (hb : bs.length = 1) :
    ((List.take 9 I ++ bs ++ List.drop (9 + 1) I).drop 0).take 4 = (I.drop 0).take 4 := by
  match bs, hb with
  | [b], _ => rw [l10 I h]; rfl

omit [CodeEnv] in
theorem couple_list (I0 I : List UInt8) (h0 : I0.length = 10) (h : I.length = 10)
    (bs : List UInt8) (hb : bs.length = 4) (hbs : bs = (I0.drop 0).take 4) :
    List.take 4 (List.take 0 (mk 10 (fun i => if i < 5 then old I i else old I (i - 5))) ++ bs
        ++ List.drop (0 + 4) (mk 10 (fun i => if i < 5 then old I i else old I (i - 5))))
      ++ (I0.drop 4).take 1
      ++ List.drop (4 + 1) (List.take 0 (mk 10 (fun i => if i < 5 then old I i else old I (i - 5)))
        ++ bs ++ List.drop (0 + 4) (mk 10 (fun i => if i < 5 then old I i else old I (i - 5))))
    = mk 10 (fun i => if i < 5 then old I0 i
        else old (mk 10 (fun i => if i < 5 then old I i else old I (i - 5))) (i - 5)) := by
  subst hbs; rw [l10 I0 h0, l10 I h]; rfl

/-- `L382e`: `invfShift`. -/
theorem blk_L382e (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L382e" := by
  cfg_block
  measure_hb "L382e"
    intro n
    simp only [tbl_L382e, var_L382e, tbl_L3847, var_L3847]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, hS, hm⟩, h15⟩, -⟩, rfl⟩ := hs₀
    have hbxc : PLift (s₀.regs.get64 .rbx = A.1.c) := ⟨hbx⟩
    have hd1 : DWF False st.x.d1 := hS.1.1.1.2.2.2.1
    have hiv : st.x.d1.invf.length = 10 := hd1.2.1
    have hm' : s₀.dmem =⋆ UM k A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) (Sv t₀)
      (st.wd1 st.x.d1) := hm
    have L1 := um_load1Iv hm' hiv 4 1 (by omega) (A.1.c + 255115#64)
      (by simp only [dAc, sA]; bv_omega)
    have S1 := um_load1Iv hm' hiv 9 1 (by omega) (A.1.c + 255120#64)
      (by simp only [dAc, sA]; bv_omega)
    have hm1 := fun val => um_store1Iv hm' hiv 9 1 (by omega) (A.1.c + 255120#64)
      (by simp only [dAc, sA]; bv_omega) val
    have L3 : ∀ bs1 : List UInt8, bs1.length = 1 →
        (s₀.dmem.storeInt (A.1.c + 255120#64) 1 (BitVec.setWidth 8 (BitVec.setWidth 64
          (BitVec.setWidth 32 (BitVec.ofInt 8 (Int.ofBytes bs1))))).toInt).loadInt
          (A.1.c + 255111#64) 4 = some (Int.ofBytes ((st.x.d1.invf.drop 0).take 4)) := by
      intro bs1 h1
      rw [um_load1Iv (hm1 _) (lenT hiv) 0 4 (by omega) (A.1.c + 255111#64)
        (by simp only [dAc, sA]; bv_omega)]
      simp only [b1_of _ h1]
      rw [shift_take4 _ hiv _ h1]
    have S3 := fun val => um_load1Iv (hm1 val) (lenT hiv) 5 4 (by omega)
      (A.1.c + 255116#64) (by simp only [dAc, sA]; bv_omega)
    have hmF : PLift (∀ bs1 : List UInt8, bs1.length = 1 →
        ((s₀.dmem.storeInt (A.1.c + 255120#64) 1 (BitVec.setWidth 8 (BitVec.setWidth 64
          (BitVec.setWidth 32 (BitVec.ofInt 8 (Int.ofBytes bs1))))).toInt).storeInt
          (A.1.c + 255116#64) 4 (BitVec.setWidth 32 (BitVec.setWidth 64
          (BitVec.ofInt 32 (Int.ofBytes ((st.x.d1.invf.drop 0).take 4))))).toInt)
        =⋆ UM k A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) (Sv t₀)
          (st.wd1 { st.x.d1 with
            invf := List.take 5 (List.take 9 st.x.d1.invf ++ bs1 ++ List.drop (9 + 1) st.x.d1.invf)
              ++ (st.x.d1.invf.drop 0).take 4
              ++ List.drop (5 + 4) (List.take 9 st.x.d1.invf ++ bs1
                ++ List.drop (9 + 1) st.x.d1.invf) })) := by
      refine ⟨fun bs1 h1 => ?_⟩
      have := um_store1Iv (hm1 (BitVec.setWidth 8 (BitVec.setWidth 64
          (BitVec.setWidth 32 (BitVec.ofInt 8 (Int.ofBytes bs1))))).toInt) (lenT hiv) 5 4
        (by omega) (A.1.c + 255116#64) (by simp only [dAc, sA]; bv_omega)
        (BitVec.setWidth 32 (BitVec.setWidth 64
          (BitVec.ofInt 32 (Int.ofBytes ((st.x.d1.invf.drop 0).take 4))))).toInt
      rw [b1_of _ h1, b4_of _ (lenT hiv)] at this
      exact this
    have eS : invfShift st.x.d1 = { st.x.d1 with
        invf := List.take 5 (List.take 9 st.x.d1.invf ++ (st.x.d1.invf.drop 4).take 1
            ++ List.drop (9 + 1) st.x.d1.invf)
          ++ (st.x.d1.invf.drop 0).take 4
          ++ List.drop (5 + 4) (List.take 9 st.x.d1.invf ++ (st.x.d1.invf.drop 4).take 1
            ++ List.drop (9 + 1) st.x.d1.invf) } := by
      unfold invfShift; rw [shift_list _ hiv]
    have L3' := L3 ((st.x.d1.invf.drop 4).take 1) (by simp [hiv])
    clear hm1
    generalize UM k A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) (Sv t₀) _ = P at hm hm'
    vcgen
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true,
      ite_false, Int64.toBitVec_ofNat_norm, AddrIndex.offset64_none, AddrIndex.offset64_scale1,
      BitVec.add_zero, BitVec.ofNat_eq_ofNat, hbxc.down] at *
    all_goals try simp only [L1, S1, Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [L3', S3, Option.isSome_some,
      Option.some.injEq] at *
    all_goals try subst_vars
    all_goals
      refine ⟨?_, Nat.le_refl _⟩
      simp only [T_L3847, AtD, AtI, At, Reg64s.get64_set64, reduceCtorEq, ite_true,
        ite_false]
      refine ⟨⟨⟨hF, ⟨hsp, hbp, h12, hbxc.down, h14⟩, h13, st.wd1 (invfShift st.x.d1), hI,
        trivial, ?_⟩, h15⟩, st, hI, hS, ?_⟩ <;>
      (rw [eS]; exact hmF.down _ (by simp; omega))

/-- `L3847`: `invfCouple`. -/
theorem blk_L3847 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L3847" := by
  cfg_block
  measure_hb "L3847"
    intro n
    simp only [tbl_L3847, var_L3847, tbl_L3860, var_L3860]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, -, -, -, -⟩, h15⟩, st, hI, hS, hm⟩, rfl⟩ :=
      hs₀
    have hbxc : PLift (s₀.regs.get64 .rbx = A.1.c) := ⟨hbx⟩
    have hd0 : DWF False st.x.d0 := hS.1.1.1.2.2.1
    have hd1 : DWF False st.x.d1 := hS.1.1.1.2.2.2.1
    have hiv0 : st.x.d0.invf.length = 10 := hd0.2.1
    have hiv : st.x.d1.invf.length = 10 := hd1.2.1
    have hsv : (invfShift st.x.d1).invf.length = 10 := mk_length _ _
    have L1 := um_load0Iv hm hiv0 0 4 (by omega) (A.1.c + 166343#64)
      (by simp only [dAc, sA]; bv_omega)
    have S1 := um_load1Iv hm hsv 0 4 (by omega) (A.1.c + 255111#64)
      (by simp only [dAc, sA]; bv_omega)
    have hm1 := fun val => um_store1Iv hm hsv 0 4 (by omega) (A.1.c + 255111#64)
      (by simp only [dAc, sA]; bv_omega) val
    have L3 := fun val => um_load0Iv (hm1 val) hiv0 4 1 (by omega) (A.1.c + 166347#64)
      (by simp only [dAc, sA]; bv_omega)
    have S3 := fun val => um_load1Iv (hm1 val) (lenT hsv) 4 1 (by omega)
      (A.1.c + 255115#64) (by simp only [dAc, sA]; bv_omega)
    have hmF : PLift (∀ bs2 : List UInt8, bs2.length = 1 →
        ((s₀.dmem.storeInt (A.1.c + 255111#64) 4 (BitVec.setWidth 32 (BitVec.setWidth 64
          (BitVec.ofInt 32 (Int.ofBytes ((st.x.d0.invf.drop 0).take 4))))).toInt).storeInt
          (A.1.c + 255115#64) 1 (BitVec.setWidth 8 (BitVec.setWidth 64
          (BitVec.setWidth 32 (BitVec.ofInt 8 (Int.ofBytes bs2))))).toInt)
        =⋆ UM k A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) (Sv t₀)
          (st.wd1 { invfShift st.x.d1 with
            invf := List.take 4 (List.take 0 (invfShift st.x.d1).invf
                ++ (st.x.d0.invf.drop 0).take 4 ++ List.drop (0 + 4) (invfShift st.x.d1).invf)
              ++ bs2
              ++ List.drop (4 + 1) (List.take 0 (invfShift st.x.d1).invf
                ++ (st.x.d0.invf.drop 0).take 4 ++ List.drop (0 + 4) (invfShift st.x.d1).invf) }))
        := by
      refine ⟨fun bs2 h2 => ?_⟩
      have := um_store1Iv (hm1 (BitVec.setWidth 32 (BitVec.setWidth 64
          (BitVec.ofInt 32 (Int.ofBytes ((st.x.d0.invf.drop 0).take 4))))).toInt)
        (lenT hsv) 4 1 (by omega) (A.1.c + 255115#64) (by simp only [dAc, sA]; bv_omega)
        (BitVec.setWidth 8 (BitVec.setWidth 64
          (BitVec.setWidth 32 (BitVec.ofInt 8 (Int.ofBytes bs2))))).toInt
      rw [b4_of _ (lenT hiv0), b1_of _ h2] at this
      exact this
    have eC : invfCouple st.x.d0 (invfShift st.x.d1) = { invfShift st.x.d1 with
        invf := List.take 4 (List.take 0 (invfShift st.x.d1).invf
            ++ (st.x.d0.invf.drop 0).take 4 ++ List.drop (0 + 4) (invfShift st.x.d1).invf)
          ++ (st.x.d0.invf.drop 4).take 1
          ++ List.drop (4 + 1) (List.take 0 (invfShift st.x.d1).invf
            ++ (st.x.d0.invf.drop 0).take 4 ++ List.drop (0 + 4) (invfShift st.x.d1).invf) } := by
      unfold invfCouple invfShift
      rw [couple_list _ _ hiv0 hiv _ (lenT hiv0) rfl]
    have hS' := se01_inv hS
    clear hm1
    generalize UM k A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) (Sv t₀) _ = P at hm
    vcgen
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true,
      ite_false, Int64.toBitVec_ofNat_norm, AddrIndex.offset64_none, AddrIndex.offset64_scale1,
      BitVec.add_zero, BitVec.ofNat_eq_ofNat, hbxc.down] at *
    all_goals try simp only [L1, S1, L3, S3, Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals
      refine ⟨?_, Nat.le_refl _⟩
      simp only [T_L3860, AtD, AtI, At, Reg64s.get64_set64, reduceCtorEq, ite_true,
        ite_false]
      refine ⟨⟨hF, ⟨hsp, hbp, h12, hbxc.down, h14⟩, h13,
        st.wd1 (invfCouple st.x.d0 (invfShift st.x.d1)), hI, hS', ?_⟩, h15⟩
      rw [eC]; exact hmF.down _ (by simp; omega)

end Kraken.Examples.Sbr.Usac
