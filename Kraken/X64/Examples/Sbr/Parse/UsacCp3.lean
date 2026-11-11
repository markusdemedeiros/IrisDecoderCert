import Kraken.X64.Examples.Sbr.Parse.UsacCp2
open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse
set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true
set_option linter.unusedSimpArgs false
/-! # `ff_aac_sbr_decode_usac_data`: the inlined `copy_sbr_grid` (`L377f`..`L37cb`)

`t_env[8]`, `t_q[0..1]` (`cpC`); `t_q[2]`, `bs_num_env` (`cpD`); `bs_num_noise` (`cpE`, with a
raw `int`); two raw `int`s, after which channel 1 is `copyGrid` (`se01_cp`). -/
namespace Kraken.Examples.Sbr.Usac
variable [CodeEnv]

omit [CodeEnv] in
theorem b2_of (bs : List UInt8) (h : bs.length = 2) :
    Int.toBytes 2 (BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32
      (BitVec.ofInt 16 (Int.ofBytes bs))))).toInt = bs := by
  rw [show ∀ x : BitVec 16, BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32 x)) = x
    from fun x => by bv_omega]
  exact tb_of 2 bs h

omit [CodeEnv] in
theorem b4_of (bs : List UInt8) (h : bs.length = 4) :
    Int.toBytes 4 (BitVec.setWidth 32 (BitVec.setWidth 64
      (BitVec.ofInt 32 (Int.ofBytes bs)))).toInt = bs := by
  rw [sw32]; exact tb_of 4 bs h

/-- `L377f`: `cpC`. -/
theorem blk_L377f (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L377f" := by
  cfg_block
  measure_hb "L377f"
    intro n
    simp only [tbl_L377f, var_L377f, tbl_L379a, var_L379a]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, -, -, -, -⟩, h15⟩, st, hI, hP, hc, hn9,
      hm⟩, rfl⟩ := hs₀
    have hbxc : PLift (s₀.regs.get64 .rbx = A.1.c) := ⟨hbx⟩
    have hd0 : DWF False st.x.d0 := hP.1.1.1.2.2.1
    have hd1 : DWF False st.x.d1 := hP.1.1.1.2.2.2.1
    have hte0 : st.x.d0.te.length = 10 := hd0.2.2.1
    have htq0 : st.x.d0.tq.length = 3 := hd0.2.2.2.1
    have hte : (cpB st.x.d0 st.x.d1).te.length = 10 := by simp [cpB, cpA, hd1.2.2.1, hte0]
    have htq : (cpB st.x.d0 st.x.d1).tq.length = 3 := by simp [cpB, cpA, hd1.2.2.2.1]
    have L1 := um_load0Te hm hte0 8 1 (by omega) (A.1.c + 255044#64)
      (by simp only [dAc, sA]; bv_omega)
    have S1 := um_load1Te hm hte 8 1 (by omega) (A.1.c + 343812#64)
      (by simp only [dAc, sA]; bv_omega)
    have hm1 := fun val => um_store1Te hm hte 8 1 (by omega) (A.1.c + 343812#64)
      (by simp only [dAc, sA]; bv_omega) val
    have L3 := fun val => um_load0Tq (hm1 val) htq0 0 2 (by omega) (A.1.c + 255046#64)
      (by simp only [dAc, sA]; bv_omega)
    have S3 := fun val => um_load1Tq (hm1 val) htq 0 2 (by omega) (A.1.c + 343814#64)
      (by simp only [dAc, sA]; bv_omega)
    have hmF : PLift (∀ bs1 bs2 : List UInt8, bs1.length = 1 → bs2.length = 2 →
        ((s₀.dmem.storeInt (A.1.c + 343812#64) 1 (BitVec.setWidth 8 (BitVec.setWidth 64
          (BitVec.setWidth 32 (BitVec.ofInt 8 (Int.ofBytes bs1))))).toInt).storeInt
          (A.1.c + 343814#64) 2 (BitVec.setWidth 16 (BitVec.setWidth 64
          (BitVec.setWidth 32 (BitVec.ofInt 16 (Int.ofBytes bs2))))).toInt)
        =⋆ UM k A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) (Sv t₀)
          (st.wd1 { cpB st.x.d0 st.x.d1 with
            te := List.take 8 (cpB st.x.d0 st.x.d1).te ++ bs1
              ++ List.drop (8 + 1) (cpB st.x.d0 st.x.d1).te,
            tq := List.take 0 (cpB st.x.d0 st.x.d1).tq ++ bs2
              ++ List.drop (0 + 2) (cpB st.x.d0 st.x.d1).tq })) := by
      refine ⟨fun bs1 bs2 h1 h2 => ?_⟩
      have := um_store1Tq (hm1 (BitVec.setWidth 8 (BitVec.setWidth 64
          (BitVec.setWidth 32 (BitVec.ofInt 8 (Int.ofBytes bs1))))).toInt) htq 0 2 (by omega)
        (A.1.c + 343814#64) (by simp only [dAc, sA]; bv_omega)
        (BitVec.setWidth 16 (BitVec.setWidth 64
          (BitVec.setWidth 32 (BitVec.ofInt 16 (Int.ofBytes bs2))))).toInt
      rw [b1_of _ h1, b2_of _ h2] at this
      exact this
    have eC : cpC st.x.d0 st.x.d1 = { cpB st.x.d0 st.x.d1 with
        te := List.take 8 (cpB st.x.d0 st.x.d1).te ++ (st.x.d0.te.drop 8).take 1
          ++ List.drop (8 + 1) (cpB st.x.d0 st.x.d1).te,
        tq := List.take 0 (cpB st.x.d0 st.x.d1).tq ++ (st.x.d0.tq.drop 0).take 2
          ++ List.drop (0 + 2) (cpB st.x.d0 st.x.d1).tq } := by
      unfold cpC
      rw [tk1 _ _ (by omega), ← splice1 _ _ _ (by omega)]
      simp only [List.take_zero, List.drop_zero, List.nil_append, Nat.zero_add]
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
      simp only [T_L379a, AtCq, AtD, AtI, At, Reg64s.get64_set64, reduceCtorEq, ite_true,
        ite_false]
      refine ⟨⟨⟨hF, ⟨hsp, hbp, h12, hbxc.down, h14⟩, h13, st.wd1 (cpC st.x.d0 st.x.d1), hI,
        trivial, ?_⟩, h15⟩, st, hI, hP, hc, hn9, ?_⟩ <;>
      (rw [eC]; exact hmF.down _ _ (by simp; omega) (by simp; omega))

/-- `L379a`: `cpD`. -/
theorem blk_L379a (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L379a" := by
  cfg_block
  measure_hb "L379a"
    intro n
    simp only [tbl_L379a, var_L379a, tbl_L37b3, var_L37b3]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, -, -, -, -⟩, h15⟩, st, hI, hP, hc, hn9,
      hm⟩, rfl⟩ := hs₀
    have hbxc : PLift (s₀.regs.get64 .rbx = A.1.c) := ⟨hbx⟩
    have hd0 : DWF False st.x.d0 := hP.1.1.1.2.2.1
    have hd1 : DWF False st.x.d1 := hP.1.1.1.2.2.2.1
    have htq0 : st.x.d0.tq.length = 3 := hd0.2.2.2.1
    have htq : (cpC st.x.d0 st.x.d1).tq.length = 3 := by
      simp [cpC, cpB, cpA, hd1.2.2.2.1, htq0]
    have L1 := um_load0Tq hm htq0 2 1 (by omega) (A.1.c + 255048#64)
      (by simp only [dAc, sA]; bv_omega)
    have S1 := um_load1Tq hm htq 2 1 (by omega) (A.1.c + 343816#64)
      (by simp only [dAc, sA]; bv_omega)
    have hm1 := fun val => um_store1Tq hm htq 2 1 (by omega) (A.1.c + 343816#64)
      (by simp only [dAc, sA]; bv_omega) val
    have L3 := fun val => um_load0Ne (hm1 val) (A.1.c + 166312#64)
      (by simp only [dAc, sA]; bv_omega)
    have S3 := fun val => um_load1Ne (hm1 val) (A.1.c + 255080#64)
      (by simp only [dAc, sA]; bv_omega)
    have hmF : PLift (∀ bs1 : List UInt8, bs1.length = 1 →
        ((s₀.dmem.storeInt (A.1.c + 343816#64) 1 (BitVec.setWidth 8 (BitVec.setWidth 64
          (BitVec.setWidth 32 (BitVec.ofInt 8 (Int.ofBytes bs1))))).toInt).storeInt
          (A.1.c + 255080#64) 4 (BitVec.setWidth 32 (BitVec.setWidth 64
          (BitVec.ofInt 32 (Int.ofBytes (Int.toBytes 4 (st.x.d0.nenv : Int)))))).toInt)
        =⋆ UM k A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) (Sv t₀)
          (st.wd1 { cpC st.x.d0 st.x.d1 with
            tq := List.take 2 (cpC st.x.d0 st.x.d1).tq ++ bs1
              ++ List.drop (2 + 1) (cpC st.x.d0 st.x.d1).tq,
            nenv := st.x.d0.nenv })) := by
      refine ⟨fun bs1 h1 => ?_⟩
      have := um_store1Ne (hm1 (BitVec.setWidth 8 (BitVec.setWidth 64
          (BitVec.setWidth 32 (BitVec.ofInt 8 (Int.ofBytes bs1))))).toInt)
        (A.1.c + 255080#64) (by simp only [dAc, sA]; bv_omega) _ st.x.d0.nenv
        (b4_of _ (Int.toBytes_length 4 _))
      rw [b1_of _ h1] at this
      exact this
    have eD : cpD st.x.d0 st.x.d1 = { cpC st.x.d0 st.x.d1 with
        tq := List.take 2 (cpC st.x.d0 st.x.d1).tq ++ (st.x.d0.tq.drop 2).take 1
          ++ List.drop (2 + 1) (cpC st.x.d0 st.x.d1).tq,
        nenv := st.x.d0.nenv } := by
      unfold cpD
      rw [tk1 _ _ (by omega), ← splice1 _ _ _ (by omega)]
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
      simp only [T_L37b3, AtCq, AtD, AtI, At, Reg64s.get64_set64, reduceCtorEq, ite_true,
        ite_false]
      refine ⟨⟨⟨hF, ⟨hsp, hbp, h12, hbxc.down, h14⟩, h13, st.wd1 (cpD st.x.d0 st.x.d1), hI,
        trivial, ?_⟩, h15⟩, st, hI, hP, hc, hn9, ?_⟩ <;>
      (rw [eD]; exact hmF.down _ (by simp; omega))

/-- `L37b3`: a raw `int`, `bs_num_noise` (`cpE`). -/
theorem blk_L37b3 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L37b3" := by
  cfg_block
  measure_hb "L37b3"
    intro n
    simp only [tbl_L37b3, var_L37b3, tbl_L37cb, var_L37cb]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, -, -, -, -⟩, h15⟩, st, hI, hP, hc, hn9,
      hm⟩, rfl⟩ := hs₀
    have hbxc : PLift (s₀.regs.get64 .rbx = A.1.c) := ⟨hbx⟩
    have L1 := um_load0R64 hm (A.1.c + 166404#64) (by simp only [dAc, sA]; bv_omega)
    have S1 := um_load1R64 hm (A.1.c + 255172#64) (by simp only [dAc, sA]; bv_omega)
    have hm1 := fun val => um_store1R64 hm (A.1.c + 255172#64)
      (by simp only [dAc, sA]; bv_omega) val
    have L3 := fun val => um_load0Nn (hm1 val) (A.1.c + 166328#64)
      (by simp only [dAc, sA]; bv_omega)
    have S3 := fun val => um_load1Nn (hm1 val) (A.1.c + 255096#64)
      (by simp only [dAc, sA]; bv_omega)
    have hmF : PLift (∀ val,
        ((s₀.dmem.storeInt (A.1.c + 255172#64) 4 val).storeInt
          (A.1.c + 255096#64) 4 (BitVec.setWidth 32 (BitVec.setWidth 64
          (BitVec.ofInt 32 (Int.ofBytes (Int.toBytes 4 (st.x.d0.nnoise : Int)))))).toInt)
        =⋆ UM k A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) (Sv t₀)
          (st.wd1 (cpE st.x.d0 st.x.d1))) :=
      ⟨fun val => um_store1Nn (hm1 val) (A.1.c + 255096#64) (by simp only [dAc, sA]; bv_omega)
        _ st.x.d0.nnoise (b4_of _ (Int.toBytes_length 4 _))⟩
    clear hm1
    generalize UM k A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) (Sv t₀) _ = P at hm
    vcgen
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true,
      ite_false, Int64.toBitVec_ofNat_norm, AddrIndex.offset64_none, AddrIndex.offset64_scale1,
      BitVec.add_zero, BitVec.ofNat_eq_ofNat, hbxc.down] at *
    all_goals try simp only [L1, S1, L3, S3, Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try exact L1
    all_goals try exact S1
    all_goals try exact L3 _
    all_goals try exact S3 _
    all_goals
      refine ⟨?_, Nat.le_refl _⟩
      simp only [T_L37cb, AtCq, AtD, AtI, At, Reg64s.get64_set64, reduceCtorEq, ite_true,
        ite_false]
      refine ⟨⟨⟨hF, ⟨hsp, hbp, h12, hbxc.down, h14⟩, h13, st.wd1 (cpE st.x.d0 st.x.d1), hI,
        trivial, ?_⟩, h15⟩, st, hI, hP, hc, hn9, ?_⟩ <;> exact hmF.down _

/-- `L37cb`: two raw `int`s; channel 1 is now `copyGrid` (`SE01`). -/
theorem blk_L37cb (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L37cb" := by
  cfg_block
  measure_hb "L37cb"
    intro n
    simp only [tbl_L37cb, var_L37cb, tbl_L37e3, var_L37e3]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, -, -, -, -⟩, h15⟩, st, hI, hP, hc, hn9,
      hm⟩, rfl⟩ := hs₀
    have hbxc : PLift (s₀.regs.get64 .rbx = A.1.c) := ⟨hbx⟩
    have L1 := um_load0R0 hm (A.1.c + 166304#64) (by simp only [dAc, sA]; bv_omega)
    have S1 := um_load1R0 hm (A.1.c + 255072#64) (by simp only [dAc, sA]; bv_omega)
    have hm1 := fun val => um_store1R0 hm (A.1.c + 255072#64)
      (by simp only [dAc, sA]; bv_omega) val
    have L3 := fun val => um_load0R3908 (hm1 val) (A.1.c + 180904#64)
      (by simp only [dAc, sA]; bv_omega)
    have S3 := fun val => um_load1R3908 (hm1 val) (A.1.c + 269672#64)
      (by simp only [dAc, sA]; bv_omega)
    have hmF : PLift (∀ val val',
        ((s₀.dmem.storeInt (A.1.c + 255072#64) 4 val).storeInt (A.1.c + 269672#64) 4 val')
        =⋆ UM k A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) (Sv t₀)
          (st.wd1 (cpE st.x.d0 st.x.d1))) :=
      ⟨fun val val' => um_store1R3908 (hm1 val) (A.1.c + 269672#64)
        (by simp only [dAc, sA]; bv_omega) val'⟩
    have hS := se01_cp hP
    clear hm1
    generalize UM k A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) (Sv t₀) _ = P at hm
    vcgen
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true,
      ite_false, Int64.toBitVec_ofNat_norm, AddrIndex.offset64_none, AddrIndex.offset64_scale1,
      BitVec.add_zero, BitVec.ofNat_eq_ofNat, hbxc.down] at *
    all_goals try simp only [L1, S1, L3, S3, Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try exact L1
    all_goals try exact S1
    all_goals try exact L3 _
    all_goals try exact S3 _
    all_goals
      refine ⟨?_, Nat.le_refl _⟩
      simp only [T_L37e3, AtD, AtI, At, Reg64s.get64_set64, reduceCtorEq, ite_true,
        ite_false]
      exact ⟨⟨hF, ⟨hsp, hbp, h12, hbxc.down, h14⟩, h13, st.wd1 (cpE st.x.d0 st.x.d1), hI,
        hS, hmF.down _ _⟩, h15⟩

end Kraken.Examples.Sbr.Usac
