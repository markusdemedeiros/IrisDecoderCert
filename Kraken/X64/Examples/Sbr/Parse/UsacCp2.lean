import Kraken.X64.Examples.Sbr.Parse.UsacCp1
open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse
set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true
set_option linter.unusedSimpArgs false
/-! # `ff_aac_sbr_decode_usac_data`: the inlined `copy_sbr_grid` (`L3750`, `L3763`)

`L3750`: `t_env_num_env_old` test into the raw `int` at `data[1] + 0x3904`; `L3763`:
`bs_freq_res[1..8]`, `t_env[0..7]` from channel 0 (`cpB`). -/
namespace Kraken.Examples.Sbr.Usac
variable [CodeEnv]

/-- `L3750`: a store into a raw cell. -/
theorem blk_L3750 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L3750" := by
  cfg_block
  measure_hb "L3750"
    intro n
    simp only [tbl_L3750, var_L3750, tbl_L3763, var_L3763]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, -, -, -, -⟩, h15⟩, st, hI, hP, hc, hn9, hax,
      hm⟩, rfl⟩ := hs₀
    have hbxc : PLift (s₀.regs.get64 .rbx = A.1.c) := ⟨hbx⟩
    have haxc : PLift (s₀.regs.get64 .rax = BitVec.ofNat 64 st.x.d1.nenv) := ⟨hax⟩
    dsimp only at hm
    have L1 := um_load1R3908 hm (A.1.c + 269672#64) (by simp only [dAc, sA]; bv_omega)
    have S1 := um_load1R3904 hm (A.1.c + 269668#64) (by simp only [dAc, sA]; bv_omega)
    have hmF : PLift (∀ val, s₀.dmem.storeInt (A.1.c + 269668#64) 4 val
        =⋆ UM k A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) (Sv t₀) (st.wd1 (cpA st.x.d1))) :=
      ⟨fun val => um_store1R3904 hm _ (by simp only [dAc, sA]; bv_omega) val⟩
    generalize UM k A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) (Sv t₀) _ = P at hm
    vcgen
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true,
      ite_false, Int64.toBitVec_ofNat_norm, AddrIndex.offset64_none, AddrIndex.offset64_scale1,
      BitVec.add_zero, BitVec.ofNat_eq_ofNat, hbxc.down] at *
    all_goals try simp only [L1, S1, Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try exact L1
    all_goals
      refine ⟨?_, Nat.le_refl _⟩
      simp only [T_L3763, AtCp, AtD, AtI, At, Reg64s.get64_set64, reduceCtorEq, ite_true,
        ite_false]
      refine ⟨⟨⟨hF, ⟨hsp, hbp, h12, hbxc.down, h14⟩, h13, st.wd1 (cpA st.x.d1), hI, trivial, ?_⟩,
        h15⟩, st, hI, hP, hc, hn9, haxc.down, ?_⟩ <;> exact hmF.down _

omit [CodeEnv] in
theorem tb8 (bs : List UInt8) (h : bs.length = 8) :
    Int.toBytes 8 (BitVec.ofInt 64 (Int.ofBytes bs)).toInt = bs := tb_of 8 bs h

/-- `L3763`: `cpB`, two 8-byte copies. -/
theorem blk_L3763 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L3763" := by
  cfg_block
  measure_hb "L3763"
    intro n
    simp only [tbl_L3763, var_L3763, tbl_L377f, var_L377f]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, -, -, -, -⟩, h15⟩, st, hI, hP, hc, hn9, -,
      hm⟩, rfl⟩ := hs₀
    have hbxc : PLift (s₀.regs.get64 .rbx = A.1.c) := ⟨hbx⟩
    have hd0 : DWF False st.x.d0 := hP.1.1.1.2.2.1
    have hd1 : DWF False st.x.d1 := hP.1.1.1.2.2.2.1
    have hfr0 : st.x.d0.freqRes.length = 9 := hd0.1
    have hte0 : st.x.d0.te.length = 10 := hd0.2.2.1
    have hfr : (cpA st.x.d1).freqRes.length = 9 := by simp [cpA, hd1.1]
    have hte : (cpA st.x.d1).te.length = 10 := by simp [cpA, hd1.2.2.1]
    dsimp only at hm
    have L1 := um_load0Fr hm hfr0 1 8 (by omega) (A.1.c + 166317#64)
      (by simp only [dAc, sA]; bv_omega)
    have S1 := um_load1Fr hm hfr 1 8 (by omega) (A.1.c + 255085#64)
      (by simp only [dAc, sA]; bv_omega)
    have hm1 := fun val => um_store1Fr hm hfr 1 8 (by omega) (A.1.c + 255085#64)
      (by simp only [dAc, sA]; bv_omega) val
    have L3 := fun val => um_load0Te (hm1 val) hte0 0 8 (by omega) (A.1.c + 255036#64)
      (by simp only [dAc, sA]; bv_omega)
    have S3 := fun val => um_load1Te (hm1 val) hte 0 8 (by omega) (A.1.c + 343804#64)
      (by simp only [dAc, sA]; bv_omega)
    have hmF : PLift (∀ bs1 bs2 : List UInt8, bs1.length = 8 → bs2.length = 8 →
        ((s₀.dmem.storeInt (A.1.c + 255085#64) 8 (BitVec.ofInt 64 (Int.ofBytes bs1)).toInt).storeInt
          (A.1.c + 343804#64) 8 (BitVec.ofInt 64 (Int.ofBytes bs2)).toInt)
        =⋆ UM k A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) (Sv t₀) (st.wd1 { cpA st.x.d1 with
          freqRes := List.take 1 (cpA st.x.d1).freqRes ++ bs1
            ++ List.drop (1 + 8) (cpA st.x.d1).freqRes,
          te := List.take 0 (cpA st.x.d1).te ++ bs2 ++ List.drop (0 + 8) (cpA st.x.d1).te })) := by
      refine ⟨fun bs1 bs2 h1 h2 => ?_⟩
      have := um_store1Te (hm1 (BitVec.ofInt 64 (Int.ofBytes bs1)).toInt) hte 0 8 (by omega)
        (A.1.c + 343804#64) (by simp only [dAc, sA]; bv_omega)
        (BitVec.ofInt 64 (Int.ofBytes bs2)).toInt
      rw [tb8 _ h1, tb8 _ h2] at this
      exact this
    have eB : cpB st.x.d0 st.x.d1 = { cpA st.x.d1 with
        freqRes := List.take 1 (cpA st.x.d1).freqRes ++ (st.x.d0.freqRes.drop 1).take 8
          ++ List.drop (1 + 8) (cpA st.x.d1).freqRes,
        te := List.take 0 (cpA st.x.d1).te ++ (st.x.d0.te.drop 0).take 8
          ++ List.drop (0 + 8) (cpA st.x.d1).te } := by
      have hdn : List.drop (1 + 8) (cpA st.x.d1).freqRes = [] :=
        List.drop_eq_nil_of_le (by simp [hfr])
      unfold cpB
      rw [hdn, List.append_nil, List.take_zero, List.drop_zero, List.nil_append]
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
      simp only [T_L377f, AtCq, AtD, AtI, At, Reg64s.get64_set64, reduceCtorEq, ite_true,
        ite_false]
      refine ⟨⟨⟨hF, ⟨hsp, hbp, h12, hbxc.down, h14⟩, h13, st.wd1 (cpB st.x.d0 st.x.d1), hI,
        trivial, ?_⟩, h15⟩, st, hI, hP, hc, hn9, ?_⟩ <;>
      (rw [eB]; exact hmF.down _ _ (by simp; omega) (by simp; omega))

end Kraken.Examples.Sbr.Usac
