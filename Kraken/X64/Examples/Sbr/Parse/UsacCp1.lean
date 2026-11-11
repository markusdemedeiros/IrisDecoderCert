import Kraken.X64.Examples.Sbr.Parse.UsacCpL
open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse
set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true
set_option linter.unusedSimpArgs false
/-! # `ff_aac_sbr_decode_usac_data`: the inlined `copy_sbr_grid` (`L3734`)

`bs_freq_res[0]` and `t_env_num_env_old` from channel 1's own last envelope (`cpA`). -/
namespace Kraken.Examples.Sbr.Usac
variable [CodeEnv]

omit [CodeEnv] in
theorem sw8 (x : BitVec 8) : BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 x)) = x := by
  bv_omega

omit [CodeEnv] in
theorem sw32 (x : BitVec 32) : BitVec.setWidth 32 (BitVec.setWidth 64 x) = x := by
  bv_omega

omit [CodeEnv] in
theorem b1_of (bs : List UInt8) (h : bs.length = 1) :
    Int.toBytes 1 (BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32
      (BitVec.ofInt 8 (Int.ofBytes bs))))).toInt = bs := by
  rw [sw8]; exact tb_of 1 bs h

omit [CodeEnv] in
theorem tk1 (l : List UInt8) (j : Nat) (h : j < l.length) : (l.drop j).take 1 = [l.getD j 0] := by
  rw [List.drop_eq_getElem_cons h, List.take_succ_cons, List.take_zero,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

omit [CodeEnv] in
theorem splice1 (l : List UInt8) (j : Nat) (b : UInt8) (h : j < l.length) :
    l.set j b = l.take j ++ [b] ++ l.drop (j + 1) := by
  rw [List.set_eq_take_append_cons_drop, ite_eq_left_iff.mpr (fun h' => absurd h h')]; simp

/-- `L3734`: `cpA`. -/
theorem blk_L3734 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L3734" := by
  cfg_block
  measure_hb "L3734"
    intro n
    simp only [tbl_L3734, var_L3734, tbl_L3750, var_L3750]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, -, -, -, -⟩, h15⟩, st, hI, hP, hc, hn9, hax,
      hm⟩, rfl⟩ := hs₀
    have hdw : DWF False st.x.d1 := hP.1.1.1.2.2.2.1
    have hfr : st.x.d1.freqRes.length = 9 := hdw.1
    have hte : st.x.d1.te.length = 10 := hdw.2.2.1
    have hbxc : PLift (s₀.regs.get64 .rbx = A.1.c) := ⟨hbx⟩
    have haxc : PLift (s₀.regs.get64 .rax = BitVec.ofNat 64 st.x.d1.nenv) := ⟨hax⟩
    dsimp only at hm
    have hm0 := hm
    have L1 := um_load1Fr hm0 hfr st.x.d1.nenv 1 (by omega)
      (A.1.c + BitVec.ofNat 64 st.x.d1.nenv + 255084#64) (by simp only [dAc, sA]; bv_omega)
    have S1 := um_load1Fr hm0 hfr 0 1 (by omega) (A.1.c + 255084#64)
      (by simp only [dAc, sA]; bv_omega)
    have hm1 := fun val => um_store1Fr hm0 hfr 0 1 (by omega) (A.1.c + 255084#64)
      (by simp only [dAc, sA]; bv_omega) val
    have L3 := fun val => um_load1Te (hm1 val) hte st.x.d1.nenv 1 (by omega)
      (A.1.c + BitVec.ofNat 64 st.x.d1.nenv + 343804#64) (by simp only [dAc, sA]; bv_omega)
    have S3 := fun val => um_load1Te (hm1 val) hte 9 1 (by omega)
      (A.1.c + 343813#64) (by simp only [dAc, sA]; bv_omega)
    have hm2 : PLift (∀ bs1 bs2 : List UInt8, bs1.length = 1 → bs2.length = 1 →
        ((s₀.dmem.storeInt (A.1.c + 255084#64) 1 (BitVec.setWidth 8 (BitVec.setWidth 64
          (BitVec.setWidth 32 (BitVec.ofInt 8 (Int.ofBytes bs1))))).toInt).storeInt
          (A.1.c + 343813#64) 1 (BitVec.setWidth 8 (BitVec.setWidth 64
          (BitVec.setWidth 32 (BitVec.ofInt 8 (Int.ofBytes bs2))))).toInt)
        =⋆ UM k A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) (Sv t₀) (st.wd1 { st.x.d1 with
          freqRes := List.take 0 st.x.d1.freqRes ++ bs1 ++ List.drop (0 + 1) st.x.d1.freqRes,
          te := List.take 9 st.x.d1.te ++ bs2 ++ List.drop (9 + 1) st.x.d1.te })) := by
      refine ⟨fun bs1 bs2 h1 h2 => ?_⟩
      have := um_store1Te (hm1 (BitVec.setWidth 8 (BitVec.setWidth 64
          (BitVec.setWidth 32 (BitVec.ofInt 8 (Int.ofBytes bs1))))).toInt) hte 9 1 (by omega)
        (A.1.c + 343813#64)
        (by simp only [dAc, sA]; bv_omega) (BitVec.setWidth 8 (BitVec.setWidth 64
          (BitVec.setWidth 32 (BitVec.ofInt 8 (Int.ofBytes bs2))))).toInt
      rw [b1_of _ h1, b1_of _ h2] at this
      exact this
    have eA : cpA st.x.d1 = { st.x.d1 with
        freqRes := List.take 0 st.x.d1.freqRes ++ (st.x.d1.freqRes.drop st.x.d1.nenv).take 1
          ++ List.drop (0 + 1) st.x.d1.freqRes,
        te := List.take 9 st.x.d1.te ++ (st.x.d1.te.drop st.x.d1.nenv).take 1
          ++ List.drop (9 + 1) st.x.d1.te } := by
      unfold cpA
      rw [tk1 _ _ (by omega), tk1 _ _ (by omega), ← splice1 _ _ _ (by omega),
        ← splice1 _ _ _ (by omega)]
    have hmc : PLift (s₀.dmem =⋆ UM k A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) (Sv t₀)
      (st.wd1 st.x.d1)) := ⟨hm⟩
    clear hm1
    generalize UM k A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) (Sv t₀) _ = P at hm
    vcgen
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true,
      ite_false, Int64.toBitVec_ofNat_norm, AddrIndex.offset64_none, AddrIndex.offset64_scale1,
      BitVec.add_zero, hbxc.down, hax] at *
    all_goals try simp only [L1, S1, L3, S3, Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    case vc5 =>
      refine ⟨?_, Nat.le_refl _⟩
      simp only [T_L3750, AtCp, AtD, AtI, At, Reg64s.get64_set64, reduceCtorEq, ite_true,
        ite_false]
      refine ⟨⟨⟨hF, ⟨hsp, hbp, h12, hbxc.down, h14⟩, h13, st.wd1 (cpA st.x.d1), hI, trivial, ?_⟩,
        h15⟩, st, hI, hP, hc, hn9, haxc.down, ?_⟩ <;>
      (rw [eA]; exact hm2.down _ _ (by simp; omega) (by simp; omega))

end Kraken.Examples.Sbr.Usac
