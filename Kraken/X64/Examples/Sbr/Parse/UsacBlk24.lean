import Kraken.X64.Examples.Sbr.Parse.UsacBlk23
open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse
set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true
/-! # `ff_aac_sbr_decode_usac_data`: the default header's end and the change test

`bs_interpol_freq`, `bs_smoothing_mode`; the comparison of the old bytes with the new
(`reset`), the test of `bs_limiter_bands`. -/
namespace Kraken.Examples.Sbr.Usac
variable [CodeEnv]

omit [CodeEnv] in
/-- `movzbl`, `and $1`: bit 0. -/
theorem ip_val (b : UInt8) :
    BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64
      (BitVec.setWidth 32 (BitVec.ofInt 8 (Int.ofBytes [b])))) &&& BitVec.setWidth 32 1#64))
      = BitVec.ofNat 32 (b.toNat % 2) := by
  rw [ob1v]
  cases b with | ofBitVec v => ?_
  apply BitVec.eq_of_toNat_eq
  have := v.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat, UInt8.toNat_ofBitVec,
    Nat.and_one_is_mod, Nat.reduceMod, Nat.reducePow]
  omega

omit [CodeEnv] in
/-- `mov` (4 bytes), `shr $1`, `and $1`: bit 1 of the first byte. -/
theorem sm_val (b : UInt8) (r : List UInt8) :
    BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64
      ((BitVec.setWidth 32 (BitVec.setWidth 64
        (BitVec.ofInt 32 (Int.ofBytes (b :: r))))).ushiftRight 1)) &&& BitVec.setWidth 32 1#64))
      = BitVec.ofNat 32 (b.toNat / 2 % 2) := by
  have e : Int.ofBytes (b :: r) = Int.ofBytes r * 256 + (b.toNat : Int) := rfl
  rw [e]
  apply BitVec.eq_of_toNat_eq
  have := b.toNat_lt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ushiftRight,
    BitVec.toNat_ofInt, Nat.and_one_is_mod, Nat.reduceMod, Nat.reducePow, BitVec.ushiftRight_eq,
    Nat.shiftRight_eq_div_pow, Nat.pow_one]
  omega

omit [CodeEnv] in
theorem drop_take_cons (l : List UInt8) (j n : Nat) (hj : j < l.length) :
    (l.drop j).take (n + 1) = l.getD j 0 :: (l.drop (j + 1)).take n := by
  induction j generalizing l with
  | zero => cases l <;> simp_all
  | succ j ih =>
    cases l with
    | nil => simp at hj
    | cons x l =>
      simp only [List.drop_succ_cons, List.getD_cons_succ]
      exact ih l (by simp at hj; omega)

set_option maxRecDepth 20000 in
/-- `bs_interpol_freq`, `bs_smoothing_mode` (bits 0, 1 of byte 8). -/
theorem blk_L354e (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L354e" := by
  cfg_block
  measure_hb "L354e"
    intro n
    simp only [tbl_L354e, var_L354e]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, hdx, st, hI, hS, -, hax, hm⟩, hcx⟩, h15⟩ :=
      hs₀.1
    obtain rfl := hs₀.2
    have hlen : A.1.uev.length = 12 := hF.1.2.2.2.2.1.1
    have m0 : s₀.dmem =⋆ UM k A ra t₀ (LocT (t₀.regs.get64 .rsp) (ivv t₀) (st.sp.take 4)
        (st.sp.drop 4)) (Sv t₀) (dhD A.1 st) := hm
    have lu8 : s₀.dmem.loadInt (A.1.ue + 20#64) 1 = some (Int.ofBytes ((A.1.uev.drop 8).take 1)) :=
      um_loadUe m0 hlen 8 1 (by omega) _ (by bv_omega)
    have lu84 : ∀ v : BitVec 32, (s₀.dmem.storeInt (A.1.c + 166228#64) 4 v.toInt).loadInt
        (A.1.ue + 20#64) 4 = some (Int.ofBytes ((A.1.uev.drop 8).take 4)) := fun v =>
      um_loadUe (um_storeIp m0 _ (by (try simp only [sA]); bv_omega) v) hlen 8 4 (by omega) _
        (by bv_omega)
    have ldi : (s₀.dmem.loadInt (A.1.c + 166228#64) 4).isSome = true :=
      um_loadIp m0 _ (by (try simp only [sA]); bv_omega)
    have lds : ∀ v : BitVec 32,
        ((s₀.dmem.storeInt (A.1.c + 166228#64) 4 v.toInt).loadInt (A.1.c + 166232#64) 4).isSome
          = true := fun v =>
      um_loadSm (um_storeIp m0 _ (by (try simp only [sA]); bv_omega) v) _
        (by (try simp only [sA]); bv_omega)
    have hst : ∀ v1 v2 : BitVec 32, v1 = BitVec.ofNat 32 (u8 A.1.uev 8 % 2) →
        v2 = BitVec.ofNat 32 (u8 A.1.uev 8 / 2 % 2) →
        UM k A ra t₀ (LocT (t₀.regs.get64 .rsp) (ivv t₀) (st.sp.take 4) (st.sp.drop 4)) (Sv t₀)
          (dh A.1 st)
          ((s₀.dmem.storeInt (A.1.c + 166228#64) 4 v1.toInt).storeInt (A.1.c + 166232#64) 4
            v2.toInt) := by
      intro v1 v2 e1 e2
      have := um_storeSm (um_storeIp m0 (A.1.c + 166228#64) (by (try simp only [sA]); bv_omega) v1)
        (A.1.c + 166232#64) (by (try simp only [sA]); bv_omega) v2
      subst e1 e2
      simp only [UM, UF, SHW, dh, dhD] at this ⊢
      exact this
    have hbxc : PLift (s₀.regs.get64 .rbx = A.1.c) := ⟨hbx⟩
    have hcxc : PLift (s₀.regs.get64 .rcx = BitVec.ofNat 64 (u8 A.1.uev 6)) := ⟨hcx⟩
    have hdxc : PLift (s₀.regs.get64 .rdx = A.1.ue) := ⟨hdx⟩
    generalize UM k A ra t₀ (LocT (t₀.regs.get64 .rsp) (ivv t₀) (st.sp.take 4) (st.sp.drop 4))
      (Sv t₀) (dhD A.1 st) = P at hm
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ofNat_eq_ofNat, BitVec.add_zero, hbxc.down, hdxc.down] at *
    all_goals try simp only [lu8, lu84, ldi, lds, Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    refine ⟨?_, by simp only [var_L3569]; omega⟩
    rw [tbl_L3569]
    unfold T_L3569
    refine ⟨⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ⟨st, hI, hS, ?_, ?mem⟩, ?_⟩, ?_⟩
    case mem =>
      exact hst _ _ (by rw [drop_take1 _ _ (by omega), ip_val])
        (by rw [drop_take_cons _ _ _ (by omega), sm_val])
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]
    all_goals first
      | exact hsp | exact hbp | exact h12 | exact h14 | exact hbxc.down | exact hcxc.down
      | exact h13 | exact hax | exact h15

omit [CodeEnv] in
theorem ofInt_inj4 (a b : List UInt8) (ha : a.length = 4) (hb : b.length = 4)
    (h : BitVec.ofInt 32 (Int.ofBytes a) = BitVec.ofInt 32 (Int.ofBytes b)) : a = b := by
  have e := congrArg (fun x : BitVec 32 => Int.toBytes 4 x.toInt) h
  rw [tb_ofInt 4, tb_ofInt 4, ← ha, Int.toBytes_ofBytes_all, ha, ← hb,
    Int.toBytes_ofBytes_all] at e
  exact e

omit [CodeEnv] in
theorem ofInt_inj2 (a b : List UInt8) (ha : a.length = 2) (hb : b.length = 2)
    (h : BitVec.ofInt 16 (Int.ofBytes a) = BitVec.ofInt 16 (Int.ofBytes b)) : a = b := by
  have e := congrArg (fun x : BitVec 16 => Int.toBytes 2 x.toInt) h
  rw [tb_ofInt 2, tb_ofInt 2, ← ha, Int.toBytes_ofBytes_all, ha, ← hb,
    Int.toBytes_ofBytes_all] at e
  exact e

omit [CodeEnv] in
/-- The test of L3569: `xor` of the old and new words, `or`, `je`. -/
theorem zcmp (x4 y4 : BitVec 32) (x2 y2 : BitVec 16) :
    (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 16
      ((BitVec.setWidth 64 (BitVec.setWidth 32 x2)).replaceLow
        (BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32 x2)) ^^^ y2))))) |||
      BitVec.setWidth 32 (BitVec.setWidth 64
        (BitVec.setWidth 32 (BitVec.setWidth 64 x4) ^^^ y4)) == BitVec.zero 32) = true
      ↔ x4 = y4 ∧ x2 = y2 := by
  have e1 : ∀ y : BitVec 32, BitVec.setWidth 32 (BitVec.setWidth 64 y) = y :=
    fun y => by apply BitVec.eq_of_toNat_eq; simp
  have e2 : ∀ y : BitVec 16, BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32 y)) = y :=
    fun y => by apply BitVec.eq_of_toNat_eq; simp
  have e3 : ∀ a : BitVec 16, BitVec.setWidth 32 a = 0#32 ↔ a = 0#16 := by
    intro a; constructor
    · intro h; apply BitVec.eq_of_toNat_eq
      have h1 := congrArg BitVec.toNat h
      have h2 := a.isLt
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at h1 ⊢
      omega
    · rintro rfl; rfl
  simp only [BitVec.setWidth_replaceLow16, e1, e2, beq_iff_eq, BitVec.zero_eq,
    BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff, e3]
  exact and_comm

omit [CodeEnv] in
theorem sp_eq (a b : List UInt8) (h4 : a.take 4 = b.take 4) (h2 : a.drop 4 = b.drop 4) :
    a = b := by
  rw [← List.take_append_drop 4 a, h4, h2, List.take_append_drop]

omit [CodeEnv] in
theorem dhR_eq (q : UQ) (st : USt) (h : dsp q st = st.sp) (h0 : st.x.reset = 0#32) :
    dhR q st = dh q st := by
  unfold dhR
  rw [ite_cond_eq_true _ _ (eq_true h), ← h0]
  rfl

set_option maxRecDepth 20000 in
/-- The change test: the old bytes against the new; `reset = 1` if they differ. -/
theorem blk_L3569 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L3569" := by
  cfg_block
  measure_hb "L3569"
    intro n
    simp only [tbl_L3569, var_L3569]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, ⟨st, hI, hS, hax, hm⟩, hcx⟩, h15⟩ := hs₀.1
    obtain rfl := hs₀.2
    have hsl : st.sp.length = 6 := hI.2.1.1
    have hm2 := hm
    simp only [UM, UF, SHW, LocT] at hm2
    have la : s₀.dmem.loadInt (t₀.regs.get64 .rsp - 8#64 + (-52 : Int64).toBitVec) 4
        = some (Int.ofBytes (st.sp.take 4)) := by
      rw [show t₀.regs.get64 .rsp - 8#64 + (-52 : Int64).toBitVec = t₀.regs.get64 .rsp - 60#64 by
        rw [show (-52 : Int64).toBitVec = -52#64 from rfl]; bv_omega]
      sep_mem hm2 <;> simp [hsl, List.take_take]
    have lb : s₀.dmem.loadInt (t₀.regs.get64 .rsp - 8#64 + (-48 : Int64).toBitVec) 2
        = some (Int.ofBytes (st.sp.drop 4)) := by
      rw [show t₀.regs.get64 .rsp - 8#64 + (-48 : Int64).toBitVec = t₀.regs.get64 .rsp - 56#64 by
        rw [show (-48 : Int64).toBitVec = -48#64 from rfl]; bv_omega]
      have e : st.sp.drop 4 = (st.sp.drop 4).take 2 :=
        (List.take_of_length_le (by simp [hsl])).symm
      rw [e]
      sep_mem hm2 <;> simp [hsl]
    clear hm2
    have hdl : (dsp A.1 st).length = 6 := by simp [dsp, hsl]
    have m0 : s₀.dmem =⋆ UM k A ra t₀ (LocT (t₀.regs.get64 .rsp) (ivv t₀) (st.sp.take 4)
        (st.sp.drop 4)) (Sv t₀) (dh A.1 st) := hm
    have lc : s₀.dmem.loadInt (A.1.c + 166204#64) 4
        = some (Int.ofBytes ((dsp A.1 st).take 4)) := by
      rw [um_loadSpT m0 hdl 0 4 (by omega) _ (by (try simp only [sA]); bv_omega)]
      simp [dh, List.take_take]
    have ld : s₀.dmem.loadInt (A.1.c + 166208#64) 2
        = some (Int.ofBytes ((dsp A.1 st).drop 4)) := by
      rw [um_loadSpD m0 hdl 0 2 (by omega) _ (by (try simp only [sA]); bv_omega)]
      simp only [dh, List.drop_zero]
      rw [List.take_of_length_le (by simp [hdl])]
    have ldr : (s₀.dmem.loadInt (A.1.c + 166200#64) 4).isSome = true :=
      um_loadRst m0 _ (by (try simp only [sA]); bv_omega)
    have hJ : PLift (dsp A.1 st = st.sp → UM k A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀))
        (Sv t₀) (dhR A.1 st) s₀.dmem) := ⟨fun he => by
      rw [dhR_eq _ _ he hS.1.2.1]
      exact um_forgetLoc (by simp [hsl]) (by simp [hsl]) m0⟩
    have hN : PLift (dsp A.1 st ≠ st.sp → ∀ v : BitVec 32, v = 1#32 →
        UM k A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) (Sv t₀) (dhR A.1 st)
          (s₀.dmem.storeInt (A.1.c + 166200#64) 4 v.toInt)) := ⟨fun hne v hv => by
      subst hv
      have := um_forgetLoc (by simp [hsl]) (by simp [hsl])
        (um_storeRst m0 (A.1.c + 166200#64) (by (try simp only [sA]); bv_omega) 1#32)
      unfold dhR
      rw [ite_cond_eq_false _ _ (eq_false hne)]
      exact this⟩
    have key := zcmp (BitVec.ofInt 32 (Int.ofBytes (st.sp.take 4)))
      (BitVec.ofInt 32 (Int.ofBytes ((dsp A.1 st).take 4)))
      (BitVec.ofInt 16 (Int.ofBytes (st.sp.drop 4)))
      (BitVec.ofInt 16 (Int.ofBytes ((dsp A.1 st).drop 4)))
    have hiff : (BitVec.ofInt 32 (Int.ofBytes (st.sp.take 4))
        = BitVec.ofInt 32 (Int.ofBytes ((dsp A.1 st).take 4))
        ∧ BitVec.ofInt 16 (Int.ofBytes (st.sp.drop 4))
          = BitVec.ofInt 16 (Int.ofBytes ((dsp A.1 st).drop 4))) ↔ dsp A.1 st = st.sp := by
      constructor
      · rintro ⟨h4, h2⟩
        exact (sp_eq _ _ (ofInt_inj4 _ _ (by simp [hsl]) (by simp [hdl]) h4)
          (ofInt_inj2 _ _ (by simp [hsl]) (by simp [hdl]) h2)).symm
      · intro he; rw [he]; exact ⟨rfl, rfl⟩
    rw [hiff] at key
    have hbxc : PLift (s₀.regs.get64 .rbx = A.1.c) := ⟨hbx⟩
    have hbpc : PLift (s₀.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64) := ⟨hbp⟩
    have hcxc : PLift (s₀.regs.get64 .rcx = BitVec.ofNat 64 (u8 A.1.uev 6)) := ⟨hcx⟩
    generalize UM k A ra t₀ (LocT (t₀.regs.get64 .rsp) (ivv t₀) (st.sp.take 4) (st.sp.drop 4))
      (Sv t₀) (dh A.1 st) = P at hm
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ofNat_eq_ofNat, BitVec.add_zero, hbxc.down, hbpc.down] at *
    all_goals try simp only [la, lb, lc, ld, ldr, Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    · rename_i hc
      simp only [CondCode.interp, StatusFlags.from_result, key] at hc
      left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, ?_⟩
      · rw [tbl_L358e]
        unfold T_L358e
        refine ⟨⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, st, hI, hS, ?_, hJ.down hc⟩, ?_⟩
        all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]
        all_goals first
          | exact hsp | exact hbp | exact h12 | exact h14 | exact hbxc.down | exact hcxc.down
          | exact h13 | exact hax | exact h15 | exact hbpc.down
      · first
          | exact Or.inr ⟨by simp only [var_L358e], by decide⟩
          | exact Or.inl (by simp only [var_L358e]; omega)
    · rename_i hc
      have hne : dsp A.1 st ≠ st.sp := by
        simp only [CondCode.interp, StatusFlags.from_result] at hc
        intro he
        rw [← key] at he
        rw [he] at hc
        exact Bool.noConfusion hc
      refine ⟨?_, by simp only [var_L358e]; omega⟩
      rw [tbl_L358e]
      unfold T_L358e
      refine ⟨⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, st, hI, hS, ?_, hN.down hne _ (by decide)⟩, ?_⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]
      all_goals first
        | exact hsp | exact hbp | exact h12 | exact h14 | exact hbxc.down | exact hcxc.down
        | exact h13 | exact hax | exact h15 | exact hbpc.down

end Kraken.Examples.Sbr.Usac
