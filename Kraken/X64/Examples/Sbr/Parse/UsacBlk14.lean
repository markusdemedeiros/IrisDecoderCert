import Kraken.X64.Examples.Sbr.Parse.UsacBlk13
open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse
set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true
/-! # `ff_aac_sbr_decode_usac_data`: the second byte of each pair of the harmonic loops

The second byte of the pair, `counter += 2`, the loop test (`lp_next`: the counter stays below
the bound and the rank `bound - counter` decreases) and the exits (`lp_exit`; with `n[1]` odd
the last bit, `lp_odd`). -/
namespace Kraken.Examples.Sbr.Usac
variable [CodeEnv]

omit [CodeEnv] in
theorem two_add (i : BitVec 64) : BitVec.setWidth 64 2#64 + i = i + 2#64 := by
  rw [BitVec.add_comm]; rfl

omit [CodeEnv] in
/-- The loop step: the counter `+ 2` stays below the bound, the rank decreases. -/
theorem lp_next {N : Nat} {i b : BitVec 64} (hN : N ≤ 48) (hb : b = BitVec.ofNat 64 (N / 2 * 2))
    (hev : i.toNat % 2 = 0) (hlt : i.toNat < b.toNat)
    (hne : (!b - (BitVec.setWidth 64 2#64 + i) == BitVec.zero 64) = true) :
    (BitVec.setWidth 64 2#64 + i).toNat % 2 = 0 ∧ (BitVec.setWidth 64 2#64 + i).toNat < b.toNat
    ∧ (b - (BitVec.setWidth 64 2#64 + i)).toNat < (b - i).toNat := by
  rw [two_add] at hne ⊢
  subst hb
  have e : (BitVec.ofNat 64 (N / 2 * 2)).toNat = N / 2 * 2 := by
    rw [BitVec.toNat_ofNat]; omega
  rw [e] at hlt ⊢
  have hne' : BitVec.ofNat 64 (N / 2 * 2) - (i + 2#64) ≠ 0#64 := by
    simpa [BitVec.zero_eq] using hne
  have hi : (i + 2#64).toNat = i.toNat + 2 := by rw [BitVec.toNat_add]; simp; omega
  have hne2 : (i + 2#64).toNat ≠ N / 2 * 2 := by
    intro h; apply hne'; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, h, e]; simp only [BitVec.toNat_ofNat]; omega
  refine ⟨by omega, by omega, ?_⟩
  rw [BitVec.toNat_sub, BitVec.toNat_sub, e, hi]; omega

omit [CodeEnv] in
/-- The loop exit with `n[1]` odd: the counter is `n[1] - 1`. -/
theorem lp_odd {N : Nat} {i b n : BitVec 64} (hN : N ≤ 48) (hn : n = BitVec.ofNat 64 N)
    (hb : b = BitVec.ofNat 64 (N / 2 * 2))
    (hev : i.toNat % 2 = 0) (hlt : i.toNat < b.toNat)
    (hne : (!b - (BitVec.setWidth 64 2#64 + i) == BitVec.zero 64) = false)
    (hz : (BitVec.setWidth 8 n &&& BitVec.setWidth 8 1#64 == BitVec.zero 8) = false) :
    (BitVec.setWidth 64 2#64 + i).toNat + 1 = N := by
  rw [two_add] at hne ⊢
  subst hb hn
  have e : (BitVec.ofNat 64 (N / 2 * 2)).toNat = N / 2 * 2 := by
    rw [BitVec.toNat_ofNat]; omega
  have hq : BitVec.ofNat 64 (N / 2 * 2) - (i + 2#64) = 0#64 := by
    simpa [BitVec.zero_eq] using hne
  have hi : (i + 2#64).toNat = i.toNat + 2 := by rw [BitVec.toNat_add]; simp; omega
  have hq' := congrArg BitVec.toNat hq
  rw [BitVec.toNat_sub, e, hi] at hq'
  simp only [BitVec.toNat_ofNat, Nat.zero_mod] at hq'
  have hodd : N % 2 = 1 := by
    have key : ∀ M, M ≤ 48 → (BitVec.setWidth 8 (BitVec.ofNat 64 M) &&& BitVec.setWidth 8 1#64
        == BitVec.zero 8) = false → M % 2 = 1 := by decide
    exact key N hN hz
  rw [hi]; omega

omit [CodeEnv] in
/-- The second byte of a pair is below `48`. -/
theorem lp_lt2 {st : USt} {i b n : BitVec 64} (h : Lp st i b n) (h48 : st.x.n1 ≤ 48) :
    i.toNat + 1 < 48 := by
  obtain ⟨-, rfl, h2, h3⟩ := h
  have : (BitVec.ofNat 64 (st.x.n1 / 2 * 2)).toNat = st.x.n1 / 2 * 2 := by
    rw [BitVec.toNat_ofNat]; omega
  rw [this] at h3; omega

omit [CodeEnv] in
/-- The loop exit: the counter `+ 2` is the bound. -/
theorem lp_exit {N : Nat} {i b : BitVec 64} (hb : b = BitVec.ofNat 64 (N / 2 * 2))
    (hlt : i.toNat < b.toNat)
    (hne : (!b - (BitVec.setWidth 64 2#64 + i) == BitVec.zero 64) = false) :
    BitVec.setWidth 64 2#64 + i = b := by
  rw [two_add] at hne ⊢
  have hq : b - (i + 2#64) = 0#64 := by simpa [BitVec.zero_eq] using hne
  have hq' := congrArg BitVec.toNat hq
  have hb' : b.toNat < 2 ^ 64 := b.isLt
  rw [BitVec.toNat_sub] at hq'
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add] at hq' ⊢
  simp only [BitVec.toNat_ofNat, Nat.zero_mod] at hq' ⊢
  omega

/-- The second byte of a pair of the first harmonic loop, the loop test, the exits. -/
theorem blk_L3b17 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L3b17" := by
  cfg_block
  measure_hb "L3b17"
    intro n
    simp only [tbl_L3b17, var_L3b17]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, ⟨hfin, hlp⟩, hm⟩, hax⟩, rfl⟩ := hs₀
    have hp : A.1.p8.toNat < 2 ^ 31 := hF.1.2.2.2.1.1
    have hoff := Parse.rd_off st.i A.1.p8 A.1.L hI.2.2 hF.1.2.2.2.1.2.1
    obtain ⟨F, hB⟩ := um_blocks hm
    have hbl := Blocks.loadInt_isSome hB (Blocks.Inside.base_add (n := 1)
      (x := (st.i.ushiftRight 3).setWidth 64) (by omega))
    have hst := fun v a ha w => um_storeH (um_storeI hm v) a ha w
    have hld := fun v a ha => um_loadH (um_storeI hm v) a ha
    have hm2 := hm
    simp only [UM, UF, GbU] at hm2
    have li : s₀.dmem.loadInt (A.1.g + 8#64) 4 = some (Int.ofBytes (Int.toBytes 4 st.i.toInt)) := by
      sep_mem hm2 <;> rfl
    have lp : s₀.dmem.loadInt (A.1.g + 16#64) 4
        = some (Int.ofBytes (Int.toBytes 4 A.1.p8.toInt)) := by
      sep_mem hm2 <;> rfl
    have lb : s₀.dmem.loadInt A.1.g 8 = some (Int.ofBytes (Int.toBytes 8 A.1.buf.toInt)) := by
      sep_mem hm2 <;> rfl
    clear hm2 hB
    have h14c : PLift (s₀.regs.get64 .r14 = A.1.g) := ⟨h14⟩
    generalize UM k A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) (Sv t₀) st = P at hm
    vcgen [Parse.shl_cl32_havoc]
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      AddrIndex.offset64_scale1, AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, h14,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
      BitVec.setWidth_32_64_32] at *
    all_goals try simp only [li, lp, lb, Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt64_ofBytes_toBytes8,
      BitVec.ofInt_toInt] at *
    all_goals try simp only [CondCode.interp_nz, CondCode.interp_z, StatusFlags.zf_from_result] at *
    · exact hbl
    · exact hld _ _ (by
        rw [hbx]; exact h_off _ _ _ 1 rfl (by have := lp_lt2 hlp (n1_le hfin); omega))
    · have hn := lp_next (n1_le hfin) hlp.2.1 hlp.2.2.1 hlp.2.2.2 ‹(!_ == BitVec.zero 64) = true›
      left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, Or.inl (by
        simp only [var_L3ae0, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]; omega)⟩
      rw [tbl_L3ae0]
      refine ⟨⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, _, ?inv, ?sm, hst _ _ ?hof _⟩, ?_⟩
      case inv => exact ⟨hI.1, hI.2.1, idx_le _ _ _ _ _ hI.2.2 hp⟩
      case sm =>
        refine ⟨hfin, ?_⟩
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]
        exact ⟨hlp.1, hlp.2.1, hn.1, hn.2.1⟩
      case hof => rw [hbx]; exact h_off _ _ _ 1 rfl (by have := lp_lt2 hlp (n1_le hfin); omega)
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]
      · exact hsp
      · exact hbp
      · exact h12
      · exact hbx
      · exact h14c.down
      · exact h13
      · exact hax
    · left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, Or.inl (by
        simp only [var_L36c0, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]; omega)⟩
      rw [tbl_L36c0]
      refine ⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, _, ?inv, ?sm, hst _ _ ?hof _⟩
      case inv => exact ⟨hI.1, hI.2.1, idx_le _ _ _ _ _ hI.2.2 hp⟩
      case sm => exact hfin
      case hof => rw [hbx]; exact h_off _ _ _ 1 rfl (by have := lp_lt2 hlp (n1_le hfin); omega)
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]
      · exact hsp
      · exact hbp
      · exact h12
      · exact hbx
      · exact h14c.down
      · exact h13
    · have ho := lp_odd (n1_le hfin) hlp.1 hlp.2.1 hlp.2.2.1 hlp.2.2.2
        ‹(!_ == BitVec.zero 64) = false› ‹(_ == BitVec.zero 8) = false›
      refine ⟨?_, by
        simp only [var_L3b61, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]; omega⟩
      rw [tbl_L3b61]
      refine ⟨⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, _, ?inv, ?sm, hst _ _ ?hof _⟩, ?_⟩
      case inv => exact ⟨hI.1, hI.2.1, idx_le _ _ _ _ _ hI.2.2 hp⟩
      case sm =>
        refine ⟨hfin, ?_⟩
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]
        exact ho
      case hof => rw [hbx]; exact h_off _ _ _ 1 rfl (by have := lp_lt2 hlp (n1_le hfin); omega)
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]
      · exact hsp
      · exact hbp
      · exact h12
      · exact hbx
      · exact h14c.down
      · exact h13
      · exact hax
/-- The second byte of a pair of the second harmonic loop (channel 0). -/
theorem blk_L3bd8 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L3bd8" := by
  cfg_block
  measure_hb "L3bd8"
    intro n
    simp only [tbl_L3bd8, var_L3bd8]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, ⟨hfin, hlp⟩, hm⟩, rfl⟩ := hs₀
    have hp : A.1.p8.toNat < 2 ^ 31 := hF.1.2.2.2.1.1
    have hoff := Parse.rd_off st.i A.1.p8 A.1.L hI.2.2 hF.1.2.2.2.1.2.1
    obtain ⟨F, hB⟩ := um_blocks hm
    have hbl := Blocks.loadInt_isSome hB (Blocks.Inside.base_add (n := 1)
      (x := (st.i.ushiftRight 3).setWidth 64) (by omega))
    have hst := fun v a ha w => um_storeH (um_storeI hm v) a ha w
    have hld := fun v a ha => um_loadH (um_storeI hm v) a ha
    have hm2 := hm
    simp only [UM, UF, GbU] at hm2
    have li : s₀.dmem.loadInt (A.1.g + 8#64) 4 = some (Int.ofBytes (Int.toBytes 4 st.i.toInt)) := by
      sep_mem hm2 <;> rfl
    have lp : s₀.dmem.loadInt (A.1.g + 16#64) 4
        = some (Int.ofBytes (Int.toBytes 4 A.1.p8.toInt)) := by
      sep_mem hm2 <;> rfl
    have lb : s₀.dmem.loadInt A.1.g 8 = some (Int.ofBytes (Int.toBytes 8 A.1.buf.toInt)) := by
      sep_mem hm2 <;> rfl
    clear hm2 hB
    have h14c : PLift (s₀.regs.get64 .r14 = A.1.g) := ⟨h14⟩
    generalize UM k A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) (Sv t₀) st = P at hm
    vcgen [Parse.shl_cl32_havoc]
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      AddrIndex.offset64_scale1, AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, h14,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
      BitVec.setWidth_32_64_32] at *
    all_goals try simp only [li, lp, lb, Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt64_ofBytes_toBytes8,
      BitVec.ofInt_toInt] at *
    all_goals try simp only [CondCode.interp_nz, CondCode.interp_z, StatusFlags.zf_from_result] at *
    · exact hbl
    · exact hld _ _ (by
        rw [hbx]; exact h_off _ _ _ 1 rfl (by have := lp_lt2 hlp (n1_le hfin); omega))
    · have hn := lp_next (n1_le hfin) hlp.2.1 hlp.2.2.1 hlp.2.2.2 ‹(!_ == BitVec.zero 64) = true›
      left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, Or.inl (by
        simp only [var_L3ba2, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]; omega)⟩
      rw [tbl_L3ba2]
      refine ⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, _, ?inv, ?sm, hst _ _ ?hof _⟩
      case inv => exact ⟨hI.1, hI.2.1, idx_le _ _ _ _ _ hI.2.2 hp⟩
      case sm =>
        refine ⟨hfin, ?_⟩
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]
        exact ⟨hlp.1, hlp.2.1, hn.1, hn.2.1⟩
      case hof => rw [hbx]; exact h_off _ _ _ 1 rfl (by have := lp_lt2 hlp (n1_le hfin); omega)
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]
      · exact hsp
      · exact hbp
      · exact h12
      · exact hbx
      · exact h14c.down
      · exact h13
    · left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, Or.inl (by
        simp only [var_L3c4b, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]; omega)⟩
      rw [tbl_L3c4b]
      refine ⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, _, ?inv, ?sm, hst _ _ ?hof _⟩
      case inv => exact ⟨hI.1, hI.2.1, idx_le _ _ _ _ _ hI.2.2 hp⟩
      case sm => exact ⟨hfin, trivial⟩
      case hof => rw [hbx]; exact h_off _ _ _ 1 rfl (by have := lp_lt2 hlp (n1_le hfin); omega)
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]
      · exact hsp
      · exact hbp
      · exact h12
      · exact hbx
      · exact h14c.down
      · exact h13
    · have ho := lp_odd (n1_le hfin) hlp.1 hlp.2.1 hlp.2.2.1 hlp.2.2.2
        ‹(!_ == BitVec.zero 64) = false› ‹(_ == BitVec.zero 8) = false›
      refine ⟨?_, by
        simp only [var_L3c1c, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]; omega⟩
      rw [tbl_L3c1c]
      refine ⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, _, ?inv, ?sm, hst _ _ ?hof _⟩
      case inv => exact ⟨hI.1, hI.2.1, idx_le _ _ _ _ _ hI.2.2 hp⟩
      case sm =>
        refine ⟨hfin, ?_⟩
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]
        exact ho
      case hof => rw [hbx]; exact h_off _ _ _ 1 rfl (by have := lp_lt2 hlp (n1_le hfin); omega)
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]
      · exact hsp
      · exact hbp
      · exact h12
      · exact hbx
      · exact h14c.down
      · exact h13
/-- The second byte of a pair of the coupled loop (channel 0). -/
theorem blk_L3da4 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L3da4" := by
  cfg_block
  measure_hb "L3da4"
    intro n
    simp only [tbl_L3da4, var_L3da4]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, ⟨hfin, hlp⟩, hm⟩, rfl⟩ := hs₀
    have hp : A.1.p8.toNat < 2 ^ 31 := hF.1.2.2.2.1.1
    have hoff := Parse.rd_off st.i A.1.p8 A.1.L hI.2.2 hF.1.2.2.2.1.2.1
    obtain ⟨F, hB⟩ := um_blocks hm
    have hbl := Blocks.loadInt_isSome hB (Blocks.Inside.base_add (n := 1)
      (x := (st.i.ushiftRight 3).setWidth 64) (by omega))
    have hst := fun v a ha w => um_storeH (um_storeI hm v) a ha w
    have hld := fun v a ha => um_loadH (um_storeI hm v) a ha
    have hm2 := hm
    simp only [UM, UF, GbU] at hm2
    have li : s₀.dmem.loadInt (A.1.g + 8#64) 4 = some (Int.ofBytes (Int.toBytes 4 st.i.toInt)) := by
      sep_mem hm2 <;> rfl
    have lp : s₀.dmem.loadInt (A.1.g + 16#64) 4
        = some (Int.ofBytes (Int.toBytes 4 A.1.p8.toInt)) := by
      sep_mem hm2 <;> rfl
    have lb : s₀.dmem.loadInt A.1.g 8 = some (Int.ofBytes (Int.toBytes 8 A.1.buf.toInt)) := by
      sep_mem hm2 <;> rfl
    clear hm2 hB
    have h14c : PLift (s₀.regs.get64 .r14 = A.1.g) := ⟨h14⟩
    generalize UM k A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) (Sv t₀) st = P at hm
    vcgen [Parse.shl_cl32_havoc]
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      AddrIndex.offset64_scale1, AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, h14,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
      BitVec.setWidth_32_64_32] at *
    all_goals try simp only [li, lp, lb, Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt64_ofBytes_toBytes8,
      BitVec.ofInt_toInt] at *
    all_goals try simp only [CondCode.interp_nz, CondCode.interp_z, StatusFlags.zf_from_result] at *
    · exact hbl
    · exact hld _ _ (by
        rw [hbx]; exact h_off _ _ _ 1 rfl (by have := lp_lt2 hlp (n1_le hfin); omega))
    · have hn := lp_next (n1_le hfin) hlp.2.1 hlp.2.2.1 hlp.2.2.2 ‹(!_ == BitVec.zero 64) = true›
      left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, Or.inl (by
        simp only [var_L3d6e, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]; omega)⟩
      rw [tbl_L3d6e]
      refine ⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, _, ?inv, ?sm, hst _ _ ?hof _⟩
      case inv => exact ⟨hI.1, hI.2.1, idx_le _ _ _ _ _ hI.2.2 hp⟩
      case sm =>
        refine ⟨hfin, ?_⟩
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]
        exact ⟨hlp.1, hlp.2.1, hn.1, hn.2.1⟩
      case hof => rw [hbx]; exact h_off _ _ _ 1 rfl (by have := lp_lt2 hlp (n1_le hfin); omega)
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]
      · exact hsp
      · exact hbp
      · exact h12
      · exact hbx
      · exact h14c.down
      · exact h13
    · left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, Or.inl (by
        simp only [var_L3e17, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]; omega)⟩
      rw [tbl_L3e17]
      refine ⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, _, ?inv, ?sm, hst _ _ ?hof _⟩
      case inv => exact ⟨hI.1, hI.2.1, idx_le _ _ _ _ _ hI.2.2 hp⟩
      case sm => exact ⟨hfin, trivial⟩
      case hof => rw [hbx]; exact h_off _ _ _ 1 rfl (by have := lp_lt2 hlp (n1_le hfin); omega)
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]
      · exact hsp
      · exact hbp
      · exact h12
      · exact hbx
      · exact h14c.down
      · exact h13
    · have ho := lp_odd (n1_le hfin) hlp.1 hlp.2.1 hlp.2.2.1 hlp.2.2.2
        ‹(!_ == BitVec.zero 64) = false› ‹(_ == BitVec.zero 8) = false›
      refine ⟨?_, by
        simp only [var_L3de8, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]; omega⟩
      rw [tbl_L3de8]
      refine ⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, _, ?inv, ?sm, hst _ _ ?hof _⟩
      case inv => exact ⟨hI.1, hI.2.1, idx_le _ _ _ _ _ hI.2.2 hp⟩
      case sm =>
        refine ⟨hfin, ?_⟩
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]
        exact ho
      case hof => rw [hbx]; exact h_off _ _ _ 1 rfl (by have := lp_lt2 hlp (n1_le hfin); omega)
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]
      · exact hsp
      · exact hbp
      · exact h12
      · exact hbx
      · exact h14c.down
      · exact h13
/-- The second byte of a pair of the coupled loop (channel 1). -/
theorem blk_L3ce3 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L3ce3" := by
  cfg_block
  measure_hb "L3ce3"
    intro n
    simp only [tbl_L3ce3, var_L3ce3]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, ⟨hfin, hlp⟩, hm⟩, hax⟩, rfl⟩ := hs₀
    have hp : A.1.p8.toNat < 2 ^ 31 := hF.1.2.2.2.1.1
    have hoff := Parse.rd_off st.i A.1.p8 A.1.L hI.2.2 hF.1.2.2.2.1.2.1
    obtain ⟨F, hB⟩ := um_blocks hm
    have hbl := Blocks.loadInt_isSome hB (Blocks.Inside.base_add (n := 1)
      (x := (st.i.ushiftRight 3).setWidth 64) (by omega))
    have hst := fun v a ha w => um_storeH1 (um_storeI hm v) a ha w
    have hld := fun v a ha => um_loadH1 (um_storeI hm v) a ha
    have hm2 := hm
    simp only [UM, UF, GbU] at hm2
    have li : s₀.dmem.loadInt (A.1.g + 8#64) 4 = some (Int.ofBytes (Int.toBytes 4 st.i.toInt)) := by
      sep_mem hm2 <;> rfl
    have lp : s₀.dmem.loadInt (A.1.g + 16#64) 4
        = some (Int.ofBytes (Int.toBytes 4 A.1.p8.toInt)) := by
      sep_mem hm2 <;> rfl
    have lb : s₀.dmem.loadInt A.1.g 8 = some (Int.ofBytes (Int.toBytes 8 A.1.buf.toInt)) := by
      sep_mem hm2 <;> rfl
    clear hm2 hB
    have h14c : PLift (s₀.regs.get64 .r14 = A.1.g) := ⟨h14⟩
    generalize UM k A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) (Sv t₀) st = P at hm
    vcgen [Parse.shl_cl32_havoc]
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      AddrIndex.offset64_scale1, AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, h14,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
      BitVec.setWidth_32_64_32] at *
    all_goals try simp only [li, lp, lb, Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt64_ofBytes_toBytes8,
      BitVec.ofInt_toInt] at *
    all_goals try simp only [CondCode.interp_nz, CondCode.interp_z, StatusFlags.zf_from_result] at *
    · exact hbl
    · exact hld _ _ (by
        rw [hbx]; exact h_off1 _ _ _ 1 rfl (by have := lp_lt2 hlp (n1_le hfin); omega))
    · have hn := lp_next (n1_le hfin) hlp.2.1 hlp.2.2.1 hlp.2.2.2 ‹(!_ == BitVec.zero 64) = true›
      left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, Or.inl (by
        simp only [var_L3cac, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]; omega)⟩
      rw [tbl_L3cac]
      refine ⟨⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, _, ?inv, ?sm, hst _ _ ?hof _⟩, ?_⟩
      case inv => exact ⟨hI.1, hI.2.1, idx_le _ _ _ _ _ hI.2.2 hp⟩
      case sm =>
        refine ⟨hfin, ?_⟩
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]
        exact ⟨hlp.1, hlp.2.1, hn.1, hn.2.1⟩
      case hof => rw [hbx]; exact h_off1 _ _ _ 1 rfl (by have := lp_lt2 hlp (n1_le hfin); omega)
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]
      · exact hsp
      · exact hbp
      · exact h12
      · exact hbx
      · exact h14c.down
      · exact h13
      · exact hax
    · have hx := lp_exit hlp.2.1 hlp.2.2.2 ‹(!_ == BitVec.zero 64) = false›
      refine ⟨?_, by
        simp only [var_L3d23, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]; omega⟩
      rw [tbl_L3d23]
      refine ⟨⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, _, ?inv, ?sm, hst _ _ ?hof _⟩, ?_⟩
      case inv => exact ⟨hI.1, hI.2.1, idx_le _ _ _ _ _ hI.2.2 hp⟩
      case sm =>
        refine ⟨hfin, ?_⟩
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]
        exact ⟨hlp.1, (hx.trans hlp.2.1)⟩
      case hof => rw [hbx]; exact h_off1 _ _ _ 1 rfl (by have := lp_lt2 hlp (n1_le hfin); omega)
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]
      · exact hsp
      · exact hbp
      · exact h12
      · exact hbx
      · exact h14c.down
      · exact h13
      · exact hax
/-- The second byte of a pair of the second coupled loop (channel 1). -/
theorem blk_L3eac (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L3eac" := by
  cfg_block
  measure_hb "L3eac"
    intro n
    simp only [tbl_L3eac, var_L3eac]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, ⟨hfin, hlp⟩, hm⟩, hax⟩, rfl⟩ := hs₀
    have hp : A.1.p8.toNat < 2 ^ 31 := hF.1.2.2.2.1.1
    have hoff := Parse.rd_off st.i A.1.p8 A.1.L hI.2.2 hF.1.2.2.2.1.2.1
    obtain ⟨F, hB⟩ := um_blocks hm
    have hbl := Blocks.loadInt_isSome hB (Blocks.Inside.base_add (n := 1)
      (x := (st.i.ushiftRight 3).setWidth 64) (by omega))
    have hst := fun v a ha w => um_storeH1 (um_storeI hm v) a ha w
    have hld := fun v a ha => um_loadH1 (um_storeI hm v) a ha
    have hm2 := hm
    simp only [UM, UF, GbU] at hm2
    have li : s₀.dmem.loadInt (A.1.g + 8#64) 4 = some (Int.ofBytes (Int.toBytes 4 st.i.toInt)) := by
      sep_mem hm2 <;> rfl
    have lp : s₀.dmem.loadInt (A.1.g + 16#64) 4
        = some (Int.ofBytes (Int.toBytes 4 A.1.p8.toInt)) := by
      sep_mem hm2 <;> rfl
    have lb : s₀.dmem.loadInt A.1.g 8 = some (Int.ofBytes (Int.toBytes 8 A.1.buf.toInt)) := by
      sep_mem hm2 <;> rfl
    clear hm2 hB
    have h14c : PLift (s₀.regs.get64 .r14 = A.1.g) := ⟨h14⟩
    generalize UM k A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) (Sv t₀) st = P at hm
    vcgen [Parse.shl_cl32_havoc]
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      AddrIndex.offset64_scale1, AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, h14,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
      BitVec.setWidth_32_64_32] at *
    all_goals try simp only [li, lp, lb, Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt64_ofBytes_toBytes8,
      BitVec.ofInt_toInt] at *
    all_goals try simp only [CondCode.interp_nz, CondCode.interp_z, StatusFlags.zf_from_result] at *
    · exact hbl
    · exact hld _ _ (by
        rw [hbx]; exact h_off1 _ _ _ 1 rfl (by have := lp_lt2 hlp (n1_le hfin); omega))
    · have hn := lp_next (n1_le hfin) hlp.2.1 hlp.2.2.1 hlp.2.2.2 ‹(!_ == BitVec.zero 64) = true›
      left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, Or.inl (by
        simp only [var_L3e75, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]; omega)⟩
      rw [tbl_L3e75]
      refine ⟨⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, _, ?inv, ?sm, hst _ _ ?hof _⟩, ?_⟩
      case inv => exact ⟨hI.1, hI.2.1, idx_le _ _ _ _ _ hI.2.2 hp⟩
      case sm =>
        refine ⟨hfin, ?_⟩
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]
        exact ⟨hlp.1, hlp.2.1, hn.1, hn.2.1⟩
      case hof => rw [hbx]; exact h_off1 _ _ _ 1 rfl (by have := lp_lt2 hlp (n1_le hfin); omega)
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]
      · exact hsp
      · exact hbp
      · exact h12
      · exact hbx
      · exact h14c.down
      · exact h13
      · exact hax
    · have hx := lp_exit hlp.2.1 hlp.2.2.2 ‹(!_ == BitVec.zero 64) = false›
      left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, Or.inl (by
        simp only [var_L3d23, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]; omega)⟩
      rw [tbl_L3d23]
      refine ⟨⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, _, ?inv, ?sm, hst _ _ ?hof _⟩, ?_⟩
      case inv => exact ⟨hI.1, hI.2.1, idx_le _ _ _ _ _ hI.2.2 hp⟩
      case sm =>
        refine ⟨hfin, ?_⟩
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]
        exact ⟨hlp.1, (hx.trans hlp.2.1)⟩
      case hof => rw [hbx]; exact h_off1 _ _ _ 1 rfl (by have := lp_lt2 hlp (n1_le hfin); omega)
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]
      · exact hsp
      · exact hbp
      · exact h12
      · exact hbx
      · exact h14c.down
      · exact h13
      · exact hax
end Kraken.Examples.Sbr.Usac
