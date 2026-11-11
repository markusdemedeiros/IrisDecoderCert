import Kraken.X64.Examples.Sbr.Parse.ResetA1Mem

/-!
# `sbr_reset`: `start_min`, `k[0]`, the `bs_stop_freq` dispatch (shard A1)
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Reset

variable [CodeEnv]

theorem blk_L114a (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L114a" ⟨"sbr_reset.L114a", B.L114a, some "sbr_reset.L1179"⟩ := by
  info_off
  measure_hb "L114a"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hRD, hrow⟩ := T.L114a.mp hs
    clear hs
    have hcx := hRD.2.2.2
    have hcx' : s₀.regs.rcx.toBitVec = a.x.sampleRate.setWidth 64 := hcx
    simp only [B.L114a]
    vcgen
    all_goals try subst_vars
    · decide
    · obtain ⟨row, hr, hdi⟩ := hrow
      have hlt := a.x.sampleRate.isLt
      refine ⟨T.L1179.mpr ⟨RD.congr (by simp) (by simp) rfl (by simp) (by simp) ?_ hRD,
        ⟨row, hr, ?_⟩, ?_, ?_, ?_⟩, by var_step⟩
      all_goals simp [Reg64s.get64_set64, hcx', hdi, tmpOf, Reg64s.get_low32]
      all_goals try exact hdi
      all_goals (repeat' split) <;> (apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth,
        BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow] at * <;> omega)

theorem blk_L1179 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1179" ⟨"sbr_reset.L1179", B.L1179, some "sbr_reset.L117d"⟩ := by
  info_off
  measure_hb "L1179"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hRD, ⟨row, hr, hdi⟩, hax, hsi, h8⟩ := T.L1179.mp hs
    clear hs
    have hcx : s₀.regs.rcx.toBitVec = a.x.sampleRate.setWidth 64 := hRD.2.2.2
    have hsr0 : a.x.sampleRate.toNat ≠ 0 := by
      intro h0
      have hm := rateRow_mem hr
      have : a.x.sampleRate = 0#32 := BitVec.eq_of_toNat_eq h0
      simp only [srI, this] at hm; revert hm; decide
    have hcx' : s₀.regs.get64 .rcx = a.x.sampleRate.setWidth 64 := hRD.2.2.2
    have hlt := a.x.sampleRate.isLt
    have htmp : tmpOf a.x.sampleRate.toNat ≤ 5000 := by unfold tmpOf; split <;> (try split) <;> omega
    simp only [B.L1179]
    vcgen
    all_goals try subst_vars
    refine ⟨⟨?_, ?_⟩, fun st' => ?_⟩
    · simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hcx', sw32_64]; exact hsr0
    · simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hcx', sw32_64, hax,
        BitVec.xor_self, BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat,
        BitVec.reduceSetWidth, BitVec.toNat_zero]
      apply Nat.lt_of_le_of_lt (Nat.div_le_self _ _); omega
    dsimp only
    simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hcx', sw32_64, hax,
      BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      BitVec.toNat_zero, Nat.zero_mul, Nat.zero_add, Nat.zero_mod]
    vcgen
    all_goals try subst_vars
    have hN : tmpOf a.x.sampleRate.toNat * 128 + a.x.sampleRate.toNat / 2 < 2 ^ 32 := by omega
    have hq := Nat.div_le_self (tmpOf a.x.sampleRate.toNat * 128 + a.x.sampleRate.toNat / 2)
      a.x.sampleRate.toNat
    refine ⟨T.L117d.mpr ⟨RD.congr ?_ ?_ rfl ?_ ?_ ?_ hRD, ⟨row, hr, ?_⟩, ?_, ?_, ?_⟩, by var_step⟩
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hcx', sw32_64, hax, hsi,
      h8, hdi, BitVec.xor_self, BitVec.reduceSetWidth]
    rw [Nat.mod_eq_of_lt (by omega : tmpOf a.x.sampleRate.toNat * 128 + a.x.sampleRate.toNat / 2 < 2 ^ 64),
      Nat.mod_eq_of_lt hN]
    generalize (tmpOf a.x.sampleRate.toNat * 128 + a.x.sampleRate.toNat / 2) / a.x.sampleRate.toNat = q at *
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega

theorem blk_L117d (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L117d" ⟨"sbr_reset.L117d", B.L117d, some "sbr_reset.L118e"⟩ := by
  info_off
  measure_hb "L117d"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨⟨⟨hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF, -, hm⟩, h12, h15, hcx⟩,
      ⟨row, hr, hdi⟩, hax, hsi, h8⟩ := T.L117d.mp hs
    clear hs
    have hl : st.sp.length = 6 := hsp ▸ hC.1
    have hrow : row ≤ 5 := a1_rateRow_le hr
    have hs0 : u8 a.sp 0 < 16 := hC.2.1
    have hlen : 0 < st.sp.length := by omega
    have ld1 : loadInt s₀.dmem (t₀.regs.get64 .rsi + 28#64) 1
        = some (((a.sp.getD 0 0).toNat : Nat) : Int) := by
      have := a1_sp_load hm hl (i := 0) (by omega)
      rw [a1_slice_one hlen, a1_ofBytes_one, hsp] at this; exact this
    have ld2 : loadInt s₀.dmem (offLab row + BitVec.ofNat 64 (a.sp.getD 0 0).toNat) 1
        = some ((((sbrOffsetBytes row).getD (a.sp.getD 0 0).toNat 0).toNat : Nat) : Int) := by
      have := a1_cst_load hm hrow hs0
      rwa [a1_slice_one (by rw [a1_sbrOffsetBytes_length hrow]; exact hs0), a1_ofBytes_one] at this
    have ld3 := a1_k0_load hm
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L117d]
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    · simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, AddrIndex.offset64_none,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, ld1, Option.isSome_some]
    · rename_i b1 hl1
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, AddrIndex.offset64_none,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, ld1] at hl1
      obtain rfl := Option.some.inj hl1
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hdi, AddrIndex.offset64_scale1,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, a1_zx_byte, ld2,
        Option.isSome_some]
    all_goals rename_i b1 hl1 b2 hl2
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, AddrIndex.offset64_none,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, ld1] at hl1
    all_goals obtain rfl := Option.some.inj hl1
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hdi, AddrIndex.offset64_scale1,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, a1_zx_byte, ld2] at hl2
    all_goals obtain rfl := Option.some.inj hl2
    · simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, ld3, Option.isSome_some]
    have hsr := a1_sr_toInt (rateRow_mem hr)
    have hr' : rateRow (a.x.sampleRate.toNat : Int) = some row := hsr ▸ hr
    have hk := a1_k0_bv hr' hs0
    have hkr := k0Of_range hr hs0
    try simp only [srI, u8] at hkr
    rw [hsr] at hkr
    have hkn : (k0Of (a.x.sampleRate.toNat : Int) row (a.sp.getD 0 0).toNat).toNat ≤ 32 := by omega
    have hk0 : k0N a row = (k0Of (a.x.sampleRate.toNat : Int) row (a.sp.getD 0 0).toNat).toNat := by
      simp only [k0N, k0A, srI, hsr]
    have hst := a1_k0_store hm (k0N a row)
    simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, hax, sw32_64, a1_sw_ofNat64, hk,
      Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat]
    rw [← hk0, a1_toInt_ofNat32 (by omega)]
    refine ⟨T.L118e.mpr ⟨row, hr, ⟨hC, hBO, ⟨?_, ?_⟩, { st with x := { st.x with k0 := k0N a row } },
      fr, by rw [hx], hsp, hfm, hF, ⟨?_, ?_⟩, hst⟩, ?_, ?_⟩, ?_⟩
    rotate_right
    · clear hst hk hk0 hkn hkr hr' hsr ld1 ld2 ld3; var_step
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hrsp, hrbp, hcx]
    rw [hk0]; exact a1_sw64_ofNat32 (by omega)

theorem blk_L118e (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L118e" ⟨"sbr_reset.L118e", B.L118e, some "sbr_reset.L11a7"⟩ := by
  info_off
  measure_hb "L118e"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, hr, ⟨hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF, ⟨hdx, hcx⟩, hm⟩, h12, h15⟩ :=
      T.L118e.mp hs
    clear hs
    have hl : st.sp.length = 6 := hsp ▸ hC.1
    have hlen : 1 < st.sp.length := by omega
    have ld1 : loadInt s₀.dmem (t₀.regs.get64 .rsi + 29#64) 1
        = some (((a.sp.getD 1 0).toNat : Nat) : Int) := by
      have := a1_sp_load hm hl (i := 1) (by omega)
      rw [a1_slice_one hlen, a1_ofBytes_one, hsp] at this; exact this
    have ld2 := fr_load (d := 0x40) (n := 8) hm hF (by omega) (by omega)
    have hst := fr_store (d := 0x40) (n := 8) hm hF (by omega) (by omega) (t₀.regs.get64 .rdi).toInt
    have ha : t₀.regs.get64 .rsp - 8#64 + (-64 : Int64).toBitVec
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x40 := by
      rw [show (-64 : Int64).toBitVec = -64#64 from rfl]; bv_omega
    have hb1 := (a.sp.getD 1 0).toNat_lt
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L118e]
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    · simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, AddrIndex.offset64_none,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, ld1, Option.isSome_some]
    · rename_i b hl1 hc
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, AddrIndex.offset64_none,
          Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, ld1] at hl1
      obtain rfl := Option.some.inj hl1
      try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, a1_zx_byte, a1_sw_ofNat64, sw32_64, a1_zx_byte32,
          Int64.toBitVec_ofNat_norm, BitVec.reduceSetWidth, cc_a_sub, BitVec.toNat_ofNat,
          decide_eq_true_eq, decide_eq_false_iff_not, Nat.not_lt] at hc
      refine Or.inl (Table.ofLabels_at ⟨S.L150a, T.L150a.mpr ⟨row, hr, ⟨hC, hBO, ⟨?_, ?_⟩, st, fr, hx,
        hsp, hfm, hF, ⟨?_, ?_, ?_⟩, hm⟩, ?_, ?_⟩, by edge_step⟩)
      all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hrsp, hrbp, hdx,
        a1_zx_byte, u8]
      omega
    · simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrbp, ha, ld2, Option.isSome_some]
    · decide
    · rename_i b hl1 hc _
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, AddrIndex.offset64_none,
          Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, ld1] at hl1
      obtain rfl := Option.some.inj hl1
      try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, a1_zx_byte, a1_sw_ofNat64, sw32_64, a1_zx_byte32,
          Int64.toBitVec_ofNat_norm, BitVec.reduceSetWidth, cc_a_sub, BitVec.toNat_ofNat,
          decide_eq_true_eq, decide_eq_false_iff_not, Nat.not_lt] at hc
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrbp, ha, h15]
      refine ⟨T.L11a7.mpr ⟨row, hr, ?_, ⟨hC, hBO, ⟨?_, ?_⟩, st, _, hx, hsp, hfm,
        fr_wr_len hF (by omega) _, ?_, hst⟩, ?_, ?_⟩, ?_⟩
      rotate_right
      · clear hst ld1 ld2 ha; var_step
      all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hrsp, hrbp, hcx, u8]
      · omega
      · rw [frSlot64_wr_same hF (by decide) (by decide), BitVec.ofInt_toInt]

end Kraken.Examples.Sbr.Reset
