import Kraken.X64.Examples.Sbr.Parse.ResetA2Flt
import Kraken.X64.Examples.Sbr.Parse.ResetA2Lane
import Kraken.X64.Examples.Sbr.Parse.ResetA1Mem

/-!
# `sbr_reset`, shard A2: the setup blocks of the first `make_bands` (`L16f8`, `L171d`)
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Reset

variable [CodeEnv]

omit [CodeEnv] in
/-- The frame facts `SD` survive a 16-byte store to `-0x100`. -/
theorem a2_SD_wr100 {fr : List UInt8} (hF : FrOk fr) (v : Int) {e : REnv} {a : RArgs}
    {t₀ : MachineData} {k0 k2 : Nat} (h : A2.SD fr e a t₀ k0 k2) :
    A2.SD (wr fr (rb 0x100) (Int.toBytes 16 v)) e a t₀ k0 k2 := by
  obtain ⟨⟨⟨⟨h80, h88⟩, h38⟩, h50, h40⟩, h30⟩ := h
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩, ?_⟩
  · rw [frSlot32_wr_other hF (d := 0x100) (n := 16) (by omega) (by omega) _ (d' := 0x80) (by omega)
      (by omega) (by omega)]; exact h80
  · rw [frSlot32_wr_other hF (d := 0x100) (n := 16) (by omega) (by omega) _ (d' := 0x88) (by omega)
      (by omega) (by omega)]; exact h88
  · rw [frSlot32_wr_other hF (d := 0x100) (n := 16) (by omega) (by omega) _ (d' := 0x38) (by omega)
      (by omega) (by omega)]; exact h38
  · rw [frSlot32_wr_other hF (d := 0x100) (n := 16) (by omega) (by omega) _ (d' := 0x50) (by omega)
      (by omega) (by omega)]; exact h50
  · rw [frSlot64_wr_other hF (d := 0x100) (n := 16) (by omega) (by omega) _ (d' := 0x40) (by omega)
      (by omega) (by omega)]; exact h40
  · rw [frSlot64_wr_other hF (d := 0x100) (n := 16) (by omega) (by omega) _ (d' := 0x30) (by omega)
      (by omega) (by omega)]; exact h30

omit [CodeEnv] in
/-- The low lane of a 16-byte store, read back as a 4-byte slot. -/
theorem a2_frSlot32_wr16 {fr : List UInt8} (hF : FrOk fr) {d : Nat} (h : 0x38 ≤ d) (hd : d ≤ 0x570)
    (V : BitVec 128) : frSlot32 (wr fr (rb d) (Int.toBytes 16 V.toInt)) d = V.setWidth 32 := by
  simp only [frSlot32]
  rw [← a2_lo32_slice16, slice_wr_toBytes hF (by simp only [rb]; omega), BitVec.ofInt128_ofBytes_toBytes16,
    BitVec.ofInt_toInt]

set_option maxRecDepth 100000 in
/-- `(float)k[1] / (float)k[0]`, `1 / (float)num_bands_0`; `(float)k[0]` saved at `-0x100`. -/
theorem blk_L171d (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L171d" ⟨"sbr_reset.L171d", B.L171d, some "sbr_reset.L1736"⟩ := by
  info_off
  measure_hb "L171d"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, h15, h13, h14, hSD, hN0, hcx, hd0, hd1, hl2, hl1⟩, hm⟩⟩ := T.L171d.mp hs
    clear hs
    have hl100 := fr_load hm hF (d := 0x100) (n := 16) (by omega) (by omega)
    have st100 := fr_store hm hF (d := 0x100) (n := 16) (by omega) (by omega)
    have hF1 := fun v => fr_wr_len hF (o := rb 0x100) (n := 16) (by simp only [rb]; omega) v
    have e100 : t₀.regs.get64 .rsp - 8#64 + 18446744073709551360#64
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x100 := by bv_omega
    have hal := a2_al16_fr _ hC.2.2.2.2.2.2.2.2.2.2.2.2.2.1 18446744073709551360#64 (by decide)
    simp only [ln_sw] at hl2 hl1
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L171d]
    vcgen
    case vc1 =>
      rename_i s1 hs1
      subst hs1
      simp only [AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, hrbp]
      exact hal
    case vc2 =>
      rename_i s1 hs1
      subst hs1
      simp only [AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, hrbp, e100, hl100, Option.isSome_some]
    case vc3 =>
      rename_i s1 hs1
      subst hs1 hP
      simp only [AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, hrbp, e100]
      refine ⟨T.L1736.mpr ?_, ?_⟩
      rotate_left
      · rw [← hn]; simp only [lex_var]
        exact Kraken.lex_cons_le_of_lt (by lex_len) (by decide)
      refine ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st,
        wr fr (rb 0x100) (Int.toBytes 16 (s1.zmms.get (AvxReg.xmm .mm2)).toInt), hx, hsp, hfm, hF1 _,
        ⟨hk2v, hk1v, ?_, ?_, ?_, ⟨a2_SD_wr100 hF _ hSD, ?_⟩, hN0, ?_, ?_, ?_⟩, ?_⟩⟩
      rotate_right
      · exact st100 _
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
      · exact hrsp
      · exact hrbp
      · exact h15
      · exact h13
      · exact h14
      · rw [a2_frSlot32_wr16 hF (by omega) (by omega), ln_sw]; exact hl2
      · exact hcx
      · simp only [lo32, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne, ne_eq, reduceCtorEq,
          not_false_eq_true, ln_sw, ln_pk_l0, ln_ins16, ln_d4_l0]
        rw [hl2]; exact congrArg (BitVec.f32div · _) hd0
      · simp only [lo32, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne, ne_eq, reduceCtorEq,
          not_false_eq_true, ln_sw, ln_pk128, ln_d4_l0, Nat.reduceMul, ln_pk_l1, ln_ins16,
          UInt8.reduceToNat, Nat.reduceShiftRight, Nat.reduceMod, ln_d4_l1]
        simp only [Nat.reduceMul] at hd1
        rw [hd1, hl1]

omit [CodeEnv] in
/-- `SC` survives a frame store away from its slots. -/
theorem a2_SC_wr {fr : List UInt8} (hF : FrOk fr) {d n : Nat} (h : n + 0x28 ≤ d) (hd : d ≤ 0x570)
    (hne : 0x88 + n ≤ d ∨ d + 8 ≤ 0x38) (v : Int) {e : REnv} {a : RArgs} {t₀ : MachineData}
    {k0 k2 : Nat} (hS : A2.SC fr e a t₀ k0 k2) :
    A2.SC (wr fr (rb d) (Int.toBytes n v)) e a t₀ k0 k2 := by
  obtain ⟨⟨⟨h80, h88⟩, h38⟩, h50, h40⟩ := hS
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · rw [frSlot32_wr_other hF h hd v (d' := 0x80) (by omega) (by omega) (by omega)]; exact h80
  · rw [frSlot32_wr_other hF h hd v (d' := 0x88) (by omega) (by omega) (by omega)]; exact h88
  · rw [frSlot32_wr_other hF h hd v (d' := 0x38) (by omega) (by omega) (by omega)]; exact h38
  · rw [frSlot32_wr_other hF h hd v (d' := 0x50) (by omega) (by omega) (by omega)]; exact h50
  · rw [frSlot64_wr_other hF h hd v (d' := 0x40) (by omega) (by omega) (by omega)]; exact h40

/-- `.LCPI5_2` (16 bytes) out of the memory. -/
theorem a2_lcpi2_load {m : Mem 64} {k : Nat} {e : REnv} {a : RArgs} {ra : Int64} {t₀ : MachineData}
    {st : St} {fr : List UInt8} (hm : m =⋆ Mm k e a ra t₀ st fr) :
    m.loadInt (lab "LCPI5_2") 16 = some (Int.ofBytes (Int.toBytes 16 (0x3f80000000000000 : Int))) := by
  have h := focus (Mm_cst ..) hm
  simp only [CstR] at h
  obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_lr h
  obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_lr h
  obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_lr h
  obtain ⟨F, h⟩ := a1_pick_lr h
  obtain ⟨F, h⟩ := a1_pick_ll h
  have := region_load (o := 0) (n := 16) (addr := lab "LCPI5_2") h (by simp) (by simp [Int.toBytes_length])
    (by simp [Int.toBytes_length])
  rw [this]; rfl

omit [CodeEnv] in
theorem a2_c2_l1 : (BitVec.ofInt 128 (Int.ofBytes (Int.toBytes 16 (0x3f80000000000000 : Int)))).extractLsb' 32 32
    = 1065353216#32 := by
  rw [ofBytes_toBytes]; rfl

set_option maxRecDepth 100000 in
/-- `sbr` saved at `-0x30`; `(float)k[1]`, `(float)k[0]`, `(float)num_bands_0`, `1.0f` in lane 1. -/
theorem blk_L16f8 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L16f8" ⟨"sbr_reset.L16f8", B.L16f8, some "sbr_reset.L171d"⟩ := by
  info_off
  measure_hb "L16f8"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, h12, h15, h13, h14, hSC, hN0, hcx⟩, hm⟩⟩ := T.L16f8.mp hs
    clear hs
    have hl30 := fr_load hm hF (d := 0x30) (n := 8) (by omega) (by omega)
    have st30 := fr_store hm hF (d := 0x30) (n := 8) (by omega) (by omega)
    have hF1 := fun v => fr_wr_len hF (o := rb 0x30) (n := 8) (by simp only [rb]; omega) v
    have hl170 := fun v => fr_load (st30 v) (hF1 v) (d := 0x170) (n := 2) (by omega) (by omega)
    have st170 := fun v => fr_store (st30 v) (hF1 v) (d := 0x170) (n := 2) (by omega) (by omega)
    have hc2 := fun v => a2_lcpi2_load (st30 v)
    have e30 : t₀.regs.get64 .rsp - 8#64 + 18446744073709551568#64
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x30 := by bv_omega
    have e170 : t₀.regs.get64 .rsp - 8#64 + 18446744073709551248#64
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x170 := by bv_omega
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L16f8]
    vcgen
    case vc1 =>
      rename_i s1 hs1
      subst hs1
      simp only [AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, hrbp, e30, hl30, Option.isSome_some]
    case vc2 =>
      rename_i s1 hs1
      subst hs1
      simp only [AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, hrbp, e30]
      rw [hc2]; rfl
    case vc3 =>
      rename_i s1 hs1 v hv
      subst hs1
      simp only [AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, hrbp, e30, e170, hl170, Option.isSome_some]
    case vc4 =>
      rename_i s1 hs1 v hv
      subst hs1 hP
      simp only [AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, hrbp, e30, e170] at hv ⊢
      rw [hc2, Option.some.injEq] at hv
      subst hv
      refine ⟨T.L171d.mpr ?_, ?_⟩
      rotate_left
      · rw [← hn]; simp only [lex_var]
        exact Kraken.lex_cons_le_of_lt (by lex_len) (by decide)
      refine ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st, _, hx, hsp, hfm,
        fr_wr_len (hF1 _) (o := rb 0x170) (n := 2) (by simp only [rb]; omega) _,
        ⟨hk2v, hk1v, ?_, ?_, ?_, ⟨a2_SC_wr (hF1 _) (d := 0x170) (n := 2) (by omega) (by omega) (by omega) _
          (a2_SC_wr hF (d := 0x30) (n := 8) (by omega) (by omega) (by omega) _ hSC), ?_⟩,
          hN0, ?_, ?_, ?_, ?_, ?_⟩, st170 _ _⟩⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
      · exact hrsp
      · exact hrbp
      · exact h15
      · exact h13
      · exact h14
      · rw [frSlot64_wr_other (hF1 _) (d := 0x170) (n := 2) (by omega) (by omega) _ (d' := 0x30) (by omega)
          (by omega) (by omega), frSlot64_wr_same hF (by omega) (by omega), BitVec.ofInt_toInt]
        exact h12
      · exact hcx
      · simp only [RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne, ne_eq, reduceCtorEq,
          not_false_eq_true, Nat.reduceMul, ln_pki_l0, UInt8.reduceToNat, Nat.reduceShiftRight, Nat.reduceMod,
          Nat.zero_mod, ↓reduceIte, ln_la_l0, h14, a2_setWidth32_ofNat64]
        rw [ln_pki32 _ _ _ 0 (by decide)]
        simp only [Nat.zero_mod, Nat.reduceShiftRight, Nat.reduceMod, BitVec.dw, Nat.reduceMul, ln_la_l0]
        rfl
      · simp only [RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne, ne_eq, reduceCtorEq,
          not_false_eq_true, Nat.reduceMul, ln_pki_l1, UInt8.reduceToNat, Nat.reduceShiftRight, Nat.reduceMod,
          ↓reduceIte, a2_c2_l1]
        rw [ln_pki32 _ _ _ 1 (by decide)]
        simp only [Nat.one_mod, Nat.reduceShiftRight, Nat.reduceMod, BitVec.dw, Nat.reduceMul, ↓reduceIte, a2_c2_l1]
      · simp only [lo32, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne, ne_eq, reduceCtorEq,
          not_false_eq_true, ln_sw, ln_la_l0, h13, a2_setWidth32_ofNat64]
      · simp only [lo32, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne, ne_eq, reduceCtorEq,
          not_false_eq_true, ln_sw, ln_la_l0, hcx, a2_setWidth32_ofNat64]

end Kraken.Examples.Sbr.Reset
