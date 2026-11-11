import Kraken.X64.Examples.Sbr.Parse.ResetA2Mk

/-!
# `sbr_reset`, shard A2: the setup blocks of the second `make_bands` (`L1c33`, `L1c59`, `L1c7b`)
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Reset

variable [CodeEnv]

/-- `.LCPI5_3` (8 bytes) as a region. -/
theorem a2_lcpi3 {m : Mem 64} {k : Nat} {e : REnv} {a : RArgs} {ra : Int64} {t₀ : MachineData}
    {st : St} {fr : List UInt8} (hm : m =⋆ Mm k e a ra t₀ st fr) :
    ∃ F, m =⋆ Int.toBytes 8 (0x3f8000003f44ec4f : Int) =@ lab "LCPI5_3" ⋆ F := by
  have h := focus (Mm_cst ..) hm
  simp only [CstR] at h
  obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_lr h
  obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_lr h
  obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_lr h
  obtain ⟨F, h⟩ := a1_pick_ll h
  exact ⟨F, h⟩

omit [CodeEnv] in
/-- `xor eax,eax; cmpb $0,x; sete al`: `rax = (x = 0)`. -/
theorem a2_sete_idx (r : BitVec 64) (fl : StatusFlags.from_result.Remaining) (x : Nat) (hx : x < 256) :
    (BitVec.setWidth 64 (r.setWidth 32 ^^^ r.setWidth 32)).replaceLow
      (BitVec.ofNat 8 (CondCode.z.interp
        (StatusFlags.from_result (BitVec.ofInt 8 (x : Int) - BitVec.setWidth 8 0#64) fl)).toNat)
      = BitVec.ofNat 64 (if x = 0 then 1 else 0) := by
  simp only [CondCode.interp_z, StatusFlags.zf_from_result, BitVec.xor_self]
  by_cases h : x = 0
  · subst h; rfl
  · simp only [h, ↓reduceIte]
    have : (BitVec.ofInt 8 (x : Int) - BitVec.setWidth 8 0#64 == BitVec.zero 8) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro h'
      have := congrArg BitVec.toNat h'
      simp at this
      omega
    rw [this]; rfl

theorem a2_lcpi3_load {m : Mem 64} {k : Nat} {e : REnv} {a : RArgs} {ra : Int64} {t₀ : MachineData}
    {st : St} {fr : List UInt8} (hm : m =⋆ Mm k e a ra t₀ st fr) (x : Nat) :
    ∃ u, m.loadInt (lab "LCPI5_3" + BitVec.ofNat 64 (if x = 0 then 1 else 0) * 4#64) 4 = some u
      ∧ BitVec.ofInt 32 u = invwarp x := by
  obtain ⟨F, h⟩ := a2_lcpi3 hm
  by_cases hx : x = 0
  · simp only [hx, ↓reduceIte, invwarp]
    refine ⟨_, region_load (o := 4) (n := 4) h (by bv_omega) (by simp [Int.toBytes_length])
      (by simp [Int.toBytes_length]), ?_⟩
    decide
  · simp only [hx, ↓reduceIte, invwarp]
    refine ⟨_, region_load (o := 0) (n := 4) h (by bv_omega) (by simp [Int.toBytes_length])
      (by simp [Int.toBytes_length]), ?_⟩
    decide


omit [CodeEnv] in
theorem a2_ex0_sw128 (x : BitVec 32) : (x.setWidth 128).extractLsb' 0 32 = x := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj; simp [hj]; omega

omit [CodeEnv] in
/-- A frame write above the array at `o` keeps `Inc`. -/
theorem a2_inc_wr {fr : List UInt8} {p o n m : Nat} {v0 v1 : Int} (v : Int) (h : p + m ≤ fr.length)
    (hd : o + 2 * n + 2 ≤ p) (hI : A2.Inc fr o n v0 v1) :
    A2.Inc (wr fr p (Int.toBytes m v)) o n v0 v1 := by
  have hl : (Int.toBytes m v).length = m := Int.toBytes_length m v
  have key : ∀ i, i ≤ n → A2.fv (wr fr p (Int.toBytes m v)) o i = A2.fv fr o i := by
    intro i hi
    unfold A2.fv
    rw [slice_wr_disj (by rw [hl]; omega) (by rw [hl]; omega)]
  obtain ⟨h0, h1, h2⟩ := hI
  refine ⟨?_, ?_, fun i hi => ?_⟩
  · rw [key 0 (by omega)]; exact h0
  · rw [key n (by omega)]; exact h1
  · rw [key i (by omega), key (i + 1) (by omega)]; exact h2 i hi

set_option maxRecDepth 100000 in
theorem blk_L1c33 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1c33" ⟨"sbr_reset.L1c33", B.L1c33, some "sbr_reset.L1c59"⟩ := by
  info_off
  measure_hb "L1c33"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hSF, hlt, hInc, hN0, h12, h15, hsi, vm, hvm, hvm', hdi⟩, hm⟩⟩ := T.L1c33.mp hs
    clear hs
    have hl50 := fr_load hm hF (d := 0x50) (n := 4) (by omega) (by omega)
    have st50 := fr_store hm hF (d := 0x50) (n := 4) (by omega) (by omega)
    have hF1 := fun v => fr_wr_len hF (o := rb 0x50) (n := 4) (by simp only [rb]; omega) v
    have hl88 := fun v => fr_load (st50 v) (hF1 v) (d := 0x88) (n := 8) (by omega) (by omega)
    have st88 := fun v => fr_store (st50 v) (hF1 v) (d := 0x88) (n := 8) (by omega) (by omega)
    have hF2 := fun v w => fr_wr_len (hF1 v) (o := rb 0x88) (n := 8) (by simp only [rb]; omega) w
    have hl38 := fun v w => fr_load (st88 v w) (hF2 v w) (d := 0x38) (n := 4) (by omega) (by omega)
    have ld4 := fun v w => a2_sp_load (st88 v w) (by rw [hsp]; exact hC.1) (i := 4) (by omega)
    have hc3 := fun v w => a2_lcpi3 (st88 v w)
    have e50 : t₀.regs.get64 .rsp - 8#64 + 18446744073709551536#64
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x50 := by bv_omega
    have e88 : t₀.regs.get64 .rsp - 8#64 + 18446744073709551480#64
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x88 := by bv_omega
    have e38 : t₀.regs.get64 .rsp - 8#64 + 18446744073709551560#64
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x38 := by bv_omega
    have e4 : arg1 t₀ + 32#64 = arg1 t₀ + 0x1c#64 + BitVec.ofNat 64 4 := by bv_omega
    rw [hsp] at ld4
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L1c33]
    vcgen
    case vc1 =>
      rename_i s1 hs1
      subst hs1
      simp only [AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, hrbp, e50, hl50, Option.isSome_some]
    case vc2 =>
      rename_i s1 hs1
      subst hs1
      simp only [AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, hrbp, e50, e88, hl88, Option.isSome_some]
    case vc3 =>
      rename_i s1 hs1 b
      subst hs1
      simp only [AddrIndex.offset64_none, AddrIndex.offset64_scale4, Int64.toBitVec_neg_ofNat_norm,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, e50, e88, e38, reduceCtorEq,
        ↓reduceIte, Reg64s.get64_set64, h12, e4, ld4, Option.isSome_some, Nat.reduceMod, Nat.reducePow]
    case vc4 =>
      rename_i s1 hs1 b v hv
      subst hs1
      simp only [AddrIndex.offset64_none, AddrIndex.offset64_scale4, Int64.toBitVec_neg_ofNat_norm,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, e50, e88, e38, reduceCtorEq,
        ↓reduceIte, Reg64s.get64_set64, h12, e4, ld4, Option.isSome_some, Nat.reduceMod, Nat.reducePow]
      rw [hl38]; rfl
    case vc5 =>
      rename_i s1 hs1 b v hv w hw
      subst hs1
      simp only [AddrIndex.offset64_none, AddrIndex.offset64_scale4, Int64.toBitVec_neg_ofNat_norm,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, e50, e88, e38, reduceCtorEq,
        ↓reduceIte, Reg64s.get64_set64, h12, e4, ld4, Option.isSome_some, Nat.reduceMod, Nat.reducePow] at hv ⊢
      obtain rfl := Option.some.inj hv
      rw [a2_sete_idx _ _ _ (UInt8.toNat_lt _)]
      obtain ⟨u0, hu0, -⟩ := a2_lcpi3_load (st88 (BitVec.setWidth 32 (s1.regs.get64 Reg64.rdi)).toInt
        (s1.regs.get64 Reg64.rsi).toInt) ((a.sp.getD 4 0).toNat)
      rw [hu0]; rfl
    case vc6 =>
      rename_i s1 hs1 b v hv w hw u hlu
      subst hs1 hP
      simp only [AddrIndex.offset64_none, AddrIndex.offset64_scale4, Int64.toBitVec_neg_ofNat_norm,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, e50, e88, e38, reduceCtorEq,
        ↓reduceIte, Reg64s.get64_set64, h12, e4, ld4, Option.isSome_some, Nat.reduceMod, Nat.reducePow] at hv hw hlu ⊢
      obtain rfl := Option.some.inj hv
      rw [a2_sete_idx _ _ _ (UInt8.toNat_lt _)] at hlu ⊢
      obtain ⟨u0, hu0, hinv⟩ := a2_lcpi3_load (st88 (BitVec.setWidth 32 (s1.regs.get64 Reg64.rdi)).toInt
        (s1.regs.get64 Reg64.rsi).toInt) ((a.sp.getD 4 0).toNat)
      rw [hu0] at hlu
      obtain rfl := Option.some.inj hlu
      rw [hl38] at hw
      obtain rfl := Option.some.inj hw
      obtain ⟨⟨⟨⟨⟨⟨h80, h88⟩, h38⟩, h50s, h40⟩, h30⟩, h100⟩, h48⟩ := hSF
      have hn0 : A2.n0N e a (k0N a row) k2 ≤ 48 := by
        have h2 : A2.n0I e a (k0N a row) k2 ≤ 48 := hN0.2.1
        show (A2.n0I e a (k0N a row) k2).toNat ≤ 48
        omega
      refine ⟨T.L1c59.mpr ?_, ?_⟩
      rotate_left
      · rw [← hn]; simp only [lex_var]
        exact Kraken.lex_cons_le_of_lt (by lex_len) (by decide)
      refine ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st, _, hx, hsp, hfm, hF2 _ _,
        ⟨hk2v, hk1v, hlt,
          a2_inc_wr _ (by rw [hF1 _]; simp only [rb]; omega) (by simp only [rb]; omega)
            (a2_inc_wr _ (by rw [hF]; simp only [rb]; omega) (by simp only [rb]; omega) hInc),
          hN0, ?_, ?_, ?_, ?_, vm, hvm, hvm', ⟨?_, ?_, ?_, ?_⟩, trivial⟩, st88 _ _⟩⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
      · exact hrsp
      · exact hrbp
      · exact h12
      · exact h15
      · rw [frSlot64_wr_other (hF1 _) (d := 0x88) (n := 8) (by omega) (by omega) _ (d' := 0x30) (by omega)
          (by omega) (by omega), frSlot64_wr_other hF (d := 0x50) (n := 4) (by omega) (by omega) _
          (d' := 0x30) (by omega) (by omega) (by omega)]; exact h30
      · dsimp only [lo32]
        rw [RegZmms.get_set_xmm_same, a2_lo_app, RegZmms.get_set_xmm_same, a2_ex0_sw128, A2.h1Of, hinv]
        refine congrArg (BitVec.f32mul · _) ?_
        show frSlot32 _ 0x38 = _
        rw [frSlot32_wr_other (hF1 _) (d := 0x88) (n := 8) (by omega) (by omega) _ (d' := 0x38) (by omega)
          (by omega) (by omega), frSlot32_wr_other hF (d := 0x50) (n := 4) (by omega) (by omega) _
          (d' := 0x38) (by omega) (by omega) (by omega)]; exact h38
      · rw [frSlot64_wr_other (hF1 _) (d := 0x88) (n := 8) (by omega) (by omega) _ (d' := 0x40) (by omega)
          (by omega) (by omega), frSlot64_wr_other hF (d := 0x50) (n := 4) (by omega) (by omega) _
          (d' := 0x40) (by omega) (by omega) (by omega)]; exact h40
      · rw [frSlot64_wr_other (hF1 _) (d := 0x88) (n := 8) (by omega) (by omega) _ (d' := 0x48) (by omega)
          (by omega) (by omega), frSlot64_wr_other hF (d := 0x50) (n := 4) (by omega) (by omega) _
          (d' := 0x48) (by omega) (by omega) (by omega)]; exact h48
      · rw [frSlot64_wr_same (hF1 _) (by omega) (by omega), BitVec.ofInt_toInt]; exact hsi
      · rw [frSlot32_wr_other (hF1 _) (d := 0x88) (n := 8) (by omega) (by omega) _ (d' := 0x50) (by omega)
          (by omega) (by omega), frSlot32_wr_same hF (by omega) (by omega), BitVec.ofInt_toInt]; exact hdi

set_option maxRecDepth 100000 in
theorem blk_L1c59 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1c59" ⟨"sbr_reset.L1c59", B.L1c59, some "sbr_reset.L1c76"⟩ := by
  info_off
  measure_hb "L1c59"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hlt, hInc, hN0, h12, h15, h30, hlo, vm, hvm, hvm', hTA, -⟩, hm⟩⟩ := T.L1c59.mp hs
    clear hs
    have hl38 := fr_load hm hF (d := 0x38) (n := 4) (by omega) (by omega)
    have st38 := fr_store hm hF (d := 0x38) (n := 4) (by omega) (by omega)
    have hF1 := fun v => fr_wr_len hF (o := rb 0x38) (n := 4) (by simp only [rb]; omega) v
    have hk1l := fun v => cell4_load (focus (Mm_k1 ..) (st38 v))
    have hk2l := fun v => cell4_load (focus (Mm_k2 ..) (st38 v))
    have e38 : t₀.regs.get64 .rsp - 8#64 + 18446744073709551560#64
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x38 := by bv_omega
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L1c59]
    vcgen
    case vc1 =>
      rename_i s1 hs1
      subst hs1
      simp only [AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, e38, reduceCtorEq,
        ↓reduceIte, Reg64s.get64_set64, h12, Option.isSome_some]
      rw [hl38]; rfl
    case vc2 =>
      rename_i s1 hs1
      subst hs1
      simp only [AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, e38, reduceCtorEq,
        ↓reduceIte, Reg64s.get64_set64, h12, Option.isSome_some]
      rw [hk1l]; rfl
    case vc3 =>
      rename_i s1 hs1 x hlx
      subst hs1
      simp only [AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, e38, reduceCtorEq,
        ↓reduceIte, Reg64s.get64_set64, h12, Option.isSome_some]
      rw [hk2l]; rfl
    case vc4 =>
      rename_i s1 hs1 x hlx y hly
      subst hs1 hP
      simp only [AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, e38, reduceCtorEq,
        ↓reduceIte, Reg64s.get64_set64, h12, Option.isSome_some] at hlx hly ⊢
      rw [hk1l] at hlx
      rw [hk2l] at hly
      obtain rfl := Option.some.inj hlx
      obtain rfl := Option.some.inj hly
      have hk1b : A2.k1Of (k0N a row) k2 < 2 ^ 31 := by
        simp only [A2.k1Of, k0N, k0A, srI, u8]; split <;> omega
      have hn0 : A2.n0N e a (k0N a row) k2 ≤ 48 := by
        have h2 : A2.n0I e a (k0N a row) k2 ≤ 48 := hN0.2.1
        show (A2.n0I e a (k0N a row) k2).toNat ≤ 48
        omega
      have hk2b : k2 < 2 ^ 31 := by omega
      have ek1 : BitVec.ofInt 32 (Int.ofBytes (Int.toBytes 4 st.k1.toInt))
          = BitVec.ofNat 32 (A2.k1Of (k0N a row) k2) := by
        rw [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt_toInt, hk1v]
      have ek2 : BitVec.ofInt 32 (Int.ofBytes (Int.toBytes 4 st.k2.toInt)) = BitVec.ofNat 32 k2 := by
        rw [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt_toInt, hk2v]
      obtain ⟨t40, t48, t88, t50⟩ := hTA
      refine ⟨T.L1c76.mpr ?_, ?_⟩
      rotate_left
      · rw [← hn]; simp only [lex_var]
        exact Kraken.lex_cons_le_of_lt (by lex_len) (by decide)
      refine ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st, _, hx, hsp, hfm, hF1 _,
        ⟨hk2v, hk1v, hlt,
          a2_inc_wr _ (by rw [hF]; simp only [rb]; omega) (by simp only [rb]; omega) hInc,
          hN0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, vm, hvm, hvm', ⟨?_, ?_, ?_, ?_⟩, trivial⟩, st38 _⟩⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
      · exact hrsp
      · exact hrbp
      · exact h12
      · exact h15
      · rw [frSlot64_wr_other hF (d := 0x38) (n := 4) (by omega) (by omega) _
          (d' := 0x30) (by omega) (by omega) (by omega)]; exact h30
      · rw [frSlot32_wr_same hF (by omega) (by omega), BitVec.ofInt_toInt]; exact hlo
      · rw [ek1, a2_setWidth64_ofNat32 (by omega)]
      · rw [ek2, a2_setWidth64_ofNat32 (by omega)]
      · simp only [lo32, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne, ne_eq, reduceCtorEq,
          not_false_eq_true, a2_lo_app, a2_ex0_app, Reg64s.get64_set64, ↓reduceIte, ek1, ek2]
        rw [a2_setWidth64_ofNat32 (by omega), a2_setWidth64_ofNat32 (by omega), a2_sitof32_ofNat64 hk2b,
          a2_sitof32_ofNat64 hk1b]
      · rw [frSlot64_wr_other hF (d := 0x38) (n := 4) (by omega) (by omega) _
          (d' := 0x40) (by omega) (by omega) (by omega)]; exact t40
      · rw [frSlot64_wr_other hF (d := 0x38) (n := 4) (by omega) (by omega) _
          (d' := 0x48) (by omega) (by omega) (by omega)]; exact t48
      · rw [frSlot64_wr_other hF (d := 0x38) (n := 4) (by omega) (by omega) _
          (d' := 0x88) (by omega) (by omega) (by omega)]; exact t88
      · rw [frSlot32_wr_other hF (d := 0x38) (n := 4) (by omega) (by omega) _
          (d' := 0x50) (by omega) (by omega) (by omega)]; exact t50

set_option maxRecDepth 100000 in
theorem blk_L1c7b (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1c7b" ⟨"sbr_reset.L1c7b", B.L1c7b, some "sbr_reset.L1cb4"⟩ := by
  info_off
  measure_hb "L1c7b"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hlt, hInc, hN0, h12, h15, h30, h38, h13, h14, hlo, vm, hvm, hvm', hTA, -⟩, hm⟩⟩ :=
      T.L1c7b.mp hs
    clear hs
    have hl38 := fr_load hm hF (d := 0x38) (n := 4) (by omega) (by omega)
    have st80 := fr_store hm hF (d := 0x80) (n := 16) (by omega) (by omega)
    have hF1 := fun v => fr_wr_len hF (o := rb 0x80) (n := 16) (by simp only [rb]; omega) v
    have hc2 := a2_lcpi2_load hm
    have hl80 := fr_load hm hF (d := 0x80) (n := 16) (by omega) (by omega)
    have hal := a2_al16_fr _ hC.2.2.2.2.2.2.2.2.2.2.2.2.2.1 18446744073709551488#64 (by decide)
    have e38 : t₀.regs.get64 .rsp - 8#64 + 18446744073709551560#64
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x38 := by bv_omega
    have e80 : t₀.regs.get64 .rsp - 8#64 + 18446744073709551488#64
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x80 := by bv_omega
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L1c7b]
    vcgen
    case vc1 =>
      rename_i s1 hs1
      subst hs1
      simp only [AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, e38, e80, reduceCtorEq,
        ↓reduceIte, Reg64s.get64_set64, h12, h13, h14, Option.isSome_some]
      rw [hl38]; rfl
    case vc2 =>
      rename_i s1 hs1 w hw
      subst hs1
      simp only [AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, e38, e80, reduceCtorEq,
        ↓reduceIte, Reg64s.get64_set64, h12, h13, h14, Option.isSome_some]
      rw [hc2]; rfl
    case vc3 =>
      rename_i s1 hs1 w hw c hc
      subst hs1
      simp only [AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrbp]
      exact hal
    case vc4 =>
      rename_i s1 hs1 w hw c hc
      subst hs1
      simp only [AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, e38, e80, reduceCtorEq,
        ↓reduceIte, Reg64s.get64_set64, h12, h13, h14, Option.isSome_some]
      rw [hl80]; rfl
    case vc5 =>
      rename_i s1 hs1 w hw c hc
      subst hs1 hP
      simp only [AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, e38, e80, reduceCtorEq,
        ↓reduceIte, Reg64s.get64_set64, h12, h13, h14, Option.isSome_some] at hw hc ⊢
      rw [hl38] at hw
      rw [hc2] at hc
      obtain rfl := Option.some.inj hw
      obtain rfl := Option.some.inj hc
      try simp only [lo32] at hlo
      try simp only [frSlot32] at h38
      simp only [RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne, ne_eq, reduceCtorEq, not_false_eq_true,
        a2_lo_app, a2_ex0_eq_sw, hlo, h38, AddrIndex.offset64_scale1, a2_setWidth32_ofNat64, sw32_64]
      simp only [Reg64s.get64_set64, ↓reduceIte, a2_lea2]
      generalize hX : BitVec.f32toi64 (BitVec.f32mul (e.lg (BitVec.f32div (A2.fl k2)
        (A2.fl (A2.k1Of (k0N a row) k2)))) (A2.h1Of a)) = X
      have hnI : A2.n1I e a (k0N a row) k2 = (BitVec.ofInt 32 (2 * X.toInt)).toInt := by
        rw [← hX]; rfl
      have hb := (a2_bands_of hB hC hrow hk2 hk02 hkq hu).2 hlt
      have hev := a2_even_nb X.toInt
      have hpos : 0 ≤ (BitVec.ofInt 32 (2 * X.toInt)).toInt := by rw [← hnI]; omega
      have hn1 : BitVec.ofNat 32 (A2.n1N e a (k0N a row) k2) = BitVec.ofInt 32 (2 * X.toInt) := by
        simp only [A2.n1N, hnI]; exact a2_ofNat_toInt_toNat32 _ hpos
      have hn0 : A2.n0N e a (k0N a row) k2 ≤ 48 := by
        have h2 : A2.n0I e a (k0N a row) k2 ≤ 48 := hN0.2.1
        show (A2.n0I e a (k0N a row) k2).toNat ≤ 48
        omega
      obtain ⟨t40, t48, t88, t50⟩ := hTA
      refine ⟨T.L1cb4.mpr ?_, ?_⟩
      rotate_left
      · rw [← hn]; simp only [lex_var]
        exact Kraken.lex_cons_le_of_lt (by lex_len) (by decide)
      refine ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st, _, hx, hsp, hfm, hF1 _,
        ⟨hk2v, hk1v, hlt,
          a2_inc_wr _ (by rw [hF]; simp only [rb]; omega) (by simp only [rb]; omega) hInc,
          hN0, ⟨hb.1, hb.2.1, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, vm, hvm, hvm', ⟨?_, ?_, ?_, ?_⟩, trivial⟩,
          st80 _⟩⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
      · exact hrsp
      · exact hrbp
      · simp only [A2.n1N, hnI]; omega
      · exact h12
      · rw [frSlot64_wr_other hF (d := 0x80) (n := 16) (by omega) (by omega) _
          (d' := 0x30) (by omega) (by omega) (by omega)]; exact h30
      · exact h13
      · exact h14
      · rw [hn1, ← a2_lea2]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_setWidth]
        omega
      · rw [a2_sw64_toInt32 _ hpos]; simp only [A2.n1N, hnI]
      · rw [a2_frSlot32_wr16 hF (by omega) (by omega)]
        simp (config := {decide := true}) only [ln_sw, ln_pk_l0, ln_pki_l0, UInt8.reduceToNat, Nat.reduceMod,
          ↓reduceIte, a2_ex0_sw128, A2.fl]
      · simp (config := {decide := true}) only [lo32, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
          ne_eq, reduceCtorEq, not_false_eq_true, ln_sw, ln_pk_l0,
          ln_pki_l0, UInt8.reduceToNat, Nat.reduceMod, Nat.reduceShiftRight, ↓reduceIte, a2_ex0_sw128, A2.fl,
          ln_la_l0]
      · simp (config := {decide := true}) only [lo32, RegZmms.get_set_xmm_same, ln_sw, ln_pk128, ln_d4_l0,
          Nat.reduceMul, ln_pk_l1, ln_pki_l1, UInt8.reduceToNat, Nat.reduceMod, Nat.reduceShiftRight,
          ↓reduceIte, a2_c2_l1, A2.fl, hn1]
      · rw [frSlot64_wr_other hF (d := 0x80) (n := 16) (by omega) (by omega) _
          (d' := 0x40) (by omega) (by omega) (by omega)]; exact t40
      · rw [frSlot64_wr_other hF (d := 0x80) (n := 16) (by omega) (by omega) _
          (d' := 0x48) (by omega) (by omega) (by omega)]; exact t48
      · rw [frSlot64_wr_other hF (d := 0x80) (n := 16) (by omega) (by omega) _
          (d' := 0x88) (by omega) (by omega) (by omega)]; exact t88
      · rw [frSlot32_wr_other hF (d := 0x80) (n := 16) (by omega) (by omega) _
          (d' := 0x50) (by omega) (by omega) (by omega)]; exact t50

end Kraken.Examples.Sbr.Reset
