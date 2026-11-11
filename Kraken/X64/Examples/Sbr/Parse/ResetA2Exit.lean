import Kraken.X64.Examples.Sbr.Parse.ResetA2Lib
import Kraken.X64.Examples.Sbr.Parse.ResetModel

/-!
# `sbr_reset`, shard A2: the failure exits

The checks of `sbr_make_f_master` (`bs_freq_scale > 0`) that fail end at the shared error log
(`L167a`, `L1cff`, `L1d2a`) with `AtFail`: turning the current values off is a result
`Reset` allows (`Master.fail`).
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
/-- A rejection after `k[0]` is stored: `Reset` turns the values with `k[0]` off. -/
theorem a2_fail_reset {a : RArgs} {row : Nat} (hrow : rateRow (srI a) = some row)
    (h0 : u8 a.sp 0 < 16) : Reset (spOf a) (lbN a) a.x (xk0 a row).turnoff :=
  Reset.badMaster h0 (Master.fail hrow)

set_option maxRecDepth 100000 in
/-- The `bs_xover_band` check failed: `rdx = fmt`, `jmp L167a`. -/
theorem blk_L29ad (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L29ad" ⟨"sbr_reset.L29ad", B.L29ad, some "sbr_reset.L29b9"⟩ := by
  info_off
  measure_hb "L29ad"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨⟨hC, ⟨hrsp, hrbp⟩, h12, h15, st, fr, hM, hsp, hfm, hF, hm⟩, hdi⟩ := T.L29ad.mp hs
    clear hs
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L29ad]
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    left; apply Table.ofLabels_at
    refine ⟨by decide, T.L167a.mpr ⟨⟨hC, ⟨?_, ?_⟩, ?_, ?_, st, fr, hM, hsp, hfm, hF, hm⟩, ?_⟩, ?_⟩
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15, hdi]
    edge_step

set_option maxRecDepth 100000 in
/-- `n_master ≤ 0`: `rdx = fmt`, `esi = AV_LOG_ERROR`, `ecx = n_master`, `jmp L1d2a`. -/
theorem blk_L29b9 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L29b9" ⟨"sbr_reset.L29b9", B.L29b9, some "sbr_reset.L29cd"⟩ := by
  info_off
  measure_hb "L29b9"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨⟨hC, ⟨hrsp, hrbp⟩, h12, h15, st, fr, hM, hsp, hfm, hF, hm⟩, hdi⟩ := T.L29b9.mp hs
    clear hs
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L29b9]
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    left; apply Table.ofLabels_at
    refine ⟨by decide, T.L1d2a.mpr ⟨⟨hC, ⟨?_, ?_⟩, ?_, ?_, st, fr, hM, hsp, hfm, hF, hm⟩, ?_⟩, ?_⟩
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15, hdi]
    edge_step

omit [CodeEnv] in
theorem a2_c8_load2 {m : Mem 64} {addr : BitVec 64} {F : Mem 64 → Prop} {v : BitVec 64}
    (h : m =⋆ c8 addr v ⋆ F) : m.loadInt addr 8 = some (Int.ofBytes (Int.toBytes 8 v.toInt)) :=
  loadInt_sep _ _ 8 F m h (Int.toBytes_length 8 _) (by omega)

set_option maxRecDepth 100000 in
/-- The one-region `bs_xover_band` check failed: `rdi = ac->avctx`, `jmp L29ad`. -/
theorem blk_L1e00 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1e00" ⟨"sbr_reset.L1e00", B.L1e00, some "sbr_reset.L1e09"⟩ := by
  info_off
  measure_hb "L1e00"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hC, ⟨hrsp, hrbp⟩, h12, h15, st, fr, hM, hsp, hfm, hF, hm⟩ := T.L1e00.mp hs
    clear hs
    have ld1 := a2_c8_load2 (focus (Mm_avctx ..) hm)
    have hav : st.x.avctx = a.x.avctx := (reset_keeps hM).2.2
    simp only [arg0] at ld1
    rw [hav] at ld1
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L1e00]
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    · simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h15, AddrIndex.offset64_none,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, ld1, Option.isSome_some]
    · rename_i _ hl
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h15, AddrIndex.offset64_none,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at hl
      rw [ld1] at hl
      obtain rfl := Option.some.inj hl
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L29ad.mpr ⟨⟨hC, ⟨?_, ?_⟩, ?_, ?_, st, fr, hM, hsp, hfm, hF, hm⟩, ?_⟩, ?_⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15,
        BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]
      edge_step

set_option maxRecDepth 100000 in
/-- `rcx -= 3`, `jmp L29dc`. -/
theorem blk_L29cd (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L29cd" ⟨"sbr_reset.L29cd", B.L29cd, some "sbr_reset.L29d3"⟩ := by
  info_off
  measure_hb "L29cd"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, hrow, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF, hsl, hm⟩, h12⟩ := T.L29cd.mp hs
    clear hs
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L29cd]
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    left; apply Table.ofLabels_at
    refine ⟨by decide, T.L29dc.mpr ⟨row, hrow, ⟨hC, hB, ⟨?_, ?_⟩, st, fr, hx, hsp, hfm, hF, hsl, hm⟩, ?_⟩, ?_⟩
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12]
    edge_step

set_option maxRecDepth 100000 in
/-- `rcx -= 2`, `jmp L29dc`. -/
theorem blk_L29d3 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L29d3" ⟨"sbr_reset.L29d3", B.L29d3, some "sbr_reset.L29d9"⟩ := by
  info_off
  measure_hb "L29d3"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, hrow, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF, hsl, hm⟩, h12⟩ := T.L29d3.mp hs
    clear hs
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L29d3]
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    left; apply Table.ofLabels_at
    refine ⟨by decide, T.L29dc.mpr ⟨row, hrow, ⟨hC, hB, ⟨?_, ?_⟩, st, fr, hx, hsp, hfm, hF, hsl, hm⟩, ?_⟩, ?_⟩
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12]
    edge_step

set_option maxRecDepth 100000 in
/-- `rcx -= 1`, on to `L29dc`. -/
theorem blk_L29d9 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L29d9" ⟨"sbr_reset.L29d9", B.L29d9, some "sbr_reset.L29dc"⟩ := by
  info_off
  measure_hb "L29d9"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, hrow, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF, hsl, hm⟩, h12⟩ := T.L29d9.mp hs
    clear hs
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L29d9]
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    refine ⟨T.L29dc.mpr ⟨row, hrow, ⟨hC, hB, ⟨?_, ?_⟩, st, fr, hx, hsp, hfm, hF, hsl, hm⟩, ?_⟩, by var_step⟩
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12]

set_option maxRecDepth 100000 in
/-- A step of the second prefix sum is not positive: `r15 = ac` (frame), `rdi = ac->avctx`,
`jmp L1cff`. -/
theorem blk_L29dc (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L29dc" ⟨"sbr_reset.L29dc", B.L29dc, some "sbr_reset.L29f4"⟩ := by
  info_off
  measure_hb "L29dc"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, hrow, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF, hsl, hm⟩, h12⟩ := T.L29dc.mp hs
    clear hs
    have ld0 := fr_load hm hF (d := 0x40) (n := 8) (by omega) (by omega)
    have ld1 := a2_c8_load2 (focus (Mm_avctx ..) hm)
    have hsl' : BitVec.ofInt 64 (Int.ofBytes (slice fr (rb 0x40) 8)) = arg0 t₀ := hsl
    simp only [arg0] at ld1 hsl'
    have e40 : t₀.regs.get64 .rsp - 8#64 + 0xffffffffffffffc0#64
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x40 := by bv_omega
    have hav : st.x.avctx = a.x.avctx := by rw [hx]
    rw [hav] at ld1
    have hM : Reset (spOf a) (lbN a) a.x st.x.turnoff := by rw [hx]; exact a2_fail_reset hrow hC.2.1
    have hrbpF : ∀ s : MachineData, s = s₀ → s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64 :=
      fun s h => h ▸ hrbp
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L29dc]
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrbp, AddrIndex.offset64_none,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
        Nat.reduceMod, Nat.reducePow, Nat.reduceSub, e40, ld0, Option.isSome_some] at *
    · rename_i hl0
      obtain rfl := Option.some.inj hl0
      simp only [hsl', ld1, Option.isSome_some]
    · rename_i v0 v1 hl0 hl1
      obtain rfl := Option.some.inj hl0
      simp only [hsl', ld1] at hl1
      obtain rfl := Option.some.inj hl1
      refine Or.inl (Table.ofLabels_at ⟨S.L1cff, T.L1cff.mpr ⟨⟨hC, ⟨?_, ?_⟩, ?_, ?_, st, fr, hM, hsp, hfm, hF, hm⟩, ?_⟩, by edge_step⟩)
      all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, hsl', arg0,
        BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]
      all_goals exact hrbpF _ rfl

set_option maxRecDepth 100000 in
/-- Unreachable: `num_bands_1 < 2` contradicts `BandsOK`. -/
theorem blk_L1de3 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1de3" ⟨"sbr_reset.L1de3", B.L1de3, some "sbr_reset.L1e00"⟩ := by
  info_off
  measure_hb "L1de3"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    exact (T.L1de3.mp hs).elim

end Kraken.Examples.Sbr.Reset
