import Kraken.InfoOff
import Kraken.X64.Examples.Sbr.Parse.ResetTable
import Kraken.X64.Examples.Sbr.Parse.ResetModel

/-!
# `sbr_reset`: the failure paths' argument set-up (shard B)
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
theorem c8_load' {m : Mem 64} {addr : BitVec 64} {F : Mem 64 → Prop} {v : BitVec 64}
    (h : m =⋆ c8 addr v ⋆ F) : m.loadInt addr 8 = some (Int.ofBytes (Int.toBytes 8 v.toInt)) :=
  loadInt_sep _ _ 8 F m h (Int.toBytes_length 8 _) (by omega)

set_option maxRecDepth 100000 in
/-- `rdi = ac->avctx` for `sbr_make_f_master`'s error log. -/
theorem blk_L1cf4 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1cf4" ⟨"sbr_reset.L1cf4", B.L1cf4, some "sbr_reset.L1cff"⟩ := by
  info_off
  measure_hb "L1cf4"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hC, ⟨hrsp, hrbp⟩, h12, h15, st, fr, hM, hsp, hfm, hF, hm⟩ := T.L1cf4.mp hs
    clear hs
    have ld1 := c8_load' (focus (Mm_avctx ..) hm)
    have hav : st.x.avctx = a.x.avctx := (reset_keeps hM).2.2
    simp only [arg0] at ld1
    rw [hav] at ld1
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L1cf4]
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
      refine ⟨T.L1cff.mpr ⟨⟨hC, ⟨?_, ?_⟩, ?_, ?_, st, fr, hM, hsp, hfm, hF, hm⟩, ?_⟩, by var_step⟩
      all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15,
        BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]

set_option maxRecDepth 100000 in
/-- `jmp L1d31`. -/
theorem blk_L1d0b (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1d0b" ⟨"sbr_reset.L1d0b", B.L1d0b, some "sbr_reset.L1d0d"⟩ := by
  info_off
  measure_hb "L1d0b"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    have hE := T.L1d0b.mp hs
    simp only [B.L1d0b]
    vcgen
    all_goals try subst_vars
    left; apply Table.ofLabels_at
    refine ⟨by decide, T.L1d31.mpr hE, ?_⟩
    edge_step

set_option maxRecDepth 100000 in
/-- `rdx = fmt`, `esi = AV_LOG_ERROR`, `jmp L1d2a`. -/
theorem blk_L1d0d (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1d0d" ⟨"sbr_reset.L1d0d", B.L1d0d, some "sbr_reset.L1d1b"⟩ := by
  info_off
  measure_hb "L1d0d"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨⟨hC, ⟨hrsp, hrbp⟩, h12, h15, st, fr, hM, hsp, hfm, hF, hm⟩, hdi⟩ := T.L1d0d.mp hs
    clear hs
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L1d0d]
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    left; apply Table.ofLabels_at
    refine ⟨by decide, T.L1d2a.mpr ⟨⟨hC, ⟨?_, ?_⟩, ?_, ?_, st, fr, hM, hsp, hfm, hF, hm⟩, ?_⟩, ?_⟩
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15, hdi]
    edge_step

set_option maxRecDepth 100000 in
/-- `rdx = fmt`, `esi = AV_LOG_ERROR`, `ecx = r8d`. -/
theorem blk_L1d1b (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1d1b" ⟨"sbr_reset.L1d1b", B.L1d1b, some "sbr_reset.L1d2a"⟩ := by
  info_off
  measure_hb "L1d1b"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨⟨hC, ⟨hrsp, hrbp⟩, h12, h15, st, fr, hM, hsp, hfm, hF, hm⟩, hdi⟩ := T.L1d1b.mp hs
    clear hs
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L1d1b]
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    refine ⟨T.L1d2a.mpr ⟨⟨hC, ⟨?_, ?_⟩, ?_, ?_, st, fr, hM, hsp, hfm, hF, hm⟩, ?_⟩, by var_step⟩
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15, hdi]

end Kraken.Examples.Sbr.Reset
