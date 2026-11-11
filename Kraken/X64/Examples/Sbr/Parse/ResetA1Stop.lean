import Kraken.X64.Examples.Sbr.Parse.ResetA1Mem
import Kraken.X64.Examples.Sbr.Parse.ResetLog

/-!
# `sbr_reset`: `stop_min` (shard A1)

`L11a7`: `stop_min = (temp * 256 + sr / 2) / sr`; `L11ad`: `stop_min` into `k[2]` (scratch until
the sum of `L1523`), `sbr` saved at `rbp - 0x30`.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Reset

variable [CodeEnv]

theorem blk_L11a7 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L11a7" ⟨"sbr_reset.L11a7", B.L11a7, some "sbr_reset.L11ad"⟩ := by
  info_off
  measure_hb "L11a7"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, hr, hsp1, hA, h12, hcx'⟩ := T.L11a7.mp hs
    clear hs
    have hsr0 : a.x.sampleRate.toNat ≠ 0 := by
      intro h0
      have hm := rateRow_mem hr
      have : a.x.sampleRate = 0#32 := BitVec.eq_of_toNat_eq h0
      simp only [srI, this] at hm; revert hm; decide
    simp only [B.L11a7]
    vcgen
    all_goals try subst_vars
    refine ⟨⟨?_, ?_⟩, fun st' => ?_⟩
    · simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hcx', sw32_64]; exact hsr0
    · simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hcx', sw32_64,
        BitVec.xor_self, BitVec.toNat_setWidth, BitVec.reduceSetWidth, BitVec.toNat_zero,
        Nat.zero_mul, Nat.zero_add, Nat.zero_mod]
      apply Nat.lt_of_le_of_lt (Nat.div_le_self _ _); omega
    dsimp only
    simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hcx', sw32_64,
      BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_setWidth, BitVec.toNat_zero,
      Nat.zero_mul, Nat.zero_add, Nat.zero_mod]
    vcgen
    all_goals try subst_vars
    exact ⟨T.L11ad.mpr ⟨row, hr, hsp1, A1S.congr (by simp) (by simp) rfl (fun _ _ x => x) hA,
      by simpa using h12⟩, by var_step⟩

theorem blk_L11ad (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L11ad" ⟨"sbr_reset.L11ad", B.L11ad, some "sbr_reset.L11bd"⟩ := by
  info_off
  measure_hb "L11ad"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, hr, hsp1, ⟨hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF, hf40, hm⟩, h12⟩ :=
      T.L11ad.mp hs
    clear hs
    have ha : t₀.regs.get64 .rsp - 8#64 + (-48 : Int64).toBitVec
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x30 := by
      rw [show (-48 : Int64).toBitVec = -48#64 from rfl]; bv_omega
    have ld1 := fr_load (d := 0x30) (n := 8) hm hF (by omega) (by omega)
    have hst1 := fr_store (d := 0x30) (n := 8) hm hF (by omega) (by omega) (t₀.regs.get64 .rsi).toInt
    have hF1 := fr_wr_len hF (o := rb 0x30) (n := 8) (by simp only [rb]; omega) (t₀.regs.get64 .rsi).toInt
    generalize hfr1 : wr fr (rb 0x30) (Int.toBytes 8 (t₀.regs.get64 .rsi).toInt) = fr1 at hst1 hF1
    have hs40 : frSlot64 fr1 0x40 = arg0 t₀ := by
      rw [← hfr1, frSlot64_wr_other hF (by omega) (by omega) _ (by omega) (by omega) (by omega), hf40]
    have hs30 : frSlot64 fr1 0x30 = arg1 t₀ := by
      rw [← hfr1, frSlot64_wr_same hF (by omega) (by omega), BitVec.ofInt_toInt]
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L11ad]
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrbp, ha, h12,
      Int64.toBitVec_ofNat_norm]
    · simp only [ld1, Option.isSome_some]
    · exact a1_k2_isSome hst1
    · rename_i s
      refine ⟨T.L11bd.mpr ⟨row, hr, hsp1, hC, hBO, ⟨hrsp, hrbp⟩,
        { st with k2 := BitVec.setWidth 32 (s.regs.get64 .rax) }, _, hx, hsp, hfm, hF1,
        ⟨hs40, hs30, trivial⟩, a1_k2_store hst1 _⟩, ?_⟩
      clear hst1 ld1 ha hs40 hs30 hF1; var_step

/-- `powf(64 / stop_min, 1 / 13)` (`LCPI5_0 = 64.0`, `LCPI5_1 = 1/13`). -/
theorem blk_L11bd (k : Nat) (e : REnv) (hc : ResetCallees k e) (a : RArgs) (ra : Int64)
    (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L11bd" ⟨"sbr_reset.L11bd", B.L11bd, some "sbr_reset.L11db"⟩ := by
  info_off
  measure_hb "L11bd"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, hr, hsp1, ⟨hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF, ⟨hs40, hs30, -⟩, hm⟩⟩ :=
      T.L11bd.mp hs
    clear hs
    have hd := reserve_le (focus (Mm_reserve ..) hm)
    generalize hV : ((s₀.zmms.get (AvxReg.xmm .mm1)).setWidth 32).toInt = V
    have hst0 := fr_store (d := 0x38) (n := 4) hm hF (by omega) (by omega) V
    have hst := hst0
    rw [Mm_callF _ _ _ _ _ _ _ hd] at hst
    have hc0 := a1_lcpi0_isSome hst0
    have hc1 := a1_lcpi1_isSome hst0
    have ld1 := fr_load (d := 0x38) (n := 4) hm hF (by omega) (by omega)
    have hF1 := fr_wr_len hF (o := rb 0x38) (n := 4) (by simp only [rb]; omega) V
    have hs40' : frSlot64 (wr fr (rb 0x38) (Int.toBytes 4 V)) 0x40 = arg0 t₀ := by
      rw [frSlot64_wr_other hF (by omega) (by omega) _ (by omega) (by omega) (by omega), hs40]
    have hs30' : frSlot64 (wr fr (rb 0x38) (Int.toBytes 4 V)) 0x30 = arg1 t₀ := by
      rw [frSlot64_wr_other hF (by omega) (by omega) _ (by omega) (by omega) (by omega), hs30]
    have ha : t₀.regs.get64 .rsp - 8#64 + 0 + (-56 : Int64).toBitVec
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x38 := by
      rw [show (-56 : Int64).toBitVec = -56#64 from rfl]; bv_omega
    have hld : ∀ m : Mem 64, (m =⋆ 8 ?@ (t₀.regs.get64 .rsp - 0x578#64 - 8#64) ⋆ (Reserve k
        (t₀.regs.get64 .rsp - 0x578#64 - 8#64) ⋆ (e.Ext ⋆ CallF k e a ra t₀ st
        (wr fr (rb 0x38) (Int.toBytes 4 V))))) →
        (m.loadInt (t₀.regs.get64 .rsp - 0x578#64 - 8#64) 8).isSome = true :=
      fun m h => Block.loadInt_isSome h (by simp)
    have hpush := fun v => Block.storeInt_val hst (Split.here _ _) v
    simp only [B.L11bd]
    vcgen [MachineWP.call_proc_spec_at (CallF k e a ra t₀ st (wr fr (rb 0x38) (Int.toBytes 4 V)))
      "powf" hc.powf]
    all_goals try call_simp
    all_goals try subst_vars
    all_goals simp only [AddrIndex.offset64_none, hrbp, ha, hrsp] at *
    · simp only [ld1, Option.isSome_some]
    · exact hc0
    · exact hc1
    have e8 : t₀.regs.get64 .rsp - 1400#64 - Width.W64.bytesv = t₀.regs.get64 .rsp - 0x578#64 - 8#64 := rfl
    refine ⟨fun ra' => ⟨⟨?_, trivial⟩, fun s' hpost => ?_⟩, ?_⟩
    · rw [e8]; exact hpush _
    · rw [e8] at hpost
      obtain ⟨⟨hsp', hbp', -, hm'⟩, -⟩ := hpost
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨T.L11db.mpr ⟨row, hr, hsp1, hC, hBO, ⟨?_, ?_⟩, st, _, hx, hsp, hfm, hF1,
        ⟨hs40', hs30', trivial⟩, ?_⟩, by var_step⟩
      · rw [hsp']; bv_omega
      · rw [hbp']
      · show Mm k e a ra t₀ st _ s'.dmem
        rw [Mm_callF _ _ _ _ _ _ _ hd]; exact hm'
    · rw [e8]; exact hld _ hst

end Kraken.Examples.Sbr.Reset
