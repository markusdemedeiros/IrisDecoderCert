import Kraken.X64.Examples.Sbr.Parse.HdrStep

/-!
# `read_sbr_header`: the block obligations of the extra fields

`Le45` skips `bs_reserved` and reads the two `bs_header_extra` flags; `Le9d`..`Lefb` read
`bs_freq_scale`, `bs_alter_scale` and `bs_noise_bands`; `Lf31` stores their defaults; `Lf3a`
stores `bs_noise_bands` and compares `spectrum_params` with the copy in the locals.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Hdr

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm
open Kraken.Examples.Sbr.Parse (bswap32_havoc shl_cl32_havoc)
open Kraken.Examples.Sbr.HdrLib

theorem blk_Le45 (k : Nat) (TlT : BitVec 64 → Mem 64 → Prop)
    (TlT' : BitVec 32 → BitVec 64 → Mem 64 → Prop) (TlC : BitVec 32 → BitVec 64 → Prop)
    (x : HArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k TlT TlT' TlC x ra t₀ "read_sbr_header.Le45" := by
  cfg_block
  measure_hb "Le45"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hR, i, sp, amp, ⟨hi1, hi2⟩, hA, hm⟩, hn⟩ := hs₀
    have hli := M_ld_i hm
    have hlp := M_ld_p8 hm
    have hlb := M_ld_buf hm
    have hb1 := fun a off (h : off.toNat + 1 ≤ x.L) => M_ld_bytes (M_st_i hm a) off 1 h
    have hb2 := fun a b off (h : off.toNat + 1 ≤ x.L) => M_ld_bytes (M_st_i (M_st_i hm a) b) off 1 h
    have hlb1 := fun a => M_ld_buf (M_st_i hm a)
    have hok1 := fun a => M_ok_i (M_st_i hm a)
    have hok2 := fun a b => M_ok_i (M_st_i (M_st_i hm a) b)
    have hS := fun a b c => M_st_i (M_st_i (M_st_i hm a) b) c
    have hcl := clamp _ x.p8 2 hi2 hC.2.2.1 (by omega)
    have hRh : ∀ s : MachineData, s = s₀ → Rs x t₀ s := fun _ h => h ▸ hR
    obtain ⟨hrdi, hrsi, hrsp, hrbp, hrest⟩ := hR
    clear hm
    simp only [arg0, arg1, BitVec.add_zero, Nat.reduceAdd, BitVec.add_assoc,
      BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at hli hlp hlb hb1 hb2 hS hlb1 hok1 hok2
    vcgen [bswap32_havoc, shl_cl32_havoc]
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals try simp only [AddrIndex.offset64_none, AddrIndex.offset64_scale1,
      BitVec.add_zero, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, Reg64s.get64_set64,
      reduceCtorEq, ↓reduceIte, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow] at *
    all_goals try simp only [hrdi, hrsi, hli, hlp, hlb, hlb1, hok1, hok2, Option.isSome_some,
      Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 32 4 rfl,
      BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, Nat.reduceLeDiff,
      CondCode.interp, StatusFlags.from_result, cf_sub, BitVec.reduceSetWidth, BitVec.xor_self,
      setl_val] at *
    all_goals try simp only [decide_eq_true_eq] at *
    all_goals have hb2' := bit_idx _ x.p8 hcl.2 hC.2.2.1
    all_goals have hb3' := bit_idx _ x.p8 hb2'.2 hC.2.2.1
    · exact hb1 _ _ (by have := rd_off _ x.p8 x.L hcl.2 hC.2.2.2.1; omega)
    · exact hb2 _ _ _ (by have := rd_off _ x.p8 x.L hb2'.2 hC.2.2.2.1; omega)
    · left
      refine ⟨"read_sbr_header.Lf31", rfl, by decide, ⟨hC, ?_, _, sp, amp, ⟨by omega, hb3'.2⟩, hA,
        hS _ _ _⟩, Or.inr ⟨trivial, by decide⟩⟩
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      exact hRh _ rfl
    · refine ⟨⟨hC, ⟨trivial, trivial, hrsp, hrbp, hrest⟩, ?_, ?_, _, sp, amp, ⟨by omega, hb3'.2⟩, ?_,
        hA, hS _ _ _⟩, trivial⟩
      · trivial
      · trivial
      · rfl

theorem blk_Le9d (k : Nat) (TlT : BitVec 64 → Mem 64 → Prop)
    (TlT' : BitVec 32 → BitVec 64 → Mem 64 → Prop) (TlC : BitVec 32 → BitVec 64 → Prop)
    (x : HArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k TlT TlT' TlC x ra t₀ "read_sbr_header.Le9d" := by
  cfg_block
  measure_hb "Le9d"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hR, hr10, hr9, i, sp, amp, ⟨hi1, hi2⟩, hr11, hA, hm⟩, hn⟩ := hs₀
    have hl : sp.length = 6 := hA.1
    hdr_read 3, 2
    · exact hbl
    · refine ⟨⟨hC, ⟨trivial, trivial, hrsp, hrbp, hrest⟩, _, _, amp, ?_, ?_, ?_, hstep _ _⟩,
        trivial⟩ <;> dsimp only
      · exact ⟨by omega, hcl.2⟩
      · exact spA_set hA 3 (by omega) _
      · rw [getD_set_eq _ _ _ (by omega)]; exact shr_lt _ 30 (by omega) (by omega)

theorem blk_Leca (k : Nat) (TlT : BitVec 64 → Mem 64 → Prop)
    (TlT' : BitVec 32 → BitVec 64 → Mem 64 → Prop) (TlC : BitVec 32 → BitVec 64 → Prop)
    (x : HArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k TlT TlT' TlC x ra t₀ "read_sbr_header.Leca" := by
  cfg_block
  measure_hb "Leca"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hR, i, sp, amp, ⟨hi1, hi2⟩, hA, h3, hm⟩, hn⟩ := hs₀
    have hl : sp.length = 6 := hA.1
    have hok := fun v => M_ok_sp (M_st_i hm v) 4 1 (by simp only [hl]; omega) (by simp only [hl]; omega)
    have hstep := fun i' w => hdr_step hm 4 (by simp only [hl]; omega) (by simp only [hl]; omega) i' w
    hdr_bit i
    · exact hbl
    · refine ⟨⟨hC, ⟨trivial, trivial, hrsp, hrbp, hrest⟩, _, _, amp, ?_, ?_, ?_, ?_, hstep _ _⟩,
        trivial⟩ <;> dsimp only
      · have := bit_idx i x.p8 hi2 hC.2.2.1; exact ⟨by omega, this.2⟩
      · exact spA_set hA 4 (by omega) _
      · rw [getD_set_ne _ _ _ _ (by decide)]; exact h3
      · rw [getD_set_eq _ _ _ (by omega), low8]; exact shr7_lt _

theorem blk_Lf31 (k : Nat) (TlT : BitVec 64 → Mem 64 → Prop)
    (TlT' : BitVec 32 → BitVec 64 → Mem 64 → Prop) (TlC : BitVec 32 → BitVec 64 → Prop)
    (x : HArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k TlT TlT' TlC x ra t₀ "read_sbr_header.Lf31" := by
  cfg_block
  measure_hb "Lf31"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hR, i, sp, amp, hB, hA, hm⟩, hn⟩ := hs₀
    have hl : sp.length = 6 := hA.1
    have hok := M_ok_sp hm 3 2 (by simp only [hl]; omega) (by simp only [hl]; omega)
    have hS := fun v => M_st_sp hm 3 2 (by simp only [hl]; omega) (by simp only [hl]; omega) v
    have hRh : ∀ s : MachineData, s = s₀ → Rs x t₀ s := fun _ h => h ▸ hR
    obtain ⟨hrdi, hrsi, hrsp, hrbp, hrest⟩ := hR
    clear hm
    simp only [arg0, arg1, BitVec.add_zero, Nat.reduceAdd, BitVec.add_assoc,
      BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at hok hS
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals try simp only [AddrIndex.offset64_none, BitVec.add_zero, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] at *
    all_goals try simp only [hrdi, hrsi, hok] at *
    have hmem := hS (BitVec.setWidth 16 258#64).toInt
    rw [show Int.toBytes 2 (BitVec.setWidth 16 258#64).toInt = Int.toBytes 2 258 from rfl,
      sp_102 _ hl] at hmem
    refine ⟨⟨hC, ⟨trivial, trivial, hrsp, hrbp, hrest⟩, by rw [low8]; decide, i, (sp.set 3 2).set 4 1,
      amp, hB, spA_set (spA_set hA 3 (by omega) _) 4 (by omega) _, ?_, ?_, hmem⟩, Nat.le_refl 0⟩
    · simp [List.getD_eq_getElem?_getD, hl]
    · simp [List.getD_eq_getElem?_getD, hl]

theorem blk_Lefb (k : Nat) (TlT : BitVec 64 → Mem 64 → Prop)
    (TlT' : BitVec 32 → BitVec 64 → Mem 64 → Prop) (TlC : BitVec 32 → BitVec 64 → Prop)
    (x : HArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k TlT TlT' TlC x ra t₀ "read_sbr_header.Lefb" := by
  cfg_block
  measure_hb "Lefb"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hR, i, sp, amp, ⟨hi1, hi2⟩, hA, h3, h4, hm⟩, hn⟩ := hs₀
    have hli := M_ld_i hm
    have hlp := M_ld_p8 hm
    have hlb := M_ld_buf hm
    have hbl := M_ld_bytes hm _ 4 (rd_off i x.p8 x.L hi2 hC.2.2.2.1)
    have hS := fun v => M_st_i hm v
    have hcl := clamp _ x.p8 2 hi2 hC.2.2.1 (by omega)
    have hRh : ∀ s : MachineData, s = s₀ → Rs x t₀ s := fun _ h => h ▸ hR
    obtain ⟨hrdi, hrsi, hrsp, hrbp, hrest⟩ := hR
    clear hm
    simp only [arg0, arg1, BitVec.add_zero] at hli hlp hlb hS
    vcgen [bswap32_havoc, shl_cl32_havoc]
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals try simp only [AddrIndex.offset64_none, AddrIndex.offset64_scale1,
      BitVec.add_zero, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, Reg64s.get64_set64,
      reduceCtorEq, ↓reduceIte, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow] at *
    all_goals try simp only [hrdi, hrsi, hli, hlp, hlb, Option.isSome_some,
      Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 32 4 rfl,
      BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, Nat.reduceLeDiff,
      CondCode.interp, StatusFlags.from_result, cf_sub, BitVec.reduceSetWidth] at *
    all_goals try simp only [decide_eq_true_eq] at *
    · exact hbl
    · left
      refine ⟨"read_sbr_header.Lf3a", rfl, by decide, ⟨hC, ?_, ?_, _, sp, amp, ⟨by omega, hcl.2⟩, hA,
        h3, h4, hS _⟩, Or.inr ⟨trivial, by decide⟩⟩
      · simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        exact hRh _ rfl
      · simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, BitVec.setWidth_setWidth_of_le,
          Nat.reduceLeDiff]
        exact shr_lt _ 30 (by omega) (by omega)

theorem blk_Lf3a (k : Nat) (TlT : BitVec 64 → Mem 64 → Prop)
    (TlT' : BitVec 32 → BitVec 64 → Mem 64 → Prop) (TlC : BitVec 32 → BitVec 64 → Prop)
    (x : HArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k TlT TlT' TlC x ra t₀ "read_sbr_header.Lf3a" := by
  cfg_block
  measure_hb "Lf3a"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hR, hr9, i, sp, amp, hB, hA, h3, h4, hm⟩, hn⟩ := hs₀
    have hl : sp.length = 6 := hA.1
    have hxl : x.sp.length = 6 := hC.1
    have hok := M_ok_sp hm 5 1 (by simp only [hl]; omega) (by simp only [hl]; omega)
    have hS := fun v => M_st_sp1 hm 5 (by simp only [hl]; omega) (by simp only [hl]; omega) v
    have hL := fun v => M_ld_loc x.sp hxl (hS v)
    have hN1 := fun v => M_ld_sp (hS v) 0 4 (by simp only [List.length_set, hl]; omega)
      (by simp only [List.length_set, hl]; omega)
    have hN2 := fun v => M_ld_sp (hS v) 4 2 (by simp only [List.length_set, hl]; omega)
      (by simp only [List.length_set, hl]; omega)
    have hok2 := fun v => M_ok_reset (hS v)
    have hR1 := fun v => M_st_reset (hS v) 1#32
    have hE : ∀ v : BitVec 8, sp.set 5 (UInt8.ofBitVec v) = x.sp →
        s₀.dmem.storeInt (arg0 t₀ + BitVec.ofNat 64 (0x1c + 5)) 1 v.toInt =⋆ M k x ra t₀
          (Fr t₀ (Lsp t₀ x.sp)) (St i (sp.set 5 (UInt8.ofBitVec v)) amp
            (rsOf x (sp.set 5 (UInt8.ofBitVec v))) x.lb x.lg x.ip x.sm) (TlT (arg0 t₀)) := by
      intro v h
      rw [show rsOf x (sp.set 5 (UInt8.ofBitVec v)) = x.reset from if_pos h]
      exact hS v
    have hNe : ∀ v : BitVec 8, ¬ sp.set 5 (UInt8.ofBitVec v) = x.sp →
        (s₀.dmem.storeInt (arg0 t₀ + BitVec.ofNat 64 (0x1c + 5)) 1 v.toInt).storeInt
          (arg0 t₀ + 0x18#64) 4 (1#32).toInt =⋆ M k x ra t₀
          (Fr t₀ (Lsp t₀ x.sp)) (St i (sp.set 5 (UInt8.ofBitVec v)) amp
            (rsOf x (sp.set 5 (UInt8.ofBitVec v))) x.lb x.lg x.ip x.sm) (TlT (arg0 t₀)) := by
      intro v h
      rw [show rsOf x (sp.set 5 (UInt8.ofBitVec v)) = 1#32 from if_neg h]
      exact hR1 v
    have hRh : ∀ s : MachineData, s = s₀ → Rs x t₀ s := fun _ h => h ▸ hR
    obtain ⟨hrdi, hrsi, hrsp, hrbp, hrest⟩ := hR
    clear hm hS hR1
    simp only [arg0, arg1, BitVec.add_zero, Nat.reduceAdd, List.drop_zero] at hok hL hN1 hN2 hok2 hE hNe
    have ha1 : t₀.regs.get64 .rsp - 8#64 + (-20 : Int64).toBitVec = t₀.regs.get64 .rsp - 28#64 := by
      rw [show (-20 : Int64).toBitVec = 0xffffffffffffffec#64 by decide]; bv_omega
    have ha2 : t₀.regs.get64 .rsp - 8#64 + (-24 : Int64).toBitVec = t₀.regs.get64 .rsp - 32#64 := by
      rw [show (-24 : Int64).toBitVec = 0xffffffffffffffe8#64 by decide]; bv_omega
    vcgen [bswap32_havoc, shl_cl32_havoc]
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals try simp only [AddrIndex.offset64_none, AddrIndex.offset64_scale1,
      BitVec.add_zero, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, Reg64s.get64_set64,
      reduceCtorEq, ↓reduceIte, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow] at *
    all_goals try simp only [hrdi, hrsi, hrsp, hrbp, ha1, ha2] at *
    all_goals try simp only [hok, hok2, hL, hN1, hN2, Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    · rename_i hz
      simp only [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, Nat.reduceLeDiff,
        low16, CondCode.interp, StatusFlags.from_result, beq_iff_eq] at hz
      have hor := or_xor_zero _ _ _ _ hz
      have heq := sp_eq_of x.sp _ hxl (by simp only [List.length_set, hl]) hor.1 hor.2
      left
      refine ⟨"read_sbr_header.Lf61", rfl, by decide, ⟨hC, ?_, i, _, amp,
        x.lb, x.lg, x.ip, x.sm, hB, spA_set hA 5 (by omega) _, ⟨?_, ?_, ?_⟩, ⟨rfl, rfl, rfl, rfl⟩,
        hE _ heq⟩, Or.inr ⟨trivial, by decide⟩⟩
      · simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        exact hRh _ rfl
      · rw [getD_set_ne _ _ _ _ (by decide)]; exact h3
      · rw [getD_set_ne _ _ _ _ (by decide)]; exact h4
      · rw [getD_set_eq _ _ _ (by omega)]; exact hr9
    · rename_i hz
      simp only [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, Nat.reduceLeDiff,
        low16, CondCode.interp, StatusFlags.from_result, beq_iff_eq] at hz
      have hne : ¬ sp.set 5 (UInt8.ofBitVec _) = x.sp := fun h => by
        rw [h] at hz; simp only [List.take_of_length_le (show (x.sp.drop 4).length ≤ 2 by simp [hxl])] at hz
        simp at hz
      refine ⟨⟨hC, ⟨trivial, trivial, trivial, trivial, hrest⟩, i, _, amp,
        x.lb, x.lg, x.ip, x.sm, hB, spA_set hA 5 (by omega) _, ⟨?_, ?_, ?_⟩, ⟨rfl, rfl, rfl, rfl⟩,
        hNe _ hne⟩, Nat.le_refl 0⟩
      · rw [getD_set_ne _ _ _ _ (by decide)]; exact h3
      · rw [getD_set_ne _ _ _ _ (by decide)]; exact h4
      · rw [getD_set_eq _ _ _ (by omega)]; exact hr9

end Kraken.Examples.Sbr.Hdr
