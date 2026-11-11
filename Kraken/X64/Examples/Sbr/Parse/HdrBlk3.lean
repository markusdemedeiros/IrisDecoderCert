import Kraken.X64.Examples.Sbr.Parse.HdrStep

/-!
# `read_sbr_header`: the block obligations of the limiter fields

`Lf61` tests `bs_header_extra_2`; `Lf6d`..`Lff8` read `bs_limiter_bands`, `bs_limiter_gains`,
`bs_interpol_freq` and `bs_smoothing_mode` (`hdr_rdn`); `L102d` stores their defaults. Both
`Lff8` and `L102d` end with the compare of `bs_limiter_bands` with its old value.
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

theorem blk_Lf61 (k : Nat) (TlT : BitVec 64 → Mem 64 → Prop)
    (TlT' : BitVec 32 → BitVec 64 → Mem 64 → Prop) (TlC : BitVec 32 → BitVec 64 → Prop)
    (x : HArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k TlT TlT' TlC x ra t₀ "read_sbr_header.Lf61" := by
  cfg_block
  measure_hb "Lf61"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hR, hP⟩, hn⟩ := hs₀
    have hRh : ∀ s : MachineData, s = s₀ → Rs x t₀ s := fun _ h => h ▸ hR
    obtain ⟨hrdi, hrsi, hrsp, hrbp, hrest⟩ := hR
    vcgen [shl_cl32_havoc]
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    · left
      refine ⟨"read_sbr_header.L102d", rfl, by decide, ⟨hC, ?_, hP⟩, Or.inr ⟨rfl, by decide⟩⟩
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      exact hRh _ rfl
    · refine ⟨⟨hC, ?_, hP⟩, Nat.le_refl 0⟩
      try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      exact hRh _ rfl

theorem blk_Lf6d (k : Nat) (TlT : BitVec 64 → Mem 64 → Prop)
    (TlT' : BitVec 32 → BitVec 64 → Mem 64 → Prop) (TlC : BitVec 32 → BitVec 64 → Prop)
    (x : HArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k TlT TlT' TlC x ra t₀ "read_sbr_header.Lf6d" := by
  cfg_block
  measure_hb "Lf6d"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hR, i, sp, amp, lb, lg, ip, sm, ⟨hi1, hi2⟩, hA, hSB, hP, hm⟩, hn⟩ := hs₀
    have hok := fun v => M_ok_lb (M_st_i hm v)
    have hstep := fun i' v => M_st_lb (M_st_i hm i') v
    have hcl := clamp i x.p8 2 hi2 hC.2.2.1 (by omega)
    hdr_rdn i, 4
    · exact hbl
    · refine ⟨⟨hC, ⟨trivial, trivial, hrsp, hrbp, hrest⟩, _, sp, amp, _, lg, ip, sm, ?_, hA, hSB, ?_,
        hstep _ _⟩, trivial⟩ <;> try dsimp only
      · exact ⟨by omega, hcl.2⟩
      · exact ⟨shr30_lt _, hP.2.1, hP.2.2.1, hP.2.2.2⟩

theorem blk_Lf98 (k : Nat) (TlT : BitVec 64 → Mem 64 → Prop)
    (TlT' : BitVec 32 → BitVec 64 → Mem 64 → Prop) (TlC : BitVec 32 → BitVec 64 → Prop)
    (x : HArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k TlT TlT' TlC x ra t₀ "read_sbr_header.Lf98" := by
  cfg_block
  measure_hb "Lf98"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hR, i, sp, amp, lb, lg, ip, sm, ⟨hi1, hi2⟩, hA, hSB, hP, hm⟩, hn⟩ := hs₀
    have hok := fun v => M_ok_lg (M_st_i hm v)
    have hstep := fun i' v => M_st_lg (M_st_i hm i') v
    have hcl := clamp i x.p8 2 hi2 hC.2.2.1 (by omega)
    hdr_rdn i, 4
    · exact hbl
    · refine ⟨⟨hC, ⟨trivial, trivial, hrsp, hrbp, hrest⟩, _, sp, amp, lb, _, ip, sm, ?_, hA, hSB, ?_,
        hstep _ _⟩, trivial⟩ <;> try dsimp only
      · exact ⟨by omega, hcl.2⟩
      · exact ⟨hP.1, shr30_lt _, hP.2.2.1, hP.2.2.2⟩

theorem blk_Lfca (k : Nat) (TlT : BitVec 64 → Mem 64 → Prop)
    (TlT' : BitVec 32 → BitVec 64 → Mem 64 → Prop) (TlC : BitVec 32 → BitVec 64 → Prop)
    (x : HArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k TlT TlT' TlC x ra t₀ "read_sbr_header.Lfca" := by
  cfg_block
  measure_hb "Lfca"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hR, i, sp, amp, lb, lg, ip, sm, ⟨hi1, hi2⟩, hA, hSB, hP, hm⟩, hn⟩ := hs₀
    have hok := fun v => M_ok_ip (M_st_i hm v)
    have hstep := fun i' v => M_st_ip (M_st_i hm i') v
    hdr_rdn i, 1
    · exact hbl
    · refine ⟨⟨hC, ⟨trivial, trivial, hrsp, hrbp, hrest⟩, _, sp, amp, lb, lg, _, sm, ?_, hA, hSB, ?_,
        hstep _ _⟩, trivial⟩ <;> try dsimp only
      · have := bit_idx i x.p8 hi2 hC.2.2.1; exact ⟨by omega, this.2⟩
      · exact ⟨hP.1, hP.2.1, and1_lt _, hP.2.2.2⟩

theorem blk_Lff8 (k : Nat) (TlT : BitVec 64 → Mem 64 → Prop)
    (TlT' : BitVec 32 → BitVec 64 → Mem 64 → Prop) (TlC : BitVec 32 → BitVec 64 → Prop)
    (x : HArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k TlT TlT' TlC x ra t₀ "read_sbr_header.Lff8" := by
  cfg_block
  measure_hb "Lff8"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hR, i, sp, amp, lb, lg, ip, sm, ⟨hi1, hi2⟩, hA, hSB, hP, hm⟩, hn⟩ := hs₀
    have hr8 : s₀.regs.get64 .r8 = x.lb.setWidth 64 := hR.2.2.2.2.2.1
    have hok := fun v => M_ok_sm (M_st_i hm v)
    have hstep := fun i' v => M_st_sm (M_st_i hm i') v
    have hlb2 := fun i' => M_ld_lb (M_st_i hm i')
    have hE : ∀ i' v, lb = x.lb → (s₀.dmem.storeInt (arg1 t₀ + 8#64) 4 i'.toInt).storeInt
        (arg0 t₀ + 0x38#64) 4 v.toInt =⋆ M k x ra t₀ (Fr t₀ (Lsp t₀ x.sp))
          (St i' sp amp (rsOf x sp) lb lg ip v)
          (TlOut TlT TlT' x t₀ (St i' sp amp (rsOf x sp) lb lg ip v)) := by
      intro i' v h
      rw [TlOut, if_neg (fun hc => hc.1 h)]
      exact hstep i' v
    simp only [arg0, arg1, BitVec.add_zero] at hlb2 hE
    hdr_rdn i, 1
    all_goals try simp only [hr8, hlb2, Option.some.injEq, BitVec.ofInt_ofBytes_toBytes 32 4 rfl] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, Nat.reduceLeDiff] at *
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 32 4 rfl] at *
    all_goals have hb := bit_idx i x.p8 hi2 hC.2.2.1
    · exact hbl
    · rfl
    · rename_i hz
      have hne : ¬ lb = x.lb := fun h => by subst h; simp at hz
      left
      refine ⟨"read_sbr_header.L1054", rfl, by decide, ⟨hC, ?_, _, sp, amp, lb, lg, ip, _,
        ⟨by omega, hb.2⟩, hA, hSB, ⟨⟨hP.1, hP.2.1, hP.2.2.1, and1_lt _⟩, hne⟩, hstep _ _⟩,
        Or.inr ⟨by trivial, by decide⟩⟩
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      exact hRh _ rfl
    · rename_i hz
      have heq : lb = x.lb := (zf_sub _ _).1 (by simpa using hz)
      left
      refine ⟨"read_sbr_header.L1065", rfl, by decide, ⟨hC, ?_, ?_, St _ sp amp (rsOf x sp) lb lg ip _,
        ?_, hE _ _ heq⟩, Or.inr ⟨by trivial, by decide⟩⟩
      all_goals try dsimp only
      · obtain ⟨_, _, hsp, hbp, hbx, _, h12, h13, h15⟩ := hRh _ rfl
        simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        exact ⟨hsp, hbp, hbx, h12, h13, h15⟩
      · simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        exact (hRh _ rfl).2.1
      · exact ⟨rfl, rfl, hA, hSB, rfl, ⟨hP.1, hP.2.1, hP.2.2.1, and1_lt _⟩, by omega, hb.2⟩

theorem blk_L102d (k : Nat) (TlT : BitVec 64 → Mem 64 → Prop)
    (TlT' : BitVec 32 → BitVec 64 → Mem 64 → Prop) (TlC : BitVec 32 → BitVec 64 → Prop)
    (x : HArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k TlT TlT' TlC x ra t₀ "read_sbr_header.L102d" := by
  cfg_block
  measure_hb "L102d"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hR, i, sp, amp, lb, lg, ip, sm, hB, hA, hSB, hP, hm⟩, hn⟩ := hs₀
    have hr8 : s₀.regs.get64 .r8 = x.lb.setWidth 64 := hR.2.2.2.2.2.1
    have ok1 := M_ok_lblg hm
    have hS1 := M_st_lblg hm
    have ok2 := M_ok_ip hS1
    have hS2 := M_st_ip hS1 1#32
    have ok3 := M_ok_sm hS2
    have hS3 := M_st_sm hS2 1#32
    have hE : lb = x.lb → 2#32 = x.lb → ((s₀.dmem.storeInt (arg0 t₀ + 0x2c#64) 8 (0x200000002 : Int)).storeInt
        (arg0 t₀ + 0x34#64) 4 (1#32).toInt).storeInt (arg0 t₀ + 0x38#64) 4 (1#32).toInt
        =⋆ M k x ra t₀ (Fr t₀ (Lsp t₀ x.sp)) (St i sp amp (rsOf x sp) 2#32 2#32 1#32 1#32)
          (TlOut TlT TlT' x t₀ (St i sp amp (rsOf x sp) 2#32 2#32 1#32 1#32)) := by
      intro h h2
      rw [TlOut, if_neg (fun hc => hc.1 h2)]
      exact hS3
    have hRh : ∀ s : MachineData, s = s₀ → Rs x t₀ s := fun _ h => h ▸ hR
    obtain ⟨hrdi, hrsi, hrsp, hrbp, hrest⟩ := hR
    clear hm hS1 hS2
    simp only [arg0, arg1, BitVec.add_zero] at ok1 ok2 ok3 hS3 hE
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals try simp only [AddrIndex.offset64_none, BitVec.add_zero, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] at *
    all_goals try simp only [show (BitVec.setWidth 64 8589934594#64).toInt = 8589934594 by decide,
      show BitVec.setWidth 32 1#64 = 1#32 by decide] at *
    all_goals try simp only [hrdi, hr8, ok1, ok2, ok3] at *
    all_goals try simp only [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, Nat.reduceLeDiff,
      BitVec.reduceSetWidth, CondCode.interp, StatusFlags.from_result] at *
    · rename_i hz
      have h2 : 2#32 = x.lb := (zf_sub _ _).1 hz
      left
      refine ⟨"read_sbr_header.L1065", rfl, by decide, ⟨hC, ?_, ?_, St i sp amp (rsOf x sp) 2#32 2#32 1#32 1#32,
        ?_, hE hP.1 h2⟩, Or.inr ⟨by trivial, by decide⟩⟩
      all_goals try dsimp only
      · obtain ⟨_, _, hsp, hbp, hbx, _, h12, h13, h15⟩ := hRh _ rfl
        simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        exact ⟨hsp, hbp, hbx, h12, h13, h15⟩
      · simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        exact (hRh _ rfl).2.1
      · exact ⟨rfl, rfl, hA, hSB, rfl, ⟨by decide, by decide, by decide, by decide⟩, hB⟩
    · rename_i hz
      have h2 : ¬ 2#32 = x.lb := fun h => by rw [← h] at hz; revert hz; decide
      refine ⟨⟨hC, ⟨trivial, hrsi, hrsp, hrbp, hrest⟩, i, sp, amp, 2#32, 2#32, 1#32, 1#32, hB, hA, hSB,
        ⟨⟨by decide, by decide, by decide, by decide⟩, fun h => h2 h⟩, hS3⟩, trivial⟩

end Kraken.Examples.Sbr.Hdr
