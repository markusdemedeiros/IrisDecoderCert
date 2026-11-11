import Kraken.X64.Examples.Sbr.Parse.HdrStep

/-!
# `read_sbr_header`: the block obligations up to the frequency fields

The entry pushes and sets `start`/`ready`/`usac`; `Ld1d` copies `spectrum_params` to the locals
and tests `is_usac`; the field reads `Ld32`..`Le1a` use `hdr_read` (`hdr_step` for the two
stores); `Ld91` reads `bs_amp_res`.
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

theorem blk_entry (k : Nat) (TlT : BitVec 64 → Mem 64 → Prop)
    (TlT' : BitVec 32 → BitVec 64 → Mem 64 → Prop) (TlC : BitVec 32 → BitVec 64 → Prop)
    (x : HArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k TlT TlT' TlC x ra t₀ "read_sbr_header" := by
  cfg_block
  measure_hb "entry"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨rfl, hC, u, hm⟩, hn⟩ := hs₀
    obtain ⟨hp1, hp2, hp3, hP⟩ := M_push hm (s₀.regs.get64 .rbp) (s₀.regs.get64 .r14)
      (s₀.regs.get64 .rbx)
    have hli := M_ld_i hP
    have hlb := M_ld_lb hP
    have hok1 := M_ok_sr hP
    have hS1 := M_st_sr hP
    have hok2 := M_ok_us hS1
    have hS2 := fun v => M_st_us hS1 v
    clear hm hP
    simp only [arg0, arg1, arg2, BitVec.add_zero] at hli hlb hok1 hS1 hok2 hS2
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals try simp only [BitVec.sub_sub_eight, BitVec.reduceAdd, AddrIndex.offset64_none,
      BitVec.add_zero, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat] at *
    all_goals try simp only [hli, hlb, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.setWidth_eq,
      show (1#64).toInt = 1 by decide] at *
    · exact hp1
    · exact hp2
    · exact hp3
    · rfl
    · rfl
    · exact hok1
    · exact hok2
    refine ⟨⟨hC, ⟨trivial, trivial, by bv_omega, trivial, rfl, rfl, trivial, trivial, trivial⟩,
      trivial, hS2 _⟩, Nat.le_refl 0⟩

theorem blk_Ld1d (k : Nat) (TlT : BitVec 64 → Mem 64 → Prop)
    (TlT' : BitVec 32 → BitVec 64 → Mem 64 → Prop) (TlC : BitVec 32 → BitVec 64 → Prop)
    (x : HArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k TlT TlT' TlC x ra t₀ "read_sbr_header.Ld1d" := by
  cfg_block
  measure_hb "Ld1d"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hR, hdx, hm⟩, hn⟩ := hs₀
    have hl : x.sp.length = 6 := hC.1
    have hRh : ∀ s : MachineData, s = s₀ → Rs x t₀ s := fun _ h => h ▸ hR
    obtain ⟨hrdi, hrsi, hrsp, hrbp, hrest⟩ := hR
    have ha1 : t₀.regs.get64 .rsp - 8#64 + (-20 : Int64).toBitVec = t₀.regs.get64 .rsp - 28#64 := by
      rw [show (-20 : Int64).toBitVec = 0xffffffffffffffec#64 by decide]; bv_omega
    have ha2 : t₀.regs.get64 .rsp - 8#64 + (-24 : Int64).toBitVec = t₀.regs.get64 .rsp - 32#64 := by
      rw [show (-24 : Int64).toBitVec = 0xffffffffffffffe8#64 by decide]; bv_omega
    have ldA := M_ld_sp hm 4 2 (by simp [hl]) (by simp [hl])
    have ok1 := (M_loc1 hm 0).1
    have h1 := fun v => (M_loc1 hm v).2
    have ldB := fun v => M_ld_sp (h1 v) 0 4 (by simp [hl]) (by simp [hl])
    have ok2 := fun v => (M_loc2 _ (h1 v) 0).1
    have h2 := fun v w => (M_loc2 _ (h1 v) w).2
    have ldI := fun v w => M_ld_i (h2 v w)
    have hfin := fun v w (hv : Int.toBytes 2 v = x.sp.drop 4) (hw : Int.toBytes 4 w = x.sp.take 4) =>
      M_lsp hv hw (h2 v w)
    have e1 : Int.toBytes 2 (BitVec.ofInt 16 (Int.ofBytes ((x.sp.drop 4).take 2))).toInt
        = x.sp.drop 4 := by
      rw [toBytes2_ofBytes _ (by simp [hl]), List.take_take, Nat.min_self,
        List.take_of_length_le (by simp [hl])]
    have e2 := toBytes4_ofBytes (x.sp.take 4) (by simp [hl])
    simp only [List.take_take, Nat.min_self] at e2
    clear hm h1
    simp only [arg0, arg1, arg2, Nat.reduceAdd, List.drop_zero] at ldA ok1 ldB ok2 h2 ldI hfin
    vcgen [bswap32_havoc, shl_cl32_havoc]
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals try simp only [AddrIndex.offset64_none, AddrIndex.offset64_scale1,
      BitVec.add_zero, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, Reg64s.get64_set64,
      reduceCtorEq, ↓reduceIte, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow] at *
    all_goals try simp only [hrdi, hrsi, hrsp, hrbp, hdx, ha1, ha2, ldA, ldB, ldI, ok1, ok2,
      Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 32 4 rfl,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, Nat.reduceLeDiff,
      CondCode.interp, StatusFlags.from_result, BitVec.and_self] at *
    · rename_i hz
      have hu : usacOf t₀ = 0#32 := by simpa using hz
      left
      refine ⟨"read_sbr_header.Ld91", rfl, by decide, ⟨hC, ?_, hu, ?_, hfin _ _ e1 e2⟩,
        Or.inr ⟨trivial, by decide⟩⟩
      · simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        exact hRh _ rfl
      · simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    · rename_i hz
      have hu : usacOf t₀ ≠ 0#32 := by simpa using hz
      exact ⟨⟨hC, ⟨trivial, trivial, trivial, trivial, hrest⟩, hu, trivial, hfin _ _ e1 e2⟩, trivial⟩

theorem blk_Ld32 (k : Nat) (TlT : BitVec 64 → Mem 64 → Prop)
    (TlT' : BitVec 32 → BitVec 64 → Mem 64 → Prop) (TlC : BitVec 32 → BitVec 64 → Prop)
    (x : HArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k TlT TlT' TlC x ra t₀ "read_sbr_header.Ld32" := by
  cfg_block
  measure_hb "Ld32"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hR, hu, hrax, hm⟩, hn⟩ := hs₀
    have hi2 : x.idx.toNat ≤ x.p8.toNat := hC.2.1
    have hl : x.sp.length = 6 := hC.1
    hdr_read 0, 4
    · exact hbl
    · refine ⟨⟨hC, ⟨trivial, trivial, hrsp, hrbp, hrest⟩, hu, _, _, ?_, ?_, ?_, ?_, hstep _ _⟩,
        trivial⟩ <;> dsimp only
      · exact ⟨by omega, hcl.2⟩
      · simp only [List.length_set, hl]
      · rw [getD_set_eq _ _ _ (by omega)]; exact shr_lt _ 28 (by omega) (by omega)
      · rw [getD_set_ne _ _ _ _ (by decide)]

theorem blk_Ld61 (k : Nat) (TlT : BitVec 64 → Mem 64 → Prop)
    (TlT' : BitVec 32 → BitVec 64 → Mem 64 → Prop) (TlC : BitVec 32 → BitVec 64 → Prop)
    (x : HArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k TlT TlT' TlC x ra t₀ "read_sbr_header.Ld61" := by
  cfg_block
  measure_hb "Ld61"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hR, hu, i, sp, ⟨hi1, hi2⟩, hl, h0, h2, hm⟩, hn⟩ := hs₀
    hdr_read 1, 4
    · exact hbl
    · left
      refine ⟨"read_sbr_header.Le45", rfl, by decide, ⟨hC, ?_, ?_⟩, Or.inr ⟨trivial, by decide⟩⟩
      · simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        exact hRh _ rfl
      refine ⟨_, _, x.amp, ?_, ?_, hstep _ _⟩ <;> dsimp only
      · exact ⟨by omega, hcl.2⟩
      · refine ⟨by simp only [List.length_set, hl], ?_, ?_, fun h => absurd h hu, fun _ => ⟨?_, rfl⟩⟩
        · rw [getD_set_ne _ _ _ _ (by decide)]; exact h0
        · rw [getD_set_eq _ _ _ (by omega)]; exact shr_lt _ 28 (by omega) (by omega)
        · rw [getD_set_ne _ _ _ _ (by decide)]; exact h2

theorem blk_Ldbd (k : Nat) (TlT : BitVec 64 → Mem 64 → Prop)
    (TlT' : BitVec 32 → BitVec 64 → Mem 64 → Prop) (TlC : BitVec 32 → BitVec 64 → Prop)
    (x : HArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k TlT TlT' TlC x ra t₀ "read_sbr_header.Ldbd" := by
  cfg_block
  measure_hb "Ldbd"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hR, hu, i, amp, ⟨hi1, hi2⟩, ha, hm⟩, hn⟩ := hs₀
    have hl : x.sp.length = 6 := hC.1
    hdr_read 0, 4
    · exact hbl
    · refine ⟨⟨hC, ⟨trivial, trivial, hrsp, hrbp, hrest⟩, hu, _, _, amp, ?_, ha, ?_, ?_,
        hstep _ _⟩, trivial⟩ <;> dsimp only
      · exact ⟨by omega, hcl.2⟩
      · simp only [List.length_set, hl]
      · rw [getD_set_eq _ _ _ (by omega)]; exact shr_lt _ 28 (by omega) (by omega)

theorem blk_Lde8 (k : Nat) (TlT : BitVec 64 → Mem 64 → Prop)
    (TlT' : BitVec 32 → BitVec 64 → Mem 64 → Prop) (TlC : BitVec 32 → BitVec 64 → Prop)
    (x : HArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k TlT TlT' TlC x ra t₀ "read_sbr_header.Lde8" := by
  cfg_block
  measure_hb "Lde8"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hR, hu, i, sp, amp, ⟨hi1, hi2⟩, ha, hl, h0, hm⟩, hn⟩ := hs₀
    hdr_read 1, 4
    · exact hbl
    · refine ⟨⟨hC, ⟨trivial, trivial, hrsp, hrbp, hrest⟩, hu, _, _, amp, ?_, ha, ?_, ?_, ?_,
        hstep _ _⟩, trivial⟩ <;> dsimp only
      · exact ⟨by omega, hcl.2⟩
      · simp only [List.length_set, hl]
      · rw [getD_set_ne _ _ _ _ (by decide)]; exact h0
      · rw [getD_set_eq _ _ _ (by omega)]; exact shr_lt _ 28 (by omega) (by omega)

theorem blk_Le1a (k : Nat) (TlT : BitVec 64 → Mem 64 → Prop)
    (TlT' : BitVec 32 → BitVec 64 → Mem 64 → Prop) (TlC : BitVec 32 → BitVec 64 → Prop)
    (x : HArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k TlT TlT' TlC x ra t₀ "read_sbr_header.Le1a" := by
  cfg_block
  measure_hb "Le1a"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hR, hu, i, sp, amp, ⟨hi1, hi2⟩, ha, hl, h0, h1, hm⟩, hn⟩ := hs₀
    hdr_read 2, 3
    · exact hbl
    · refine ⟨⟨hC, ⟨trivial, trivial, hrsp, hrbp, hrest⟩, _, _, amp, ?_, ?_, hstep _ _⟩,
        trivial⟩ <;> dsimp only
      · exact ⟨by omega, hcl.2⟩
      · refine ⟨by simp only [List.length_set, hl], ?_, ?_, fun _ => ⟨?_, ha⟩, fun h => absurd hu h⟩
        · rw [getD_set_ne _ _ _ _ (by decide)]; exact h0
        · rw [getD_set_ne _ _ _ _ (by decide)]; exact h1
        · rw [getD_set_eq _ _ _ (by omega)]; exact shr_lt _ 29 (by omega) (by omega)

theorem blk_Ld91 (k : Nat) (TlT : BitVec 64 → Mem 64 → Prop)
    (TlT' : BitVec 32 → BitVec 64 → Mem 64 → Prop) (TlC : BitVec 32 → BitVec 64 → Prop)
    (x : HArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k TlT TlT' TlC x ra t₀ "read_sbr_header.Ld91" := by
  cfg_block
  measure_hb "Ld91"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hR, hu, hrax, hm⟩, hn⟩ := hs₀
    have hi2 : x.idx.toNat ≤ x.p8.toNat := hC.2.1
    have hok := fun v => M_ok_amp (M_st_i hm v)
    have hstep := fun i' v => M_st_amp (M_st_i hm i') v
    hdr_bit x.idx
    · exact hbl
    · refine ⟨⟨hC, ⟨trivial, trivial, hrsp, hrbp, hrest⟩, hu, _, _, ?_, ?_, hstep _ _⟩, trivial⟩
        <;> dsimp only
      · exact bit_idx x.idx x.p8 hi2 hC.2.2.1
      · exact and1_lt _

end Kraken.Examples.Sbr.Hdr
