import Kraken.X64.Examples.Sbr.Parse.TlimAcc

/-!
# `sbr_make_f_tablelim`: `bs_limiter_bands == 0` (`L438a`, `L4398`, `L43a4`)
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Tlim

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

theorem blk_L438a (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L438a" := by
  cfg_block
  measure_hb "L438a"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨⟨hsp, hbp, h13⟩, hbx⟩, hlb, stk, pb, hL, hP, hm⟩, hn⟩ := hs₀
    rw [var_L438a] at hn
    subst hn
    have hC' := hC
    obtain ⟨-, -, -, -, hlow, hlim, -⟩ := hC'
    have hld := RO_ftLow (focus (T_ro k x ra t₀ (Saved t₀) _) hm) hlow 0 (by omega)
      (addr := s₀.regs.get64 .rbx + 0x4c252#64) (by rw [hbx]; simp)
    have hfl := focus (T_fl k x ra t₀ (Saved t₀) (st0 x stk pb)) hm
    have hl60 : x.a.ftLim.length = 60 := hlim
    have hl2 := ld16 hfl 0 (addr := s₀.regs.get64 .rbx + 0x4c2f2#64) (by rw [hbx]; simp) (by simp only; omega) (by simp only; omega)
    have hs2 : Hide _ := st16 hfl 0 (addr := s₀.regs.get64 .rbx + 0x4c2f2#64) (by rw [hbx]; simp) (by simp only; omega) (by simp only; omega)
    clear hm hfl
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals simp only [AddrIndex.offset64_none, BitVec.add_zero, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, hld, hl2, Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    rw [tab_L4398, var_L4398]
    refine ⟨⟨hC, ⟨⟨?_, ?_, ?_⟩, ?_⟩, hlb, stk, pb, hL, ?_⟩, Nat.le_refl 0⟩
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hsp, hbp, h13, hbx]
    rw [← setW2_congr x.a.ftLim 0 (sw16_val _ (u16_lt _ _))]
    unfold Hide at hs2
    rw [hbx] at hs2
    exact focus (T_fl k x ra t₀ (Saved t₀) ⟨_, _, stk, pb⟩).symm (hs2 _)

theorem blk_L4398 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L4398" := by
  cfg_block
  measure_hb "L4398"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨⟨hsp, hbp, h13⟩, hbx⟩, hlb, stk, pb, hL, hm⟩, hn⟩ := hs₀
    rw [var_L4398] at hn
    subst hn
    have hC' := hC
    obtain ⟨-, hn0, -⟩ := hC'
    have hld := RO_n0 (focus (T_ro k x ra t₀ (Saved t₀) _) hm)
    rw [show sA t₀ = s₀.regs.get64 .rbx from hbx.symm] at hld
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals simp only [AddrIndex.offset64_none, BitVec.add_zero, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, hld, Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals simp only [BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl, BitVec.ofInt_toInt,
      BitVec.ofInt_natCast, zx_small _ (show x.a.n0 < 2 ^ 31 by omega)] at *
    all_goals first
      | (exfalso; rename_i hc; simp at hc; bv_omega)
      | (rw [tab_L43a4, var_L43a4]
         refine ⟨⟨hC, ⟨⟨?_, ?_, ?_⟩, ?_⟩, hlb, ?_, stk, pb, hL, hmT⟩, Nat.le_refl 0⟩
         all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hsp, hbp, h13, hbx])

/-- The array `bs_limiter_bands == 0` leaves. -/
theorem fl_zero (l low : List UInt8) (hl : l.length = 60) (n0 : Nat) (V : Int)
    (hV : V % 65536 = (u16 low n0 : Int) % 65536) :
    setW2 (setW2 l 0 (u16 low 0 : Int)) 1 V = mk16 30 (fun q => if q = 0 then u16 low 0
      else if q = 1 then u16 low n0 else u16 l q) := by
  have h1 : (setW2 l 0 (u16 low 0 : Int)).length = 60 := by rw [setW2_length _ _ _ (by omega)]; exact hl
  apply mk16_ext (by rw [setW2_length _ _ _ (by omega)]; exact h1)
  intro i hi
  rw [u16_setW2 _ _ _ (by omega), u16_setW2 _ _ _ (by omega)]
  have a0 := u16_lt low 0
  have a1 := u16_lt low n0
  have a2 := u16_lt l i
  by_cases e1 : i = 1
  · subst e1; simp only [↓reduceIte, Nat.one_ne_zero]; omega
  · by_cases e0 : i = 0
    · subst e0; simp only [↓reduceIte, Nat.zero_ne_one]; omega
    · simp only [e0, e1, ↓reduceIte]; omega

theorem blk_L43a4 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L43a4" := by
  cfg_block
  measure_hb "L43a4"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨⟨hsp, hbp, h13⟩, hbx⟩, hlb, hax, stk, pb, hL, hm⟩, hn⟩ := hs₀
    rw [var_L43a4] at hn
    subst hn
    have hC' := hC
    obtain ⟨-, hn0, -, -, hlow, hlim, -⟩ := hC'
    have hL' := hL
    obtain ⟨hL1, hL2, hL3⟩ := hL'
    have hld := RO_ftLow (focus (T_ro k x ra t₀ (Saved t₀) _) hm) hlow x.a.n0 (by omega)
      (addr := s₀.regs.get64 .rbx + s₀.regs.get64 .rax * 2#64 + 311890#64)
      (by rw [hbx, hax]; simp only [sA]; bv_omega)
    have hfl := focus (T_fl k x ra t₀ (Saved t₀) ⟨setW2 x.a.ftLim 0 (u16 x.a.ftLow 0), x.a.nlim, stk, pb⟩) hm
    have hlen : (setW2 x.a.ftLim 0 (u16 x.a.ftLow 0 : Int)).length = 60 := by
      rw [setW2_length _ _ _ (by omega)]; exact hlim
    have hl2 := ld16 hfl 1 (addr := s₀.regs.get64 .rbx + 312052#64) (by rw [hbx]; simp only [sA, pA]; bv_omega)
      (by simp only; omega) (by simp only; omega)
    have hs2 := st16 hfl 1 (addr := s₀.regs.get64 .rbx + 312052#64) (by rw [hbx]; simp only [sA, pA]; bv_omega)
      (by simp only; omega) (by simp only; omega)
    have hb' : s₀.regs.get64 .rbx + 311788#64 = sA t₀ + 0x4c1ec#64 := by rw [hbx]
    have hn4 : ∀ v, (s₀.dmem.storeInt (s₀.regs.get64 .rbx + 312052#64) 2 v) =⋆
        c4 (sA t₀ + 0x4c1ec#64) x.a.nlim
          ⋆ Tnl k x ra t₀ (Saved t₀) (setW2 (setW2 x.a.ftLim 0 (u16 x.a.ftLow 0 : Int)) 1 v) stk pb :=
      fun v => focus (T_nl k x ra t₀ (Saved t₀) ⟨_, x.a.nlim, stk, pb⟩)
        (focus (T_fl k x ra t₀ (Saved t₀) ⟨_, x.a.nlim, stk, pb⟩).symm (hs2 v))
    have hl4 : ∀ v, ((s₀.dmem.storeInt (s₀.regs.get64 .rbx + 312052#64) 2 v).loadInt
        (s₀.regs.get64 .rbx + 311788#64) 4).isSome = true := fun v => by
      rw [hb', loadInt_sep _ _ 4 _ _ (hn4 v) (Int.toBytes_length 4 _) (by omega)]; rfl
    have e1 : (BitVec.setWidth 32 1#64).toInt = ((1 : Nat) : Int) := by decide
    have hs4 : Hide (∀ v, ((s₀.dmem.storeInt (s₀.regs.get64 .rbx + 312052#64) 2 v).storeInt
        (s₀.regs.get64 .rbx + 311788#64) 4 (BitVec.setWidth 32 1#64).toInt) =⋆
        T k x ra t₀ (Saved t₀) ⟨setW2 (setW2 x.a.ftLim 0 (u16 x.a.ftLow 0 : Int)) 1 v, 1, stk, pb⟩) := by
      intro v
      rw [hb']
      have := storeInt_sep _ 4 _ _ _ ⟨hn4 v, Int.toBytes_length 4 _⟩ (BitVec.setWidth 32 1#64).toInt
      rw [e1] at this
      exact focus (T_nl k x ra t₀ (Saved t₀) ⟨_, 1, stk, pb⟩).symm this
    clear hm hfl hs2 hn4
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals simp only [AddrIndex.offset64_none, AddrIndex.offset64_scale2, BitVec.add_zero,
      Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, hld, hl2, hl4, Option.isSome_some,
      Option.some.injEq] at *
    all_goals try subst_vars
    rw [tab_L43bd, var_L43bd]
    refine ⟨⟨hC, ⟨?_, ?_, ?_⟩, { x.a with ftLim := mk16 30 (fun q => if q = 0 then u16 x.a.ftLow 0
      else if q = 1 then u16 x.a.ftLow x.a.n0 else u16 x.a.ftLim q), nlim := 1 }, stk, pb,
      Tablelim.zero (by simp [hlb]), rfl, ⟨by simp, hL2, hL3⟩, ?_⟩, Nat.le_refl 0⟩
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hsp, hbp, h13]
    unfold Hide at hs4
    have e := fl_zero x.a.ftLim x.a.ftLow hlim x.a.n0 _ (sw16_val _ (u16_lt _ _))
    have h5 := hs4 (BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32
      (BitVec.ofInt 16 (u16 x.a.ftLow x.a.n0 : Int))))).toInt
    rw [e] at h5
    exact h5

end Kraken.Examples.Sbr.Tlim
