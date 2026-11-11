import Kraken.X64.Examples.Sbr.Parse.TlimMem

/-!
# `sbr_make_f_tablelim`: the prologue and the `bs_limiter_bands` dispatch
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

theorem blk_entry (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim" := by
  cfg_block
  measure_hb "entry"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨rfl, hC, stk, pb, hL, hm⟩, hn⟩ := hs₀
    rw [var_entry] at hn
    subst hn
    have hm' := focus (T_fr k x ra s₀ (BlankS (rS s₀)) _) hm
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := push5 hm' (s₀.regs.get64 .rbp) (s₀.regs.get64 .r15)
      (s₀.regs.get64 .r14) (s₀.regs.get64 .r12) (s₀.regs.get64 .rbx)
    clear hm hm'
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try simp only [BitVec.sub_sub_eight, BitVec.reduceAdd] at *
    case vc1 => exact h1
    case vc2 => exact h2
    case vc3 => exact h3
    case vc4 => exact h4
    case vc5 => exact h5
    refine ⟨?_, by rw [var_L3f22]; exact Nat.le_refl _⟩
    rw [tab_L3f22]
    refine ⟨hC, ⟨?_, ?_, ?_⟩, ?_, stk, pb, hL, fun _ h => absurd h (Nat.not_lt_zero _), ?_⟩
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, sA, arg0, rS,
      Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.setWidth_eq]
    · bv_omega
    · exact focus (T_fr k x ra _ (Saved _) (st0 x stk pb)).symm h6

theorem blk_L3f22 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L3f22" := by
  cfg_block
  measure_hb "L3f22"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hR, hdi, stk, pb, hL, hP, hm⟩, hn⟩ := hs₀
    rw [var_L3f22] at hn
    subst hn
    have hlb := RO_lb (focus (T_ro k x ra t₀ (Saved t₀) _) hm)
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals simp only [Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, hdi, hlb,
      Option.isSome_some, Option.some.injEq,
      CondCode.interp_z, StatusFlags.zf_from_result, BitVec.and_self] at *
    all_goals try subst_vars
    all_goals simp only [BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl, BitVec.ofInt_toInt] at *
    · left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, Or.inl (by rw [var_L438a]; decide)⟩
      rw [tab_L438a]
      rename_i hz
      refine ⟨hC, ⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_, stk, pb, hL, hP, hm⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hR, sA, arg0]
      simp at hz; bv_omega
    · rw [tab_L3f31, var_L3f31]
      rename_i hz
      refine ⟨⟨hC, ⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_, ?_, stk, pb, hL, hP, hm⟩, Nat.le_refl _⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hR, sA, arg0]
      all_goals simp at hz; bv_omega

theorem blk_L3f31 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L3f31" := by
  cfg_block
  measure_hb "L3f31"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hR, hax, hlb0, hP0⟩, hn⟩ := hs₀
    rw [var_L3f31] at hn
    subst hn
    have hl3 : x.lb.toNat ≤ 3 := hC.1
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    · exfalso
      rename_i hc
      rw [hax] at hc
      simp [Int64.toBitVec_ofNat_norm] at hc
      bv_omega
    · rw [tab_L3f3a, var_L3f3a]
      exact ⟨⟨hC, hR, hax, hlb0, hP0⟩, Nat.le_refl _⟩

end Kraken.Examples.Sbr.Tlim
