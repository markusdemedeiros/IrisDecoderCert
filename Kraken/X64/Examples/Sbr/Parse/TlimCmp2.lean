import Kraken.X64.Examples.Sbr.Parse.TlimCmp

/-!
# `sbr_make_f_tablelim`: the compaction loop, branch blocks (`L4312` … `L4342`)

The branch conditions select among the `Compact` steps; the model allows each step on every
branch, so only the step taken is recorded (`drop` on the way to `L4370`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Tlim

variable [CodeEnv]

theorem blk_L4312 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L4312" := by
  cfg_block
  measure_hb "L4312"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨⟨hsp, hbp, h13⟩, hbx⟩, h14, hNN, hlb, sa, fl, stk, pb, i, o, L, hL, hP,
      ⟨hS, hL1, hoL, hi, hcx, hax, hCm⟩, ⟨hol, hdx, hsi, hdi⟩, hm⟩, hn⟩ := hs₀
    rw [var_L4312] at hn
    subst hn
    subst hi
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    · left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, Or.inl ?_⟩
      · rw [tab_L4370]
        refine ⟨hC, ⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_, hNN, hlb, sa, fl, stk, pb, _, o, L, hL, hP,
          ⟨hS, hL1, hoL, rfl, ?_, ?_, fun r R h => hCm r R (Compact.drop hol h)⟩, hol, ?_, hmT⟩
        all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hsp, hbp, h13, hbx,
          h14, hcx, hax, hdx]
      · rw [var_L4370]
        simp only [mu, rN, ld4, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        omega
    · rw [tab_L4317, var_L4317]
      refine ⟨⟨hC, ⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_, hNN, hlb, sa, fl, stk, pb, _, o, L, hL, hP,
        ⟨hS, hL1, hoL, rfl, ?_, ?_, hCm⟩, ⟨hol, ?_, ?_⟩, hmT⟩, ?var⟩
      case var =>
        simp only [mu, rN, ld4, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        omega
      all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hsp, hbp, h13, hbx,
        h14, hcx, hax, hdx, hsi]

theorem blk_L4317 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L4317" := by
  cfg_block
  measure_hb "L4317"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨⟨hsp, hbp, h13⟩, hbx⟩, h14, hNN, hlb, sa, fl, stk, pb, i, o, L, hL, hP,
      ⟨hS, hL1, hoL, hi, hcx, hax, hCm⟩, ⟨hol, hdx, hsi⟩, hm⟩, hn⟩ := hs₀
    rw [var_L4317] at hn
    subst hn
    subst hi
    have hC' := hC
    obtain ⟨-, hn0, hnp6, -⟩ := hC'
    have hl1 := RO_np (focus (T_ro k x ra t₀ (Saved t₀) _) hm)
    rw [show sA t₀ = s₀.regs.get64 .rbx from hbx.symm] at hl1
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals simp only [Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, hl1,
      Option.isSome_some, Option.some.injEq, AddrIndex.offset64_none, BitVec.add_zero] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl, BitVec.ofInt_natCast,
      zx_small _ (show x.a.npatch < 2 ^ 31 by omega)] at *
    · left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, Or.inl ?_⟩
      · rw [tab_L4370]
        refine ⟨hC, ⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_, hNN, hlb, sa, fl, stk, pb, _, o, L, hL, hP,
          ⟨hS, hL1, hoL, rfl, ?_, ?_, fun r R h => hCm r R (Compact.drop hol h)⟩, hol, ?_, hmT⟩
        all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hsp, hbp, h13, hbx,
          h14, hcx, hax, hdx]
      · rw [var_L4370]
        simp only [mu, rN, ld4, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        omega
    · rw [tab_L4323, var_L4323]
      refine ⟨⟨hC, ⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_, hNN, hlb, sa, fl, stk, pb, _, o, L, hL, hP,
        ⟨hS, hL1, hoL, rfl, ?_, ?_, hCm⟩, ⟨hol, ?_, ?_, ?_⟩, hmT⟩, ?var⟩
      case var =>
        simp only [mu, rN, ld4, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        omega
      all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hsp, hbp, h13, hbx,
        h14, hcx, hax, hdx, hsi]

omit [CodeEnv] in
theorem inc64 (n : Nat) (h : n < 2 ^ 31) :
    BitVec.ofNat 64 n + 1 = BitVec.ofNat 64 (n + 1) := by
  rw [BitVec.ofNat_add]; rfl

theorem blk_L4323 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L4323" := by
  cfg_block
  measure_hb "L4323"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨⟨hsp, hbp, h13⟩, hbx⟩, h14, hNN, hlb, sa, fl, stk, pb, i, o, L, hL, hP,
      ⟨hS, hL1, hoL, hi, hcx, hax, hCm⟩, ⟨hol, hdx, hsi, h8⟩, hm⟩, hn⟩ := hs₀
    rw [var_L4323] at hn
    subst hn
    subst hi
    have hC' := hC
    obtain ⟨-, hn0, hnp6, -⟩ := hC'
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    rw [tab_L4330, var_L4330]
    refine ⟨⟨hC, ⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_, hNN, hlb, sa, fl, stk, pb, _, o, L, hL, hP,
      ⟨hS, hL1, hoL, rfl, ?_, ?_, hCm⟩, ⟨hol, ?_, ?_, ?_, 0, by omega, ?_⟩, hmT⟩, ?var⟩
    case var =>
      simp only [mu, rN, ld4, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, h8,
        inc64 _ (show x.a.npatch < 2 ^ 31 by omega)]
      try simp
      omega
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hsp, hbp, h13, hbx,
      h14, hcx, hax, hdx, hsi, h8, inc64 _ (show x.a.npatch < 2 ^ 31 by omega)]
    all_goals try (simp; done)

theorem blk_L4340 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L4340" := by
  cfg_block
  measure_hb "L4340"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨⟨hsp, hbp, h13⟩, hbx⟩, h14, hNN, hlb, sa, fl, stk, pb, i, o, L, hL, hP,
      ⟨hS, hL1, hoL, hi, hcx, hax, hCm⟩, ⟨hol, hdx⟩, hm⟩, hn⟩ := hs₀
    rw [var_L4340] at hn
    subst hn
    subst hi
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try (left; apply Table.ofLabels_at)
    all_goals try refine ⟨by decide, ?_, Or.inl ?_⟩
    · rw [tab_L4370]
      refine ⟨hC, ⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_, hNN, hlb, sa, fl, stk, pb, _, o, L, hL, hP,
        ⟨hS, hL1, hoL, rfl, ?_, ?_, fun r R h => hCm r R (Compact.drop hol h)⟩, hol, ?_, hmT⟩
      all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hsp, hbp, h13, hbx,
        h14, hcx, hax, hdx]
    · rw [var_L4370]
      simp only [mu, rN, ld4, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      omega

theorem blk_L4342 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L4342" := by
  cfg_block
  measure_hb "L4342"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨⟨hsp, hbp, h13⟩, hbx⟩, h14, hNN, hlb, sa, fl, stk, pb, i, o, L, hL, hP,
      ⟨hS, hL1, hoL, hi, hcx, hax, hCm⟩, ⟨hol, hsi, h8⟩, hm⟩, hn⟩ := hs₀
    rw [var_L4342] at hn
    subst hn
    subst hi
    have hC' := hC
    obtain ⟨-, hn0, hnp6, -⟩ := hC'
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    rw [tab_L4350, var_L4350]
    refine ⟨⟨hC, ⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_, hNN, hlb, sa, fl, stk, pb, _, o, L, hL, hP,
      ⟨hS, hL1, hoL, rfl, ?_, ?_, hCm⟩, ⟨hol, ?_, ?_, 0, by omega, ?_⟩, hmT⟩, ?var⟩
    case var =>
      simp only [mu, rN, ld4, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, h8]
      try simp
      omega
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hsp, hbp, h13, hbx,
      h14, hcx, hax, hsi, h8]
    all_goals try (simp; done)

omit [CodeEnv] in
theorem pbA (r : BitVec 64) (j : Nat) (h : j < 8) :
    r - 8#64 + BitVec.ofNat 64 j * 2#64 + 18446744073709551570#64
      = r - 0x36#64 + BitVec.ofNat 64 (2 * j) := by
  bv_omega

theorem blk_L4330 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L4330" := by
  cfg_block
  measure_hb "L4330"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨⟨hsp, hbp, h13⟩, hbx⟩, h14, hNN, hlb, sa, fl, stk, pb, i, o, L, hL, hP,
      ⟨hS, hL1, hoL, hi, hcx, hax, hCm⟩, ⟨hol, hdx, hsi, h8, j, hj, h9⟩, hm⟩, hn⟩ := hs₀
    rw [var_L4330] at hn
    subst hn
    subst hi
    have hC' := hC
    obtain ⟨-, hn0, hnp6, -⟩ := hC'
    have hpb : pb.length = 14 := hL.2.2
    have hl := ld16 (focus (T_pb k x ra t₀ (Saved t₀) _) hm) j
      (addr := s₀.regs.get64 .rbp + s₀.regs.get64 .r9 * 2#64 + 18446744073709551570#64)
      (by rw [hbp, h9, pbA _ _ (by omega)]) (by simp only; omega) (by simp only; omega)
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals simp only [AddrIndex.offset64_scale2, AddrIndex.offset64_none, BitVec.add_zero,
      Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.ofNat_eq_ofNat, hl,
      Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    · left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, Or.inl ?_⟩
      · rw [tab_L4342]
        refine ⟨hC, ⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_, hNN, hlb, sa, fl, stk, pb, _, o, L, hL, hP,
          ⟨hS, hL1, hoL, rfl, ?_, ?_, hCm⟩, ⟨hol, ?_, ?_⟩, hmT⟩
        all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hsp, hbp, h13, hbx,
          h14, hcx, hax, hsi, h8]
      · rw [var_L4342]
        simp only [mu, rN, ld4, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, h8, h9,
          BitVec.toNat_ofNat]
        omega
    · rw [tab_L4338, var_L4338]
      refine ⟨⟨hC, ⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_, hNN, hlb, sa, fl, stk, pb, _, o, L, hL, hP,
        ⟨hS, hL1, hoL, rfl, ?_, ?_, hCm⟩, ⟨hol, ?_, ?_, ?_, j, hj, ?_⟩, hmT⟩, ?var⟩
      case var =>
        simp only [mu, rN, ld4, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, h8, h9,
          BitVec.toNat_ofNat]
        omega
      all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hsp, hbp, h13, hbx,
        h14, hcx, hax, hdx, hsi, h8, h9]

omit [CodeEnv] in
theorem zne64 (a b : Nat) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b == BitVec.zero 64) = decide (a = b) := by
  by_cases h : a = b
  · subst h; simp
  · have : BitVec.ofNat 64 a - BitVec.ofNat 64 b ≠ BitVec.zero 64 := by
      intro e; apply h; have := congrArg BitVec.toNat e; simp at this; omega
    simp only [beq_eq_false_iff_ne.mpr this, h, decide_false]

theorem blk_L4338 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L4338" := by
  cfg_block
  measure_hb "L4338"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨⟨hsp, hbp, h13⟩, hbx⟩, h14, hNN, hlb, sa, fl, stk, pb, i, o, L, hL, hP,
      ⟨hS, hL1, hoL, hi, hcx, hax, hCm⟩, ⟨hol, hdx, hsi, h8, j, hj, h9⟩, hm⟩, hn⟩ := hs₀
    rw [var_L4338] at hn
    subst hn
    subst hi
    have hC' := hC
    obtain ⟨-, hn0, hnp6, -⟩ := hC'
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try call_simp
    all_goals rename_i hs hc
    all_goals subst hs
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, h8, h9,
      inc64 _ (show j < 2 ^ 31 by omega)] at hc
    all_goals try simp only [CondCode.interp_nz, CondCode.interp_z, StatusFlags.zf_from_result,
      zne64 _ _ (show x.a.npatch + 1 < 2 ^ 32 by omega) (show j + 1 < 2 ^ 32 by omega)] at hc
    · left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, Or.inl ?_⟩
      · rw [tab_L4330]
        refine ⟨hC, ⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_, hNN, hlb, sa, fl, stk, pb, _, o, L, hL, hP,
          ⟨hS, hL1, hoL, rfl, ?_, ?_, hCm⟩, ⟨hol, ?_, ?_, ?_, j + 1, by simp at hc; omega, ?_⟩, hmT⟩
        all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hsp, hbp, h13, hbx,
          h14, hcx, hax, hdx, hsi, h8, h9, inc64 _ (show j < 2 ^ 31 by omega)]
      · rw [var_L4330]
        simp only [mu, rN, ld4, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, h8, h9,
          inc64 _ (show j < 2 ^ 31 by omega), BitVec.toNat_ofNat]
        omega
    · rw [tab_L4340, var_L4340]
      refine ⟨⟨hC, ⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_, hNN, hlb, sa, fl, stk, pb, _, o, L, hL, hP,
        ⟨hS, hL1, hoL, rfl, ?_, ?_, hCm⟩, ⟨hol, ?_⟩, hmT⟩, ?var⟩
      case var =>
        simp only [mu, rN, ld4, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        omega
      all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hsp, hbp, h13, hbx,
        h14, hcx, hax, hdx]

theorem blk_L4350 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L4350" := by
  cfg_block
  measure_hb "L4350"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨⟨hsp, hbp, h13⟩, hbx⟩, h14, hNN, hlb, sa, fl, stk, pb, i, o, L, hL, hP,
      ⟨hS, hL1, hoL, hi, hcx, hax, hCm⟩, ⟨hol, hsi, h8, j, hj, h9⟩, hm⟩, hn⟩ := hs₀
    rw [var_L4350] at hn
    subst hn
    subst hi
    have hC' := hC
    obtain ⟨-, hn0, hnp6, -⟩ := hC'
    have hpb : pb.length = 14 := hL.2.2
    have hl := ld16 (focus (T_pb k x ra t₀ (Saved t₀) _) hm) j
      (addr := s₀.regs.get64 .rbp + s₀.regs.get64 .rdx * 2#64 + 18446744073709551570#64)
      (by rw [hbp, h9, pbA _ _ (by omega)]) (by simp only; omega) (by simp only; omega)
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals simp only [AddrIndex.offset64_scale2, AddrIndex.offset64_none, BitVec.add_zero,
      Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.ofNat_eq_ofNat, hl,
      Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    · left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, Or.inl ?_⟩
      · rw [tab_L42d0]
        refine ⟨hC, ⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_, hNN, hlb, sa, fl, stk, pb, _, o, L, hL, hP,
          ⟨hS, hL1, hoL, rfl, ?_, ?_, hCm⟩, ⟨hol, ?_⟩, hmT⟩
        all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hsp, hbp, h13, hbx,
          h14, hcx, hax, hsi, h8]
      · rw [var_L42d0]
        simp only [mu, rN, ld4, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, h8, h9,
          BitVec.toNat_ofNat]
        omega
    · rw [tab_L435b, var_L435b]
      refine ⟨⟨hC, ⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_, hNN, hlb, sa, fl, stk, pb, _, o, L, hL, hP,
        ⟨hS, hL1, hoL, rfl, ?_, ?_, hCm⟩, ⟨hol, ?_, ?_, j, hj, ?_⟩, hmT⟩, ?var⟩
      case var =>
        simp only [mu, rN, ld4, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, h8, h9,
          BitVec.toNat_ofNat]
        omega
      all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hsp, hbp, h13, hbx,
        h14, hcx, hax, hsi, h8, h9]

theorem blk_L435b (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L435b" := by
  cfg_block
  measure_hb "L435b"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨⟨hsp, hbp, h13⟩, hbx⟩, h14, hNN, hlb, sa, fl, stk, pb, i, o, L, hL, hP,
      ⟨hS, hL1, hoL, hi, hcx, hax, hCm⟩, ⟨hol, hsi, h8, j, hj, h9⟩, hm⟩, hn⟩ := hs₀
    rw [var_L435b] at hn
    subst hn
    subst hi
    have hC' := hC
    obtain ⟨-, hn0, hnp6, -⟩ := hC'
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try call_simp
    all_goals rename_i hs hc
    all_goals subst hs
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, h8, h9,
      inc64 _ (show j < 2 ^ 31 by omega)] at hc
    all_goals try simp only [CondCode.interp_nz, CondCode.interp_z, StatusFlags.zf_from_result,
      zne64 _ _ (show x.a.npatch + 1 < 2 ^ 32 by omega) (show j + 1 < 2 ^ 32 by omega)] at hc
    · left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, Or.inl ?_⟩
      · rw [tab_L4350]
        refine ⟨hC, ⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_, hNN, hlb, sa, fl, stk, pb, _, o, L, hL, hP,
          ⟨hS, hL1, hoL, rfl, ?_, ?_, hCm⟩, ⟨hol, ?_, ?_, j + 1, by simp at hc; omega, ?_⟩, hmT⟩
        all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hsp, hbp, h13, hbx,
          h14, hcx, hax, hsi, h8, h9, inc64 _ (show j < 2 ^ 31 by omega)]
      · rw [var_L4350]
        simp only [mu, rN, ld4, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, h8, h9,
          inc64 _ (show j < 2 ^ 31 by omega), BitVec.toNat_ofNat]
        omega
    · rw [tab_L4363, var_L4363]
      refine ⟨⟨hC, ⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_, hNN, hlb, sa, fl, stk, pb, _, o, L, hL, hP,
        ⟨hS, hL1, hoL, rfl, ?_, ?_, hCm⟩, ⟨hol, ?_⟩, hmT⟩, ?var⟩
      case var =>
        simp only [mu, rN, ld4, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        omega
      all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hsp, hbp, h13, hbx,
        h14, hcx, hax, hsi]

end Kraken.Examples.Sbr.Tlim
