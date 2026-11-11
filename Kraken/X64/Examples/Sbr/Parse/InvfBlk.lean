import Kraken.X64.Examples.Sbr.Parse.InvfMem

/-!
# `read_sbr_invf`: the block obligations

The entry copies the old modes, then the five unrolled reads `L564a`..`L5751` each read two bits,
store them at `0x27 + k` and test `n_q`. Every read uses the same script (`invf_read`): the memory
facts are computed before `vcgen` from the footprint (`T_load_*`, `invf_step`), and the
`n_q` tests are decided by `nq_le` / `nq_lt`.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Invf

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm
open Kraken.Examples.Sbr.Parse (bswap32_havoc shl_cl32_havoc)
open Kraken.Examples.Sbr.HdrLib

theorem blk_entry (x : IArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb x ra t₀ "read_sbr_invf" := by
  cfg_block
  measure_hb "entry"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨rfl, hC, hm⟩, hn⟩ := hs₀
    have hlen : x.inv.length = 10 := hC.2.1
    have ld0 := T_load_inv hm 9 1 (by omega) (by omega)
    have ld1 := T_load_inv hm 4 1 (by omega) (by omega)
    have st1 := T_store_inv hm 9 1 (by omega) (by omega)
    have ld2 := fun v => T_load_inv (st1 v) 0 4 (by simp [hlen, Int.toBytes_length])
      (by simp [hlen, Int.toBytes_length])
    have ld2' := fun v => T_load_inv (st1 v) 5 4 (by simp [hlen, Int.toBytes_length])
      (by simp [hlen, Int.toBytes_length])
    have st2 := fun v => T_store_inv (st1 v) 5 4 (by simp [hlen, Int.toBytes_length])
      (by simp [hlen, Int.toBytes_length])
    have ld3 := fun v w => T_load_nq (st2 v w)
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, hinv⟩ := HdrLib.list10 _ hlen
    simp only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_zero, hinv,
      List.take, List.drop, List.cons_append, List.nil_append, Nat.reduceAdd,
      Int.toBytes_length] at ld0 ld1 st1 ld2 ld2' st2 ld3
    clear hm
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals try simp only [AddrIndex.offset64_none, BitVec.add_zero, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat] at *
    all_goals try simp only [ld0, ld1, ld2, ld2', ld3, Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals simp only [BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl, CondCode.interp,
      StatusFlags.from_result] at *
    all_goals simp only [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, Nat.reduceLeDiff,
      toBytes4_ofBytes _ (by simp : 4 ≤ [a0, a1, a2, a3].length),
      toBytes1_ofBytes _ (by simp : 1 ≤ [a4].length), List.take, List.cons_append,
      List.nil_append] at *
    · rename_i hz
      have hq : x.nq = 0 := (nq_z x.nq 0 hC.1 (by omega)).mp hz
      have := st2 (BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32
          (BitVec.ofInt 8 (Int.ofBytes [a4]))))).toInt
        (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.ofInt 32 (Int.ofBytes [a0, a1, a2, a3])))).toInt
      simp only [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, Nat.reduceLeDiff,
        toBytes4_ofBytes _ (by simp : 4 ≤ [a0, a1, a2, a3].length),
        toBytes1_ofBytes _ (by simp : 1 ≤ [a4].length), List.take, List.cons_append,
        List.nil_append] at this
      left
      refine ⟨"read_sbr_invf.L578f", rfl, by decide,
        ⟨hC, by simp, fun _ => 0, x.idx, Nat.le_refl _, hC.2.2.1, ?_⟩, Or.inr ⟨trivial, by decide⟩⟩
      rw [show invfMid x.nq x.inv (fun _ => 0) = _ by rw [hq, hinv, invfMid0]]
      exact this
    · rename_i hz
      have hq : x.nq ≠ 0 := fun h => by rw [h] at hz; simp at hz
      refine ⟨⟨hC, by simp, by omega, fun _ => 0, x.idx, Nat.le_refl _, hC.2.2.1, ?_⟩, trivial⟩
      have := st2 (BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32
          (BitVec.ofInt 8 (Int.ofBytes [a4]))))).toInt
        (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.ofInt 32 (Int.ofBytes [a0, a1, a2, a3])))).toInt
      simp only [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, Nat.reduceLeDiff,
        toBytes4_ofBytes _ (by simp : 4 ≤ [a0, a1, a2, a3].length),
        toBytes1_ofBytes _ (by simp : 1 ≤ [a4].length), List.take, List.cons_append,
        List.nil_append] at this
      rw [hinv, invfMid0]
      exact this

set_option hygiene false in
/-- Read `k`: symbolic execution up to the `n_q` test. Leaves the buffer-load check, then the
jump goal and the fall-through goal; names `hC hk hi2 hcl hRh hstep hfin hbl` in each. -/
macro "invf_read" k:term : tactic => `(tactic| (
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hR, hk, vals, i, hi1, hi2, hm⟩, hn⟩ := hs₀
    have hli := T_load_i hm
    have hlp := T_load_p8 hm
    have hlb := T_load_buf hm
    have hbl := T_buf_load hm _ 4 (rd_off i x.p8 x.L hi2 hC.2.2.2.2.1)
    have hst := T_storeI hm
    have hstep := fun i' w => invf_step hm (k := $k) (by omega) i' _ (b30_lt w)
    have hfin := fun (hq : x.nq = $k + 1) i' w => invf_step_fin hm (k := $k) (by omega) hq i' _ (b30_lt w)
    have hld0 := fun v => T_load_inv (hst v) $k 1 (by simp only [invfMid_length]; omega)
      (by simp [invfMid_length])
    have hld := fun v w => T_load_nq (T_store_inv (hst v) $k 1 (by simp only [invfMid_length]; omega)
      (by simp [invfMid_length]) w)
    have hcl := clamp i x.p8 2 hi2 hC.2.2.2.1 (by omega)
    have hRh : ∀ s : MachineData, s = s₀ → Regs t₀ s := fun _ h => h ▸ hR
    obtain ⟨hrdi, hrsi, hrdx, hrest⟩ := hR
    clear hm hst
    simp only [arg0, arg1, arg2, BitVec.add_zero, Nat.reduceAdd, BitVec.add_assoc,
      BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at hli hlp hlb hstep hfin hld0 hld
    vcgen [bswap32_havoc, shl_cl32_havoc]
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals try simp only [AddrIndex.offset64_none, AddrIndex.offset64_scale1,
      BitVec.add_zero, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, Reg64s.get64_set64,
      reduceCtorEq, ↓reduceIte, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow] at *
    all_goals try simp only [hrdi, hrsi, hrdx, hli, hlp, hlb, hld, Option.isSome_some,
      Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 32 4 rfl,
      BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, Nat.reduceLeDiff,
      CondCode.interp, StatusFlags.from_result, cf_sub, BitVec.reduceSetWidth] at *
    all_goals try simp only [hld0, Option.isSome_some]
    all_goals try simp only [decide_eq_true_eq]))

theorem blk_L564a (x : IArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb x ra t₀ "read_sbr_invf.L564a" := by
  cfg_block
  measure_hb "L564a"
    invf_read 0
    · exact hbl
    · have hq := (nq_le x.nq 1 hC.1 (by omega)).mp (by assumption)
      left
      refine ⟨"read_sbr_invf.L578f", rfl, by decide,
        ⟨hC, ?_, _, _, by omega, hcl.2, hfin (by omega) _ _⟩, Or.inr ⟨trivial, by decide⟩⟩
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      exact hRh _ rfl
    · have hf : (decide ((BitVec.ofInt 32 (x.nq : Int)).toNat < (BitVec.ofNat 32 1).toNat)
          || BitVec.ofInt 32 (x.nq : Int) - BitVec.ofNat 32 1 == BitVec.zero 32) = false := by
        assumption
      have hq : ¬ x.nq ≤ 1 := fun h => by
        rw [(nq_le x.nq 1 hC.1 (by omega)).mpr h] at hf; cases hf
      refine ⟨⟨hC, ⟨trivial, trivial, trivial, hrest⟩, by omega, _, _, by omega, hcl.2,
        hstep _ _⟩, trivial⟩

set_option hygiene false in
/-- Read `k` with the test `jb` on `c = k + 2`, after `invf_read k`. -/
macro "invf_jb" k:term "," c:term : tactic => `(tactic| (
    · exact hbl
    · have hq := (nq_lt x.nq $c hC.1 (by omega)).mp (by assumption)
      left
      refine ⟨"read_sbr_invf.L578f", rfl, by decide,
        ⟨hC, ?_, _, _, by omega, hcl.2, hfin (by omega) _ _⟩, Or.inr ⟨trivial, by decide⟩⟩
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      exact hRh _ rfl
    · have hf : decide ((BitVec.ofInt 32 (x.nq : Int)).toNat < (BitVec.ofNat 32 $c).toNat) = false :=
        by assumption
      have hq : ¬ x.nq < $c := fun h => by
        rw [(nq_lt x.nq $c hC.1 (by omega)).mpr h] at hf; cases hf
      refine ⟨⟨hC, ⟨trivial, trivial, trivial, hrest⟩, by omega, _, _, by omega, hcl.2,
        hstep _ _⟩, trivial⟩))

theorem blk_L5693 (x : IArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb x ra t₀ "read_sbr_invf.L5693" := by
  cfg_block
  measure_hb "L5693"
    invf_read 1
    invf_jb 1, 3

theorem blk_L56d5 (x : IArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb x ra t₀ "read_sbr_invf.L56d5" := by
  cfg_block
  measure_hb "L56d5"
    invf_read 2
    invf_jb 2, 4

theorem blk_L5713 (x : IArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb x ra t₀ "read_sbr_invf.L5713" := by
  cfg_block
  measure_hb "L5713"
    invf_read 3
    invf_jb 3, 5

theorem blk_L5751 (x : IArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb x ra t₀ "read_sbr_invf.L5751" := by
  cfg_block
  measure_hb "L5751"
    invf_read 4
    · exact hbl
    · have hf : (!decide ((BitVec.ofInt 32 (x.nq : Int)).toNat < (BitVec.ofNat 32 5).toNat)
          && !(BitVec.ofInt 32 (x.nq : Int) - BitVec.ofNat 32 5 == BitVec.zero 32)) = true := by
        assumption
      rw [nq_ja x.nq 5 hC.1 (by omega)] at hf; cases hf
    · have := hC.1
      refine ⟨⟨hC, ⟨trivial, trivial, trivial, hrest⟩, _, _, by omega, hcl.2,
        hfin (by omega) _ _⟩, trivial⟩

theorem blk_L578f (x : IArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb x ra t₀ "read_sbr_invf.L578f" := by
  cfg_block
  measure_hb "L578f"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨h, -⟩ := hs₀
    change Fin x ra t₀ s₀ at h
    vcgen
    subst_vars
    exact ⟨h, Nat.zero_le _⟩

omit [CodeEnv] in
theorem T_ret (x : IArgs) (ra : Int64) (t₀ : MachineData) (inv : List UInt8) (i : BitVec 32) :
    T x ra t₀ inv i = RetCell ra (t₀.regs.get64 .rsp) ⋆ (c4 (arg0 t₀ + 0x4c1e8#64) x.nq
      ⋆ (InvB (arg2 t₀) inv ⋆ (GbW (arg1 t₀) x i ⋆ (Blocks [(x.buf, x.L)]
      ⋆ (Reserve 0 (t₀.regs.get64 .rsp) ⋆ x.R))))) := by
  simp only [T, Rest]; ac_rfl

omit [CodeEnv] in
theorem Post_mem (x : IArgs) (t₀ : MachineData) (inv : List UInt8) (i : BitVec 32) :
    8 ?@ t₀.regs.get64 .rsp ⋆ (c4 (arg0 t₀ + 0x4c1e8#64) x.nq
      ⋆ (InvB (arg2 t₀) inv ⋆ (GbW (arg1 t₀) x i ⋆ (Blocks [(x.buf, x.L)]
      ⋆ (Reserve 0 (t₀.regs.get64 .rsp) ⋆ x.R)))))
    = c4 (arg0 t₀ + 0x4c1e8#64) x.nq ⋆ (InvB (arg2 t₀) inv ⋆ (GbW (arg1 t₀) x i
      ⋆ (Blocks [(x.buf, x.L)] ⋆ (8 ?@ t₀.regs.get64 .rsp ⋆ (Reserve 0 (t₀.regs.get64 .rsp)
      ⋆ x.R))))) := by
  ac_rfl

theorem blk_done (x : IArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb x ra t₀ "read_sbr_invf.done" := by
  cfg_block
  measure_hb "done"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨hdi, hsi, hdx, hsp, hbp, hsv⟩, vals, i, hi1, hi2, hm⟩, hn⟩ := hs₀
    rw [T_ret] at hm
    have l0 : s₀.dmem.loadInt (t₀.regs.get64 .rsp) 8
        = some (Int.ofBytes (Int.toBytes 8 ra.toBitVec.toInt)) :=
      loadInt_sep _ _ 8 _ _ hm (Int.toBytes_length 8 _) (by omega)
    have hpost := Block.sep_intro (Int.toBytes_length _ _) (by decide) hm
    rw [Post_mem] at hpost
    have hra : s₀.retAddr = some ra := by
      simp only [MachineData.retAddr, hsp, l0, Option.map_some,
        BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Int64.ofBitVec_toBitVec]
    clear hm l0
    vcgen
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals simp only [hra, Option.isSome_some, Option.some.injEq] at *
    subst_vars
    right
    refine ⟨rfl, vals, i, hi1, hi2, ?_, ?_, ?_, hpost⟩
    all_goals try simp only [reduceCtorEq, ↓reduceIte, hsp, hbp, hsv, and_self]
    rfl

theorem blk_L5790 (x : IArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb x ra t₀ "read_sbr_invf.L5790" := by
  cfg_block
  measure_hb "L5790"
    intro n
    exact Triple.pin fun _ h => h.1.elim

end Kraken.Examples.Sbr.Invf
