import Kraken.X64.Examples.Sbr.Parse.ResetA1Mem
import Kraken.X64.Examples.Sbr.Parse.ResetModel

/-!
# `sbr_reset`: `k[2]` (shard A1)

`L150a`: `bs_stop_freq ≥ 14` (`k[2] = 2 k[0]`, `3 k[0]`, or the failure); `L1618`, `L161f`: the
other two sources of `k[2]`; `L1622`: the clamp `k[2] = min(k[2], 64)` and the
`max_qmf_subbands` choice; `L1655`, `L1661`: the checks.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Reset

variable [CodeEnv]

/-- After `k[0]`, a rejection is a `Reset` result (`Master.fail`). -/
theorem a1_K0S_fail {k : Nat} {e : REnv} {a : RArgs} {ra : Int64} {t₀ s : MachineData}
    {P : Nat → St → List UInt8 → Prop} (h : K0S k e a ra t₀ s P) : AtFail k e a ra t₀ s := by
  obtain ⟨row, hr, ⟨hC, -, hb, st, fr, hx, hsp, hfm, hF, -, hm⟩, h12, h15⟩ := h
  exact ⟨hC, hb, h12, h15, st, fr, by rw [hx]; exact Reset.badMaster hC.2.1 (Master.fail hr),
    hsp, hfm, hF, hm⟩

/-- `cmp $0x40, %edx; mov $0x40, %esi; cmovb %edx, %esi`. -/
def a1min (D : BitVec 32) : BitVec 32 := if D.toNat < 64 then D else 64#32

theorem a1_min_eq (D : BitVec 32) : (if D.toNat < 64 then D else 64#32) = a1min D := rfl

theorem a1min_le (D : BitVec 32) : (a1min D).toNat ≤ 64 := by
  unfold a1min; split
  · omega
  · decide

/-- `bs_stop_freq ≥ 14`: `15` → `L161f`, `14` → `k[2] = 2 k[0]`, else the failure. -/
theorem blk_L150a (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L150a" ⟨"sbr_reset.L150a", B.L150a, some "sbr_reset.L1523"⟩ := by
  info_off
  measure_hb "L150a"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, hr, ⟨hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF, ⟨-, -, hdx⟩, hm⟩, h12, h15⟩ :=
      T.L150a.mp hs
    clear hs
    simp only [B.L150a]
    vcgen
    all_goals try subst_vars
    all_goals first
      | (refine Or.inl (Table.ofLabels_at ⟨S.L161f, T.L161f.mpr ⟨row, hr, ⟨hC, hBO, ⟨?_, ?_⟩, st,
          fr, hx, hsp, hfm, hF, ?_, hm⟩, ?_, ?_⟩, by edge_step⟩)
         all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hrsp, hrbp,
          hdx])
      | (refine Or.inl (Table.ofLabels_at ⟨S.L1762, T.L1762.mpr (a1_K0S_fail (P := fun _ _ _ => True)
          ⟨row, hr, ⟨hC, hBO, ⟨?_, ?_⟩, st, fr, hx, hsp, hfm, hF, trivial, hm⟩, ?_, ?_⟩), by edge_step⟩)
         all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hrsp, hrbp])
      | (refine Or.inl (Table.ofLabels_at ⟨S.L1622, T.L1622.mpr ⟨row, hr, ⟨hC, hBO, ⟨?_, ?_⟩, st,
          fr, hx, hsp, hfm, hF, trivial, hm⟩, ?_, ?_⟩, by edge_step⟩)
         all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hrsp, hrbp])

/-- `bs_stop_freq = 0`: `k[2] = stop_min` (already stored). -/
theorem blk_L1618 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1618" ⟨"sbr_reset.L1618", B.L1618, some "sbr_reset.L161f"⟩ := by
  info_off
  measure_hb "L1618"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, hr, ⟨hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF, -, hm⟩, h12, h15⟩ :=
      T.L1618.mp hs
    clear hs
    have ld := a1_k2_isSome hm
    simp only [B.L1618]
    vcgen
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12,
      AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    · exact ld
    · refine Or.inl (Table.ofLabels_at ⟨S.L1622, T.L1622.mpr ⟨row, hr, ⟨hC, hBO, ⟨?_, ?_⟩, st,
        fr, hx, hsp, hfm, hF, trivial, hm⟩, ?_, ?_⟩, by edge_step⟩)
      all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hrsp, hrbp]

/-- `bs_stop_freq = 15`: `k[2] = 3 k[0]`. -/
theorem blk_L161f (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L161f" ⟨"sbr_reset.L161f", B.L161f, some "sbr_reset.L1622"⟩ := by
  info_off
  measure_hb "L161f"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, hr, ⟨hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF, -, hm⟩, h12, h15⟩ :=
      T.L161f.mp hs
    clear hs
    simp only [B.L161f]
    vcgen
    all_goals try subst_vars
    refine ⟨T.L1622.mpr ⟨row, hr, ⟨hC, hBO, ⟨?_, ?_⟩, st, fr, hx, hsp, hfm, hF, trivial, hm⟩,
      ?_, ?_⟩, by var_step⟩
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hrsp, hrbp]

/-- The simp set of `L1622`. -/
local macro "k2s" : tactic => `(tactic| simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
  AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
  BitVec.reduceSetWidth, cc_c_sub, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
  decide_eq_true_eq, a1_min_eq, sw32_64])

/-- `k[2] = min(k[2], 64)` stored; `max_qmf_subbands` by the rate. -/
theorem blk_L1622 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1622" ⟨"sbr_reset.L1622", B.L1622, some "sbr_reset.L1655"⟩ := by
  info_off
  measure_hb "L1622"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, hr, ⟨hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF, -, hm⟩, h12, h15⟩ :=
      T.L1622.mp hs
    clear hs
    have ld := a1_k2_isSome hm
    have hst := fun v => a1_k2_store hm v
    have ldsr := fun v => cell4_load (focus (Mm_sr ..) (a1_k2_store hm v))
    simp only [B.L1622]
    obtain ⟨D, hD⟩ : ∃ D, (s₀.regs.get64 .rdx).setWidth 32 = D := ⟨_, rfl⟩
    vcgen
    all_goals try subst s₀
    all_goals try subst n
    all_goals try k2s
    all_goals try simp only [h12, hD]
    · exact ld
    · simp only [ldsr, Option.isSome_some]
    · rename_i v hv hc
      revert hv hc; k2s; (try simp only [h12, hD]); intro hv hc
      rw [ldsr] at hv; obtain rfl := Option.some.inj hv
      simp only [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt_toInt, hx,
        CondCode.interp_l_cmp_toInt32, BitVec.reduceToInt, decide_eq_true_eq] at hc
      refine Or.inl (Table.ofLabels_at ⟨S.L1661, T.L1661.mpr ⟨⟨row, (a1min D).toNat, hr,
        a1min_le D, ⟨hC, hBO, ⟨?_, ?_⟩, { st with k2 := a1min D }, fr, hx, hsp, hfm, hF, ?_,
        hst (a1min D)⟩, ?_, ?_, ?_⟩, ?_⟩, by edge_step⟩)
      all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hrsp, hrbp,
        BitVec.ofNat_toNat, BitVec.setWidth_eq]
      simp only [maxQ, srI, show a.x.sampleRate.toInt ≤ 32000 by omega, ↓reduceIte]; rfl
    · rename_i v hv hc1 hc2
      revert hv hc1 hc2; k2s; (try simp only [h12, hD]); intro hv hc1 hc2
      rw [ldsr] at hv; obtain rfl := Option.some.inj hv
      simp only [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt_toInt, hx,
        CondCode.interp_l_cmp_toInt32, BitVec.reduceToInt, decide_eq_true_eq, cc_z_sub,
        decide_eq_false_iff_not, Int.not_lt] at hc1 hc2
      have h44 : a.x.sampleRate.toInt = 44100 := by rw [hc2]; rfl
      refine Or.inl (Table.ofLabels_at ⟨S.L1661, T.L1661.mpr ⟨⟨row, (a1min D).toNat, hr,
        a1min_le D, ⟨hC, hBO, ⟨?_, ?_⟩, { st with k2 := a1min D }, fr, hx, hsp, hfm, hF, ?_,
        hst (a1min D)⟩, ?_, ?_, ?_⟩, ?_⟩, by edge_step⟩)
      all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hrsp, hrbp,
        BitVec.ofNat_toNat, BitVec.setWidth_eq]
      all_goals try rfl
      simp only [maxQ, srI, h44]; rfl
    · rename_i v hv hc1 hc2
      revert hv hc1 hc2; k2s; (try simp only [h12, hD]); intro hv hc1 hc2
      rw [ldsr] at hv; obtain rfl := Option.some.inj hv
      simp only [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt_toInt, hx,
        CondCode.interp_l_cmp_toInt32, BitVec.reduceToInt, decide_eq_true_eq, cc_z_sub,
        decide_eq_false_iff_not, Int.not_lt] at hc1 hc2
      have h44 : a.x.sampleRate.toInt ≠ 44100 := fun h => hc2 (by
        apply BitVec.eq_of_toInt_eq; rw [h]; rfl)
      refine ⟨T.L1655.mpr ⟨⟨row, (a1min D).toNat, hr,
        a1min_le D, ⟨hC, hBO, ⟨?_, ?_⟩, { st with k2 := a1min D }, fr, hx, hsp, hfm, hF, ?_,
        hst (a1min D)⟩, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩, by var_step⟩
      all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hrsp, hrbp,
        BitVec.ofNat_toNat, BitVec.setWidth_eq, srI, hx]
      all_goals try rfl
      all_goals first | exact hc1 | exact h44 | simp only [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt_toInt]

/-- `sr ≤ 47999` (after `sr > 32000`, `sr ≠ 44100`) is no supported rate: the abort `L328e` is
unreachable. -/
theorem blk_L1655 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1655" ⟨"sbr_reset.L1655", B.L1655, some "sbr_reset.L1661"⟩ := by
  info_off
  measure_hb "L1655"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨⟨row, k2, hr, hk2, hA, h12, h15, hsi⟩, hcx, hax, hlo, hne⟩ := T.L1655.mp hs
    clear hs
    have hm := rateRow_mem hr
    have hsr := a1_sr_toInt hm
    simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at hm
    simp only [srI] at hlo hne hm hsr
    have key : 48000 ≤ a.x.sampleRate.toNat := by
      rcases hm with h|h|h|h|h|h|h|h|h|h|h|h <;> omega
    have hgt : ¬ a.x.sampleRate.toInt ≤ 32000 := by omega
    clear hm hsr
    simp only [B.L1655]
    vcgen
    all_goals try subst_vars
    all_goals try simp only [hcx] at *
    all_goals try disp_simp
    · exfalso; rename_i hc
      simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hc
      omega
    · refine ⟨T.L1661.mpr ⟨⟨row, k2, hr, hk2,
        A1S.congr (by simp) (by simp) rfl (fun _ _ x => x) hA, ?_, ?_, ?_⟩, ?_⟩, by var_step⟩
      all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hsi, hax]
      simp only [maxQ, srI, hne, ↓reduceIte]
      simp only [show ¬ a.x.sampleRate.toInt ≤ 32000 by omega, ↓reduceIte]; rfl

omit [CodeEnv] in
/-- The unsigned check `k[2] - k[0] ≤ max_qmf_subbands` (`k[0] ≤ 32`, `k[2] ≤ 64`). -/
theorem a1_sub_cmp {k2 K q : Nat} (hk2 : k2 ≤ 64) (hK : K ≤ 32) (hq : q ≤ 48) :
    (BitVec.ofNat 32 k2 - BitVec.ofNat 32 K).toNat ≤ q ↔ (K ≤ k2 ∧ k2 - K ≤ q) := by
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

omit [CodeEnv] in
theorem a1_sub_val {k2 K : Nat} (hk2 : k2 ≤ 64) (h : K ≤ k2) :
    (BitVec.ofNat 32 k2 - BitVec.ofNat 32 K).setWidth 64 = BitVec.ofNat 64 (k2 - K) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

/-- `k[2] - k[0] ≤ max_qmf_subbands` (unsigned): `L1684` (`AtMaster`), else the failure log. -/
theorem blk_L1661 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1661" ⟨"sbr_reset.L1661", B.L1661, some "sbr_reset.L167a"⟩ := by
  info_off
  measure_hb "L1661"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨⟨row, k2, hr, hk2, ⟨hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF, hk2s, hm⟩, h12, h15,
      hsi⟩, hax⟩ := T.L1661.mp hs
    clear hs
    have ld1 := a1_k0_load hm
    have ld2 := avctx_load hm
    have hr0 := k0Of_range hr (st := u8 a.sp 0) hC.2.1
    have hq : maxQ (srI a) = 48 ∨ maxQ (srI a) = 35 ∨ maxQ (srI a) = 32 := by
      unfold maxQ; split
      · exact Or.inl rfl
      · split
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
    have hk0 : st.x.k0 = k0N a row := by rw [hx]
    have hsl : slice (Int.toBytes 4 (st.x.k0 : Int)) 0 4 = Int.toBytes 4 (st.x.k0 : Int) := by
      simp only [slice, List.drop_zero]
      exact List.take_of_length_le (by rw [Int.toBytes_length]; exact Nat.le_refl _)
    rw [hsl, hk0] at ld1
    simp only [arg0, arg1] at ld1 ld2
    rw [show st.x.avctx = a.x.avctx by rw [hx]] at ld2
    simp only [srI] at hq hax hr0
    simp only [B.L1661]
    vcgen
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15,
      AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    · simp only [ld1, Option.isSome_some]
    · rename_i v hv hc
      simp only [h12, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, ld1] at hv
      obtain rfl := Option.some.inj hv
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, cc_be_sub, hsi, hax,
        BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt_natCast, a1_sw_ofNat64, BitVec.toNat_sub,
        BitVec.toNat_ofNat, decide_eq_true_eq] at hc
      obtain ⟨hK1, hK2⟩ := hr0
      have f1 : k0N a row ≤ k2 ∧ (k2 : Int) - k0A a row ≤ maxQ (srI a) := by
        simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat] at hc
        simp only [k0N, k0A, srI, u8]
        rcases hq with h|h|h <;> rw [h] at hc ⊢ <;> simp only [Int.reduceToNat] at hc <;> omega
      refine Or.inl (Table.ofLabels_at ⟨S.L1684, T.L1684.mpr ⟨row, k2, hr, hk2, f1.1, f1.2,
        ⟨hC, hBO, ⟨?_, ?_⟩, st, fr, hx, hsp, hfm, hF, hk2s, hm⟩, ?_, ?_, ?_, ?_, ?_⟩, by edge_step⟩)
      all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hrsp, hrbp, hsi]
      all_goals try rfl
      all_goals have e1 : k0N a row = (k0Of a.x.sampleRate.toInt row (a.sp.getD 0 0).toNat).toNat := rfl
      all_goals have f2 := f1.1
      all_goals apply BitVec.eq_of_toNat_eq
      all_goals simp only [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt_natCast,
        BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
      all_goals omega
    · simp only [ld2, Option.isSome_some]
    · rename_i v hv hc v2 hv2
      simp only [h12, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, ld1] at hv
      obtain rfl := Option.some.inj hv
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h15, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, AddrIndex.offset64_none, BitVec.add_zero, ld2] at hv2
      obtain rfl := Option.some.inj hv2
      refine ⟨T.L167a.mpr ⟨a1_K0S_fail (P := fun _ st _ => st.k2 = BitVec.ofNat 32 k2)
        ⟨row, hr, ⟨hC, hBO, ⟨?_, ?_⟩, st, fr, hx, hsp, hfm, hF, hk2s, hm⟩, ?_, ?_⟩, ?_⟩, by var_step⟩
      all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hrsp, hrbp,
        BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]

end Kraken.Examples.Sbr.Reset
