import Kraken.X64.Examples.Sbr.Parse.PsBlkHNAvx

/-!
# `ff_ps_read_data`: the class-0 fixed borders (`0x22d`–`0x714`)
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Ps

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

set_option maxRecDepth 20000 in
/-- Class 0: `cl = log2 num_env` from `ff_log2_tab`; `num_env < 4` takes the scalar loop. -/
theorem blk_L22d (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L22d" := by
  cfg_block
  measure_hb "L22d"
    intro n
    simp only [tab_L22d, var_L22d, tab_L259, var_L259]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, v, hB, hv1, hv3⟩, hn⟩ := hs₀
    have hB' := hB
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, hf, hP, hbl, h08, hid⟩, hm⟩, ⟨h13, h12⟩, hbx, hKp⟩, hH, h38, hv4, hne,
      h58, h10, hb0, hix⟩ := hB'
    have e1 : s₀.regs.get64 .rbp + Int64.toBitVec (-72)
        = t₀.regs.get64 .rsp - 0xa8#64 + BitVec.ofNat 64 0x58 := by
      rw [hbp]; exact fr_addr _ 72 (by omega) (by omega)
    have hL := Fr_f_load hm hf 0x58 8 (by omega)
    rw [← e1, h58] at hL
    have hG := Fr_log2got hm
    have hT := Fr_log2 hm v (by omega)
    have z0 : ∀ a : BitVec 64, a + 0 = a := fun a => by simp
    vcgen [hn_mov_load_rip_spec]
    all_goals try call_simp
    case vc1 =>
      rename_i s hs
      subst hs
      simp only [AddrIndex.offset64_none, z0]
      rw [hL]; rfl
    case vc2 =>
      rename_i s hs xv hxv hj
      subst hs
      simp only [AddrIndex.offset64_none, z0, hL, Option.some.injEq] at hxv
      subst hxv
      simp only [AddrIndex.offset64_none, z0] at hj
      rw [hn_c32] at hj
      exact absurd (of_decide_eq_true hj) (hn_trap v hv1 hv4)
    case vc3 =>
      rename_i s hs xv hxv hj
      subst hs
      rw [hG]; rfl
    case vc4 =>
      rename_i s hs xv hxv xg hxg hj
      subst hs
      simp only [AddrIndex.offset64_none, z0, hL, Option.some.injEq] at hxv
      subst hxv
      rw [hG, Option.some.injEq] at hxg
      subst hxg
      simp only [AddrIndex.offset64_scale1, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
        BitVec.ofInt_ofBytes_toBytes 64 8 rfl, hn_eax_v v (by omega)]
      rw [hn_i64z, BitVec.add_zero, hT]; rfl
    case vc5 =>
      rename_i s hs xv hxv xg hxg htr xb hxb hj2
      subst hs
      simp only [AddrIndex.offset64_none, z0, hL, Option.some.injEq] at hxv
      subst hxv
      rw [hG, Option.some.injEq] at hxg
      subst hxg
      simp only [AddrIndex.offset64_scale1, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
        BitVec.ofInt_ofBytes_toBytes 64 8 rfl, hn_eax_v v (by omega)] at hxb
      rw [hn_i64z, BitVec.add_zero, hT, Option.some.injEq] at hxb
      subst hxb
      rw [hn_c8] at hj2
      have hlt := of_decide_eq_true hj2
      rw [hn_r10_4 _ (by omega), h10] at hlt
      have hv12 : v = 1 ∨ v = 2 := by omega
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.L6f5") ⟨rfl, ?_, Or.inl ?_⟩
      · refine (tab_L6f5 _ _ _ _ _ _).mpr ?_
        refine ⟨c, f, v, hn_BS_mv hB ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl, hv12, ?_, ?_⟩
        all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
        all_goals try rfl
        all_goals try exact hix
        all_goals first | exact hn_one32 | exact hn_lg v hv12
      · rw [var_L6f5]; subst hn; exact Kraken.lex_cons_lt_of_lt rfl (by decide)
    case vc6 =>
      rename_i s hs xv hxv xg hxg htr xb hxb hj2
      subst hs
      simp only [AddrIndex.offset64_none, z0, hL, Option.some.injEq] at hxv
      subst hxv
      rw [hG, Option.some.injEq] at hxg
      subst hxg
      simp only [AddrIndex.offset64_scale1, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
        BitVec.ofInt_ofBytes_toBytes 64 8 rfl, hn_eax_v v (by omega)] at hxb
      rw [hn_i64z, BitVec.add_zero, hT, Option.some.injEq] at hxb
      subst hxb
      rw [hn_c8] at hj2
      have hlt := of_decide_eq_false hj2
      rw [hn_r10_4 _ (by omega), h10] at hlt
      have hv : v = 4 := by omega
      subst hv
      refine ⟨⟨c, f, hn_BS_mv hB ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl, ?_, ?_⟩, ?_⟩
      rotate_right
      · subst hn; refine Kraken.lex_cons_le_of_lt (by lex_len) ?_; lex_digit
      all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
      all_goals try rfl
      all_goals try exact hix
      all_goals first | exact hn_one32 | exact hn_lg4

set_option maxRecDepth 20000 in
/-- The scalar fill setup: `rax = num_env + 1`, `esi = 32`. -/
theorem blk_L6f5 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L6f5" := by
  cfg_block
  measure_hb "L6f5"
    intro n
    simp only [tab_L6f5, var_L6f5, tab_L700, var_L700]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, v, hB, hv12, hdx, hcx⟩, hn⟩ := hs₀
    have hB' := hB
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, hf, hP, hbl, h08, hid⟩, hm⟩, ⟨h13, h12⟩, hbx, hKp⟩, hH, h38, hv4, hne,
      h58, h10, hb0, hix⟩ := hB'
    have hax : (s₀.regs.get64 .r10 + Int64.toBitVec 1).toNat = v + 1 := by
      rw [BitVec.toNat_add, h10, show (Int64.toBitVec 1).toNat = 1 by simp]; omega
    have hsi : (BitVec.setWidth 64 ((BitVec.setWidth 32 (s₀.regs.get64 .rdx)) <<<
        ((Int64.toBitVec 5).toNat % 32))).toNat = 32 * (s₀.regs.get64 .rdx).toNat := by
      rw [hdx]; simp
    vcgen
    all_goals try call_simp
    case vc1 => simp
    case vc2 =>
      rename_i s hs fl
      subst hs
      refine ⟨⟨c, f, v, hn_BS_mv hB ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl, hv12, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      rotate_right
      · subst hn; refine Kraken.lex_cons_le_of_lt (by lex_len) ?_; lex_digit
      all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
      all_goals try rfl
      all_goals try exact hix
      all_goals try exact hax
      all_goals try exact hcx
      all_goals try (rw [hdx]; simp <;> omega)
      · rw [Reg64s.get_low32]
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_32_64_32]
        exact hsi
      · simp only [Fixed]
        intro e h1 h2
        rw [hdx] at h2
        simp at h2
        omega

set_option maxRecDepth 20000 in
/-- The scalar fill: `border[rdx] = (32 rdx >> log2 v) - 1`. -/
theorem blk_L700 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L700" := by
  cfg_block
  measure_hb "L700"
    intro n
    simp only [tab_L700, var_L700, tab_L715, var_L715]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, v, hB, hv12, hax, hd1, hdv, hsi, hcx, hfx⟩, hn⟩ := hs₀
    have hB' := hB
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, hf, hP, hbl, h08, hid⟩, hm⟩, ⟨h13, h12⟩, hbx, hKp⟩, hH, h38, hv4, hne,
      h58, h10, hb0, hix⟩ := hB'
    have hcl : c.length = 764 := hP.1
    obtain ⟨j, hj⟩ : ∃ j, (s₀.regs.get64 .rdx).toNat = j := ⟨_, rfl⟩
    rw [hj] at hd1 hdv hfx
    have hj5 : j ≤ 2 := by omega
    have hsi' : (s₀.regs.get64 .rsi).toNat = 32 * j := by rw [hsi, hj]
    have hW := hn_fill _ _ j v hsi' hd1 hdv hv12 hcx
    have hFx := hn_fixed_step hcl hfx (by omega) _ hW
    have hrd : (s₀.regs.get64 .rdx + 1).toNat = j + 1 := by
      rw [BitVec.toNat_add, hj]; simp; omega
    have hrs := hn_rsi_step _ j hsi' (by omega)
    have e0 : s₀.regs.get64 .rbx + s₀.regs.get64 .rdx * 4#64 + Int64.toBitVec 52
        = arg2 t₀ + BitVec.ofNat 64 (52 + 4 * j) := by
      rw [hbx]; apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
        show (Int64.toBitVec 52).toNat = 52 by simp, hj]
      omega
    have l1 := Fr_c_isSome hm hcl (52 + 4 * j) 4 (by omega)
    have hst := fun w => Fr_c_store hm hcl (52 + 4 * j) 4 (by omega) w
    rw [← e0] at l1 hst
    have P := PLift.up hst
    clear hst
    vcgen
    all_goals try call_simp
    all_goals (have hs := ‹_ = s₀›; subst hs)
    all_goals simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ite_self,
      AddrIndex.offset64_scale4] at *
    case vc1 => exact l1
    case vc2 =>
      rename_i hjn _
      rw [hn_nz64, Bool.not_eq_true', decide_eq_false_iff_not] at hjn
      have hlt : j + 1 ≤ v := by
        rw [← BitVec.toNat_inj, hax, hrd] at hjn; omega
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.L700") ⟨rfl, ?_, Or.inl ?_⟩
      · refine (tab_L700 _ _ _ _ _ _).mpr ?_
        refine ⟨_, f, v, hn_BS_wr hB _ _ (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ (P.down _), hv12,
          ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, get64_ite, ite_self]
        all_goals try rfl
        all_goals try exact hix
        all_goals try exact hax
        all_goals try exact hcx
        all_goals try (rw [hrd]; omega)
        all_goals try (rw [hrs, hrd])
        all_goals try (rw [hrd]; exact hFx)
      · rw [var_L700]
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, get64_ite, ite_self]
        subst hn
        refine Kraken.lex_cons_lt_cons (by lex_len) ?_
        refine Kraken.lex_cons_lt_of_lt (by lex_len) ?_
        rw [BitVec.toNat_sub, BitVec.toNat_sub, hrd, hax, hj]; omega
    case vc3 =>
      rename_i hjn _
      rw [hn_nz64] at hjn
      simp only [Bool.not_eq_false', decide_eq_true_eq] at hjn
      have hjv : j = v := by
        have := congrArg BitVec.toNat hjn
        rw [hax, hrd] at this; omega
      subst hjv
      refine ⟨toHdr (hn_BS_wr hB _ _ (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ (P.down _))
        (hn_bordTo_fin (hn_bord0_wr hcl hd1 (by omega) _ hb0) hFx hv12), ?_⟩
      rotate_right
      · subst hn; refine Kraken.lex_cons_le_of_lt (by lex_len) ?_; lex_digit
      all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, get64_ite, ite_self]
      all_goals try rfl
      all_goals try exact hix

set_option maxRecDepth 20000 in
/-- `num_env = 4`: `xmm0 = log2 4 = 2`, `rax = 0`; the `num_env ≥ 16` trap is not taken. -/
theorem blk_L259 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L259" := by
  cfg_block
  measure_hb "L259"
    intro n
    simp only [tab_L259, var_L259, tab_L69c, var_L69c, tab_L3aa, var_L3aa]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hB, hcx, hdx⟩, hn⟩ := hs₀
    have hB' := hB
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, hf, hP, hbl, h08, hid⟩, hm⟩, ⟨h13, h12⟩, hbx, hKp⟩, hH, h38, hv4, hne,
      h58, h10, hb0, hix⟩ := hB'
    have e1 : s₀.regs.get64 .rbp + Int64.toBitVec (-72)
        = t₀.regs.get64 .rsp - 0xa8#64 + BitVec.ofNat 64 0x58 := by
      rw [hbp]; exact fr_addr _ 72 (by omega) (by omega)
    have hL := Fr_f_load hm hf 0x58 1 (by omega)
    rw [← e1] at hL
    have z0 : ∀ a : BitVec 64, a + 0 = a := fun a => by simp
    have hb4 : Int.ofBytes (List.take 1 (List.drop 88 f)) = 4 := by
      apply hn_byte0 _ _ (by simp; omega) _ (by omega)
      exact h58
    vcgen
    all_goals try call_simp
    all_goals (have hs := ‹_ = s₀›; subst hs)
    case vc1 =>
      simp only [AddrIndex.offset64_none, z0]
      rw [hL]; rfl
    case vc2 =>
      rename_i xv hxv hj _
      simp only [AddrIndex.offset64_none, z0, hL, Option.some.injEq] at hxv
      rw [hb4] at hxv
      subst hxv
      rw [hn_nc8] at hj
      simp only [hn_lt16, decide_true, Bool.not_true] at hj
      exact absurd hj (by simp)
    case vc3 =>
      rename_i xv hxv hj _
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.L69c") ⟨rfl, ?_, Or.inl ?_⟩
      · refine (tab_L69c _ _ _ _ _ _).mpr ?_
        refine ⟨c, f, hn_BS_mv hB ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl, ?_, ?_, ?_⟩
        all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
        all_goals try rfl
        all_goals try exact hix
        · simp
        · exact hdx
        · rw [RegZmms.get_set_xmm_same, hcx]; decide
      · rw [var_L69c]; subst hn; exact Kraken.lex_cons_lt_of_lt rfl (by decide)

set_option maxRecDepth 20000 in
/-- The vector fill setup: `xmm1 = {1, 2, 3, 4}`, `xmm2 = -1`, `esi = 4`. -/
theorem blk_L69c (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L69c" := by
  cfg_block
  measure_hb "L69c"
    intro n
    simp only [tab_L69c, var_L69c, tab_L6d0, var_L6d0]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hB, hax, hdx, hx0⟩, hn⟩ := hs₀
    have hB' := hB
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, hf, hP, hbl, h08, hid⟩, hm⟩, ⟨h13, h12⟩, hbx, hKp⟩, hH, h38, hv4, hne,
      h58, h10, hb0, hix⟩ := hB'
    have hr10 : s₀.regs.get64 .r10 = 4#64 := BitVec.eq_of_toNat_eq (by rw [h10]; rfl)
    have hc28 := Fr_lcpi28 hm
    have hc30 := Fr_lcpi30 hm
    vcgen [hn_vpshufd_spec, hn_vpcmpeqd_spec, hn_vpmovzxdq_spec]
    all_goals try call_simp
    all_goals (have hs := ‹_ = s₀›; subst hs)
    case vc1 => rw [hc28]; rfl
    case vc2 => rw [hc30]; rfl
    case vc3 =>
      rename_i x28 h28 x30 h30 _
      rw [hc28, Option.some.injEq] at h28
      subst h28
      rw [hc30, Option.some.injEq] at h30
      subst h30
      refine ⟨⟨c, f, hn_BS_mv hB ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      rotate_right
      · subst hn; refine Kraken.lex_cons_le_of_lt (by lex_len) ?_; lex_digit
      all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
        RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne, ne_eq, not_false_eq_true]
      all_goals try rfl
      all_goals try exact hix
      all_goals try exact hax
      all_goals try rw [hr10]
      all_goals try rw [hdx]
      all_goals try rw [hx0]
      all_goals try exact hn_cmpeq_self _
      all_goals first
        | (simp; done)
        | (simp [BitVec.packedBinOp, BitVec.pshufd128] <;> first | rfl | decide)
        | decide

end Kraken.Examples.Sbr.Ps
