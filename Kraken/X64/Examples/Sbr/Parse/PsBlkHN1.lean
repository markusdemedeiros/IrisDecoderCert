import Kraken.X64.Examples.Sbr.Parse.PsBlkHNLib

/-!
# `ff_ps_read_data`: `num_env`, the first branches, the unreachable blocks
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
/-- Unreachable (`num_env ≤ 4`). -/
theorem blk_L36e (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L36e" := by
  cfg_block
  intro n
  simp only [tab_L36e]
  exact Triple.pin fun _ h => h.1.elim

set_option maxRecDepth 20000 in
/-- `num_env` loaded into `r10b` is at least 1: on to the borders. -/
theorem blk_L26e (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L26e" := by
  cfg_block
  measure_hb "L26e"
    intro n
    simp only [tab_L26e, var_L26e, tab_L277, var_L277]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, v, hBS, hv1⟩, hn⟩ := hs₀
    have h10 : (s₀.regs.get64 .r10).toNat = v := hBS.2.2.2.2.2.2.1
    have hv4 : v ≤ 4 := hBS.2.2.2.1
    have hle := hn_le_test8 (s₀.regs.get64 .r10) (by omega) (by omega)
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    case vc1 => rename_i h; rw [hle] at h; exact absurd h (by decide)
    case vc2 => exact ⟨⟨c, f, _, hBS, hv1⟩, by var_step⟩

set_option maxRecDepth 20000 in
/-- `num_env` from `num_env_tab[frame_class][bits]`. -/
theorem blk_L1fa (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L1fa" := by
  cfg_block
  measure_hb "L1fa"
    intro n
    simp only [tab_L1fa, var_L1fa, tab_L216, var_L216]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hHB, hH, h38, hix, hsi, hr9⟩, hn⟩ := hs₀
    have hHB' := hHB
    obtain ⟨⟨hC, ⟨hsp, hbp, hf, hP, hbl, h08, hid⟩, hm⟩, ⟨h13, h12⟩, hbx, hKp⟩ := hHB'
    have hj : 4 * (s₀.regs.get64 .rsi).toNat + (s₀.regs.get64 .r9).toNat < 8 := by omega
    have ea := hn_nenv_addr (lab "num_env_tab") (s₀.regs.get64 .r9) (s₀.regs.get64 .rsi) hsi hr9
    have hL := Fr_nenv hm _ hj
    have hv := hn_nenv_val _ hj
    have hr0 : (s₀.regs.get64 .rsi).toNat = 0 → 4 * (s₀.regs.get64 .rsi).toNat + (s₀.regs.get64 .r9).toNat < 4 := by omega
    have hr1 : (s₀.regs.get64 .rsi).toNat = 1 → 4 ≤ 4 * (s₀.regs.get64 .rsi).toNat + (s₀.regs.get64 .r9).toNat := by omega
    generalize 4 * (s₀.regs.get64 .rsi).toNat + (s₀.regs.get64 .r9).toNat = j at hj ea hL hv hr0 hr1
    have e1 : s₀.regs.get64 .rbp + Int64.toBitVec (-72)
        = t₀.regs.get64 .rsp - 0xa8#64 + BitVec.ofNat 64 0x58 := by
      rw [hbp]; exact fr_addr _ 72 (by omega) (by omega)
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals try pnorm at *
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      AddrIndex.offset64, Width.bytes, BitVec.mul_one] at *
    all_goals try simp only [e1] at *
    case vc1 => rw [ea, hL]; rfl
    case vc2 => exact Fr_f_isSome hm hf 0x58 8 (by omega)
    case vc3 =>
      rename_i hld
      rw [ea, hL, Option.some.injEq] at hld
      subst hld
      refine ⟨?_, by var_step⟩
      generalize BitVec.setWidth 64 (BitVec.signExtend 32 (BitVec.ofInt 8
        (rd [0, 1, 2, 4, 1, 2, 3, 4] j 1))) = V at hv ⊢
      obtain ⟨hv4, hv10, hv0, hv1⟩ := hv
      unfold q216 HB Cm Bs HdrOk
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hv10]
      have hfl : (wr f 0x58 8 V.toInt).length = 0x78 := by rw [wr_length _ _ _ _ (by omega), hf]
      refine ⟨c, wr f 0x58 8 V.toInt, ⟨⟨hC, ⟨?_, ?_, hfl, hP, ?_, ?_, ?_⟩, Fr_f_store hm hf 0x58 8 (by omega) _⟩,
        ⟨?_, ?_⟩, ?_, hKp⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]
      all_goals try trivial
      all_goals try assumption
      all_goals try (rw [rd_wr_disj _ _ _ _ _ _ (by omega) (by omega)]; assumption)
      · rw [rd_wr_disj _ _ _ _ _ _ (by omega) (by omega)]; exact hH.1
      · rw [rd_wr_disj _ _ _ _ _ _ (by omega) (by omega)]; exact hH.2
      · unfold S38; rw [rd_wr_disj _ _ _ _ _ _ (by omega) (by omega)]; exact h38
      · rw [rd_wr_same _ _ _ _ (by omega), rd_toBytes64]
      · intro h0; exact hv0 (hr0 h0)
      · intro h1; exact hv1 (hr1 h1)

set_option maxRecDepth 20000 in
/-- `num_env` and `border[0] = -1` stored; branch on the frame class and `num_env`. -/
theorem blk_L216 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L216" := by
  cfg_block
  measure_hb "L216"
    intro n
    simp only [tab_L216, var_L216, tab_L22d, var_L22d]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hHB, hH, h38, hix, hsi, hax, h10, h58, hs0, hs1⟩, hn⟩ := hs₀
    have hHB' := hHB
    obtain ⟨⟨hC, ⟨hsp, hbp, hf, hP, hbl, h08, hid⟩, hm⟩, ⟨h13, h12⟩, hbx, hKp⟩ := hHB'
    have hcl : c.length = 764 := hP.1
    have e44 : s₀.regs.get64 .rbx + 44#64 = arg2 t₀ + BitVec.ofNat 64 44 := by rw [hbx]
    have e52 : s₀.regs.get64 .rbx + 52#64 = arg2 t₀ + BitVec.ofNat 64 52 := by rw [hbx]
    have hl1 : ∀ v, (wr c 44 4 v).length = 764 := fun v => (wr_length c 44 4 v (by omega)).trans hcl
    have l1 := Fr_c_isSome hm hcl 44 4 (by omega)
    have l2 := fun v => Fr_c_isSome (Fr_c_store hm hcl 44 4 (by omega) v) (hl1 v) 52 4 (by omega)
    have hst := fun v w => Fr_c_store (Fr_c_store hm hcl 44 4 (by omega) v) (hl1 v) 52 4 (by omega) w
    rw [← e44] at l1 l2 hst
    rw [← e52] at l2 hst
    have hsi31 : (s₀.regs.get64 .rsi).toNat < 2 ^ 31 := by omega
    have hz := hn_nz32 (s₀.regs.get64 .rsi) hsi31
    have hle := hn_le8 (s₀.regs.get64 .r10) (by rw [h10]; omega)
    have ha4 := hax
    rw [← h10] at ha4 hs0 hs1
    have P := PLift.up hst
    clear hst
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try simp only [AddrIndex.offset64_none, BitVec.add_zero, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat] at *
    case vc1 => exact l1
    case vc2 => exact l2 _
    case vc3 =>
      rename_i _ hj
      rw [hz] at hj
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.L26e") ⟨rfl, ?_, Or.inl ?_⟩
      · refine (tab_L26e _ _ _ _ _ _).mpr ?_
        exact ⟨_, _, _, hn_BS216 hHB hH h38 hix hax h10 h58 (by rfl) (by exact P.down _ _),
          by rw [← h10]; exact hs1 (by have := of_decide_eq_true hj; omega)⟩
      · rw [var_L26e]; first | var_step | exact Kraken.lex_cons_lt_of_lt rfl (by decide)
    case vc4 =>
      rename_i _ hj0 _ hj
      rw [hle] at hj
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.L715") ⟨rfl, ?_, Or.inl ?_⟩
      · refine (tab_L715 _ _ _ _ _ _).mpr ?_
        exact toHdr0 (hn_BS216 hHB hH h38 hix hax h10 h58 (by rfl) (by exact P.down _ _))
          (by rw [← h10]; exact of_decide_eq_true hj)
      · rw [var_L715]; first | var_step | exact Kraken.lex_cons_lt_of_lt rfl (by decide)
    case vc5 =>
      rename_i _ hj0 _ hj
      rw [hle] at hj; rw [hz] at hj0
      refine ⟨⟨_, _, _, hn_BS216 hHB hH h38 hix hax h10 h58 (by rfl) (by exact P.down _ _), ?_, ?_⟩,
        by var_step⟩
      · rw [← h10]; have := of_decide_eq_false hj; omega
      · rw [← h10]; exact hs0 (by have := of_decide_eq_false hj0; omega)

set_option maxRecDepth 20000 in
/-- Unreachable (`num_env ≤ 4`). -/
theorem blk_L3aa (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L3aa" := by
  cfg_block
  intro n
  simp only [tab_L3aa]
  exact Triple.pin fun _ h => h.1.elim

set_option maxRecDepth 20000 in
/-- Unreachable. -/
theorem blk_L689 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L689" := by
  cfg_block
  intro n
  simp only [tab_L689]
  exact Triple.pin fun _ h => h.1.elim

end Kraken.Examples.Sbr.Ps
