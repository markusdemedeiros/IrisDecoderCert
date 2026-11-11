import Kraken.X64.Examples.Sbr.Parse.PsBlkLLib

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Ps

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

set_option maxRecDepth 20000 in
theorem blk_715 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.L715" := by
  cfg_block
  simp only [tab_L715, var_L715, tab_L71b, var_L71b]
  measure_hb "L715"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, ⟨hC, ⟨hsp, hbp, hfl, hP, hB1⟩, hm⟩, hR, hbx, hix, hH, h10, hW⟩, hn⟩ := hs₀
    have hcl : c.length = 764 := hP.1
    have l1 := Fr_c_load hm hcl 4 4 (by omega)
    have e2 : arg2 t₀ + (4 : Int64).toBitVec = arg2 t₀ + BitVec.ofNat 64 4 := rfl
    rw [← e2, ← hbx] at l1
    have s1 := fun v => Fr_f_store hm hfl 0x34 4 (by omega) v
    have e1 : s₀.regs.get64 .rbp + (-108 : Int64).toBitVec
        = rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 0x34 := by
      rw [hbp, Int64.toBitVec_neg_ofNat_norm]; bv_omega
    rw [← e1] at s1
    have l2 := Fr_f_load hm hfl 0x34 4 (by omega)
    rw [← e1] at l2
    vcgen
    all_goals try subst_vars
    case vc1 => simp only [l1, Option.isSome_some]
    all_goals rename_i v1 hv1
    all_goals simp only [l1, Option.some.injEq] at hv1
    all_goals subst hv1
    case vc2 => simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, l2, Option.isSome_some]
    case vc3 =>
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]
      refine ⟨⟨c, wr f 0x34 4 _, ⟨hC, ⟨hsp, hbp, ?_, hP, ?_⟩, s1 _⟩, hR, hbx, hix, ?_, h10, ?_, ?_, ?_⟩, ?_⟩
      · fsimp; exact hfl
      · fsimp; exact hB1
      · simp only [HSlots] at hH ⊢; fsimp; exact hH
      · fsimp; simp only [BitVec.ofInt_toInt, BitVec.setWidth_32_64_32, rd_i32]
      · simp only [Reg64s.get64_set64, ite_true, BitVec.setWidth_32_64_32, rd_i32]
      · intro hw; fsimp; exact hW hw
      · exact Kraken.lex_cons_le_of_lt rfl (by decide)

set_option maxRecDepth 20000 in
theorem blk_71b (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.L71b" := by
  cfg_block
  simp only [tab_L71b, var_L71b, tab_L737, var_L737]
  measure_hb "L71b"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, ⟨hC, ⟨hsp, hbp, hfl, hP, hB1⟩, hm⟩, hR, hbx, hix, hH, h10, h34, hax, hW⟩, hn⟩ := hs₀
    subst hn
    have hcl : c.length = 764 := hP.1
    have e1 : s₀.regs.get64 .rbp + (-56 : Int64).toBitVec
        = rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 0x68 := slot_addr hbp 56 0x68 rfl
    have e2 : s₀.regs.get64 .rbp + (-96 : Int64).toBitVec
        = rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 0x40 := slot_addr hbp 96 0x40 rfl
    have e3 : s₀.regs.get64 .rbp + 0 + (-72 : Int64).toBitVec
        = rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 0x58 :=
      slot_addr (by rw [hbp]; exact BitVec.add_zero _) 72 0x58 rfl
    have s1 := Fr_f_store hm hfl 0x68 8 (by omega) (s₀.regs.get64 .rbx).toInt
    have hf1 : (wr f 0x68 8 (s₀.regs.get64 .rbx).toInt).length = 0x78 := by
      rw [wr_len _ _ _ _ (by omega)]; exact hfl
    have s2 := Fr_f_store s1 hf1 0x40 8 (by omega) (s₀.regs.get64 .r10).toInt
    have hf2 : (wr (wr f 0x68 8 (s₀.regs.get64 .rbx).toInt) 0x40 8
        (s₀.regs.get64 .r10).toInt).length = 0x78 := by
      rw [wr_len _ _ _ _ (by omega)]; exact hf1
    have l3 := Fr_f_load s2 hf2 0x58 8 (by omega)
    have l1 := Fr_f_load hm hfl 0x68 8 (by omega)
    have l2 := Fr_f_load s1 hf1 0x40 8 (by omega)
    rw [← e1] at s1
    rw [← e2, ← e1] at s2
    rw [← e3, ← e2, ← e1] at l3
    obtain ⟨h0, h4, h58, h38⟩ := hH
    have hLS : LSlots t₀ c (wr (wr f 0x68 8 (s₀.regs.get64 .rbx).toInt) 0x40 8
        (s₀.regs.get64 .r10).toInt) := by
      refine ⟨⟨h0, h4, ?_, ?_⟩, ?_, ?_, ?_⟩
      · fsimp; exact h58
      · fsimp; exact h38
      · fsimp; exact h34
      · fsimp; rw [BitVec.ofInt_toInt]; exact hbx
      · rw [rd_wr_same _ _ _ _ (by omega), rd_toBytes64]; omega
    have hB2 : BitVec.ofInt 32 (rd (wr (wr f 0x68 8 (s₀.regs.get64 .rbx).toInt) 0x40 8
        (s₀.regs.get64 .r10).toInt) 0x74 4) = bitsLeft t₀
        ∧ BitVec.ofInt 64 (rd (wr (wr f 0x68 8 (s₀.regs.get64 .rbx).toInt) 0x40 8
        (s₀.regs.get64 .r10).toInt) 0x08 8) = arg1 t₀
        ∧ BitVec.ofInt 32 (rd (wr (wr f 0x68 8 (s₀.regs.get64 .rbx).toInt) 0x40 8
        (s₀.regs.get64 .r10).toInt) 0x14 4) = x.idx := by fsimp; exact hB1
    have hW2 : PsWFb x.c → Rng c ∧ Hdr c ∧ IidS c (rd (wr (wr f 0x68 8 (s₀.regs.get64 .rbx).toInt)
        0x40 8 (s₀.regs.get64 .r10).toInt) 0x18 4) := by fsimp; exact hW
    rw [← e1] at l1
    rw [← e2, ← e1] at l2
    vcgen
    all_goals try subst_vars
    all_goals dsimp only
    case vc1 => simp only [l1, Option.isSome_some]
    case vc2 => simp only [l2, Option.isSome_some]
    case vc4 => simp only [AddrIndex.offset64_none, l3, Option.isSome_some]
    all_goals clear hm s1
    case vc3 =>
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.La1e") ⟨rfl, ?_, Or.inl ?_⟩
      · refine (tab_La1e _ _ _ _ _ _).mpr ?_
        exact ⟨c, _, ⟨⟨hC, ⟨hsp, hbp, hf2, hP, hB2⟩, s2⟩, hR, hix, hLS⟩, hbx, h10, hW2⟩
      · rw [var_La1e]
        exact Kraken.lex_cons_lt_of_lt rfl (by decide)
    case vc5 =>
      rename_i af hz v hv af2 hle
      dsimp only at hz hle hv
      simp only [AddrIndex.offset64_none, l3, Option.some.injEq] at hv
      subst hv
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false] at hle
      simp (disch := omega) only [rd_wr_disj] at hle ⊢
      simp only [h58] at hle ⊢
      rw [le_and8_small _ h0 h4, decide_eq_true_eq] at hle
      simp only [CondCode.interp_z, StatusFlags.zf_from_result, BitVec.and_self, hax] at hz
      have h4' : i32 c 4 ≠ 0 := by
        intro e
        have h' : BitVec.ofInt 32 (i32 c 4) = 0#32 := by rw [e]; rfl
        simp only [h'] at hz
        exact absurd hz (by decide)
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.La4c") ⟨rfl, ?_, Or.inl ?_⟩
      · refine (tab_La4c _ _ _ _ _ _).mpr ?_
        refine ⟨c, _, ⟨hC, ⟨hsp, hbp, hf2, hP, hB2⟩, s2⟩, hR, hix, hLS, ?_, ?_⟩
        · simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact h10
        · intro hw
          have hne : ne c = 0 := hle
          exact ⟨(hW2 hw).1, (hW2 hw).2.1, (hW2 hw).2.2, fun e he => by omega,
            fun h => absurd h h4'⟩
      · rw [var_La4c]
        exact Kraken.lex_cons_lt_of_lt rfl (by decide)
    case vc6 =>
      rename_i af hz v hv af2 hle
      dsimp only at hz hle hv
      simp only [AddrIndex.offset64_none, l3, Option.some.injEq] at hv
      subst hv
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false] at hle hz ⊢
      simp (disch := omega) only [rd_wr_disj] at hle ⊢
      simp only [h58] at hle ⊢
      rw [le_and8_small _ h0 h4, decide_eq_false_iff_not] at hle
      simp only [CondCode.interp_z, StatusFlags.zf_from_result, BitVec.and_self, hax] at hz
      have h4' : i32 c 4 ≠ 0 := by
        intro e
        have h' : BitVec.ofInt 32 (i32 c 4) = 0#32 := by rw [e]; rfl
        simp only [h'] at hz
        exact absurd hz (by decide)
      have hne : ¬ ne c = 0 := hle
      have h0' : 0 ≤ ne c := h0
      refine ⟨⟨c, _, ⟨⟨hC, ⟨hsp, hbp, hf2, hP, hB2⟩, s2⟩, hR, hix, hLS⟩, hbx, h4', by omega,
        ?_, hW2⟩, Kraken.lex_cons_le_of_lt rfl (by decide)⟩
      all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]

set_option maxRecDepth 20000 in
theorem blk_737 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.L737" := by
  cfg_block
  simp only [tab_L737, var_L737, tab_L74a, var_L74a]
  measure_hb "L737"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hLB, hbx, h4, hne, hax, hW⟩, hn⟩ := hs₀
    subst hn
    have hcl := LB_cl hLB
    have hfl := LB_fl hLB
    have hm := hLB.1.2.2
    have hbp := hLB.1.2.1.2.1
    have h8 : i32 c 8 = 0 ∨ i32 c 8 = 1 := hLB.1.2.1.2.2.2.1.2.2.2.2.2.2
    have hcx : (BitVec.ofInt 32 (rd c 8 4)).setWidth 64 = BitVec.ofInt 64 (i32 c 8) := by
      rw [rd_i32]; exact zx_ofInt32 _ (by omega) (by omega)
    have e1 : s₀.regs.get64 .rbp + (-80 : Int64).toBitVec
        = rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 0x50 := slot_addr hbp 80 0x50 rfl
    have l1 := Fr_c_load hm hcl 8 4 (by omega)
    have e2 : arg2 t₀ + (8 : Int64).toBitVec = arg2 t₀ + BitVec.ofNat 64 8 := rfl
    rw [← e2, ← hbx] at l1
    have s1 := fun v => Fr_f_store hm hfl 0x50 8 (by omega) v
    rw [← e1] at s1
    have l2 := Fr_f_load hm hfl 0x50 8 (by omega)
    rw [← e1] at l2
    vcgen
    all_goals try subst_vars
    case vc1 => simp only [l1, Option.isSome_some]
    case vc2 =>
      rename_i v hv
      simp only [l1, Option.some.injEq] at hv
      subst hv
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, l2, Option.isSome_some]
    case vc3 =>
      rename_i v hv
      simp only [l1, Option.some.injEq] at hv
      subst hv
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_scale8, hcx]
      refine ⟨⟨c, _, LB_wrf hLB rfl rfl hLB.2.1 hLB.2.2.1 (s1 _) (by omega), h4, hne, hax, ?_, ?_, ?_,
        by fsimp; exact hW⟩, Kraken.lex_cons_le_of_lt rfl (by decide)⟩
      · rw [hbx]; rfl
      · rw [rd_wr_self f 0x50 8 64 _ (by omega) rfl, BitVec.ofInt_toInt]
      · rcases h8 with h | h <;> simp only [h] <;> rfl

set_option maxRecDepth 20000 in
theorem blk_74a (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.L74a" := by
  cfg_block
  simp only [tab_L74a, var_L74a]
  measure_hb "L74a"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hLB, h4, hne, hax, h14, h50, h9, hW⟩, hn⟩ := hs₀
    subst hn
    have hcl := LB_cl hLB
    have hfl := LB_fl hLB
    have hm := hLB.1.2.2
    have hbp := hLB.1.2.1.2.1
    have hne4 : ne c ≤ 4 := hLB.2.2.2.1.2.1
    have e1 : s₀.regs.get64 .rbp + (-120 : Int64).toBitVec
        = rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 0x28 := slot_addr hbp 120 0x28 rfl
    have e2 : s₀.regs.get64 .rbp + (-128 : Int64).toBitVec
        = rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 0x20 := slot_addr hbp 128 0x20 rfl
    have s1 := fun v => Fr_f_store hm hfl 0x28 8 (by omega) v
    rw [← e1] at s1
    have s2 := fun v w => Fr_f_store (s1 v) (by fsimp; exact hfl) 0x20 8 (by omega) w
    rw [← e2] at s2
    have l1 := Fr_f_load hm hfl 0x28 8 (by omega)
    rw [← e1] at l1
    have l2 := fun v => Fr_f_load (s1 v) (by fsimp; exact hfl) 0x20 8 (by omega)
    rw [← e2] at l2
    have hv : rd (wr f 0x28 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (s₀.regs.get64 .rax))).toInt)
        0x28 8 = ne c := by
      rw [rd_wr_same _ _ _ _ (by omega), rd_toBytes64, hax]
      have h0 : 0 ≤ ne c := by omega
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt]
      omega
    vcgen
    all_goals try subst_vars
    all_goals try dsimp only
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.xor_self]
    case vc1 => simp only [l1, Option.isSome_some]
    case vc2 => simp only [l2, Option.isSome_some]
    case vc3 =>
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.L775") ⟨rfl, ?_, Or.inl ?_⟩
      · refine (tab_L775 _ _ _ _ _ _).mpr ?_
        refine ⟨c, _, 0, ⟨LB_wrf (LB_wrf_m hLB _ (s1 _) (by omega)) rfl rfl
          hLB.2.1 hLB.2.2.1 (s2 _ _) (by omega), ⟨h4, ?_, ?_, ?_⟩, h9, by simpa using hne, ?_, ?_⟩, ?_⟩
        · fsimp; exact hv
        · rw [rd_wr_self _ 32 8 64 _ (by fsimp; omega) rfl, BitVec.ofInt_toInt, h14]
        · fsimp; exact h50
        · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]; rfl
        · simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, h14]
        · intro hw
          obtain ⟨hr, hh, hi⟩ := hW hw
          exact ⟨hr, hh, by fsimp; exact hi, fun e he => absurd he (by omega),
            fun b hb => absurd hb (by omega)⟩
      · rw [var_L775]
        exact Kraken.lex_cons_lt_of_lt rfl (by decide)

end Kraken.Examples.Sbr.Ps
