import Kraken.X64.Examples.Sbr.Parse.PsBlkT2Lib

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Ps

theorem t2_PsInv_wr0 {c : List UInt8} (h : PsInv c) (v : Int) : PsInv (wr c 0 4 v) := by
  obtain ⟨hl, h1, h2, h3, h4, h5, h6⟩ := h
  have hL : 0 + 4 ≤ c.length := by omega
  refine ⟨by rw [wr_length _ _ _ _ hL, hl], ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := omega) only [i32_wr] <;> assumption

theorem t2_cmov (r p i : BitVec 32) (hr : 0 ≤ r.toInt) (hi : i.toNat ≤ p.toNat)
    (hp : p.toNat < 2 ^ 31) :
    (if r.toInt < (p - i).toInt then r else p - i).toNat ≤ p.toNat - i.toNat := by
  have e : (p - i).toNat = p.toNat - i.toNat := by rw [BitVec.toNat_sub]; omega
  have e2 := BitVec.toInt_eq_toNat_cond (p - i)
  have e3 := BitVec.toInt_eq_toNat_cond r
  split
  · rename_i hlt
    rw [e2, e] at hlt; rw [e3] at hlt hr
    split at hlt <;> split at hr <;> omega
  · omega

variable [CodeEnv]

theorem t2_Cm_st0 {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64}
    {t₀ s : MachineData} {c f : List UInt8} (h : Cm k Ext x ra t₀ s c f) (v : Int)
    (s' : MachineData) (hm : s'.dmem = s.dmem.storeInt (arg2 t₀) 4 v)
    (hsp : s'.regs.get64 .rsp = s.regs.get64 .rsp) (hbp : s'.regs.get64 .rbp = s.regs.get64 .rbp) :
    Cm k Ext x ra t₀ s' (wr c 0 4 v) f := by
  obtain ⟨hC, ⟨a1, a2, a3, a4, a5⟩, hM⟩ := h
  refine ⟨hC, ⟨by rw [hsp]; exact a1, by rw [hbp]; exact a2, a3, t2_PsInv_wr0 a4 v, a5⟩, ?_⟩
  have := Fr_c_store hM a4.1 0 4 (by omega) v
  simp only [BitVec.add_zero] at this
  rw [hm]; exact this

open scoped Kraken.Rules.GenericMem.Norm

set_option maxRecDepth 20000 in
/-- The error path: `start = 0`; skip `bits_left` in `*gb_host` (clamp, first half). -/
theorem blk_L1479 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L1479" := by
  cfg_block
  measure_hb "L1479"
    intro n
    simp only [tab_L1479, var_L1479, tab_L1499, var_L1499]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨c, f, hC, hbx, hR⟩, h15⟩, hn⟩ := hs₀
    have hl : c.length = 764 := hC.2.1.2.2.2.1.1
    have L8 := t2_fload hC (18446744073709551464#64) 0x98 8 rfl (by omega) (by omega) (by omega)
    have hPs := hC.1
    have ha1 := hC.2.1.2.2.2.2.2.1
    let v : Int := (BitVec.setWidth 32 0#64).toInt
    let s₁ : MachineData := { s₀ with dmem := s₀.dmem.storeInt (s₀.regs.get64 .rbx) 4 v }
    have C1 : Cm k Ext x ra t₀ s₁ (wr c 0 4 v) f :=
      t2_Cm_st0 hC v s₁ (by simp only [s₁, hbx]) rfl rfl
    have L8' := t2_fload C1 (18446744073709551464#64) 0x98 8 rfl (by omega) (by omega) (by omega)
    have Gi := Fr_gb_idx C1.2.2
    have Gp := Fr_gb_p8 C1.2.2
    simp only [s₁, v] at L8' Gi Gp
    simp only [arg1] at Gi Gp ha1
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals t1norm at *
    · rw [hbx]
      have h0 := Fr_c_isSome hC.2.2 hl 0 4 (by omega)
      simp only [BitVec.add_zero, arg2] at h0
      exact h0
    · rw [L8']; rfl
    · simp only [L8', Option.some.injEq] at *
      subst_vars
      rw [ha1, Gi]; rfl
    · simp only [L8', Option.some.injEq] at *
      subst_vars
      rw [ha1, Gp]; rfl
    · simp only [L8', Option.some.injEq] at *
      subst_vars
      simp only [ha1, Gi, Gp, Option.some.injEq] at *
      subst_vars
      refine ⟨⟨wr c 0 4 v, f, ?_, ?_, ?_, ?_, ?_, ?_⟩, by var_step⟩
      · exact t2_C_eq C1 rfl (by t1r; rfl) (by t1r; rfl)
      · t1r; exact hbx
      · t1r; exact h15
      · simp only [v]; rw [i32_wr_same _ _ _ (by omega)]; rfl
      · intro hw
        have h := hR hw
        simp (disch := omega) only [Rng0, i32_wr] at h ⊢
        exact h
      · obtain ⟨-, -, hip, hp31, -, -, hb0⟩ := hPs
        refine ⟨?_, ?_, ?_, ?_⟩ <;> t1r <;> try simp only [ofInt_toBytes32, t2_sw3264]
        · bv_omega
        rw [CondCode.interp_l_sub32 _ _ _ (by rfl), h15]
        simp only [decide_eq_true_eq]
        exact t2_cmov _ _ _ hb0 hip hp31

end Kraken.Examples.Sbr.Ps
