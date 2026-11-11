import Kraken.X64.Examples.Sbr.Parse.PsBlkT2Lib

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Ps

theorem t2_cmov2 (r p i : BitVec 32) (hr : r.toNat ≤ p.toNat - i.toNat) (hi : i.toNat ≤ p.toNat)
    (b : Bool) : ((if b = true then r else p - i)).toNat ≤ p.toNat - i.toNat := by
  have e : (p - i).toNat = p.toNat - i.toNat := by rw [BitVec.toNat_sub]; omega
  split
  · exact hr
  · omega

theorem t2_idx (a d c' p i : BitVec 32) (b : Bool) (ha : a = i) (hd : d = 0#32 - i)
    (hc : c'.toNat ≤ p.toNat - i.toNat) (hip : i.toNat ≤ p.toNat) (hp : p.toNat < 2 ^ 31) :
    (a + (if b = true then d else c')).toNat ≤ p.toNat := by
  subst a d
  split
  · rw [show i + (0#32 - i) = 0#32 by bv_omega]; simp
  · rw [BitVec.toNat_add]; omega

theorem t2_r0 (r : BitVec 32) (p i : Nat) (h : r.toNat ≤ p - i) (hp : p < 2 ^ 31) : 0 ≤ r.toInt := by
  rw [BitVec.toInt_eq_toNat_cond]; split <;> omega

variable [CodeEnv]

/-- `*gb_host`'s `index` split out of `Fr` (the rest not depending on it). -/
theorem Fr_gb_split (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData)
    (f c : List UInt8) : ∃ G, ∀ j : BitVec 32,
    Fr k Ext x ra t₀ f c j = (Int.toBytes 4 j.toInt =@ (arg1 t₀ + 8#64)) ⋆ G :=
  ⟨_, fun j => by simp only [Fr, PF, GbW]; exact eq_r (eq_r (eq_r (eq_r (eq_l (eq_r (eq_l (eq_r eq_h)))))))⟩

/-- A store to `*gb_host`'s `index`. -/
theorem Fr_gb_st {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64}
    {t₀ : MachineData} {f c : List UInt8} {i : BitVec 32} (h : m =⋆ Fr k Ext x ra t₀ f c i)
    (v : Int) :
    m.storeInt (arg1 t₀ + 8#64) 4 v =⋆ Fr k Ext x ra t₀ f c (BitVec.ofInt 32 v) := by
  obtain ⟨G, hG⟩ := Fr_gb_split k Ext x ra t₀ f c
  rw [hG] at h ⊢
  have e := t1_toBytes_ofInt 4 v
  rw [e]
  exact storeInt_sep _ 4 _ _ m ⟨h, Int.toBytes_length 4 _⟩ v

/-- The exit to `0x14b7` after the store of `index`. -/
theorem t2_q14b7 {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64}
    {t₀ s : MachineData} {c f : List UInt8} (hC : Cm k Ext x ra t₀ s c f)
    (hW : PsWFb x.c → PsWFb c) (s' : MachineData) (a : BitVec 64) (v : Int) (r : BitVec 32)
    (hm : s'.dmem = s.dmem.storeInt a 4 v) (ha : a = arg1 t₀ + 8#64)
    (hsp : s'.regs.get64 .rsp = s.regs.get64 .rsp) (hbp : s'.regs.get64 .rbp = s.regs.get64 .rbp)
    (hr : (s'.regs.get64 .r15).setWidth 32 = r) (hi : (BitVec.ofInt 32 v).toNat ≤ x.p8.toNat)
    (hr0 : 0 ≤ r.toInt) (hr1 : r.toInt ≤ (bitsLeft t₀).toInt) : q14b7 k Ext x ra t₀ s' := by
  obtain ⟨-, ⟨h1, h2, hfl, hPI, -⟩, hM⟩ := hC
  refine ⟨c, _, f, ⟨hPI, hW, hi, by rw [hr]; exact hr0, by rw [hr]; exact hr1⟩, hfl,
    by rw [hsp, h1], by rw [hbp, h2], ?_⟩
  rw [hm, ha]; exact Fr_gb_st hM v

open scoped Kraken.Rules.GenericMem.Norm

set_option maxRecDepth 20000 in
/-- `r8d ≤ bits_left`: the clamp of the skip, first half. -/
theorem blk_L142f (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L142f" := by
  cfg_block
  measure_hb "L142f"
    intro n
    simp only [tab_L142f, var_L142f, tab_L1449, var_L1449]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, ⟨hC, h15, hW⟩, hR⟩, hn⟩ := hs₀
    have L8 := t2_fload hC (18446744073709551464#64) 0x98 8 rfl (by omega) (by omega) (by omega)
    have hPs := hC.1
    have ha1 := hC.2.1.2.2.2.2.2.1
    have Gi := Fr_gb_idx hC.2.2
    have Gp := Fr_gb_p8 hC.2.2
    simp only [arg1] at Gi Gp ha1
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals t1norm at *
    · rw [L8]; rfl
    · simp only [L8, Option.some.injEq] at *
      subst_vars
      rw [ha1, Gi]; rfl
    · simp only [L8, Option.some.injEq] at *
      subst_vars
      rw [ha1, Gp]; rfl
    · simp only [L8, Option.some.injEq] at *
      subst_vars
      simp only [ha1, Gi, Gp, Option.some.injEq] at *
      subst_vars
      obtain ⟨-, -, hip, hp31, -, -, hb0⟩ := hPs
      refine ⟨⟨c, f, ⟨t2_C_eq hC rfl (by t1r) (by t1r), by t1r; exact h15, hW⟩, ?_, ?_⟩, by var_step⟩
      · t1r; exact hR
      · refine ⟨?_, ?_, ?_, ?_⟩ <;> t1r <;> try simp only [ofInt_toBytes32, t2_sw3264]
        · bv_omega
        exact t2_cmov2 _ _ _ hR.1 hip _

set_option maxRecDepth 20000 in
/-- The clamp, second half; `index` stored; the result `r8d`. -/
theorem blk_L1449 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L1449" := by
  cfg_block
  measure_hb "L1449"
    intro n
    simp only [tab_L1449, var_L1449]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, ⟨hC, h15, hW⟩, hR, hax, hdx, hsi, hcx⟩, hn⟩ := hs₀
    have Gi := Fr_gb_idx hC.2.2
    simp only [arg1] at Gi
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals t1norm at *
    · rw [hsi, Gi]; rfl
    · t1_jump "ff_ps_read_data.L14b7"
      show q14b7 _ _ _ _ _ _
      obtain ⟨-, -, hip, hp31, -, -, -⟩ := hC.1
      refine t2_q14b7 hC hW _ _ _ _ rfl (by rw [hsi]) (by t1r) (by t1r) rfl ?_ ?_ ?_
      · simp only [BitVec.ofInt_toInt, t2_sw3264]
        rw [CondCode.interp_l_sub32 _ _ _ (by rfl)]
        exact t2_idx _ _ _ _ _ _ hax hdx hcx hip hp31
      · t1r; rw [t2_sw3264]; exact t2_r0 _ _ _ hR.1 hp31
      · t1r; rw [t2_sw3264]; exact hR.2

end Kraken.Examples.Sbr.Ps
