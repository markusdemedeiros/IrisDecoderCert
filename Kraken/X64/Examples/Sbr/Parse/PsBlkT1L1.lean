import Kraken.X64.Examples.Sbr.Parse.PsBlkT1Lib

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Ps

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

theorem t1L_fload {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64}
    {t₀ s : MachineData} {c f : List UInt8} (h : Cm k Ext x ra t₀ s c f)
    (a : BitVec 64) (d n : Nat) (ha : a.toNat = 2 ^ 64 - d) (h1 : 8 < d) (h2 : d ≤ 0xa0)
    (hn : 0xa0 - d + n ≤ 0x78) :
    s.dmem.loadInt (s.regs.get64 .rbp + a) n = some (rd f (0xa0 - d) n) := by
  obtain ⟨_, ⟨_, hbp, hfl, _⟩, hm⟩ := h
  have e : s.regs.get64 .rbp + a = rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 (0xa0 - d) := by
    rw [hbp, show a = BitVec.ofNat 64 (2 ^ 64 - d) from BitVec.eq_of_toNat_eq (by simp [ha]; omega)]
    exact fr_addr _ d h1 h2
  rw [e]; exact Fr_f_load hm hfl _ n hn

theorem t1L_fl {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64}
    {t₀ : MachineData} {f c : List UInt8} {i : BitVec 32} (h : m =⋆ Fr k Ext x ra t₀ f c i)
    (hf : f.length = 0x78) (r : BitVec 64) (hbp : r = rsp0 t₀ - 8#64)
    (a : BitVec 64) (d n : Nat) (ha : a.toNat = 2 ^ 64 - d) (h1 : 8 < d) (h2 : d ≤ 0xa0)
    (hn : 0xa0 - d + n ≤ 0x78) :
    m.loadInt (r + a) n = some (rd f (0xa0 - d) n) := by
  rw [hbp, show a = BitVec.ofNat 64 (2 ^ 64 - d) from BitVec.eq_of_toNat_eq (by simp [ha]; omega),
    fr_addr _ d h1 h2]
  exact Fr_f_load h hf _ n hn

theorem t1L_B_mk {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64} {t₀ s s' : MachineData}
    {c f : List UInt8} {N : Nat} (h : Cm k Ext x ra t₀ s c f) (hI : Ix x (s.regs.get64 .r8))
    (hN : N ≤ 4) (h40 : rd f 0x40 8 = N) (h68 : BitVec.ofInt 64 (rd f 0x68 8) = arg2 t₀) (v : Int)
    (hm : s'.dmem = s.dmem.storeInt (arg2 t₀ + BitVec.ofNat 64 48) 4 v)
    (hsp : s'.regs.get64 .rsp = s.regs.get64 .rsp) (hbp : s'.regs.get64 .rbp = s.regs.get64 .rbp)
    (h8 : s'.regs.get64 .r8 = s.regs.get64 .r8)
    (h15 : (s'.regs.get64 .r15).setWidth 32 = bitsLeft t₀) :
    T1B k Ext x ra t₀ s' (wr c 48 4 v) f N := by
  obtain ⟨hC, ⟨a1, a2, a3, a4, a5, a6, a7⟩, hM⟩ := h
  exact ⟨⟨hC, ⟨by rw [hsp]; exact a1, by rw [hbp]; exact a2, a3,
    t1_PsInv_wr 48 4 v a4 (by omega) (by omega), a5, a6, a7⟩,
    by rw [hm]; exact Fr_c_store hM a4.1 48 4 (by omega) v⟩,
    by rw [h8]; exact hI, h15, hN, h40, h68⟩

omit [CodeEnv] in
theorem t1L_W0 {c f : List UInt8} {N : Nat} (hl : c.length = 764) (hne : ne c = N)
    (h : Rng c ∧ Hdr c ∧ IidS c (rd f 0x18 4) ∧ IidB c (ne c) ∧ IidZ c) (v : Int) :
    T1W0 (wr c 48 4 v) f N := by
  obtain ⟨hR, ⟨_, h4, hb0, hmon, h31⟩, hS, hB, hZ⟩ := h
  rw [hne] at hB
  exact ⟨t1_Rng_wr 48 4 v hR hl (by omega) (Or.inl (by omega)) (by omega),
    t1_H_wr 48 4 v ⟨hb0, fun e he => hmon e (by omega), fun e he => h31 e (by omega)⟩ hl (by omega)
      (Or.inr (by omega)) (by omega),
    t1_IidS_wr 48 4 v hS hl (by omega) (by omega),
    t1_IidB_wr 48 4 v hB hl (by omega) (by omega) (Or.inr (by omega)) (by omega),
    t1_IidZ_wr 48 4 v hZ hl (by omega) (Or.inr (by omega)) (by omega)⟩

set_option maxRecDepth 20000 in
theorem blk_L1063 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L1063" := by
  cfg_block
  measure_hb "L1063"
    intro n
    simp only [tab_L1063, var_L1063, tab_L1084, var_L1084]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hCm, hbx, hI, ⟨⟨hn0, hn4, h58, h38⟩, h34, h68, h40⟩, h1c, h10, hW⟩, hn⟩ := hs₀
    obtain ⟨N, hNe⟩ : ∃ N : Nat, ne c = N := ⟨(ne c).toNat, by omega⟩
    have hl : c.length = 764 := hCm.2.1.2.2.2.1.1
    have hbl := hCm.2.1.2.2.2.2.1
    have hf : f.length = 0x78 := hCm.2.1.2.2.1
    have hbp := hCm.2.1.2.1
    have hM' := fun v => Fr_c_store hCm.2.2 hl 48 4 (by omega) v
    have L74 := t1L_fload hCm (18446744073709551572#64) 44 4 rfl (by omega) (by omega) (by omega)
    have L58 := fun v => t1L_fl (hM' v) hf _ hbp (18446744073709551544#64) 72 8 rfl (by omega) (by omega) (by omega)
    have L38 := fun v => t1L_fl (hM' v) hf _ hbp (18446744073709551512#64) 104 8 rfl (by omega) (by omega) (by omega)
    have L1c := fun v => t1L_fl (hM' v) hf _ hbp (18446744073709551484#64) 132 4 rfl (by omega) (by omega) (by omega)
    have L48 := Fr_c_load hCm.2.2 hl 48 4 (by omega)
    simp only [arg2] at L48 L58 L38 L1c
    have hN4 : N ≤ 4 := by omega
    have h40' : rd f 0x40 8 = N := by rw [h40, hNe]
    have h12 : BitVec.ofInt 64 (rd f 0x58 8) = BitVec.ofNat 64 N := by rw [h58, hNe]; simp
    have hne' : ∀ v, ne (wr c 48 4 v) = N := fun v => by
      simp (disch := omega) only [ne, i32_wr]; exact hNe
    have hI34 : ∀ v, BitVec.ofInt 32 (rd f 0x34 4) = BitVec.ofInt 32 (i32 (wr c 48 4 v) 4) := fun v => by
      simp (disch := omega) only [i32_wr]; exact h34
    have h9 : ∀ v, BitVec.ofInt 64 (rd f 0x38 8) = BitVec.ofInt 64 (i32 (wr c 48 4 v) 40) := fun v => by
      simp (disch := omega) only [i32_wr]; exact h38
    have hz0 : s₀.regs.get64 .r10 &&& s₀.regs.get64 .r10 = 0#64 ↔ N = 0 := by
      rw [BitVec.and_self]
      constructor
      · intro h; rw [h] at h10; simp at h10; omega
      · intro h; apply BitVec.eq_of_toNat_eq; rw [h10, hNe, h]; rfl
    clear h58 h34 h38 h40
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals t1norm
    all_goals try simp only [hbx, L74, L48, L58, L38, L1c, Option.isSome_some]
    all_goals try (rename_i v15 e15 v48 _ _ v12 v9 v13 e48 e12 e9 e13 hz
                   t1norm at hbx e15 e48 e12 e9 e13 hz
                   simp only [hbx, L74, L48, L58, L38, L1c, Option.some.injEq] at e15 e48 e12 e9 e13
                   subst e15 e48 e12 e9 e13)
    case vc7 =>
      have hN0 : N = 0 := hz0.mp (by
        simp only [CondCode.interp_z, StatusFlags.zf_from_result, beq_iff_eq] at hz; exact hz)
      subst hN0
      t1_jump "ff_ps_read_data.L10f6"
      exact ⟨_, f, t1L_B_mk hCm hI hN4 h40' h68 _ rfl (by t1r) (by t1r) (by t1r)
          (by t1r; simp only [BitVec.setWidth_32_64_32]; exact hbl),
        ⟨hne' _, by t1r; exact h12⟩, by t1r; exact hbx, by t1r; exact h9 _, hI34 _,
        fun hp => t1L_W0 hl hNe (hW hp) _⟩
    case vc8 =>
      have hN1 : N ≠ 0 := fun h => by
        have := hz0.mpr h
        simp only [CondCode.interp_z, StatusFlags.zf_from_result, this] at hz
        exact absurd hz (by decide)
      exact ⟨⟨_, f, N, t1L_B_mk hCm hI hN4 h40' h68 _ rfl (by t1r) (by t1r) (by t1r)
          (by t1r; simp only [BitVec.setWidth_32_64_32]; exact hbl),
        ⟨hne' _, by t1r; exact h12⟩, by omega, by t1r; exact hbx, hI34 _,
        fun hp => t1L_W0 hl hNe (hW hp) _⟩, by var_step⟩

end Kraken.Examples.Sbr.Ps
