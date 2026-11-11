import Kraken.X64.Examples.Sbr.Parse.NoiseMem

/-!
# `read_sbr_noise`: the frame on the way out

The locals written to the locals raw (`T_blank`), the pushes at the head (`T_saved`, for the
pops), the return slot at the head (`T_ret`, for the `ret`), `Ext` at the head (`T_ext`, for
the `av_log` call).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply
open Kraken.Examples.Sbr.Dtdf (eq_r eq_l eq_h eq_last)

namespace Kraken.Examples.Sbr.Noise

variable [CodeEnv]

omit [CodeEnv] in
theorem blank1 {m : Mem 64} {a : BitVec 64} {v : BitVec 64} {Q : Mem 64 → Prop}
    (h : m =⋆ c8 a v ⋆ Q) : m =⋆ 8 ?@ a ⋆ Q :=
  Block.sep_intro (Int.toBytes_length _ _) (by decide) h

omit [CodeEnv] in
theorem blank4 {m : Mem 64} {a1 a2 a3 a4 v1 v2 v3 v4 : BitVec 64} {W : Mem 64 → Prop}
    (h : m =⋆ c8 a1 v1 ⋆ (c8 a2 v2 ⋆ (c8 a3 v3 ⋆ (c8 a4 v4 ⋆ W)))) :
    m =⋆ 8 ?@ a1 ⋆ (8 ?@ a2 ⋆ (8 ?@ a3 ⋆ (8 ?@ a4 ⋆ W))) := by
  have rot : ∀ A B C D : Mem 64 → Prop, (A ⋆ (B ⋆ (C ⋆ (D ⋆ W)))) = B ⋆ (C ⋆ (D ⋆ (A ⋆ W))) :=
    fun _ _ _ _ => by ac_rfl
  have h1 := blank1 h; rw [rot] at h1
  have h2 := blank1 h1; rw [rot] at h2
  have h3 := blank1 h2; rw [rot] at h3
  have h4 := blank1 h3; rw [rot] at h4
  exact h4

theorem T_blank {k : Nat} {Ext : Mem 64 → Prop} {x : NArgs} {ra : Int64} {t₀ : MachineData}
    {FR : (Mem 64 → Prop) → Mem 64 → Prop} {i : BitVec 32} {m : Mem 64}
    (h : m =⋆ T k Ext x ra t₀ (Loc x t₀) FR i) : m =⋆ T k Ext x ra t₀ (Blank t₀) FR i := by
  have e1 : T k Ext x ra t₀ (Loc x t₀) FR i = c8 (t₀.regs.get64 .rsp - 0x58#64) (arg3 t₀)
      ⋆ (c8 (t₀.regs.get64 .rsp - 0x50#64) (arg3 t₀ + 0x15a50#64)
      ⋆ (c8 (t₀.regs.get64 .rsp - 0x48#64) (arg0 t₀)
      ⋆ (c8 (t₀.regs.get64 .rsp - 0x40#64) (TH x t₀).p ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x38#64)
      ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x60#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x60#64)
      ⋆ (NoiseF Ext x t₀ i ⋆ FR (Rest x.R ra t₀)))))))) := by
    simp only [T, Loc]; ac_rfl
  have e2 : T k Ext x ra t₀ (Blank t₀) FR i = 8 ?@ (t₀.regs.get64 .rsp - 0x58#64)
      ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x50#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x48#64)
      ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x40#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x38#64)
      ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x60#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x60#64)
      ⋆ (NoiseF Ext x t₀ i ⋆ FR (Rest x.R ra t₀)))))))) := by
    simp only [T, Blank]; ac_rfl
  rw [e1] at h
  rw [e2]
  exact blank4 h

theorem T_ext (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ : MachineData)
    (LF : Mem 64 → Prop) (FR : (Mem 64 → Prop) → Mem 64 → Prop) (i : BitVec 32) :
    ∃ F, T k Ext x ra t₀ LF FR i = 8 ?@ (t₀.regs.get64 .rsp - 0x60#64)
      ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x60#64) ⋆ (Ext ⋆ F)) :=
  ⟨_, congrArg (8 ?@ (t₀.regs.get64 .rsp - 0x60#64) ⋆ ·)
    (congrArg (Reserve k (t₀.regs.get64 .rsp - 0x60#64) ⋆ ·)
      (eq_r (eq_l (eq_r (eq_r (eq_r (eq_r (eq_r (eq_r (eq_r (eq_r eq_last)))))))))))⟩

theorem T_saved (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ : MachineData)
    (LF : Mem 64 → Prop) (i : BitVec 32) :
    T k Ext x ra t₀ LF (Saved t₀) i = Saved t₀ (8 ?@ (t₀.regs.get64 .rsp - 0x60#64)
      ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x60#64) ⋆ (LF ⋆ (NoiseF Ext x t₀ i
      ⋆ Rest x.R ra t₀)))) := by
  simp only [T, Saved]; ac_rfl

theorem T_ret (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ : MachineData)
    (LF : Mem 64 → Prop) (i : BitVec 32) :
    T k Ext x ra t₀ LF (Saved t₀) i = RetCell ra (t₀.regs.get64 .rsp)
      ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x60#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x60#64)
      ⋆ (LF ⋆ (NoiseF Ext x t₀ i ⋆ Saved t₀ x.R)))) := by
  simp only [T, Saved, Rest]; ac_rfl

theorem Post_mem (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (t₀ : MachineData)
    (i : BitVec 32) :
    (8 ?@ (t₀.regs.get64 .rsp - 0x60#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x60#64)
      ⋆ (Blank t₀ ⋆ (NoiseF Ext x t₀ i ⋆ Saved t₀ (8 ?@ t₀.regs.get64 .rsp ⋆ x.R)))))
    = 8 ?@ t₀.regs.get64 .rsp ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x60#64)
      ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x60#64) ⋆ (Blank t₀ ⋆ (NoiseF Ext x t₀ i
      ⋆ Saved t₀ x.R)))) := by
  simp only [Saved]; ac_rfl

omit [CodeEnv] in
theorem pop_offs (t : BitVec 64) : BitVec.setWidth 64 40#64 + (t - 88#64) = t - 48#64
    ∧ t - 48#64 + 8#64 = t - 40#64 ∧ t - 40#64 + 8#64 = t - 32#64
    ∧ t - 32#64 + 8#64 = t - 24#64 ∧ t - 24#64 + 8#64 = t - 16#64
    ∧ t - 16#64 + 8#64 = t - 8#64 ∧ t - 8#64 + 8#64 = t := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_omega

end Kraken.Examples.Sbr.Noise
