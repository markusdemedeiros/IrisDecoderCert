import Kraken.X64.Examples.Sbr.Parse.PsBlkT2Lib

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Ps

theorem t2_WF {c c' f : List UInt8} (h : T1W2 c f) (hP : PsInv c) (hl : c'.length = 764)
    (h4 : ∀ o, 4 ≤ o → i32 c' o = i32 c o) (h8 : ∀ j, 4 ≤ j → i8 c' j = i8 c j)
    (hn : i32 c' 0 ≠ 0 → i32 c 4 ≠ 0 → i32 c 12 = 10 ∨ i32 c 12 = 20 ∨ i32 c 12 = 34) :
    PsWFb c' := by
  obtain ⟨⟨r1, r2, r3, r4⟩, -, f1, f2, f3, f4, f5, f6⟩ := h
  obtain ⟨-, -, -, -, p5, -, -⟩ := hP
  simp only [PsWFb]
  simp (disch := omega) only [h4, h8]
  simp only [ne, bord] at f1 f2 f3 f4 f5 f6
  refine ⟨hl, r1, ⟨by omega, f2⟩, p5, r2, r3, r4, fun hs => ⟨f1, f3, f4, f5, hn hs, f6⟩⟩


theorem t2_PsInv_wr0b {c : List UInt8} (h : PsInv c) (v : Int) : PsInv (wr c 0 4 v) := by
  obtain ⟨hl, h1, h2, h3, h4, h5, h6⟩ := h
  have hL : 0 + 4 ≤ c.length := by omega
  refine ⟨by rw [wr_length _ _ _ _ hL, hl], ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := omega) only [i32_wr] <;> assumption

theorem t2_hdr (v : Int) (h : ¬((BitVec.ofInt 32 v - BitVec.setWidth 32 0#64) == 0#32) = true) :
    v ≠ 0 := by
  rintro rfl; exact h (by decide)

variable [CodeEnv]

theorem t2_Cm_st0b {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64}
    {t₀ s : MachineData} {c f : List UInt8} (h : Cm k Ext x ra t₀ s c f) (v : Int)
    (s' : MachineData) (hm : s'.dmem = s.dmem.storeInt (arg2 t₀) 4 v)
    (hsp : s'.regs.get64 .rsp = s.regs.get64 .rsp) (hbp : s'.regs.get64 .rbp = s.regs.get64 .rbp) :
    Cm k Ext x ra t₀ s' (wr c 0 4 v) f := by
  obtain ⟨hC, ⟨a1, a2, a3, a4, a5⟩, hM⟩ := h
  refine ⟨hC, ⟨by rw [hsp]; exact a1, by rw [hbp]; exact a2, a3, t2_PsInv_wr0b a4 v, a5⟩, ?_⟩
  have := Fr_c_store hM a4.1 0 4 (by omega) v
  simp only [BitVec.add_zero] at this
  rw [hm]; exact this

open scoped Kraken.Rules.GenericMem.Norm

set_option maxRecDepth 20000 in
/-- `start = 1` when a header was read. -/
theorem blk_L13f5 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L13f5" := by
  cfg_block
  measure_hb "L13f5"
    intro n
    simp only [tab_L13f5, var_L13f5, tab_L1404, var_L1404]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, N, ⟨hC, hix, h15, -⟩, hbx, hW⟩, hn⟩ := hs₀
    have hl : c.length = 764 := hC.2.1.2.2.2.1.1
    have L := t2_fload hC (18446744073709551480#64) 0x88 4 rfl (by omega) (by omega) (by omega)
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals t1norm at *
    · rw [L]; rfl
    · simp only [L, Option.some.injEq] at *
      subst_vars
      t1_jump "ff_ps_read_data.L1404"
      show q1404 _ _ _ _ _ _
      exact ⟨c, f, ⟨t2_C_eq hC rfl rfl rfl, h15, fun hw => t2_WF (hW hw) hC.2.1.2.2.2.1 hl
        (fun _ _ => rfl) (fun _ _ => rfl) (fun h0 => (hW hw).2.1 (Or.inl h0))⟩, hix, hbx⟩
    · rw [hbx]
      have h0 := Fr_c_isSome hC.2.2 hl 0 4 (by omega)
      simp only [BitVec.add_zero, arg2] at h0
      exact h0
    · simp only [L, Option.some.injEq] at *
      subst_vars
      have hz := ‹CondCode.z.interp _ = false›
      simp only [t1_z, t1_zf] at hz
      have hd := t2_hdr _ (by rw [hz]; decide)
      have hP := hC.2.1.2.2.2.1
      have hL : 0 + 4 ≤ c.length := by omega
      refine ⟨⟨wr c 0 4 (BitVec.setWidth 32 1#64).toInt, f, ⟨t2_Cm_st0b hC _ _ (by simp only [hbx]) rfl rfl, h15,
        fun hw => t2_WF (hW hw) hP (by rw [wr_length _ _ _ _ hL, hl])
          (fun o ho => i32_wr c 0 4 o _ hL (Or.inr ho))
          (fun j hj => i8_wr c 0 4 j _ hL (Or.inr hj))
          (fun _ h4 => (hW hw).2.1 (Or.inr hd) h4)⟩, hix, hbx⟩, by var_step⟩

end Kraken.Examples.Sbr.Ps
