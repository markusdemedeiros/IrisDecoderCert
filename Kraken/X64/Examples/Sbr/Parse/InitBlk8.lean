import Kraken.X64.Examples.Sbr.Parse.InitEnd

/-!
# `ff_aac_sbr_ctx_alloc_init`: the result `-12`, the epilogue and the return
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr
open Kraken.Examples.Sbr.Apply (c8)

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Init

variable [CodeEnv]

theorem blk_L17a (k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (TxTab X : Mem 64 → Prop)
    (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ctx TxTab X R ra t₀ "ff_aac_sbr_ctx_alloc_init.L17a" := by
  cfg_block
  measure_hb "L17a"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hR, hm⟩, hn⟩ := hs₀
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    exact ⟨⟨hR, Or.inr (Or.inl ⟨by decide, hm⟩)⟩, Nat.le_refl 0⟩

omit [CodeEnv] in
theorem pop_sp (r : BitVec 64) : r - 56#64 + 24#64 = r - 0x20#64 ∧ r - 0x20#64 + 8#64 = r - 0x18#64
    ∧ r - 0x18#64 + 8#64 = r - 0x10#64 ∧ r - 0x10#64 + 8#64 = r - 0x8#64
    ∧ r - 0x8#64 + 8#64 = r := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> bv_omega

theorem blk_L17f (k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (TxTab X : Mem 64 → Prop)
    (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ctx TxTab X R ra t₀ "ff_aac_sbr_ctx_alloc_init.L17f" := by
  cfg_block
  measure_hb "L17f"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hR, hO⟩, hn⟩ := hs₀
    obtain ⟨B, hm⟩ := Out_ex hO
    obtain ⟨p1, p2, p3, p4⟩ := M_pop hm
    have hF := Out_mono (fun _ h => M_forget h) hO
    clear hm
    obtain ⟨a1, a2, a3, a4, a5⟩ := pop_sp (t₀.regs.get64 .rsp)
    obtain ⟨hrsp, hrbp, h14, h15, h12, h13⟩ := hR
    have ad : BitVec.setWidth 64 (Int64.toBitVec 24) + s₀.regs.get64 .rsp
        = t₀.regs.get64 .rsp - 0x20#64 := by
      rw [hrsp, show BitVec.setWidth 64 (Int64.toBitVec 24) = 24#64 from rfl,
        BitVec.add_comm 24#64, a1]
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals simp only [ad, a2, a3, a4, a5, p1, p2, p3, p4, Option.isSome_some,
      Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at *
    exact ⟨⟨trivial, trivial, ⟨trivial, h12, h13, trivial, trivial⟩, hF⟩, Nat.le_refl 0⟩

theorem blk_done (k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (TxTab X : Mem 64 → Prop)
    (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ctx TxTab X R ra t₀ "ff_aac_sbr_ctx_alloc_init.done" := by
  cfg_block
  measure_hb "done"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hsp, hbp, hsv, hO⟩, hn⟩ := hs₀
    obtain ⟨B, hm⟩ := Out_ex hO
    rw [MF_ret] at hm
    have l0 : s₀.dmem.loadInt (t₀.regs.get64 .rsp) 8
        = some (Int.ofBytes (Int.toBytes 8 ra.toBitVec.toInt)) :=
      loadInt_sep _ _ 8 _ _ hm (Int.toBytes_length 8 _) (by omega)
    have hra : s₀.retAddr = some ra := by
      simp only [MachineData.retAddr, hsp, l0, Option.map_some,
        BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Int64.ofBitVec_toBitVec]
    have hpost : Out k Ctx TxTab t₀
        (fun B => 8 ?@ t₀.regs.get64 .rsp ⋆ MF k TxTab X t₀ (FrB t₀) B R) (eax s₀) s₀.dmem :=
      Out_mono (fun _ h => by
      rw [MF_ret] at h; exact Block.sep_intro (Int.toBytes_length _ _) (by decide) h) hO
    clear hm l0 hO
    vcgen
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals simp only [hra, Option.isSome_some, Option.some.injEq] at *
    subst_vars
    right
    refine ⟨rfl, ?_⟩
    exact ⟨by rw [hsp]; rfl, hbp, hsv, hpost⟩

end Kraken.Examples.Sbr.Init
