import Kraken.InfoOff
import Kraken.X64.Examples.Sbr.Parse.ResetELib
import Kraken.X64.Examples.Sbr.Parse.ResetE2
import Kraken.X64.Examples.Sbr.Parse.ResetA1Mem

/-!
# `sbr_reset`: `sbr_make_f_derived`, the `f_tablelow` copy (`derived2`): the `vpshufb` masks
(shard B, env)
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

section Specs

open Lean.Order

variable [CodeEnv] {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}
  {p : Program}

local macro "wp_step" : tactic =>
  `(tactic| simp only [Executable.stepAt, Directive.interp, Instr.interp,
      Operation.interp, AvxOperation.interp, Operand.interp, RegOrMem.interp,
      AvxRegOrMem.interp, AvxRegOrMem.interpLow, RelRegOrMem.interp, ConstExpr.interp,
      MachineData.set, MachineData.setReg, MachineData.setAvxLegacy, MachineData.setAvxLegacyReg,
      MachineData.setAvx, MachineData.setAvxReg,
      Reg64s.get_low64, Reg64s.set_low64, Effects.All, or_false, false_or])

local macro "mem_access" hal:ident hv:ident : tactic =>
  `(tactic| simp only [MachineData.loadAvx, MachineData.storeAvx, MachineData.load,
      MachineData.store, AddrExpr.zeroExtend_interp_base_idx_disp,
      AddrExpr.zeroExtend_interp_rip_label, AddrExpr.zeroExtend_interp_rip_label_add,
      $hal:ident, $hv:ident, AvxWidth.bytes, Width.bytes,
      Bool.not_true, Bool.and_false, Bool.false_and, Bool.false_eq_true, ite_false,
      Effects.All])

local macro "mem_load_al" : tactic =>
  `(tactic| (
    refine Triple.intro fun s h => ?_
    simp only [meet_prop_eq_and] at h
    obtain ⟨⟨hal, hsome⟩, hk⟩ := h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    rw [after_instr hseg]
    refine step_here hseg (Or.inl ?_)
    wp_step
    mem_access hal hv
    exact hk v hv _ hpl'))

/-- `vmovdqa sym(%rip), %xmm`: 16 readable bytes, 16-byte aligned. -/
@[spec low] theorem MachineWP.rsE_vmovdqa_load_rip_spec (x : AvxReg .W128) (l : Label) :
    ⦃ fun s =>
        let a := ((_root_.Executable.labels cenv).label l).toBitVec
        (isAligned 16 a = true) ⊓ ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set x (BitVec.ofInt 128 v) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vmovdqa (.avx x) (.mem ⟨some .rip, none, .sub (.label l) .after_current_instruction⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load_al

local macro "mem_rule" : tactic =>
  `(tactic| (
    refine Triple.intro fun s h => ?_
    simp only [meet_prop_eq_and] at h
    obtain ⟨hsome, hk⟩ := h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    rw [after_instr hseg]
    refine step_here hseg (Or.inl ?_)
    wp_step
    simp only [AvxRegOrMem.interpLow, MachineData.load, MachineData.store,
      AddrExpr.zeroExtend_interp_base_idx_disp, AddrExpr.zeroExtend_interp_rip_label,
      AddrExpr.zeroExtend_interp_rip_label_add,
      Width.bytes, hv, Effects.All]
    first
      | exact hk v hv _ hpl'
      | exact hk _ hpl'))

/-- `vmovq sym(%rip), %xmm`: 8 readable bytes, zero-extended into the register. -/
@[spec low] theorem MachineWP.rsE_vmovq_to_load_rip_spec (dst : AvxReg .W128) (l : Label) :
    ⦃ fun s =>
        let a := ((_root_.Executable.labels cenv).label l).toBitVec
        ((Mem.loadInt s.dmem a 8).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 8 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set dst ((BitVec.ofInt 64 v).zeroExtend 128) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vmovqTo dst (RegOrMem.mem ⟨some .rip, none, .sub (.label l) .after_current_instruction⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_rule

end Specs

namespace Kraken.Examples.Sbr.Reset

variable [CodeEnv]

set_option maxRecDepth 100000 in
/-- The 16-wide loop's entry: `rdi = 0`, `xmm0 = .LCPI5_6`. -/
theorem blk_L2a26 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2a26" ⟨"sbr_reset.L2a26", B.L2a26, some "sbr_reset.L2a30"⟩ := by
  info_off
  measure_hb "L2a26"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hC, ⟨hrsp, hrbp⟩, st, fr, nm, k0, hMa, hsp, hfm, hF, h40,
      ⟨hk2, hf64, hbr, h30, h38, m, hx, h14, h15, h10, hcx, rfl, h17, h13, h8, hsi, h9, hdx, hax⟩, hm⟩ := T.L2a26.mp hs
    clear hs
    obtain ⟨hxo, hnm, -, -⟩ := master_bounds hMa
    have hxo' : xoOf a < nm := hxo
    have h17' : 17 ≤ (nm - xoOf a + 1) / 2 := h17
    have hlt0 : 0 < (nm - xoOf a + 1) / 2 - R16 ((nm - xoOf a + 1) / 2) := by
      simp only [R16]; split <;> omega
    have hcst : s₀.dmem.loadInt (lab "LCPI5_6") 16
        = some (Int.ofBytes (Int.toBytes 16 (0x0f0e0d0c0d0c09080d0c090805040100 : Int))) := by
      have h := focus (Mm_cst ..) hm
      simp only [CstR] at h
      obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_lr h
      obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_lr h
      obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_lr h
      obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_lr h
      obtain ⟨F, h⟩ := a1_pick_ll h
      have := region_load (o := 0) (n := 16) (addr := lab "LCPI5_6") h (by simp) (by simp [Int.toBytes_length])
        (by simp [Int.toBytes_length])
      rw [this]; rfl
    have hval : BitVec.ofInt 128 (Int.ofBytes (Int.toBytes 16 (0x0f0e0d0c0d0c09080d0c090805040100 : Int)))
        = C56 := by
      rw [ofBytes_toBytes]; rfl
    have hal : isAligned 16 (lab "LCPI5_6") = true := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have P30 : PLift (frSlot64 fr 0x30 = arg1 t₀) := ⟨h30⟩
    have Px := PLift.up hx
    have Pm := PLift.up hm
    clear h30 hx hm
    simp only [B.L2a26]
    vcgen
    all_goals try subst_vars
    case vc1 => exact hal
    case vc2 => exact (congrArg Option.isSome hcst).trans rfl
    case vc3 =>
      rename_i _ v hl
      have hl := hl.symm.trans hcst
      simp only [Option.some.injEq] at hl
      subst hl
      refine ⟨T.L2a30.mpr ⟨hC, ⟨by rsE_rs; exact hrsp, by rsE_rs; exact hrbp⟩, st, fr, nm, k0, hMa, hsp,
        hfm, hF, h40, ⟨hk2, hf64, hbr, P30.down, h38, 0, Px.down, by rsE_rs; exact h14, by rsE_rs; exact h15, by rsE_rs; exact h10, by rsE_rs; exact hcx,
        h17, by rsE_rs; exact h13, by rsE_rs; exact h8, by rsE_rs; exact hsi, by rsE_rs; exact h9,
        by rsE_rs; exact hdx, by rsE_rs; exact hax, Nat.zero_mod 16, hlt0,
        by rsE_rs; exact rsE_xor_self _, by rw [RegZmms.get_set_xmm_same]; exact hval⟩, Pm.down⟩,
        by var_step⟩


omit [CodeEnv] in
theorem rsE_rsi4 (x : BitVec 64) (m : Nat) (hm : m < 2 ^ 32) :
    311892#64 + (x + BitVec.ofNat 64 (2 * m)) = x + BitVec.ofNat 64 (0x4c254 + 2 * m) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

omit [CodeEnv] in
theorem rsE_r84 (x : BitVec 64) (m p : Nat) (hm : m < 2 ^ 32) (hp : p < 2) :
    311944#64 + (x + BitVec.ofNat 64 m * 4#64 + 0#64
      - BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 p * 2#64 + 0#64)))
      = x + BitVec.ofNat 64 (0x4c288 + 4 * m - 2 * p) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat]; omega

set_option maxRecDepth 100000 in
/-- The 4-wide loop's entry: `xmm0 = .LCPI5_9`, the pointers at entry `m`. -/
theorem blk_L2aaf (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2aaf" ⟨"sbr_reset.L2aaf", B.L2aaf, some "sbr_reset.L2ad6"⟩ := by
  info_off
  measure_hb "L2aaf"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hC, ⟨hrsp, hrbp⟩, st, fr, nm, k0, hMa, hsp, hfm, hF, h40,
      ⟨hk2, hf64, hbr, h30, h38, m, hx, h14, h15, h10, hcx, h13, h16, h5, h9, h8, hsi, hdx, hax⟩, hm⟩ := T.L2aaf.mp hs
    clear hs
    obtain ⟨hxo, hnm, -, -⟩ := master_bounds hMa
    have hxo' : xoOf a < nm := hxo
    have h5' : m + 5 ≤ (nm - xoOf a + 1) / 2 := h5
    have hlt0 : m + 0 < (nm - xoOf a + 1) / 2 - R4 ((nm - xoOf a + 1) / 2) := by
      simp only [R4]; split <;> omega
    have hm4 : m % 4 = 0 := by omega
    have hm32 : m < 2 ^ 32 := by omega
    have hp : (nm - xoOf a) % 2 < 2 := Nat.mod_lt _ (by omega)
    have hcst : s₀.dmem.loadInt (lab "LCPI5_9") 8
        = some (Int.ofBytes (slice (Int.toBytes 16 (0x0d0c090805040100 : Int)) 0 8)) := by
      have h := focus (Mm_cst ..) hm
      simp only [CstR] at h
      obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_lr h
      obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_lr h
      obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_lr h
      obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_lr h
      obtain ⟨F, h⟩ := a1_pick_lr h
      exact region_load (o := 0) (n := 8) (addr := lab "LCPI5_9") h (by simp)
        (by simp [Int.toBytes_length]) (by simp [Int.toBytes_length])
    have hval : (BitVec.ofInt 64 (Int.ofBytes (slice (Int.toBytes 16 (0x0d0c090805040100 : Int)) 0 8))).zeroExtend 128
        = C59 := by rfl
    have P30 : PLift (frSlot64 fr 0x30 = arg1 t₀) := ⟨h30⟩
    have Px := PLift.up hx
    have Pm := PLift.up hm
    clear h30 hx hm
    have hW4 : BitVec.ofNat 64 Width.W32.bytes = 4#64 := rfl
    have hW2 : BitVec.ofNat 64 Width.W16.bytes = 2#64 := rfl
    simp only [B.L2aaf]
    vcgen
    all_goals try subst_vars
    case vc1 => exact (congrArg Option.isSome hcst).trans rfl
    case vc2 =>
      rename_i _ v hl
      have hl := hl.symm.trans hcst
      simp only [Option.some.injEq] at hl
      subst hl
      simp only [Int64.toBitVec_ofNat_norm, BitVec.reduceSetWidth, AddrIndex.offset64,
        Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hW4, hW2]
      refine ⟨T.L2ad6.mpr ⟨hC, ⟨by rsE_rs; exact hrsp, by rsE_rs; exact hrbp⟩, st, fr, nm, k0, hMa, hsp,
        hfm, hF, h40, ⟨hk2, hf64, hbr, P30.down, h38, m, Px.down, by rsE_rs; exact h14, by rsE_rs; exact h15, by rsE_rs; exact h10, by rsE_rs; exact hcx,
        by rsE_rs; exact h13, m, 0, rfl, hm4, Nat.zero_mod 4, hlt0, by rsE_rs; exact rsE_xor_self _, by rsE_rs; exact hdx,
        by rsE_rs; exact hax, by rsE_rs; rw [hsi]; exact rsE_rsi4 _ _ hm32,
        by rsE_rs; rw [h8, h9, h13]; exact rsE_r84 _ _ _ hm32 hp,
        by rw [RegZmms.get_set_xmm_same]; exact hval⟩, Pm.down⟩, by var_step⟩

end Kraken.Examples.Sbr.Reset
