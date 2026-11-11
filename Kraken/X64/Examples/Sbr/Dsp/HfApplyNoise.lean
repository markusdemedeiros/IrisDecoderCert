import Kraken.X64.Parser
import Kraken.MachineWP
import Kraken.Rules.PackedSse
import Kraken.Rules.IntMisc
import Kraken.X64.Examples.Sbr.Spec
import Kraken.Rules.LeafLemmas
import Kraken.X64.Examples.Sbr.Dsp.HfApplyNoiseText

/-!
# `ff_sbr_hf_apply_noise_{0,1,2,3}_sse2` as `ProcSpec`s

`hf_apply_noise[k](Y, s_m, q_filt, noise, kx, m_max)` adds, for
`m < m_max`, either the sinusoid `s_m[m] * phi_sign[k]` or the noise
`q_filt[m] * ff_sbr_noise_table[(noise + m + 1) & 0x1ff]` to `Y[m]`
(`libavcodec/x86/sbrdsp.asm`, macro `SBR_HF_APPLY_NOISE`; C reference
`libavcodec/sbrdsp_template.c`; call site `libavcodec/aacsbr.c`). The four
entries load their `phi_sign` constant into `xmm0` and share the loop
`apply_noise_main`: entries 0, 1, 2 end in `jmp apply_noise_main`, entry 3
falls through into it. `spec` proves `HfApplyNoiseSpec` (all four slots)
from the placement of the whole text; `main_spec` proves the shared tail as
a `LeafSpec` of its own, which `spec0/1/2` reuse at the jump (`tail`), and
`spec3` reruns its blocks after the entry.

## Contract (`HfApplyNoiseF`, `HfApplyNoiseC`)

* Owned: `32 * ⌈m_max/4⌉` bytes of `Y`, `16 * ⌈m_max/4⌉` of `s_m` and of
  `q_filt` (read), 4160 bytes of `ff_sbr_noise_table` (read), and the
  entry's constant (16 bytes of `ps_noise0`/`ps_noise2`, 32 of
  `ps_noise13` for entries 1 and 3). Reservation 0, no callee-saved register
  touched.
* Needs: `s_m`, `q_filt` and the constant 16-aligned (`movdqa`
  loads; `Y` and the table are accessed with `movdqu`);
  `1 ≤ m_max < 2^28`; `noise ≤ 515` (as 32-bit).

## Notes

* `ff_sbr_noise_table` is 520 entries on x86 (512 plus the first 8
  repeated, `sbrdsp_template.c`), 4160 bytes, not 4096: the loop masks the
  index (to at most 511) after the first iteration but reads entries
  past it, up to byte 4136.
  Dropping it to 4096 makes the loop blocks fail (negative check, scratch).
* The first iteration is unmasked: the prologue computes `8 * (noise - 1)`,
  so `noise` must be at most 515. The caller passes `noise & 0x1ff`, fine.
* The loop is a do-while over four elements: it runs once for
  `m_max = 0` and touches `⌈m_max/4⌉ * 4` elements (beyond `Y[m_max]`
  when `m_max % 4 ≠ 0`). The footprint states this, and `m_max ≥ 1` is
  required.
* `kx` needs no condition: entries 1 and 3 use `kx & 1` only.
* Linking: the alignment padding between the entries is part of the text
  (dead `nop`s behind each `jmp apply_noise_main`), so `PlacedIn body` holds of
  the object's layout; without it the entry blocks would end short of the next
  entry's address.
* Entry 3 loads from `ps_noise13+16(%rip)` (parsed as the label plus 16,
  `MachineWP.lea_rip_label_add_spec`). `ps_noise13` is 48 bytes: entry 1 reads
  `[ps_noise13, +32)`, entry 3 `[ps_noise13+16, +48)`, so entry 3's constant
  block is the 32 bytes at `ps_noise13 + 16` (16-aligned when `ps_noise13`
  is).
* Proof shape: the loop is split at labels (`.b` after the index mask,
  `.c` before the `Y` loads, `.d` before `add/jl`), so each block is small.
  Address matching works when the invariant states `(p - base).toNat = j`
  with `p` the operand's exact address prefix (`rdx + r9`, `rdi + r9*2`).
  The `add $0x10,%r9; jl` block times out in `grind` (4M heartbeats) and is
  closed by hand: `CondCode.interp_l_add` turns the `jl` flags into unsigned
  arithmetic, then `omega`.
* Rules found missing: `CondCode.interp_l_add` (`jl` after `add`),
  `BitVec.toNat_and_le_right` and `Program.PlacedIn.of_subBlocksOf` are in
  `Kraken/Rules/LeafLemmas.lean`; `shl2_toNat`, `sext_small`, `kx_off_toNat`,
  `noise_init` are specific to this routine and stay here.
* Rule-file `grind` scopes opened (see `Kraken/Rules/*.lean`):
  `Kraken.Rules.GenericMem.Norm`, `Kraken.Rules.IntMisc.SubReg`.
-/

open Kraken.X64.Parser
open Kraken
open Kraken.SysV
open Std.WP
open Mem
open MachineWP
open scoped Kraken.LeafLemmas.Mask Kraken.LeafLemmas.AddFlags
open scoped Kraken.Rules.GenericMem.Norm Kraken.Rules.IntMisc.SubReg

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.HfApplyNoise

/-- `shl $2,%r32` of the low half of a register, zero-extended. -/
theorem shl2_toNat (x : BitVec 64) :
    ((x.setWidth 32 <<< 2).setWidth 64).toNat = x.toNat % 2 ^ 32 * 4 % 2 ^ 32 := by
  simp [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, Nat.shiftLeft_eq]
  omega

grind_pattern shl2_toNat => ((x.setWidth 32 <<< 2).setWidth 64).toNat

/-- `movslq` of a non-negative 32-bit value is its zero extension. -/
theorem sext_small (x : BitVec 64) (h : x.toNat % 2 ^ 32 < 2 ^ 31) :
    BitVec.signExtend 64 (x.setWidth 32) = BitVec.ofNat 64 (x.toNat % 2 ^ 32) := by
  rw [BitVec.signExtend_eq_setWidth_of_msb_false]
  · apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]
  · rw [BitVec.msb_eq_decide]; simp [BitVec.toNat_setWidth]; omega

/-- The noise offset the prologue computes, `8 * (noise - 1)`, for
`0 ≤ noise ≤ 515`: at most `4112`, or `-8` when `noise = 0`. -/
theorem noise_init (x : BitVec 64) (h : x.toNat % 2 ^ 32 ≤ 515) :
    ((BitVec.signExtend 64 (x.setWidth 32) - 1) <<< 3).toNat ≤ 4112
      ∨ (BitVec.signExtend 64 (x.setWidth 32) - 1) <<< 3 + 8 = 0 := by
  rw [sext_small x (by omega)]
  generalize hn : x.toNat % 2 ^ 32 = n at h
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · right; decide
  · left; simp [BitVec.toNat_sub]; omega

/-- `(x & 1) << 4`, the offset entries 1 and 3 add to their constant: 0 or 16. -/
theorem kx_off_toNat (x : BitVec 64) : ((x &&& 1#64) <<< 4).toNat = 16 * (x.toNat % 2) := by
  simp [BitVec.toNat_shiftLeft, BitVec.toNat_and, Nat.shiftLeft_eq]
  omega

grind_pattern kx_off_toNat => ((x &&& 1#64) <<< 4).toNat

variable [CodeEnv]

def Rest (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) : Mem 64 → Prop :=
  RetCell ra (t₀.regs.get64 .rsp) ⋆ (Reserve 0 (t₀.regs.get64 .rsp) ⋆ R)

/-- `4 * m_max` in bytes, as the prologue computes it. -/
abbrev B (t : MachineData) : BitVec 64 := ((arg5 t).setWidth 32 <<< 2).setWidth 64

/-- The loop invariant, without `rcx`: `j = r9 + 4 m_max` bytes into `s_m`
and `q_filt` (twice that into `Y`), a multiple of 16 below `4 m_max`. -/
abbrev inv (R : Mem 64 → Prop) (ra : Int64) (t₀ s : MachineData) : Prop :=
  let j := (s.regs.get64 .r9 + B t₀).toNat
  HfApplyNoiseMainC t₀
  ∧ s.regs.get64 .rdi = arg0 t₀ + B t₀ + B t₀
  ∧ s.regs.get64 .rsi = arg1 t₀ + B t₀
  ∧ s.regs.get64 .rdx = arg2 t₀ + B t₀
  ∧ s.regs.get64 .rax = lab "ff_sbr_noise_table"
  ∧ (s.regs.get64 .rdx + s.regs.get64 .r9 - arg2 t₀).toNat = j
  ∧ (s.regs.get64 .rsi + s.regs.get64 .r9 - arg1 t₀).toNat = j
  ∧ (s.regs.get64 .rdi + s.regs.get64 .r9 * 2 - arg0 t₀).toNat = 2 * j
  ∧ j % 16 = 0 ∧ j < 4 * HfApplyNoiseM t₀
  ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp
  ∧ SavedRegs t₀ s
  ∧ (s.dmem =⋆ HfApplyNoiseMainF t₀ ⋆ Rest R ra t₀)

/-- `s` agrees with `t₀` on the argument registers `apply_noise_main` reads
and on the convention's registers. -/
abbrev Agree (t₀ s : MachineData) : Prop :=
  s.regs.get64 .rdi = t₀.regs.get64 .rdi ∧ s.regs.get64 .rsi = t₀.regs.get64 .rsi
  ∧ s.regs.get64 .rdx = t₀.regs.get64 .rdx ∧ s.regs.get64 .rcx = t₀.regs.get64 .rcx
  ∧ s.regs.get64 .r9 = t₀.regs.get64 .r9
  ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp
  ∧ SavedRegs t₀ s

/-- The assertions of `apply_noise_main`, for the entry state `t₀` (whose
registers the state at `apply_noise_main` agrees with) and the caller's
memory `R`. -/
abbrev tableMain (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) :
    Label → MachineData → Prop
  | "apply_noise_main", s => Agree t₀ s ∧ HfApplyNoiseMainC t₀
      ∧ (s.dmem =⋆ HfApplyNoiseMainF t₀ ⋆ Rest R ra t₀)
  | "apply_noise_main.loop", s => inv R ra t₀ s
      ∧ ((s.regs.get64 .rcx).toNat ≤ 4112 ∨ s.regs.get64 .rcx + 8#64 = 0#64)
  | "apply_noise_main.b", s => inv R ra t₀ s ∧ (s.regs.get64 .rcx).toNat ≤ 4088
  | "apply_noise_main.c", s => inv R ra t₀ s ∧ (s.regs.get64 .rcx).toNat ≤ 4088
  | "apply_noise_main.d", s => inv R ra t₀ s ∧ (s.regs.get64 .rcx).toNat ≤ 4088
  | "apply_noise_main.done", s =>
      s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp
      ∧ SavedRegs t₀ s
      ∧ (s.dmem =⋆ HfApplyNoiseMainF t₀ ⋆ Rest R ra t₀)
  | _, _ => False

abbrev varMain : Label → MachineData → Nat
  | "apply_noise_main.loop", s => (0#64 - s.regs.get64 .r9).toNat
  | "apply_noise_main.b", s => (0#64 - s.regs.get64 .r9).toNat
  | "apply_noise_main.c", s => (0#64 - s.regs.get64 .r9).toNat
  | "apply_noise_main.d", s => (0#64 - s.regs.get64 .r9).toNat
  | "apply_noise_main.done", _ => 0
  | _, _ => 2 ^ 64

abbrev PostMain' (R : Mem 64 → Prop) (ra : Int64) (t₀ s : MachineData) : Prop :=
  s.regs.get64 .rsp = t₀.regs.get64 .rsp + 8
  ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp ∧ SavedRegs t₀ s
  ∧ (s.dmem =⋆ HfApplyNoiseMainF t₀ ⋆ (8 ?@ (t₀.regs.get64 .rsp)
      ⋆ (Reserve 0 (t₀.regs.get64 .rsp) ⋆ R)))

/-! ## The blocks of `apply_noise_main`, shared by `main_spec` and `spec3` -/

set_option hygiene false in
macro "blk_main" : tactic => `(tactic| (
    have hn := noise_init (t₀.regs.get64 .rcx)
    vcgen with finish))

set_option hygiene false in
macro "blk_loop" : tactic => `(tactic| (
    vcgen with finish))

set_option hygiene false in
macro "blk_b" : tactic => `(tactic| (
    vcgen with finish))

set_option hygiene false in
macro "blk_c" : tactic => `(tactic| (
    vcgen with finish))

set_option hygiene false in
macro "blk_d" : tactic => `(tactic| (
    vcgen
    case vc2 => grind
    case vc1 =>
      rename_i s hpre hcond
      dsimp only at hpre
      obtain ⟨⟨⟨hC, hrdi, hrsi, hrdx, hrax, hq, hs, hy, hj16, hjlt, hrsp, hrbp, hsaved, hmem⟩, hrcx⟩, hvar⟩ := hpre
      have h16 : BitVec.setWidth 64 (Int64.toBitVec 16) = 16#64 := by decide
      simp only [h16] at hcond ⊢
      rw [CondCode.interp_l_add _ _ _ rfl] at hcond
      simp only [decide_eq_true_eq] at hcond
      left
      refine Table.ofLabels_at (l := "apply_noise_main.loop") ?_
      have hb := shl2_toNat (t₀.regs.get64 .r9)
      change (0#64 - s.regs.get64 .r9).toNat = _ at hvar
      generalize BitVec.setWidth 64 (BitVec.setWidth 32 (t₀.regs.get64 Reg64.r9) <<< 2) = b at *
      generalize s.regs.get64 Reg64.r9 = r at *
      obtain ⟨hal1, hal2, hm1, hm2, hnz⟩ := hC
      -- the arithmetic core: `r = j - 4 m` and the branch condition `j + 16 < 4 m`
      have hm : (b).toNat = 4 * ((t₀.regs.get64 Reg64.r9).toNat % 2 ^ 32) := by omega
      generalize (t₀.regs.get64 Reg64.r9).toNat % 2 ^ 32 = m at *
      generalize hjd : (r + b).toNat = j at *
      have hr : r.toNat + 4 * m = 2 ^ 64 + j := by
        rw [BitVec.toNat_add] at hjd; omega
      have hc : j + 16 < 4 * m := by
        simp only [BitVec.toNat_ofNat] at hcond; omega
      have hj' : (16#64 + r + b).toNat = j + 16 := by
        rw [show 16#64 + r + b = (r + b) + 16#64 by grind, BitVec.toNat_add, hjd]
        simp only [BitVec.toNat_ofNat]; omega
      refine ⟨by decide, ?_, ?_⟩
      · simp (config := { decide := true }) only [Reg64s.get64_set64, ite_true, ite_false]
        refine ⟨⟨⟨hal1, hal2, hm1, hm2, hnz⟩, hrdi, hrsi, hrdx, hrax, ?_, ?_, ?_, ?_, ?_, hrsp, hrbp, hsaved, hmem⟩, Or.inl (by omega)⟩
        · rw [hj', show s.regs.get64 .rdx + (16#64 + r) - t₀.regs.get64 .rdx
              = (s.regs.get64 .rdx + r - t₀.regs.get64 .rdx) + 16#64 by grind, BitVec.toNat_add, hq]
          simp only [BitVec.toNat_ofNat]; omega
        · rw [hj', show s.regs.get64 .rsi + (16#64 + r) - t₀.regs.get64 .rsi
              = (s.regs.get64 .rsi + r - t₀.regs.get64 .rsi) + 16#64 by grind, BitVec.toNat_add, hs]
          simp only [BitVec.toNat_ofNat]; omega
        · rw [hj', show s.regs.get64 .rdi + (16#64 + r) * 2 - t₀.regs.get64 .rdi
              = (s.regs.get64 .rdi + r * 2 - t₀.regs.get64 .rdi) + 32#64 by grind, BitVec.toNat_add, hy]
          simp only [BitVec.toNat_ofNat]; omega
        · omega
        · omega
      · left
        change (0#64 - (16#64 + r)).toNat < _
        rw [show 0#64 - (16#64 + r) = (0#64 - r) - 16#64 by grind]
        rw [BitVec.toNat_sub, BitVec.toNat_sub] at *
        simp only [BitVec.toNat_ofNat] at *
        omega))

set_option hygiene false in
macro "blk_done" : tactic => `(tactic| (
    vcgen
    all_goals simp only [Rest] at *
    all_goals call_simp
    all_goals grind_cells))

theorem main_spec (hpl : Program.PlacedIn bodyMain) : HfApplyNoiseMainSpec := by
  refine Kraken.Executable.ProcSpec.of_cfg_post (p := bodyMain) tableMain PostMain' varMain
    (hblocks := ?_) (hpre := ?_) (hpost := ?_)
  · intro R ra t₀
    cfg_cases [bodyMain]
    · blk_main
    · blk_loop
    · blk_b
    · blk_c
    · blk_d
    · blk_done
  · rintro R ra t ⟨hcall, hc⟩
    refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, hc, ?_⟩
    have h := hcall
    simp only [Rest, CallPre] at h ⊢
    rw [Std.ExtHashMap.sep_comm_l (Reserve _ _), Std.ExtHashMap.sep_comm_l (RetCell _ _)] at h
    exact h
  · rintro R ra t₀ s ⟨h1, h2, h3, hm⟩
    refine ⟨h1, h2, h3, ?_⟩
    show (_ ⋆ (_ ⋆ (HfApplyNoiseMainF t₀ ⋆ R))) s.dmem
    rw [Std.ExtHashMap.sep_comm_l (Reserve _ _), Std.ExtHashMap.sep_comm_l (Block _ _)]
    exact hm


/-! ## The entries -/

/-- The tail call: from an entry's state `s` at `apply_noise_main` (memory
and argument registers as at the entry `t₀`), `main_spec`, with the entry's
constant moved into the caller's memory, reaches the return address with the
entry's postcondition. -/
theorem tail (hm : HfApplyNoiseMainSpec) (c : BitVec 64 × Nat) (R : Mem 64 → Prop)
    (ra : Int64) (t₀ s : MachineData)
    (hcall : CallPre 0 (HfApplyNoiseF c t₀ ⋆ R) ra t₀) (hc : HfApplyNoiseMainC t₀)
    (hmem : s.dmem = t₀.dmem) (hag : Agree t₀ s) :
    Eventually cenv.instrStep
      (fun st => st.2 = ra ∧ LeafPost 0 (HfApplyNoiseF c) R ra t₀ st.1)
      (s, entry "apply_noise_main") := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hag
  have key : ∀ X : Mem 64 → Prop,
      HfApplyNoiseF c t₀ ⋆ X = HfApplyNoiseMainF t₀ ⋆ (Block c.1 c.2 ⋆ X) := by
    intro X; simp only [Blocks, Std.ExtHashMap.sep_assoc]
  have hF : HfApplyNoiseMainF s = HfApplyNoiseMainF t₀ := by
    simp only [HfApplyNoiseMainF, HfApplyNoiseIt, HfApplyNoiseM, arg0, arg1, arg2, arg5,
      h1, h2, h3, h5]
  have hpre : LeafPre 0 HfApplyNoiseMainF HfApplyNoiseMainC (Block c.1 c.2 ⋆ R) ra s := by
    refine ⟨?_, ?_⟩
    · simp only [CallPre, hF, hmem, h6]
      rw [← key]; exact hcall
    · simp only [HfApplyNoiseMainC, HfApplyNoiseM, arg1, arg2, arg3, arg5, h2, h3, h4, h5]
      exact hc
  refine eventually_weaken _ _ _ _ ?_ (hm (Block c.1 c.2 ⋆ R) ra s hpre)
  rintro st ⟨hra, hrsp, hrbp, hsv, hst⟩
  refine ⟨hra, ?_, ?_, ?_, ?_⟩
  · rw [hrsp, h6]
  · rw [hrbp, h7]
  · obtain ⟨g1, g2, g3, g4, g5⟩ := hsv
    exact ⟨g1.trans h8, g2.trans h9, g3.trans h10, g4.trans h11, g5.trans h12⟩
  · simp only [hF, h6] at hst
    rw [key]; exact hst

/-- The assertion at an entry `l₀` that tail-calls `apply_noise_main`. -/
abbrev tableE (c : BitVec 64 × Nat) (l₀ : Label) (R : Mem 64 → Prop) (ra : Int64)
    (t₀ : MachineData) : Label → MachineData → Prop := fun l s =>
  l = l₀ ∧ s = t₀ ∧ HfApplyNoiseC c.1 t₀ ∧ CallPre 0 (HfApplyNoiseF c t₀ ⋆ R) ra t₀
    ∧ (t₀.dmem =⋆ HfApplyNoiseF c t₀ ⋆ Rest R ra t₀)

/-- The tail jump's exit: at `apply_noise_main`, memory and argument registers
as at the entry. -/
abbrev ExitE (c : BitVec 64 × Nat) (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData)
    (a : Int64) (s : MachineData) : Prop :=
  a = entry "apply_noise_main" ∧ HfApplyNoiseC c.1 t₀
    ∧ CallPre 0 (HfApplyNoiseF c t₀ ⋆ R) ra t₀ ∧ s.dmem = t₀.dmem ∧ Agree t₀ s

theorem tableE_pre (c : BitVec 64 × Nat) (l₀ : Label) (R : Mem 64 → Prop) (ra : Int64)
    (t : MachineData) (h : LeafPre 0 (HfApplyNoiseF c) (HfApplyNoiseC c.1) R ra t) :
    tableE c l₀ R ra t l₀ t := by
  obtain ⟨hcall, hc⟩ := h
  refine ⟨rfl, rfl, hc, hcall, ?_⟩
  have h := hcall
  simp only [Rest, CallPre] at h ⊢
  rw [Std.ExtHashMap.sep_comm_l (Reserve _ _), Std.ExtHashMap.sep_comm_l (RetCell _ _)] at h
  exact h

theorem spec0 (hm : HfApplyNoiseMainSpec) (hpl : Program.PlacedIn body0) :
    HfApplyNoise0Spec := by
  refine Kraken.Executable.ProcSpec.of_cfg (p := body0)
    (tableE HfApplyNoiseK0 "ff_sbr_hf_apply_noise_0_sse2") (Exit := ExitE HfApplyNoiseK0)
    (hblocks := ?_) (hpre := ?_) (hexit := ?_)
  · intro R ra t₀
    cfg_cases [body0]
    vcgen with finish
  · exact fun R ra t h => tableE_pre _ _ R ra t h
  · rintro R ra t₀ a s ⟨rfl, hc, hcall, hmem, hag⟩
    exact tail hm _ R ra t₀ s hcall hc.1 hmem hag

theorem spec1 (hm : HfApplyNoiseMainSpec) (hpl : Program.PlacedIn body1) :
    HfApplyNoise1Spec := by
  refine Kraken.Executable.ProcSpec.of_cfg (p := body1)
    (tableE HfApplyNoiseK1 "ff_sbr_hf_apply_noise_1_sse2") (Exit := ExitE HfApplyNoiseK1)
    (hblocks := ?_) (hpre := ?_) (hexit := ?_)
  · intro R ra t₀
    cfg_cases [body1]
    vcgen with finish
  · exact fun R ra t h => tableE_pre _ _ R ra t h
  · rintro R ra t₀ a s ⟨rfl, hc, hcall, hmem, hag⟩
    exact tail hm _ R ra t₀ s hcall hc.1 hmem hag

theorem spec2 (hm : HfApplyNoiseMainSpec) (hpl : Program.PlacedIn body2) :
    HfApplyNoise2Spec := by
  refine Kraken.Executable.ProcSpec.of_cfg (p := body2)
    (tableE HfApplyNoiseK2 "ff_sbr_hf_apply_noise_2_sse2") (Exit := ExitE HfApplyNoiseK2)
    (hblocks := ?_) (hpre := ?_) (hexit := ?_)
  · intro R ra t₀
    cfg_cases [body2]
    vcgen with finish
  · exact fun R ra t h => tableE_pre _ _ R ra t h
  · rintro R ra t₀ a s ⟨rfl, hc, hcall, hmem, hag⟩
    exact tail hm _ R ra t₀ s hcall hc.1 hmem hag

/-- Entry 3 falls into `apply_noise_main`: its table is `apply_noise_main`'s,
with the constant moved into the caller's memory, plus the entry. -/
abbrev table3 (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) :
    Label → MachineData → Prop
  | "ff_sbr_hf_apply_noise_3_sse2", s => s = t₀ ∧ HfApplyNoiseC HfApplyNoiseK3.1 t₀
      ∧ (t₀.dmem =⋆ Blocks [HfApplyNoiseK3] ⋆ (HfApplyNoiseMainF t₀ ⋆ Rest R ra t₀))
      ∧ (t₀.dmem =⋆ HfApplyNoiseMainF t₀ ⋆ Rest (Block HfApplyNoiseK3.1 32 ⋆ R) ra t₀)
  | l, s => tableMain (Block HfApplyNoiseK3.1 32 ⋆ R) ra t₀ l s

theorem spec3 (hpl : Program.PlacedIn body3) : HfApplyNoise3Spec := by
  refine Kraken.Executable.ProcSpec.of_cfg_post (p := body3) table3
    (fun R ra t₀ s => PostMain' (Block HfApplyNoiseK3.1 32 ⋆ R) ra t₀ s) varMain
    (hblocks := ?_) (hpre := ?_) (hpost := ?_)
  · intro R ra t₀
    cfg_cases [body3]
    · vcgen with finish
    · blk_main
    · blk_loop
    · blk_b
    · blk_c
    · blk_d
    · blk_done
  · rintro R ra t ⟨hcall, hc⟩
    refine ⟨rfl, hc, ?_, ?_⟩
    all_goals
      have h := hcall
      simp only [Rest, CallPre, Blocks] at h ⊢
      exact Mem.ac h
  · rintro R ra t₀ s ⟨h1, h2, h3, hm⟩
    refine ⟨h1, h2, h3, ?_⟩
    simp only [Blocks] at hm ⊢
    exact Mem.ac hm

/-- The four entries, from the placement of the whole text. -/
theorem spec (hpl : Program.PlacedIn body) : HfApplyNoiseSpec := by
  have hm := main_spec (Program.PlacedIn.of_subBlocksOf hpl (by decide))
  exact ⟨spec0 hm (Program.PlacedIn.of_subBlocksOf hpl (by decide)), spec1 hm (Program.PlacedIn.of_subBlocksOf hpl (by decide)),
    spec2 hm (Program.PlacedIn.of_subBlocksOf hpl (by decide)), spec3 (Program.PlacedIn.of_subBlocksOf hpl (by decide))⟩
end Kraken.Examples.Sbr.HfApplyNoise
