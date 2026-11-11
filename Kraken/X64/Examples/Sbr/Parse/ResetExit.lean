import Kraken.InfoOff
import Kraken.X64.Examples.Sbr.Parse.ResetTable
import Kraken.X64.Examples.Sbr.Parse.ResetModel
import Kraken.X64.Examples.Sbr.Parse.ResetExitW

/-!
# `sbr_reset`: the epilogue and the return (shard B)

`L1d95` frees the frame and pops the six saved registers (`Saved`); `done` returns. The body's
memory `Mm` is given back as the convention's reservation and the footprint `RF` of the result
values (`exit_mem`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Reset

variable [CodeEnv]

omit [CodeEnv] in
theorem blk_cons (a : BitVec 64) (i n m : Nat) (hm : m = i + n) (h : m ≤ 2 ^ 64) :
    m ?@ a = i ?@ a ⋆ n ?@ (a + BitVec.ofNat 64 i) := by
  subst hm; exact Block.split a i n h

omit [CodeEnv] in
theorem savedB_eq (t₀ : MachineData) :
    0x30 ?@ (t₀.regs.get64 .rsp - 0x30#64) = SavedB t₀ := by
  unfold SavedB
  generalize t₀.regs.get64 .rsp = R
  rw [blk_cons _ 8 0x28 0x30 rfl (by decide),
    show R - 0x30#64 + BitVec.ofNat 64 8 = R - 0x28#64 by bv_omega,
    blk_cons _ 8 0x20 0x28 rfl (by decide),
    show R - 0x28#64 + BitVec.ofNat 64 8 = R - 0x20#64 by bv_omega,
    blk_cons _ 8 0x18 0x20 rfl (by decide),
    show R - 0x20#64 + BitVec.ofNat 64 8 = R - 0x18#64 by bv_omega,
    blk_cons _ 8 0x10 0x18 rfl (by decide),
    show R - 0x18#64 + BitVec.ofNat 64 8 = R - 0x10#64 by bv_omega,
    blk_cons _ 8 8 0x10 rfl (by decide),
    show R - 0x10#64 + BitVec.ofNat 64 8 = R - 0x8#64 by bv_omega]
  ac_rfl

omit [CodeEnv] in
/-- The caller's reservation is the callees' stack, the frame and the pushes. -/
theorem reserve_exit (k : Nat) (t₀ : MachineData) (hR : 0x578 ≤ (t₀.regs.get64 .rsp).toNat) :
    Reserve (resetNeed k) (t₀.regs.get64 .rsp)
      = Reserve (8 + tlimNeed k) (t₀.regs.get64 .rsp - 0x578#64)
        ⋆ 0x548 ?@ (t₀.regs.get64 .rsp - 0x578#64) ⋆ SavedB t₀ := by
  rw [← savedB_eq]
  generalize t₀.regs.get64 .rsp = R at hR ⊢
  rw [show resetNeed k = 0x578 + (8 + tlimNeed k) by unfold resetNeed tlimNeed; omega,
    Reserve_split 0x578 _ R hR, blk_cons _ 0x548 0x30 0x578 rfl (by decide),
    show R - BitVec.ofNat 64 0x578 + BitVec.ofNat 64 0x548 = R - 0x30#64 by bv_omega]
  ac_rfl

omit [CodeEnv] in
theorem blk8_split (s : BitVec 64) : 8 ?@ (s + 0x44#64) = 4 ?@ (s + 0x44#64) ⋆ 4 ?@ (s + 0x48#64) := by
  rw [blk_cons _ 4 4 8 rfl (by decide), show s + 0x44#64 + BitVec.ofNat 64 4 = s + 0x48#64 by bv_omega]

/-- The body's memory given back: the return slot, the reservation, the footprint of the
result values. -/
theorem exit_mem {k : Nat} {e : REnv} {a : RArgs} {ra : Int64}
    {t₀ : MachineData} (hR : 0x578 ≤ (t₀.regs.get64 .rsp).toNat) {st : St} {fr : List UInt8}
    (hF : FrOk fr) (hfm : st.fm.length = 98)
    {m : Mem 64} (h : m =⋆ Mm k e a ra t₀ st fr) :
    m =⋆ RetCell ra (t₀.regs.get64 .rsp) ⋆ (Reserve (resetNeed k) (t₀.regs.get64 .rsp)
      ⋆ (RF e { a with x := st.x, sp := st.sp } t₀ ⋆ a.x.R)) := by
  have hw := Mm_MmW k e a ra t₀ st fr hF hfm m h
  rw [reserve_exit k t₀ hR]
  simp only [RF, ScR, TabR, DR]
  rw [blk8_split]
  unfold MmW at hw
  exact Mem.ac hw


omit [CodeEnv] in
theorem pop_a0 (t : BitVec 64) : BitVec.setWidth 64 1352#64 + (t - 1400#64) = t - 48#64 := by
  bv_omega

omit [CodeEnv] in
theorem pop_a (t : BitVec 64) : t - 48#64 + 8#64 = t - 40#64 ∧ t - 40#64 + 8#64 = t - 32#64
    ∧ t - 32#64 + 8#64 = t - 24#64 ∧ t - 24#64 + 8#64 = t - 16#64
    ∧ t - 16#64 + 8#64 = t - 8#64 ∧ t - 8#64 + 8#64 = t := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_omega

omit [CodeEnv] in
theorem saved_rbp {t₀ : MachineData} {Q : Mem 64 → Prop} {m : Mem 64} (h : m =⋆ Saved t₀ ⋆ Q) :
    m.loadInt ((t₀.regs.get64 .rsp) - 8#64) 8 = some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 .rbp).toInt)) := by
  unfold Saved at h
  exact loadInt_sep _ _ 8 _ m (Mem.ac h (H₂ := c8 ((t₀.regs.get64 .rsp) - 0x8#64) (t₀.regs.get64 .rbp)
    ⋆ (c8 ((t₀.regs.get64 .rsp) - 0x10#64) (t₀.regs.get64 .r15) ⋆ c8 ((t₀.regs.get64 .rsp) - 0x18#64) (t₀.regs.get64 .r14) ⋆ c8 ((t₀.regs.get64 .rsp) - 0x20#64) (t₀.regs.get64 .r13) ⋆ c8 ((t₀.regs.get64 .rsp) - 0x28#64) (t₀.regs.get64 .r12) ⋆ c8 ((t₀.regs.get64 .rsp) - 0x30#64) (t₀.regs.get64 .rbx) ⋆ Q))) (Int.toBytes_length _ _) (by omega)

omit [CodeEnv] in
theorem saved_r15 {t₀ : MachineData} {Q : Mem 64 → Prop} {m : Mem 64} (h : m =⋆ Saved t₀ ⋆ Q) :
    m.loadInt ((t₀.regs.get64 .rsp) - 16#64) 8 = some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 .r15).toInt)) := by
  unfold Saved at h
  exact loadInt_sep _ _ 8 _ m (Mem.ac h (H₂ := c8 ((t₀.regs.get64 .rsp) - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 ((t₀.regs.get64 .rsp) - 0x8#64) (t₀.regs.get64 .rbp) ⋆ c8 ((t₀.regs.get64 .rsp) - 0x18#64) (t₀.regs.get64 .r14) ⋆ c8 ((t₀.regs.get64 .rsp) - 0x20#64) (t₀.regs.get64 .r13) ⋆ c8 ((t₀.regs.get64 .rsp) - 0x28#64) (t₀.regs.get64 .r12) ⋆ c8 ((t₀.regs.get64 .rsp) - 0x30#64) (t₀.regs.get64 .rbx) ⋆ Q))) (Int.toBytes_length _ _) (by omega)

omit [CodeEnv] in
theorem saved_r14 {t₀ : MachineData} {Q : Mem 64 → Prop} {m : Mem 64} (h : m =⋆ Saved t₀ ⋆ Q) :
    m.loadInt ((t₀.regs.get64 .rsp) - 24#64) 8 = some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 .r14).toInt)) := by
  unfold Saved at h
  exact loadInt_sep _ _ 8 _ m (Mem.ac h (H₂ := c8 ((t₀.regs.get64 .rsp) - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 ((t₀.regs.get64 .rsp) - 0x8#64) (t₀.regs.get64 .rbp) ⋆ c8 ((t₀.regs.get64 .rsp) - 0x10#64) (t₀.regs.get64 .r15) ⋆ c8 ((t₀.regs.get64 .rsp) - 0x20#64) (t₀.regs.get64 .r13) ⋆ c8 ((t₀.regs.get64 .rsp) - 0x28#64) (t₀.regs.get64 .r12) ⋆ c8 ((t₀.regs.get64 .rsp) - 0x30#64) (t₀.regs.get64 .rbx) ⋆ Q))) (Int.toBytes_length _ _) (by omega)

omit [CodeEnv] in
theorem saved_r13 {t₀ : MachineData} {Q : Mem 64 → Prop} {m : Mem 64} (h : m =⋆ Saved t₀ ⋆ Q) :
    m.loadInt ((t₀.regs.get64 .rsp) - 32#64) 8 = some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 .r13).toInt)) := by
  unfold Saved at h
  exact loadInt_sep _ _ 8 _ m (Mem.ac h (H₂ := c8 ((t₀.regs.get64 .rsp) - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 ((t₀.regs.get64 .rsp) - 0x8#64) (t₀.regs.get64 .rbp) ⋆ c8 ((t₀.regs.get64 .rsp) - 0x10#64) (t₀.regs.get64 .r15) ⋆ c8 ((t₀.regs.get64 .rsp) - 0x18#64) (t₀.regs.get64 .r14) ⋆ c8 ((t₀.regs.get64 .rsp) - 0x28#64) (t₀.regs.get64 .r12) ⋆ c8 ((t₀.regs.get64 .rsp) - 0x30#64) (t₀.regs.get64 .rbx) ⋆ Q))) (Int.toBytes_length _ _) (by omega)

omit [CodeEnv] in
theorem saved_r12 {t₀ : MachineData} {Q : Mem 64 → Prop} {m : Mem 64} (h : m =⋆ Saved t₀ ⋆ Q) :
    m.loadInt ((t₀.regs.get64 .rsp) - 40#64) 8 = some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 .r12).toInt)) := by
  unfold Saved at h
  exact loadInt_sep _ _ 8 _ m (Mem.ac h (H₂ := c8 ((t₀.regs.get64 .rsp) - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 ((t₀.regs.get64 .rsp) - 0x8#64) (t₀.regs.get64 .rbp) ⋆ c8 ((t₀.regs.get64 .rsp) - 0x10#64) (t₀.regs.get64 .r15) ⋆ c8 ((t₀.regs.get64 .rsp) - 0x18#64) (t₀.regs.get64 .r14) ⋆ c8 ((t₀.regs.get64 .rsp) - 0x20#64) (t₀.regs.get64 .r13) ⋆ c8 ((t₀.regs.get64 .rsp) - 0x30#64) (t₀.regs.get64 .rbx) ⋆ Q))) (Int.toBytes_length _ _) (by omega)

omit [CodeEnv] in
theorem saved_rbx {t₀ : MachineData} {Q : Mem 64 → Prop} {m : Mem 64} (h : m =⋆ Saved t₀ ⋆ Q) :
    m.loadInt ((t₀.regs.get64 .rsp) - 48#64) 8 = some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 .rbx).toInt)) := by
  unfold Saved at h
  exact loadInt_sep _ _ 8 _ m (Mem.ac h (H₂ := c8 ((t₀.regs.get64 .rsp) - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 ((t₀.regs.get64 .rsp) - 0x8#64) (t₀.regs.get64 .rbp) ⋆ c8 ((t₀.regs.get64 .rsp) - 0x10#64) (t₀.regs.get64 .r15) ⋆ c8 ((t₀.regs.get64 .rsp) - 0x18#64) (t₀.regs.get64 .r14) ⋆ c8 ((t₀.regs.get64 .rsp) - 0x20#64) (t₀.regs.get64 .r13) ⋆ c8 ((t₀.regs.get64 .rsp) - 0x28#64) (t₀.regs.get64 .r12) ⋆ Q))) (Int.toBytes_length _ _) (by omega)

set_option maxRecDepth 100000 in
/-- Free the frame, pop the six saved registers. -/
theorem blk_L1d95 (k : Nat) (hk : k ≤ 2 ^ 32) (e : REnv) (a : RArgs) (ra : Int64)
    (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1d95" ⟨"sbr_reset.L1d95", B.L1d95, some "sbr_reset.done"⟩ := by
  info_off
  measure_hb "L1d95"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hC, ⟨hrsp, hrbp⟩, u, st, fr, hout, hfm, hF, hm⟩ := T.L1d95.mp hs
    clear hs
    have hX0 := exit_mem (by have := hC.rsp; unfold resetStkMin at this; omega) hF hfm hm
    have hX : s₀.dmem =⋆ RetCell ra (t₀.regs.get64 .rsp) ⋆ (Reserve (resetNeed k) (t₀.regs.get64 .rsp)
        ⋆ (RF e { a with x := st.x, sp := st.sp, us := u } t₀ ⋆ a.x.R)) := hX0
    clear hX0
    have hS := focus (Mm_saved ..) hm
    clear hm
    generalize Mx_saved k e { a with us := u } ra t₀ st fr = Q at hS
    obtain ⟨p1, p2, p3, p4, p5, p6⟩ := pop_a (t₀.regs.get64 .rsp)
    have l1 : s₀.dmem.loadInt (t₀.regs.get64 .rsp - 48#64) 8
        = some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 .rbx).toInt)) := by
      exact saved_rbx hS
    have l2 : s₀.dmem.loadInt (t₀.regs.get64 .rsp - 40#64) 8
        = some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 .r12).toInt)) := by
      exact saved_r12 hS
    have l3 : s₀.dmem.loadInt (t₀.regs.get64 .rsp - 32#64) 8
        = some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 .r13).toInt)) := by
      exact saved_r13 hS
    have l4 : s₀.dmem.loadInt (t₀.regs.get64 .rsp - 24#64) 8
        = some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 .r14).toInt)) := by
      exact saved_r14 hS
    have l5 : s₀.dmem.loadInt (t₀.regs.get64 .rsp - 16#64) 8
        = some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 .r15).toInt)) := by
      exact saved_r15 hS
    have l6 : s₀.dmem.loadInt (t₀.regs.get64 .rsp - 8#64) 8
        = some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 .rbp).toInt)) := by
      exact saved_rbp hS
    clear hS
    generalize hP : RetCell ra (t₀.regs.get64 .rsp) ⋆ (Reserve (resetNeed k) (t₀.regs.get64 .rsp)
      ⋆ (RF e { a with x := st.x, sp := st.sp, us := u } t₀ ⋆ a.x.R)) = P at hX
    simp only [B.L1d95]
    vcgen
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals simp only [hrsp, Int64.toBitVec_ofNat_norm] at *
    all_goals simp only [pop_a0, p1, p2, p3, p4, p5, p6, l1, l2, l3, l4, l5, l6, Option.isSome_some,
      Option.some.injEq] at *
    all_goals try subst_vars
    refine ⟨T.done.mpr ⟨hC, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, st.x, st.sp, u, hout, ?_⟩, by var_step⟩
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, BitVec.ofInt64_ofBytes_toBytes8,
      BitVec.ofInt_toInt]
    first | exact hX | exact hP ▸ hX

set_option maxRecDepth 100000 in
/-- `ret`. -/
theorem blk_done (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.done" ⟨"sbr_reset.done", B.done, some "sbr_reset.L1da7"⟩ := by
  info_off
  measure_hb "done"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hC, hsp, hbp, hsv, x', sp', us', hout, hm⟩ := T.done.mp hs
    clear hs
    have hpost : s₀.dmem =⋆ 8 ?@ t₀.regs.get64 .rsp ⋆ (Reserve (resetNeed k) (t₀.regs.get64 .rsp)
        ⋆ (RF e { a with x := x', sp := sp', us := us' } t₀ ⋆ a.x.R)) :=
      Block.sep_intro (Int.toBytes_length _ _) (by decide) hm
    have l0 : s₀.dmem.loadInt (t₀.regs.get64 .rsp) 8
        = some (Int.ofBytes (Int.toBytes 8 ra.toBitVec.toInt)) :=
      loadInt_sep _ _ 8 _ _ hm (Int.toBytes_length 8 _) (by omega)
    have hra : s₀.retAddr = some ra := by
      simp only [MachineData.retAddr, hsp, l0, Option.map_some,
        BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Int64.ofBitVec_toBitVec]
    clear hm l0
    generalize hQ : 8 ?@ t₀.regs.get64 .rsp ⋆ (Reserve (resetNeed k) (t₀.regs.get64 .rsp)
        ⋆ (RF e { a with x := x', sp := sp', us := us' } t₀ ⋆ a.x.R)) = Q at hpost
    simp only [B.done]
    vcgen
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals simp only [hra, Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    right
    refine ⟨rfl, x', sp', us', hout, ?_, ?_, ?_, ?_⟩
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hsp, hbp]
    all_goals first | rfl | exact hsv | exact hpost | exact hQ ▸ hpost

end Kraken.Examples.Sbr.Reset
