import Kraken.X64.Examples.Sbr.Parse.InitBlk1
import Kraken.X64.Examples.Sbr.Parse.InitBlk2
import Kraken.X64.Examples.Sbr.Parse.InitBlk3
import Kraken.X64.Examples.Sbr.Parse.InitBlk4
import Kraken.X64.Examples.Sbr.Parse.InitBlk5
import Kraken.X64.Examples.Sbr.Parse.InitBlk6
import Kraken.X64.Examples.Sbr.Parse.InitBlk7
import Kraken.X64.Examples.Sbr.Parse.InitBlk8

/-!
# `ff_aac_sbr_ctx_alloc_init`: the procedure

The block obligations of `InitBlk1`-`InitBlk8` assembled by `ProcSpec.of_cfg_post`. The
hypotheses are the placement of the text and the callees' contracts `InitAssumed`; `k ≤ 2^32`
bounds the callees' stack.

At entry the routine's `0x40` bytes come off the top of the caller's reservation of
`initNeed k`: the 56 bytes of the frame (`FrB`), the return slot of a call at `r - 0x40` and the
callees' `k` bytes below it; at the return they are merged back.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr
open Kraken.Examples.Sbr.Apply (c8)

namespace Kraken.Examples.Sbr.Init

variable [CodeEnv]

omit [CodeEnv] in
/-- The 56 bytes below the return address as the slots of `FrB`. -/
theorem frame_split (r : BitVec 64) :
    ((0x40 - 8) ?@ (r - BitVec.ofNat 64 (0x40 - 8)) : Mem 64 → Prop)
      = 8 ?@ (r - 0x8#64) ⋆ (8 ?@ (r - 0x10#64) ⋆ (8 ?@ (r - 0x18#64) ⋆ (8 ?@ (r - 0x20#64)
        ⋆ (4 ?@ (r - 0x24#64) ⋆ (12 ?@ (r - 0x30#64) ⋆ 8 ?@ (r - 0x38#64)))))) := by
  have h1 := Block.split (r - 0x38#64) 8 0x30 (by omega)
  have h2 := Block.split (r - 0x30#64) 12 0x24 (by omega)
  have h3 := Block.split (r - 0x24#64) 4 0x20 (by omega)
  have h4 := Block.split (r - 0x20#64) 8 0x18 (by omega)
  have h5 := Block.split (r - 0x18#64) 8 0x10 (by omega)
  have h6 := Block.split (r - 0x10#64) 8 8 (by omega)
  have a1 : r - 0x38#64 + BitVec.ofNat 64 8 = r - 0x30#64 := by bv_omega
  have a2 : r - 0x30#64 + BitVec.ofNat 64 12 = r - 0x24#64 := by bv_omega
  have a3 : r - 0x24#64 + BitVec.ofNat 64 4 = r - 0x20#64 := by bv_omega
  have a4 : r - 0x20#64 + BitVec.ofNat 64 8 = r - 0x18#64 := by bv_omega
  have a5 : r - 0x18#64 + BitVec.ofNat 64 8 = r - 0x10#64 := by bv_omega
  have a6 : r - 0x10#64 + BitVec.ofNat 64 8 = r - 0x8#64 := by bv_omega
  rw [a1] at h1; rw [a2] at h2; rw [a3] at h3; rw [a4] at h4; rw [a5] at h5; rw [a6] at h6
  simp only [Nat.reduceAdd] at h1 h2 h3 h4 h5 h6
  show (56 ?@ (r - 0x38#64) : Mem 64 → Prop) = _
  rw [h1, h2, h3, h4, h5, h6]
  ac_rfl

omit [CodeEnv] in
/-- The caller's reservation as the routine's frame, the return slot of a call and the
callees' reservation. -/
theorem need_split (k : Nat) (r : BitVec 64) (hw : 0x40 ≤ r.toNat) (K : Mem 64 → Prop) :
    Reserve (initNeed k) r ⋆ K
      = 8 ?@ (r - 0x40#64) ⋆ (Reserve k (r - 0x40#64)
        ⋆ ((8 ?@ (r - 0x8#64) ⋆ (8 ?@ (r - 0x10#64) ⋆ (8 ?@ (r - 0x18#64) ⋆ (8 ?@ (r - 0x20#64)
        ⋆ (4 ?@ (r - 0x24#64) ⋆ (12 ?@ (r - 0x30#64) ⋆ 8 ?@ (r - 0x38#64))))))) ⋆ K)) := by
  rw [initNeed, Reserve_split_frame 0x40 k (by omega) r hw K, frame_split]

omit [CodeEnv] in
/-- The memory at the return as the convention's. -/
theorem post_mem {k : Nat} {TxTab X R B : Mem 64 → Prop} {t₀ : MachineData}
    (hw : 0x40 ≤ (t₀.regs.get64 .rsp).toNat) {m : Mem 64}
    (h : m =⋆ 8 ?@ t₀.regs.get64 .rsp ⋆ MF k TxTab X t₀ (FrB t₀) B R) :
    m =⋆ 8 ?@ t₀.regs.get64 .rsp ⋆ (Reserve (initNeed k) (t₀.regs.get64 .rsp)
      ⋆ ((B ⋆ (TxTab ⋆ X)) ⋆ R)) := by
  rw [need_split k _ hw]
  simp only [MF, FrB] at h
  exact Mem.ac h

theorem spec (hpl : Program.PlacedIn body) (k : Nat) (hk : k ≤ 2 ^ 32)
    (Ctx : BitVec 64 → Mem 64 → Prop) (TxTab X : Mem 64 → Prop)
    (hA : InitAssumed k Ctx TxTab X) : InitSpec k Ctx TxTab X := by
  refine Kraken.Executable.ProcSpec.of_cfg_post_pre (p := body) (table k Ctx TxTab X)
    (fun R _ t₀ s => Post' k Ctx TxTab X R t₀ s) var (hblocks := ?_) (hpre := ?_) (hpost := ?_)
  · intro R ra t₀ _
    refine Program.forall_blockAt ?_
    exact
      (.cons (blk_entry k Ctx TxTab X hA.mallocz R ra t₀ _ rfl)
      (.cons (blk_L22 k Ctx TxTab X R ra t₀ _ rfl)
      (.cons (blk_L2b k Ctx TxTab X R ra t₀ _ rfl)
      (.cons (blk_L3e k Ctx TxTab X R ra t₀ _ rfl)
      (.cons (blk_L58 k Ctx TxTab X R ra t₀ _ rfl)
      (.cons (blk_L67 k Ctx TxTab X R ra t₀ _ rfl)
      (.cons (blk_L78 k Ctx TxTab X R ra t₀ _ rfl)
      (.cons (blk_L89 k Ctx TxTab X R ra t₀ _ rfl)
      (.cons (blk_L95 k Ctx TxTab X R ra t₀ _ rfl)
      (.cons (blk_La9 k Ctx TxTab X R ra t₀ _ rfl)
      (.cons (blk_Lba k Ctx TxTab X hA.txInit R ra t₀ _ rfl)
      (.cons (blk_Le1 k Ctx TxTab X R ra t₀ _ rfl)
      (.cons (blk_Le9 k Ctx TxTab X hA.txInit R ra t₀ _ rfl)
      (.cons (blk_L11f k Ctx TxTab X R ra t₀ _ rfl)
      (.cons (blk_L123 k Ctx TxTab X hA.psdsp R ra t₀ _ rfl)
      (.cons (blk_L12f k Ctx TxTab X hA.sbrdsp R ra t₀ _ rfl)
      (.cons (blk_L13e k Ctx TxTab X R ra t₀ _ rfl)
      (.cons (blk_L15a k Ctx TxTab X R ra t₀ _ rfl)
      (.cons (blk_L17a k Ctx TxTab X R ra t₀ _ rfl)
      (.cons (blk_L17f k Ctx TxTab X R ra t₀ _ rfl)
      (.cons (blk_done k Ctx TxTab X R ra t₀ _ rfl)
      (.nil _))))))))))))))))))))))
  · rintro R ra t hcall
    refine ⟨rfl, ?_⟩
    have hw : 0x40 ≤ (t.regs.get64 .rsp).toNat := by
      have := CallPre.le hcall; unfold initNeed at this; omega
    simp only [InitPre, CallPre] at hcall; rw [need_split k _ hw] at hcall
    simp only [MF, FrB, Rest]
    exact Mem.ac hcall
  · rintro R ra t₀ s hcall ⟨hsp, hbp, hsv, hO⟩
    have hw : 0x40 ≤ (t₀.regs.get64 .rsp).toNat := by
      have := CallPre.le hcall; unfold initNeed at this; omega
    rcases hO with ⟨h1, r, h2, h4, ha, hs, h3⟩ | ⟨h1, h3⟩ | ⟨h1, p, bc, bf, l1, l2, h3⟩
      | ⟨h1, p, c, f, bc, bf, l1, l2, h3⟩
    · exact Or.inl ⟨h1, r, h2, h4, ha, hs, hsp, hbp, hsv, post_mem hw h3⟩
    · exact Or.inr (Or.inl ⟨h1, hsp, hbp, hsv, post_mem hw h3⟩)
    · refine Or.inr (Or.inr (Or.inl ⟨h1, p, bc, bf, l1, l2, hsp, hbp, hsv, ?_⟩))
      have h := post_mem hw h3
      unfold BF1 at h
      exact Mem.ac h
    · refine Or.inr (Or.inr (Or.inr ⟨h1, p, c, f, bc, bf, l1, l2, hsp, hbp, hsv, ?_⟩))
      have h := post_mem hw h3
      unfold BF2 at h
      exact Mem.ac h

end Kraken.Examples.Sbr.Init
