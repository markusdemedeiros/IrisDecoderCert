import Kraken.X64.Examples.Sbr.Parse.HdrBlk1
import Kraken.X64.Examples.Sbr.Parse.HdrBlk2
import Kraken.X64.Examples.Sbr.Parse.HdrBlk3
import Kraken.X64.Examples.Sbr.Parse.HdrBlk4
import Kraken.X64.Examples.Sbr.Parse.HdrCall

/-!
# `read_sbr_header`: the procedure

The block obligations of `HdrBlk1`-`HdrBlk4` and `HdrCall` assembled by
`ProcSpec.of_cfg_post`. The hypotheses are the placement of the text and the callee's
contract `TlimSpec`; `k ≤ 2^32` bounds the callee's stack.

At entry the routine's `0x30` bytes come off the top of the caller's reservation of
`hdrNeed k`: the 40 bytes of the frame (`FrB`), the return slot of the call at `r - 0x30` and
the callee's `k` bytes below it; at the return they are merged back.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply

namespace Kraken.Examples.Sbr.Hdr

variable [CodeEnv]

omit [CodeEnv] in
/-- The 40 bytes below the return address as the slots of `FrB`. -/
theorem frame_split (r : BitVec 64) :
    ((0x30 - 8) ?@ (r - BitVec.ofNat 64 (0x30 - 8)) : Mem 64 → Prop)
      = 8 ?@ (r - 0x28#64) ⋆ (4 ?@ (r - 0x20#64) ⋆ (2 ?@ (r - 0x1c#64) ⋆ (2 ?@ (r - 0x1a#64)
        ⋆ (8 ?@ (r - 0x18#64) ⋆ (8 ?@ (r - 0x10#64) ⋆ 8 ?@ (r - 0x8#64)))))) := by
  have h1 := Block.split (r - 0x28#64) 8 0x20 (by omega)
  have h2 := Block.split (r - 0x20#64) 4 0x1c (by omega)
  have h3 := Block.split (r - 0x1c#64) 2 0x1a (by omega)
  have h4 := Block.split (r - 0x1a#64) 2 0x18 (by omega)
  have h5 := Block.split (r - 0x18#64) 8 0x10 (by omega)
  have h6 := Block.split (r - 0x10#64) 8 8 (by omega)
  have a1 : r - 0x28#64 + BitVec.ofNat 64 8 = r - 0x20#64 := by bv_omega
  have a2 : r - 0x20#64 + BitVec.ofNat 64 4 = r - 0x1c#64 := by bv_omega
  have a3 : r - 0x1c#64 + BitVec.ofNat 64 2 = r - 0x1a#64 := by bv_omega
  have a4 : r - 0x1a#64 + BitVec.ofNat 64 2 = r - 0x18#64 := by bv_omega
  have a5 : r - 0x18#64 + BitVec.ofNat 64 8 = r - 0x10#64 := by bv_omega
  have a6 : r - 0x10#64 + BitVec.ofNat 64 8 = r - 0x8#64 := by bv_omega
  rw [a1] at h1; rw [a2] at h2; rw [a3] at h3; rw [a4] at h4; rw [a5] at h5; rw [a6] at h6
  simp only [Nat.reduceAdd] at h1 h2 h3 h4 h5 h6
  show (40 ?@ (r - 0x28#64) : Mem 64 → Prop) = _
  rw [h1, h2, h3, h4, h5, h6]

omit [CodeEnv] in
/-- The caller's reservation as the routine's frame, the return slot of the call and the
callee's reservation. -/
theorem need_split (k : Nat) (r : BitVec 64) (hw : 0x30 ≤ r.toNat) (K : Mem 64 → Prop) :
    Reserve (hdrNeed k) r ⋆ K
      = 8 ?@ (r - 0x30#64) ⋆ (Reserve k (r - 0x30#64)
        ⋆ ((8 ?@ (r - 0x28#64) ⋆ (4 ?@ (r - 0x20#64) ⋆ (2 ?@ (r - 0x1c#64) ⋆ (2 ?@ (r - 0x1a#64)
        ⋆ (8 ?@ (r - 0x18#64) ⋆ (8 ?@ (r - 0x10#64) ⋆ 8 ?@ (r - 0x8#64))))))) ⋆ K)) := by
  rw [hdrNeed, Reserve_split_frame 0x30 k (by omega) r hw K, frame_split]

omit [CodeEnv] in
theorem toBytes4_ofInt (bs : List UInt8) (h : bs.length = 4) :
    Int.toBytes 4 (BitVec.ofInt 32 (Int.ofBytes bs)).toInt = bs := by
  rw [← Int.toBytes_emod 4 (BitVec.ofInt 32 (Int.ofBytes bs)).toInt]
  have e : ((BitVec.ofInt 32 (Int.ofBytes bs)).toInt).take (8 * 4) = (Int.ofBytes bs).take (8 * 4) := by
    simp only [Int.take, BitVec.toInt_ofInt]
    exact Int.bmod_emod
  rw [e, Int.toBytes_emod, ← h, Int.toBytes_ofBytes_all]

omit [CodeEnv] in
/-- A raw 4-byte slot holds some 32-bit value. -/
theorem slot4_cell {m : Mem 64} {a : BitVec 64} {F : Mem 64 → Prop} (h : m =⋆ 4 ?@ a ⋆ F) :
    ∃ u : BitVec 32, m =⋆ cell4 a u ⋆ F := by
  obtain ⟨_, bs, hlen, h'⟩ := Block.sep_elim h
  refine ⟨BitVec.ofInt 32 (Int.ofBytes bs), ?_⟩
  simp only [cell4, Val]
  rw [toBytes4_ofInt bs hlen]
  exact h'

/-- `MU` without `sbr->usac`. -/
abbrev Mr (k : Nat) (x : HArgs) (ra : Int64) (t₀ : MachineData) (Fm : Mem 64 → Prop) (st : HSt)
    (Tl : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  SbX_us (arg0 t₀) 0#32 st ⋆ (GbW (arg1 t₀) x st.i ⋆ (Blocks [(x.buf, x.L)] ⋆ (Tl ⋆ (Fm
    ⋆ (8 ?@ (r - 0x30#64) ⋆ (Reserve k (r - 0x30#64) ⋆ Rest x.R ra t₀))))))

theorem spec (hpl : Program.PlacedIn body) (k : Nat) (hk : k ≤ 2 ^ 32)
    (TlT : BitVec 64 → Mem 64 → Prop) (TlT' : BitVec 32 → BitVec 64 → Mem 64 → Prop)
    (TlC : BitVec 32 → BitVec 64 → Prop) (htl : TlimSpec TlT TlT' TlC k) :
    HdrSpec k TlT TlT' TlC := by
  refine Kraken.Executable.ProcSpec.of_cfg_post_pre (p := body) (table k TlT TlT' TlC)
    (Post' k TlT TlT') var (hblocks := ?_) (hpre := ?_) (hpost := ?_)
  · intro x ra t₀ _
    refine Program.forall_blockAt ?_
    exact
      (.cons (blk_entry k TlT TlT' TlC x ra t₀ _ rfl)
      (.cons (blk_Ld1d k TlT TlT' TlC x ra t₀ _ rfl)
      (.cons (blk_Ld32 k TlT TlT' TlC x ra t₀ _ rfl)
      (.cons (blk_Ld61 k TlT TlT' TlC x ra t₀ _ rfl)
      (.cons (blk_Ld91 k TlT TlT' TlC x ra t₀ _ rfl)
      (.cons (blk_Ldbd k TlT TlT' TlC x ra t₀ _ rfl)
      (.cons (blk_Lde8 k TlT TlT' TlC x ra t₀ _ rfl)
      (.cons (blk_Le1a k TlT TlT' TlC x ra t₀ _ rfl)
      (.cons (blk_Le45 k TlT TlT' TlC x ra t₀ _ rfl)
      (.cons (blk_Le9d k TlT TlT' TlC x ra t₀ _ rfl)
      (.cons (blk_Leca k TlT TlT' TlC x ra t₀ _ rfl)
      (.cons (blk_Lefb k TlT TlT' TlC x ra t₀ _ rfl)
      (.cons (blk_Lf31 k TlT TlT' TlC x ra t₀ _ rfl)
      (.cons (blk_Lf3a k TlT TlT' TlC x ra t₀ _ rfl)
      (.cons (blk_Lf61 k TlT TlT' TlC x ra t₀ _ rfl)
      (.cons (blk_Lf6d k TlT TlT' TlC x ra t₀ _ rfl)
      (.cons (blk_Lf98 k TlT TlT' TlC x ra t₀ _ rfl)
      (.cons (blk_Lfca k TlT TlT' TlC x ra t₀ _ rfl)
      (.cons (blk_Lff8 k TlT TlT' TlC x ra t₀ _ rfl)
      (.cons (blk_L102d k TlT TlT' TlC x ra t₀ _ rfl)
      (.cons (blk_L1054 k TlT TlT' TlC x ra t₀ _ rfl)
      (.cons (blk_L105a k hk TlT TlT' TlC htl x ra t₀ _ rfl)
      (.cons (blk_L1062 k TlT TlT' TlC x ra t₀ _ rfl)
      (.cons (blk_L1065 k TlT TlT' TlC x ra t₀ _ rfl)
      (.cons (blk_done k TlT TlT' TlC x ra t₀ _ rfl)
      (.nil _))))))))))))))))))))))))))
  · rintro x ra t ⟨hcall, hc⟩
    refine ⟨rfl, hc, ?_⟩
    have hw : 0x30 ≤ (t.regs.get64 .rsp).toNat := by
      have := CallPre.le hcall; unfold hdrNeed at this; omega
    simp only [CallPre] at hcall
    rw [need_split k _ hw] at hcall
    have h4 : t.dmem =⋆ 4 ?@ (arg0 t + 0x10#64) ⋆ Mr k x ra t (FrB t) x.st (TlT (arg0 t)) := by
      simp only [Mr, SbX_us, GbW, Rest, HF, SbW, HArgs.st, FrB, L0] at hcall ⊢
      exact Mem.ac hcall
    obtain ⟨u, hu⟩ := slot4_cell h4
    refine ⟨u, ?_⟩
    simp only [Mr, SbX_us, GbW, Rest, MU, MtU, SbWu, HArgs.st, FrB, L0] at hu ⊢
    exact Mem.ac hu
  · rintro x ra t₀ s ⟨hcall, -⟩ ⟨hsp, hbp, hsv, st, hO, hm⟩
    have hw : 0x30 ≤ (t₀.regs.get64 .rsp).toNat := by
      have := CallPre.le hcall; unfold hdrNeed at this; omega
    refine ⟨st, hO, hsp, hbp, hsv, ?_⟩
    rw [need_split k _ hw]
    simp only [Mt, MtU, usacOf, HFu, FrB, L0] at hm ⊢
    exact Mem.ac hm

end Kraken.Examples.Sbr.Hdr
