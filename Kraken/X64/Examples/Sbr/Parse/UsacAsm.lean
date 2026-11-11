import Kraken.X64.Examples.Sbr.Parse.UsacModel
import Kraken.X64.Examples.Sbr.Parse.UsacBlk1
import Kraken.X64.Examples.Sbr.Parse.UsacBlk10
import Kraken.X64.Examples.Sbr.Parse.UsacBlk11
import Kraken.X64.Examples.Sbr.Parse.UsacBlk12
import Kraken.X64.Examples.Sbr.Parse.UsacBlk13
import Kraken.X64.Examples.Sbr.Parse.UsacBlk14
import Kraken.X64.Examples.Sbr.Parse.UsacBlk15
import Kraken.X64.Examples.Sbr.Parse.UsacBlk16
import Kraken.X64.Examples.Sbr.Parse.UsacBlk17
import Kraken.X64.Examples.Sbr.Parse.UsacBlk18
import Kraken.X64.Examples.Sbr.Parse.UsacBlk19
import Kraken.X64.Examples.Sbr.Parse.UsacBlk2
import Kraken.X64.Examples.Sbr.Parse.UsacBlk20
import Kraken.X64.Examples.Sbr.Parse.UsacBlk21
import Kraken.X64.Examples.Sbr.Parse.UsacBlk22
import Kraken.X64.Examples.Sbr.Parse.UsacBlk23
import Kraken.X64.Examples.Sbr.Parse.UsacBlk24
import Kraken.X64.Examples.Sbr.Parse.UsacBlk25
import Kraken.X64.Examples.Sbr.Parse.UsacBlk3
import Kraken.X64.Examples.Sbr.Parse.UsacBlk4
import Kraken.X64.Examples.Sbr.Parse.UsacBlk5
import Kraken.X64.Examples.Sbr.Parse.UsacBlk6
import Kraken.X64.Examples.Sbr.Parse.UsacBlk7
import Kraken.X64.Examples.Sbr.Parse.UsacBlk8
import Kraken.X64.Examples.Sbr.Parse.UsacBlk9
import Kraken.X64.Examples.Sbr.Parse.UsacCall
import Kraken.X64.Examples.Sbr.Parse.UsacCall2
import Kraken.X64.Examples.Sbr.Parse.UsacCp1
import Kraken.X64.Examples.Sbr.Parse.UsacCp2
import Kraken.X64.Examples.Sbr.Parse.UsacCp3
import Kraken.X64.Examples.Sbr.Parse.UsacCp4
import Kraken.X64.Examples.Sbr.Parse.UsacGC1
import Kraken.X64.Examples.Sbr.Parse.UsacGrd2

/-!
# `ff_aac_sbr_decode_usac_data`: the assembly

`ProcSpecA.of_cfg_post` over the blocks of `body` with the table of `UsacBase.lean`. Every block is
proved in `Usac*.lean`.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

namespace Kraken.Examples.Sbr.Usac

variable [CodeEnv]


omit [CodeEnv] in
theorem rsub (r : BitVec 64) (a b : Nat) :
    r - BitVec.ofNat 64 a - BitVec.ofNat 64 b = r - BitVec.ofNat 64 (a + b) := by
  rw [BitVec.sub_sub, BitVec.ofNat_add]

omit [CodeEnv] in
/-- The caller's reservation as the frame's slots. -/
theorem reserve_frame (n : Nat) (r : BitVec 64) (hr : 0x50 ≤ r.toNat) :
    Reserve (0x50 + n) r = 8 ?@ (r - 0x50#64) ⋆ (Reserve n (r - 0x50#64) ⋆ (LocR r ⋆ Bs r)) := by
  rw [Reserve_split 0x50 n r hr]
  have e : (0x50 : Nat) = 8 + (8 + (8 + (8 + (8 + (8 + (4 + (2 + (2 + (4 + (12 + 8)))))))))) := by
    omega
  rw [e]
  repeat rw [block_split_top _ _ _ (by omega)]
  simp only [rsub, Bs, LocR]
  try simp only [Nat.reduceAdd]
  ac_rfl

theorem usac_hpre (k : Nat) (A : UA) (ra : Int64) (t : MachineData)
    (h : UsacPre k A ra t) : table k A ra t "ff_aac_sbr_decode_usac_data" t := by
  obtain ⟨hm, hc, h0, h1, h2, h3, h4⟩ := h
  have hr : 0x50 ≤ (t.regs.get64 .rsp).toNat := by
    have := CallPre.le hm; simp only [usacNeed, cneed, Grid.gridNeed] at this; omega
  refine ⟨rfl, ⟨hc, h0, h1, h2, h3, h4⟩, ?_⟩
  have e : RetCell ra (t.regs.get64 .rsp) ⋆ (Reserve (usacNeed k) (t.regs.get64 .rsp)
      ⋆ (UF A.1 A.2 ⋆ A.1.R))
      = UM k A ra t (LocR (t.regs.get64 .rsp)) (Bs (t.regs.get64 .rsp)) A.2 := by
    simp only [UM, usacNeed, reserve_frame (cneed k) _ hr]
    ac_rfl
  exact e ▸ hm

theorem usac_hpost (k : Nat) (A : UA) (ra : Int64) (t s : MachineData)
    (hp : UsacPre k A ra t) (h : Post' k A ra t s) : UsacPost k A ra t s := by
  have hr : 0x50 ≤ (t.regs.get64 .rsp).toNat := by
    have := CallPre.le hp.1; simp only [usacNeed, cneed, Grid.gridNeed] at this; omega
  obtain ⟨st, ho, h1, h2, h3, hm⟩ := h
  refine ⟨st, ho, h1, h2, h3, ?_⟩
  have e : 8 ?@ (t.regs.get64 .rsp) ⋆ (Reserve (usacNeed k) (t.regs.get64 .rsp)
      ⋆ (UF A.1 st ⋆ A.1.R)) = 8 ?@ (t.regs.get64 .rsp - 0x50#64) ⋆ (Reserve (cneed k)
        (t.regs.get64 .rsp - 0x50#64) ⋆ (UF A.1 st ⋆ (LocR (t.regs.get64 .rsp)
        ⋆ (Bs (t.regs.get64 .rsp) ⋆ (8 ?@ (t.regs.get64 .rsp) ⋆ A.1.R))))) := by
    simp only [usacNeed, reserve_frame (cneed k) _ hr]
    ac_rfl
  exact e ▸ hm

/-- The logical variable with the callees' states `Ext`, `Oth`. -/
abbrev UA.fix (Ext Oth : Mem 64 → Prop) (A : UA) : UA := ({ A.1 with Ext := Ext, Oth := Oth }, A.2)

/-- The routine at every logical variable with its callees' states replaced by `Ext`, `Oth`. -/
theorem usacSpec_fix (k : Nat) (_hk : k ≤ 2 ^ 32) (Ext Oth : Mem 64 → Prop)
    (hc : UsacCallees k Ext Oth) (hpl : Program.PlacedIn body) :
    ProcSpecS usacStops (entry "ff_aac_sbr_decode_usac_data")
      (fun (A : UA) => UsacPre k (A.fix Ext Oth))
      (fun (A : UA) => UsacPost k (A.fix Ext Oth)) := by
  refine ProcSpecS.of_cfg_postP (p := body) (fun (A : UA) => table k (A.fix Ext Oth))
    (fun (A : UA) => Post' k (A.fix Ext Oth)) var (hblocks := ?_)
    (hpre := fun (A : UA) => usac_hpre k (A.fix Ext Oth))
    (hpost := fun (A : UA) => usac_hpost k (A.fix Ext Oth)) (hwf := by decide +kernel)
  intro A ra t₀ l blk hblk
  have hmem := Program.isSome_blockAt body l
  cfg_view hblk as hview
  rw [hblk, hview] at hmem
  replace hmem := hmem.symm
  clear hview
  simp only [Option.isSome_some, List.map_cons, List.map_nil, List.contains_cons,
    List.contains_nil, Bool.or_false, Bool.or_eq_true, beq_iff_eq] at hmem
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl := hmem
  · exact (blk_entry k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L3361 k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L3388 k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L33a3 k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L33ba k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L33e6 k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L3410 k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L343d k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L3475 k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L34b0 k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L34dd k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L34f7 k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L350f k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L3523 k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L353a k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L354e k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L3569 k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L358e k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L359b k (A.fix Ext Oth) ra t₀ hc.2.2.1) blk hblk
  · exact (blk_L35a3 k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L35a5 k (A.fix Ext Oth) ra t₀ hc.2.1) blk hblk
  · exact (blk_L35b5 k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L35bf k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L35d7 k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L35ea k (A.fix Ext Oth) ra t₀ hc.2.2.2.1) blk hblk
  · exact (blk_L35f5 k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L3609 k (A.fix Ext Oth) ra t₀ hc.1) blk hblk
  · exact (blk_L3621 k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L3630 k (A.fix Ext Oth) ra t₀ hc.2.2.2.2.1) blk hblk
  · exact (blk_L3644 k (A.fix Ext Oth) ra t₀ hc.2.2.2.2.2.2.1) blk hblk
  · exact (blk_L3652 k (A.fix Ext Oth) ra t₀ hc.2.2.2.2.2.2.2.2.1) blk hblk
  · exact (blk_L3666 k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L366e k (A.fix Ext Oth) ra t₀ hc.2.2.2.2.2.2.2.2.2.2.1) blk hblk
  · exact (blk_L3682 k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L368a k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L36c0 k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L36c7 k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L36fa k (A.fix Ext Oth) ra t₀ hc.1) blk hblk
  · exact (blk_L3715 k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L3724 k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L3734 k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L3750 k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L3763 k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L377f k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L379a k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L37b3 k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L37cb k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L37e3 k (A.fix Ext Oth) ra t₀ hc.2.2.2.2.1) blk hblk
  · exact (blk_L37fe k (A.fix Ext Oth) ra t₀ hc.2.2.2.2.2.1) blk hblk
  · exact (blk_L3819 k (A.fix Ext Oth) ra t₀ hc.2.2.2.2.2.2.1) blk hblk
  · exact (blk_L382e k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L3847 k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L3860 k (A.fix Ext Oth) ra t₀ hc.2.2.2.2.2.2.2.2.1) blk hblk
  · exact (blk_L3874 k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L387c k (A.fix Ext Oth) ra t₀ hc.2.2.2.2.2.2.2.2.2.2.1) blk hblk
  · exact (blk_L3890 k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L3898 k (A.fix Ext Oth) ra t₀ hc.2.2.2.2.2.2.2.2.2.1) blk hblk
  · exact (blk_L38b6 k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L38be k (A.fix Ext Oth) ra t₀ hc.2.2.2.2.2.2.2.2.2.2.2) blk hblk
  · exact (blk_L38d5 k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L38dd k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L3913 k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L3933 k (A.fix Ext Oth) ra t₀ hc.1) blk hblk
  · exact (blk_L394e k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L395d k (A.fix Ext Oth) ra t₀ hc.1) blk hblk
  · exact (blk_L3972 k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L3981 k (A.fix Ext Oth) ra t₀ hc.2.2.2.2.1) blk hblk
  · exact (blk_L3999 k (A.fix Ext Oth) ra t₀ hc.2.2.2.2.2.1) blk hblk
  · exact (blk_L39b8 k (A.fix Ext Oth) ra t₀ hc.2.2.2.2.2.2.1) blk hblk
  · exact (blk_L39c6 k (A.fix Ext Oth) ra t₀ hc.2.2.2.2.2.2.2.1) blk hblk
  · exact (blk_L39d8 k (A.fix Ext Oth) ra t₀ hc.2.2.2.2.2.2.2.2.1) blk hblk
  · exact (blk_L39ec k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L39f4 k (A.fix Ext Oth) ra t₀ hc.2.2.2.2.2.2.2.2.2.1) blk hblk
  · exact (blk_L3a0f k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L3a17 k (A.fix Ext Oth) ra t₀ hc.2.2.2.2.2.2.2.2.2.2.1) blk hblk
  · exact (blk_L3a2b k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L3a33 k (A.fix Ext Oth) ra t₀ hc.2.2.2.2.2.2.2.2.2.2.2) blk hblk
  · exact (blk_L3a4e k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L3a56 k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L3a8c k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L3aac k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L3ab1 k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L3ad4 k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L3ae0 k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L3b17 k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L3b61 k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L3b98 k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L3ba2 k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L3bd8 k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L3c1c k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L3c4b k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L3c84 k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L3c9b k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L3ca2 k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L3cac k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L3ce3 k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L3d23 k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L3d2d k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L3d64 k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L3d6e k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L3da4 k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L3de8 k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L3e17 k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L3e50 k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L3e75 k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L3eac k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L3ef1 k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_done k (A.fix Ext Oth) ra t₀) blk hblk
  · exact (blk_L3f00 k (A.fix Ext Oth) ra t₀) blk hblk

/-- **`ff_aac_sbr_decode_usac_data`** from its callees' contracts (with the callees' states
`Ext`, `Oth`), `k ≤ 2^32`, and the placement of the text. -/
theorem usacSpec_holds (k : Nat) (hk : k ≤ 2 ^ 32) (Ext Oth : Mem 64 → Prop)
    (hc : UsacCallees k Ext Oth) (hpl : Program.PlacedIn body) : UsacSpec k Ext Oth := by
  intro A ra t ⟨hp, hE, hO⟩
  have e : A.fix Ext Oth = A := by rw [← hE, ← hO]
  have h := usacSpec_fix k hk Ext Oth hc hpl A ra t
    (by show UsacPre k (A.fix Ext Oth) ra t; rw [e]; exact hp)
  dsimp only at h
  rw [e] at h
  exact h

end Kraken.Examples.Sbr.Usac
