import Kraken.X64.Examples.Sbr.Parse.NoiseVlc

/-!
# `read_sbr_noise`: the entry and exit conversions

`noise_pre`: `NoisePre` (the call convention's `Reserve (0x60 + k)`) gives the table's entry
(the pushes `BlankS` and the locals `Blank` carved off the reservation's top, `frame58`).
`noise_post`: `Post'` gives `NoisePost` (the saved slots forgotten, the frame merged back into
the reservation; `k ≤ 2 ^ 32` keeps `0x60 + k` within the address space).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Vlc

namespace Kraken.Examples.Sbr.Noise

variable [CodeEnv]

omit [CodeEnv] in
/-- The `0x58` bytes of the frame (pushes and locals) as eleven 8-byte slots. -/
theorem frame58 (r : BitVec 64) (K : Mem 64 → Prop) :
    0x58 ?@ (r - 0x58#64) ⋆ K = 8 ?@ (r - 0x58#64) ⋆ (8 ?@ (r - 0x50#64) ⋆ (8 ?@ (r - 0x48#64) ⋆ (8 ?@ (r - 0x40#64) ⋆ (8 ?@ (r - 0x38#64) ⋆ (8 ?@ (r - 0x30#64) ⋆ (8 ?@ (r - 0x28#64) ⋆ (8 ?@ (r - 0x20#64) ⋆ (8 ?@ (r - 0x18#64) ⋆ (8 ?@ (r - 0x10#64) ⋆ (8 ?@ (r - 0x8#64) ⋆ K)))))))))) := by
  rw [show (88 ?@ (r - 0x58#64) : Mem 64 → Prop) = (8 + 80) ?@ (r - 0x58#64) from rfl,
    Block.split (r - 0x58#64) 8 80 (by decide), show r - 0x58#64 + BitVec.ofNat 64 8 = r - 0x50#64 by bv_omega]
  rw [show (80 ?@ (r - 0x50#64) : Mem 64 → Prop) = (8 + 72) ?@ (r - 0x50#64) from rfl,
    Block.split (r - 0x50#64) 8 72 (by decide), show r - 0x50#64 + BitVec.ofNat 64 8 = r - 0x48#64 by bv_omega]
  rw [show (72 ?@ (r - 0x48#64) : Mem 64 → Prop) = (8 + 64) ?@ (r - 0x48#64) from rfl,
    Block.split (r - 0x48#64) 8 64 (by decide), show r - 0x48#64 + BitVec.ofNat 64 8 = r - 0x40#64 by bv_omega]
  rw [show (64 ?@ (r - 0x40#64) : Mem 64 → Prop) = (8 + 56) ?@ (r - 0x40#64) from rfl,
    Block.split (r - 0x40#64) 8 56 (by decide), show r - 0x40#64 + BitVec.ofNat 64 8 = r - 0x38#64 by bv_omega]
  rw [show (56 ?@ (r - 0x38#64) : Mem 64 → Prop) = (8 + 48) ?@ (r - 0x38#64) from rfl,
    Block.split (r - 0x38#64) 8 48 (by decide), show r - 0x38#64 + BitVec.ofNat 64 8 = r - 0x30#64 by bv_omega]
  rw [show (48 ?@ (r - 0x30#64) : Mem 64 → Prop) = (8 + 40) ?@ (r - 0x30#64) from rfl,
    Block.split (r - 0x30#64) 8 40 (by decide), show r - 0x30#64 + BitVec.ofNat 64 8 = r - 0x28#64 by bv_omega]
  rw [show (40 ?@ (r - 0x28#64) : Mem 64 → Prop) = (8 + 32) ?@ (r - 0x28#64) from rfl,
    Block.split (r - 0x28#64) 8 32 (by decide), show r - 0x28#64 + BitVec.ofNat 64 8 = r - 0x20#64 by bv_omega]
  rw [show (32 ?@ (r - 0x20#64) : Mem 64 → Prop) = (8 + 24) ?@ (r - 0x20#64) from rfl,
    Block.split (r - 0x20#64) 8 24 (by decide), show r - 0x20#64 + BitVec.ofNat 64 8 = r - 0x18#64 by bv_omega]
  rw [show (24 ?@ (r - 0x18#64) : Mem 64 → Prop) = (8 + 16) ?@ (r - 0x18#64) from rfl,
    Block.split (r - 0x18#64) 8 16 (by decide), show r - 0x18#64 + BitVec.ofNat 64 8 = r - 0x10#64 by bv_omega]
  rw [show (16 ?@ (r - 0x10#64) : Mem 64 → Prop) = (8 + 8) ?@ (r - 0x10#64) from rfl,
    Block.split (r - 0x10#64) 8 8 (by decide), show r - 0x10#64 + BitVec.ofNat 64 8 = r - 0x8#64 by bv_omega]
  ac_rfl

theorem noise_pre (k : Nat) (Ext : Mem 64 → Prop) :
    ∀ x ra t, NoisePre k Ext x ra t → table k Ext x ra t "read_sbr_noise" t := by
  rintro x ra t ⟨hm, hC⟩
  dsimp only [reduceTable]
  refine ⟨rfl, hC, ?_⟩
  have hw : 0x60 ≤ (t.regs.get64 .rsp).toNat := by
    have := CallPre.le hm; unfold noiseNeed at this; omega
  simp only [CallPre, noiseNeed] at hm
  rw [Reserve_split_frame 0x60 k (by decide) _ hw] at hm
  simp only [Nat.reduceSub, frame58] at hm
  simp only [T, Blank, BlankS, Rest] at hm ⊢
  exact Mem.ac hm


theorem noise_post (k : Nat) (Ext : Mem 64 → Prop) :
    ∀ x ra t₀ s, NoisePre k Ext x ra t₀ → Post' k Ext x ra t₀ s → NoisePost k Ext x ra t₀ s := by
  rintro x ra t₀ s ⟨hcall, -⟩ ⟨i, hi, hv, h1, h2, h3, hm⟩
  have hw : 0x60 ≤ (t₀.regs.get64 .rsp).toNat := by
    have := CallPre.le hcall; unfold noiseNeed at this; omega
  refine ⟨i, hi, hv, h1, h2, h3, ?_⟩
  have e : ∀ K : Mem 64 → Prop, Mem.Entails (Saved t₀ K) (BlankS (t₀.regs.get64 .rsp) K) :=
    fun K => Mem.Entails.forget8 _ _ (Mem.Entails.forget8 _ _ (Mem.Entails.forget8 _ _
      (Mem.Entails.forget8 _ _ (Mem.Entails.forget8 _ _ (Mem.Entails.forget8 _ _
      (Mem.Entails.refl _))))))
  have hm0 : s.dmem =⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x60#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x60#64)
      ⋆ (Blank t₀ ⋆ NoiseF Ext x t₀ i))) ⋆ Saved t₀ (8 ?@ t₀.regs.get64 .rsp ⋆ x.R) :=
    Mem.ac hm
  have hm1 := Mem.Entails.sep_left (e _) _ hm0
  simp only [noiseNeed]
  rw [Reserve_split_frame 0x60 k (by decide) _ hw]
  simp only [Nat.reduceSub, frame58]
  simp only [Blank, BlankS] at hm1 ⊢
  exact Mem.ac hm1

end Kraken.Examples.Sbr.Noise
