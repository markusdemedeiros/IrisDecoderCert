import Kraken.X64.Examples.Sbr.ApplySpec
import Kraken.X64.Examples.Sbr.Parse.DecExtSpec

/-!
# Footprint conversion for `ff_aac_sbr_apply`: one `SBRData`

`DecExt.DataF` (the parser's view of `sbr->data[ch]`, raw spans for the arrays) is apply's
`DScW` and `DArrW` with the bytes neither of them owns (`GapD`): the raw spans are cut at the
array boundaries of `DArrW`, `e_a[2]` is one 8-byte block.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply

namespace Kraken.Examples.Sbr.SessionBin

/-- A block cut at a literal offset. -/
theorem fa_cut (a b : BitVec 64) (i j : Nat) (hb : b = a + BitVec.ofNat 64 i)
    (hw : i + j ≤ 2 ^ 64) : (i + j) ?@ a = i ?@ a ⋆ j ?@ b := by
  subst hb; exact Block.split a i j hw

/-- The bytes of one `SBRData` at `d` owned by the parser's `DataF` but by neither `DScW` nor
`DArrW`. -/
def GapD (d : BitVec 64) : Mem 64 → Prop :=
  4 ?@ d ⋆ (3 ?@ (d + 0x15#64) ⋆ (11 ?@ (d + 0x1c#64) ⋆ (3 ?@ (d + 0x61#64)
    ⋆ (0x18 ?@ (d + 0x68#64) ⋆ (12 ?@ (d + 0x7924#64) ⋆ (1 ?@ (d + 0x15a5f#64)
    ⋆ (3 ?@ (d + 0x15aa9#64) ⋆ 12 ?@ (d + 0x15ab4#64))))))))

theorem fa_blk3898 (d : BitVec 64) :
    0x3898 ?@ (d + 0x68#64)
      = 0x18 ?@ (d + 0x68#64) ⋆ (9216 ?@ (d + 0x80#64) ⋆ 5248 ?@ (d + 0x2480#64)) := by
  rw [show (0x3898 : Nat) = 0x18 + (9216 + 5248) from rfl,
    fa_cut _ (d + 0x80#64) _ _ (by rw [BitVec.add_assoc]; rfl) (by omega),
    fa_cut _ (d + 0x2480#64) 9216 _ (by rw [BitVec.add_assoc]; rfl) (by omega)]

theorem fa_blk4014 (d : BitVec 64) :
    0x4014 ?@ (d + 0x390c#64) = 20 ?@ (d + 0x390c#64) ⋆ 16384 ?@ (d + 0x3920#64) := by
  rw [show (0x4014 : Nat) = 20 + 16384 from rfl,
    fa_cut _ (d + 0x3920#64) _ _ (by rw [BitVec.add_assoc]; rfl) (by omega)]

theorem fa_blke178 (d : BitVec 64) :
    0xe178 ?@ (d + 0x7924#64) = 12 ?@ (d + 0x7924#64) ⋆ (38936 ?@ (d + 0x7930#64)
      ⋆ (8040 ?@ (d + 0x11148#64) ⋆ (8064 ?@ (d + 0x130b0#64) ⋆ (432 ?@ (d + 0x15030#64)
      ⋆ (432 ?@ (d + 0x151e0#64) ⋆ (1728 ?@ (d + 0x15390#64) ⋆ (15 ?@ (d + 0x15a50#64)
      ⋆ (1 ?@ (d + 0x15a5f#64) ⋆ 60 ?@ (d + 0x15a60#64))))))))) := by
  rw [show (0xe178 : Nat) = 12 + (38936 + (8040 + (8064 + (432 + (432 + (1728 + (15
      + (1 + 60)))))))) from rfl,
    fa_cut _ (d + 0x7930#64) _ _ (by rw [BitVec.add_assoc]; rfl) (by omega),
    fa_cut _ (d + 0x11148#64) 38936 _ (by rw [BitVec.add_assoc]; rfl) (by omega),
    fa_cut _ (d + 0x130b0#64) 8040 _ (by rw [BitVec.add_assoc]; rfl) (by omega),
    fa_cut _ (d + 0x15030#64) 8064 _ (by rw [BitVec.add_assoc]; rfl) (by omega),
    fa_cut _ (d + 0x151e0#64) 432 _ (by rw [BitVec.add_assoc]; rfl) (by omega),
    fa_cut _ (d + 0x15390#64) 432 _ (by rw [BitVec.add_assoc]; rfl) (by omega),
    fa_cut _ (d + 0x15a50#64) 1728 _ (by rw [BitVec.add_assoc]; rfl) (by omega),
    fa_cut _ (d + 0x15a5f#64) 15 _ (by rw [BitVec.add_assoc]; rfl) (by omega),
    fa_cut _ (d + 0x15a60#64) 1 _ (by rw [BitVec.add_assoc]; rfl) (by omega)]

theorem fa_blk8 (d : BitVec 64) :
    4 ?@ (d + 0x3904#64) ⋆ 4 ?@ (d + 0x3908#64) = 8 ?@ (d + 0x3904#64) :=
  (fa_cut _ _ 4 4 (by rw [BitVec.add_assoc]; rfl) (by omega)).symm

/-- `DataF` with its raw spans cut at `DArrW`'s arrays. -/
abbrev DataCut (v : DV) (d : BitVec 64) : Mem 64 → Prop :=
  4 ?@ d ⋆ (4 ?@ (d + 0x4#64) ⋆ (c4 (d + 0x8#64) v.nenv ⋆ (v.freqRes =@ (d + 0xc#64)
  ⋆ (3 ?@ (d + 0x15#64) ⋆ (c4 (d + 0x18#64) v.nnoise ⋆ (11 ?@ (d + 0x1c#64)
  ⋆ (v.invf =@ (d + 0x27#64) ⋆ (48 ?@ (d + 0x31#64) ⋆ (3 ?@ (d + 0x61#64)
  ⋆ (4 ?@ (d + 0x64#64)
  ⋆ ((0x18 ?@ (d + 0x68#64) ⋆ (9216 ?@ (d + 0x80#64) ⋆ 5248 ?@ (d + 0x2480#64)))
  ⋆ (cell4 (d + 0x3900#64) v.vOff
  ⋆ (8 ?@ (d + 0x3904#64)
  ⋆ ((20 ?@ (d + 0x390c#64) ⋆ 16384 ?@ (d + 0x3920#64))
  ⋆ (c4 (d + 0x7920#64) v.ypos
  ⋆ ((12 ?@ (d + 0x7924#64) ⋆ (38936 ?@ (d + 0x7930#64)
      ⋆ (8040 ?@ (d + 0x11148#64) ⋆ (8064 ?@ (d + 0x130b0#64) ⋆ (432 ?@ (d + 0x15030#64)
      ⋆ (432 ?@ (d + 0x151e0#64) ⋆ (1728 ?@ (d + 0x15390#64) ⋆ (15 ?@ (d + 0x15a50#64)
      ⋆ (1 ?@ (d + 0x15a5f#64) ⋆ 60 ?@ (d + 0x15a60#64))))))))))
  ⋆ (v.te =@ (d + 0x15a9c#64) ⋆ (v.tq =@ (d + 0x15aa6#64)
  ⋆ (3 ?@ (d + 0x15aa9#64) ⋆ (Apply.c8 (d + 0x15aac#64) v.idx ⋆ 12 ?@ (d + 0x15ab4#64)))))))))))))))))))))

theorem fa_dataCut (v : DV) (d : BitVec 64) : DecExt.DataF v d = DataCut v d := by
  simp only [DecExt.DataF, DataCut, fa_blk3898, fa_blke178, fa_blk4014]
  rw [← fa_blk8 d]
  simp only [Std.ExtHashMap.sep_assoc]

/-- `DScW` and `DArrW` at an address `d`. -/
abbrev DScA (v : DV) (d : BitVec 64) : Mem 64 → Prop :=
  4 ?@ (d + 0x4#64) ⋆ (c4 (d + 0x8#64) v.nenv ⋆ (v.freqRes =@ (d + 0xc#64)
    ⋆ (c4 (d + 0x18#64) v.nnoise ⋆ (v.invf =@ (d + 0x27#64) ⋆ (48 ?@ (d + 0x31#64)
    ⋆ (4 ?@ (d + 0x64#64) ⋆ (cell4 (d + 0x3900#64) v.vOff ⋆ (8 ?@ (d + 0x3904#64)
    ⋆ (c4 (d + 0x7920#64) v.ypos ⋆ (v.te =@ (d + 0x15a9c#64) ⋆ (v.tq =@ (d + 0x15aa6#64)
    ⋆ Int.toBytes 8 v.idx.toInt =@ (d + 0x15aac#64))))))))))))

abbrev DArrA (d : BitVec 64) : Mem 64 → Prop :=
  9216 ?@ (d + 0x80#64) ⋆ (5248 ?@ (d + 0x2480#64) ⋆ (20 ?@ (d + 0x390c#64)
    ⋆ (16384 ?@ (d + 0x3920#64) ⋆ (38936 ?@ (d + 0x7930#64) ⋆ (8040 ?@ (d + 0x11148#64)
    ⋆ (8064 ?@ (d + 0x130b0#64)
    ⋆ (432 ?@ (d + 0x15030#64) ⋆ (432 ?@ (d + 0x151e0#64) ⋆ (1728 ?@ (d + 0x15390#64)
    ⋆ (15 ?@ (d + 0x15a50#64) ⋆ 60 ?@ (d + 0x15a60#64)))))))))))

theorem fa_dscw (v : DV) (t : MachineData) (ch : Nat) : DScW v t ch = DScA v (dA t ch) := rfl

theorem fa_darrw (t : MachineData) (ch : Nat) : DArrW t ch = DArrA (dA t ch) := rfl

/-- **One `SBRData`**: the parser's `DataF` is apply's `DScW ⋆ DArrW` and the gap bytes. -/
theorem fa_dataF (v : DV) (t : MachineData) (ch : Nat) :
    DecExt.DataF v (dA t ch) = DScW v t ch ⋆ (DArrW t ch ⋆ GapD (dA t ch)) := by
  rw [fa_dataCut, fa_dscw, fa_darrw]
  simp only [DataCut, DScA, DArrA, GapD, Apply.c8]
  ac_rfl

end Kraken.Examples.Sbr.SessionBin
