import Kraken.X64.Examples.Sbr.ApplySpec
import Kraken.X64.Examples.Sbr.Parse.DecExtSpec

/-!
# Footprint conversion for `ff_aac_sbr_apply`: the scalars and the tables of `*sbr`

* `DecExt.SbrS` (the parser's scalars of `*sbr`) is apply's `ScW` with `sbr->usac` typed
  (raw in `ScW`), `spectrum_params` as one 6-byte cell (two cells in `ScW`), and the bytes `ScW`
  does not own (`GapS`: `inter_tes`, `bs_amp_res_header`, `bs_limiter_bands`, padding).
* `DecExt.TabF` is apply's `TabW` with `f_master` and a padding pair (`GapT`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply

namespace Kraken.Examples.Sbr.SessionBin

/-- `ScW` without the raw `sbr->usac` cell, at `s`. -/
abbrev ScA (x : Args) (s : BitVec 64) : Mem 64 → Prop :=
  cell4 s x.sampleRate ⋆ (cell4 (s + 0x4#64) x.start ⋆ (cell4 (s + 0x8#64) x.ready
    ⋆ (cell4 (s + 0xc#64) x.idAac ⋆ (cell4 (s + 0x18#64) x.reset
    ⋆ (cell4 (s + 0x1c#64) x.spLo ⋆ (Int.toBytes 2 x.spHi.toInt =@ (s + 0x20#64)
    ⋆ (c4 (s + 0x30#64) x.limGains ⋆ (cell4 (s + 0x34#64) x.interpol
    ⋆ (cell4 (s + 0x38#64) x.smooth ⋆ (cell4 (s + 0x3c#64) x.coupling
    ⋆ (c4 (s + 0x40#64) x.k0 ⋆ (c4 (s + 0x54#64) x.kx0 ⋆ (c4 (s + 0x58#64) x.kx1
    ⋆ (c4 (s + 0x5c#64) x.m0 ⋆ (c4 (s + 0x60#64) x.m1
    ⋆ cell4 (s + 0x64#64) x.pushed)))))))))))))))

theorem fa_scw (x : Args) (t : MachineData) :
    ScW x t = 4 ?@ (sbrA t + 0x10#64) ⋆ ScA x (sbrA t) := by
  simp only [ScW, ScA]; generalize sbrA t = s; ac_rfl

/-- The scalar bytes of `*sbr` the parser owns and `ScW` does not: `inter_tes` (+0x14), padding
(+0x22), `bs_amp_res_header` (+0x24), padding (+0x28), `bs_limiter_bands` (+0x2c), +0x44
(16 bytes), +0x68 (0x18 bytes). -/
def GapS (it amp : BitVec 32) (lb : Nat) (s : BitVec 64) : Mem 64 → Prop :=
  cell4 (s + 0x14#64) it ⋆ (2 ?@ (s + 0x22#64) ⋆ (cell4 (s + 0x24#64) amp
    ⋆ (4 ?@ (s + 0x28#64) ⋆ (c4 (s + 0x2c#64) lb ⋆ (16 ?@ (s + 0x44#64)
    ⋆ 0x18 ?@ (s + 0x68#64))))))

theorem fa_sp (lo : BitVec 32) (hi : BitVec 16) (s : BitVec 64) :
    (Int.toBytes 4 lo.toInt ++ Int.toBytes 2 hi.toInt) =@ (s + 0x1c#64)
      = cell4 (s + 0x1c#64) lo ⋆ Int.toBytes 2 hi.toInt =@ (s + 0x20#64) :=
  Val.append_eq _ _ _ _ (by simp only [Int.toBytes_length]; rw [BitVec.add_assoc]; rfl)
    (by simp only [Int.toBytes_length]; omega)

/-- **The scalars**: `SbrS` at values whose six `spectrum_params` bytes are `spLo`, `spHi`. -/
theorem fa_sbrS (d : DecExt.DS) (s : BitVec 64)
    (hsp : d.sp = Int.toBytes 4 d.a.spLo.toInt ++ Int.toBytes 2 d.a.spHi.toInt) :
    DecExt.SbrS d s = cell4 (s + 0x10#64) d.usac ⋆ (ScA d.a s ⋆ GapS d.it d.amp d.h.lb s) := by
  simp only [DecExt.SbrS, hsp, fa_sp, ScA, GapS]
  ac_rfl

/-- The table bytes the parser owns and `TabW` does not: `f_master` (98 bytes) and the two
bytes before `num_patches`. -/
def GapT (s : BitVec 64) : Mem 64 → Prop := 98 ?@ (s + 0x4c1f0#64) ⋆ 2 ?@ (s + 0x4c32e#64)

/-- **The tables.** -/
theorem fa_tabF (x : Args) (t : MachineData) :
    DecExt.TabF x (sbrA t) = TabW x t ⋆ GapT (sbrA t) := by
  simp only [DecExt.TabF, TabW, GapT]; generalize sbrA t = s; ac_rfl

variable [CodeEnv] in
/-- A 4-byte cell forgets its contents. -/
theorem fa_cell4_blk {a : BitVec 64} {v : BitVec 32} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (cell4 a v ⋆ R) m) : (4 ?@ a ⋆ R) m := by
  rw [block_eq_exists a 4 (by decide)]
  obtain ⟨m₁, m₂, hd, hm, h₁, h₂⟩ := h
  exact ⟨m₁, m₂, hd, hm, ⟨v, h₁⟩, h₂⟩

variable [CodeEnv] in
/-- Four raw bytes hold some 32-bit value. -/
theorem fa_blk_cell4 {a : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64} (h : (4 ?@ a ⋆ R) m) :
    ∃ v : BitVec 32, (cell4 a v ⋆ R) m := by
  rw [block_eq_exists a 4 (by decide)] at h
  obtain ⟨m₁, m₂, hd, hm, ⟨v, h₁⟩, h₂⟩ := h
  exact ⟨v, m₁, m₂, hd, hm, h₁, h₂⟩

end Kraken.Examples.Sbr.SessionBin
