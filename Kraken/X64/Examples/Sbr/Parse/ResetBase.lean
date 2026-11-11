import Kraken.X64.Examples.Sbr.Parse.ResetSpec
import Kraken.X64.Examples.Sbr.Parse.ResetLib

/-!
# `sbr_reset`: the memory at the labels

* `St`: the values between blocks: the decoder values `x`, `spectrum_params`, and the raw
  fields with values (`k[1]`, `k[2]`, `n_master`, `f_master`).
* The frame: the `0x548` bytes of locals are one region `fr` at `rsp₀ - 0x578`
  (`rbp - 0x570`); the slot `rbp - d` is at offset `rb d = 0x570 - d` (`region_load`,
  `region_store` of `ResetLib.lean`). Layout (rbp-relative): the `AV_QSORT` stack
  `[-0x570, -0x170)` (64 pairs of pointers), `vk0[49]` `[-0x170, -0x10e)`, `-0x100` (16),
  `vk1[49]` `[-0xf0, -0x8e)`, `-0x88` (8), `-0x80` (16), `stop_dk[13]` `[-0x70, -0x56)`,
  `-0x50`, `-0x48`, `-0x40`, `-0x38`, `-0x30` (8 each).
* `Mm` (`ResetFoot.lean`, generated): the memory at every label inside the body.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

namespace Kraken.Examples.Sbr.Reset

/-- The values between blocks. -/
structure St where
  x : Args
  sp : List UInt8
  /-- `k[1]`, `k[2]` (`sbr + 0x44`, `+ 0x48`), `n_master` (`+ 0x68`). -/
  k1 : BitVec 32
  k2 : BitVec 32
  nm : BitVec 32
  /-- `f_master[49]` (`sbr + 0x4c1f0`, 98 bytes). -/
  fm : List UInt8

/-- Offset in the frame region of the slot `rbp - d`. -/
abbrev rb (d : Nat) : Nat := 0x570 - d

variable [CodeEnv]

/-- The six pushes (`rbp`, `r15`, `r14`, `r13`, `r12`, `rbx`) with the entry values. -/
def Saved (t₀ : MachineData) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14) ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12) ⋆ c8 (r - 0x30#64) (t₀.regs.get64 .rbx)))))

/-- `rsp`/`rbp` inside the body. -/
abbrev Base (t₀ s : MachineData) : Prop :=
  s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x578#64 ∧ s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64

/-- The frame region's length. -/
abbrev FrOk (fr : List UInt8) : Prop := fr.length = 0x548

/-- An `int`-sized frame slot read as a number. -/
abbrev frSlot32 (fr : List UInt8) (d : Nat) : BitVec 32 :=
  BitVec.ofInt 32 (Int.ofBytes (slice fr (rb d) 4))

abbrev frSlot64 (fr : List UInt8) (d : Nat) : BitVec 64 :=
  BitVec.ofInt 64 (Int.ofBytes (slice fr (rb d) 8))

end Kraken.Examples.Sbr.Reset
