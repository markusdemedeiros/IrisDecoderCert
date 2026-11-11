import Kraken.X64.Examples.Sbr.Parse.InvfText
import Kraken.X64.Examples.Sbr.ParseModel

/-!
# `read_sbr_invf`: the specification

`read_sbr_invf(sbr, gb, ch_data)` (`libavcodec/aacsbr_template.c`, FFmpeg n8.1, l.827-835):
`bs_invf_mode[1] = bs_invf_mode[0]`, then `n_q` 2-bit values from `gb` into
`bs_invf_mode[0]`.

* Logical variables `IArgs`: the caller's memory `R`, `sbr->n_q`, the 10 bytes
  `ch_data->bs_invf_mode` (at `ch_data + 0x27`), and the bit reader as for the header.
* The post is `ParseModel.invfRead`'s `bs_invf_mode` for some values `vals` (`invf_model`),
  and the reader's `index` within `size_in_bits_plus8`.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply

namespace Kraken.Examples.Sbr.Invf

open Kraken.Examples.Sbr.ParseModel (mk old invfRead)

structure IArgs where
  R : Mem 64 → Prop
  nq : Nat
  inv : List UInt8
  buf : BitVec 64
  idx : BitVec 32
  p8 : BitVec 32
  L : Nat

variable [CodeEnv]

/-- `*gb` at `g` with `index = i` (`size_in_bits` raw). -/
abbrev GbW (g : BitVec 64) (x : IArgs) (i : BitVec 32) : Mem 64 → Prop :=
  Int.toBytes 8 x.buf.toInt =@ g ⋆ (cell4 (g + 8#64) i ⋆ (4 ?@ (g + 0xc#64)
    ⋆ cell4 (g + 0x10#64) x.p8))

/-- The footprint with `bs_invf_mode = inv` and `index = i`. -/
abbrev IF (x : IArgs) (t : MachineData) (inv : List UInt8) (i : BitVec 32) : Mem 64 → Prop :=
  c4 (arg0 t + 0x4c1e8#64) x.nq ⋆ (inv =@ (arg2 t + 0x27#64) ⋆ (GbW (arg1 t) x i
    ⋆ Blocks [(x.buf, x.L)]))

/-- The side conditions: `n_q ≤ 5` (`Scal`), the array is 10 bytes, the reader's bounds. -/
def InvfC (x : IArgs) : Prop :=
  x.nq ≤ 5 ∧ x.inv.length = 10
  ∧ x.idx.toNat ≤ x.p8.toNat ∧ x.p8.toNat < 2 ^ 31 ∧ x.p8.toNat / 8 + 4 ≤ x.L ∧ x.L < 2 ^ 32

/-- `bs_invf_mode` after the routine, as `invfRead` builds it. -/
def invfNew (nq : Nat) (inv : List UInt8) (vals : Nat → Nat) : List UInt8 :=
  mk 10 (fun i => if i < 5 then (if i < nq then UInt8.ofNat (vals i % 4) else old inv i)
    else old inv (i - 5))

abbrev InvfPre (x : IArgs) (ra : Int64) (t : MachineData) : Prop :=
  CallPre 0 (IF x t x.inv x.idx ⋆ x.R) ra t ∧ InvfC x

abbrev InvfPost (x : IArgs) (ra : Int64) (t s : MachineData) : Prop :=
  ∃ (vals : Nat → Nat) (i : BitVec 32), x.idx.toNat ≤ i.toNat ∧ i.toNat ≤ x.p8.toNat
    ∧ CallPost 0 (IF x t (invfNew x.nq x.inv vals) i ⋆ x.R) ra t s

abbrev InvfSpec : Prop :=
  cenv.ProcSpec (entry "read_sbr_invf") InvfPre InvfPost

omit [CodeEnv] in
/-- The link to the model: the new bytes are `invfRead`'s. -/
theorem invf_model (nq : Nat) (v : DV) (vals : Nat → Nat) :
    invfNew nq v.invf vals = (invfRead nq v vals).invf := rfl

end Kraken.Examples.Sbr.Invf
