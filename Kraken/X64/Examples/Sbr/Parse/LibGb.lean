import Kraken.X64.Examples.Sbr.Parse.Lib

/-!
# The bit reader (`GetBitContext`, `libavcodec/get_bits.h`)

`GetBitContext` at `g`: `buffer` (+0), `index` (+8), `size_in_bits` (+0xc, not read by the
inlined readers), `size_in_bits_plus8` (+0x10). The inlined readers of the parsers:

* `get_bits(gb, n)` (n constant or in `%cl`): a 4-byte unaligned load at `buffer + index / 8`,
  `bswap`, `shl %cl` by `index & 7`, `shr` by `32 - n`; then `index' = min(index + n, plus8)`
  computed as `add $n; cmp; cmovb`.
* `get_bits1(gb)`: a 1-byte load at `buffer + index / 8`, `shl %cl`, `shr $7`; then
  `index' = index + (index < plus8)` computed as `xor; cmp; setl; add`.

The bitstream contents are not constrained: the loaded value is havocked (`bswap32_havoc`,
`shl_cl32_havoc`), and only its bound after the final shift is used (`shr30_lt`, `shr_lt`).
What the proofs need is (1) the load in bounds, from `GbC` (`rd_off`), and (2) the new index
`≤ plus8` (`gb_clamp`, `gb_clamp64` for `get_bits`).

Usage in a block: bring `GbW` to the front (`T_gb` of the footprint), rewrite the three loads
of `*gb` with `gb_load_idx`/`gb_load_buf`/`gb_load_p8` (`simp only [..., Option.some.injEq] at *;
subst_vars; simp only [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt64_ofBytes_toBytes8] at *`),
the buffer load with `rd_off` + `blocks_load`, the index store with `gb_store_idx`, and close
the index bound with `gb_clamp`/`gb_clamp64`.
-/

open Kraken MachineWP Std.WP Lean.Order Mem Kraken.SysV Kraken.Examples.Sbr

namespace Kraken.Examples.Sbr.Parse

/-- `*gb` at `g` with `buffer = buf`, `index = i`, `size_in_bits_plus8 = p8`
(`size_in_bits` raw). -/
abbrev GbW (g buf : BitVec 64) (i p8 : BitVec 32) : Mem 64 → Prop :=
  cell8 g buf ⋆ (cell4 (g + 8#64) i ⋆ (4 ?@ (g + 0xc#64) ⋆ cell4 (g + 0x10#64) p8))

/-- The reader's precondition: `index ≤ size_in_bits_plus8 < 2^31`, and the caller owns
`[buffer, buffer + L)` with `size_in_bits_plus8 / 8 + 4 ≤ L` (every read loads at most 4 bytes
at `buffer + index / 8`; in the decoder `L` is the packet size plus the input padding). -/
def GbC (i p8 : BitVec 32) (L : Nat) : Prop :=
  i.toNat ≤ p8.toNat ∧ p8.toNat < 2 ^ 31 ∧ p8.toNat / 8 + 4 ≤ L

theorem gb_load_buf {m : Mem 64} {g buf : BitVec 64} {i p8 : BitVec 32} {F : Mem 64 → Prop}
    (h : m =⋆ GbW g buf i p8 ⋆ F) :
    m.loadInt g 8 = some (Int.ofBytes (Int.toBytes 8 buf.toInt)) := by
  obtain ⟨F', h'⟩ := pick_ll h
  exact cell8_load h'

theorem gb_load_idx {m : Mem 64} {g buf : BitVec 64} {i p8 : BitVec 32} {F : Mem 64 → Prop}
    (h : m =⋆ GbW g buf i p8 ⋆ F) :
    m.loadInt (g + 8#64) 4 = some (Int.ofBytes (Int.toBytes 4 i.toInt)) := by
  obtain ⟨F', h'⟩ := pick_lr h
  obtain ⟨F'', h''⟩ := pick_ll h'
  exact cell4_load h''

theorem gb_load_p8 {m : Mem 64} {g buf : BitVec 64} {i p8 : BitVec 32} {F : Mem 64 → Prop}
    (h : m =⋆ GbW g buf i p8 ⋆ F) :
    m.loadInt (g + 16#64) 4 = some (Int.ofBytes (Int.toBytes 4 p8.toInt)) := by
  obtain ⟨F', h'⟩ := pick_lr h
  obtain ⟨F'', h''⟩ := pick_lr h'
  obtain ⟨F''', h'''⟩ := pick_lr h''
  exact cell4_load h'''

theorem GbW_idx (g buf : BitVec 64) (i p8 : BitVec 32) (F : Mem 64 → Prop) :
    GbW g buf i p8 ⋆ F
      = cell4 (g + 8#64) i ⋆ ((cell8 g buf ⋆ (4 ?@ (g + 0xc#64) ⋆ cell4 (g + 0x10#64) p8)) ⋆ F) := by
  simp only [GbW]; ac_rfl

/-- Storing the index. -/
theorem gb_store_idx {m : Mem 64} {g buf : BitVec 64} {i p8 : BitVec 32} {F : Mem 64 → Prop}
    (h : m =⋆ GbW g buf i p8 ⋆ F) (v : BitVec 32) :
    m.storeInt (g + 8#64) 4 v.toInt =⋆ GbW g buf v p8 ⋆ F := by
  rw [GbW_idx] at h ⊢
  exact cell4_store h v

/-- The load of `get_bits`/`get_bits1` is inside the buffer: `buffer + (index >> 3)`, 4 bytes. -/
theorem rd_off (i p : BitVec 32) (L : Nat) (hi : i.toNat ≤ p.toNat) (hL : p.toNat / 8 + 4 ≤ L) :
    ((i.ushiftRight 3).setWidth 64).toNat + 4 ≤ L := by
  rw [BitVec.toNat_setWidth, BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight]
  have := i.isLt
  rw [Nat.mod_eq_of_lt (by omega)]; omega

/-- `rd_off` for a 1-byte load. -/
theorem rd_off1 (i p : BitVec 32) (L : Nat) (hi : i.toNat ≤ p.toNat) (hL : p.toNat / 8 + 4 ≤ L) :
    ((i.ushiftRight 3).setWidth 64).toNat + 1 ≤ L := by
  have := rd_off i p L hi hL; omega

/-- The value of `get_bits(gb, 2)`. -/
theorem shr30_lt (v : BitVec 32) : (v >>> 30).toNat < 4 := by
  rw [BitVec.toNat_ushiftRight]; have := v.isLt; omega

/-- The value of `get_bits(gb, n)`, `n ≤ 32`. -/
theorem shr_lt (v : BitVec 32) (n : Nat) (hn : n ≤ 32) : (v >>> (32 - n)).toNat < 2 ^ n := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := v.isLt
  apply Nat.div_lt_of_lt_mul
  rw [← Nat.pow_add, Nat.sub_add_cancel hn]; exact this

/-- The value of `get_bits1` (`shr $7` of a byte). -/
theorem shr7_lt (v : BitVec 8) : (v >>> 7).toNat < 2 := by
  rw [BitVec.toNat_ushiftRight]; have := v.isLt; omega

/-- The index update of `get_bits` (`cmp i', p8; cmovb p8, i'`): the new index is at most
`size_in_bits_plus8`. The form is the one `vcgen` leaves. -/
theorem gb_clamp (p i' : BitVec 32) (af of : Bool) :
    (if CondCode.c.interp (StatusFlags.from_result (p - i')
        { cf := (p - i').unsigned != p.unsigned - i'.unsigned, af := af, of := of }) = true
      then p else i').toNat ≤ p.toNat := by
  split
  · exact Nat.le_refl _
  · rename_i h
    simp only [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, bne_iff_ne, ne_eq,
      Decidable.not_not] at h
    rw [BitVec.toNat_sub] at h
    have := p.isLt; have := i'.isLt
    omega

theorem gb_clamp64 (p i' : BitVec 32) (af of : Bool) :
    (BitVec.setWidth 64 (if CondCode.c.interp (StatusFlags.from_result (p - i')
        { cf := (p - i').unsigned != p.unsigned - i'.unsigned, af := af, of := of }) = true
      then p else i')).toNat ≤ p.toNat := by
  rw [BitVec.toNat_setWidth]
  have := gb_clamp p i' af of
  have := (if CondCode.c.interp (StatusFlags.from_result (p - i')
        { cf := (p - i').unsigned != p.unsigned - i'.unsigned, af := af, of := of }) = true
      then p else i').isLt
  omega

/-- The index update of `get_bits1` (`xor r, r; cmp i, p8; setl r8; add r, i`): the new index
is at most `size_in_bits_plus8`. The form is the one `vcgen` leaves. -/
theorem gb1_idx (i p r : BitVec 32) (cf af : Bool) (hi : i.toNat ≤ p.toNat)
    (hp : p.toNat < 2 ^ 31) :
    (i + BitVec.setWidth 32 ((BitVec.setWidth 64 (r ^^^ r)).replaceLow
      (BitVec.ofNat 8 (CondCode.l.interp (StatusFlags.from_result (i - p)
        { cf := cf, af := af, of := (i - p).signed != i.signed - p.signed })).toNat))).toNat
      ≤ p.toNat := by
  rw [CondCode.interp_l_cmp_toInt32, BitVec.xor_self]
  have hi' : i.toInt = i.toNat := by
    rw [BitVec.toInt_eq_toNat_of_lt]; omega
  have hp' : p.toInt = p.toNat := by
    rw [BitVec.toInt_eq_toNat_of_lt]; omega
  rw [hi', hp']
  by_cases h : (i.toNat : Int) < p.toNat
  · simp only [h, decide_true, Bool.toNat_true]
    have e : BitVec.setWidth 32 ((BitVec.setWidth 64 (0#32)).replaceLow (BitVec.ofNat 8 1)) = 1#32 := by
      decide
    rw [e]; bv_omega
  · simp only [h, decide_false, Bool.toNat_false]
    have e : BitVec.setWidth 32 ((BitVec.setWidth 64 (0#32)).replaceLow (BitVec.ofNat 8 0)) = 0#32 := by
      decide
    rw [e]; bv_omega

end Kraken.Examples.Sbr.Parse
