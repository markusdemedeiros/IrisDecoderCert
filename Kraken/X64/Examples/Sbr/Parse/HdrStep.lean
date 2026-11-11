import Kraken.X64.Examples.Sbr.Parse.HdrFrame

/-!
# `read_sbr_header`: one field read

A read of a `spectrum_params` byte stores the reader's index and then the byte at
`0x1c + o`; `hdr_step` gives the footprint after both stores. The `u8_set_*` lemmas give the
bytes of the list after the store, `shr_lt` the width of the stored value.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Hdr

open Kraken.Examples.Sbr.HdrLib

theorem shr_lt (v : BitVec 32) (s : Nat) (hs : 24 ≤ s) (hs' : s < 32) :
    (BitVec.setWidth 8 (v.ushiftRight s)).toNat < 2 ^ (32 - s) := by
  rw [BitVec.toNat_setWidth, BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  have := v.isLt
  have h1 : v.toNat / 2 ^ s < 2 ^ (32 - s) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
    rw [show 32 - s + s = 32 by omega]; exact this
  have h2 : 2 ^ (32 - s) ≤ 2 ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  rw [Nat.mod_eq_of_lt (by omega)]; exact h1

theorem u8_set_eq (l : List UInt8) (o : Nat) (b : BitVec 8) (ho : o < l.length) :
    u8 (l.set o (UInt8.ofBitVec b)) o = b.toNat := by
  simp [u8, List.getD_eq_getElem?_getD, ho]

theorem u8_set_ne (l : List UInt8) (o j : Nat) (v : UInt8) (h : j ≠ o) :
    u8 (l.set o v) j = u8 l j := by
  simp only [u8, List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm h)]

theorem getD_set_ne (l : List UInt8) (o j : Nat) (v : UInt8) (h : j ≠ o) :
    (l.set o v).getD j 0 = l.getD j 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm h)]

theorem getD_set_eq (l : List UInt8) (o : Nat) (b : BitVec 8) (ho : o < l.length) :
    ((l.set o (UInt8.ofBitVec b)).getD o 0).toNat = b.toNat := u8_set_eq l o b ho

/-- `xor r, r; …; setl r8`: the flag as a 32-bit value. -/
theorem setl_val (c : Bool) :
    BitVec.setWidth 32 ((0#64).replaceLow (BitVec.ofNat 8 c.toNat))
      = if c then 1#32 else 0#32 := by
  cases c <;> simp [BitVec.replaceLow] <;> decide

/-- The index after `get_bits1`: `index + (index < size_in_bits_plus8)`. -/
theorem bit_idx (i p : BitVec 32) (hi : i.toNat ≤ p.toNat) (hp : p.toNat < 2 ^ 31) :
    i.toNat ≤ (i + if ((i - p).msb != ((i - p).signed != i.signed - p.signed)) then 1#32 else 0#32).toNat
    ∧ (i + if ((i - p).msb != ((i - p).signed != i.signed - p.signed)) then 1#32 else 0#32).toNat
      ≤ p.toNat := by
  by_cases h : i = p
  · subst h; simp
  · have : i.toNat < p.toNat := by
      have : i.toNat ≠ p.toNat := fun e => h (BitVec.eq_of_toNat_eq e)
      omega
    split <;> simp only [BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega

theorem shr7_lt (b : BitVec 8) : (b.ushiftRight 7).toNat < 2 := by
  rw [BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight]; have := b.isLt; omega

/-- A byte write into a 64-bit register, read back. -/
theorem low8 (r : BitVec 64) (b : BitVec 8) : BitVec.setWidth 8 (r.replaceLow b) = b := by
  simp only [BitVec.replaceLow]; exact BitVec.setWidth_append_eq_right

theorem and1_lt (v : BitVec 32) : (v &&& 1#32).toNat < 2 := by
  rw [BitVec.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem spA_set {x : HArgs} {u : BitVec 32} {sp : List UInt8} {amp : BitVec 32}
    (h : SpA x u sp amp) (o : Nat) (ho : 3 ≤ o) (v : UInt8) : SpA x u (sp.set o v) amp := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨by simp only [List.length_set, h1], ?_, ?_, fun hu => ⟨?_, (h4 hu).2⟩,
    fun hu => ⟨?_, (h5 hu).2⟩⟩
  · rw [u8_set_ne _ _ _ _ (by omega)]; exact h2
  · rw [u8_set_ne _ _ _ _ (by omega)]; exact h3
  · rw [u8_set_ne _ _ _ _ (by omega)]; exact (h4 hu).1
  · rw [getD_set_ne _ _ _ _ (by omega)]; exact (h5 hu).1

/-- `movw $0x102, 0x1f(%rdi)`: `bs_freq_scale = 2`, `bs_alter_scale = 1`. -/
theorem sp_102 (l : List UInt8) (hl : l.length = 6) :
    l.take 3 ++ Int.toBytes 2 258 ++ l.drop 5 = (l.set 3 2).set 4 1 := by
  match l, hl with
  | [a0, a1, a2, a3, a4, a5], _ => rfl

theorem low16 (r : BitVec 64) (b : BitVec 16) : BitVec.setWidth 16 (r.replaceLow b) = b := by
  simp only [BitVec.replaceLow]; exact BitVec.setWidth_append_eq_right
/-- The compare of `spectrum_params` (`xor`, `xor`, `or`) is zero only on equal words. -/
theorem or_xor_zero (A B : BitVec 16) (C D : BitVec 32)
    (h : (BitVec.setWidth 32 (A ^^^ B) ||| (C ^^^ D)) = 0#32) : A = B ∧ C = D := by
  constructor
  · ext i hi
    have := congrArg (fun v => v.getLsbD i) h
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_xor, BitVec.getLsbD_setWidth, BitVec.getLsbD_zero] at this
    rw [← BitVec.getLsbD_eq_getElem, ← BitVec.getLsbD_eq_getElem]
    revert this
    cases A.getLsbD i <;> cases B.getLsbD i <;> cases C.getLsbD i <;> cases D.getLsbD i <;>
      simp [show i < 32 by omega]
  · ext i hi
    have := congrArg (fun v => v.getLsbD i) h
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_xor, BitVec.getLsbD_setWidth, BitVec.getLsbD_zero] at this
    rw [← BitVec.getLsbD_eq_getElem, ← BitVec.getLsbD_eq_getElem]
    revert this
    cases A.getLsbD i <;> cases B.getLsbD i <;> cases C.getLsbD i <;> cases D.getLsbD i <;> simp

/-- Equal words: equal `spectrum_params`. -/
theorem sp_eq_of (a b : List UInt8) (ha : a.length = 6) (hb : b.length = 6)
    (h1 : BitVec.ofInt 16 (Int.ofBytes (a.drop 4)) = BitVec.ofInt 16 (Int.ofBytes ((b.drop 4).take 2)))
    (h2 : BitVec.ofInt 32 (Int.ofBytes (a.take 4)) = BitVec.ofInt 32 (Int.ofBytes (b.take 4))) :
    b = a := by
  have e1 := congrArg (fun v => Int.toBytes 2 v.toInt) h1
  have e2 := congrArg (fun v => Int.toBytes 4 v.toInt) h2
  rw [toBytes2_ofBytes _ (by simp [ha]), toBytes2_ofBytes _ (by simp [hb])] at e1
  rw [toBytes4_ofBytes _ (by simp [ha]), toBytes4_ofBytes _ (by simp [hb])] at e2
  simp only [List.take_take, Nat.min_self] at e1 e2
  rw [List.take_of_length_le (by simp [ha]), List.take_of_length_le (by simp [hb])] at e1
  rw [← List.take_append_drop 4 a, ← List.take_append_drop 4 b, e1, e2]

theorem zf_sub (a b : BitVec 32) : (a - b == BitVec.zero 32) = true ↔ a = b := by
  rw [beq_iff_eq, show BitVec.zero 32 = 0#32 from rfl]
  constructor <;> intro h <;> bv_omega

section Step

variable {m : Mem 64} {k : Nat} {x : HArgs} {ra : Int64} {t₀ : MachineData}
  {Fm : Mem 64 → Prop} {st : HSt} {Tl : Mem 64 → Prop}

/-- A field read: the index store, then the byte store at `0x1c + o`. -/
theorem hdr_step (h : m =⋆ M k x ra t₀ Fm st Tl) (o : Nat) (ho : o < st.sp.length)
    (hl : st.sp.length < 2 ^ 32) (i' : BitVec 32) (b : BitVec 8) :
    (m.storeInt (arg1 t₀ + 8#64) 4 i'.toInt).storeInt (arg0 t₀ + BitVec.ofNat 64 (0x1c + o)) 1
        b.toInt
      =⋆ M k x ra t₀ Fm { st with i := i', sp := st.sp.set o (UInt8.ofBitVec b) } Tl := by
  have h1 := M_st_sp (M_st_i h i') o 1 (by simp only; omega) hl b.toInt
  rw [slice1_set _ _ _ ho, BitVec.ofInt_toInt] at h1
  exact h1

/-- A byte store into `spectrum_params`. -/
theorem M_st_sp1 (h : m =⋆ M k x ra t₀ Fm st Tl) (o : Nat) (ho : o < st.sp.length)
    (hl : st.sp.length < 2 ^ 32) (b : BitVec 8) :
    m.storeInt (arg0 t₀ + BitVec.ofNat 64 (0x1c + o)) 1 b.toInt
      =⋆ M k x ra t₀ Fm { st with sp := st.sp.set o (UInt8.ofBitVec b) } Tl := by
  have h1 := M_st_sp h o 1 (by omega) hl b.toInt
  rw [slice1_set _ _ _ ho, BitVec.ofInt_toInt] at h1
  exact h1

end Step

set_option hygiene false in
/-- A field read at `0x1c + o` of `n` bits; expects `hm hC hR hi2 hl` (and `hrax` if
`%eax` holds the index at entry). Leaves the buffer-load check and the exit goal. -/
macro "hdr_read" o:term "," n:term : tactic => `(tactic| (
    have hli := M_ld_i hm
    have hlp := M_ld_p8 hm
    have hlb := M_ld_buf hm
    have hbl := M_ld_bytes hm _ 4 (rd_off _ x.p8 x.L hi2 hC.2.2.2.1)
    have hok := fun v => M_ok_sp (M_st_i hm v) $o 1 (by simp only [hl]; omega) (by simp only [hl]; omega)
    have hstep := fun i' w => hdr_step hm $o (by simp only [hl]; omega) (by simp only [hl]; omega) i' w
    have hcl := clamp _ x.p8 $n hi2 hC.2.2.1 (by omega)
    have hRh : ∀ s : MachineData, s = s₀ → Rs x t₀ s := fun _ h => h ▸ hR
    obtain ⟨hrdi, hrsi, hrsp, hrbp, hrest⟩ := hR
    clear hm
    simp only [arg0, arg1, BitVec.add_zero, Nat.reduceAdd, BitVec.add_assoc,
      BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at hli hlp hlb hok hstep
    vcgen [bswap32_havoc, shl_cl32_havoc]
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals try simp only [AddrIndex.offset64_none, AddrIndex.offset64_scale1,
      BitVec.add_zero, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, Reg64s.get64_set64,
      reduceCtorEq, ↓reduceIte, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow] at *
    all_goals try simp only [hrax] at *
    all_goals try simp only [hr9, hr10, hr11] at *
    all_goals try simp only [hrdi, hrsi, hli, hlp, hlb, Option.isSome_some,
      Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 32 4 rfl,
      BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, Nat.reduceLeDiff,
      CondCode.interp, StatusFlags.from_result, cf_sub, BitVec.reduceSetWidth] at *
    all_goals try simp only [hok, Option.isSome_some]
    all_goals try simp only [decide_eq_true_eq] at *))

set_option hygiene false in
/-- A one-bit read; expects `hm hC hR hi2`, the two stores `hstep` and the
store check `hok` (and `hrax` if `%eax` holds the index at entry). -/
macro "hdr_bit" i:term : tactic => `(tactic| (
    have hli := M_ld_i hm
    have hlp := M_ld_p8 hm
    have hlb := M_ld_buf hm
    have hbl := M_ld_bytes hm ((($i).ushiftRight 3).setWidth 64) 1
      (by have := rd_off _ x.p8 x.L hi2 hC.2.2.2.1; omega)
    have hRh : ∀ s : MachineData, s = s₀ → Rs x t₀ s := fun _ h => h ▸ hR
    obtain ⟨hrdi, hrsi, hrsp, hrbp, hrest⟩ := hR
    clear hm
    simp only [arg0, arg1, BitVec.add_zero, Nat.reduceAdd, BitVec.add_assoc,
      BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at hli hlp hlb hok hstep
    vcgen [bswap32_havoc, shl_cl32_havoc]
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals try simp only [AddrIndex.offset64_none, AddrIndex.offset64_scale1,
      BitVec.add_zero, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, Reg64s.get64_set64,
      reduceCtorEq, ↓reduceIte, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow] at *
    all_goals try simp only [hrax] at *
    all_goals try simp only [hr9, hr10, hr11] at *
    all_goals try simp only [hrdi, hrsi, hli, hlp, hlb, Option.isSome_some,
      Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 32 4 rfl,
      BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, Nat.reduceLeDiff,
      CondCode.interp, StatusFlags.from_result, cf_sub, BitVec.reduceSetWidth, BitVec.xor_self,
      setl_val] at *
    all_goals try simp only [hok, Option.isSome_some]
    all_goals try simp only [decide_eq_true_eq] at *))

set_option hygiene false in
/-- `hdr_bit` with an `nb`-byte buffer load; expects `hm hC hR hi2`, the two stores `hstep` and the
store check `hok` (and `hrax` if `%eax` holds the index at entry). -/
macro "hdr_rdn" i:term "," nb:term : tactic => `(tactic| (
    have hli := M_ld_i hm
    have hlp := M_ld_p8 hm
    have hlb := M_ld_buf hm
    have hbl := M_ld_bytes hm ((($i).ushiftRight 3).setWidth 64) $nb
      (by have := rd_off _ x.p8 x.L hi2 hC.2.2.2.1; omega)
    have hRh : ∀ s : MachineData, s = s₀ → Rs x t₀ s := fun _ h => h ▸ hR
    obtain ⟨hrdi, hrsi, hrsp, hrbp, hrest⟩ := hR
    clear hm
    simp only [arg0, arg1, BitVec.add_zero, Nat.reduceAdd, BitVec.add_assoc,
      BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at hli hlp hlb hok hstep
    vcgen [bswap32_havoc, shl_cl32_havoc]
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals try simp only [AddrIndex.offset64_none, AddrIndex.offset64_scale1,
      BitVec.add_zero, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, Reg64s.get64_set64,
      reduceCtorEq, ↓reduceIte, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow] at *
    all_goals try simp only [hrax] at *
    all_goals try simp only [hr9, hr10, hr11] at *
    all_goals try simp only [hrdi, hrsi, hli, hlp, hlb, Option.isSome_some,
      Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 32 4 rfl,
      BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, Nat.reduceLeDiff,
      CondCode.interp, StatusFlags.from_result, cf_sub, BitVec.reduceSetWidth, BitVec.xor_self,
      setl_val] at *
    all_goals try simp only [hok, Option.isSome_some]
    all_goals try simp only [decide_eq_true_eq] at *))

end Kraken.Examples.Sbr.Hdr
