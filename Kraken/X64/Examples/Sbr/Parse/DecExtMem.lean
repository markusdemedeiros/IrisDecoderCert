import Kraken.X64.Examples.Sbr.Parse.DecExtBase

/-!
# `ff_aac_sbr_decode_extension`: memory lemmas

* The copy of `*gb_host` to the frame (`gbc = *gb_host`, l.1138): a 16-byte and an 8-byte move
  across the cells of the struct. The struct is regrouped as two runs of bytes (`gh_eq`), each
  moved whole, then split again at the frame (`val_split3`, `val_split2`).
* Bytes stored from a loaded value are the loaded bytes (`tb_ofInt`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.DecExt

/-- The bytes of `n` loaded and stored back at the same width are the bytes. -/
theorem tb_ofInt (n : Nat) (bs : List UInt8) (h : bs.length = n) :
    Int.toBytes n (BitVec.ofInt (8 * n) (Int.ofBytes bs)).toInt = bs := by
  rw [BitVec.toInt_ofInt, Nat.pow_mul]
  exact Int.toBytes_bmod_ofBytes n bs h

theorem val_split2 (a b : BitVec 64) (y z : BitVec 32) (hb : b = a + 4#64) :
    (Int.toBytes 4 y.toInt ++ Int.toBytes 4 z.toInt) =@ a = cell4 a y ⋆ cell4 b z := by
  rw [Val.append_eq _ _ a b (by rw [hb, Int.toBytes_length])
    (by simp only [Int.toBytes_length]; omega)]

theorem val_split3 (a : BitVec 64) (x : BitVec 64) (y z : BitVec 32) :
    (Int.toBytes 8 x.toInt ++ (Int.toBytes 4 y.toInt ++ Int.toBytes 4 z.toInt)) =@ a
      = Apply.c8 a x ⋆ (cell4 (a + 8#64) y ⋆ cell4 (a + 0xc#64) z) := by
  rw [Val.append_eq _ _ a (a + 8#64) (by rw [Int.toBytes_length])
    (by simp only [Int.toBytes_length, List.length_append]; omega),
    val_split2 (a + 8#64) (a + 0xc#64) y z (by rw [BitVec.add_assoc]; rfl)]

/-- The first 16 bytes of `*gb_host` (`buffer`, `index`, `size_in_bits`). -/
def L16 (X : XA) (i : BitVec 32) : List UInt8 :=
  Int.toBytes 8 X.r.buf.toInt ++ (Int.toBytes 4 i.toInt ++ Int.toBytes 4 X.sib.toInt)

/-- The last 8 bytes (`size_in_bits_plus8`, padding). -/
def L8 (X : XA) : List UInt8 := Int.toBytes 4 X.r.p8.toInt ++ Int.toBytes 4 X.pad.toInt

theorem L16_len (X : XA) (i : BitVec 32) : (L16 X i).length = 16 := by
  simp only [L16, List.length_append, Int.toBytes_length]

theorem L8_len (X : XA) : (L8 X).length = 8 := by
  simp only [L8, List.length_append, Int.toBytes_length]

theorem gh_eq (g : BitVec 64) (X : XA) (i : BitVec 32) :
    GhW g X i = L16 X i =@ g ⋆ L8 X =@ (g + 0x10#64) := by
  simp only [GhW, L16, L8]
  rw [val_split3, val_split2 (g + 0x10#64) (g + 0x14#64) _ _ (by rw [BitVec.add_assoc]; rfl)]
  simp only [Std.ExtHashMap.sep_assoc]

theorem L16_split (a b c : BitVec 64) (X : XA) (i : BitVec 32) (hb : b = a + 8#64)
    (hc : c = a + 0xc#64) :
    L16 X i =@ a = Apply.c8 a X.r.buf ⋆ (cell4 b i ⋆ cell4 c X.sib) := by
  subst hb hc; simp only [L16]; exact val_split3 a _ _ _

theorem L8_split (a b : BitVec 64) (X : XA) (hb : b = a + 4#64) :
    L8 X =@ a = cell4 a X.r.p8 ⋆ cell4 b X.pad := by
  simp only [L8]; exact val_split2 a b _ _ hb

theorem tb_L16 (X : XA) (i : BitVec 32) :
    Int.toBytes 16 (BitVec.ofInt 128 (Int.ofBytes (L16 X i))).toInt = L16 X i :=
  tb_ofInt 16 _ (L16_len X i)

theorem tb_L8 (X : XA) :
    Int.toBytes 8 (BitVec.ofInt 64 (Int.ofBytes (L8 X))).toInt = L8 X :=
  tb_ofInt 8 _ (L8_len X)

theorem add_ofNat0 (x : BitVec 64) : x + (0 : BitVec 64) = x := BitVec.add_zero x

/-- The frame's `vmovaps` target is 16-byte aligned (`rsp + 8` is at entry). -/
theorem al_sub (r : BitVec 64) (c : Nat) (h : isAligned 16 (r + 8#64) = true)
    (hc : (c + 8) % 16 = 0) :
    isAligned 16 (r - BitVec.ofNat 64 c) = true := by
  simp only [isAligned, beq_iff_eq] at *
  have e : r - BitVec.ofNat 64 c = (r + 8#64) - BitVec.ofNat 64 (c + 8) := by bv_omega
  rw [e, BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat]
  omega

/-- The ranking `var` at literal labels. -/
macro "var_n " h:ident : tactic => `(tactic| (
  simp only [var_entry, var_L21, var_L36, var_L63, var_L301, var_L31c, var_L8b, var_Lad, var_Ld4, var_L333, var_Lff, var_L10d, var_L11d, var_L128, var_L4ee, var_L50b, var_L527, var_L53d, var_L553, var_L569, var_L57e, var_done, var_L349, var_L164, var_L384, var_L39d, var_L3bd, var_L3cb, var_L3e4, var_L401, var_L409, var_L43d, var_Lb1a, var_L48b, var_L4a1, var_L4b7, var_L4cd, var_L4e2, var_L7de, var_L898, var_L7e8, var_L80e, var_L835, var_L85b, var_L8b0,
    var_Lb40, var_Lb64, var_Lb86, var_Lc41, var_Lc4b, var_Lc67, var_Lc7d, var_Lc83, var_Lcc0, var_Lcd3, var_Lc1c, var_Lc1f, var_Lca0, var_Lcbb, var_Lb9d, var_Lbd4, var_Lbe6, var_Lbf5] at $h:ident
  subst $h:ident))

/-- After `vcgen`: normalise the loads' addresses with the register facts `ts`, replace the loaded
values by the cells' values (`sep_vals`), normalise the goals' addresses to `rsp₀ - c`, and step
the stores over the memory fact `h` (`sep_mem`). -/
syntax "dx_run " ident " [" term,* "]" : tactic

macro_rules
  | `(tactic| dx_run $h [$ts,*]) => do
    let ls : Array (Lean.TSyntax ``Lean.Parser.Tactic.simpLemma) ←
      ts.getElems.mapM fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)
    `(tactic| (
      all_goals try subst_vars
      all_goals try simp_loads [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
        AddrIndex.offset64, Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm,
        add_ofNat0, BitVec.add_zero, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod,
        BitVec.reduceToNat, Nat.reduceEqDiff, $ts,*]
      all_goals try simp_loads [BitVec.sub_add_ofNat_wrap, Nat.reduceAdd, Nat.reducePow,
        Nat.reduceSub, Nat.reduceLeDiff]
      all_goals try sep_vals $h
      all_goals try sep_vals $h
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
        Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Int64.toBitVec_neg_ofNat_norm,
        Int64.toBitVec_ofNat_norm, AddrIndex.offset64, BitVec.add_zero, add_ofNat0,
        RegZmms.get_set_xmm_same, sbrA, arg0, arg1, arg2, arg3, arg4, AvW, BufW, BitVec.reduceToNat,
        Nat.reduceEqDiff, $ls,*]
      all_goals try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub]
      all_goals try simp only [BitVec.sub_add_ofNat_wrap, Nat.reduceAdd, Nat.reducePow,
        Nat.reduceSub, Nat.reduceLeDiff]
      all_goals try sep_mem $h))

/-- After `dx_run`: the branch conditions as equations of the loaded values, and the frame
addresses of `hm` in normal form. -/
macro "dx_br" h:ident : tactic => `(tactic| (
  all_goals try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub] at $h:ident
  all_goals try sep_mem $h:ident
  all_goals try sep_vals $h:ident
  all_goals try subst_vars
  all_goals try simp only [CondCode.interp_z, CondCode.interp_nz, StatusFlags.zf_from_result_sub,
    BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt_toInt, Int64.toBitVec_zero, BitVec.setWidth_zero,
    beq_iff_eq, Bool.not_eq_true', beq_eq_false_iff_ne, BitVec.ofNat_eq_ofNat, Bool.not_eq_eq_eq_not,
    Bool.not_false, Bool.not_true, BitVec.setWidth_32_64_32] at *))

/-- The ranking of a jump edge to a literal label, with its `var` equation `e`. -/
macro "edge_ok " e:ident : tactic => `(tactic| (
  rw [$e:ident]
  first | exact Or.inl (by decide) | decide | exact Or.inr ⟨by decide, by decide⟩))


theorem newRate_zero (sr : BitVec 32) : newRate 0 sr = sr + sr := if_pos rfl

theorem newRate_ne {v : BitVec 32} (sr : BitVec 32) (h : v ≠ 0) : newRate v sr = v := if_neg h

theorem TabF_st1 (x : Args) (r s e : BitVec 32) (p : BitVec 64) :
    TabF { x with reset := r, sampleRate := s, extRate := e } p = TabF x p := rfl


/-- `jb`/`cmovb` after a 32-bit `cmp`, as the unsigned order. -/
theorem interp_c_sub32 (a b : BitVec 32) (af o : Bool) :
    CondCode.c.interp (StatusFlags.from_result (a - b)
      { cf := (a - b).unsigned != a.unsigned - b.unsigned, af := af, of := o })
      = decide (a.toNat < b.toNat) := by
  rw [CondCode.interp_c, StatusFlags.cf_from_result]
  simp only [BitVec.unsigned_eq, BitVec.toNat_sub]
  have := a.isLt; have := b.isLt
  by_cases h : a.toNat < b.toNat
  · simp only [h, decide_true, bne_iff_ne, ne_eq]; omega
  · simp only [h, decide_false, bne_eq_false_iff_eq]; omega

/-- A clamp `min(y, p)` (by `cmovb`), or `g`, stays below `p`. -/
theorem min_le (g p y : BitVec 32) (z : Prop) [Decidable z] (hg : g.toNat ≤ p.toNat) :
    (BitVec.setWidth 64 (if z then g else if p.toNat < y.toNat then p else y)).toNat
      ≤ p.toNat := by
  split
  · simp only [BitVec.toNat_setWidth]; omega
  · split
    · simp only [BitVec.toNat_setWidth]; omega
    · simp only [BitVec.toNat_setWidth]; omega

/-- A 32-bit store of a loaded `int` writes its bytes back. -/
theorem tb4_ofInt (v : Int) : Int.toBytes 4 (BitVec.ofInt 32 v).toInt = Int.toBytes 4 v := by
  rw [BitVec.toInt_ofInt, ← Int.toBytes_emod]
  have h : v.bmod (2 ^ 32) % (2 ^ (8 * 4) : Int) = v % 2 ^ (8 * 4) := Int.bmod_emod
  rw [show (v.bmod (2 ^ 32)).take (8 * 4) = v.bmod (2 ^ 32) % 2 ^ (8 * 4) from rfl, h,
    show v % 2 ^ (8 * 4) = v.take (8 * 4) from rfl, Int.toBytes_emod]

theorem TabF_pro (x : Args) (a b : BitVec 32) (p : BitVec 64) :
    TabF (extPro x a b) p = TabF x p := rfl

end Kraken.Examples.Sbr.DecExt
