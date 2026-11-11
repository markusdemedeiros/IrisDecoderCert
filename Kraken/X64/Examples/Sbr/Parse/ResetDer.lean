import Kraken.InfoOff
import Kraken.X64.Examples.Sbr.Parse.ResetTable
import Kraken.X64.Examples.Sbr.Parse.ResetModel
import Kraken.X64.Examples.Sbr.Parse.ResetDerLib
import Kraken.X64.Examples.Sbr.Parse.ResetA1Lib
import Kraken.X64.Examples.Sbr.Parse.ResetLog
import Kraken.X64.Examples.Sbr.Parse.ResetExitW
import Kraken.X64.Examples.Sbr.Parse.ResetOff2

/-!
# `sbr_reset`: `sbr_make_f_derived`, the stores of `derived1` (shard B)
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Reset

variable [CodeEnv]

omit [CodeEnv] in
/-- What `Master` gives `sbr_make_f_derived`: `xover < n_master ≤ 48`, `f` increasing up to
`f n_master ≤ 64`. -/
theorem master_bounds {sr : Int} {st xo : Nat} {k0 : Int} {nm : Nat} {f : Nat → Nat}
    (h : Master sr st xo (some k0) (some (nm, f))) :
    xo < nm ∧ nm ≤ 48 ∧ f nm ≤ 64 ∧ (∀ i j, i ≤ j → j ≤ nm → f i + (j - i) ≤ f j) := by
  cases h with
  | ok k2 _ _ hr h64 hk hq hxo hf0 hinc hfn =>
    have hmono : ∀ i j, i ≤ j → j ≤ nm → f i + (j - i) ≤ f j := by
      intro i j hij hj
      induction j with
      | zero => have : i = 0 := by omega
                subst this; omega
      | succ j ih =>
        rcases Nat.eq_or_lt_of_le hij with e | hlt
        · subst e; omega
        · have := ih (by omega) (by omega); have := hinc j (by omega); omega
    have h0n := hmono 0 nm (Nat.zero_le _) (Nat.le_refl _)
    refine ⟨hxo, ?_, by omega, hmono⟩
    split at hq <;> (try split at hq) <;> omega

section Mem
variable {m : Mem 64} {k : Nat} {e : REnv} {a : RArgs} {ra : Int64} {t₀ : MachineData} {st : St}
  {fr : List UInt8}

/-- An 8-byte frame slot `rbp - d` is readable. -/
theorem fr_load8 (hm : m =⋆ Mm k e a ra t₀ st fr) (hF : FrOk fr) {d : Nat} (hd : 0x30 ≤ d)
    (hd' : d ≤ 0x570) {addr : BitVec 64}
    (ha : addr = t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 (rb d)) :
    m.loadInt addr 8 = some (Int.ofBytes (slice fr (rb d) 8)) :=
  region_load (focus (Mm_fr ..) hm) ha (by rw [hF]; unfold rb; omega) (by rw [hF]; omega)

/-- An 8-byte store into the frame slot `rbp - d`. -/
theorem fr_store8 (hm : m =⋆ Mm k e a ra t₀ st fr) (hF : FrOk fr) {d : Nat} (hd : 0x30 ≤ d)
    (hd' : d ≤ 0x570) {addr : BitVec 64}
    (ha : addr = t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 (rb d)) (v : Int) :
    m.storeInt addr 8 v =⋆ Mm k e a ra t₀ st (wr fr (rb d) (Int.toBytes 8 v)) := by
  have h := region_store (o := rb d) (n := 8) (focus (Mm_fr ..) hm) ha (by rw [hF]; unfold rb; omega)
    (by rw [hF]; omega) v
  rw [← Mm_upd_fr]; exact h

omit [CodeEnv] in
theorem fr_wr_ok (hF : FrOk fr) {d : Nat} (hd : 0x30 ≤ d) (hd' : d ≤ 0x570) (v : Int) :
    FrOk (wr fr (rb d) (Int.toBytes 8 v)) := by
  unfold FrOk at *; rw [wr_length (by rw [Int.toBytes_length, hF]; unfold rb; omega), hF]

omit [CodeEnv] in
theorem der_frSlot64_wr_same (hF : FrOk fr) {d : Nat} (hd : 0x30 ≤ d) (hd' : d ≤ 0x570)
    (v : BitVec 64) : frSlot64 (wr fr (rb d) (Int.toBytes 8 v.toInt)) d = v := by
  unfold frSlot64
  have h := slice_wr_same (l := fr) (o := rb d) (v := Int.toBytes 8 v.toInt)
    (by rw [Int.toBytes_length, hF]; unfold rb; omega)
  rw [Int.toBytes_length] at h
  rw [h, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]

omit [CodeEnv] in
theorem der_frSlot64_wr_ne (hF : FrOk fr) {d : Nat} (hd : 0x30 ≤ d) (hd' : d ≤ 0x570) (v : Int)
    {d' : Nat} (hd'' : d' ≤ 0x570) (hdd : d' + 8 ≤ d ∨ d + 8 ≤ d') :
    frSlot64 (wr fr (rb d) (Int.toBytes 8 v)) d' = frSlot64 fr d' := by
  unfold frSlot64
  rw [slice_wr_disj (by rw [Int.toBytes_length, hF]; unfold rb; omega)
    (by rw [Int.toBytes_length]; unfold rb; omega)]

/-- The store of `n[1]`. -/
theorem n1_store (hm : m =⋆ Mm k e a ra t₀ st fr) {w : Int} {v : Nat}
    (hv : Int.toBytes 4 w = Int.toBytes 4 (v : Int)) :
    m.storeInt (arg1 t₀ + 0x4c1e4#64) 4 w
      =⋆ Mm k e a ra t₀ { st with x := { st.x with n1 := v } } fr := by
  have h := region_store (o := 0) (n := 4) (addr := arg1 t₀ + 0x4c1e4#64) (focus (Mm_n1 ..) hm)
    (by simp) (by simp [Int.toBytes_length]) (by simp [Int.toBytes_length]) w
  rw [← Mm_upd_n1]
  have hw : wr (Int.toBytes 4 (st.x.n1 : Int)) 0 (Int.toBytes 4 w) = Int.toBytes 4 (v : Int) := by
    simp [wr, Int.toBytes_length, hv]
  rwa [hw] at h

theorem n1_load (hm : m =⋆ Mm k e a ra t₀ st fr) :
    m.loadInt (arg1 t₀ + 0x4c1e4#64) 4 = some (Int.ofBytes (Int.toBytes 4 (st.x.n1 : Int))) := by
  have h := region_load (o := 0) (n := 4) (addr := arg1 t₀ + 0x4c1e4#64) (focus (Mm_n1 ..) hm)
    (by simp) (by simp [Int.toBytes_length]) (by simp [Int.toBytes_length])
  rw [h]; congr 2

/-- The store of `n[0]`. -/
theorem n0_store (hm : m =⋆ Mm k e a ra t₀ st fr) {w : Int} {v : Nat}
    (hv : Int.toBytes 4 w = Int.toBytes 4 (v : Int)) :
    m.storeInt (arg1 t₀ + 0x4c1e0#64) 4 w
      =⋆ Mm k e a ra t₀ { st with x := { st.x with n0 := v } } fr := by
  have h := region_store (o := 0) (n := 4) (addr := arg1 t₀ + 0x4c1e0#64) (focus (Mm_n0 ..) hm)
    (by simp) (by simp [Int.toBytes_length]) (by simp [Int.toBytes_length]) w
  rw [← Mm_upd_n0]
  have hw : wr (Int.toBytes 4 (st.x.n0 : Int)) 0 (Int.toBytes 4 w) = Int.toBytes 4 (v : Int) := by
    simp [wr, Int.toBytes_length, hv]
  rwa [hw] at h

theorem n0_load (hm : m =⋆ Mm k e a ra t₀ st fr) :
    m.loadInt (arg1 t₀ + 0x4c1e0#64) 4 = some (Int.ofBytes (Int.toBytes 4 (st.x.n0 : Int))) := by
  have h := region_load (o := 0) (n := 4) (addr := arg1 t₀ + 0x4c1e0#64) (focus (Mm_n0 ..) hm)
    (by simp) (by simp [Int.toBytes_length]) (by simp [Int.toBytes_length])
  rw [h]; congr 2

/-- The store of `m[1]`. -/
theorem m1_store (hm : m =⋆ Mm k e a ra t₀ st fr) {w : Int} {v : Nat}
    (hv : Int.toBytes 4 w = Int.toBytes 4 (v : Int)) :
    m.storeInt (arg1 t₀ + 0x60#64) 4 w
      =⋆ Mm k e a ra t₀ { st with x := { st.x with m1 := v } } fr := by
  have h := region_store (o := 0) (n := 4) (addr := arg1 t₀ + 0x60#64) (focus (Mm_m1 ..) hm)
    (by simp) (by simp [Int.toBytes_length]) (by simp [Int.toBytes_length]) w
  rw [← Mm_upd_m1]
  have hw : wr (Int.toBytes 4 (st.x.m1 : Int)) 0 (Int.toBytes 4 w) = Int.toBytes 4 (v : Int) := by
    simp [wr, Int.toBytes_length, hv]
  rwa [hw] at h

theorem m1_load (hm : m =⋆ Mm k e a ra t₀ st fr) :
    m.loadInt (arg1 t₀ + 0x60#64) 4 = some (Int.ofBytes (Int.toBytes 4 (st.x.m1 : Int))) := by
  have h := region_load (o := 0) (n := 4) (addr := arg1 t₀ + 0x60#64) (focus (Mm_m1 ..) hm)
    (by simp) (by simp [Int.toBytes_length]) (by simp [Int.toBytes_length])
  rw [h]; congr 2

omit [CodeEnv] in
theorem ofBytes_slice2 (l : List UInt8) (i : Nat) (h : 2 * i + 2 ≤ l.length) :
    Int.ofBytes (slice l (2 * i) 2) = (u16 l i : Int) := by
  have e : slice l (2 * i) 2 = [l[2 * i], l[2 * i + 1]] := by
    apply List.ext_getElem (by simp only [slice, List.length_take, List.length_drop,
      List.length_cons, List.length_nil]; omega)
    intro j h1 h2
    simp only [List.length_cons, List.length_nil] at h2
    simp only [slice, List.getElem_take, List.getElem_drop]
    rcases j with _ | _ | j
    · rfl
    · rfl
    · omega
  rw [e, Int.ofBytes_cons, Int.ofBytes_cons]
  unfold u16 u8
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega),
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  simp only [Option.getD_some, show Int.ofBytes [] = 0 from rfl]
  omega

/-- An element of `f_tablehigh`. -/
theorem ftH_load (hm : m =⋆ Mm k e a ra t₀ st fr) (hfh : st.x.ftHigh.length = 98) {i : Nat}
    (hi : i < 49) {addr : BitVec 64} (ha : addr = arg1 t₀ + 0x4c284#64 + BitVec.ofNat 64 (2 * i)) :
    m.loadInt addr 2 = some (u16 st.x.ftHigh i : Int) := by
  rw [region_load (o := 2 * i) (n := 2) (focus (Mm_ftHigh ..) hm) ha (by omega) (by omega),
    ofBytes_slice2 _ _ (by omega)]

/-- The store of `kx[1]`. -/
theorem kx1_store (hm : m =⋆ Mm k e a ra t₀ st fr) {w : Int} {v : Nat}
    (hv : Int.toBytes 4 w = Int.toBytes 4 (v : Int)) :
    m.storeInt (arg1 t₀ + 0x58#64) 4 w
      =⋆ Mm k e a ra t₀ { st with x := { st.x with kx1 := v } } fr := by
  have h := region_store (o := 0) (n := 4) (addr := arg1 t₀ + 0x58#64) (focus (Mm_kx1 ..) hm)
    (by simp) (by simp [Int.toBytes_length]) (by simp [Int.toBytes_length]) w
  rw [← Mm_upd_kx1]
  have hw : wr (Int.toBytes 4 (st.x.kx1 : Int)) 0 (Int.toBytes 4 w) = Int.toBytes 4 (v : Int) := by
    simp [wr, Int.toBytes_length, hv]
  rwa [hw] at h

theorem kx1_load (hm : m =⋆ Mm k e a ra t₀ st fr) :
    m.loadInt (arg1 t₀ + 0x58#64) 4 = some (Int.ofBytes (Int.toBytes 4 (st.x.kx1 : Int))) := by
  have h := region_load (o := 0) (n := 4) (addr := arg1 t₀ + 0x58#64) (focus (Mm_kx1 ..) hm)
    (by simp) (by simp [Int.toBytes_length]) (by simp [Int.toBytes_length])
  rw [h]; congr 2

end Mem

/-! ## The `memcpy` of `derived1`: `f_master[xover ..]` (source) and `f_tablehigh` (destination) -/

/-- `Mm` without `f_master`, `f_tablehigh`, the reservation and `Ext`. -/
def Mx_cp (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) (st : St) (fr : List UInt8) : Mem 64 → Prop :=
  fr =@ ((t₀.regs.get64 .rsp) - 0x578#64) ⋆ Saved t₀ ⋆ RetCell ra (t₀.regs.get64 .rsp)
    ⋆ cell4 (arg1 t₀) st.x.sampleRate ⋆ cell4 ((arg1 t₀) + 0x4#64) st.x.start
    ⋆ cell4 ((arg1 t₀) + 0x8#64) st.x.ready ⋆ cell4 ((arg1 t₀) + 0x10#64) a.us
    ⋆ st.sp =@ ((arg1 t₀) + 0x1c#64) ⋆ cell4 ((arg1 t₀) + 0x2c#64) a.lb
    ⋆ c4 ((arg1 t₀) + 0x40#64) st.x.k0 ⋆ cell4 ((arg1 t₀) + 0x44#64) st.k1
    ⋆ cell4 ((arg1 t₀) + 0x48#64) st.k2 ⋆ c4 ((arg1 t₀) + 0x58#64) st.x.kx1
    ⋆ c4 ((arg1 t₀) + 0x60#64) st.x.m1 ⋆ cell4 ((arg1 t₀) + 0x68#64) st.nm
    ⋆ c4 ((arg1 t₀) + 0x4c1e0#64) st.x.n0 ⋆ c4 ((arg1 t₀) + 0x4c1e4#64) st.x.n1
    ⋆ c4 ((arg1 t₀) + 0x4c1e8#64) st.x.nq ⋆ c4 ((arg1 t₀) + 0x4c1ec#64) st.x.nlim
    ⋆ st.x.ftLow =@ ((arg1 t₀) + 0x4c252#64)
    ⋆ st.x.ftNoise =@ ((arg1 t₀) + 0x4c2e6#64)
    ⋆ st.x.ftLim =@ ((arg1 t₀) + 0x4c2f2#64) ⋆ c4 ((arg1 t₀) + 0x4c330#64) st.x.npatch
    ⋆ st.x.pnum =@ ((arg1 t₀) + 0x4c334#64) ⋆ st.x.pstart =@ ((arg1 t₀) + 0x4c33a#64)
    ⋆ 4 ?@ ((arg1 t₀) + 0x3988#64) ⋆ c8 ((arg1 t₀) + 0x15b2c#64) st.x.d0.idx
    ⋆ 4 ?@ ((arg1 t₀) + 0x19448#64) ⋆ c8 ((arg1 t₀) + 0x2b5ec#64) st.x.d1.idx
    ⋆ c8 (arg0 t₀ + 0x8#64) st.x.avctx ⋆ CstR ⋆ BwR ⋆ a.x.R

/-- What stays beside the copied bytes: the rest of the two tables. -/
def CpRest (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) (st : St)
    (fr : List UInt8) (o n : Nat) : Mem 64 → Prop :=
  Mx_cp k e a ra t₀ st fr ⋆ (st.fm.take o =@ (arg1 t₀ + 0x4c1f0#64)
    ⋆ (st.fm.drop (o + n) =@ (arg1 t₀ + 0x4c1f0#64 + BitVec.ofNat 64 (o + n))
    ⋆ st.x.ftHigh.drop n =@ (arg1 t₀ + 0x4c284#64 + BitVec.ofNat 64 n)))

/-- `memcpy`'s caller memory `R`. -/
abbrev CpR (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) (st : St)
    (fr : List UInt8) (o n : Nat) : Mem 64 → Prop :=
  Reserve 0x450 (t₀.regs.get64 .rsp - 0x578#64 - 8#64 - BitVec.ofNat 64 k)
    ⋆ (e.Ext ⋆ CpRest k e a ra t₀ st fr o n)

omit [CodeEnv] in
theorem fm_split (fm : List UInt8) (A : BitVec 64) {o n : Nat} (h : o + n ≤ fm.length)
    (hw : fm.length ≤ 2 ^ 64) :
    (fm =@ A) = (slice fm o n =@ (A + BitVec.ofNat 64 o))
      ⋆ (fm.take o =@ A ⋆ fm.drop (o + n) =@ (A + BitVec.ofNat 64 (o + n))) := by
  have hs : fm = fm.take o ++ slice fm o n ++ fm.drop (o + n) := by
    simp only [slice]
    rw [List.append_assoc, ← List.drop_drop, List.take_append_drop, List.take_append_drop]
  have h1 : (fm.take o).length = o := by simp only [List.length_take]; omega
  have h2 : (slice fm o n).length = n := slice_length h
  simp only [Val.eq]
  conv => lhs; rw [hs]
  rw [At_append3_sep _ _ _ _ (by rw [h1, h2, List.length_drop]; omega), h1, h2]

omit [CodeEnv] in
theorem fh_split (fh : List UInt8) (A : BitVec 64) {n : Nat} (h : n ≤ fh.length)
    (hw : fh.length ≤ 2 ^ 64) :
    (fh =@ A) = (fh.take n =@ A ⋆ fh.drop n =@ (A + BitVec.ofNat 64 n)) := by
  have h1 : (fh.take n).length = n := by simp only [List.length_take]; omega
  simp only [Val.eq]
  conv => lhs; rw [← List.take_append_drop n fh]
  rw [At_append_sep _ _ _ (by rw [h1, List.length_drop]; omega), h1]

theorem Mx_call_cp (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) (st : St)
    (fr : List UInt8) {o n : Nat} (hfm : st.fm.length = 98) (hfh : st.x.ftHigh.length = 98)
    (h : o + n ≤ 98) :
    Mx_call k e a ra t₀ st fr
      = (slice st.fm o n =@ (arg1 t₀ + 0x4c1f0#64 + BitVec.ofNat 64 o)
        ⋆ st.x.ftHigh.take n =@ (arg1 t₀ + 0x4c284#64)) ⋆ CpRest k e a ra t₀ st fr o n := by
  simp only [Mx_call, CpRest, Mx_cp]
  rw [fm_split st.fm _ (o := o) (n := n) (by omega) (by omega),
    fh_split st.x.ftHigh _ (n := n) (by omega) (by omega)]
  ac_rfl

theorem Mm_cp (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) (st : St)
    (fr : List UInt8) {o n : Nat} (hfm : st.fm.length = 98) (hfh : st.x.ftHigh.length = 98)
    (h : o + n ≤ 98) (hd : 8 + tlimNeed k ≤ (t₀.regs.get64 .rsp - 0x578#64).toNat) :
    Mm k e a ra t₀ st fr = 8 ?@ (t₀.regs.get64 .rsp - 0x578#64 - 8#64)
      ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x578#64 - 8#64)
        ⋆ ((slice st.fm o n =@ (arg1 t₀ + 0x4c1f0#64 + BitVec.ofNat 64 o)
          ⋆ st.x.ftHigh.take n =@ (arg1 t₀ + 0x4c284#64)) ⋆ CpR k e a ra t₀ st fr o n)) := by
  rw [Mm_callF _ _ _ _ _ _ _ hd]
  simp only [CallF, CpR]
  rw [Mx_call_cp k e a ra t₀ st fr hfm hfh h]
  ac_rfl

/-- After the copy: `f_tablehigh` starts with the copied bytes. -/
theorem Mm_cp_post {m : Mem 64} (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData)
    (st : St) (fr : List UInt8) {o n : Nat} (hfm : st.fm.length = 98)
    (hfh : st.x.ftHigh.length = 98) (h : o + n ≤ 98)
    (hd : 8 + tlimNeed k ≤ (t₀.regs.get64 .rsp - 0x578#64).toNat)
    (hm : m =⋆ 8 ?@ (t₀.regs.get64 .rsp - 0x578#64 - 8#64)
      ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x578#64 - 8#64)
        ⋆ ((slice st.fm o n =@ (arg1 t₀ + 0x4c1f0#64 + BitVec.ofNat 64 o)
          ⋆ slice st.fm o n =@ (arg1 t₀ + 0x4c284#64)) ⋆ CpR k e a ra t₀ st fr o n))) :
    m =⋆ Mm k e a ra t₀ { st with x := { st.x with ftHigh := wr st.x.ftHigh 0 (slice st.fm o n) } }
      fr := by
  have hsrc : (slice st.fm o n).length = n := slice_length (by omega)
  have hw : wr st.x.ftHigh 0 (slice st.fm o n) = slice st.fm o n ++ st.x.ftHigh.drop n := by
    simp only [wr, List.take_zero, List.nil_append, hsrc, Nat.zero_add]
  have hfh' : (wr st.x.ftHigh 0 (slice st.fm o n)).length = 98 := by
    rw [wr_length (by rw [hsrc, hfh]; omega), hfh]
  rw [Mm_cp k e a ra t₀ { st with x := { st.x with ftHigh := wr st.x.ftHigh 0 (slice st.fm o n) } }
    fr (o := o) (n := n) hfm hfh' h hd]
  dsimp only
  simp only [CpR, CpRest] at hm ⊢
  rw [hw, List.take_left' hsrc, List.drop_left' hsrc]
  exact hm

set_option maxRecDepth 100000 in
/-- `n[1] = n_master - xover`; `n_master` saved in the frame; `n[0]`'s operands. -/
theorem blk_L2012 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2012" ⟨"sbr_reset.L2012", B.L2012, some "sbr_reset.L2032"⟩ := by
  info_off
  measure_hb "L2012"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hC, ⟨hrsp, hrbp⟩, h12, st, fr, nm, k0, hMa, hx, hsp, hk2, hfm, hF, h13, h14, h40, hm⟩ :=
      T.L2012.mp hs
    clear hs
    obtain ⟨hxo, hnm, -, -⟩ := master_bounds hMa
    have ha1 : t₀.regs.get64 .rsp - 8#64 + (-56 : Int64).toBitVec
        = t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 (rb 0x38) := by
      have : (-56 : Int64).toBitVec = 0xffffffffffffffc8#64 := by decide
      simp only [rb, this]; bv_omega
    have ld1 := fr_load8 hm hF (d := 0x38) (by omega) (by omega) ha1
    have ld2 := n1_load (focus rfl (fr_store8 hm hF (d := 0x38) (by omega) (by omega) ha1
      (s₀.regs.get64 .r13).toInt))
    have hxl := u8_lt a.sp 2
    have e14 : BitVec.setWidth 32 (BitVec.setWidth 8 (s₀.regs.get64 .r14))
        = BitVec.ofNat 32 (xoOf a) := by
      rw [h14]; apply BitVec.eq_of_toNat_eq; simp [xoOf] at hxl ⊢ <;> omega
    have e13 : BitVec.setWidth 32 (s₀.regs.get64 .r13) = BitVec.ofNat 32 nm := by
      rw [h13]; apply BitVec.eq_of_toNat_eq; simp <;> omega
    have esub : BitVec.ofNat 32 nm - BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.ofNat 32 (xoOf a)))
        = BitVec.ofNat 32 (nm - xoOf a) := by
      simp only [xoOf] at *; bv_omega
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L2012]
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, hrbp,
        AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
        BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.one_ne_zero]
    · rw [ld1]; rfl
    · rw [ld2]; rfl
    · simp only [e14, e13, esub]
      rw [h13]
      have hv : Int.toBytes 4 (BitVec.setWidth 32 (BitVec.setWidth 64
          (BitVec.ofNat 32 (nm - xoOf a)))).toInt = Int.toBytes 4 ((nm - xoOf a : Nat) : Int) := by
        congr 1
        rw [BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_eq,
          BitVec.toInt_eq_toNat_of_lt (by simp; omega)]
        simp; omega
      refine ⟨T.L2032.mpr ⟨hC, ⟨?_, ?_⟩, { st with x := { st.x with n1 := nm - xoOf a } },
        wr fr (rb 0x38) (Int.toBytes 8 (BitVec.ofNat 64 nm).toInt), nm, k0, hMa, hsp, hfm,
        fr_wr_ok hF (by omega) (by omega) _, ?_, ⟨hk2, ?_, der_frSlot64_wr_same hF (by omega) (by omega) _,
        ?_, ?_, ?_, ?_, ?_⟩, n1_store (fr_store8 hm hF (d := 0x38) (by omega) (by omega) ha1 _) hv⟩,
        by var_step⟩
      · simpa [Reg64s.get64_set64] using hrsp
      · simpa [Reg64s.get64_set64] using hrbp
      · rw [der_frSlot64_wr_ne hF (by omega) (by omega) _ (by omega) (by omega)]; exact h40
      · simp only [hx]
      all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      all_goals try rfl
      all_goals apply BitVec.eq_of_toNat_eq
      all_goals simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, xoOf, u8_eq_get?] at hxo hxl ⊢
      all_goals omega

set_option maxRecDepth 100000 in
/-- `n[0] = (n[1] + 1) / 2`; `xover < 50` (from `Master`); the `memcpy` operands. -/
theorem blk_L2032 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2032" ⟨"sbr_reset.L2032", B.L2032, some "sbr_reset.L2059"⟩ := by
  info_off
  measure_hb "L2032"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hC, ⟨hrsp, hrbp⟩, st, fr, nm, k0, hMa, hsp, hfm, hF, h40,
      ⟨hk2, hx, hsl, hbx, h12, h13, h15, hax⟩, hm⟩ := T.L2032.mp hs
    clear hs
    obtain ⟨hxo, hnm, -, -⟩ := master_bounds hMa
    have hxl := u8_lt a.sp 2
    have ld1 := n0_load hm
    simp only [arg1] at ld1
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L2032]
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hbx, hax, h12, h13, h15,
        AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    all_goals try disp_simp
    · rw [ld1]; rfl
    · rename_i hc
      exfalso; rw [hax] at hc
      simp [u8_eq_get?] at hc hxl hxo; omega
    · have hv : Int.toBytes 4 (BitVec.setWidth 32 (BitVec.ofNat 64
          ((nm - (xoOf a) + 1) / 2))).toInt = Int.toBytes 4 (((nm - xoOf a + 1) / 2 : Nat) : Int) := by
        congr 1
        rw [BitVec.toInt_eq_toNat_of_lt (by simp; omega)]
        simp; omega
      refine ⟨T.L2059.mpr ⟨hC, ⟨?_, ?_⟩, { st with x := { st.x with n0 := (nm - xoOf a + 1) / 2 } },
        fr, nm, k0, hMa, hsp, hfm, hF, h40, ⟨hk2, ?_, hsl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, n0_store hm hv⟩,
        by var_step⟩
      · simpa [Reg64s.get64_set64] using hrsp
      · simpa [Reg64s.get64_set64] using hrbp
      · simp only [hx]
      all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, AddrIndex.offset64, hax, hbx]
      · exact h12
      · exact h13
      · exact h15
      · simp only [Width.bytes, arg1, xoOf, u8_eq_get?, List.getD_eq_getElem?_getD] at hxl ⊢
        bv_omega
      · apply BitVec.eq_of_toNat_eq
        simp [xoOf, u8_eq_get?] at hxo hxl ⊢; omega

set_option maxRecDepth 100000 in
/-- `memcpy(f_tablehigh, f_master + xover, 2 (n[1] + 1))`. -/
theorem blk_L2059 (k : Nat) (e : REnv) (hc : ResetCallees k e) (a : RArgs) (ra : Int64)
    (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2059" ⟨"sbr_reset.L2059", B.L2059, some "sbr_reset.L205e"⟩ := by
  info_off
  measure_hb "L2059"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hC, ⟨hrsp, hrbp⟩, st, fr, nm, k0, hMa, hsp, hfm, hF, h40,
      ⟨hk2, hx, hsl, hbx, h12, h13, h15, hdi, hsi, hdx⟩, hm⟩ := T.L2059.mp hs
    clear hs
    obtain ⟨hxo, hnm, -, -⟩ := master_bounds hMa
    have hxo' : xoOf a < nm := hxo
    have hfh : st.x.ftHigh.length = 98 := by rw [hx]; exact hC.2.2.2.2.2.2.2.1
    have hsrc : (slice st.fm (2 * xoOf a) (2 * (nm - xoOf a + 1))).length = 2 * (nm - xoOf a + 1) :=
      slice_length (by omega)
    have hdxn : (s₀.regs.get64 .rdx).toNat = 2 * (nm - xoOf a + 1) := by
      rw [hdx, BitVec.toNat_ofNat]; omega
    have hd := reserve_le (focus (Mm_reserve ..) hm)
    rw [Mm_cp (o := 2 * xoOf a) (n := 2 * (nm - xoOf a + 1)) _ _ _ _ _ _ _ hfm hfh (by omega) hd] at hm
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rsp - 8#64) 8).isSome = true := by
      rw [hrsp]
      exact Block.loadInt_isSome hm (by simp)
    have hpush := fun v => Block.storeInt_val hm (Split.here _ _) v
    have e8 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 0x578#64 - 8#64 := by
      rw [hrsp]
    simp only [B.L2059]
    vcgen [MachineWP.call_proc_spec_at
      (⟨CpR k e a ra t₀ st fr (2 * xoOf a) (2 * (nm - xoOf a + 1)),
        slice st.fm (2 * xoOf a) (2 * (nm - xoOf a + 1))⟩ : McA) "memcpy" hc.memcpy]
    all_goals try call_simp
    all_goals try subst_vars
    refine ⟨fun ra' => ⟨⟨?_, ?_⟩, fun s' hpost => ?_⟩, hld⟩
    · rw [e8, hsi, hdi, hdxn]
      exact sep_imp (fun _ h => h) (sep_imp (fun _ h => h) (sep_imp (sep_imp (fun _ h => h)
        (val_imp (by simp only [List.length_take]; omega) (by omega))) (fun _ h => h))) _ (hpush _)
    · rw [hsrc, hdxn]
    · rw [e8, hsi, hdi] at hpost
      obtain ⟨hsp', hbp', ⟨hbx', h12', h13', -, h15'⟩, hm'⟩ := hpost
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨T.L205e.mpr ⟨hC, ⟨?_, ?_⟩,
        { st with x := { st.x with ftHigh := wr st.x.ftHigh 0 (slice st.fm (2 * xoOf a) (2 * (nm - xoOf a + 1))) } },
        fr, nm, k0, hMa, hsp, hfm, hF, h40, ⟨hk2, ?_, hsl, ?_, ?_, ?_, ?_⟩, ?_⟩, by var_step⟩
      · rw [hsp']; bv_omega
      · rw [hbp', hrbp]
      · dsimp only
        rw [ftHigh_copy hfm hfh hnm (Nat.le_of_lt hxo')]
        simp only [hx]
      · rw [hbx', hbx]
      · rw [h12', h12]
      · rw [h13', h13]
      · rw [h15', h15]
      · exact Mm_cp_post k e a ra t₀ st fr hfm hfh (by have : xoOf a = (a.sp.getD 2 0).toNat := rfl; omega) hd hm'

set_option maxRecDepth 100000 in
/-- `n[1] < 49`; `m[1] = f[n_master] - f[xover]` (from the copy); `sbr` saved in the frame. -/
theorem blk_L205e (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L205e" ⟨"sbr_reset.L205e", B.L205e, some "sbr_reset.L208b"⟩ := by
  info_off
  measure_hb "L205e"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hC, ⟨hrsp, hrbp⟩, st, fr, nm, k0, hMa, hsp, hfm, hF, h40,
      ⟨hk2, hx, hsl, hbx, h12, h13, h15⟩, hm⟩ := T.L205e.mp hs
    clear hs
    obtain ⟨hxo, hnm, hf64, hmono⟩ := master_bounds hMa
    have hxo' : xoOf a < nm := hxo
    have hfx := hmono (xoOf a) nm (Nat.le_of_lt hxo') (Nat.le_refl _)
    have hxl := u8_lt a.sp 2
    have hfh : st.x.ftHigh.length = 98 := by
      rw [hx]; simp only [d1c]; exact mk16_length _ _
    have ldA := fun {addr} => ftH_load hm hfh (i := nm - xoOf a) (addr := addr) (by omega)
    have ldB := ftH_load hm hfh (i := 0) (by omega) (addr := arg1 t₀ + 0x4c284#64) (by simp)
    have fA : u16 st.x.ftHigh (nm - xoOf a) = fOf st nm := by
      rw [hx]; simp only [d1c]; rw [u16_mk16 (by omega)]
      simp only [Nat.le_refl, ↓reduceIte, fOf]
      rw [show xoOf a + (nm - xoOf a) = nm by omega]; exact Nat.mod_eq_of_lt (u16_lt _ _)
    have fB : u16 st.x.ftHigh 0 = fOf st (xoOf a) := by
      rw [hx]; simp only [d1c]; rw [u16_mk16 (by omega)]
      simp only [Nat.zero_le, ↓reduceIte, Nat.add_zero, fOf]; exact Nat.mod_eq_of_lt (u16_lt _ _)
    rw [fA] at ldA; rw [fB] at ldB
    have ldM := m1_load hm
    have ha2 : t₀.regs.get64 .rsp - 8#64 + (-48 : Int64).toBitVec
        = t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 (rb 0x30) := by
      have : (-48 : Int64).toBitVec = 0xffffffffffffffd0#64 := by decide
      simp only [rb, this]; bv_omega
    have hv : ∀ x y : Nat, x ≤ 64 → y ≤ x →
        Int.toBytes 4 (BitVec.setWidth 32 (BitVec.ofInt 16 (x : Int)) - BitVec.setWidth 32
          (BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32
            (BitVec.ofInt 16 (y : Int)))))).toInt = Int.toBytes 4 ((x - y : Nat) : Int) := by
      intro x y hx hy
      congr 1
      rw [BitVec.ofInt_natCast, BitVec.ofInt_natCast]
      rw [BitVec.toInt_eq_toNat_of_lt (by simp [BitVec.toNat_sub]; omega)]
      simp [BitVec.toNat_sub]; omega
    simp only [arg1] at ldA ldB ldM
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L205e]
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hbx, h12, h13, h15, hrbp,
        AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    all_goals try disp_simp
    · rename_i hc; exfalso
      rw [h13] at hc
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at hc
      have : xoOf a = (a.sp.getD 2 0).toNat := rfl
      omega
    · rw [ldA (by simp only [AddrIndex.offset64, Reg64s.get64_set64, ↓reduceIte, Width.bytes, xoOf, u8] at hxo hnm ⊢; bv_omega)]; rfl
    · rw [ldB]; rfl
    · rw [ldM]; rfl
    · rename_i vA vB _ hlA hlB
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hbx, h13, AddrIndex.offset64_none,
        BitVec.add_zero, BitVec.ofNat_eq_ofNat, Int64.toBitVec_ofNat_norm] at hlA hlB
      rw [ldA (by simp only [AddrIndex.offset64, Reg64s.get64_set64, ↓reduceIte, Width.bytes, xoOf, u8] at hxo hnm ⊢; bv_omega)] at hlA
      rw [ldB] at hlB
      obtain rfl := Option.some.inj hlA
      obtain rfl := Option.some.inj hlB
      rw [fr_load8 (m1_store hm (hv _ _ hf64 (by omega))) hF (d := 0x30) (by omega) (by omega) ha2]
      rfl
    · rename_i vA vB _ hlA hlB
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hbx, h13, AddrIndex.offset64_none,
        BitVec.add_zero, BitVec.ofNat_eq_ofNat, Int64.toBitVec_ofNat_norm] at hlA hlB
      rw [ldA (by simp only [AddrIndex.offset64, Reg64s.get64_set64, ↓reduceIte, Width.bytes, xoOf, u8] at hxo hnm ⊢; bv_omega)] at hlA
      rw [ldB] at hlB
      obtain rfl := Option.some.inj hlA
      obtain rfl := Option.some.inj hlB
      refine ⟨T.L208b.mpr ⟨hC, ⟨?_, ?_⟩,
        { st with x := { st.x with m1 := fOf st nm - fOf st (xoOf a) } },
        wr fr (rb 0x30) (Int.toBytes 8 (t₀.regs.get64 .rsi).toInt), nm, k0, hMa, hsp, hfm,
        fr_wr_ok hF (by omega) (by omega) _, ?_, ⟨hk2, ?_, ?_, der_frSlot64_wr_same hF (by omega) (by omega) _,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
        fr_store8 (m1_store hm (hv (fOf st nm) (fOf st (xoOf a)) hf64
          (by simp only [fOf, u16, u8, xoOf] at *; omega))) hF (d := 0x30) (by omega) (by omega) ha2 _⟩,
        by var_step⟩
      · simpa [Reg64s.get64_set64] using hrsp
      · simpa [Reg64s.get64_set64] using hrbp
      · rw [der_frSlot64_wr_ne hF (by omega) (by omega) _ (by omega) (by omega)]; exact h40
      · simp only [hx]
      · rw [der_frSlot64_wr_ne hF (by omega) (by omega) _ (by omega) (by omega)]; exact hsl
      all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      all_goals try exact hbx
      all_goals try exact h12
      all_goals try exact h13
      all_goals try exact h15
      all_goals rw [BitVec.ofInt_natCast]
      all_goals apply BitVec.eq_of_toNat_eq
      all_goals simp only [fOf, u16, u8, xoOf] at *
      all_goals (try simp)
      all_goals simp only [List.getD_eq_getElem?_getD] at *
      all_goals omega

set_option maxRecDepth 100000 in
/-- `kx[1] = f[xover]`; `f[n_master] ≤ 64` (from `Master`), so the first check passes. -/
theorem blk_L208b (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L208b" ⟨"sbr_reset.L208b", B.L208b, some "sbr_reset.L20aa"⟩ := by
  info_off
  measure_hb "L208b"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hC, ⟨hrsp, hrbp⟩, st, fr, nm, k0, hMa, hsp, hfm, hF, h40,
      ⟨hk2, hx, hsl, hs30, hbx, h12, h13, h15, hcx, h14, h10⟩, hm⟩ := T.L208b.mp hs
    clear hs
    obtain ⟨hxo, hnm, hf64, hmono⟩ := master_bounds hMa
    have ldK := kx1_load hm
    have hv : ∀ x : Nat, x ≤ 64 → Int.toBytes 4 (BitVec.setWidth 32 (BitVec.ofNat 64 x)).toInt
        = Int.toBytes 4 (x : Int) := by
      intro x hx
      congr 1
      rw [BitVec.toInt_eq_toNat_of_lt (by simp; omega)]
      simp; omega
    have hfx := hmono (xoOf a) nm (Nat.le_of_lt hxo) (Nat.le_refl _)
    have hlt : (BitVec.setWidth 32 (s₀.regs.get64 .rcx)).toNat < 65 := by
      have aux : ∀ v : Nat, v ≤ 64 → (BitVec.setWidth 32 (BitVec.ofNat 64 v)).toNat < 65 := by
        intro v hv; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
      rw [hcx]; exact aux _ hf64
    have hfx64 : fOf st (xoOf a) ≤ 64 := by omega
    simp only [arg1] at ldK
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L208b]
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hbx, h12, h13, h15, hcx,
        h14, h10, hrbp, AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero]
    · rw [ldK]; rfl
    · refine Or.inl (Table.ofLabels_at ⟨S.L20aa, T.L20aa.mpr ⟨hC, ⟨hrsp, hrbp⟩,
        { st with x := { st.x with kx1 := fOf st (xoOf a) } }, fr, nm, k0, hMa, hsp, hfm, hF, h40,
        ⟨hk2, ?_, hsl, hs30, hbx, h12, h13, h15, h14, h10, ?_, hf64⟩, kx1_store hm (hv _ hfx64)⟩, by edge_step⟩)
      · rw [hx]; rfl
      · first | exact hcx | (simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact hcx)
    all_goals exfalso
    all_goals disp_simp
    all_goals (simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at *; omega)

set_option maxRecDepth 100000 in
/-- `f[xover] ≤ 32` goes on; otherwise the `av_log` of the error. -/
theorem blk_L20aa (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L20aa" ⟨"sbr_reset.L20aa", B.L20aa, some "sbr_reset.L20c8"⟩ := by
  info_off
  measure_hb "L20aa"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hC, ⟨hrsp, hrbp⟩, st, fr, nm, k0, hMa, hsp, hfm, hF, h40,
      ⟨hk2, hx, hsl, hs30, hbx, h12, h13, h15, h14, h10, hcx, hf64⟩, hm⟩ := T.L20aa.mp hs
    clear hs
    have ha3 : t₀.regs.get64 .rsp - 8#64 + (-64 : Int64).toBitVec
        = t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 (rb 0x40) := by
      have : (-64 : Int64).toBitVec = 0xffffffffffffffc0#64 := by decide
      simp only [rb, this]; bv_omega
    have ld1 := fr_load8 hm hF (d := 0x40) (by omega) (by omega) ha3
    have ld2 := c8_load (focus (Mm_avctx ..) hm)
    have hav : st.x.avctx = a.x.avctx := by rw [hx]; rfl
    rw [hav] at ld2
    simp only [arg0] at ld2 h40
    have P40 : PLift (frSlot64 fr 0x40 = arg0 t₀) := ⟨h40⟩
    have Prbp : PLift (s₀.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64) := ⟨hrbp⟩
    have hb16 := u16_lt st.fm (xoOf a)
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L20aa]
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hbx, h12, h13, h15,
        h14, h10, hrbp, AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero]
    all_goals try disp_simp
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, AddrIndex.offset64_none,
      BitVec.add_zero, hrbp, ld1, Option.some.injEq, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp only [h40, ld2, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    · have hbr : fOf st (xoOf a) ≤ 32 := by
        simp only [h14, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at *
        simp only [fOf, u16, u8, xoOf] at *
        omega
      have hrbp := Prbp.down
      exact Or.inl (Table.ofLabels_at ⟨S.L20d8, T.L20d8.mpr ⟨hC, ⟨hrsp, hrbp⟩, st, fr, nm, k0, hMa,
        hsp, hfm, hF, P40.down, ⟨hk2, hx, hsl, hs30, h12, h13, h15, h14, hf64, hbr,
        by first | exact h10 | (simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact h10),
        by first | exact hcx | (simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact hcx)⟩,
        hm⟩, by edge_step⟩)
    · have hbr : 32 < fOf st (xoOf a) := by
        simp only [h14, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at *
        simp only [fOf, u16, u8, xoOf] at *
        omega
      have hrbp := Prbp.down
      refine ⟨T.L20c8.mpr ⟨hC, ⟨?_, ?_⟩, st, fr, nm, k0, hMa, hsp, hfm, hF, P40.down,
        ⟨Or.inl ⟨hx, Or.inr ⟨hf64, hbr⟩⟩, hs30, ?_, ?_⟩, hm⟩, by var_step⟩
      all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrsp, hrbp,
        BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]
      all_goals rfl

set_option maxRecDepth 100000 in
/-- `av_log` (the errors of `derived1`). -/
theorem blk_L20c8 (k : Nat) (e : REnv) (hAv : AvLogSpec e.Ext k) (a : RArgs) (ra : Int64)
    (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L20c8" ⟨"sbr_reset.L20c8", B.L20c8, some "sbr_reset.L20cf"⟩ := by
  info_off
  measure_hb "L20c8"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hC, ⟨hrsp, hrbp⟩, st, fr, nm, k0, hMa, hsp, hfm, hF, h40,
      ⟨hQ, hs30, h15, hdi⟩, hm⟩ := T.L20c8.mp hs
    clear hs
    have hd := reserve_le (focus (Mm_reserve ..) hm)
    rw [Mm_callF _ _ _ _ _ _ _ hd] at hm
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rsp - 8#64) 8).isSome = true := by
      rw [hrsp]
      exact Block.loadInt_isSome hm (by simp)
    have hpush := fun v => Block.storeInt_val hm (Split.here _ _) v
    have e8 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 0x578#64 - 8#64 := by
      rw [hrsp]
    simp only [B.L20c8]
    vcgen [MachineWP.call_proc_spec_at (CallF k e a ra t₀ st fr) "av_log" hAv]
    all_goals try call_simp
    all_goals try subst_vars
    refine ⟨fun ra' => ⟨⟨?_, trivial⟩, fun s' hpost => ?_⟩, hld⟩
    · rw [e8]; exact hpush _
    · rw [e8] at hpost
      obtain ⟨hsp', hbp', ⟨-, -, -, -, h15'⟩, hm'⟩ := hpost
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨T.L20cf.mpr ⟨hC, ⟨?_, ?_⟩, st, fr, nm, k0, hMa, hsp, hfm, hF, h40,
        ⟨hQ, hs30, ?_⟩, ?_⟩, by var_step⟩
      · rw [hsp']; bv_omega
      · rw [hbp', hrbp]
      · rw [h15', h15]
      · show Mm k e a ra t₀ st fr s'.dmem
        rw [Mm_callF _ _ _ _ _ _ _ hd]; exact hm'

omit [CodeEnv] in
/-- The two errors of `derived1` are failures `Reset` allows. -/
theorem reset_bad {a : RArgs} {k0 : Int} {nm : Nat} {f : Nat → Nat} (hst : u8 a.sp 0 < 16)
    (hMa : Master a.x.sampleRate.toInt (u8 a.sp 0) (u8 a.sp 2) (some k0) (some (nm, f)))
    (hfx : f (xoOf a) ≤ f nm) (hbad : 64 < f nm ∨ (f nm ≤ 64 ∧ 32 < f (xoOf a))) :
    Reset (spOf a) (lbN a) a.x (derived1 (x0D a k0) nm (xoOf a) f).turnoff := by
  have e1 : (derived1 (x0D a k0) nm (xoOf a) f).kx1 = f (xoOf a) := rfl
  have e2 : (derived1 (x0D a k0) nm (xoOf a) f).m1 = f nm - f (xoOf a) := rfl
  rcases hbad with h | ⟨h1, h2⟩
  · exact Reset.badDerived hst hMa (Derived.badTop (by rw [e1, e2]; omega))
  · exact Reset.badDerived hst hMa (Derived.badKx (by rw [e1, e2]; omega) (by rw [e1]; omega))

set_option maxRecDepth 100000 in
/-- `r12 = sbr` again, then `sbr_turnoff`. -/
theorem blk_L20cf (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L20cf" ⟨"sbr_reset.L20cf", B.L20cf, some "sbr_reset.L20d8"⟩ := by
  info_off
  measure_hb "L20cf"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hC, ⟨hrsp, hrbp⟩, st, fr, nm, k0, hMa, hsp, hfm, hF, h40,
      ⟨hQ, hs30, h15⟩, hm⟩ := T.L20cf.mp hs
    clear hs
    obtain ⟨hxo, -, -, hmono⟩ := master_bounds hMa
    have hR : Reset (spOf a) (lbN a) a.x st.x.turnoff := by
      rcases hQ with ⟨hx, hbad⟩ | hR
      · have hR := reset_bad hC.2.1 hMa
          (Nat.le_trans (Nat.le_add_right _ _) (hmono (xoOf a) nm (Nat.le_of_lt hxo) (Nat.le_refl _))) hbad
        rw [← hx] at hR
        exact hR
      · exact hR
    have ha2 : t₀.regs.get64 .rsp - 8#64 + (-48 : Int64).toBitVec
        = t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 (rb 0x30) := by
      have : (-48 : Int64).toBitVec = 0xffffffffffffffd0#64 := by decide
      simp only [rb, this]; bv_omega
    have ld1 := fr_load8 hm hF (d := 0x30) (by omega) (by omega) ha2
    have P30 : PLift (frSlot64 fr 0x30 = arg1 t₀) := ⟨hs30⟩
    have Prbp : PLift (s₀.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64) := ⟨hrbp⟩
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L20cf]
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, AddrIndex.offset64_none,
      BitVec.add_zero, hrbp, ld1, Option.some.injEq, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, Option.isSome_some] at *
    all_goals try subst_vars
    exact Or.inl (Table.ofLabels_at ⟨S.L1d31, T.L1d31.mpr ⟨hC, ⟨by simpa [Reg64s.get64_set64] using hrsp,
      by simpa [Reg64s.get64_set64] using Prbp.down⟩, by simpa [Reg64s.get64_set64] using P30.down,
      by simpa [Reg64s.get64_set64] using h15, st, fr, hR, hsp, hfm, hF, hm⟩, by edge_step⟩)

end Kraken.Examples.Sbr.Reset
