import Kraken.X64.Examples.Sbr.Parse.ResetA2Blk
import Kraken.X64.Examples.Sbr.Parse.ResetExitW

/-!
# `sbr_reset`, shard A2: the `memcpy`s of `f_master` from the frame arrays `vk0`, `vk1`

`memcpy(f_master + o, frame + fo, n)`: the source is a slice of the frame region `fr`, the
destination a slice of `f_master`. `a2_Mm_mc` splits `Mm` into the two slices and the rest;
`a2_Mm_mc_post` puts the copied bytes back into `f_master`.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Reset

variable [CodeEnv]

/-- `Mm` without the frame, `f_master`, the reservation and `Ext`. -/
def A2Mx (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) (st : St) : Mem 64 → Prop :=
  Saved t₀ ⋆ RetCell ra (t₀.regs.get64 .rsp)
    ⋆ cell4 (arg1 t₀) st.x.sampleRate ⋆ cell4 ((arg1 t₀) + 0x4#64) st.x.start
    ⋆ cell4 ((arg1 t₀) + 0x8#64) st.x.ready ⋆ cell4 ((arg1 t₀) + 0x10#64) a.us
    ⋆ st.sp =@ ((arg1 t₀) + 0x1c#64) ⋆ cell4 ((arg1 t₀) + 0x2c#64) a.lb
    ⋆ c4 ((arg1 t₀) + 0x40#64) st.x.k0 ⋆ cell4 ((arg1 t₀) + 0x44#64) st.k1
    ⋆ cell4 ((arg1 t₀) + 0x48#64) st.k2 ⋆ c4 ((arg1 t₀) + 0x58#64) st.x.kx1
    ⋆ c4 ((arg1 t₀) + 0x60#64) st.x.m1 ⋆ cell4 ((arg1 t₀) + 0x68#64) st.nm
    ⋆ c4 ((arg1 t₀) + 0x4c1e0#64) st.x.n0 ⋆ c4 ((arg1 t₀) + 0x4c1e4#64) st.x.n1
    ⋆ c4 ((arg1 t₀) + 0x4c1e8#64) st.x.nq ⋆ c4 ((arg1 t₀) + 0x4c1ec#64) st.x.nlim
    ⋆ st.x.ftLow =@ ((arg1 t₀) + 0x4c252#64)
    ⋆ st.x.ftHigh =@ ((arg1 t₀) + 0x4c284#64) ⋆ st.x.ftNoise =@ ((arg1 t₀) + 0x4c2e6#64)
    ⋆ st.x.ftLim =@ ((arg1 t₀) + 0x4c2f2#64) ⋆ c4 ((arg1 t₀) + 0x4c330#64) st.x.npatch
    ⋆ st.x.pnum =@ ((arg1 t₀) + 0x4c334#64) ⋆ st.x.pstart =@ ((arg1 t₀) + 0x4c33a#64)
    ⋆ 4 ?@ ((arg1 t₀) + 0x3988#64) ⋆ c8 ((arg1 t₀) + 0x15b2c#64) st.x.d0.idx
    ⋆ 4 ?@ ((arg1 t₀) + 0x19448#64) ⋆ c8 ((arg1 t₀) + 0x2b5ec#64) st.x.d1.idx
    ⋆ c8 (arg0 t₀ + 0x8#64) st.x.avctx ⋆ CstR ⋆ BwR ⋆ a.x.R

/-- What stays beside the two slices. -/
def A2McRest (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) (st : St)
    (fr : List UInt8) (fo o n : Nat) : Mem 64 → Prop :=
  A2Mx k e a ra t₀ st
    ⋆ ((fr.take fo =@ (t₀.regs.get64 .rsp - 0x578#64)
      ⋆ fr.drop (fo + n) =@ (t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 (fo + n)))
    ⋆ (st.fm.take o =@ (arg1 t₀ + 0x4c1f0#64)
      ⋆ st.fm.drop (o + n) =@ (arg1 t₀ + 0x4c1f0#64 + BitVec.ofNat 64 (o + n))))

/-- `memcpy`'s caller memory `R`. -/
abbrev A2McR (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) (st : St)
    (fr : List UInt8) (fo o n : Nat) : Mem 64 → Prop :=
  Reserve 0x450 (t₀.regs.get64 .rsp - 0x578#64 - 8#64 - BitVec.ofNat 64 k)
    ⋆ (e.Ext ⋆ A2McRest k e a ra t₀ st fr fo o n)

omit [CodeEnv] in
theorem a2_split3 (l : List UInt8) (A : BitVec 64) {o n : Nat} (h : o + n ≤ l.length)
    (hw : l.length ≤ 2 ^ 64) :
    (l =@ A) = (slice l o n =@ (A + BitVec.ofNat 64 o))
      ⋆ (l.take o =@ A ⋆ l.drop (o + n) =@ (A + BitVec.ofNat 64 (o + n))) := by
  have hs : l = l.take o ++ slice l o n ++ l.drop (o + n) := by
    simp only [slice]
    rw [List.append_assoc, ← List.drop_drop, List.take_append_drop, List.take_append_drop]
  have h1 : (l.take o).length = o := by simp only [List.length_take]; omega
  have h2 : (slice l o n).length = n := slice_length h
  simp only [Val.eq]
  conv => lhs; rw [hs]
  rw [At_append3_sep _ _ _ _ (by rw [h1, h2, List.length_drop]; omega), h1, h2]

theorem a2_Mx_call_mc (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) (st : St)
    (fr : List UInt8) {fo o n : Nat} (hF : FrOk fr) (hfm : st.fm.length = 98)
    (h1 : fo + n ≤ 0x548) (h2 : o + n ≤ 98) :
    Mx_call k e a ra t₀ st fr
      = (slice fr fo n =@ (t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 fo)
        ⋆ slice st.fm o n =@ (arg1 t₀ + 0x4c1f0#64 + BitVec.ofNat 64 o))
        ⋆ A2McRest k e a ra t₀ st fr fo o n := by
  simp only [Mx_call, A2McRest, A2Mx]
  rw [a2_split3 fr _ (o := fo) (n := n) (by rw [hF]; omega) (by rw [hF]; omega),
    a2_split3 st.fm _ (o := o) (n := n) (by omega) (by omega)]
  ac_rfl

theorem a2_Mm_mc (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) (st : St)
    (fr : List UInt8) {fo o n : Nat} (hF : FrOk fr) (hfm : st.fm.length = 98)
    (h1 : fo + n ≤ 0x548) (h2 : o + n ≤ 98)
    (hd : 8 + tlimNeed k ≤ (t₀.regs.get64 .rsp - 0x578#64).toNat) :
    Mm k e a ra t₀ st fr = 8 ?@ (t₀.regs.get64 .rsp - 0x578#64 - 8#64)
      ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x578#64 - 8#64)
        ⋆ ((slice fr fo n =@ (t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 fo)
          ⋆ slice st.fm o n =@ (arg1 t₀ + 0x4c1f0#64 + BitVec.ofNat 64 o))
          ⋆ A2McR k e a ra t₀ st fr fo o n)) := by
  rw [Mm_callF _ _ _ _ _ _ _ hd]
  simp only [CallF, A2McR]
  rw [a2_Mx_call_mc k e a ra t₀ st fr hF hfm h1 h2]
  ac_rfl

/-- After the copy: `f_master[o ..]` holds the frame bytes. -/
theorem a2_Mm_mc_post {m : Mem 64} (k : Nat) (e : REnv) (a : RArgs) (ra : Int64)
    (t₀ : MachineData) (st : St) (fr : List UInt8) {fo o n : Nat} (hF : FrOk fr)
    (hfm : st.fm.length = 98) (h1 : fo + n ≤ 0x548) (h2 : o + n ≤ 98)
    (hd : 8 + tlimNeed k ≤ (t₀.regs.get64 .rsp - 0x578#64).toNat)
    (hm : m =⋆ 8 ?@ (t₀.regs.get64 .rsp - 0x578#64 - 8#64)
      ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x578#64 - 8#64)
        ⋆ ((slice fr fo n =@ (t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 fo)
          ⋆ slice fr fo n =@ (arg1 t₀ + 0x4c1f0#64 + BitVec.ofNat 64 o))
          ⋆ A2McR k e a ra t₀ st fr fo o n))) :
    m =⋆ Mm k e a ra t₀ { st with fm := wr st.fm o (slice fr fo n) } fr := by
  have hsrc : (slice fr fo n).length = n := slice_length (by rw [hF]; omega)
  have hfm' : (wr st.fm o (slice fr fo n)).length = 98 := by
    rw [wr_length (by rw [hsrc, hfm]; omega), hfm]
  rw [a2_Mm_mc k e a ra t₀ { st with fm := wr st.fm o (slice fr fo n) } fr (fo := fo) (o := o)
    (n := n) hF hfm' h1 h2 hd]
  have ht : (wr st.fm o (slice fr fo n)).take o = st.fm.take o := by
    simp only [wr, List.append_assoc]
    rw [List.take_left' (by simp only [List.length_take]; omega)]
  have hdr : (wr st.fm o (slice fr fo n)).drop (o + n) = st.fm.drop (o + n) := by
    simp only [wr, hsrc]
    rw [List.drop_left' (by simp only [List.length_append, List.length_take, hsrc]; omega)]
  have hsl : slice (wr st.fm o (slice fr fo n)) o n = slice fr fo n := by
    have := slice_wr_same (l := st.fm) (o := o) (v := slice fr fo n) (by rw [hsrc]; omega)
    rwa [hsrc] at this
  dsimp only
  simp only [A2McR, A2McRest, A2Mx] at hm ⊢
  rw [ht, hdr, hsl]
  exact hm

omit [CodeEnv] in
theorem a2_slice_wr (l v : List UInt8) {o p q : Nat} (h : p + q ≤ v.length)
    (hl : o + v.length ≤ l.length) : slice (wr l o v) (o + p) q = slice v p q := by
  have h1 : (l.take o).length = o := by simp only [List.length_take]; omega
  simp only [slice, wr, List.append_assoc]
  rw [← List.drop_drop, List.drop_left' h1, List.drop_append_of_le_length (by omega),
    List.take_append_of_le_length (by simp; omega)]

omit [CodeEnv] in
theorem a2_slice_slice (l : List UInt8) {a b p q : Nat} (h : p + q ≤ b) :
    slice (slice l a b) p q = slice l (a + p) q := by
  simp only [slice, List.drop_take, List.take_take, List.drop_drop]
  congr 1
  omega

omit [CodeEnv] in
theorem a2_ofBytes_slice2 (l : List UInt8) (i : Nat) (h : 2 * i + 2 ≤ l.length) :
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

omit [CodeEnv] in
theorem a2_u16_lt (l : List UInt8) (i : Nat) : u16 l i < 65536 := by
  have := (l.getD (2 * i) 0).toNat_lt; have := (l.getD (2 * i + 1) 0).toNat_lt
  unfold u16 u8; omega

omit [CodeEnv] in
/-- A nonnegative signed 16-bit value is its unsigned value. -/
theorem a2_toInt16_nonneg {X : Int} (h0 : 0 ≤ X) (h1 : X < 65536)
    (h : 0 ≤ (BitVec.ofInt 16 X).toInt) : (BitVec.ofInt 16 X).toInt = X := by
  rw [BitVec.toInt_ofInt] at h ⊢
  simp only [Int.bmod] at h ⊢
  split at h <;> simp_all <;> omega

omit [CodeEnv] in
/-- An element of `f_master` after the copy of the frame array at `fo`: the frame element. -/
theorem a2_u16_copy {fm fr : List UInt8} {o fo L j : Nat} (hfm : o + L ≤ fm.length)
    (hfr : fo + L ≤ fr.length) (hj : 2 * j + 2 ≤ L) (ho : o % 2 = 0) (hfo : fo % 2 = 0)
    (h : 0 ≤ A2.fv fr fo j) :
    (u16 (wr fm o (slice fr fo L)) (o / 2 + j) : Int) = A2.fv fr fo j := by
  have hsl : (slice fr fo L).length = L := slice_length hfr
  have e1 : Int.ofBytes (slice (wr fm o (slice fr fo L)) (2 * (o / 2 + j)) 2)
      = Int.ofBytes (slice fr (fo + 2 * j) 2) := by
    rw [show 2 * (o / 2 + j) = o + 2 * j by omega, a2_slice_wr _ _ (by rw [hsl]; omega)
      (by rw [hsl]; omega), a2_slice_slice _ (by omega)]
  have hw : (wr fm o (slice fr fo L)).length = fm.length := wr_length (by rw [hsl]; omega)
  rw [a2_ofBytes_slice2 _ _ (by rw [hw]; omega)] at e1
  simp only [A2.fv] at h ⊢
  rw [e1]
  have := a2_ofBytes_slice2 fr (fo / 2 + j) (by omega)
  rw [show 2 * (fo / 2 + j) = fo + 2 * j by omega] at this
  rw [this] at h ⊢
  exact (a2_toInt16_nonneg (by omega) (by have := a2_u16_lt fr (fo / 2 + j); omega) h).symm

omit [CodeEnv] in
/-- Strictly increasing from `v0`: `v0 + i ≤ vk[i]`. -/
theorem a2_inc_ge {fr : List UInt8} {o n : Nat} {v0 v1 : Int} (h : A2.Inc fr o n v0 v1) :
    ∀ i, i ≤ n → v0 + i ≤ A2.fv fr o i
  | 0, _ => by have := h.1; omega
  | i + 1, hi => by
    have := a2_inc_ge h i (by omega); have := h.2.2 i (by omega); push_cast; omega

set_option maxRecDepth 100000 in
/-- One region: `memcpy(f_master, vk0, 2 (nb0 + 1))`. -/
theorem blk_L1dd9 (k : Nat) (e : REnv) (hc : ResetCallees k e) (a : RArgs) (ra : Int64)
    (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1dd9" ⟨"sbr_reset.L1dd9", B.L1dd9, some "sbr_reset.L1dde"⟩ := by
  info_off
  measure_hb "L1dd9"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, h12, h15, hN0, h40, hone, hInc, hnm, h13, h14, hxo, hdi, hsi, hdx⟩, hm⟩⟩ :=
      T.L1dd9.mp hs
    clear hs
    have hvar : ∀ s, var "sbr_reset.L1dde" s ≤ n := fun s => by rw [← hn]; var_step
    have hn0 : A2.n0N e a (k0N a row) k2 ≤ 48 := by
      show (A2.n0I e a (k0N a row) k2).toNat ≤ 48
      have := hN0.2.1; omega
    obtain ⟨L, hL⟩ : ∃ L, 2 * (A2.n0N e a (k0N a row) k2 + 1) = L := ⟨_, rfl⟩
    rw [hL] at hdx
    have hL98 : L ≤ 98 := by omega
    have hLi : ∀ i, i ≤ A2.n0N e a (k0N a row) k2 → 2 * i + 2 ≤ L := fun i hi => by omega
    clear hL
    have hsrc : (slice fr 0x400 L).length = L := slice_length (by rw [hF]; omega)
    have hdxn : (s₀.regs.get64 .rdx).toNat = L := by
      rw [hdx, BitVec.toNat_ofNat]; omega
    have hsi' : s₀.regs.get64 .rsi = t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 0x400 := by
      rw [hsi, hrbp]; bv_omega
    have hdi' : s₀.regs.get64 .rdi = arg1 t₀ + 0x4c1f0#64 + BitVec.ofNat 64 0 := by
      rw [hdi]; simp
    have hd := reserve_le (focus (Mm_reserve ..) hm)
    rw [a2_Mm_mc (fo := 0x400) (o := 0) (n := L) _ _ _ _ _ _ _ hF hfm (by omega) (by omega) hd] at hm
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rsp - 8#64) 8).isSome = true := by
      rw [hrsp]
      exact Block.loadInt_isSome hm (by simp)
    have hpush := fun v => Block.storeInt_val hm (Split.here _ _) v
    have e8 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 0x578#64 - 8#64 := by
      rw [hrsp]
    simp only [B.L1dd9]
    vcgen [MachineWP.call_proc_spec_at
      (⟨A2McR k e a ra t₀ st fr 0x400 0 L, slice fr 0x400 L⟩ : McA) "memcpy" hc.memcpy]
    all_goals try call_simp
    all_goals try (rename_i hss; subst hss)
    refine ⟨fun ra' => ⟨⟨?_, ?_⟩, fun s' hpost => ?_⟩, hld⟩
    · rw [e8, hsi', hdi', hdxn]
      exact sep_imp (fun _ h => h) (sep_imp (fun _ h => h) (sep_imp (sep_imp (fun _ h => h)
        (fun _ h => ⟨by omega, _, slice_length (by omega), h⟩))
        (fun _ h => h))) _ (hpush _)
    · rw [hsrc, hdxn]
    · rw [e8, hsi', hdi'] at hpost
      obtain ⟨hsp', hbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩ := hpost
      have hm2 := a2_Mm_mc_post k e a ra t₀ st fr hF hfm (by omega) (by omega) hd hm'
      have hfm2 : (wr st.fm 0 (slice fr 0x400 L)).length = 98 := by
        rw [wr_length (by rw [hsrc, hfm]; omega), hfm]
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨T.L1dde.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩,
        { st with fm := wr st.fm 0 (slice fr 0x400 L) }, fr, hx, hsp, hfm2, hF,
        ⟨hk2v, hk1v, ?_, hN0, h40, hone, hInc, hnm, ?_, ?_, hxo, ?_⟩, hm2⟩⟩, hvar s'⟩
      · rw [hsp']; bv_omega
      · rw [hbp', hrbp]
      · rw [h12', h12]
      · rw [h13', h13]
      · rw [h14']; exact h14
      · intro i hi
        have hk0 := k0Of_range hrow hC.2.1
        have hge := a2_inc_ge hInc i hi
        have := a2_u16_copy (fm := st.fm) (fr := fr) (o := 0) (fo := 0x400) (L := L) (j := i)
          (by omega) (by rw [hF]; omega) (hLi i hi) (by omega) (by omega)
          (Int.le_trans (Int.add_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)) hge)
        simpa using this

omit [CodeEnv] in
theorem a2_cc_le_add (x y : Nat) (hx : x ≤ 48) (hy : y ≤ 48) (h : 0 < x + y) (c f : Bool) :
    CondCode.le.interp (StatusFlags.from_result (BitVec.ofNat 32 x + BitVec.ofNat 32 y)
      { cf := c, af := f, of := (BitVec.ofNat 32 x + BitVec.ofNat 32 y).signed
          != (BitVec.ofNat 32 x).signed + (BitVec.ofNat 32 y).signed }) = false := by
  simp only [CondCode.interp_le, StatusFlags.zf_from_result, StatusFlags.sf_from_result,
    StatusFlags.of_from_result, BitVec.signed]
  rw [← BitVec.ofNat_add]
  have ht : ∀ z : Nat, z ≤ 96 → (BitVec.ofNat 32 z).toInt = (z : Int) := fun z hz => by
    rw [BitVec.toInt_eq_toNat_bmod, BitVec.toNat_ofNat]; simp only [Int.bmod_def]; split <;> omega
  have hm : (BitVec.ofNat 32 (x + y)).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat]; simp; omega
  have hz : (BitVec.ofNat 32 (x + y) == BitVec.zero 32) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro h'
    have := congrArg BitVec.toNat h'
    simp only [BitVec.toNat_ofNat] at this
    simp at this; omega
  rw [ht _ (by omega), ht _ (by omega), ht _ (by omega), hm, hz]
  simp

set_option maxRecDepth 100000 in
/-- Two regions: `memcpy(f_master, vk0, 2 (nb0 + 1))`. -/
theorem blk_L297e (k : Nat) (e : REnv) (hc : ResetCallees k e) (a : RArgs) (ra : Int64)
    (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L297e" ⟨"sbr_reset.L297e", B.L297e, some "sbr_reset.L298a"⟩ := by
  info_off
  measure_hb "L297e"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hlt, hInc0, hN0, hN1, h12, h15, h40, h30, hInc1, hnm, h13, h14, hxo, hdi, hbx,
        hdx⟩, hm⟩⟩ := T.L297e.mp hs
    clear hs
    have hvar : ∀ s, var "sbr_reset.L298a" s ≤ n := fun s => by rw [← hn]; var_step
    have hn0 : A2.n0N e a (k0N a row) k2 ≤ 48 := by
      show (A2.n0I e a (k0N a row) k2).toNat ≤ 48
      have := hN0.2.1; omega
    obtain ⟨L, hL⟩ : ∃ L, 2 * (A2.n0N e a (k0N a row) k2 + 1) = L := ⟨_, rfl⟩
    rw [hL] at hdx
    have hL98 : L ≤ 98 := by omega
    have hLi : ∀ i, i ≤ A2.n0N e a (k0N a row) k2 → 2 * i + 2 ≤ L := fun i hi => by omega
    clear hL
    have hsrc : (slice fr 0x400 L).length = L := slice_length (by rw [hF]; omega)
    have hdxn : (s₀.regs.get64 .rdx).toNat = L := by
      rw [hdx, BitVec.toNat_ofNat]; omega
    have hsi' : s₀.regs.get64 .rbp + (-368 : Int64).toBitVec
        = t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 0x400 := by
      rw [show (-368 : Int64).toBitVec = 18446744073709551248#64 from rfl, hrbp]; bv_omega
    have hdi' : s₀.regs.get64 .rdi = arg1 t₀ + 0x4c1f0#64 + BitVec.ofNat 64 0 := by
      rw [hdi]; simp
    have hd := reserve_le (focus (Mm_reserve ..) hm)
    rw [a2_Mm_mc (fo := 0x400) (o := 0) (n := L) _ _ _ _ _ _ _ hF hfm (by omega) (by omega) hd] at hm
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rsp - 8#64) 8).isSome = true := by
      rw [hrsp]
      exact Block.loadInt_isSome hm (by simp)
    have hpush := fun v => Block.storeInt_val hm (Split.here _ _) v
    have e8 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 0x578#64 - 8#64 := by
      rw [hrsp]
    simp only [B.L297e]
    vcgen [MachineWP.call_proc_spec_at
      (⟨A2McR k e a ra t₀ st fr 0x400 0 L, slice fr 0x400 L⟩ : McA) "memcpy" hc.memcpy]
    all_goals try call_simp
    all_goals try (rename_i hss; subst hss)
    refine ⟨fun ra' => ⟨⟨?_, ?_⟩, fun s' hpost => ?_⟩, hld⟩
    · rw [e8, hsi', hdi', hdxn]
      exact sep_imp (fun _ h => h) (sep_imp (fun _ h => h) (sep_imp (sep_imp (fun _ h => h)
        (fun _ h => ⟨by omega, _, slice_length (by omega), h⟩))
        (fun _ h => h))) _ (hpush _)
    · rw [hsrc, hdxn]
    · rw [e8, hsi', hdi'] at hpost
      obtain ⟨hsp', hbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩ := hpost
      have hm2 := a2_Mm_mc_post k e a ra t₀ st fr hF hfm (by omega) (by omega) hd hm'
      have hfm2 : (wr st.fm 0 (slice fr 0x400 L)).length = 98 := by
        rw [wr_length (by rw [hsrc, hfm]; omega), hfm]
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨T.L298a.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩,
        { st with fm := wr st.fm 0 (slice fr 0x400 L) }, fr, hx, hsp, hfm2, hF,
        ⟨hk2v, hk1v, hlt, hInc0, hN0, hN1, ?_, h40, h30, hInc1, hnm, ?_, ?_, hxo, ?_, ?_⟩, hm2⟩⟩,
        hvar s'⟩
      · rw [hsp']; bv_omega
      · rw [hbp', hrbp]
      · rw [h12', h12]
      · rw [h13', h13]
      · rw [h14']; exact h14
      · rw [hbx', hbx]
      · intro i hi
        have hge := a2_inc_ge hInc0 i hi
        have := a2_u16_copy (fm := st.fm) (fr := fr) (o := 0) (fo := 0x400) (L := L) (j := i)
          (by omega) (by rw [hF]; omega) (hLi i hi) (by omega) (by omega)
          (Int.le_trans (Int.add_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)) hge)
        simpa using this

omit [CodeEnv] in
theorem a2_u16_wr_lt {l v : List UInt8} {o i : Nat} (h : o + v.length ≤ l.length)
    (hi : 2 * i + 2 ≤ o) : u16 (wr l o v) i = u16 l i := by
  unfold u16 u8
  simp only [List.getD_eq_getElem?_getD, getElem?_wr_ne h (Or.inl (by omega : 2 * i < o)),
    getElem?_wr_ne h (Or.inl (by omega : 2 * i + 1 < o))]

omit [CodeEnv] in
theorem a2_fv_shift (fr : List UInt8) (o j : Nat) : A2.fv fr (o + 2) j = A2.fv fr o (j + 1) := by
  simp only [A2.fv]; rw [show o + 2 + 2 * j = o + 2 * (j + 1) by omega]

set_option maxRecDepth 100000 in
/-- Two regions: `memcpy(f_master + nb0 + 1, vk1 + 1, 2 nb1)`. -/
theorem blk_L29a3 (k : Nat) (e : REnv) (hc : ResetCallees k e) (a : RArgs) (ra : Int64)
    (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L29a3" ⟨"sbr_reset.L29a3", B.L29a3, some "sbr_reset.L29a8"⟩ := by
  info_off
  measure_hb "L29a3"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hlt, hInc0, hN0, hN1, h12, h40, hInc1, hnm, h13, h14, hxo, hfm0, hdi, hsi,
        hdx⟩, hm⟩⟩ := T.L29a3.mp hs
    clear hs
    have hvar : ∀ s, var "sbr_reset.L29a8" s ≤ n := fun s => by rw [← hn]; var_step
    have hn0 : A2.n0N e a (k0N a row) k2 ≤ 48 := by
      show (A2.n0I e a (k0N a row) k2).toNat ≤ 48
      have := hN0.2.1; omega
    have hn1 : A2.n1N e a (k0N a row) k2 ≤ 48 := by
      show (A2.n1I e a (k0N a row) k2).toNat ≤ 48
      have := hN1.2.1; omega
    have hsum : A2.n0N e a (k0N a row) k2 + A2.n1N e a (k0N a row) k2 ≤ 48 := by
      have h1 := a2_inc_ge hInc0 _ (Nat.le_refl _); rw [hInc0.2.1] at h1
      have h2 := a2_inc_ge hInc1 _ (Nat.le_refl _); rw [hInc1.2.1] at h2
      have hk0 := k0Of_range hrow hC.2.1
      have hq : maxQ (srI a) ≤ 48 := by
        unfold maxQ; split
        · omega
        · split <;> omega
      simp only [k0A, k0N] at hkq h1 h2 ⊢
      omega
    obtain ⟨O, hO⟩ : ∃ O, 2 * (A2.n0N e a (k0N a row) k2 + 1) = O := ⟨_, rfl⟩
    obtain ⟨L, hL⟩ : ∃ L, 2 * A2.n1N e a (k0N a row) k2 = L := ⟨_, rfl⟩
    rw [hO] at hdi
    rw [hL] at hdx
    have hOL : O + L ≤ 98 := by omega
    have hOe : O % 2 = 0 := by omega
    have hO2 : O / 2 = A2.n0N e a (k0N a row) k2 + 1 := by omega
    have hLi : ∀ i, 1 ≤ i → i ≤ A2.n1N e a (k0N a row) k2 → 2 * (i - 1) + 2 ≤ L :=
      fun i _ hi => by omega
    have hOi : ∀ i, i ≤ A2.n0N e a (k0N a row) k2 → 2 * i + 2 ≤ O := fun i hi => by omega
    clear hL hO
    have hsrc : (slice fr 0x482 L).length = L := slice_length (by rw [hF]; omega)
    have hdxn : (s₀.regs.get64 .rdx).toNat = L := by
      rw [hdx, BitVec.toNat_ofNat]; omega
    have hsi' : s₀.regs.get64 .rsi = t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 0x482 := by
      rw [hsi, hrbp]; bv_omega
    have hd := reserve_le (focus (Mm_reserve ..) hm)
    rw [a2_Mm_mc (fo := 0x482) (o := O) (n := L) _ _ _ _ _ _ _ hF hfm (by omega) (by omega) hd] at hm
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rsp - 8#64) 8).isSome = true := by
      rw [hrsp]
      exact Block.loadInt_isSome hm (by simp)
    have hpush := fun v => Block.storeInt_val hm (Split.here _ _) v
    have e8 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 0x578#64 - 8#64 := by
      rw [hrsp]
    simp only [B.L29a3]
    vcgen [MachineWP.call_proc_spec_at
      (⟨A2McR k e a ra t₀ st fr 0x482 O L, slice fr 0x482 L⟩ : McA) "memcpy" hc.memcpy]
    all_goals try call_simp
    all_goals try (rename_i hss; subst hss)
    refine ⟨fun ra' => ⟨⟨?_, ?_⟩, fun s' hpost => ?_⟩, hld⟩
    · rw [e8, hsi', hdi, hdxn]
      exact sep_imp (fun _ h => h) (sep_imp (fun _ h => h) (sep_imp (sep_imp (fun _ h => h)
        (fun _ h => ⟨by omega, _, slice_length (by omega), h⟩))
        (fun _ h => h))) _ (hpush _)
    · rw [hsrc, hdxn]
    · rw [e8, hsi', hdi] at hpost
      obtain ⟨hsp', hbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩ := hpost
      have hm2 := a2_Mm_mc_post k e a ra t₀ st fr hF hfm (by omega) (by omega) hd hm'
      have hfm2 : (wr st.fm O (slice fr 0x482 L)).length = 98 := by
        rw [wr_length (by rw [hsrc, hfm]; omega), hfm]
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨T.L29a8.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩,
        { st with fm := wr st.fm O (slice fr 0x482 L) }, fr, hx, hsp, hfm2, hF,
        ⟨hk2v, hk1v, hlt, hInc0, hN0, hN1, ?_, h40, hInc1, hnm, ?_, ?_, hxo, ?_, ?_⟩, hm2⟩⟩,
        hvar s'⟩
      · rw [hsp']; bv_omega
      · rw [hbp', hrbp]
      · rw [h12', h12]
      · rw [h13', h13]
      · rw [h14']; exact h14
      · intro i hi
        show (u16 (wr st.fm O (slice fr 0x482 L)) i : Int) = _
        rw [a2_u16_wr_lt (by rw [hsrc, hfm]; omega) (hOi i hi)]
        exact hfm0 i hi
      · intro i h1 hi
        have hge := a2_inc_ge hInc1 i hi
        have := a2_u16_copy (fm := st.fm) (fr := fr) (o := O) (fo := 0x482) (L := L) (j := i - 1)
          (by omega) (by rw [hF]; omega) (hLi i h1 hi) hOe (by omega)
          (by rw [show (0x482 : Nat) = 0x480 + 2 from rfl, a2_fv_shift,
                show i - 1 + 1 = i by omega]
              exact Int.le_trans (Int.add_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)) hge)
        rw [hO2, show A2.n0N e a (k0N a row) k2 + 1 + (i - 1) = A2.n0N e a (k0N a row) k2 + i by omega,
          show (0x482 : Nat) = 0x480 + 2 from rfl, a2_fv_shift, show i - 1 + 1 = i by omega] at this
        exact this

omit [CodeEnv] in
theorem a2_ofNat_mul2 (x : Nat) (h : x < 2 ^ 63) :
    BitVec.ofNat 64 x * 2#64 = BitVec.ofNat 64 (2 * x) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : x < 2 ^ 64)]
  omega

omit [CodeEnv] in
theorem a2_ofNat_dbl (x : Nat) : BitVec.ofNat 64 x + BitVec.ofNat 64 x = BitVec.ofNat 64 (2 * x) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

set_option maxRecDepth 100000 in
/-- The operands of the second `memcpy`. -/
theorem blk_L298a (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L298a" ⟨"sbr_reset.L298a", B.L298a, some "sbr_reset.L29a3"⟩ := by
  info_off
  measure_hb "L298a"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hlt, hInc0, hN0, hN1, h12, h40, h30, hInc1, hnm, h13, h14, hxo, hbx, hfm0⟩,
        hm⟩⟩ := T.L298a.mp hs
    clear hs
    have hn0 : A2.n0N e a (k0N a row) k2 ≤ 48 := by
      show (A2.n0I e a (k0N a row) k2).toNat ≤ 48
      have := hN0.2.1; omega
    have hn1 : A2.n1N e a (k0N a row) k2 ≤ 48 := by
      show (A2.n1I e a (k0N a row) k2).toNat ≤ 48
      have := hN1.2.1; omega
    have hl30 := fr_load hm hF (d := 0x30) (n := 8) (by omega) (by omega)
    have e30 : t₀.regs.get64 .rsp - 8#64 + 18446744073709551568#64
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x30 := by bv_omega
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L298a]
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceMod,
        Nat.reducePow, Nat.reduceSub, Option.isSome_some]
    all_goals try simp only [hrbp, h12, e30, hl30, Option.isSome_some]
    rename_i v hl
    try simp only [hrbp, reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat] at hl
    have ea : t₀.regs.get64 .rsp - 8#64 + 0#64 + BitVec.ofNat 64 (2 ^ 64 - 48 % 2 ^ 64)
        = t₀.regs.get64 .rsp - 8#64 - 48#64 := by
      simp only [Nat.reducePow, Nat.reduceMod, Nat.reduceSub, BitVec.add_zero]; bv_omega
    rw [ea, hl30] at hl
    obtain rfl := Option.some.inj hl
    have hv : BitVec.ofInt 64 (Int.ofBytes (slice fr 1344 8))
        = BitVec.ofNat 64 (A2.n1N e a (k0N a row) k2) := h30
    refine ⟨T.L29a3.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st, fr, hx, hsp, hfm,
      hF, ⟨hk2v, hk1v, hlt, hInc0, hN0, hN1, ?_, h40, hInc1, hnm, ?_, ?_, hxo, hfm0, ?_, ?_, ?_⟩,
      hm⟩⟩, by var_step⟩
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrsp, hrbp, h12, h13, h14, hv]
    · rw [hbx]; simp only [arg1]
      rw [a2_ofNat_mul2 _ (by omega), show BitVec.setWidth 64 311792#64 = 311792#64 from rfl]
      generalize BitVec.ofNat 64 (2 * (A2.n0N e a (k0N a row) k2 + 1)) = X
      ac_rfl
    all_goals first | bv_omega | rw [a2_ofNat_dbl]

omit [CodeEnv] in
theorem a2_lo32_slice8 (l : List UInt8) (o : Nat) (h : o + 8 ≤ l.length) :
    (BitVec.ofInt 64 (Int.ofBytes (slice l o 8))).setWidth 32
      = BitVec.ofInt 32 (Int.ofBytes (slice l o 4)) := by
  have hs : slice l o 8 = slice l o 4 ++ slice l (o + 4) 4 := by
    simp only [slice]
    rw [show (8 : Nat) = 4 + 4 from rfl, List.take_add, List.drop_drop]
  have hl : (slice l o 4).length = 4 := slice_length (by omega)
  rw [hs, Int.ofBytes_append, hl]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt]
  generalize Int.ofBytes (slice l o 4) = A
  generalize Int.ofBytes (slice l (o + 4) 4) = B
  omega

/-- A store of `n_master`. -/
theorem a2_nm_store {k : Nat} {e : REnv} {a : RArgs} {ra : Int64} {t₀ : MachineData} {st : St}
    {fr : List UInt8} {m : Mem 64} (hm : m =⋆ Mm k e a ra t₀ st fr) (v : BitVec 32) :
    m.storeInt (arg1 t₀ + 0x68#64) 4 v.toInt =⋆ Mm k e a ra t₀ { st with nm := v } fr :=
  Mm_upd_nm .. ▸ cell4_store' (focus (Mm_nm ..) hm) v.toInt v rfl

omit [CodeEnv] in
theorem a2_or2_tab : ∀ j, j < 25 → BitVec.ofNat 64 (4 * j) ||| 2#64 = BitVec.ofNat 64 (4 * j + 2) := by
  decide

/-- The `memcpy` length `2 * (n0 + 1)` computed as `(F << 2) | 2` from `F + F = n0`. -/
theorem a2_rdx_or (F : BitVec 32) (n : Nat) (hn : n ≤ 48) (he : n % 2 = 0)
    (h : F + F = BitVec.ofNat 32 n) :
    BitVec.setWidth 64 (F <<< ((2#64).toNat % 32)) ||| BitVec.setWidth 64 2#64
      = BitVec.ofNat 64 (2 * (n + 1)) := by
  have hF := congrArg BitVec.toNat h
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at hF
  have h2 : (2#64).toNat % 32 = 2 := rfl
  rw [h2]
  have hx : BitVec.setWidth 64 (F <<< 2) = BitVec.ofNat 64 (4 * (n / 2)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    have := F.isLt
    omega
  rw [hx, show BitVec.setWidth 64 2#64 = 2#64 from rfl, a2_or2_tab _ (by omega)]
  congr 1; omega

set_option maxRecDepth 100000 in
/-- One region: `n_master = nb0`, the `bs_xover_band` check, the `memcpy` operands. -/
theorem blk_L1da7 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1da7" ⟨"sbr_reset.L1da7", B.L1da7, some "sbr_reset.L1dd9"⟩ := by
  info_off
  measure_hb "L1da7"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hSF, hN0, h12, h15, hone, hInc⟩, hm⟩⟩ := T.L1da7.mp hs
    clear hs
    have hn0 : A2.n0N e a (k0N a row) k2 ≤ 48 := by
      show (A2.n0I e a (k0N a row) k2).toNat ≤ 48
      have := hN0.2.1; omega
    have hl48 := fr_load hm hF (d := 0x48) (n := 8) (by omega) (by omega)
    have hnml := cell4_isSome (focus (Mm_nm ..) hm)
    have e48 : t₀.regs.get64 .rsp - 8#64 + 18446744073709551544#64
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x48 := by bv_omega
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L1da7]
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceMod,
        Nat.reducePow, Nat.reduceSub, Option.isSome_some] at *
    all_goals try simp only [hrbp, h12, e48, hl48, hnml, Option.isSome_some]
    all_goals try decide
    all_goals
      have hspl : st.sp.length = 6 := by rw [hsp]; exact hC.1
      have hsp2 := fun V => a2_sp_load (a2_nm_store hm V) hspl (i := 2) (by omega)
      have hl50 := fun V => fr_load (a2_nm_store hm V) hF (d := 0x50) (n := 8) (by omega) (by omega)
      have e50 : t₀.regs.get64 .rsp - 8#64 + 18446744073709551536#64
          = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x50 := by bv_omega
      have e30 : arg1 t₀ + 30#64 = arg1 t₀ + 0x1c#64 + BitVec.ofNat 64 2 := by bv_omega
      have hv48 : BitVec.ofInt 64 (Int.ofBytes (slice fr (rb 0x48) 8))
          = BitVec.ofNat 64 (A2.n0N e a (k0N a row) k2) := hSF.2
      have hV : BitVec.setWidth 32 (BitVec.ofInt 64 (Int.ofBytes (slice fr (rb 0x48) 8)))
          = BitVec.ofNat 32 (A2.n0N e a (k0N a row) k2) := by rw [hv48, a2_setWidth32_ofNat64]
      have hu2 : u8 st.sp 2 < 256 := UInt8.toNat_lt _
      have hxv : ∀ u : Nat, u < 256 → (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32
          (BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32
            (BitVec.ofInt 8 (u : Int)))))))).toNat = u := fun u hu => by
        simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt]; omega
    · -- the `bs_xover_band` load after the store
      rename_i v48 hl48'
      simp only [hrbp] at hl48'; rw [e48, hl48] at hl48'; obtain rfl := Option.some.inj hl48'
      rw [hV, e30, hsp2]; rfl
    · rename_i v48 vsp hl48' hlsp hz
      simp only [hrbp] at hl48'; rw [e48, hl48] at hl48'; obtain rfl := Option.some.inj hl48'
      rw [h12, hV, e30, hsp2] at hlsp; obtain rfl := Option.some.inj hlsp
      left; apply Table.ofLabels_at
      rw [hV]
      refine ⟨by decide, T.L1e00.mpr ⟨hC, ⟨?_, ?_⟩, ?_, ?_,
        { st with nm := BitVec.ofNat 32 (A2.n0N e a (k0N a row) k2) }, fr, ?_, hsp, hfm, hF,
        a2_nm_store hm _⟩, ?_⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15]
      · rw [hx]; exact a2_fail_reset hrow hC.2.1
      · edge_step
    · rename_i v48 vsp hl48' hlsp hz
      simp only [hrbp] at hl48'; rw [e48, hl48] at hl48'; obtain rfl := Option.some.inj hl48'
      rw [h12, hV, e30, hsp2] at hlsp; obtain rfl := Option.some.inj hlsp
      rw [hV, e50, hl50]; rfl
    · rename_i v48 vsp v50 fl bb hl48' hlsp hz hl50'
      simp only [hrbp] at hl48'; rw [e48, hl48] at hl48'; obtain rfl := Option.some.inj hl48'
      rw [h12, hV, e30, hsp2] at hlsp; obtain rfl := Option.some.inj hlsp
      simp only [hrbp, h12] at hl50'; rw [hV, e50, hl50] at hl50'; obtain rfl := Option.some.inj hl50'
      rw [hV, cc_be_sub, hxv _ (UInt8.toNat_lt _), BitVec.toNat_ofNat] at hz
      simp only [decide_eq_false_iff_not, Nat.not_le] at hz
      rw [hV]
      refine ⟨T.L1dd9.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩,
        { st with nm := BitVec.ofNat 32 (A2.n0N e a (k0N a row) k2) }, fr, hx, hsp, hfm, hF,
        ⟨hk2v, hk1v, ?_, ?_, hN0, hSF.1.1.1.2.2, hone, hInc, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩,
        a2_nm_store hm _⟩⟩, by var_step⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15]
      · exact hv48
      · rw [hsp]
        have h' : u8 a.sp 2 < 256 := UInt8.toNat_lt _
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
        omega
      · rw [hsp] at hz; simp only [u8]; omega
      · bv_omega
      · rw [Reg64s.get_low32]
        simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        rw [a2_lo32_slice8 fr (rb 80) (by rw [hF]; decide)]
        exact a2_rdx_or _ _ hn0 (by have := hN0.2.2; omega) hSF.1.1.1.2.1

set_option maxRecDepth 100000 in
/-- Two regions: `n_master = nb0 + nb1`, the `bs_xover_band` check, the `memcpy` operands. -/
theorem blk_L2949 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2949" ⟨"sbr_reset.L2949", B.L2949, some "sbr_reset.L297e"⟩ := by
  info_off
  measure_hb "L2949"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hlt, hInc0, hN0, hN1, h12, h13, vm, hTA, h30, hInc1⟩, hm⟩⟩ := T.L2949.mp hs
    clear hs
    have hn0 : A2.n0N e a (k0N a row) k2 ≤ 48 := by
      show (A2.n0I e a (k0N a row) k2).toNat ≤ 48
      have := hN0.2.1; omega
    have hn1 : A2.n1N e a (k0N a row) k2 ≤ 48 := by
      show (A2.n1I e a (k0N a row) k2).toNat ≤ 48
      have := hN1.2.1; omega
    have hl48 := fr_load hm hF (d := 0x48) (n := 4) (by omega) (by omega)
    have hnml := cell4_isSome (focus (Mm_nm ..) hm)
    have hav : st.x.avctx = a.x.avctx := by rw [hx]
    have hn1p : 2 ≤ A2.n1N e a (k0N a row) k2 := by
      show 2 ≤ (A2.n1I e a (k0N a row) k2).toNat
      have := hN1.1; omega
    have hV48 : BitVec.ofInt 32 (Int.ofBytes (slice fr (rb 0x48) 4))
        = BitVec.ofNat 32 (A2.n0N e a (k0N a row) k2) := by
      rw [← a2_lo32_slice8 fr (rb 0x48) (by rw [hF]; decide)]
      exact (congrArg (BitVec.setWidth 32) hTA.2.1).trans (a2_setWidth32_ofNat64 _)
    have e48 : t₀.regs.get64 .rsp - 8#64 + 18446744073709551544#64
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x48 := by bv_omega
    have hr13f : BitVec.setWidth 64 (BitVec.ofNat 32 (A2.n0N e a (k0N a row) k2 + A2.n1N e a (k0N a row) k2))
        = BitVec.ofNat 64 (A2.n0N e a (k0N a row) k2 + A2.n1N e a (k0N a row) k2) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
    have hlt' : ∀ u : Nat, u < (A2.n0N e a (k0N a row) k2 + A2.n1N e a (k0N a row) k2) % 2 ^ 32 →
        u < A2.n0N e a (k0N a row) k2 + A2.n1N e a (k0N a row) k2 := fun u h => by omega
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L2949]
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceMod,
        Nat.reducePow, Nat.reduceSub, Option.isSome_some] at *
    all_goals try simp only [hrbp, h12, e48, hl48, hnml, Option.isSome_some]
    all_goals
      have hspl : st.sp.length = 6 := by rw [hsp]; exact hC.1
      have hsp2 := fun V => a2_sp_load (a2_nm_store hm V) hspl (i := 2) (by omega)
      have hl40 := fun V => fr_load (a2_nm_store hm V) hF (d := 0x40) (n := 8) (by omega) (by omega)
      have hl88 := fun V => fr_load (a2_nm_store hm V) hF (d := 0x88) (n := 8) (by omega) (by omega)
      have hlav := fun V => avctx_load (a2_nm_store hm V)
      have e40 : t₀.regs.get64 .rsp - 8#64 + 18446744073709551552#64
          = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x40 := by bv_omega
      have e88 : t₀.regs.get64 .rsp - 8#64 + 18446744073709551480#64
          = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x88 := by bv_omega
      have e30 : arg1 t₀ + 30#64 = arg1 t₀ + 0x1c#64 + BitVec.ofNat 64 2 := by bv_omega
      have h40v : BitVec.ofInt 64 (Int.ofBytes (slice fr (rb 0x40) 8)) = arg0 t₀ := hTA.1
      have h88v : BitVec.ofInt 64 (Int.ofBytes (slice fr (rb 0x88) 8))
          = BitVec.ofNat 64 (A2.n0N e a (k0N a row) k2 + 1) := hTA.2.2.1
      have hu2 : u8 st.sp 2 < 256 := UInt8.toNat_lt _
      have hxv : ∀ u : Nat, u < 256 → (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32
          (BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32
            (BitVec.ofInt 8 (u : Int)))))))).toNat = u := fun u hu => by
        simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt]; omega
    · rename_i v48 hl48'
      simp only [hrbp] at hl48'; rw [e48, hl48] at hl48'; obtain rfl := Option.some.inj hl48'
      rw [e40, hl40]; rfl
    · rename_i v48 v40 hl48' hl40'
      simp only [hrbp] at hl48'; rw [e48, hl48] at hl48'; obtain rfl := Option.some.inj hl48'
      simp only [hrbp, h12] at hl40'; rw [e40, hl40] at hl40'; obtain rfl := Option.some.inj hl40'
      rw [h40v, hlav]; rfl
    · rename_i v48 v40 vav hle hl48' hl40' hlav'
      simp only [hrbp] at hl48'; rw [e48, hl48] at hl48'; obtain rfl := Option.some.inj hl48'
      rw [hV48, h13, a2_setWidth32_ofNat64, a2_cc_le_add _ _ hn0 hn1 (by omega)] at hle
      exact absurd hle (by decide)
    · rw [e30, hsp2]; rfl
    · rename_i v48 v40 vav hle vsp hl48' hl40' hlav' hlsp hbe
      simp only [hrbp] at hl48'; rw [e48, hl48] at hl48'; obtain rfl := Option.some.inj hl48'
      simp only [hrbp, h12] at hl40'; rw [e40, hl40] at hl40'; obtain rfl := Option.some.inj hl40'
      rw [h40v, h12, hlav] at hlav'; obtain rfl := Option.some.inj hlav'
      rw [hV48, h13, a2_setWidth32_ofNat64, ← BitVec.ofNat_add, sw32_64]
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L29ad.mpr ⟨⟨hC, ⟨?_, ?_⟩, ?_, ?_,
        { st with nm := BitVec.ofNat 32 (A2.n0N e a (k0N a row) k2 + A2.n1N e a (k0N a row) k2) },
        fr, ?_, hsp, hfm, hF, a2_nm_store hm _⟩, ?_⟩, ?_⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h40v,
        BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]
      all_goals first
        | (rw [hx]; exact a2_fail_reset hrow hC.2.1)
        | exact hav
        | edge_step
    · rw [e88, hl88]; rfl
    · rename_i v48 v40 vav hle vsp v88 hl48' hl40' hlav' hlsp hbe hl88'
      simp only [hrbp] at hl48'; rw [e48, hl48] at hl48'; obtain rfl := Option.some.inj hl48'
      simp only [hrbp, h12] at hl40'; rw [e40, hl40] at hl40'; obtain rfl := Option.some.inj hl40'
      rw [h40v, h12, hlav] at hlav'; obtain rfl := Option.some.inj hlav'
      simp only [h12] at hlsp; rw [e30, hsp2] at hlsp; obtain rfl := Option.some.inj hlsp
      simp only [hrbp, h12] at hl88'; rw [e88, hl88] at hl88'; obtain rfl := Option.some.inj hl88'
      rw [hV48, h13, a2_setWidth32_ofNat64, ← BitVec.ofNat_add, sw32_64, cc_be_sub,
        hxv _ (UInt8.toNat_lt _), BitVec.toNat_ofNat] at hbe
      simp only [decide_eq_false_iff_not, Nat.not_le] at hbe
      rw [hV48, h13, a2_setWidth32_ofNat64, ← BitVec.ofNat_add, sw32_64]
      refine ⟨T.L297e.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩,
        { st with nm := BitVec.ofNat 32 (A2.n0N e a (k0N a row) k2 + A2.n1N e a (k0N a row) k2) },
        fr, hx, hsp, hfm, hF, ⟨hk2v, hk1v, hlt, hInc0, hN0, hN1, ?_, ?_, hTA.1, h30, hInc1, rfl,
          ?_, ?_, ?_, ?_, ?_, ?_⟩, a2_nm_store hm _⟩⟩, by var_step⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h40v, h88v]
      all_goals first
        | rfl
        | (rw [a2_ofNat_dbl])
        | (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega)
        | (rw [hsp]; have h' : u8 a.sp 2 < 256 := UInt8.toNat_lt _
           apply BitVec.eq_of_toNat_eq
           simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ofNat]; omega)
        | (rw [hsp] at hbe; simp only [u8]; omega)
        | bv_omega
        | exact hr13f
        | exact hlt' _ (by have h := hbe; rw [hsp] at h; exact h)

end Kraken.Examples.Sbr.Reset
