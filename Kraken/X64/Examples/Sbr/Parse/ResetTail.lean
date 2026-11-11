import Kraken.InfoOff
import Kraken.X64.Examples.Sbr.Parse.ResetTable
import Kraken.X64.Examples.Sbr.Parse.ResetModel
import Kraken.X64.Examples.Sbr.Parse.ResetLog
import Kraken.X64.Examples.Sbr.Parse.ResetExitW

/-!
# `sbr_reset`: the success tail (shard B)

`L3228`: `sbr_make_f_tablelim(sbr)` (contract `TlimSpec`); `L3230`: `f_indexnoise = 0` for both
channels (4-byte stores into the low half of the 8-byte `idx` cells), then the epilogue with
`ResetOut`'s success case (`Reset.ok` via `Derived.ok`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Reset

/-! ## Model: the success exit -/

/-- `Derived` succeeded: `ResetOut`'s second case with `spectrum_params`, `usac` kept. -/
theorem resetOut_ok {a : RArgs} {z : Args} (hs : Scal a.x) (hl : RLens a.x) (hst : u8 a.sp 0 < 16)
    (h : DerOk a z) : ResetOut a z a.sp a.us := by
  obtain ⟨k0, nm, f, hm, hd⟩ := h
  have hr : Reset (⟨u8 a.sp 0, u8 a.sp 2⟩ : Spec) a.lb.toNat a.x z := Reset.ok hst hm hd
  obtain ⟨k1, k2, k3⟩ := reset_keeps hr
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := hs
  obtain ⟨_, b1, b2, b3, b4, b5, b6, b7, b8⟩ := master_ok hst hm
  obtain ⟨c1, c2, -, -, -, c6, c7, c8⟩ := derived_spec hd b1 b2 b3 b4 b5 b6 b7 b8
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9⟩ := c8 rfl
  have t1 := c7.1; have t2 := c7.2.1; have t3 := c7.2.2.1
  exact ⟨⟨by rw [t1]; exact a1, d2, by rw [t1, t2]; exact a3, d3, d4, by rw [c6]; exact b2,
    by rw [t3]; exact a7, c1, c2, d5, d6, d7⟩, reset_lens hr hl, z, c7, k1, k2, k3,
    Or.inr ⟨rfl, rfl, rfl, d1, d8, d9⟩⟩

/-- The tail's step: `TailOk` and `sbr_make_f_tablelim`'s result give `DerOk` with
`f_indexnoise` cleared. -/
theorem derOk_of_tail {a : RArgs} {y z : Args} (h : TailOk a y) (ht : Tablelim a.lb.toNat y z) :
    DerOk a { z with d0 := clrNoise z.d0, d1 := clrNoise z.d1 } := by
  obtain ⟨k0, nm, f, q, hm, h1, h2, h3, h4, hp⟩ := h
  exact ⟨k0, nm, f, hm, Derived.ok q h1 h2 h3 h4 hp ht⟩

/-! ## Bytes: `movl $0` into the low half of an 8-byte cell -/

theorem toBytes8_toInt (v : BitVec 64) : Int.toBytes 8 v.toInt = Int.toBytes 8 (v.toNat : Int) := by
  rw [← Int.toBytes_emod 8 v.toInt, ← Int.toBytes_emod 8 (v.toNat : Int)]
  congr 1
  simp only [Int.take]
  rw [BitVec.toInt_eq_toNat_bmod]
  have := Int.bmod_emod (x := (v.toNat : Int)) (m := 2 ^ 64)
  simpa using this

theorem clr_bytes (v : BitVec 64) :
    wr (Int.toBytes 8 v.toInt) 0 (Int.toBytes 4 (0 : Int))
      = Int.toBytes 8 (BitVec.ofNat 64 (v.toNat / 2 ^ 32 * 2 ^ 32)).toInt := by
  rw [toBytes8_toInt, toBytes8_toInt]
  have hv := v.isLt
  simp only [BitVec.toNat_ofNat]
  generalize v.toNat = x at hv ⊢
  simp only [wr, Int.toBytes, List.take_zero, List.nil_append, Nat.zero_add,
    List.length_cons, List.length_nil, List.drop_succ_cons, List.drop_zero, List.cons_append,
    List.nil_append, List.cons.injEq, Int.take, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> congr 2 <;> omega

/-- A 4-byte zero store at an 8-byte `idx` cell clears `f_indexnoise`. -/
theorem c8_clr {m : Mem 64} {A : BitVec 64} {d : DV} {F : Mem 64 → Prop}
    (h : m =⋆ c8 A d.idx ⋆ F) (w : Int) (hw : Int.toBytes 4 w = Int.toBytes 4 (0 : Int)) :
    m.storeInt A 4 w =⋆ c8 A (clrNoise d).idx ⋆ F := by
  have := region_store (o := 0) (n := 4) h (addr := A) (BitVec.add_zero A).symm
    (by rw [Int.toBytes_length]; omega) (by rw [Int.toBytes_length]; decide) w
  rw [hw, clr_bytes] at this
  exact this

/-! ## Footprint at the `sbr_make_f_tablelim` call -/

variable [CodeEnv]

/-- `Mm` without the reservation and `sbr_make_f_tablelim`'s cells (`TlimF`). -/
def Mx_tl (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) (st : St) (fr : List UInt8) : Mem 64 → Prop :=
  fr =@ ((t₀.regs.get64 .rsp) - 0x578#64)
    ⋆ Saved t₀ ⋆ RetCell ra (t₀.regs.get64 .rsp) ⋆ cell4 (arg1 t₀) st.x.sampleRate
    ⋆ cell4 ((arg1 t₀) + 0x4#64) st.x.start ⋆ cell4 ((arg1 t₀) + 0x8#64) st.x.ready
    ⋆ cell4 ((arg1 t₀) + 0x10#64) a.us ⋆ st.sp =@ ((arg1 t₀) + 0x1c#64)
    ⋆ c4 ((arg1 t₀) + 0x40#64) st.x.k0 ⋆ cell4 ((arg1 t₀) + 0x44#64) st.k1
    ⋆ cell4 ((arg1 t₀) + 0x48#64) st.k2
    ⋆ c4 ((arg1 t₀) + 0x60#64) st.x.m1 ⋆ cell4 ((arg1 t₀) + 0x68#64) st.nm
    ⋆ c4 ((arg1 t₀) + 0x4c1e4#64) st.x.n1
    ⋆ c4 ((arg1 t₀) + 0x4c1e8#64) st.x.nq
    ⋆ st.fm =@ ((arg1 t₀) + 0x4c1f0#64)
    ⋆ st.x.ftHigh =@ ((arg1 t₀) + 0x4c284#64) ⋆ st.x.ftNoise =@ ((arg1 t₀) + 0x4c2e6#64)
    ⋆ st.x.pstart =@ ((arg1 t₀) + 0x4c33a#64)
    ⋆ 4 ?@ ((arg1 t₀) + 0x3988#64) ⋆ c8 ((arg1 t₀) + 0x15b2c#64) st.x.d0.idx
    ⋆ 4 ?@ ((arg1 t₀) + 0x19448#64) ⋆ c8 ((arg1 t₀) + 0x2b5ec#64) st.x.d1.idx
    ⋆ c8 (arg0 t₀ + 0x8#64) st.x.avctx ⋆ CstR ⋆ e.Ext ⋆ a.x.R

/-- `TlimF` at the address `s` of `*sbr`. -/
def TlA (lb : BitVec 32) (a : Args) (s : BitVec 64) : Mem 64 → Prop :=
  cell4 (s + 0x2c#64) lb ⋆ (c4 (s + 0x58#64) a.kx1 ⋆ (c4 (s + 0x4c1e0#64) a.n0
    ⋆ (c4 (s + 0x4c1ec#64) a.nlim ⋆ (a.ftLow =@ (s + 0x4c252#64) ⋆ (a.ftLim =@ (s + 0x4c2f2#64)
    ⋆ (c4 (s + 0x4c330#64) a.npatch ⋆ (a.pnum =@ (s + 0x4c334#64)
    ⋆ Blocks [(lab "sbr_make_f_tablelim_bw", 12)])))))))

theorem TlimF_eq (lb : BitVec 32) (a : Args) (t : MachineData) : TlimF lb a t = TlA lb a (arg0 t) :=
  rfl

theorem Mm_tl (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) (st : St)
    (fr : List UInt8) (hd : 8 + tlimNeed k ≤ (t₀.regs.get64 .rsp - 0x578#64).toNat) :
    Mm k e a ra t₀ st fr = 8 ?@ (t₀.regs.get64 .rsp - 0x578#64 - 8#64)
      ⋆ (Reserve (tlimNeed k) (t₀.regs.get64 .rsp - 0x578#64 - 8#64)
        ⋆ (TlA a.lb st.x (arg1 t₀) ⋆ Mx_tl k e a ra t₀ st fr)) := by
  simp only [Mm, Reserve_split 8 (tlimNeed k) (t₀.regs.get64 .rsp - 0x578#64) (by omega), TlA,
    Mx_tl, BwR]
  ac_rfl

/-- `sbr_make_f_tablelim` changes only `f_tablelim` and `n_lim`, outside `Mx_tl`. -/
theorem Mx_tl_lim {k : Nat} {e : REnv} {a : RArgs} {ra : Int64} {t₀ : MachineData} {st : St}
    {fr : List UInt8} {lb : Nat} {y : Args} (ht : Tablelim lb st.x y) :
    Mx_tl k e a ra t₀ { st with x := y } fr = Mx_tl k e a ra t₀ st fr := by
  cases ht <;> rfl

set_option maxRecDepth 100000 in
/-- `sbr_make_f_tablelim(sbr)`. -/
theorem blk_L3228 (k : Nat) (e : REnv) (hc : ResetCallees k e) (a : RArgs) (ra : Int64)
    (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L3228" ⟨"sbr_reset.L3228", B.L3228, some "sbr_reset.L3230"⟩ := by
  info_off
  measure_hb "L3228"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hC, ⟨hrsp, hrbp⟩, h12, st, fr, ⟨hT, hI⟩, hsp, hfm, hF, hm⟩ := T.L3228.mp hs
    clear hs
    have hd := reserve_le (focus (Mm_reserve ..) hm)
    rw [Mm_tl k e a ra t₀ st fr hd] at hm
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rsp - 8#64) 8).isSome = true := by
      rw [hrsp]
      exact Block.loadInt_isSome hm (by simp)
    have hpush := fun v => Block.storeInt_val hm (Split.here _ _) v
    have e8 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 0x578#64 - 8#64 := by
      rw [hrsp]
    simp only [B.L3228]
    vcgen [MachineWP.call_proc_spec_at
      ((Mx_tl k e a ra t₀ st fr, a.lb, st.x) : (Mem 64 → Prop) × BitVec 32 × Args)
        "sbr_make_f_tablelim" hc.tlim]
    all_goals try call_simp
    all_goals try subst_vars
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16⟩ := hC
    obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10⟩ := hI
    refine ⟨fun ra' => ⟨⟨?_, ?_⟩, fun s' hpost => ?_⟩, hld⟩
    · simp only [TlimF_eq, arg0, MachineData.pushRa, Reg64s.get64_set64, h12, e8]
      exact hpush _
    · refine ⟨c6, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, ?_⟩
      simp only [arg0, MachineData.pushRa, Reg64s.get64_set64, h12, reduceCtorEq, ↓reduceIte]
      simp only [arg1] at c13
      omega
    · obtain ⟨y, hy, hsp', hbp', ⟨-, h12', -, -, -⟩, hm'⟩ := hpost
      simp only [TlimF_eq, arg0, MachineData.pushRa, Reg64s.get64_set64, h12, e8] at hm'
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨T.L3230.mpr ⟨⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16⟩,
        ⟨?_, ?_⟩, ?_, { st with x := y }, fr, derOk_of_tail hT hy, hsp, hfm, hF, ?_⟩, by var_step⟩
      · rw [hsp', e8]; bv_omega
      · rw [hbp', hrbp]
      · rw [h12', h12]
      · rw [Mm_tl k e a ra t₀ _ fr hd, Mx_tl_lim hy]
        exact hm'

/-- `idx` of channel 0 at a new value (`v` abstract: no unfolding of the value). -/
theorem Mm_upd_idx0 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) (st : St)
    (fr : List UInt8) (v : DV) :
    c8 ((arg1 t₀) + 0x15b2c#64) v.idx ⋆ Mx_idx0 k e a ra t₀ st fr
      = Mm k e a ra t₀ { st with x := { st.x with d0 := v } } fr := by
  rw [Mm_idx0]; rfl

theorem Mm_upd_idx1 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) (st : St)
    (fr : List UInt8) (v : DV) :
    c8 ((arg1 t₀) + 0x2b5ec#64) v.idx ⋆ Mx_idx1 k e a ra t₀ st fr
      = Mm k e a ra t₀ { st with x := { st.x with d1 := v } } fr := by
  rw [Mm_idx1]; rfl

/-- `Mm` without the two `idx` cells. -/
def Mx_idx01 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) (st : St) (fr : List UInt8) : Mem 64 → Prop :=
  Reserve (8 + tlimNeed k) ((t₀.regs.get64 .rsp) - 0x578#64) ⋆ fr =@ ((t₀.regs.get64 .rsp) - 0x578#64)
    ⋆ Saved t₀ ⋆ RetCell ra (t₀.regs.get64 .rsp) ⋆ cell4 (arg1 t₀) st.x.sampleRate
    ⋆ cell4 ((arg1 t₀) + 0x4#64) st.x.start ⋆ cell4 ((arg1 t₀) + 0x8#64) st.x.ready
    ⋆ cell4 ((arg1 t₀) + 0x10#64) a.us ⋆ st.sp =@ ((arg1 t₀) + 0x1c#64) ⋆ cell4 ((arg1 t₀) + 0x2c#64) a.lb
    ⋆ c4 ((arg1 t₀) + 0x40#64) st.x.k0 ⋆ cell4 ((arg1 t₀) + 0x44#64) st.k1
    ⋆ cell4 ((arg1 t₀) + 0x48#64) st.k2 ⋆ c4 ((arg1 t₀) + 0x58#64) st.x.kx1
    ⋆ c4 ((arg1 t₀) + 0x60#64) st.x.m1 ⋆ cell4 ((arg1 t₀) + 0x68#64) st.nm
    ⋆ c4 ((arg1 t₀) + 0x4c1e0#64) st.x.n0 ⋆ c4 ((arg1 t₀) + 0x4c1e4#64) st.x.n1
    ⋆ c4 ((arg1 t₀) + 0x4c1e8#64) st.x.nq ⋆ c4 ((arg1 t₀) + 0x4c1ec#64) st.x.nlim
    ⋆ st.fm =@ ((arg1 t₀) + 0x4c1f0#64) ⋆ st.x.ftLow =@ ((arg1 t₀) + 0x4c252#64)
    ⋆ st.x.ftHigh =@ ((arg1 t₀) + 0x4c284#64) ⋆ st.x.ftNoise =@ ((arg1 t₀) + 0x4c2e6#64)
    ⋆ st.x.ftLim =@ ((arg1 t₀) + 0x4c2f2#64) ⋆ c4 ((arg1 t₀) + 0x4c330#64) st.x.npatch
    ⋆ st.x.pnum =@ ((arg1 t₀) + 0x4c334#64) ⋆ st.x.pstart =@ ((arg1 t₀) + 0x4c33a#64)
    ⋆ 4 ?@ ((arg1 t₀) + 0x3988#64) ⋆ 4 ?@ ((arg1 t₀) + 0x19448#64)
    ⋆ c8 (arg0 t₀ + 0x8#64) st.x.avctx ⋆ CstR ⋆ BwR
    ⋆ e.Ext ⋆ a.x.R

theorem Mm_idx01 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) (st : St)
    (fr : List UInt8) :
    Mm k e a ra t₀ st fr = c8 ((arg1 t₀) + 0x15b2c#64) st.x.d0.idx
      ⋆ (c8 ((arg1 t₀) + 0x2b5ec#64) st.x.d1.idx ⋆ Mx_idx01 k e a ra t₀ st fr) := by
  simp only [Mm, Mx_idx01]; ac_rfl

theorem Mm_upd_idx01 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) (st : St)
    (fr : List UInt8) (v0 v1 : DV) :
    c8 ((arg1 t₀) + 0x2b5ec#64) v1.idx ⋆ (c8 ((arg1 t₀) + 0x15b2c#64) v0.idx ⋆ Mx_idx01 k e a ra t₀ st fr)
      = Mm k e a ra t₀ { st with x := { st.x with d0 := v0, d1 := v1 } } fr := by
  simp only [Mm, Mx_idx01]; ac_rfl

theorem Mm_clr2 {k : Nat} {e : REnv} {a : RArgs} {ra : Int64} {t₀ : MachineData} {st : St}
    {fr : List UInt8} {m : Mem 64} (h : m =⋆ Mm k e a ra t₀ st fr) (w : Int)
    (hw : Int.toBytes 4 w = Int.toBytes 4 (0 : Int)) :
    (m.storeInt (arg1 t₀ + 0x15b2c#64) 4 w).storeInt (arg1 t₀ + 0x2b5ec#64) 4 w
      =⋆ Mm k e a ra t₀ { st with x := { st.x with d0 := clrNoise st.x.d0, d1 := clrNoise st.x.d1 } } fr := by
  rw [Mm_idx01] at h
  have s1 := c8_clr h w hw
  rw [Std.ExtHashMap.sep_comm_l] at s1
  have s2 := c8_clr s1 w hw
  rw [Mm_upd_idx01] at s2
  exact s2

theorem ld_clr2 {k : Nat} {e : REnv} {a : RArgs} {ra : Int64} {t₀ : MachineData} {st : St}
    {fr : List UInt8} {m : Mem 64} (h : m =⋆ Mm k e a ra t₀ st fr) (w : Int)
    (hw : Int.toBytes 4 w = Int.toBytes 4 (0 : Int)) :
    (m.loadInt (arg1 t₀ + 0x15b2c#64) 4).isSome = true
    ∧ ((m.storeInt (arg1 t₀ + 0x15b2c#64) 4 w).loadInt (arg1 t₀ + 0x2b5ec#64) 4).isSome = true := by
  rw [Mm_idx01] at h
  refine ⟨val_isSome h (by simp [Int.toBytes_length]) (by simp [Int.toBytes_length]), ?_⟩
  have s1 := c8_clr h w hw
  rw [Std.ExtHashMap.sep_comm_l] at s1
  exact val_isSome s1 (by simp [Int.toBytes_length]) (by simp [Int.toBytes_length])

set_option maxRecDepth 100000 in
/-- `f_indexnoise = 0` (both channels), then the epilogue. -/
theorem blk_L3230 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L3230" ⟨"sbr_reset.L3230", B.L3230, some "sbr_reset.L324d"⟩ := by
  info_off
  measure_hb "L3230"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hC, ⟨hrsp, hrbp⟩, h12, st, fr, hD, hsp, hfm, hF, hm⟩ := T.L3230.mp hs
    clear hs
    have hw : Int.toBytes 4 (BitVec.setWidth 32 (0#64)).toInt = Int.toBytes 4 (0 : Int) := by decide
    obtain ⟨ld1, ld2⟩ := ld_clr2 hm _ hw
    have s2 := Mm_clr2 hm _ hw
    have hout := resetOut_ok hC.2.2.2.2.1 (resetC_lens hC) hC.2.1 hD
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    rw [← hsp] at hout
    clear hm
    simp only [B.L3230]
    vcgen
    all_goals try subst_vars
    all_goals simp only [h12, AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, z]
    · with_reducible exact ld1
    · with_reducible exact ld2
    · exact Or.inl <| Table.ofLabels_at ⟨S.L1d95, T.L1d95.mpr ⟨hC, ⟨hrsp, hrbp⟩, a.us,
        { st with x := { st.x with d0 := clrNoise st.x.d0, d1 := clrNoise st.x.d1 } }, fr, hout, hfm, hF, s2⟩,
        by edge_step⟩

end Kraken.Examples.Sbr.Reset
