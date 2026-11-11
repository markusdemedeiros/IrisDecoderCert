import Kraken.InfoOff
import Kraken.X64.Examples.Sbr.Parse.ResetTable
import Kraken.X64.Examples.Sbr.Parse.ResetModel

/-!
# `sbr_reset`: `sbr_turnoff`'s first stores (shard B)

`movq $0, 4(%r12)` clears `start` and `ready_for_dequant` with one 8-byte store.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Reset

variable [CodeEnv]

/-- `Mm` without `start`, `ready`. -/
def Mx_sr2 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) (st : St) (fr : List UInt8) : Mem 64 → Prop :=
  Reserve (8 + tlimNeed k) ((t₀.regs.get64 .rsp) - 0x578#64) ⋆ fr =@ ((t₀.regs.get64 .rsp) - 0x578#64)
    ⋆ Saved t₀ ⋆ RetCell ra (t₀.regs.get64 .rsp) ⋆ cell4 (arg1 t₀) st.x.sampleRate
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
    ⋆ 4 ?@ ((arg1 t₀) + 0x3988#64) ⋆ c8 ((arg1 t₀) + 0x15b2c#64) st.x.d0.idx
    ⋆ 4 ?@ ((arg1 t₀) + 0x19448#64) ⋆ c8 ((arg1 t₀) + 0x2b5ec#64) st.x.d1.idx
    ⋆ c8 (arg0 t₀ + 0x8#64) st.x.avctx ⋆ CstR ⋆ BwR ⋆ e.Ext ⋆ a.x.R

theorem Mm_sr2 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) (st : St) (fr : List UInt8) :
    Mm k e a ra t₀ st fr = (cell4 ((arg1 t₀) + 0x4#64) st.x.start ⋆ cell4 ((arg1 t₀) + 0x8#64) st.x.ready)
      ⋆ Mx_sr2 k e a ra t₀ st fr := by
  simp only [Mm, Mx_sr2]; ac_rfl

omit [CodeEnv] in
/-- Two adjacent 4-byte cells are one 8-byte region. -/
theorem cell4_pair (p q : BitVec 64) (hq : q = p + 0x4#64) (v w : BitVec 32) :
    (cell4 p v ⋆ cell4 q w) = (Int.toBytes 4 v.toInt ++ Int.toBytes 4 w.toInt) =@ p := by
  subst hq
  simp only [cell4, Val.eq]
  rw [At_append_sep _ _ _ (by simp [Int.toBytes_length]), Int.toBytes_length]

omit [CodeEnv] in
/-- An 8-byte store of zero over two adjacent 4-byte cells. -/
theorem cell4_pair_store0 {m : Mem 64} {p q : BitVec 64} (hq : q = p + 0x4#64) {v w : BitVec 32}
    {F : Mem 64 → Prop} (h : m =⋆ (cell4 p v ⋆ cell4 q w) ⋆ F) (z : Int)
    (hz : Int.toBytes 8 z = Int.toBytes 4 (0 : BitVec 32).toInt ++ Int.toBytes 4 (0 : BitVec 32).toInt) :
    m.storeInt p 8 z =⋆ (cell4 p 0 ⋆ cell4 q 0) ⋆ F := by
  rw [cell4_pair p q hq] at h ⊢
  have := storeInt_sep p 8 _ F m ⟨h, by simp [Int.toBytes_length]⟩ z
  rw [hz] at this
  exact this

/-- `Mx_usac` does not read `usac`. -/
theorem Mx_usac_offA (j k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) (st : St)
    (fr : List UInt8) : Mx_usac k e (offA j a) ra t₀ st fr = Mx_usac k e a ra t₀ st fr := by
  cases j <;> rfl

set_option maxRecDepth 100000 in
/-- `start = ready = 0` (one 8-byte store), `usac = 0`. -/
theorem blk_L1d4d (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1d4d" ⟨"sbr_reset.L1d4d", B.L1d4d, some "sbr_reset.L1d5f"⟩ := by
  info_off
  measure_hb "L1d4d"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hC, ⟨hrsp, hrbp⟩, h12, hbx, st, fr, hM, hsp, hfm, hF, hm⟩ := T.L1d4d.mp hs
    clear hs
    have hq : arg1 t₀ + 0x8#64 = arg1 t₀ + 0x4#64 + 0x4#64 := by bv_omega
    have h0 : s₀.dmem =⋆ (cell4 (arg1 t₀ + 0x4#64) st.x.start ⋆ cell4 (arg1 t₀ + 0x8#64) st.x.ready)
        ⋆ Mx_sr2 k e a ra t₀ st fr := by
      have hm' := hm; rw [Mm_sr2] at hm'; exact hm'
    have ld1 : (s₀.dmem.loadInt (arg1 t₀ + 0x4#64) 8).isSome = true := by
      have h := h0
      rw [cell4_pair _ _ hq] at h
      exact val_isSome h (by simp [Int.toBytes_length]) (by simp [Int.toBytes_length])
    have s1 := cell4_pair_store0 hq h0 (BitVec.setWidth 64 (0#64)).toInt (by decide)
    have s1' : s₀.dmem.storeInt (arg1 t₀ + 0x4#64) 8 (BitVec.setWidth 64 (0#64)).toInt
        =⋆ Mm k e a ra t₀ (offSt 1 st) fr := by
      rw [Mm_sr2]; exact s1
    have ld2 := cell4_isSome (focus (Mm_usac ..) s1')
    have s2 := cell4_store' (focus (Mm_usac ..) s1') (BitVec.setWidth 32 (0#64)).toInt
      (offA 1 a).us (by simp only [offA]; decide)
    rw [← Mx_usac_offA 1, ← Mm_usac] at s2
    clear s1 s1' hm h0
    simp only [B.L1d4d]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    vcgen
    all_goals try subst_vars
    all_goals simp only [h12, AddrIndex.offset64_none, z, Int64.toBitVec_ofNat_norm]
    · with_reducible exact ld1
    · with_reducible exact ld2
    · rename_i s
      refine ⟨T.L1d5f.mpr ⟨hC, ⟨hrsp, hrbp⟩, h12, hbx, st, fr, hM, hsp, hfm, hF, s2⟩, ?_⟩
      var_step

omit [CodeEnv] in
theorem c8_load {m : Mem 64} {addr : BitVec 64} {F : Mem 64 → Prop} {v : BitVec 64}
    (h : m =⋆ c8 addr v ⋆ F) : m.loadInt addr 8 = some (Int.ofBytes (Int.toBytes 8 v.toInt)) :=
  loadInt_sep _ _ 8 F m h (Int.toBytes_length 8 _) (by omega)

set_option maxRecDepth 100000 in
/-- The last `av_log`'s arguments, `rbx = &spectrum_params`. -/
theorem blk_L1d31 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1d31" ⟨"sbr_reset.L1d31", B.L1d31, some "sbr_reset.L1d48"⟩ := by
  info_off
  measure_hb "L1d31"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hC, ⟨hrsp, hrbp⟩, h12, h15, st, fr, hM, hsp, hfm, hF, hm⟩ := T.L1d31.mp hs
    clear hs
    have ld1 := c8_load (focus (Mm_avctx ..) hm)
    have hav : st.x.avctx = a.x.avctx := (reset_keeps hM).2.2
    simp only [arg0] at ld1
    rw [hav] at ld1
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L1d31]
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    · simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h15, AddrIndex.offset64_none,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, ld1, Option.isSome_some]
    · rename_i _ hl _
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h15, AddrIndex.offset64_none,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at hl
      rw [ld1] at hl
      obtain rfl := Option.some.inj hl
      refine ⟨T.L1d48.mpr ⟨⟨⟨hC, ⟨?_, ?_⟩, ?_, ?_, st, fr, hM, hsp, hfm, hF, hm⟩, ?_⟩, ?_⟩, by var_step⟩
      all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15,
        BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]
      rfl

end Kraken.Examples.Sbr.Reset
