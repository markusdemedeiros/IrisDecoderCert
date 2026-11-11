import Kraken.InfoOff
import Kraken.X64.Examples.Sbr.Parse.ResetDer
import Kraken.X64.Examples.Sbr.Parse.ResetA2Lib
import Kraken.X64.Examples.Sbr.Parse.ResetA1Float
import Kraken.X64.Examples.Sbr.Parse.ResetA2Blk

/-!
# `sbr_reset`: `n_q` (`log2f`) and its failure (shard B)

`L2b30` .. `L2ba4`: `bs_noise_bands`, `k[2] / kx[1]` as floats, `log2f`, the conversion; the
value `c` stored as `n_q` stays abstract (any `log2f` result).

`n_q = FFMAX(1, lrintf(bs_noise_bands * log2f(k[2] / kx[1])))` is stored, then `n_q > 5` logs,
stores `n_q = 1` and turns off (`Derived.badNq`).
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
theorem nq_nq (x : Args) (q r : Nat) : { { x with nq := q } with nq := r } = { x with nq := r } := rfl

omit [CodeEnv] in
/-- `n_q > 5` is a failure `Reset` allows (`n_q = 1` stored before the turnoff). -/
theorem reset_badNq {a : RArgs} {k0 : Int} {nm : Nat} {f : Nat → Nat} (hst : u8 a.sp 0 < 16)
    (hMa : Master a.x.sampleRate.toInt (u8 a.sp 0) (u8 a.sp 2) (some k0) (some (nm, f)))
    (h1 : f nm ≤ 64) (h2 : f (xoOf a) ≤ 32) {q : Nat} (hq : 5 < q) :
    Reset (spOf a) (lbN a) a.x { dD2 a k0 nm f with nq := 1 }.turnoff := by
  obtain ⟨hxo, -, -, hmono⟩ := master_bounds hMa
  have hfx : f (xoOf a) ≤ f nm :=
    Nat.le_trans (Nat.le_add_right _ _) (hmono (xoOf a) nm (Nat.le_of_lt hxo) (Nat.le_refl _))
  have e1 : (derived1 (x0D a k0) nm (xoOf a) f).kx1 = f (xoOf a) := rfl
  have e2 : (derived1 (x0D a k0) nm (xoOf a) f).m1 = f nm - f (xoOf a) := rfl
  exact Reset.badDerived hst hMa (Derived.badNq q (by rw [e1, e2]; omega) (by rw [e1]; omega) hq)

set_option maxRecDepth 100000 in
/-- `av_log` (`n_q > 5`). -/
theorem blk_L2b9d (k : Nat) (e : REnv) (hAv : AvLogSpec e.Ext k) (a : RArgs) (ra : Int64)
    (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2b9d" ⟨"sbr_reset.L2b9d", B.L2b9d, some "sbr_reset.L2ba4"⟩ := by
  info_off
  measure_hb "L2b9d"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨⟨hC, ⟨hrsp, hrbp⟩, st, fr, nm, k0, hMa, hsp, hfm, hF, h40, hP, hm⟩, h12, h15, hdi⟩ :=
      T.L2b9d.mp hs
    clear hs
    have hd := reserve_le (focus (Mm_reserve ..) hm)
    rw [Mm_callF _ _ _ _ _ _ _ hd] at hm
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rsp - 8#64) 8).isSome = true := by
      rw [hrsp]
      exact Block.loadInt_isSome hm (by simp)
    have hpush := fun v => Block.storeInt_val hm (Split.here _ _) v
    have e8 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 0x578#64 - 8#64 := by
      rw [hrsp]
    simp only [B.L2b9d]
    vcgen [MachineWP.call_proc_spec_at (CallF k e a ra t₀ st fr) "av_log" hAv]
    all_goals try call_simp
    all_goals try subst_vars
    refine ⟨fun ra' => ⟨⟨?_, trivial⟩, fun s' hpost => ?_⟩, hld⟩
    · rw [e8]; exact hpush _
    · rw [e8] at hpost
      obtain ⟨hsp', hbp', ⟨-, h12', -, -, h15'⟩, hm'⟩ := hpost
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨T.L2ba4.mpr ⟨⟨hC, ⟨?_, ?_⟩, st, fr, nm, k0, hMa, hsp, hfm, hF, h40, hP, ?_⟩, ?_, ?_⟩,
        by var_step⟩
      · rw [hsp']; bv_omega
      · rw [hbp', hrbp]
      · show Mm k e a ra t₀ st fr s'.dmem
        rw [Mm_callF _ _ _ _ _ _ _ hd]; exact hm'
      · rw [h12', h12]
      · rw [h15', h15]

set_option maxRecDepth 100000 in
/-- `n_q = 1`, then `sbr_turnoff`. -/
theorem blk_L2ba4 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2ba4" ⟨"sbr_reset.L2ba4", B.L2ba4, some "sbr_reset.L2bb5"⟩ := by
  info_off
  measure_hb "L2ba4"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨⟨hC, ⟨hrsp, hrbp⟩, st, fr, nm, k0, hMa, hsp, hfm, hF, h40,
      ⟨hk2, hf1, hf2, h30, h38, q, hq, hx⟩, hm⟩, h12, h15⟩ := T.L2ba4.mp hs
    clear hs
    have hR := reset_badNq hC.2.1 hMa hf1 hf2 hq
    have ld1 := c4_isSome (focus (Mm_nq ..) hm)
    have s1 := Mm_upd_nq .. ▸ c4_store (focus (Mm_nq ..) hm) (BitVec.setWidth 32 (1#64)).toInt 1 rfl
    have hx' : ({ st with x := { st.x with nq := 1 } } : St).x.turnoff
        = { dD2 a k0 nm (fOf st) with nq := 1 }.turnoff := by
      show ({ st.x with nq := 1 } : Args).turnoff = _
      rw [hx]
    rw [← hx'] at hR
    clear hm hx hx'
    simp only [B.L2ba4]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    vcgen
    all_goals try subst_vars
    all_goals simp only [h12, AddrIndex.offset64_none, z, Int64.toBitVec_ofNat_norm]
    · with_reducible exact ld1
    · exact Or.inl (Table.ofLabels_at ⟨S.L1d31, T.L1d31.mpr ⟨hC, ⟨hrsp, hrbp⟩, h12, h15,
        { st with x := { st.x with nq := 1 } }, fr, hR, hsp, hfm, hF, s1⟩, by edge_step⟩)

omit [CodeEnv] in
theorem nq_sx (n : Nat) (h : n ≤ 32) : BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.signExtend 32
    (BitVec.setWidth 16 (BitVec.ofNat 64 n)))) = BitVec.ofNat 32 n := by
  have hm : (BitVec.setWidth 16 (BitVec.ofNat 64 n)).msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt]; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

omit [CodeEnv] in
theorem nq_zx8 (n : Nat) (h : n < 256) : BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32
    (BitVec.ofInt 8 (n : Int)))) = BitVec.ofNat 32 n := by
  rw [BitVec.ofInt_natCast]; apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

omit [CodeEnv] in
theorem nq_k2 (k : BitVec 32) (h : k.toNat ≤ 64) : BitVec.setWidth 64 k = BitVec.ofNat 64 k.toNat := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

set_option maxRecDepth 100000 in
theorem blk_L2b30 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2b30" ⟨"sbr_reset.L2b30", B.L2b30, some "sbr_reset.L2b45"⟩ := by
  info_off
  measure_hb "L2b30"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hC, ⟨hrsp, hrbp⟩, st, fr, nm, k0, hMa, hsp, hfm, hF, h40,
      ⟨hk2, hf1, hf2, h30, h38, hx, h14, h15, h10, hcx⟩, hm⟩ := T.L2b30.mp hs
    clear hs
    have neg : ∀ (r : BitVec 64) (d : Nat), d < 2 ^ 63 →
        r + (BitVec.ofInt 64 (-(d : Int))) = r - BitVec.ofNat 64 d := by
      intro r d hd; rw [BitVec.ofInt_neg, BitVec.ofInt_natCast]; bv_omega
    have a80 : t₀.regs.get64 .rsp - 8#64 + (-128 : Int64).toBitVec
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x80 := by
      have : (-128 : Int64).toBitVec = 0xffffffffffffff80#64 := by decide
      rw [this]; bv_omega
    have a50 : t₀.regs.get64 .rsp - 8#64 + (-80 : Int64).toBitVec
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x50 := by
      have : (-80 : Int64).toBitVec = 0xffffffffffffffb0#64 := by decide
      rw [this]; bv_omega
    have a30 : t₀.regs.get64 .rsp - 8#64 + (-48 : Int64).toBitVec
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x30 := by
      have : (-48 : Int64).toBitVec = 0xffffffffffffffd0#64 := by decide
      rw [this]; bv_omega
    have hF1 : ∀ v : Int, FrOk (wr fr (rb 0x80) (Int.toBytes 4 v)) :=
      fun v => fr_wr_len hF (by simp only [rb]; omega) v
    have hF2 : ∀ v w : Int, FrOk (wr (wr fr (rb 0x80) (Int.toBytes 4 v)) (rb 0x50) (Int.toBytes 4 w)) :=
      fun v w => fr_wr_len (hF1 v) (by simp only [rb]; omega) w
    have ld80 : (s₀.dmem.loadInt (t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x80) 4).isSome = true := by
      rw [fr_load hm hF (by omega) (by omega)]; rfl
    have hs1 := fun v => fr_store hm hF (d := 0x80) (n := 4) (by omega) (by omega) v
    have ld50 : ∀ v, ((s₀.dmem.storeInt (t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x80) 4 v).loadInt
        (t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x50) 4).isSome = true := by
      intro v; rw [fr_load (hs1 v) (hF1 v) (by omega) (by omega)]; rfl
    have hs2 := fun v w => fr_store (hs1 v) (hF1 v) (d := 0x50) (n := 4) (by omega) (by omega) w
    have ld30 : ∀ v w, (((s₀.dmem.storeInt (t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x80) 4 v).storeInt
        (t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x50) 4 w).loadInt
        (t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x30) 8) = some (Int.ofBytes (slice fr (rb 0x30) 8)) := by
      intro v w
      rw [fr_load (hs2 v w) (hF2 v w) (by omega) (by omega),
        slice_wr_other (hF1 v) (by simp only [rb]; omega) w (by simp only [rb]; omega),
        slice_wr_other hF (by simp only [rb]; omega) v (by simp only [rb]; omega)]
    have ld21v : ∀ v w, (((s₀.dmem.storeInt (t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x80) 4 v).storeInt
        (t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x50) 4 w).loadInt (arg1 t₀ + 33#64) 1)
          = some (u8 a.sp 5 : Int) := by
      intro v w
      rw [show arg1 t₀ + 33#64 = arg1 t₀ + 0x1c#64 + BitVec.ofNat 64 5 by bv_omega, ← hsp]
      exact a2_sp_load (hs2 v w) (by rw [hsp]; exact hC.1) (by omega)
    have h30' : BitVec.ofInt 64 (Int.ofBytes (slice fr (rb 0x30) 8)) = arg1 t₀ := h30
    have hl : st.sp.length = 6 := by rw [hsp]; exact hC.1
    have ld21 : ∀ v w, (((s₀.dmem.storeInt (t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x80) 4 v).storeInt
        (t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x50) 4 w).loadInt (arg1 t₀ + 33#64) 1).isSome = true := by
      intro v w
      rw [region_load (o := 5) (n := 1) (focus (Mm_sp ..) (hs2 v w)) (by bv_omega) (by omega) (by omega)]
      rfl
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    simp only [B.L2b30]
    vcgen
    all_goals try subst_vars
    all_goals simp only [hrbp, z, a80, a50, a30, AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm,
      Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    · exact ld80
    · exact ld50 _
    · rw [ld30]; rfl
    · rename_i v hv
      simp only [hrbp, z, a80, a50, a30, AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm,
        Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, ld30, Option.some.injEq] at hv
      subst hv
      rw [h30']
      exact ld21 _ _
    · rename_i v1 hv1 v2 hv2
      simp only [hrbp, z, a80, a50, a30, AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm,
        Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, ld30, Option.some.injEq] at hv1
      subst hv1
      have fs : ∀ (v w : Int) (d' : Nat), 0x30 ≤ d' → d' + 4 ≤ 0x50 →
          frSlot64 (wr (wr fr (rb 0x80) (Int.toBytes 4 v)) (rb 0x50) (Int.toBytes 4 w)) d'
            = frSlot64 fr d' := by
        intro v w d' h1 h2
        rw [frSlot64_wr_other (hF1 v) (d := 0x50) (n := 4) (by omega) (by omega) w h1 (by omega)
          (by omega), frSlot64_wr_other hF (d := 0x80) (n := 4) (by omega) (by omega) v h1 (by omega)
          (by omega)]
      refine ⟨T.L2b45.mpr ⟨⟨hC, ⟨?_, ?_⟩, st, _, nm, k0, hMa, hsp, hfm, hF2 _ _,
        (fs _ _ 0x40 (by omega) (by omega)).trans h40,
        ⟨hk2, hf1, hf2, (fs _ _ 0x30 (by omega) (by omega)).trans h30,
          (fs _ _ 0x38 (by omega) (by omega)).trans h38, hx, ?_, ?_, ?_, ?_, ?_⟩, hs2 _ _⟩, ?_⟩, ?_⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrsp, hrbp, h14, h15, h30']
      · rw [frSlot32_wr_other (hF1 _) (d := 0x50) (n := 4) (by omega) (by omega) _ (d' := 0x80)
          (by omega) (by omega) (by omega), frSlot32_wr_same hF (by omega) (by omega), BitVec.ofInt_toInt,
          h10, a2_setWidth32_ofNat64]
      · rw [frSlot32_wr_same (hF1 _) (by omega) (by omega), BitVec.ofInt_toInt, hcx, a2_setWidth32_ofNat64]
      · simp only [hrbp, z, a80, a50, a30, AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm,
          Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, h30', ld21v, Option.some.injEq] at hv2
        subst hv2
        simp only [lo32, RegZmms.get_set_xmm_same, a2_lo_app]
        rw [nq_zx8 _ (UInt8.toNat_lt _)]
      var_step

set_option maxRecDepth 100000 in
/-- `k[2]` and `kx[1]` as floats, `k[2] / kx[1]`; the noise-band count saved at `rbp - 0x48`. -/
theorem blk_L2b45 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2b45" ⟨"sbr_reset.L2b45", B.L2b45, some "sbr_reset.L2b60"⟩ := by
  info_off
  measure_hb "L2b45"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨⟨hC, ⟨hrsp, hrbp⟩, st, fr, nm, k0, hMa, hsp, hfm, hF, h40,
      ⟨hk2, hf1, hf2, h30, h38, hx, h14, h15, h80, h50, hlo⟩, hm⟩, h12⟩ := T.L2b45.mp hs
    clear hs
    have a48 : t₀.regs.get64 .rsp - 8#64 + (-72 : Int64).toBitVec
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x48 := by
      have : (-72 : Int64).toBitVec = 0xffffffffffffffb8#64 := by decide
      rw [this]; bv_omega
    have hF1 : ∀ v : Int, FrOk (wr fr (rb 0x48) (Int.toBytes 4 v)) :=
      fun v => fr_wr_len hF (by simp only [rb]; omega) v
    have ld48 : (s₀.dmem.loadInt (t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x48) 4).isSome = true := by
      rw [fr_load hm hF (by omega) (by omega)]; rfl
    have hs1 := fun v => fr_store hm hF (d := 0x48) (n := 4) (by omega) (by omega) v
    have ldk2 : ∀ v, ((s₀.dmem.storeInt (t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x48) 4 v).loadInt
        (arg1 t₀ + 72#64) 4).isSome = true :=
      fun v => cell4_isSome (focus (Mm_k2 ..) (hs1 v))
    have ldk2v : ∀ v, ((s₀.dmem.storeInt (t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x48) 4 v).loadInt
        (t₀.regs.get64 .rsi + 72#64) 4) = some (Int.ofBytes (Int.toBytes 4 st.k2.toInt)) :=
      fun v => cell4_load (focus (Mm_k2 ..) (hs1 v))
    have fs : ∀ (v : Int) (d' : Nat), 0x30 ≤ d' → d' + 4 ≤ 0x48 →
        frSlot64 (wr fr (rb 0x48) (Int.toBytes 4 v)) d' = frSlot64 fr d' := by
      intro v d' h1 h2
      rw [frSlot64_wr_other hF (d := 0x48) (n := 4) (by omega) (by omega) v h1 (by omega) (by omega)]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    simp only [B.L2b45]
    vcgen
    all_goals try subst_vars
    all_goals simp only [hrbp, h12, z, a48, AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm,
      Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    · exact ld48
    · exact ldk2 _
    · rename_i v1 hv1
      refine ⟨T.L2b60.mpr ⟨⟨hC, ⟨?_, ?_⟩, st, _, nm, k0, hMa, hsp, hfm, hF1 _,
        (fs _ 0x40 (by omega) (by omega)).trans h40,
        ⟨hk2, hf1, hf2, (fs _ 0x30 (by omega) (by omega)).trans h30,
          (fs _ 0x38 (by omega) (by omega)).trans h38, hx, ?_, ?_, ?_, ?_, ?_, ?_⟩, hs1 _⟩, ?_⟩, ?_⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrsp, hrbp, h14, h15, h12]
      · rw [frSlot32_wr_other hF (d := 0x48) (n := 4) (by omega) (by omega) _ (d' := 0x80)
          (by omega) (by omega) (by omega)]; exact h80
      · rw [frSlot32_wr_other hF (d := 0x48) (n := 4) (by omega) (by omega) _ (d' := 0x50)
          (by omega) (by omega) (by omega)]; exact h50
      · rw [frSlot32_wr_same hF (by omega) (by omega), BitVec.ofInt_toInt, hlo]
      · simp only [hrbp, h12, z, a48, AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm,
          Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, ldk2v, Option.some.injEq] at hv1
        subst hv1
        simp only [lo32, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne, ne_eq, reduceCtorEq,
          not_false_eq_true, a2_lo_app, BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt_toInt]
        have hk64 : st.k2.toNat ≤ 64 := by unfold NqIn at hk2; exact hk2.1
        rw [nq_k2 _ hk64, nq_sx, a2_sitof32_ofNat64 (n := st.k2.toNat) (by omega)]
        · rw [a2_ex0_app]
        · first | exact hf2 | (simp only [fOf, xoOf, u8] at hf2 ⊢; omega)
      var_step

set_option maxRecDepth 100000 in
/-- `log2f(k[2] / kx[1])`. -/
theorem blk_L2b60 (k : Nat) (e : REnv) (hc : ResetCallees k e) (a : RArgs) (ra : Int64)
    (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2b60" ⟨"sbr_reset.L2b60", B.L2b60, some "sbr_reset.L2b65"⟩ := by
  info_off
  measure_hb "L2b60"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨⟨hC, ⟨hrsp, hrbp⟩, st, fr, nm, k0, hMa, hsp, hfm, hF, h40, hP, hm⟩, h12⟩ := T.L2b60.mp hs
    clear hs
    obtain ⟨hk2, hf1, hf2, h30, h38, hx, h14, h15, h80, h50, h48, hlo⟩ := hP
    have hd := reserve_le (focus (Mm_reserve ..) hm)
    rw [Mm_callF _ _ _ _ _ _ _ hd] at hm
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rsp - 8#64) 8).isSome = true := by
      rw [hrsp]
      exact Block.loadInt_isSome hm (by simp)
    have hpush := fun v => Block.storeInt_val hm (Split.here _ _) v
    have e8 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 0x578#64 - 8#64 := by
      rw [hrsp]
    simp only [B.L2b60]
    vcgen [MachineWP.call_proc_spec_at (CallF k e a ra t₀ st fr) "log2f" hc.log2f]
    all_goals try call_simp
    all_goals try subst_vars
    refine ⟨fun ra' => ⟨⟨?_, trivial⟩, fun s' hpost => ?_⟩, hld⟩
    · rw [e8]; exact hpush _
    · rw [e8] at hpost
      obtain ⟨⟨hsp', hbp', ⟨-, h12', -, h14', h15'⟩, hm'⟩, hlg⟩ := hpost
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨T.L2b65.mpr ⟨⟨hC, ⟨?_, ?_⟩, st, fr, nm, k0, hMa, hsp, hfm, hF, h40,
        ⟨hk2, hf1, hf2, h30, h38, hx, ?_, ?_, h80, h50, h48, ?_⟩, ?_⟩, ?_⟩, by var_step⟩
      · rw [hsp']; bv_omega
      · rw [hbp', hrbp]
      · rw [h14', h14]
      · rw [h15', h15]
      · exact hlg.trans (congrArg e.lg hlo)
      · show Mm k e a ra t₀ st fr s'.dmem
        rw [Mm_callF _ _ _ _ _ _ _ hd]; exact hm'
      · rw [h12', h12]

set_option maxRecDepth 100000 in
/-- The exit of `L2b65` to `L2bb5` (`n_q < 6`), the value `c` abstract. -/
theorem nq_to_L2bb5 {k : Nat} {e : REnv} {a : RArgs} {ra : Int64} {t₀ : MachineData} {s : MachineData}
    {st : St} {fr : List UInt8} {nm : Nat} {k0 : Int} (hC : ResetCI a t₀)
    (hMa : Master a.x.sampleRate.toInt (u8 a.sp 0) (u8 a.sp 2) (some k0) (some (nm, fOf st)))
    (hsp : st.sp = a.sp) (hfm : st.fm.length = 98) (hF : FrOk fr) (h40 : frSlot64 fr 0x40 = arg0 t₀)
    (hk2 : NqIn e st) (hf1 : (fOf st) nm ≤ 64) (hf2 : (fOf st) (xoOf a) ≤ 32) (h30 : frSlot64 fr 0x30 = arg1 t₀)
    (h38 : frSlot64 fr 0x38 = BitVec.ofNat 64 nm) (hx : st.x = dD2 a k0 nm (fOf st))
    (h80 : frSlot32 fr 0x80 = BitVec.ofNat 32 ((fOf st) (xoOf a)))
    (h50 : frSlot32 fr 0x50 = BitVec.ofNat 32 ((fOf st) nm))
    (hrsp : s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x578#64)
    (hrbp : s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64)
    (h14 : s.regs.get64 .r14 = BitVec.ofNat 64 ((fOf st) (xoOf a)))
    (h15 : s.regs.get64 .r15 = BitVec.ofNat 64 ((nm - (xoOf a) + 1) / 2))
    (h12 : s.regs.get64 .r12 = arg1 t₀) (c : BitVec 32) (hc1 : 1 ≤ c.toNat) (hc : c.toNat < (6#32).toNat)
    (hrcx : BitVec.setWidth 32 (s.regs.get64 .rcx) = c)
    (hm : s.dmem =⋆ Mm k e a ra t₀ { st with x := { st.x with nq := c.toNat } } fr) :
    table k e a ra t₀ "sbr_reset.L2bb5" s := by
  have hx' : ({ st with x := { st.x with nq := c.toNat } } : St).x
      = { dD2 a k0 nm (fOf st) with nq := c.toNat } := by
    show ({ st.x with nq := c.toNat } : Args) = _
    rw [hx]
  have hrcx' : BitVec.setWidth 32 (s.regs.get64 .rcx) = BitVec.ofNat 32 c.toNat := by
    rw [hrcx, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  exact T.L2bb5.mpr ⟨⟨hC, ⟨hrsp, hrbp⟩, { st with x := { st.x with nq := c.toNat } }, fr, nm, k0, hMa, hsp, hfm, hF, h40,
    ⟨hk2, hf1, hf2, h30, h38, h80, h50, c.toNat, hc1, by simp only [BitVec.toNat_ofNat] at hc; omega,
      hx', hrcx', h14, h15⟩, hm⟩, h12⟩

set_option maxRecDepth 100000 in
/-- The exit of `L2b65` to the log `L2b9d` (`n_q > 5`). -/
theorem nq_to_L2b9d {k : Nat} {e : REnv} {a : RArgs} {ra : Int64} {t₀ : MachineData} {s : MachineData}
    {st : St} {fr : List UInt8} {nm : Nat} {k0 : Int} (hC : ResetCI a t₀)
    (hMa : Master a.x.sampleRate.toInt (u8 a.sp 0) (u8 a.sp 2) (some k0) (some (nm, fOf st)))
    (hsp : st.sp = a.sp) (hfm : st.fm.length = 98) (hF : FrOk fr) (h40 : frSlot64 fr 0x40 = arg0 t₀)
    (hk2 : NqIn e st) (hf1 : (fOf st) nm ≤ 64) (hf2 : (fOf st) (xoOf a) ≤ 32) (h30 : frSlot64 fr 0x30 = arg1 t₀)
    (h38 : frSlot64 fr 0x38 = BitVec.ofNat 64 nm) (hx : st.x = dD2 a k0 nm (fOf st))
    (hrsp : s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x578#64)
    (hrbp : s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64)
    (h12 : s.regs.get64 .r12 = arg1 t₀) (h15 : s.regs.get64 .r15 = arg0 t₀)
    (hdi : s.regs.get64 .rdi = a.x.avctx) (c : BitVec 32) (hc : ¬ c.toNat < (6#32).toNat)
    (hm : s.dmem =⋆ Mm k e a ra t₀ { st with x := { st.x with nq := c.toNat } } fr) :
    table k e a ra t₀ "sbr_reset.L2b9d" s := by
  have hx' : ({ st with x := { st.x with nq := c.toNat } } : St).x
      = { dD2 a k0 nm (fOf st) with nq := c.toNat } := by
    show ({ st.x with nq := c.toNat } : Args) = _
    rw [hx]
  have hq : 5 < c.toNat := by simp only [BitVec.toNat_ofNat] at hc; omega
  exact T.L2b9d.mpr ⟨⟨hC, ⟨hrsp, hrbp⟩, { st with x := { st.x with nq := c.toNat } }, fr, nm, k0, hMa, hsp, hfm, hF, h40,
    ⟨hk2, hf1, hf2, h30, h38, c.toNat, hq, hx'⟩, hm⟩, h12, h15, hdi⟩

omit [CodeEnv] in
theorem toBytes4_toInt (v : BitVec 32) : Int.toBytes 4 v.toInt = Int.toBytes 4 (v.toNat : Int) := by
  rw [← Int.toBytes_emod 4 v.toInt, ← Int.toBytes_emod 4 (v.toNat : Int)]
  congr 1
  simp only [Int.take]
  rw [BitVec.toInt_eq_toNat_bmod]
  have := Int.bmod_emod (x := (v.toNat : Int)) (m := 2 ^ 32)
  simpa using this

omit [CodeEnv] in
theorem nq_ge64 (a b : BitVec 64) (cf af : Bool) :
    CondCode.ge.interp (StatusFlags.from_result (a - b)
      { cf := cf, af := af, of := (a - b).signed != a.signed - b.signed })
      = decide (b.toInt ≤ a.toInt) := by
  rw [CondCode.interp_ge_cmp, BitVec.slt_eq_decide]
  by_cases h : a.toInt < b.toInt <;> simp [h] <;> omega

omit [CodeEnv] in
/-- `FFMAX(1, v)` (a signed `cmovge` against 2) is at least 1 when `v < 2^32`. -/
theorem nq_c_pos (v : BitVec 64) (hv : v.toInt < 2 ^ 32) (cf af : Bool) :
    1 ≤ (BitVec.setWidth 32 (if CondCode.ge.interp (StatusFlags.from_result (v - 2#64)
      { cf := cf, af := af, of := (v - 2#64).signed != v.signed - (2#64).signed }) = true
      then v else 1#64)).toNat := by
  rw [nq_ge64]
  split
  · rename_i h
    simp only [decide_eq_true_eq] at h
    have h2 : (2#64).toInt = 2 := by decide
    rw [h2] at h
    have := v.isLt
    rw [BitVec.toInt_eq_toNat_bmod, Int.bmod_def] at h hv
    simp only [BitVec.toNat_setWidth]
    split at h <;> split at hv <;> omega
  · decide

set_option maxRecDepth 100000 in
/-- `n_q = FFMAX(1, lrintf(…))` stored; `n_q > 5` → the log. -/
theorem blk_L2b65 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2b65" ⟨"sbr_reset.L2b65", B.L2b65, some "sbr_reset.L2b9d"⟩ := by
  info_off
  measure_hb "L2b65"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨⟨hC, ⟨hrsp, hrbp⟩, st, fr, nm, k0, hMa, hsp, hfm, hF, h40,
      ⟨hk2, hf1, hf2, h30, h38, hx, h14, h15, h80, h50, h48, hlo⟩, hm⟩, h12⟩ := T.L2b65.mp hs
    have hk64 : st.k2.toNat ≤ 64 := by unfold NqIn at hk2; exact hk2.1
    have hq := (show NqOK e.lg by unfold NqIn at hk2; exact hk2.2) st.k2.toNat hk64 (fOf st (xoOf a)) hf2
      (u8 a.sp 5) (UInt8.toNat_lt _)
    have hq' : (BitVec.f32toi64 (BitVec.f32mul (lo32 s₀ .mm0) (frSlot32 fr 0x48))).toInt < 2 ^ 32 := by
      rw [hlo, h48]; exact hq
    have P10 := PLift.up (And.intro hk2 (And.intro h80 h50))
    have P11 := PLift.up hq'
    clear hq hq' hlo h48 h80 h50 hk2
    clear hs
    have a48 : t₀.regs.get64 .rsp - 8#64 + (-72 : Int64).toBitVec
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x48 := by
      have : (-72 : Int64).toBitVec = 0xffffffffffffffb8#64 := by decide
      rw [this]; bv_omega
    have a40 : t₀.regs.get64 .rsp - 8#64 + (-64 : Int64).toBitVec
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x40 := by
      have : (-64 : Int64).toBitVec = 0xffffffffffffffc0#64 := by decide
      rw [this]; bv_omega
    have ld48 : (s₀.dmem.loadInt (t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x48) 4).isSome = true := by
      rw [fr_load hm hF (by omega) (by omega)]; rfl
    have hs1 : ∀ c : BitVec 32, s₀.dmem.storeInt (arg1 t₀ + 0x4c1e8#64) 4 c.toInt
        =⋆ Mm k e a ra t₀ { st with x := { st.x with nq := c.toNat } } fr := fun c =>
      Mm_upd_nq .. ▸ c4_store (focus (Mm_nq ..) hm) c.toInt c.toNat (toBytes4_toInt c)
    have ldnq := c4_isSome (focus (Mm_nq ..) hm)
    have ld40 : ∀ c : BitVec 32, ((s₀.dmem.storeInt (arg1 t₀ + 0x4c1e8#64) 4 c.toInt).loadInt
        (t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x40) 8) = some (Int.ofBytes (slice fr (rb 0x40) 8)) :=
      fun c => fr_load (hs1 c) hF (by omega) (by omega)
    have h40' : BitVec.ofInt 64 (Int.ofBytes (slice fr (rb 0x40) 8)) = arg0 t₀ := h40
    have hav : ∀ c : BitVec 32, ((s₀.dmem.storeInt (arg1 t₀ + 0x4c1e8#64) 4 c.toInt).loadInt
        (arg0 t₀ + 8#64) 8) = some (Int.ofBytes (Int.toBytes 8 a.x.avctx.toInt)) := by
      intro c
      have h := c8_load (focus (Mm_avctx ..) (hs1 c))
      have e : ({ st with x := { st.x with nq := c.toNat } } : St).x.avctx = a.x.avctx := by
        show st.x.avctx = _; rw [hx]; rfl
      rw [e] at h; exact h
    have P1 := PLift.up hs1
    have P2 := PLift.up ld40
    have P3 := PLift.up hav
    have P4 := PLift.up (And.intro hx (And.intro h30 (And.intro h38 (And.intro hf1 (And.intro hf2 h40)))))
    have P6 := PLift.up (And.intro h14 (And.intro h15 (And.intro hrsp hrbp)))
    have P7 := PLift.up (And.intro hC (And.intro hMa (And.intro hsp (And.intro hfm hF))))
    have P8 := PLift.up h12
    have P9 := PLift.up (And.intro a48 (And.intro a40 (And.intro ld48 ldnq)))
    have P12 := PLift.up (fr_load hm hF (d := 0x48) (n := 4) (by omega) (by omega))
    have P5 := PLift.up h40'
    clear a48 a40 ld48 ldnq hs1 ld40 hav hm hx h30 h38 hf1 hf2 h40 hC hMa hsp hfm hF
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    simp only [B.L2b65]
    vcgen [a1_vcvtss2si_spec]
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrbp, h12,
      AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat] at *
    all_goals try disp_simp
    all_goals try simp only [BitVec.add_zero] at *
    all_goals try simp only [P9.down.1, P9.down.2.1]
    all_goals try simp only [P9.down.1, P9.down.2.1] at *
    · exact P9.down.2.2.1
    · exact P9.down.2.2.2
    · simp only [P12.down, Option.some.injEq] at *
      subst_vars
      obtain ⟨hx, h30, h38, hf1, hf2, h40⟩ := P4.down
      obtain ⟨h14, h15, hrsp, hrbp⟩ := P6.down
      obtain ⟨hC, hMa, hsp, hfm, hF⟩ := P7.down
      obtain ⟨hk2, h80, h50⟩ := P10.down
      exact Or.inl (Table.ofLabels_at ⟨S.L2bb5, nq_to_L2bb5 hC hMa hsp hfm hF h40 hk2 hf1 hf2 h30 h38 hx h80 h50
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; try exact hrsp) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; try exact hrbp) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; try exact h14) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; try exact h15)
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; try exact P8.down) _
        (nq_c_pos _ (by
          simp only [RegZmms.get_set_xmm_same, a2_lo_app, a2_ex0_eq_sw]
          exact P11.down) _ _) (by assumption)
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) (P1.down _), by edge_step⟩)
    · rw [P2.down]; rfl
    · simp only [P2.down, Option.some.injEq] at *
      subst_vars
      rw [P5.down, P3.down]; rfl
    · simp only [P2.down, Option.some.injEq] at *
      subst_vars
      simp only [P5.down, P3.down, Option.some.injEq] at *
      subst_vars
      obtain ⟨hx, h30, h38, hf1, hf2, h40⟩ := P4.down
      obtain ⟨h14, h15, hrsp, hrbp⟩ := P6.down
      obtain ⟨hC, hMa, hsp, hfm, hF⟩ := P7.down
      obtain ⟨hk2, -, -⟩ := P10.down
      refine ⟨nq_to_L2b9d hC hMa hsp hfm hF h40 hk2 hf1 hf2 h30 h38 hx
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; try exact hrsp) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; try exact hrbp) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; try exact P8.down) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; try exact P5.down)
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]) _ (by assumption) (P1.down _), ?_⟩
      var_step


end Kraken.Examples.Sbr.Reset
