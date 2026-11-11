import Kraken.InfoOff
import Kraken.X64.Examples.Sbr.Parse.ResetNzB
import Kraken.X64.Examples.Sbr.Parse.ResetA1Pro

/-!
# `sbr_reset`: `goal_sb` and the entry to the patch loop (`L2c89`)
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
theorem rsP_sw (x : BitVec 32) : BitVec.setWidth 32 (BitVec.setWidth 64 x) = x := by
  rw [BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_eq]

omit [CodeEnv] in
theorem rsP_rate {v : BitVec 32} (h : v.toInt ∈ rates) :
    v ∈ [16000#32, 22050#32, 24000#32, 32000#32, 44100#32, 48000#32, 64000#32, 88200#32,
      96000#32, 128000#32, 176400#32, 192000#32] := by
  have e := BitVec.ofInt_toInt (x := v)
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h <;> rw [← e, h] <;> decide

/-- The fixed facts of the patch loop, from `Master` and the `derived1` checks. -/
theorem rsP_fix {a : RArgs} {t₀ : MachineData} {k0 : Int} {nm q : Nat} {f : Nat → Nat}
    (hC : ResetCI a t₀)
    (hMa : Master a.x.sampleRate.toInt (u8 a.sp 0) (u8 a.sp 2) (some k0) (some (nm, f)))
    (hf1 : f nm ≤ 64) (hf2 : f (xoOf a) ≤ 32) (hq1 : 1 ≤ q) (hq6 : q < 6) :
    PFix a ⟨k0, nm, q⟩ f := by
  obtain ⟨hxo, hnm, -, hfle⟩ := master_bounds hMa
  have hxo' : xoOf a < nm := hxo
  have e : ∀ i, u16 ({ px0 a ⟨k0, nm, q⟩ f with npatch := 0 } : Args).ftLow i
      = u16 (derived2 (derived1 (x0D a k0) nm (xoOf a) f) (xoOf a) f).ftLow i := fun _ => rfl
  have hsc := hC.2.2.2.2.1
  simp only [Scal] at hsc
  have hlow : ∀ k, k ≤ (nm - xoOf a + 1) / 2 →
      u16 (derived2 (derived1 (x0D a k0) nm (xoOf a) f) (xoOf a) f).ftLow k
        = f (xoOf a + lowIx (nm - xoOf a) k) := by
    intro k hk; rw [derived2_low hk (by omega)]
    have := lowIx_le (n1 := nm - xoOf a) hk
    have := hfle (xoOf a + lowIx (nm - xoOf a) k) nm (by omega) (Nat.le_refl _)
    exact Nat.mod_eq_of_lt (by omega)
  refine ⟨hMa, ?_, ?_, hq1, (by show q ≤ 5; omega), ⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨fun i hi => ?_, fun i hi => ?_⟩, ?_, ?_, ?_⟩, ?_⟩
  · show f (xoOf a) + (f nm - f (xoOf a)) ≤ 64; omega
  · exact hf2
  · show (nm - xoOf a + 1) / 2 ≤ 24; omega
  · show 0 ≤ 6; omega
  · intro _; show 1 ≤ (nm - xoOf a + 1) / 2 + 0; omega
  · show (derived2 (derived1 (x0D a k0) nm (xoOf a) f) (xoOf a) f).ftLow.length = 50
    simp only [derived2, mk16_length]
  · exact hC.2.2.2.2.2.2.2.2.2.1
  · exact hC.2.2.2.2.2.2.2.2.2.2.1
  · show f (xoOf a) ≤ u16 _ i ∧ u16 _ i ≤ f (xoOf a) + (f nm - f (xoOf a))
    have hi' : i ≤ (nm - xoOf a + 1) / 2 := hi
    rw [e, hlow i hi']
    have := lowIx_le (n1 := nm - xoOf a) hi'
    have := hfle (xoOf a) (xoOf a + lowIx (nm - xoOf a) i) (by omega) (by omega)
    have := hfle (xoOf a + lowIx (nm - xoOf a) i) nm (by omega) (Nat.le_refl _)
    omega
  · have hi' : i + 1 ≤ (nm - xoOf a + 1) / 2 := hi
    show u16 _ i ≤ u16 _ (i + 1)
    rw [e, e, hlow i (by omega), hlow (i + 1) hi']
    have := lowIx_le (n1 := nm - xoOf a) hi'
    have := lowIx_mono (n1 := nm - xoOf a) (k := i)
    have := hfle (xoOf a + lowIx (nm - xoOf a) i) (xoOf a + lowIx (nm - xoOf a) (i + 1)) (by omega)
      (by omega)
    omega
  · show psum _ 0 ≤ _; simp [psum]
  · show f (xoOf a) + (f nm - f (xoOf a)) ≤ 64; omega
  · show a.x.nlim < 2 ^ 32; omega
  · exact hC.2.2.2.2.2.2.2.2.2.2.2.1

omit [CodeEnv] in
theorem rsP_q {S : BitVec 32} (hS : S ∈ [16000#32, 22050#32, 24000#32, 32000#32, 44100#32, 48000#32,
      64000#32, 88200#32, 96000#32, 128000#32, 176400#32, 192000#32]) :
    BitVec.ofInt 32
        ((((BitVec.setWidth 32 2048000#64 + S.sshiftRight 1).sshiftRight 31).toInt * 2 ^ 32 +
          ((BitVec.setWidth 32 2048000#64 + S.sshiftRight 1).toNat : Int)).tdiv S.toInt)
      = BitVec.ofNat 32 (goalSb S.toInt).toNat ∧ 11 ≤ goalSb S.toInt ∧ goalSb S.toInt ≤ 128 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

omit [CodeEnv] in
theorem rsP_k0 {sr : Int} {st xo : Nat} {k0 : Int} {nm : Nat} {f : Nat → Nat}
    (h : Master sr st xo (some k0) (some (nm, f))) : k0 = (f 0 : Int) := by
  cases h with
  | ok k2 _ _ hr h64 hk hq hxo hf0 hinc hfn => exact hf0.symm

omit [CodeEnv] in
theorem rsP_rm {sr : Int} {st xo : Nat} {k0 : Int} {nm : Nat} {f : Nat → Nat}
    (h : Master sr st xo (some k0) (some (nm, f))) : sr ∈ rates := by
  cases h with | ok _ _ _ hr => exact rateRow_mem hr

omit [CodeEnv] in
theorem rsP_k4 (n : Nat) (h : n < 2 ^ 31) :
    BitVec.setWidth 64 (BitVec.ofInt 32 (Int.ofBytes (Int.toBytes 4 (n : Int)))) = BitVec.ofNat 64 n := by
  have h1 : (n : Int) = (BitVec.ofNat 32 n).toInt := by
    rw [BitVec.toInt_eq_toNat_of_lt] <;> simp only [BitVec.toNat_ofNat] <;> omega
  rw [h1, a1_ofInt4]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

omit [CodeEnv] in
theorem rsP_w32 (n : Nat) (h : n < 2 ^ 32) :
    BitVec.setWidth 64 (BitVec.ofNat 32 n) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

set_option maxRecDepth 100000 in
/-- `num_patches = 0`, `goal_sb` computed; `goal_sb ≥ kx[1] + m[1]` goes to the loop with
`k = n_master`, otherwise to the search. -/
theorem blk_L2c89 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2c89" ⟨"sbr_reset.L2c89", B.L2c89, some "sbr_reset.L2cc2"⟩ := by
  info_off
  measure_hb "L2c89"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hC, ⟨hrsp, hrbp⟩, st, fr, nm, k0, hMa, hsp, hfm, hF, h40,
      ⟨hk2, hf1, hf2, h30, h38, q, j, hq1, hq6, hx, h11, h12, h50, h80, hjq⟩, hm⟩ := T.L2c89.mp hs
    clear hs
    subst hjq
    have ldsr := a1_sr_load hm
    have ldk0 := c4_load (focus (Mm_k0 ..) hm)
    have hMa' : Master a.x.sampleRate.toInt (u8 a.sp 0) (xoOf a) (some k0) (some (nm, fOf st)) := hMa
    obtain ⟨hxo, hnm, -, hfle⟩ := master_bounds hMa'
    have hf1' : fOf st nm ≤ 64 := hf1
    have hrm : a.x.sampleRate.toInt ∈ rates := rsP_rm hMa'
    have hk0 : k0.toNat = fOf st 0 := by rw [rsP_k0 hMa']; omega
    have hxn : fOf st (xoOf a) ≤ fOf st nm := by
      have := hfle (xoOf a) nm (by omega) (Nat.le_refl _); omega
    have hf0 : fOf st 0 ≤ 64 := by have := hfle 0 nm (by omega) (Nat.le_refl _); omega
    have hstk : st.x.k0 = k0.toNat := by rw [hx]; rfl
    have hpt : ptop a ⟨k0, nm, j⟩ (fOf st) = fOf st nm := by
      have := hfle (xoOf a) nm (by omega) (Nat.le_refl _)
      show fOf st (xoOf a) + (fOf st nm - fOf st (xoOf a)) = fOf st nm; omega
    have h50' : frSlot32 fr 0x50 = BitVec.ofNat 32 (fOf st nm) := h50
    have hfv : (frSlot32 fr 0x50).toNat = fOf st nm := by
      rw [h50', BitVec.toNat_ofNat]; omega
    have hpx : ({ st.x with npatch := 0 } : Args) = { px0 a ⟨k0, nm, j⟩ (fOf st) with npatch := 0 } := by
      rw [hx]; rfl
    have hrsi : BitVec.setWidth 64 (BitVec.ofInt 32 (Int.ofBytes (Int.toBytes 4 (st.x.k0 : Int))))
        = BitVec.ofNat 64 (pk0 ⟨k0, nm, j⟩) := by
      rw [hstk]; exact rsP_k4 _ (by omega)
    have hrdi : (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 nm))).toNat = nm := by
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
    have sl : ∀ d', 0x30 ≤ d' → d' ≤ 0x570 → d' + 8 ≤ 0x48 ∨ 0x48 + 8 ≤ d' →
        frSlot64 (wr fr (rb 0x48) (Int.toBytes 8 (t₀.regs.get64 .rsi + 0x4c1f0#64).toInt)) d'
          = frSlot64 fr d' :=
      fun d' h1 h2 h3 => frSlot64_wr_other hF (d := 0x48) (n := 8) (by omega) (by omega) _ h1 h2 h3
    have sl4 : ∀ d', 0x2c ≤ d' → d' ≤ 0x570 → d' + 8 ≤ 0x48 ∨ 0x48 + 4 ≤ d' →
        frSlot32 (wr fr (rb 0x48) (Int.toBytes 8 (t₀.regs.get64 .rsi + 0x4c1f0#64).toInt)) d'
          = frSlot32 fr d' :=
      fun d' h1 h2 h3 => frSlot32_wr_other hF (d := 0x48) (n := 8) (by omega) (by omega) _ h1 h2 h3
    have s48 : frSlot64 (wr fr (rb 0x48) (Int.toBytes 8 (t₀.regs.get64 .rsi + 0x4c1f0#64).toInt)) 0x48
        = t₀.regs.get64 .rsi + 0x4c1f0#64 := by
      rw [frSlot64_wr_same hF (d := 0x48) (by omega) (by omega), BitVec.ofInt_toInt]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    have a48 : t₀.regs.get64 .rsp - 8#64 + (-72 : Int64).toBitVec
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x48 := by
      have : (-72 : Int64).toBitVec = 0xffffffffffffffb8#64 := by decide
      rw [this]; bv_omega
    have a50 : t₀.regs.get64 .rsp - 8#64 + (-80 : Int64).toBitVec
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x50 := by
      have : (-80 : Int64).toBitVec = 0xffffffffffffffb0#64 := by decide
      rw [this]; bv_omega
    have hF1 : ∀ v : Int, FrOk (wr fr (rb 0x48) (Int.toBytes 8 v)) :=
      fun v => fr_wr_len hF (by simp only [rb]; omega) v
    have ld48 : (s₀.dmem.loadInt (t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x48) 8).isSome = true := by
      rw [fr_load hm hF (by omega) (by omega)]; rfl
    have hs1 := fun v => fr_store hm hF (d := 0x48) (n := 8) (by omega) (by omega) v
    have ldnp : ∀ v, ((s₀.dmem.storeInt (t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x48) 8 v).loadInt
        (t₀.regs.get64 .rsi + 0x4c330#64) 4).isSome = true :=
      fun v => c4_isSome (focus (Mm_npatch ..) (hs1 v))
    have hs2 : ∀ v w, Int.toBytes 4 w = Int.toBytes 4 ((0 : Nat) : Int) →
        ((s₀.dmem.storeInt (t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x48) 8 v).storeInt
          (t₀.regs.get64 .rsi + 0x4c330#64) 4 w)
          =⋆ Mm k e a ra t₀ { st with x := { st.x with npatch := 0 } } (wr fr (rb 0x48) (Int.toBytes 8 v)) :=
      fun v w hw => Mm_upd_npatch .. ▸ c4_store (focus (Mm_npatch ..) (hs1 v)) w 0 hw
    have ld50 : ∀ v w, Int.toBytes 4 w = Int.toBytes 4 ((0 : Nat) : Int) →
        (((s₀.dmem.storeInt (t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x48) 8 v).storeInt
          (t₀.regs.get64 .rsi + 0x4c330#64) 4 w).loadInt (t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x50) 4)
          = some (Int.ofBytes (slice fr (rb 0x50) 4)) := fun v w hw => by
      rw [fr_load (hs2 v w hw) (hF1 v) (by omega) (by omega),
        slice_wr_other hF (by simp only [rb]; omega) v (by simp only [rb]; omega)]
    simp only [B.L2c89]
    vcgen
    all_goals try subst_vars
    all_goals try simp only [hrbp, h12, z, AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm,
      Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    case vc1 => rw [BitVec.add_zero, ldsr]; rfl
    case vc2 => rw [ldk0]; rfl
    case vc3 =>
      rename_i v1 hv1 v2 hv2 _ _ _
      simp only [hrbp, h12, z, a1_addi0, BitVec.add_zero, AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm,
        Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, ldsr, ldk0, Option.some.injEq] at hv1 hv2
      subst hv1 hv2
      simp only [a1_ofInt4, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, ↓reduceIte, Reg64s.get64_set64,
        reduceCtorEq, rsP_sw, Nat.one_mod]
      have hsrx : st.x.sampleRate = a.x.sampleRate := by rw [hx]; rfl
      have hS := rsP_rate hrm
      rw [hsrx]
      refine ⟨?_, fun fl => ?_⟩
      · generalize a.x.sampleRate = S at hS ⊢
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hS
        rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      vcgen
      all_goals try subst_vars
      all_goals try simp only [hrbp, h12, z, a1_addi0, BitVec.add_zero, a48, a50, AddrIndex.offset64_none,
        Int64.toBitVec_ofNat_norm, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      case vc1 => exact ld48
      case vc2 => exact ldnp _
      case vc3 => rw [ld50 _ (BitVec.setWidth 32 0#64).toInt rfl]; rfl
      case vc4 =>
        rename_i v hl hc
        simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrbp, h12, z, a1_addi0, a48, a50,
          AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, cc_nc_sub, rsP_sw] at hc hl
        rw [ld50 _ (BitVec.setWidth 32 0#64).toInt rfl, Option.some.injEq] at hl
        subst hl
        obtain ⟨hQ, hg1, hg2⟩ := rsP_q hS
        rw [hQ] at hc
        have hfv' : (BitVec.ofInt 32 (Int.ofBytes (slice fr (rb 0x50) 4))).toNat = fOf st nm := hfv
        simp only [hfv', BitVec.toNat_ofNat, decide_eq_true_eq] at hc
        refine Or.inl (Table.ofLabels_at ⟨S.L30df, T.L30df.mpr ⟨hC, ⟨?_, ?_⟩,
          ({ st with x := { st.x with npatch := 0 } } : St),
          wr fr (rb 0x48) (Int.toBytes 8 (t₀.regs.get64 .rsi + 0x4c1f0#64).toInt), ⟨k0, nm, j⟩,
          rsP_fix hC hMa hf1 hf2 hq1 hq6, hsp, hfm, hF1 _, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩,
          hs2 _ (BitVec.setWidth 32 0#64).toInt rfl⟩, by edge_step⟩)
        all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        · exact hrsp
        · exact hrbp
        · exact (sl 0x40 (by omega) (by omega) (by omega)).trans h40
        · exact (sl 0x30 (by omega) (by omega) (by omega)).trans h30
        · exact (sl 0x38 (by omega) (by omega) (by omega)).trans h38
        · exact s48
        · exact (sl4 0x50 (by omega) (by omega) (by omega)).trans (h50'.trans (congrArg (BitVec.ofNat 32) hpt.symm))
        · exact (sl4 0x80 (by omega) (by omega) (by omega)).trans h80
        · show KInit (fOf st) nm (ptop a ⟨k0, nm, j⟩ (fOf st)) _ _
          refine (congrArg (fun T => KInit (fOf st) nm T (goalSb a.x.sampleRate.toInt) _) hpt).mpr ?_
          rw [h11, hrdi]; unfold KInit; split
          · rename_i h; exact absurd h (by show ¬ goalSb _ < ((fOf st nm : Nat) : Int); omega)
          · rfl
        · exact hpx
        · exact hrsi
        · exact h12
      case vc5 =>
        rename_i v hl hc
        simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrbp, h12, z, a1_addi0, a48, a50,
          AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, cc_nc_sub, rsP_sw] at hc hl
        rw [ld50 _ (BitVec.setWidth 32 0#64).toInt rfl, Option.some.injEq] at hl
        subst hl
        obtain ⟨hQ, hg1, hg2⟩ := rsP_q hS
        rw [hQ] at hc
        have hfv' : (BitVec.ofInt 32 (Int.ofBytes (slice fr (rb 0x50) 4))).toNat = fOf st nm := hfv
        simp only [hfv', BitVec.toNat_ofNat, decide_eq_false_iff_not] at hc
        refine ⟨T.L2cc2.mpr ?_, ?_⟩
        rotate_left
        · var_step
        refine ⟨hC, ⟨?_, ?_⟩,
          ({ st with x := { st.x with npatch := 0 } } : St),
          wr fr (rb 0x48) (Int.toBytes 8 (t₀.regs.get64 .rsi + 0x4c1f0#64).toInt), ⟨k0, nm, j⟩,
          rsP_fix hC hMa hf1 hf2 hq1 hq6, hsp, hfm, hF1 _, ?_, ?_, ?_, ?_, ?_, ?_,
          ⟨?_, fun i hi => absurd hi (Nat.not_lt_zero _), ?_, ?_, ?_, ?_⟩, hs2 _ (BitVec.setWidth 32 0#64).toInt rfl⟩
        all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        · exact hrsp
        · exact hrbp
        · exact (sl 0x40 (by omega) (by omega) (by omega)).trans h40
        · exact (sl 0x30 (by omega) (by omega) (by omega)).trans h30
        · exact (sl 0x38 (by omega) (by omega) (by omega)).trans h38
        · exact s48
        · exact (sl4 0x50 (by omega) (by omega) (by omega)).trans (h50'.trans (congrArg (BitVec.ofNat 32) hpt.symm))
        · exact (sl4 0x80 (by omega) (by omega) (by omega)).trans h80
        · show goalSb a.x.sampleRate.toInt < (ptop a ⟨k0, nm, j⟩ (fOf st) : Int)
          show _ < ((fOf st (xoOf a) + (fOf st nm - fOf st (xoOf a)) : Nat) : Int); omega
        · exact hpx
        · exact hrsi
        · exact h12
        · rw [hQ, rsP_w32 _ (by omega)]

end Kraken.Examples.Sbr.Reset
