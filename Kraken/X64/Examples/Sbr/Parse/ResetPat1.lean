import Kraken.X64.Examples.Sbr.Parse.ResetPatLib

/-!
# `sbr_reset`: the patch loop `sbr_hf_calc_npatches`, its exits (shard B, gB)
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Reset

variable [CodeEnv]

set_option maxRecDepth 100000 in
/-- `jmp L1d31` (the shared failure exit). -/
theorem blk_L31f0 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L31f0" ⟨"sbr_reset.L31f0", B.L31f0, some "sbr_reset.L31f5"⟩ := by
  info_off
  measure_hb "L31f0"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hC, ⟨hrsp, hrbp⟩, h12, h15, st, fr, hM, hsp, hfm, hF, hm⟩ := T.L31f0.mp hs
    clear hs
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L31f0]
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    left; apply Table.ofLabels_at
    refine ⟨by decide, T.L1d31.mpr ⟨hC, ⟨?_, ?_⟩, ?_, ?_, st, fr, hM, hsp, hfm, hF, hm⟩, ?_⟩
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15]
    edge_step

set_option maxRecDepth 100000 in
/-- `av_log` (the repeated-patch error). -/
theorem blk_L31eb (k : Nat) (e : REnv) (hAv : AvLogSpec e.Ext k) (a : RArgs) (ra : Int64)
    (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L31eb" ⟨"sbr_reset.L31eb", B.L31eb, some "sbr_reset.L31f0"⟩ := by
  info_off
  measure_hb "L31eb"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨⟨hC, ⟨hrsp, hrbp⟩, h12, h15, st, fr, hM, hsp, hfm, hF, hm⟩, hdi⟩ := T.L31eb.mp hs
    clear hs
    have hd := reserve_le (focus (Mm_reserve ..) hm)
    rw [Mm_callF _ _ _ _ _ _ _ hd] at hm
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rsp - 8#64) 8).isSome = true := by
      rw [hrsp]
      exact Block.loadInt_isSome hm (by simp)
    have hpush := fun v => Block.storeInt_val hm (Split.here _ _) v
    have e8 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 0x578#64 - 8#64 := by
      rw [hrsp]
    simp only [B.L31eb]
    vcgen [MachineWP.call_proc_spec_at (CallF k e a ra t₀ st fr) "av_log" hAv]
    all_goals try call_simp
    all_goals try subst_vars
    refine ⟨fun ra' => ⟨⟨?_, trivial⟩, fun s' hpost => ?_⟩, hld⟩
    · rw [e8]; exact hpush _
    · rw [e8] at hpost
      obtain ⟨hsp', hbp', ⟨-, h12', -, -, h15'⟩, hm'⟩ := hpost
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨T.L31f0.mpr ⟨hC, ⟨?_, ?_⟩, ?_, ?_, st, fr, hM, hsp, hfm, hF, ?_⟩, by var_step⟩
      · rw [hsp']; bv_omega
      · rw [hbp', hrbp]
      · rw [h12', h12]
      · rw [h15', h15]
      · show Mm k e a ra t₀ st fr s'.dmem
        rw [Mm_callF _ _ _ _ _ _ _ hd]; exact hm'

set_option maxRecDepth 100000 in
/-- `k == last_k && msb == last_msb`: `r15 = ac`, `rdi = ac->avctx`, the format. -/
theorem blk_L31d5 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L31d5" ⟨"sbr_reset.L31d5", B.L31d5, some "sbr_reset.L31eb"⟩ := by
  info_off
  measure_hb "L31d5"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hC, ⟨hrsp, hrbp⟩, h12, st, fr, c, hMa, hR, hav, hsp, hfm, hF, h40, h30, hm⟩ :=
      T.L31d5.mp hs
    clear hs
    have ha3 : t₀.regs.get64 .rsp - 8#64 + (-64 : Int64).toBitVec
        = t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 (rb 0x40) := by
      have : (-64 : Int64).toBitVec = 0xffffffffffffffc0#64 := by decide
      simp only [rb, this]; bv_omega
    have ld1 := fr_load8 hm hF (d := 0x40) (by omega) (by omega) ha3
    have ld2 := c8_load (focus (Mm_avctx ..) hm)
    rw [hav] at ld2
    simp only [arg0] at ld2 h40
    have P40 : PLift (frSlot64 fr 0x40 = arg0 t₀) := ⟨h40⟩
    have Prbp : PLift (s₀.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64) := ⟨hrbp⟩
    have P12 : PLift (s₀.regs.get64 .r12 = arg1 t₀) := ⟨h12⟩
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L31d5]
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, AddrIndex.offset64_none,
      BitVec.add_zero, hrbp, ld1, Option.some.injEq, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp only [h40, ld2, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    have hrbp := Prbp.down
    refine ⟨T.L31eb.mpr ⟨⟨hC, ⟨?_, ?_⟩, ?_, ?_, st, fr, hR, hsp, hfm, hF, hm⟩, ?_⟩, by var_step⟩
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrsp, hrbp, P12.down,
      BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]
    all_goals rfl

set_option maxRecDepth 100000 in
/-- More than 5 patches: `r15 = ac`, `rdi = ac->avctx`, the format, `jmp L20c8`. -/
theorem blk_L31f5 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L31f5" ⟨"sbr_reset.L31f5", B.L31f5, some "sbr_reset.L320e"⟩ := by
  info_off
  measure_hb "L31f5"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hC, ⟨hrsp, hrbp⟩, st, fr, c, hMa, hR, hav, hsp, hfm, hF, h40, h30, hm⟩ :=
      T.L31f5.mp hs
    clear hs
    have ha3 : t₀.regs.get64 .rsp - 8#64 + (-64 : Int64).toBitVec
        = t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 (rb 0x40) := by
      have : (-64 : Int64).toBitVec = 0xffffffffffffffc0#64 := by decide
      simp only [rb, this]; bv_omega
    have ld1 := fr_load8 hm hF (d := 0x40) (by omega) (by omega) ha3
    have ld2 := c8_load (focus (Mm_avctx ..) hm)
    rw [hav] at ld2
    simp only [arg0] at ld2 h40
    have P40 : PLift (frSlot64 fr 0x40 = arg0 t₀) := ⟨h40⟩
    have Prbp : PLift (s₀.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64) := ⟨hrbp⟩
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L31f5]
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, AddrIndex.offset64_none,
      BitVec.add_zero, hrbp, ld1, Option.some.injEq, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp only [h40, ld2, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    have hrbp := Prbp.down
    left; apply Table.ofLabels_at
    refine ⟨by decide, T.L20c8.mpr ⟨hC, ⟨?_, ?_⟩, st, fr, c.nm, c.k0, hMa, hsp, hfm, hF, P40.down,
      ⟨Or.inr hR, h30, ?_, ?_⟩, hm⟩, ?_⟩
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrsp, hrbp,
      BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]
    all_goals try rfl
    edge_step

set_option maxRecDepth 100000 in
/-- The loop's start: `last_k = -1`, `num_patches = 0`, `last_msb = -1`, `msb = k[0]`,
`usb = kx[1]`. -/
theorem blk_L30df (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L30df" ⟨"sbr_reset.L30df", B.L30df, some "sbr_reset.L30f8"⟩ := by
  info_off
  measure_hb "L30df"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hC, ⟨hrsp, hrbp⟩, st, fr, c, hFx, hsp, hfm, hF, h40, h30, h38, h48, h50, h80,
      ⟨hk, hx, hsi, h12⟩, hm⟩ := T.L30df.mp hs
    clear hs
    have hl80 := fr_load hm hF (d := 0x80) (n := 4) (by omega) (by omega)
    have e80 : t₀.regs.get64 .rsp - 8#64 + 18446744073709551488#64
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x80 := by bv_omega
    obtain ⟨-, -, hx32, -⟩ := rsB_fix hFx
    have hpn : (px0 a c (fOf st)).pnum.length = 6 := hFx.2.2.2.2.2.1.2.2.2.2.2.1
    have hps : (px0 a c (fOf st)).pstart.length = 6 := hFx.2.2.2.2.2.2
    have hxe : st.x = pxs a c (fOf st) (pinit a c (fOf st) (s₀.regs.get64 .rdi).toNat) := by
      rw [hx]; simp only [pxs, pinit]; rw [rsB_mk_old hpn, rsB_mk_old hps]
    have hr10 : ∀ v : Int, BitVec.ofInt 32 v = BitVec.ofNat 32 (pkx a (fOf st)) →
        BitVec.setWidth 64 (BitVec.ofInt 32 v) = BitVec.ofNat 64 (pkx a (fOf st)) := by
      intro v hv; rw [hv]; apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
    have hr9 : BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 (pk0 c)))
        = BitVec.ofNat 64 (pk0 c) := by
      apply BitVec.eq_of_toNat_eq
      have := (rsB_fix hFx).1; have := (rsB_fix hFx).2.1
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
    have hH := rsB_hd_init hFx hk
    have PH : PLift (PHd a c (fOf st) (pinit a c (fOf st) (s₀.regs.get64 .rdi).toNat)) := ⟨hH⟩
    have PX : PLift (st.x = pxs a c (fOf st) (pinit a c (fOf st) (s₀.regs.get64 .rdi).toNat)) := ⟨hxe⟩
    have PF : PLift (PFix a c (fOf st)) := ⟨hFx⟩
    have P80 : PLift (frSlot32 fr 0x80 = BitVec.ofNat 32 (pkx a (fOf st))) := ⟨h80⟩
    have PS : PLift (frSlot64 fr 0x40 = arg0 t₀ ∧ frSlot64 fr 0x30 = arg1 t₀
        ∧ frSlot64 fr 0x38 = BitVec.ofNat 64 c.nm ∧ frSlot64 fr 0x48 = arg1 t₀ + 0x4c1f0#64
        ∧ frSlot32 fr 0x50 = BitVec.ofNat 32 (ptop a c (fOf st))) := ⟨h40, h30, h38, h48, h50⟩
    have P12 : PLift (s₀.regs.get64 .r12 = arg1 t₀) := ⟨h12⟩
    have Prsp : PLift (s₀.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x578#64) := ⟨hrsp⟩
    clear hH hxe hFx h80 h40 h30 h38 h48 h50 hk hx
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L30df]
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceMod, Nat.reducePow, Nat.reduceSub,
        Option.isSome_some]
    all_goals try simp only [hrbp, e80, hl80, Option.isSome_some]
    rename_i hld
    simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, hrbp, e80, hl80, Option.some.injEq] at hld
    subst hld
    obtain ⟨h40, h30, h38, h48, h50⟩ := PS.down
    left; apply Table.ofLabels_at
    refine ⟨by decide, T.L312e.mpr ⟨hC, ⟨?_, ?_⟩, st, fr, c, PF.down, hsp, hfm, hF, h40, h30, h38,
      h48, h50, P80.down, ⟨_, PH.down, PX.down, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hm⟩, ?_⟩
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, Prsp.down, hrbp,
      P12.down, hsi, hr9, BitVec.xor_self]
    all_goals first
      | exact hr9
      | exact hr10 _ P80.down
      | rfl
      | (simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done)
      | decide
      | edge_step

/-- The inner loop's fall-through to the trap is unreachable (`j = 0` always stops it). -/
theorem blk_L3187 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L3187" ⟨"sbr_reset.L3187", B.L3187, some "sbr_reset.L318c"⟩ := by
  info_off
  measure_hb "L3187"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    exact (T.L3187.mp hs₀.1).elim

end Kraken.Examples.Sbr.Reset
