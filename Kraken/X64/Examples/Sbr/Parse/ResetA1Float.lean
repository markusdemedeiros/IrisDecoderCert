import Kraken.X64.Examples.Sbr.Parse.ResetA1Mem
import Kraken.X64.Examples.Sbr.Parse.ResetLog

/-!
# `sbr_reset`: the `stop_dk` bands (shard A1)

`L11db` .. `L12aa`: `make_bands(stop_dk, stop_min, 64, 13)` unrolled: the powers of the ratio
(`xmm`), their truncations, the differences, stored as `int16` at `rbp - 0x70 .. rbp - 0x58`.
Only the frame bytes there change; the saved `ac` / `sbr` slots stay.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Reset

variable [CodeEnv]

/-- `vcvtss2si %src, %r64`: the low float of `src` converted to a 64-bit integer. -/
theorem a1_vcvtss2si_spec {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}
    {p : Program} {w : AvxWidth} (asz : Width) (r : Reg64) (src : AvxReg .W128) :
    ⦃ fun s => WP.wp p Q E { s with regs := (s.regs.set64 r
        (BitVec.f32toi64 ((s.zmms.get src).setWidth 32))) } ⦄
      (Directive.instr (.avx asz w (.vcvtss2si (Reg.low r .W64) (.avx src))) :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by
    simp only [Directive.interp, Instr.interp, AvxOperation.interp, MachineData.setReg,
      Reg64s.set_low64, Effects.All]
    simp only [AvxRegOrMem.interpLow]
    exact hP)

section Mem

variable {k : Nat} {e : REnv} {a : RArgs} {ra : Int64} {t₀ : MachineData} {st : St}
  {fr : List UInt8} {m : Mem 64}

/-- Some frame with the saved `ac` / `sbr` slots holds the memory. -/
def a1FK (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) (st : St)
    (m : Mem 64) : Prop :=
  ∃ fr, FrOk fr ∧ frSlot64 fr 0x40 = arg0 t₀ ∧ frSlot64 fr 0x30 = arg1 t₀
    ∧ (m =⋆ Mm k e a ra t₀ st fr)

omit [CodeEnv] in
theorem a1_fa (r : BitVec 64) (d : Nat) (N : Int64) (h : N.toBitVec = -BitVec.ofNat 64 d) :
    r - 8#64 + N.toBitVec = r - 8#64 - BitVec.ofNat 64 d := by
  rw [h]; bv_omega

/-- A store into the frame below the saved slots. -/
theorem a1_fk_store (h : a1FK k e a ra t₀ st m) {d n : Nat} (hn : n + 0x28 ≤ d) (hd : d ≤ 0x570)
    (h1 : 0x40 + n ≤ d) (v : Int) :
    a1FK k e a ra t₀ st (m.storeInt (t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 d) n v) := by
  obtain ⟨fr, hF, h40, h30, hm⟩ := h
  exact ⟨_, fr_wr_len hF (by simp only [rb]; omega) v,
    by rw [frSlot64_wr_other hF hn hd v (by omega) (by omega) (by omega), h40],
    by rw [frSlot64_wr_other hF hn hd v (by omega) (by omega) (by omega), h30],
    fr_store hm hF hn hd v⟩

/-- The frame is readable (the check of a store). -/
theorem a1_fk_isSome (h : a1FK k e a ra t₀ st m) {d n : Nat} (hn : n + 0x28 ≤ d)
    (hd : d ≤ 0x570) :
    (m.loadInt (t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 d) n).isSome = true := by
  obtain ⟨fr, hF, -, -, hm⟩ := h
  rw [fr_load hm hF hn hd]; rfl

/-- The store of the `AV_QSORT` stack base at `rbp - 0x570`. -/
theorem a1_fk_store570 (h : a1FK k e a ra t₀ st m) (v : Int) :
    ∃ fr, FrOk fr ∧ frSlot64 fr 0x40 = arg0 t₀ ∧ frSlot64 fr 0x30 = arg1 t₀
      ∧ frSlot64 fr 0x570 = BitVec.ofInt 64 v
      ∧ (m.storeInt (t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x570) 8 v
          =⋆ Mm k e a ra t₀ st fr) := by
  obtain ⟨fr, hF, h40, h30, hm⟩ := h
  exact ⟨_, fr_wr_len hF (by simp only [rb]; omega) v,
    by rw [frSlot64_wr_other hF (by omega) (by omega) v (by omega) (by omega) (by omega), h40],
    by rw [frSlot64_wr_other hF (by omega) (by omega) v (by omega) (by omega) (by omega), h30],
    frSlot64_wr_same hF (by omega) (by omega) v,
    fr_store hm hF (by omega) (by omega) v⟩

end Mem

theorem a1_SD_of {k : Nat} {e : REnv} {a : RArgs} {ra : Int64} {t₀ s : MachineData} {st : St}
    {row : Nat} (hr : rateRow (srI a) = some row) (hsp1 : u8 a.sp 1 ≤ 13) (hC : ResetCI a t₀)
    (hBO : BandsOK e.lg e.pw) (hb : Base t₀ s) (hx : st.x = xk0 a row) (hsp : st.sp = a.sp)
    (hfm : st.fm.length = 98) (h : a1FK k e a ra t₀ st s.dmem) :
    SD k e a ra t₀ s (fun _ _ => True) := by
  obtain ⟨fr, hF, h4, h3, hm⟩ := h
  exact ⟨row, hr, hsp1, hC, hBO, hb, st, fr, hx, hsp, hfm, hF, ⟨h4, h3, trivial⟩, hm⟩

theorem a1_SD570_of {k : Nat} {e : REnv} {a : RArgs} {ra : Int64} {t₀ s : MachineData} {st : St}
    {row : Nat} {v : Int} (hr : rateRow (srI a) = some row) (hsp1 : u8 a.sp 1 ≤ 13)
    (hC : ResetCI a t₀) (hBO : BandsOK e.lg e.pw) (hb : Base t₀ s) (hx : st.x = xk0 a row)
    (hsp : st.sp = a.sp) (hfm : st.fm.length = 98)
    (h : ∃ fr, FrOk fr ∧ frSlot64 fr 0x40 = arg0 t₀ ∧ frSlot64 fr 0x30 = arg1 t₀
      ∧ frSlot64 fr 0x570 = BitVec.ofInt 64 v ∧ (s.dmem =⋆ Mm k e a ra t₀ st fr))
    (hv : BitVec.ofInt 64 v = t₀.regs.get64 .rsp - 0x78#64) :
    SD k e a ra t₀ s (fun _ fr => frSlot64 fr 0x570 = t₀.regs.get64 .rsp - 0x78#64) := by
  obtain ⟨fr, hF, h4, h3, h5, hm⟩ := h
  exact ⟨row, hr, hsp1, hC, hBO, hb, st, fr, hx, hsp, hfm, hF, ⟨h4, h3, h5.trans hv⟩, hm⟩

theorem blk_L11db (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L11db" ⟨"sbr_reset.L11db", B.L11db, some "sbr_reset.L1211"⟩ := by
  info_off
  measure_hb "L11db"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, hr, hsp1, ⟨hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF, ⟨h40, h30, -⟩, hm⟩⟩ :=
      T.L11db.mp hs
    clear hs
    have hK : a1FK k e a ra t₀ st s₀.dmem := ⟨fr, hF, h40, h30, hm⟩
    have ha : t₀.regs.get64 .rsp - 8#64 + 0 + (-56 : Int64).toBitVec
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x38 := by
      rw [show (-56 : Int64).toBitVec = -56#64 from rfl]; bv_omega
    clear hm h40 h30
    simp only [B.L11db]
    vcgen [a1_vcvtss2si_spec]
    all_goals try subst_vars
    all_goals try simp only [AddrIndex.offset64_none, hrbp, ha]
    · exact a1_fk_isSome (d := 0x38) (n := 4) hK (by omega) (by omega)
    · refine ⟨T.L1211.mpr (a1_SD_of hr hsp1 hC hBO ⟨?_, ?_⟩ hx hsp hfm hK), by var_step⟩
      all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp]

theorem blk_L1211 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1211" ⟨"sbr_reset.L1211", B.L1211, some "sbr_reset.L1249"⟩ := by
  info_off
  measure_hb "L1211"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, hr, hsp1, ⟨hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF, ⟨h40, h30, -⟩, hm⟩⟩ :=
      T.L1211.mp hs
    clear hs
    have hK : a1FK k e a ra t₀ st s₀.dmem := ⟨fr, hF, h40, h30, hm⟩
    clear hm h40 h30
    simp only [B.L1211]
    vcgen [a1_vcvtss2si_spec]
    all_goals try subst_vars
    refine ⟨T.L1249.mpr (a1_SD_of hr hsp1 hC hBO ⟨?_, ?_⟩ hx hsp hfm hK), by var_step⟩
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp]

theorem blk_L1249 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1249" ⟨"sbr_reset.L1249", B.L1249, some "sbr_reset.L126b"⟩ := by
  info_off
  measure_hb "L1249"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, hr, hsp1, ⟨hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF, ⟨h40, h30, -⟩, hm⟩⟩ :=
      T.L1249.mp hs
    clear hs
    have hK : a1FK k e a ra t₀ st s₀.dmem := ⟨fr, hF, h40, h30, hm⟩
    clear hm h40 h30
    simp only [B.L1249]
    vcgen [a1_vcvtss2si_spec]
    all_goals try subst_vars
    refine ⟨T.L126b.mpr (a1_SD_of hr hsp1 hC hBO ⟨?_, ?_⟩ hx hsp hfm hK), by var_step⟩
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp]

theorem blk_L126b (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L126b" ⟨"sbr_reset.L126b", B.L126b, some "sbr_reset.L1278"⟩ := by
  info_off
  measure_hb "L126b"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, hr, hsp1, ⟨hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF, ⟨h40, h30, -⟩, hm⟩⟩ :=
      T.L126b.mp hs
    clear hs
    have hK : a1FK k e a ra t₀ st s₀.dmem := ⟨fr, hF, h40, h30, hm⟩
    clear hm h40 h30
    have ha1 : t₀.regs.get64 .rsp - 8#64 + 0 + (-0x70 : Int64).toBitVec
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x70 := by
      rw [show (-0x70 : Int64).toBitVec = -0x70#64 from rfl]; bv_omega
    have ha2 : t₀.regs.get64 .rsp - 8#64 + 0 + (-0x6e : Int64).toBitVec
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x6e := by
      rw [show (-0x6e : Int64).toBitVec = -0x6e#64 from rfl]; bv_omega
    simp only [B.L126b]
    vcgen
    all_goals try subst_vars
    all_goals try simp only [AddrIndex.offset64_none, reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      hrbp, ha1, ha2]
    · exact a1_fk_isSome (d := 0x70) (n := 2) hK (by omega) (by omega)
    · exact a1_fk_isSome (d := 0x6e) (n := 2)
        (a1_fk_store (d := 0x70) (n := 2) hK (by omega) (by omega) (by omega) _) (by omega) (by omega)
    · refine ⟨T.L1278.mpr (a1_SD_of hr hsp1 hC hBO ⟨?_, ?_⟩ hx hsp hfm
        (a1_fk_store (d := 0x6e) (n := 2)
          (a1_fk_store (d := 0x70) (n := 2) hK (by omega) (by omega) (by omega) _)
          (by omega) (by omega) (by omega) _)), by var_step⟩
      all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp]

theorem blk_L1278 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1278" ⟨"sbr_reset.L1278", B.L1278, some "sbr_reset.L1280"⟩ := by
  info_off
  measure_hb "L1278"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, hr, hsp1, ⟨hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF, ⟨h40, h30, -⟩, hm⟩⟩ :=
      T.L1278.mp hs
    clear hs
    have hK : a1FK k e a ra t₀ st s₀.dmem := ⟨fr, hF, h40, h30, hm⟩
    clear hm h40 h30
    have ha1 : t₀.regs.get64 .rsp - 8#64 + 0 + (-0x6c : Int64).toBitVec
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x6c := by
      rw [show (-0x6c : Int64).toBitVec = -0x6c#64 from rfl]; bv_omega
    have ha2 : t₀.regs.get64 .rsp - 8#64 + 0 + (-0x6a : Int64).toBitVec
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x6a := by
      rw [show (-0x6a : Int64).toBitVec = -0x6a#64 from rfl]; bv_omega
    simp only [B.L1278]
    vcgen
    all_goals try subst_vars
    all_goals try simp only [AddrIndex.offset64_none, reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      hrbp, ha1, ha2]
    · exact a1_fk_isSome (d := 0x6c) (n := 2) hK (by omega) (by omega)
    · exact a1_fk_isSome (d := 0x6a) (n := 2)
        (a1_fk_store (d := 0x6c) (n := 2) hK (by omega) (by omega) (by omega) _) (by omega) (by omega)
    · refine ⟨T.L1280.mpr (a1_SD_of hr hsp1 hC hBO ⟨?_, ?_⟩ hx hsp hfm
        (a1_fk_store (d := 0x6a) (n := 2)
          (a1_fk_store (d := 0x6c) (n := 2) hK (by omega) (by omega) (by omega) _)
          (by omega) (by omega) (by omega) _)), by var_step⟩
      all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp]

theorem blk_L1280 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1280" ⟨"sbr_reset.L1280", B.L1280, some "sbr_reset.L1288"⟩ := by
  info_off
  measure_hb "L1280"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, hr, hsp1, ⟨hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF, ⟨h40, h30, -⟩, hm⟩⟩ :=
      T.L1280.mp hs
    clear hs
    have hK : a1FK k e a ra t₀ st s₀.dmem := ⟨fr, hF, h40, h30, hm⟩
    clear hm h40 h30
    have ha1 : t₀.regs.get64 .rsp - 8#64 + 0 + (-0x68 : Int64).toBitVec
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x68 := by
      rw [show (-0x68 : Int64).toBitVec = -0x68#64 from rfl]; bv_omega
    have ha2 : t₀.regs.get64 .rsp - 8#64 + 0 + (-0x66 : Int64).toBitVec
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x66 := by
      rw [show (-0x66 : Int64).toBitVec = -0x66#64 from rfl]; bv_omega
    simp only [B.L1280]
    vcgen
    all_goals try subst_vars
    all_goals try simp only [AddrIndex.offset64_none, reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      hrbp, ha1, ha2]
    · exact a1_fk_isSome (d := 0x68) (n := 2) hK (by omega) (by omega)
    · exact a1_fk_isSome (d := 0x66) (n := 2)
        (a1_fk_store (d := 0x68) (n := 2) hK (by omega) (by omega) (by omega) _) (by omega) (by omega)
    · refine ⟨T.L1288.mpr (a1_SD_of hr hsp1 hC hBO ⟨?_, ?_⟩ hx hsp hfm
        (a1_fk_store (d := 0x66) (n := 2)
          (a1_fk_store (d := 0x68) (n := 2) hK (by omega) (by omega) (by omega) _)
          (by omega) (by omega) (by omega) _)), by var_step⟩
      all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp]

theorem blk_L1288 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1288" ⟨"sbr_reset.L1288", B.L1288, some "sbr_reset.L1292"⟩ := by
  info_off
  measure_hb "L1288"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, hr, hsp1, ⟨hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF, ⟨h40, h30, -⟩, hm⟩⟩ :=
      T.L1288.mp hs
    clear hs
    have hK : a1FK k e a ra t₀ st s₀.dmem := ⟨fr, hF, h40, h30, hm⟩
    clear hm h40 h30
    have ha1 : t₀.regs.get64 .rsp - 8#64 + 0 + (-0x64 : Int64).toBitVec
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x64 := by
      rw [show (-0x64 : Int64).toBitVec = -0x64#64 from rfl]; bv_omega
    have ha2 : t₀.regs.get64 .rsp - 8#64 + 0 + (-0x62 : Int64).toBitVec
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x62 := by
      rw [show (-0x62 : Int64).toBitVec = -0x62#64 from rfl]; bv_omega
    simp only [B.L1288]
    vcgen
    all_goals try subst_vars
    all_goals try simp only [AddrIndex.offset64_none, reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      hrbp, ha1, ha2]
    · exact a1_fk_isSome (d := 0x64) (n := 2) hK (by omega) (by omega)
    · exact a1_fk_isSome (d := 0x62) (n := 2)
        (a1_fk_store (d := 0x64) (n := 2) hK (by omega) (by omega) (by omega) _) (by omega) (by omega)
    · refine ⟨T.L1292.mpr (a1_SD_of hr hsp1 hC hBO ⟨?_, ?_⟩ hx hsp hfm
        (a1_fk_store (d := 0x62) (n := 2)
          (a1_fk_store (d := 0x64) (n := 2) hK (by omega) (by omega) (by omega) _)
          (by omega) (by omega) (by omega) _)), by var_step⟩
      all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp]

theorem blk_L1292 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1292" ⟨"sbr_reset.L1292", B.L1292, some "sbr_reset.L129c"⟩ := by
  info_off
  measure_hb "L1292"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, hr, hsp1, ⟨hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF, ⟨h40, h30, -⟩, hm⟩⟩ :=
      T.L1292.mp hs
    clear hs
    have hK : a1FK k e a ra t₀ st s₀.dmem := ⟨fr, hF, h40, h30, hm⟩
    clear hm h40 h30
    have ha1 : t₀.regs.get64 .rsp - 8#64 + 0 + (-0x60 : Int64).toBitVec
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x60 := by
      rw [show (-0x60 : Int64).toBitVec = -0x60#64 from rfl]; bv_omega
    have ha2 : t₀.regs.get64 .rsp - 8#64 + 0 + (-0x5e : Int64).toBitVec
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x5e := by
      rw [show (-0x5e : Int64).toBitVec = -0x5e#64 from rfl]; bv_omega
    simp only [B.L1292]
    vcgen
    all_goals try subst_vars
    all_goals try simp only [AddrIndex.offset64_none, reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      hrbp, ha1, ha2]
    · exact a1_fk_isSome (d := 0x60) (n := 2) hK (by omega) (by omega)
    · exact a1_fk_isSome (d := 0x5e) (n := 2)
        (a1_fk_store (d := 0x60) (n := 2) hK (by omega) (by omega) (by omega) _) (by omega) (by omega)
    · refine ⟨T.L129c.mpr (a1_SD_of hr hsp1 hC hBO ⟨?_, ?_⟩ hx hsp hfm
        (a1_fk_store (d := 0x5e) (n := 2)
          (a1_fk_store (d := 0x60) (n := 2) hK (by omega) (by omega) (by omega) _)
          (by omega) (by omega) (by omega) _)), by var_step⟩
      all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp]

theorem blk_L129c (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L129c" ⟨"sbr_reset.L129c", B.L129c, some "sbr_reset.L12aa"⟩ := by
  info_off
  measure_hb "L129c"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, hr, hsp1, ⟨hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF, ⟨h40, h30, -⟩, hm⟩⟩ :=
      T.L129c.mp hs
    clear hs
    have hK : a1FK k e a ra t₀ st s₀.dmem := ⟨fr, hF, h40, h30, hm⟩
    clear hm h40 h30
    have ha1 : t₀.regs.get64 .rsp - 8#64 + 0 + (-0x5c : Int64).toBitVec
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x5c := by
      rw [show (-0x5c : Int64).toBitVec = -0x5c#64 from rfl]; bv_omega
    have ha2 : t₀.regs.get64 .rsp - 8#64 + 0 + (-0x5a : Int64).toBitVec
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x5a := by
      rw [show (-0x5a : Int64).toBitVec = -0x5a#64 from rfl]; bv_omega
    simp only [B.L129c]
    vcgen
    all_goals try subst_vars
    all_goals try simp only [AddrIndex.offset64_none, reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      hrbp, ha1, ha2]
    · exact a1_fk_isSome (d := 0x5c) (n := 2) hK (by omega) (by omega)
    · exact a1_fk_isSome (d := 0x5a) (n := 2)
        (a1_fk_store (d := 0x5c) (n := 2) hK (by omega) (by omega) (by omega) _) (by omega) (by omega)
    · refine ⟨T.L12aa.mpr ⟨a1_SD_of hr hsp1 hC hBO ⟨?_, ?_⟩ hx hsp hfm
        (a1_fk_store (d := 0x5a) (n := 2)
          (a1_fk_store (d := 0x5c) (n := 2) hK (by omega) (by omega) (by omega) _)
          (by omega) (by omega) (by omega) _), ?_⟩, by var_step⟩
      all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp]
      rw [show (-0x58 : Int64).toBitVec = -0x58#64 from rfl]; bv_omega

/-- The last `int16`, the `AV_QSORT` stack base `rbp - 0x70` saved at `rbp - 0x570`. -/
theorem blk_L12aa (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L12aa" ⟨"sbr_reset.L12aa", B.L12aa, some "sbr_reset.L12ba"⟩ := by
  info_off
  measure_hb "L12aa"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨⟨row, hr, hsp1, ⟨hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF, ⟨h40, h30, -⟩, hm⟩⟩,
      hax⟩ := T.L12aa.mp hs
    clear hs
    have hK : a1FK k e a ra t₀ st s₀.dmem := ⟨fr, hF, h40, h30, hm⟩
    clear hm h40 h30
    have ha1 : t₀.regs.get64 .rsp - 8#64 + 0 + (-0x58 : Int64).toBitVec
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x58 := by
      rw [show (-0x58 : Int64).toBitVec = -0x58#64 from rfl]; bv_omega
    have ha2 : t₀.regs.get64 .rsp - 8#64 + (-0x570 : Int64).toBitVec
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x570 := by
      rw [show (-0x570 : Int64).toBitVec = -0x570#64 from rfl]; bv_omega
    simp only [B.L12aa]
    vcgen
    all_goals try subst_vars
    all_goals try simp only [AddrIndex.offset64_none, reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      hrbp, ha1, ha2]
    · exact a1_fk_isSome (d := 0x58) (n := 2) hK (by omega) (by omega)
    · exact a1_fk_isSome (d := 0x570) (n := 8)
        (a1_fk_store (d := 0x58) (n := 2) hK (by omega) (by omega) (by omega) _) (by omega) (by omega)
    · refine ⟨T.L12ba.mpr ⟨a1_SD570_of hr hsp1 hC hBO ⟨?_, ?_⟩ hx hsp hfm
        (a1_fk_store570 (a1_fk_store (d := 0x58) (n := 2) hK (by omega) (by omega) (by omega) _) _)
        ?_, ?_⟩, by var_step⟩
      all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, hax,
        BitVec.ofInt_toInt]
      rw [show (-0x70 : Int64).toBitVec = -0x70#64 from rfl]; bv_omega

end Kraken.Examples.Sbr.Reset
