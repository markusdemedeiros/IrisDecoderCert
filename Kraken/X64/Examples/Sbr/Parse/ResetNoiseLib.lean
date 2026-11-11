import Kraken.X64.Examples.Sbr.Parse.ResetPatLib

/-!
# `sbr_reset`: the `goal_sb` search of `sbr_hf_calc_npatches`, shared facts (shard B, noise)

`SQ j … s st fr c` is the body of the entry `AtSrch j` with the witnesses fixed. The exits:
`rsN_exit` (the search found `k`: gB's `L30df`), `rsN_next` (the next block of the unrolled
search), `rsN_end` (the search cannot run past `f_master[48]`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false

namespace Kraken.Examples.Sbr.Reset

/-- `goal_sb` of a supported rate is small and positive. -/
theorem rsN_goal {sr : Int} {st xo : Nat} {k0 : Int} {nm : Nat} {f : Nat → Nat}
    (h : Master sr st xo (some k0) (some (nm, f))) : 0 < goalSb sr ∧ goalSb sr < 2 ^ 15 := by
  cases h with
  | ok k2 _ _ hr _ _ _ _ _ _ _ =>
    have : sr = 16000 ∨ sr = 22050 ∨ sr = 24000 ∨ sr = 32000 ∨ sr = 44100 ∨ sr = 48000
        ∨ sr = 64000 ∨ sr = 88200 ∨ sr = 96000 ∨ sr = 128000 ∨ sr = 176400 ∨ sr = 192000 := by
      unfold rateRow at hr
      (repeat' split at hr) <;> first | omega | (simp at hr)
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [goalSb] <;> omega

/-- A 16-bit table value widened (`movzwl`). -/
theorem rsN_sw (F : Nat) (h : F < 2 ^ 16) :
    BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 16 F)))
      = BitVec.ofNat 32 F := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

/-- `goal_sb` in `eax`. -/
theorem rsN_sg (g : Nat) (_h : g < 2 ^ 32) :
    BitVec.setWidth 32 (BitVec.ofNat 64 g) = BitVec.ofNat 32 g := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

/-- `cmp`/`jle` on two small values. -/
theorem rsN_cc_le (x y : Nat) (hx : x < 2 ^ 16) (hy : y < 2 ^ 16) (c f : Bool) :
    CondCode.le.interp (StatusFlags.from_result (BitVec.ofNat 32 x - BitVec.ofNat 32 y)
      { cf := c, af := f, of := (BitVec.ofNat 32 x - BitVec.ofNat 32 y).signed
          != (BitVec.ofNat 32 x).signed - (BitVec.ofNat 32 y).signed }) = decide (x ≤ y) := by
  simp only [CondCode.interp_le, StatusFlags.zf_from_result, StatusFlags.sf_from_result,
    StatusFlags.of_from_result, BitVec.signed]
  have ht : ∀ z : Nat, z < 2 ^ 16 → (BitVec.ofNat 32 z).toInt = (z : Int) := fun z hz => by
    rw [BitVec.toInt_eq_toNat_bmod, BitVec.toNat_ofNat]; simp only [Int.bmod_def]; split <;> omega
  have hs : (BitVec.ofNat 32 x - BitVec.ofNat 32 y).toInt = (x : Int) - y := by
    rw [BitVec.toInt_eq_toNat_bmod, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    simp only [Int.bmod_def]; split <;> omega
  have hm : (BitVec.ofNat 32 x - BitVec.ofNat 32 y).msb = decide (x < y) := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    by_cases h : x < y <;> simp only [h, decide_true, decide_false, decide_eq_true_eq,
      decide_eq_false_iff_not] <;> omega
  have hz : (BitVec.ofNat 32 x - BitVec.ofNat 32 y == BitVec.zero 32) = decide (x = y) := by
    by_cases h : x = y
    · subst h; simp
    · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
      intro h'
      have := congrArg BitVec.toNat h'
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at this
      simp at this; omega
  rw [ht _ hx, ht _ hy, hs, hm, hz]
  by_cases h1 : x < y
  · simp [h1]; omega
  · by_cases h2 : x = y
    · subst h2; simp
    · simp [h1, h2]; omega

variable [CodeEnv]

/-- The body of `AtSrch j` with the witnesses `st fr c`. -/
def SQ (j k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ s : MachineData) (st : St)
    (fr : List UInt8) (c : PCx) : Prop :=
  ResetCI a t₀ ∧ Base t₀ s ∧
    (PFix a c (fOf st) ∧ st.sp = a.sp ∧ st.fm.length = 98 ∧ FrOk fr
    ∧ frSlot64 fr 0x40 = arg0 t₀ ∧ frSlot64 fr 0x30 = arg1 t₀
    ∧ frSlot64 fr 0x38 = BitVec.ofNat 64 c.nm ∧ frSlot64 fr 0x48 = arg1 t₀ + 0x4c1f0#64
    ∧ frSlot32 fr 0x50 = BitVec.ofNat 32 (ptop a c (fOf st))
    ∧ frSlot32 fr 0x80 = BitVec.ofNat 32 (pkx a (fOf st))
    ∧ (goalSb a.x.sampleRate.toInt < ptop a c (fOf st)
      ∧ (∀ i, i < j → ((fOf st) i : Int) < goalSb a.x.sampleRate.toInt)
      ∧ st.x = { px0 a c (fOf st) with npatch := 0 }
      ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (pk0 c) ∧ s.regs.get64 .r12 = arg1 t₀
      ∧ s.regs.get64 .rax = BitVec.ofNat 64 (goalSb a.x.sampleRate.toInt).toNat)
    ∧ (s.dmem =⋆ Mm k e a ra t₀ st fr))

variable {j k : Nat} {e : REnv} {a : RArgs} {ra : Int64} {t₀ s : MachineData} {st : St}
  {fr : List UInt8} {c : PCx}

/-- `f_master[i]` (`i < 49`), at its absolute offset from `sbr`. -/
theorem rsN_ld (h : SQ j k e a ra t₀ s st fr c) {i : Nat} (hi : i < 49) :
    s.dmem.loadInt (arg1 t₀ + BitVec.ofNat 64 (0x4c1f0 + 2 * i)) 2 = some (fOf st i : Int) := by
  obtain ⟨-, -, -, -, hfm, -, -, -, -, -, -, -, -, hm⟩ := h
  refine rsB_fm_load hm hfm hi ?_
  rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- `f_master[i]` as an opaque number `F` (bounded), its load. -/
theorem rsN_ldF (h : SQ j k e a ra t₀ s st fr c) {i : Nat} (hi : i < 49) : ∃ F : Nat,
    F = fOf st i ∧ F < 2 ^ 16
    ∧ s.dmem.loadInt (arg1 t₀ + BitVec.ofNat 64 (0x4c1f0 + 2 * i)) 2 = some (F : Int) := by
  refine ⟨_, rfl, ?_, rsN_ld h hi⟩
  simp only [fOf, u16]
  have := u8_lt st.fm (2 * i); have := u8_lt st.fm (2 * i + 1); omega

/-- The registers of `SQ`. -/
theorem rsN_regs (h : SQ j k e a ra t₀ s st fr c) :
    s.regs.get64 .r12 = arg1 t₀
    ∧ s.regs.get64 .rax = BitVec.ofNat 64 (goalSb a.x.sampleRate.toInt).toNat := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, ⟨-, -, -, -, h12, hax⟩, -⟩ := h
  exact ⟨h12, hax⟩

/-- The numbers of the search: `goal_sb`, `f_master` below `2^16`, `n_master ≤ 48`. -/
theorem rsN_num (h : SQ j k e a ra t₀ s st fr c) :
    0 < goalSb a.x.sampleRate.toInt ∧ goalSb a.x.sampleRate.toInt < 2 ^ 15
    ∧ (∀ i, fOf st i < 2 ^ 16) ∧ c.nm ≤ 48
    ∧ goalSb a.x.sampleRate.toInt < fOf st c.nm
    ∧ (∀ i, i < j → ((fOf st) i : Int) < goalSb a.x.sampleRate.toInt) := by
  obtain ⟨-, -, hFx, -, -, -, -, -, -, -, -, -, ⟨hg, hlt, -⟩, -⟩ := h
  obtain ⟨-, -, -, et, -, -, hnm, -, -⟩ := rsB_fix hFx
  refine ⟨(rsN_goal hFx.1).1, (rsN_goal hFx.1).2, fun i => ?_, hnm, by rw [← et]; exact hg, hlt⟩
  simp only [fOf, u16]
  have := u8_lt st.fm (2 * i); have := u8_lt st.fm (2 * i + 1); omega

/-- The search found `kk` (`f_master[kk] ≥ goal_sb`, all before below): gB's `L30df`. -/
theorem rsN_exit (h : SQ j k e a ra t₀ s st fr c) (s' : MachineData) (hm : s'.dmem = s.dmem)
    (hsp : s'.regs.get64 .rsp = s.regs.get64 .rsp) (hbp : s'.regs.get64 .rbp = s.regs.get64 .rbp)
    (h12 : s'.regs.get64 .r12 = s.regs.get64 .r12) (hsi : s'.regs.get64 .rsi = s.regs.get64 .rsi)
    (kk : Nat) (hdi : s'.regs.get64 .rdi = BitVec.ofNat 64 kk)
    (hlt : ∀ i, j ≤ i → i < kk → ∃ F : Nat, F = fOf st i ∧ (F : Int) < goalSb a.x.sampleRate.toInt)
    (hge : ∃ F : Nat, F = fOf st kk ∧ goalSb a.x.sampleRate.toInt ≤ F) : E.L30df k e a ra t₀ s' := by
  obtain ⟨F, hF, hge⟩ := hge
  subst hF
  have hn := rsN_num h
  obtain ⟨hC, ⟨hrsp, hrbp⟩, hFx, hsp', hfm, hF, h40, h30, h38, h48, h50, h80,
    ⟨hg, hlt0, hx, hsi0, h120, -⟩, hmm⟩ := h
  have hall : ∀ i, i < kk → ((fOf st) i : Int) < goalSb a.x.sampleRate.toInt := fun i hi =>
    if hij : i < j then hlt0 i hij else
      let ⟨F, hF, h⟩ := hlt i (by omega) hi
      hF ▸ h
  have hkn : kk ≤ c.nm := by
    refine Nat.le_of_not_lt fun hc => ?_
    have := hall c.nm hc; omega
  refine ⟨hC, ⟨by rw [hsp, hrsp], by rw [hbp, hrbp]⟩, st, fr, c, hFx, hsp', hfm, hF, h40, h30,
    h38, h48, h50, h80, ⟨?_, hx, by rw [hsi, hsi0], by rw [h12, h120]⟩, by rw [hm]; exact hmm⟩
  rw [hdi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold KInit; split
  · exact ⟨hkn, hall, hge⟩
  · contradiction

/-- The search goes on at `j'`. -/
theorem rsN_next (h : SQ j k e a ra t₀ s st fr c) (s' : MachineData) (hm : s'.dmem = s.dmem)
    (hsp : s'.regs.get64 .rsp = s.regs.get64 .rsp) (hbp : s'.regs.get64 .rbp = s.regs.get64 .rbp)
    (h12 : s'.regs.get64 .r12 = s.regs.get64 .r12) (hsi : s'.regs.get64 .rsi = s.regs.get64 .rsi)
    (hax : s'.regs.get64 .rax = s.regs.get64 .rax) (j' : Nat)
    (hlt : ∀ i, j ≤ i → i < j' → ∃ F : Nat, F = fOf st i ∧ (F : Int) < goalSb a.x.sampleRate.toInt) :
    AtPat k e a ra t₀ s' (fun st c => goalSb a.x.sampleRate.toInt < ptop a c (fOf st)
      ∧ (∀ i, i < j' → ((fOf st) i : Int) < goalSb a.x.sampleRate.toInt)
      ∧ st.x = { px0 a c (fOf st) with npatch := 0 }
      ∧ s'.regs.get64 .rsi = BitVec.ofNat 64 (pk0 c) ∧ s'.regs.get64 .r12 = arg1 t₀
      ∧ s'.regs.get64 .rax = BitVec.ofNat 64 (goalSb a.x.sampleRate.toInt).toNat) := by
  obtain ⟨hC, ⟨hrsp, hrbp⟩, hFx, hsp', hfm, hF, h40, h30, h38, h48, h50, h80,
    ⟨hg, hlt0, hx, hsi0, h120, hax0⟩, hmm⟩ := h
  refine ⟨hC, ⟨by rw [hsp, hrsp], by rw [hbp, hrbp]⟩, st, fr, c, hFx, hsp', hfm, hF, h40, h30,
    h38, h48, h50, h80, ⟨hg, fun i hi => ?_, hx, by rw [hsi, hsi0], by rw [h12, h120],
    by rw [hax, hax0]⟩, by rw [hm]; exact hmm⟩
  exact if hij : i < j then hlt0 i hij else
    let ⟨F, hF, h⟩ := hlt i (by omega) hi
    hF ▸ h

/-- The search cannot pass `f_master[48]` (`n_master ≤ 48`, `goal_sb < f_master[n_master]`). -/
theorem rsN_end (h : SQ j k e a ra t₀ s st fr c)
    (hlt : ∀ i, j ≤ i → i < 49 → ∃ F : Nat, F = fOf st i ∧ (F : Int) < goalSb a.x.sampleRate.toInt) :
    False := by
  obtain ⟨-, -, -, hnm, hgn, hlt0⟩ := rsN_num h
  have : ((fOf st) c.nm : Int) < goalSb a.x.sampleRate.toInt :=
    if hij : c.nm < j then hlt0 _ hij else
      let ⟨F, hF, h⟩ := hlt _ (by omega) (by omega)
      hF ▸ h
  omega

omit [CodeEnv] in
/-- An unsigned 32-bit compare of `goal_sb` with a 16-bit table value. -/
theorem rsN_ule {g : Int} {F : Nat} (hg0 : 0 < g) (hg : g < 2 ^ 15) (hF : F < 2 ^ 16) :
    (BitVec.setWidth 32 (BitVec.ofNat 64 g.toNat) ≤ BitVec.ofNat 32 F) ↔ g ≤ F := by
  rw [BitVec.le_def]; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

end Kraken.Examples.Sbr.Reset
