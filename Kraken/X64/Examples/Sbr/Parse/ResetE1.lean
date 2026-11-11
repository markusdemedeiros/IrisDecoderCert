import Kraken.InfoOff
import Kraken.X64.Examples.Sbr.Parse.ResetELib
import Kraken.X64.Examples.Sbr.Parse.ResetDer

/-!
# `sbr_reset`: `sbr_make_f_derived`, the `f_tablelow` copy (`derived2`): dispatch, scalar loop
(shard B, env)
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Reset

variable [CodeEnv]

macro "rsE_rs" : tactic => `(tactic| simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte])

omit [CodeEnv] in
theorem rsE_z_and (a : BitVec 32) (fl : StatusFlags.from_result.Remaining) :
    CondCode.z.interp (StatusFlags.from_result (a &&& a) fl) = decide (a = 0) := by
  rw [CondCode.interp_z, StatusFlags.zf_from_result, BitVec.and_self]
  rw [Bool.eq_iff_iff]; simp

omit [CodeEnv] in
theorem rsE_toInt16 (w : BitVec 16) : (w.toInt % 65536).toNat = w.toNat := by
  rw [BitVec.toInt_eq_toNat_bmod]
  have := w.isLt
  simp only [Int.bmod_def]; split <;> omega

omit [CodeEnv] in
theorem rsE_sw16 (n : Nat) : (BitVec.setWidth 16 (BitVec.ofNat 64 n)).toNat = n % 65536 := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

omit [CodeEnv] in
theorem rsE_sw32 (n : Nat) (h : n < 2 ^ 32) : BitVec.setWidth 32 (BitVec.ofNat 64 n) = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

omit [CodeEnv] in
theorem rsE_and1 (n : Nat) (h : n < 2 ^ 32) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 n) &&& BitVec.setWidth 32 1#64)
      = BitVec.ofNat 64 (n % 2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [Nat.and_one_is_mod]; omega

omit [CodeEnv] in
theorem rsE_one32 : BitVec.setWidth 64 (BitVec.setWidth 32 1#64) = BitVec.ofNat 64 (0 + 1) := rfl

omit [CodeEnv] in
theorem rsE_xor_self (x : BitVec 64) :
    BitVec.setWidth 64 (BitVec.setWidth 32 x ^^^ BitVec.setWidth 32 x) = BitVec.ofNat 64 0 := by
  rw [BitVec.xor_self]; rfl

omit [CodeEnv] in
theorem rsE_r8 (n m : Nat) (h : m < n) (hn : n < 2 ^ 32) :
    BitVec.ofNat 64 n - BitVec.ofNat 64 (m + 1) + 1 = BitVec.ofNat 64 (n - m) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (1 : BitVec 64).toNat = 1 := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h1]; omega

omit [CodeEnv] in
theorem rsE_rdx (x : BitVec 64) (m : Nat) (hm : m < 2 ^ 32) :
    311890#64 + (x + BitVec.ofNat 64 (m + 1) * BitVec.ofNat 64 2 + 0#64)
      = x + BitVec.ofNat 64 (0x4c252 + 2 * (m + 1)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]; omega

omit [CodeEnv] in
theorem rsE_rax (x : BitVec 64) (m p : Nat) (hm : m < 2 ^ 32) (hp : p < 2) :
    311940#64 + (x + BitVec.ofNat 64 (m + 1) * BitVec.ofNat 64 4 + 0#64
      - BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 p) + BitVec.setWidth 32 (BitVec.ofNat 64 p)))
      = x + BitVec.ofNat 64 (0x4c284 + 4 * (m + 1) - 2 * p) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_ofNat,
    BitVec.toNat_setWidth]; omega

set_option maxRecDepth 100000 in
/-- `f_tablelow[0] = f_tablehigh[0]`, the dispatch on `n0`. -/
theorem blk_L20d8 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L20d8" ⟨"sbr_reset.L20d8", B.L20d8, some "sbr_reset.L2112"⟩ := by
  info_off
  measure_hb "L20d8"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hC, ⟨hrsp, hrbp⟩, st, fr, nm, k0, hMa, hsp, hfm, hF, h40,
      ⟨hk2, hx, h38, h30, h12, h13, h15, h14, hf64, hbr, h10, hcx⟩, hm⟩ := T.L20d8.mp hs
    clear hs
    obtain ⟨hxo, hnm, -, -⟩ := master_bounds hMa
    have hxo' : xoOf a < nm := hxo
    have ha3 : s₀.regs.get64 .rbp + (-48 : Int64).toBitVec
        = t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 (rb 0x30) := by
      have : (-48 : Int64).toBitVec = 0xffffffffffffffd0#64 := by decide
      simp only [rb, this, hrbp]; bv_omega
    have ld1 := fr_load8 hm hF (d := 0x30) (by omega) (by omega) ha3
    have h30' : BitVec.ofInt 64 (Int.ofBytes (slice fr 1344 8)) = arg1 t₀ := h30
    have hfl : st.x.ftLow.length = 50 := by rw [hx]; exact hC.2.2.2.2.2.2.1
    have hfl0 : st.x.ftLow = (dD1 a k0 nm (fOf st)).ftLow := by rw [hx]
    have ho : arg1 t₀ + 311890#64 = arg1 t₀ + 0x4c252#64 + BitVec.ofNat 64 0 := by
      rw [BitVec.add_zero]
    have hfm' := focus (Mm_ftLow ..) hm
    have hld : (s₀.dmem.loadInt (arg1 t₀ + 311890#64) 2).isSome = true := by
      rw [region_load (o := 0) (n := 2) hfm' ho (by rw [hfl]; omega) (by rw [hfl]; omega)]; rfl
    have hval : (((BitVec.setWidth 16 (s₀.regs.get64 .r14)).toInt % 65536).toNat
        = fOf st (xoOf a) % 65536) := by rw [rsE_toInt16, h14, rsE_sw16]
    have hst := region_store (o := 0) (n := 2) hfm' ho (by rw [hfl]; omega) (by rw [hfl]; omega)
      (BitVec.setWidth 16 (s₀.regs.get64 .r14)).toInt
    rw [hfl0, rsE_LowM_zero _ _ _ (by rw [← hfl0]; exact hfl) _ hval, Mm_upd_ftLow] at hst
    have hx' : ({ st with x := { st.x with ftLow := LowM (dD1 a k0 nm (fOf st)) (xoOf a) (fOf st) 0 } } : St).x
        = dLw a k0 nm (fOf st) 0 := by
      show ({ st.x with ftLow := _ } : Args) = _
      rw [hx]
    have hn1 : 1 ≤ (nm - xoOf a + 1) / 2 := by omega
    have hr15 : BitVec.setWidth 32 (s₀.regs.get64 .r15) = BitVec.ofNat 32 ((nm - xoOf a + 1) / 2) := by
      rw [h15, rsE_sw32 _ (by omega)]
    have hr12 : (BitVec.setWidth 32 (s₀.regs.get64 .r12)).toNat = nm - xoOf a + 1 := by
      rw [h12, rsE_sw32 _ (by omega), BitVec.toNat_ofNat]; omega
    have hr13 := rsE_and1 (nm - xoOf a) (by omega)
    rw [← h13] at hr13
    clear hm hfm' hfl0 hx
    have hne : (BitVec.ofNat 32 ((nm - xoOf a + 1) / 2) = 0) = False := by
      apply propext; constructor
      · intro h; have := congrArg BitVec.toNat h; simp at this; omega
      · intro h; exact h.elim
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    have h17 : 34 ≤ nm - xoOf a + 1 → 17 ≤ (nm - xoOf a + 1) / 2 := by omega
    have h5 : 10 ≤ nm - xoOf a + 1 → 0 + 5 ≤ (nm - xoOf a + 1) / 2 := by omega
    have P30 : PLift (frSlot64 fr 0x30 = arg1 t₀) := ⟨h30⟩
    have Px := (⟨hx'⟩ : PLift (({ st with x := { st.x with ftLow := LowM (dD1 a k0 nm (fOf st)) (xoOf a) (fOf st) 0 } } : St).x
        = dLw a k0 nm (fOf st) 0))
    have Pst := PLift.up hst
    clear h30 hx' hst
    simp only [B.L20d8]
    vcgen
    all_goals try subst_vars
    all_goals simp only [AddrIndex.offset64_none, z, ld1, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, rsE_z_and, hr15, hne,
      decide_false, Bool.false_eq_true, Kraken.Examples.Sbr.Reset.cc_c_sub,
      Kraken.Examples.Sbr.Reset.cc_nc_sub, decide_eq_true_eq, decide_eq_false_iff_not, hr12,
      BitVec.reduceSetWidth, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, Nat.reduceSub, h30', Nat.not_lt] at *
    case vc2 => exact hld
    case vc3 => rename_i hz; rw [hne] at hz; exact hz.elim
    case vc4 =>
      exact Or.inl (Table.ofLabels_at ⟨S.L2aef, T.L2aef.mpr ⟨hC, ⟨by rsE_rs; exact hrsp,
        by rsE_rs; exact hrbp⟩, { st with x := { st.x with ftLow := LowM (dD1 a k0 nm (fOf st)) (xoOf a) (fOf st) 0 } }, fr, nm, k0, hMa, hsp, hfm, hF, h40, ⟨hk2, hf64, hbr, P30.down, h38, 0,
        Px.down, by rsE_rs; exact h14, by rsE_rs; exact h15,
        by rsE_rs; exact h10, by rsE_rs; exact hcx, hn1, by rsE_rs; exact hr13,
        by rsE_rs <;> rfl⟩, Pst.down⟩, by edge_step⟩)
    case vc5 =>
      rename_i _ hc
      exact Or.inl (Table.ofLabels_at ⟨S.L29f4, T.L29f4.mpr ⟨hC, ⟨by rsE_rs; exact hrsp,
        by rsE_rs; exact hrbp⟩, { st with x := { st.x with ftLow := LowM (dD1 a k0 nm (fOf st)) (xoOf a) (fOf st) 0 } }, fr, nm, k0, hMa, hsp, hfm, hF, h40, ⟨hk2, hf64, hbr, P30.down, h38, 0,
        Px.down, by rsE_rs; exact h14, by rsE_rs; exact h15,
        by rsE_rs; exact h10, by rsE_rs; exact hcx, rfl, h17 hc, by rsE_rs; exact hr13⟩, Pst.down⟩,
        by edge_step⟩)
    case vc6 =>
      rename_i hc _
      exact Or.inl (Table.ofLabels_at ⟨S.L2a85, T.L2a85.mpr ⟨hC, ⟨by rsE_rs; exact hrsp,
        by rsE_rs; exact hrbp⟩, { st with x := { st.x with ftLow := LowM (dD1 a k0 nm (fOf st)) (xoOf a) (fOf st) 0 } }, fr, nm, k0, hMa, hsp, hfm, hF, h40, ⟨hk2, hf64, hbr, P30.down, h38, 0,
        Px.down, by rsE_rs; exact h14, by rsE_rs; exact h15,
        by rsE_rs; exact h10, by rsE_rs; exact hcx, by rsE_rs; exact hr13, rfl, h5 hc,
        by rsE_rs; exact rsE_xor_self _⟩, Pst.down⟩, by edge_step⟩)

set_option maxRecDepth 100000 in
/-- The scalar copy's setup (`b = m`, `j = 0`). -/
theorem blk_L2aef (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2aef" ⟨"sbr_reset.L2aef", B.L2aef, some "sbr_reset.L2b20"⟩ := by
  info_off
  measure_hb "L2aef"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hC, ⟨hrsp, hrbp⟩, st, fr, nm, k0, hMa, hsp, hfm, hF, h40,
      ⟨hk2, hf64, hbr, h30, h38, m, hx, h14, h15, h10, hcx, hlt, h13, hax⟩, hm⟩ := T.L2aef.mp hs
    clear hs
    obtain ⟨hxo, hnm, -, -⟩ := master_bounds hMa
    have ha3 : s₀.regs.get64 .rbp + (-48 : Int64).toBitVec
        = t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 (rb 0x30) := by
      have : (-48 : Int64).toBitVec = 0xffffffffffffffd0#64 := by decide
      simp only [rb, this, hrbp]; bv_omega
    have ld1 := fr_load8 hm hF (d := 0x30) (by omega) (by omega) ha3
    have h30' : BitVec.ofInt 64 (Int.ofBytes (slice fr 1344 8)) = arg1 t₀ := h30
    have P30 : PLift (frSlot64 fr 0x30 = arg1 t₀) := ⟨h30⟩
    have P1 := PLift.up ld1
    have Px := PLift.up hx
    have Pm := PLift.up hm
    clear h30 hx hm ld1
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    simp only [B.L2aef]
    vcgen
    all_goals try subst_vars
    case vc1 =>
      simp only [AddrIndex.offset64_none, z, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      rw [P1.down]; rfl
    case vc2 =>
      rename_i v hl _
      dsimp only at hl
      try simp only [AddrIndex.offset64_none, z, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] at hl
      have hl := hl.symm.trans P1.down
      simp only [Option.some.injEq] at hl
      subst hl
      simp only [AddrIndex.offset64_none, z, h30', Reg64s.get64_set64, reduceCtorEq, ↓reduceIte,
        AddrIndex.offset64, Int64.toBitVec_ofNat_norm, BitVec.reduceSetWidth] at *
      have hp : (nm - xoOf a) % 2 < 2 := Nat.mod_lt _ (by omega)
      have hlt' : m < (nm - xoOf a + 1) / 2 := hlt
      refine ⟨T.L2b20.mpr ⟨hC, ⟨by rsE_rs; exact hrsp, by rsE_rs; exact hrbp⟩, st, fr, nm, k0, hMa, hsp,
        hfm, hF, h40, ⟨hk2, hf64, hbr, P30.down, h38, m, Px.down, by rsE_rs; exact h14, by rsE_rs; exact h15, by rsE_rs; exact h10, by rsE_rs; exact hcx,
        m, 0, rfl, hlt, by rsE_rs; exact rsE_xor_self _, ?_, ?_, ?_⟩, Pm.down⟩, by var_step⟩
      · rsE_rs; rw [h15, hax]; exact rsE_r8 _ _ hlt' (by omega)
      · rsE_rs; rw [hax]; exact rsE_rdx _ _ (by omega)
      · rsE_rs; rw [hax, h13]; exact rsE_rax _ _ _ (by omega) hp

omit [CodeEnv] in
theorem rsE_ldaddr (x : BitVec 64) (b j p : Nat) (hp : p < 2) (hb : b + j < 2 ^ 32) :
    x + BitVec.ofNat 64 (0x4c284 + 4 * (b + 1) - 2 * p) + BitVec.ofNat 64 j * BitVec.ofNat 64 4 + 0#64
      = x + 0x4c284#64 + BitVec.ofNat 64 (2 * (2 * (b + j + 1) - p)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]; omega

omit [CodeEnv] in
theorem rsE_staddr (x : BitVec 64) (b j : Nat) (hb : b + j < 2 ^ 32) :
    x + BitVec.ofNat 64 (0x4c252 + 2 * (b + 1)) + BitVec.ofNat 64 j * BitVec.ofNat 64 2 + 0#64
      = x + 0x4c252#64 + BitVec.ofNat 64 (2 * (b + j + 1)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]; omega

omit [CodeEnv] in
theorem rsE_val (u : Nat) (h : u < 65536) :
    ((BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofInt 16 (u : Int))))).toInt
      % 65536).toNat = u := by
  rw [rsE_toInt16]
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt]
  omega

omit [CodeEnv] in
theorem rsE_inc (j : Nat) (h : j < 2 ^ 32) : BitVec.ofNat 64 j + 1 = BitVec.ofNat 64 (j + 1) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (1 : BitVec 64).toNat = 1 := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h1]; omega

omit [CodeEnv] in
theorem rsE_ne (n b j : Nat) (h : b + j < n) (hn : n < 2 ^ 32) :
    (BitVec.ofNat 64 (n - b) = BitVec.ofNat 64 j + 1) ↔ b + j + 1 = n := by
  rw [rsE_inc j (by omega)]
  constructor
  · intro e; have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
  · intro e; congr 1; omega

omit [CodeEnv] in
theorem rsE_var (n b j : Nat) (h : b + j + 1 < n) (hn : n < 2 ^ 32) :
    ((BitVec.ofNat 64 (n - b)).toNat - (BitVec.ofNat 64 (j + 1)).toNat) % 2 ^ 64
      < ((BitVec.ofNat 64 (n - b)).toNat - (BitVec.ofNat 64 j).toNat) % 2 ^ 64 := by
  simp only [BitVec.toNat_ofNat]; omega

set_option maxRecDepth 100000 in
/-- The scalar copy loop: `f_tablelow[m+1] = f_tablehigh[2(m+1) - p]`. -/
theorem blk_L2b20 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2b20" ⟨"sbr_reset.L2b20", B.L2b20, some "sbr_reset.L2b30"⟩ := by
  info_off
  measure_hb "L2b20"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hC, ⟨hrsp, hrbp⟩, st, fr, nm, k0, hMa, hsp, hfm, hF, h40,
      ⟨hk2, hf64, hbr, h30, h38, m, hx, h14, h15, h10, hcx, b, j, rfl, hlt, hsi, hr8, hdx, hax⟩, hm⟩ := T.L2b20.mp hs
    clear hs
    obtain ⟨hxo, hnm, -, -⟩ := master_bounds hMa
    have hlt' : b + j < (nm - xoOf a + 1) / 2 := hlt
    have hp : (nm - xoOf a) % 2 < 2 := Nat.mod_lt _ (by omega)
    have hfh : st.x.ftHigh.length = 98 := by rw [hx]; simp [derived1]
    have hi : 2 * (b + j + 1) - (nm - xoOf a) % 2 < 49 := by omega
    have hld := ftH_load hm hfh hi (addr := s₀.regs.get64 .rax + s₀.regs.get64 .rsi * BitVec.ofNat 64 4 + 0#64)
      (by rw [hax, hsi]; exact rsE_ldaddr _ _ _ _ hp (by omega))
    have hhi : u16 st.x.ftHigh (2 * (b + j + 1) - (nm - xoOf a) % 2)
        = fOf st (xoOf a + (2 * (b + j + 1) - (dD1 a k0 nm (fOf st)).n1 % 2)) % 65536 := by
      rw [hx]
      refine (u16_mk16 (f := fun i => if i ≤ nm - xoOf a then fOf st (xoOf a + i)
        else u16 (x0D a k0).ftHigh i) hi).trans ?_
      rw [if_pos (by omega)]; rfl
    have hfl : st.x.ftLow.length = 50 := by rw [hx]; simp [LowM]
    have hfl0 : st.x.ftLow = LowM (dD1 a k0 nm (fOf st)) (xoOf a) (fOf st) (b + j) := by rw [hx]
    have hstore : ∀ v : Int, (v % 65536).toNat
        = fOf st (xoOf a + (2 * (b + j + 1) - (dD1 a k0 nm (fOf st)).n1 % 2)) % 65536 →
        s₀.dmem.storeInt (s₀.regs.get64 .rdx + s₀.regs.get64 .rsi * BitVec.ofNat 64 2 + 0#64) 2 v
          =⋆ Mm k e a ra t₀ ({ st with x := { st.x with ftLow := LowM (dD1 a k0 nm (fOf st)) (xoOf a) (fOf st) (b + j + 1) } } : St) fr := by
      intro v hv
      have h := region_store (o := 2 * (b + j + 1)) (n := 2)
        (addr := s₀.regs.get64 .rdx + s₀.regs.get64 .rsi * BitVec.ofNat 64 2 + 0#64) (focus (Mm_ftLow ..) hm)
        (by rw [hdx, hsi]; exact rsE_staddr _ _ _ (by omega)) (by rw [hfl]; omega) (by rw [hfl]; omega) v
      rw [hfl0, rsE_LowM_step _ _ _ (by omega) v hv, Mm_upd_ftLow] at h
      exact h
    have hlds : (s₀.dmem.loadInt (s₀.regs.get64 .rdx + s₀.regs.get64 .rsi * 2#64 + 0#64) 2).isSome = true := by
      rw [region_load (o := 2 * (b + j + 1)) (n := 2) (focus (Mm_ftLow ..) hm)
        (by rw [hdx, hsi]; exact rsE_staddr _ _ _ (by omega)) (by rw [hfl]; omega) (by rw [hfl]; omega)]; rfl
    have hx' : ({ st with x := { st.x with ftLow := LowM (dD1 a k0 nm (fOf st)) (xoOf a) (fOf st) (b + j + 1) } } : St).x
        = dLw a k0 nm (fOf st) (b + j + 1) := by
      show ({ st.x with ftLow := _ } : Args) = _
      rw [hx]
    have P30 : PLift (frSlot64 fr 0x30 = arg1 t₀) := ⟨h30⟩
    have Px := PLift.up hx'
    have Pld := PLift.up hld
    have Pst := PLift.up hstore
    have Phi := PLift.up hhi
    clear h30 hx hx' hm hld hstore hhi hfl0
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    have hne := rsE_ne _ _ _ hlt' (by omega)
    have hstep : ¬ (b + j + 1 = (nm - xoOf a + 1) / 2) → b + j + 1 < (nm - xoOf a + 1) / 2 := by
      omega
    have hdone : b + j + 1 = (nm - xoOf a + 1) / 2 →
        dLw a k0 nm (fOf st) (b + j + 1) = dD2 a k0 nm (fOf st) := by
      intro h; rw [h]; rfl
    have hW4 : BitVec.ofNat 64 Width.W32.bytes = 4#64 := rfl
    have hW2 : BitVec.ofNat 64 Width.W16.bytes = 2#64 := rfl
    simp only [B.L2b20]
    vcgen
    all_goals try subst_vars
    all_goals simp only [AddrIndex.offset64, Int64.toBitVec_ofNat_norm, BitVec.reduceSetWidth, hW4, hW2,
      Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] at *
    case vc1 => rw [Pld.down]; rfl
    case vc2 => exact hlds
    all_goals rename_i v hl hc
    all_goals have hl := hl.symm.trans Pld.down
    all_goals simp only [Option.some.injEq] at hl
    all_goals subst hl
    all_goals simp only [Kraken.Examples.Sbr.Reset.cc_nz_sub, hr8, hsi, hne, Bool.not_eq_true',
      Bool.not_eq_false', decide_eq_false_iff_not, decide_eq_true_eq] at hc
    all_goals have hv := (rsE_val _ (rsE_u16_lt _ _)).trans Phi.down
    case vc3 =>
      exact Or.inl (Table.ofLabels_at ⟨S.L2b20, T.L2b20.mpr ⟨hC, ⟨by rsE_rs; exact hrsp,
        by rsE_rs; exact hrbp⟩, { st with x := { st.x with ftLow := LowM (dD1 a k0 nm (fOf st)) (xoOf a) (fOf st) (b + j + 1) } }, fr, nm, k0, hMa, hsp, hfm, hF, h40, ⟨hk2, hf64, hbr, P30.down, h38, b + j + 1,
        Px.down, by rsE_rs; exact h14, by rsE_rs; exact h15,
        by rsE_rs; exact h10, by rsE_rs; exact hcx, b, j + 1, by omega, hstep hc,
        by rsE_rs; rw [hsi]; exact rsE_inc j (by omega), by rsE_rs; exact hr8, by rsE_rs; exact hdx,
        by rsE_rs; exact hax⟩, Pst.down _ hv⟩, by
          left; simp only [lex_var]
          refine Kraken.lex_cons_lt_cons (by lex_len) ?_
          refine Kraken.lex_cons_lt_of_lt (by lex_len) ?_
          dsimp only
          simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hr8, hsi, rsE_inc j (by omega)]
          exact rsE_var _ _ _ (hstep hc) (by omega)⟩)
    case vc4 =>
      refine ⟨T.L2b30.mpr ⟨hC, ⟨by rsE_rs; exact hrsp, by rsE_rs; exact hrbp⟩,
        { st with x := { st.x with ftLow := LowM (dD1 a k0 nm (fOf st)) (xoOf a) (fOf st) (b + j + 1) } }, fr, nm,
        k0, hMa, hsp, hfm, hF, h40, ⟨hk2, hf64, hbr, P30.down, h38, Px.down.trans (hdone hc),
        by rsE_rs; exact h14, by rsE_rs; exact h15,
        by rsE_rs; exact h10, by rsE_rs; exact hcx⟩, Pst.down _ hv⟩, by var_step⟩

end Kraken.Examples.Sbr.Reset
