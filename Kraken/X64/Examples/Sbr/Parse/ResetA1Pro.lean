import Kraken.InfoOff
import Kraken.X64.Examples.Sbr.Parse.ResetA1Lib

/-!
# `sbr_reset`: the prologue (shard A1)

`start`, `L1086`, `L108a`: the five pushes, `rbp`, the locals.
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
theorem a1_sub8 (r : BitVec 64) : r - 8#64 - 8#64 = r - 16#64 := by bv_omega

omit [CodeEnv] in
/-- The entry reservation with the two push slots carved off its top. -/
theorem a1_pro_split {m : Mem 64} {r : BitVec 64} {ra : Int64} {X : Mem 64 → Prop} {k : Nat}
    (hk : k ≤ 2 ^ 32) (h : m =⋆ RetCell ra r ⋆ (Reserve (1408 + 1104 + k) r ⋆ X)) :
    m =⋆ 8 ?@ (r - 8#64) ⋆ (8 ?@ (r - 16#64) ⋆ (Reserve (1408 + 1104 + k - 16) (r - 16#64)
      ⋆ (RetCell ra r ⋆ X))) := by
  have hr : 1408 + 1104 + k ≤ r.toNat := by
    obtain ⟨_, _, _, _, _, _, _, _, _, h1, _⟩ := h; exact h1.1
  have hr8 : 8 ≤ (r - BitVec.ofNat 64 8).toNat := by bv_omega
  have e : 1408 + 1104 + k = 8 + (8 + (1408 + 1104 + k - 16)) := by omega
  rw [e, Reserve_split 8 _ r (by omega), Reserve_split 8 _ _ hr8] at h
  rw [show r - BitVec.ofNat 64 8 - BitVec.ofNat 64 8 = r - 16#64 by bv_omega] at h
  have eq : (RetCell ra r ⋆ ((8 ?@ (r - BitVec.ofNat 64 8) ⋆ (8 ?@ (r - 16#64)
      ⋆ Reserve (1408 + 1104 + k - 16) (r - 16#64))) ⋆ X))
      = 8 ?@ (r - 8#64) ⋆ (8 ?@ (r - 16#64) ⋆ (Reserve (1408 + 1104 + k - 16) (r - 16#64)
        ⋆ (RetCell ra r ⋆ X))) := by ac_rfl
  rw [eq] at h
  exact h

omit [CodeEnv] in
/-- The two pushes fill the carved slots. -/
theorem a1_pro_push2 {m : Mem 64} {r : BitVec 64} {R : Mem 64 → Prop}
    (h : m =⋆ 8 ?@ (r - 8#64) ⋆ (8 ?@ (r - 16#64) ⋆ R)) (v w : BitVec 64) :
    ((m.storeInt (r - 8#64) 8 v.toInt).storeInt (r - 16#64) 8 w.toInt)
      =⋆ (c8 (r - 0x8#64) v ⋆ c8 (r - 0x10#64) w) ⋆ R := by
  have h1 := Block.storeInt_val h (Split.here _ _) v.toInt
  have h2 := Block.storeInt_val h1 (Split.right (Split.here _ _) _) w.toInt
  have eq : (c8 (r - 0x8#64) v ⋆ c8 (r - 0x10#64) w) ⋆ R
      = (Int.toBytes 8 w.toInt =@ (r - 16#64)) ⋆ ((Int.toBytes 8 v.toInt =@ (r - 8#64)) ⋆ R) := by
    simp only [c8]; ac_rfl
  rw [eq]; exact h2

theorem blk_start (k : Nat) (hk : k ≤ 2 ^ 32) (e : REnv) (a : RArgs) (ra : Int64)
    (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset" ⟨"sbr_reset", B.start, some "sbr_reset.L1086"⟩ := by
  info_off
  measure_hb "start"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨rfl, hm, hC, hBO⟩ := T.start.mp hs
    clear hs
    have hm2 := a1_pro_split hk hm
    have ld1 := Block.loadInt_isSome_at hm2 (Split.here _ _)
    have ld2 := fun v : Int => Block.loadInt_isSome_at (Block.storeInt_val hm2 (Split.here _ _) v)
      (Split.right (Split.here _ _) _)
    have hP := a1_pro_push2 hm2
    simp only [B.start]
    vcgen
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, Width.bytes, a1_sub8]
    · exact ld1
    · exact ld2 _
    · have hCI := ResetCI.of hC (by
        have := CallPre.le hm; unfold resetNeed at this; unfold resetStkMin; omega)
      refine ⟨T.L1086.mpr ⟨hCI, hBO, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by var_step⟩
      all_goals try (simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, Nat.reduceMul]; done)
      all_goals try rfl
      simp only [ProM, resetNeed, Nat.reduceMul]
      exact hP _ _

omit [CodeEnv] in
/-- Two push slots off the top of a reservation. -/
theorem a1_res_carve (d : Nat) (r : BitVec 64) (hd : 16 ≤ d) (hw : d ≤ r.toNat) :
    Reserve d r = 8 ?@ (r - 8#64) ⋆ (8 ?@ (r - 16#64) ⋆ Reserve (d - 16) (r - 16#64)) := by
  have e : d = 8 + (8 + (d - 16)) := by omega
  have hr8 : 8 ≤ (r - BitVec.ofNat 64 8).toNat := by bv_omega
  conv => lhs; rw [e]
  rw [Reserve_split 8 _ r (by omega), Reserve_split 8 _ _ hr8]
  rw [show r - BitVec.ofNat 64 8 - BitVec.ofNat 64 8 = r - 16#64 by bv_omega]

omit [CodeEnv] in
theorem a1_pro_push2' {m : Mem 64} {r : BitVec 64} {A R : Mem 64 → Prop} {d : Nat}
    (hd : 16 ≤ d) (h : m =⋆ A ⋆ (Reserve d r ⋆ R)) (v w : BitVec 64) :
    ((m.storeInt (r - 8#64) 8 v.toInt).storeInt (r - 16#64) 8 w.toInt)
      =⋆ A ⋆ ((c8 (r - 0x8#64) v ⋆ c8 (r - 0x10#64) w) ⋆ (Reserve (d - 16) (r - 16#64) ⋆ R)) := by
  rw [a1_res_carve d r hd (res_le_mid h)] at h
  have eq : A ⋆ ((8 ?@ (r - 8#64) ⋆ (8 ?@ (r - 16#64) ⋆ Reserve (d - 16) (r - 16#64))) ⋆ R)
      = 8 ?@ (r - 8#64) ⋆ (8 ?@ (r - 16#64) ⋆ (A ⋆ (Reserve (d - 16) (r - 16#64) ⋆ R))) := by
    ac_rfl
  rw [eq] at h
  have h2 := a1_pro_push2 h v w
  have eq2 : (c8 (r - 0x8#64) v ⋆ c8 (r - 0x10#64) w) ⋆ (A ⋆ (Reserve (d - 16) (r - 16#64) ⋆ R))
      = A ⋆ ((c8 (r - 0x8#64) v ⋆ c8 (r - 0x10#64) w) ⋆ (Reserve (d - 16) (r - 16#64) ⋆ R)) := by
    ac_rfl
  rw [eq2] at h2; exact h2

omit [CodeEnv] in
theorem a1_pro_ld {m : Mem 64} {r : BitVec 64} {A R : Mem 64 → Prop} {d : Nat}
    (hd : 16 ≤ d) (h : m =⋆ A ⋆ (Reserve d r ⋆ R)) :
    (m.loadInt (r - 8#64) 8).isSome = true
      ∧ ∀ v : Int, ((m.storeInt (r - 8#64) 8 v).loadInt (r - 16#64) 8).isSome = true := by
  rw [a1_res_carve d r hd (res_le_mid h)] at h
  have eq : A ⋆ ((8 ?@ (r - 8#64) ⋆ (8 ?@ (r - 16#64) ⋆ Reserve (d - 16) (r - 16#64))) ⋆ R)
      = 8 ?@ (r - 8#64) ⋆ (8 ?@ (r - 16#64) ⋆ (A ⋆ (Reserve (d - 16) (r - 16#64) ⋆ R))) := by
    ac_rfl
  rw [eq] at h
  exact ⟨Block.loadInt_isSome_at h (Split.here _ _), fun v =>
    Block.loadInt_isSome_at (Block.storeInt_val h (Split.here _ _) v) (Split.right (Split.here _ _) _)⟩

omit [CodeEnv] in
theorem a1_pro4_shape {A B C D E : Mem 64 → Prop} {m : Mem 64}
    (h : m =⋆ (A ⋆ B) ⋆ ((C ⋆ D) ⋆ E)) : m =⋆ (A ⋆ (B ⋆ (C ⋆ D))) ⋆ E := by
  have eq : (A ⋆ B) ⋆ ((C ⋆ D) ⋆ E) = (A ⋆ (B ⋆ (C ⋆ D))) ⋆ E := by ac_rfl
  rw [← eq]; exact h

theorem blk_L1086 (k : Nat) (hk : k ≤ 2 ^ 32) (e : REnv) (a : RArgs) (ra : Int64)
    (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1086" ⟨"sbr_reset.L1086", B.L1086, some "sbr_reset.L108a"⟩ := by
  info_off
  measure_hb "L1086"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hC, hBO, hrsp, hrbp, hdi, hsi, hbx, h12, h13, h14, hm⟩ := T.L1086.mp hs
    clear hs
    simp only [ProM] at hm
    have hN : resetNeed k = 0x580 + 0x450 + k := rfl
    have hP := a1_pro_push2' (by omega) hm
    have ld := a1_pro_ld (by omega) hm
    have hQ := hP (t₀.regs.get64 .r14) (t₀.regs.get64 .r13)
    simp only [Nat.reduceMul] at hQ
    rw [show t₀.regs.get64 .rsp - 16#64 - 8#64 = t₀.regs.get64 .rsp - 0x18#64 by bv_omega,
      show t₀.regs.get64 .rsp - 16#64 - 16#64 = t₀.regs.get64 .rsp - 0x20#64 by bv_omega,
      show resetNeed k - 16 - 16 = resetNeed k - 32 by omega] at hQ
    simp only [B.L1086]
    vcgen
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, Width.bytes, a1_sub8, hrsp]
    · exact ld.1
    · exact ld.2 _
    · refine ⟨T.L108a.mpr ⟨hC, hBO, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by var_step⟩
      all_goals try (simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, Nat.reduceMul, hrbp,
        hdi, hsi, hbx, h12, h13, h14]; done)
      · simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, Nat.reduceMul]; bv_omega
      · simp only [ProM, Nat.reduceMul, h13, h14]
        rw [show t₀.regs.get64 .rsp - 16#64 - 8#64 = t₀.regs.get64 .rsp - 0x18#64 by bv_omega,
          show t₀.regs.get64 .rsp - 16#64 - 16#64 = t₀.regs.get64 .rsp - 0x20#64 by bv_omega]
        with_reducible exact a1_pro4_shape hQ

/-! ## `L108a`: the last two pushes, the locals, and the entry into `Mm` -/

/-- Finds a `Split` path to a block (by reducible unification). -/
syntax "a1_split" : tactic
macro_rules
  | `(tactic| a1_split) => `(tactic| first
      | with_reducible exact Split.here _ _
      | with_reducible exact Split.block _ _
      | with_reducible exact Split.val _ _
      | (with_reducible apply Split.right; a1_split)
      | (with_reducible apply Split.left; a1_split))

omit [CodeEnv] in
omit [CodeEnv] in
theorem a1_pick {m : Mem 64} {P R H : Mem 64 → Prop} (hs : Split P R H) (h : m =⋆ P ⋆ R) :
    m =⋆ H := by
  unfold Split at hs; subst hs; exact h

omit [CodeEnv] in
theorem a1_frame {m : Mem 64} {P A B : Mem 64 → Prop} (h : m =⋆ P ⋆ A)
    (f : ∀ m' : Mem 64, (m' =⋆ A) → (m' =⋆ B)) : m =⋆ P ⋆ B := by
  obtain ⟨m1, m2, hu, hi, hP, hA⟩ := h
  exact ⟨m1, m2, hu, hi, hP, f _ hA⟩

omit [CodeEnv] in
theorem a1_open {m : Mem 64} {H R : Mem 64 → Prop} {a : BitVec 64} {n : Nat}
    (h : m =⋆ H) (hs : Split (n ?@ a) R H) :
    ∃ bs : List UInt8, bs.length = n ∧ m =⋆ bs =@ a ⋆ R := by
  unfold Split at hs; subst hs
  obtain ⟨-, bs, hl, h⟩ := Block.sep_elim h
  exact ⟨bs, hl, h⟩

omit [CodeEnv] in
theorem a1_bytes4 (bs : List UInt8) (h : bs.length = 4) :
    Int.toBytes 4 (BitVec.ofInt 32 (Int.ofBytes bs)).toInt = bs := by
  rw [BitVec.toInt_ofInt]
  have := Int.toBytes_bmod_ofBytes 4 bs h
  simpa using this

omit [CodeEnv] in
theorem a1_val4 (bs : List UInt8) (h : bs.length = 4) (p : BitVec 64) :
    bs =@ p = cell4 p (BitVec.ofInt 32 (Int.ofBytes bs)) := by
  simp only [cell4]; rw [a1_bytes4 bs h]

omit [CodeEnv] in
theorem a1_val8 (bs : List UInt8) (h : bs.length = 8) (p : BitVec 64) :
    bs =@ p = cell4 p (BitVec.ofInt 32 (Int.ofBytes (bs.take 4)))
      ⋆ cell4 (p + 0x4#64) (BitVec.ofInt 32 (Int.ofBytes (bs.drop 4))) := by
  simp only [cell4]
  rw [a1_bytes4 _ (by simp [h]), a1_bytes4 _ (by simp [h])]
  simp only [Val.eq]
  have e := At_append_sep (bs.take 4) (bs.drop 4) p (by simp [h])
  rw [List.take_append_drop] at e
  rw [e]; simp [h]

omit [CodeEnv] in
theorem a1_conv {m : Mem 64} {P Q : Mem 64 → Prop} (e : P = Q) (h : m =⋆ P) : m =⋆ Q := e ▸ h

/-- The prologue's footprint, as `Mm` at some values. -/
theorem a1_entry {k : Nat} (hk : k ≤ 2 ^ 32) {e : REnv} {a : RArgs} {ra : Int64}
    {t₀ : MachineData} {m : Mem 64}
    (h : m =⋆ Saved t₀ ⋆ (Reserve (resetNeed k - 48) (t₀.regs.get64 .rsp - 48#64)
      ⋆ (RetCell ra (t₀.regs.get64 .rsp) ⋆ (RF e a t₀ ⋆ a.x.R)))) :
    ∃ (st : St) (fr : List UInt8), st.x = a.x ∧ st.sp = a.sp ∧ st.fm.length = 98 ∧ FrOk fr
      ∧ (m =⋆ Mm k e a ra t₀ st fr) := by
  have hN : resetNeed k = 0x580 + 0x450 + k := rfl
  have hT : tlimNeed k = 0x450 + k := rfl
  have hw := res_le_mid h
  have hw' : 0x548 ≤ (t₀.regs.get64 .rsp - 48#64).toNat := by omega
  rw [show resetNeed k - 48 = 0x548 + (8 + tlimNeed k) by omega,
    Reserve_split 0x548 _ _ hw',
    show t₀.regs.get64 .rsp - 48#64 - BitVec.ofNat 64 0x548 = t₀.regs.get64 .rsp - 0x578#64 by
      bv_omega] at h
  simp only [RF, ScR, TabR, DR] at h
  obtain ⟨fr, hfr, h⟩ := a1_open (n := 0x548) h (by a1_split)
  obtain ⟨b8, hb8, h⟩ := a1_open (n := 8) h (by a1_split)
  obtain ⟨b4, hb4, h⟩ := a1_open (n := 4) (a := arg1 t₀ + 0x68#64) h (by a1_split)
  obtain ⟨fm, hfm, h⟩ := a1_open (n := 98) h (by a1_split)
  rw [a1_val8 b8 hb8, a1_val4 b4 hb4,
    show arg1 t₀ + 0x44#64 + 0x4#64 = arg1 t₀ + 0x48#64 by bv_omega] at h
  refine ⟨St.mk a.x a.sp (BitVec.ofInt 32 (Int.ofBytes (b8.take 4)))
    (BitVec.ofInt 32 (Int.ofBytes (b8.drop 4))) (BitVec.ofInt 32 (Int.ofBytes b4)) fm,
    fr, rfl, rfl, hfm, hfr, ?_⟩
  simp only [Std.ExtHashMap.sep_assoc, Std.ExtHashMap.sep_emp] at h
  simp only [Mm, Std.ExtHashMap.sep_assoc]
  refine a1_pick (by a1_split) (a1_frame h fun m h => ?_)
  refine a1_pick (by a1_split) (a1_frame h fun m h => ?_)
  refine a1_pick (by a1_split) (a1_frame h fun m h => ?_)
  refine a1_pick (by a1_split) (a1_frame h fun m h => ?_)
  refine a1_pick (by a1_split) (a1_frame h fun m h => ?_)
  refine a1_pick (by a1_split) (a1_frame h fun m h => ?_)
  exact h

omit [CodeEnv] in
theorem a1_saved_shape {t₀ : MachineData} {m : Mem 64} {d : Nat} {G : Mem 64 → Prop}
    (hd : 48 ≤ d)
    (h : m =⋆ (c8 (t₀.regs.get64 .rsp - 0x8#64) (t₀.regs.get64 .rbp)
      ⋆ (c8 (t₀.regs.get64 .rsp - 0x10#64) (t₀.regs.get64 .r15)
      ⋆ (c8 (t₀.regs.get64 .rsp - 0x18#64) (t₀.regs.get64 .r14)
      ⋆ c8 (t₀.regs.get64 .rsp - 0x20#64) (t₀.regs.get64 .r13))))
      ⋆ ((c8 (t₀.regs.get64 .rsp - 32#64 - 0x8#64) (t₀.regs.get64 .r12)
        ⋆ c8 (t₀.regs.get64 .rsp - 32#64 - 0x10#64) (t₀.regs.get64 .rbx))
      ⋆ (Reserve (d - 32 - 16) (t₀.regs.get64 .rsp - 32#64 - 16#64) ⋆ G))) :
    m =⋆ Saved t₀ ⋆ (Reserve (d - 48) (t₀.regs.get64 .rsp - 48#64) ⋆ G) := by
  rw [show t₀.regs.get64 .rsp - 32#64 - 0x8#64 = t₀.regs.get64 .rsp - 0x28#64 by bv_omega,
    show t₀.regs.get64 .rsp - 32#64 - 0x10#64 = t₀.regs.get64 .rsp - 0x30#64 by bv_omega,
    show d - 32 - 16 = d - 48 by omega] at h
  simp only [Saved]
  exact a1_conv (by ac_rfl) h

theorem a1_sr_load {k : Nat} {e : REnv} {a : RArgs} {ra : Int64} {t₀ : MachineData}
    {m : Mem 64} {st : St} {fr : List UInt8} (h : m =⋆ Mm k e a ra t₀ st fr) :
    m.loadInt (t₀.regs.get64 .rsi) 4 = some (Int.ofBytes (Int.toBytes 4 st.x.sampleRate.toInt)) := by
  rw [Mm_sr] at h
  exact loadInt_sep _ _ 4 _ m h (Int.toBytes_length 4 _) (by omega)

omit [CodeEnv] in
theorem a1_ofInt4 (v : BitVec 32) : BitVec.ofInt 32 (Int.ofBytes (Int.toBytes 4 v.toInt)) = v :=
  BitVec.ofInt_ofBytes_toBytes 32 4 rfl v

omit [CodeEnv] in
theorem a1_addi0 (x : BitVec 64) : x + Int64.toBitVec 0 = x := BitVec.add_zero x

set_option hygiene false in
/-- The `rateRow` load in `L108a`: the loaded value is the rate. -/
macro "a1_ld " hv:ident : tactic => `(tactic| (
  simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, Width.bytes, a1_sub8, hrsp, hsi,
    h12, hbx, a1_addi0] at $hv:ident
  rw [hL] at $hv:ident
  obtain rfl := Option.some.inj $hv:ident))

theorem a1_rd_of {k : Nat} {e : REnv} {a : RArgs} {ra : Int64} {t₀ s : MachineData}
    (hC : ResetCI a t₀) (hBO : BandsOK e.lg e.pw)
    (hr : s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x578#64)
    (hb : s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64)
    (h12 : s.regs.get64 .r12 = arg1 t₀) (h15 : s.regs.get64 .r15 = arg0 t₀)
    (hcx : s.regs.get64 .rcx = a.x.sampleRate.setWidth 64) {st : St} {fr : List UInt8}
    (hx : st.x = a.x) (hsp : st.sp = a.sp) (hfm : st.fm.length = 98) (hfr : FrOk fr)
    (hm : s.dmem =⋆ Mm k e a ra t₀ st fr) : RD k e a ra t₀ s :=
  ⟨⟨hC, hBO, ⟨hr, hb⟩, st, fr, hx, hsp, hfm, hfr, trivial, hm⟩, h12, h15, hcx⟩

set_option hygiene false in
/-- The `RD` side goals of `a1_rd_of` at an exit of `L108a`. -/
macro "a1_rd_close" : tactic => `(tactic| (
  · simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, Int64.toBitVec_ofNat,
      BitVec.reduceSetWidth] <;> bv_omega
  · simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrbp]
  · simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hsi] <;> rfl
  · simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hdi] <;> rfl
  · simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
  · simp only [h12, hbx]; exact hMm))

theorem blk_L108a (k : Nat) (hk : k ≤ 2 ^ 32) (e : REnv) (a : RArgs) (ra : Int64)
    (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L108a" ⟨"sbr_reset.L108a", B.L108a, some "sbr_reset.L10b8"⟩ := by
  info_off
  measure_hb "L108a"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hC, hBO, hrsp, hrbp, hdi, hsi, hbx, h12, h13, h14, hm⟩ := T.L108a.mp hs
    clear hs
    simp only [ProM, Nat.reduceMul] at hm hrsp
    have hN : resetNeed k = 0x580 + 0x450 + k := rfl
    have hP := a1_pro_push2' (by omega) hm
    have ld := a1_pro_ld (by omega) hm
    obtain ⟨st, fr, hx, hsp, hfm, hfr, hMm⟩ :=
      a1_entry hk (a1_saved_shape (by omega) (hP (t₀.regs.get64 .r12) (t₀.regs.get64 .rbx)))
    have hL := a1_sr_load hMm
    rw [hx] at hL
    simp only [B.L108a]
    vcgen
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, Width.bytes, a1_sub8, hrsp]
    · exact ld.1
    · exact ld.2 _
    · simp only [hsi, h12, hbx, a1_addi0, hL]; rfl
    all_goals clear hm hP ld
    · rename_i v hv g1
      a1_ld hv
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, Width.bytes, a1_sub8, a1_ofInt4] at g1 ⊢
      disp_simp
      refine Or.inl (Table.ofLabels_at ⟨S.L10d9, T.L10d9.mpr
        ⟨a1_rd_of hC hBO ?_ ?_ ?_ ?_ ?_ hx hsp hfm hfr ?_, ?_⟩, by edge_step⟩)
      a1_rd_close
      simp only [srI]; omega
    · rename_i v hv g1 g2
      a1_ld hv
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, Width.bytes, a1_sub8, a1_ofInt4] at g1 g2 ⊢
      disp_simp
      refine Or.inl (Table.ofLabels_at ⟨S.L10fe, T.L10fe.mpr
        ⟨a1_rd_of hC hBO ?_ ?_ ?_ ?_ ?_ hx hsp hfm hfr ?_, ?_, ?_⟩, by edge_step⟩)
      a1_rd_close
      all_goals (simp only [srI]; omega)
    · rename_i v hv g1 g2 g3
      a1_ld hv
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, Width.bytes, a1_sub8, a1_ofInt4] at g1 g2 g3 ⊢
      disp_simp
      refine Or.inl (Table.ofLabels_at ⟨S.L17fc, T.L17fc.mpr
        ⟨a1_rd_of hC hBO ?_ ?_ ?_ ?_ ?_ hx hsp hfm hfr ?_, ?_⟩, by edge_step⟩)
      a1_rd_close
      simp [rateRow, srI, toInt_of_eq32 (by assumption) (by decide)]
    · rename_i v hv g1 g2 g3
      a1_ld hv
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, Width.bytes, a1_sub8, a1_ofInt4] at g1 g2 g3 ⊢
      disp_simp
      refine ⟨T.L10b8.mpr ⟨a1_rd_of hC hBO ?_ ?_ ?_ ?_ ?_ hx hsp hfm hfr ?_, ?_, ?_⟩, by var_step⟩
      a1_rd_close
      · simp only [srI]; omega
      · exact toInt_ne_of_ne32 g3 (by decide)

end Kraken.Examples.Sbr.Reset
