import Kraken.X64.Examples.Sbr.Parse.UsacBlk20
open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse
set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true
/-! # `ff_aac_sbr_decode_usac_data`: the default header's start

The old `bs_limiter_bands` into `eax`, the old `spectrum_params` bytes into the locals
(`LocI` becomes `LocT`). -/
namespace Kraken.Examples.Sbr.Usac
variable [CodeEnv]

/-- The locals with the old bytes 4, 5 stored (`-0x30(%rbp)`). -/
abbrev LocM (r : BitVec 64) (iv : BitVec 32) (l2 : List UInt8) : Mem 64 → Prop :=
  12 ?@ (r - 0x48#64) ⋆ (4 ?@ (r - 0x3c#64) ⋆ (l2 =@ (r - 0x38#64) ⋆ (2 ?@ (r - 0x36#64)
    ⋆ cell4 (r - 0x34#64) iv)))

/-- Storing the old bytes 4, 5. -/
theorem um_storeL2 {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Sg : Mem 64 → Prop} {st : USt} {iv : BitVec 32}
    (h : m =⋆ UM k A ra t₀ (LocI (t₀.regs.get64 .rsp) iv) Sg st)
    (a : BitVec 64) (ha : a = t₀.regs.get64 .rsp - 0x38#64) (v : Int) :
    m.storeInt a 2 v =⋆ UM k A ra t₀ (LocM (t₀.regs.get64 .rsp) iv (Int.toBytes 2 v)) Sg st := by
  obtain ⟨R, hs, hs'⟩ : ∃ R, Split (2 ?@ (t₀.regs.get64 .rsp - 0x38#64)) R
        (UM k A ra t₀ (LocI (t₀.regs.get64 .rsp) iv) Sg st)
      ∧ Split (Int.toBytes 2 v =@ (t₀.regs.get64 .rsp - 0x38#64)) R
        (UM k A ra t₀ (LocM (t₀.regs.get64 .rsp) iv (Int.toBytes 2 v)) Sg st) := by
    simp only [UM, LocI, LocM]
    exact ⟨_, Split.right (Split.right (Split.right (Split.left (Split.right (Split.right
        (Split.here _ _) _) _) _) _) _) _,
      Split.right (Split.right (Split.right (Split.left (Split.right (Split.right
        (Split.here _ _) _) _) _) _) _) _⟩
  rw [hs', ha]
  exact Block.storeInt_val h hs v

/-- Storing the old bytes 0..3. -/
theorem um_storeL4 {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Sg : Mem 64 → Prop} {st : USt} {iv : BitVec 32} {l2 : List UInt8}
    (h : m =⋆ UM k A ra t₀ (LocM (t₀.regs.get64 .rsp) iv l2) Sg st)
    (a : BitVec 64) (ha : a = t₀.regs.get64 .rsp - 0x3c#64) (v : Int) :
    m.storeInt a 4 v =⋆ UM k A ra t₀ (LocT (t₀.regs.get64 .rsp) iv (Int.toBytes 4 v) l2) Sg st := by
  obtain ⟨R, hs, hs'⟩ : ∃ R, Split (4 ?@ (t₀.regs.get64 .rsp - 0x3c#64)) R
        (UM k A ra t₀ (LocM (t₀.regs.get64 .rsp) iv l2) Sg st)
      ∧ Split (Int.toBytes 4 v =@ (t₀.regs.get64 .rsp - 0x3c#64)) R
        (UM k A ra t₀ (LocT (t₀.regs.get64 .rsp) iv (Int.toBytes 4 v) l2) Sg st) := by
    simp only [UM, LocM, LocT]
    exact ⟨_, Split.right (Split.right (Split.right (Split.left (Split.right
        (Split.here _ _) _) _) _) _) _,
      Split.right (Split.right (Split.right (Split.left (Split.right
        (Split.here _ _) _) _) _) _) _⟩
  rw [hs', ha]
  exact Block.storeInt_val h hs v

/-- The raw locals are there. -/
theorem um_loadL2 {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Sg : Mem 64 → Prop} {st : USt} {iv : BitVec 32}
    (h : m =⋆ UM k A ra t₀ (LocI (t₀.regs.get64 .rsp) iv) Sg st)
    (a : BitVec 64) (ha : a = t₀.regs.get64 .rsp - 0x38#64) :
    (m.loadInt a 2).isSome = true := by
  simp only [UM, LocI] at h
  rw [ha]
  exact Block.loadInt_isSome_split h (Split.right (Split.right (Split.right (Split.left
    (Split.right (Split.right (Split.here _ _) _) _) _) _) _) _) (by simp)

theorem um_loadL4 {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Sg : Mem 64 → Prop} {st : USt} {iv : BitVec 32} {l2 : List UInt8}
    (h : m =⋆ UM k A ra t₀ (LocM (t₀.regs.get64 .rsp) iv l2) Sg st)
    (a : BitVec 64) (ha : a = t₀.regs.get64 .rsp - 0x3c#64) :
    (m.loadInt a 4).isSome = true := by
  simp only [UM, LocM] at h
  rw [ha]
  exact Block.loadInt_isSome_split h (Split.right (Split.right (Split.right (Split.left
    (Split.right (Split.here _ _) _) _) _) _) _) (by simp)

omit [CodeEnv] in
/-- The bytes of an integer read back at their width. -/
theorem tb_ofInt (n : Nat) (z : Int) :
    Int.toBytes n (BitVec.ofInt (8 * n) z).toInt = Int.toBytes n z := by
  rw [← Int.toBytes_emod n (BitVec.ofInt (8 * n) z).toInt, ← Int.toBytes_emod n z]
  congr 1
  simp only [Int.take, BitVec.toInt_ofInt]
  exact Int.bmod_emod

omit [CodeEnv] in
theorem tb4_ofBytes (l : List UInt8) (hl : l.length = 4) :
    Int.toBytes 4 (BitVec.setWidth 32 (BitVec.setWidth 64
      (BitVec.ofInt 32 (Int.ofBytes l)))).toInt = l := by
  have e : ∀ y : BitVec 32, BitVec.setWidth 32 (BitVec.setWidth 64 y) = y :=
    fun y => by apply BitVec.eq_of_toNat_eq; simp
  rw [e, tb_ofInt 4, ← hl, Int.toBytes_ofBytes_all]

omit [CodeEnv] in
theorem tb2_ofBytes (l : List UInt8) (hl : l.length = 2) :
    Int.toBytes 2 (BitVec.setWidth 16 (BitVec.setWidth 64
      (BitVec.setWidth 32 (BitVec.ofInt 16 (Int.ofBytes l))))).toInt = l := by
  have e : ∀ y : BitVec 16, BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32 y)) = y :=
    fun y => by apply BitVec.eq_of_toNat_eq; simp
  rw [e, tb_ofInt 2, ← hl, Int.toBytes_ofBytes_all]

/-- The old `bs_limiter_bands` and `spectrum_params` bytes into `eax` and the locals. -/
theorem blk_L34dd (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L34dd" := by
  cfg_block
  measure_hb "L34dd"
    intro n
    simp only [tbl_L34dd, var_L34dd]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, hP, hm⟩, hdx⟩, h15⟩ := hs₀.1
    obtain rfl := hs₀.2
    have hst : ∀ a (ha : a = t₀.regs.get64 .rsp - 0x38#64) v
        a' (ha' : a' = t₀.regs.get64 .rsp - 0x3c#64) w,
        Int.toBytes 4 w = st.sp.take 4 → Int.toBytes 2 v = st.sp.drop 4 →
        UM k A ra t₀ (LocT (t₀.regs.get64 .rsp) (ivv t₀) (st.sp.take 4) (st.sp.drop 4)) (Sv t₀) st
          ((s₀.dmem.storeInt a 2 v).storeInt a' 4 w) := by
      intro a ha v a' ha' w h4 h2
      rw [← h4, ← h2]
      exact um_storeL4 (um_storeL2 hm a ha v) a' ha' w
    have hl2 := fun a ha => um_loadL2 hm a ha
    have hl4 := fun a ha v a' ha' => um_loadL4 (um_storeL2 hm a ha v) a' ha'
    have lt4 : ∀ a (ha : a = t₀.regs.get64 .rsp - 0x38#64) v,
        (s₀.dmem.storeInt a 2 v).loadInt (A.1.c + 166204#64) 4
          = some (Int.ofBytes (st.sp.take 4)) := by
      intro a ha v
      have h := um_storeL2 hm a ha v
      simp only [UM, UF, SHW] at h
      rw [show A.1.c + 166204#64 = sA A.1.c + 0x1c#64 by simp only [sA]; bv_omega]
      sep_mem h <;> simp [hI.2.1.1, List.take_take]
    have hm2 := hm
    simp only [UM, UF, SHW] at hm2
    have llb : s₀.dmem.loadInt (A.1.c + 166220#64) 4
        = some (Int.ofBytes (Int.toBytes 4 (BitVec.ofNat 32 st.h.lb).toInt)) := by
      rw [show A.1.c + 166220#64 = sA A.1.c + 0x2c#64 by simp only [sA]; bv_omega]
      sep_mem hm2 <;> rfl
    have ld4 : s₀.dmem.loadInt (A.1.c + 166208#64) 2 = some (Int.ofBytes (st.sp.drop 4)) := by
      rw [show A.1.c + 166208#64 = sA A.1.c + 0x20#64 by simp only [sA]; bv_omega]
      have e : st.sp.drop 4 = (st.sp.drop 4).take 2 :=
        (List.take_of_length_le (by simp [hI.2.1.1])).symm
      rw [e]
      sep_mem hm2 <;> simp [hI.2.1.1]
    clear hm2
    have hof2 : s₀.regs.get64 .rbp + (-48 : Int64).toBitVec = t₀.regs.get64 .rsp - 0x38#64 := by
      rw [hbp, show (-48 : Int64).toBitVec = -48#64 from rfl]; bv_omega
    have hof4 : s₀.regs.get64 .rbp + (-52 : Int64).toBitVec = t₀.regs.get64 .rsp - 0x3c#64 := by
      rw [hbp, show (-52 : Int64).toBitVec = -52#64 from rfl]; bv_omega
    have hsl := hI.2.1.1
    generalize UM k A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) (Sv t₀) st = P at hm
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, hbx] at *
    all_goals try simp only [llb, ld4, Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    · exact hl2 _ hof2
    · rw [lt4 _ hof2 _]; rfl
    · exact hl4 _ hof2 _ _ hof4
    · simp only [lt4 _ hof2, Option.some.injEq] at *
      subst_vars
      refine ⟨?_, by simp only [var_L34f7]; omega⟩
      rw [tbl_L34f7]
      unfold T_L34f7 AtDH
      refine ⟨⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, st, ?inv, ?s1, trivial, ?_, ?mem⟩, ?_⟩
      case inv => exact hI
      case s1 => exact hP
      case mem =>
        exact hst _ hof2 _ _ hof4 _ (tb4_ofBytes _ (by simp [hsl]))
          (tb2_ofBytes _ (by simp [hsl]))
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true,
        BitVec.ofInt32_ofBytes_toBytes4]
      all_goals first
        | exact hsp | exact hbp | exact h12 | exact h14
        | exact h13 | exact hdx | exact h15
        | exact hs₀.1.1.1.2.1.2.2.2.1
        | simp

end Kraken.Examples.Sbr.Usac
