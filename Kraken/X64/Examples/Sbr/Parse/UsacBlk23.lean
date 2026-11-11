import Kraken.X64.Examples.Sbr.Parse.UsacBlk22
open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse
set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true
/-! # `ff_aac_sbr_decode_usac_data`: the default header's copy (helpers)

The stores of `copy_usac_default_header`: bytes of `spectrum_params`, the cells
`bs_limiter_bands`, `bs_limiter_gains`, `bs_interpol_freq`, `bs_smoothing_mode`, `reset`,
the raw `bs_intertes` slot (`sbr + 0x14`). -/
namespace Kraken.Examples.Sbr.Usac
variable [CodeEnv]

/-- The first four bytes of `spectrum_params`, at `st` and at new bytes `sp'`. -/
theorem um_split_spT (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) (Lc Sg : Mem 64 → Prop)
    (st : USt) (sp' : List UInt8) (he : sp'.drop 4 = st.sp.drop 4) :
    ∃ R, Split (st.sp.take 4 =@ (sA A.1.c + 0x1c#64)) R (UM k A ra t₀ Lc Sg st)
      ∧ Split (sp'.take 4 =@ (sA A.1.c + 0x1c#64)) R
        (UM k A ra t₀ Lc Sg { st with sp := sp' }) := by
  simp only [UM, UF, SHW, he]
  exact ⟨_, Split.right (Split.right (Split.left (Split.left (Split.right (Split.right
      (Split.right (Split.right (Split.right (Split.right (Split.right (Split.here _ _) _) _) _)
      _) _) _) _) _) _) _) _,
    Split.right (Split.right (Split.left (Split.left (Split.right (Split.right
      (Split.right (Split.right (Split.right (Split.right (Split.right (Split.here _ _) _) _) _)
      _) _) _) _) _) _) _) _⟩

/-- The last two bytes of `spectrum_params`, at `st` and at new bytes `sp'`. -/
theorem um_split_spD (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) (Lc Sg : Mem 64 → Prop)
    (st : USt) (sp' : List UInt8) (he : sp'.take 4 = st.sp.take 4) :
    ∃ R, Split (st.sp.drop 4 =@ (sA A.1.c + 0x20#64)) R (UM k A ra t₀ Lc Sg st)
      ∧ Split (sp'.drop 4 =@ (sA A.1.c + 0x20#64)) R
        (UM k A ra t₀ Lc Sg { st with sp := sp' }) := by
  simp only [UM, UF, SHW, he]
  exact ⟨_, Split.right (Split.right (Split.left (Split.left (Split.right (Split.right
      (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right
      (Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _,
    Split.right (Split.right (Split.left (Split.left (Split.right (Split.right
      (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right
      (Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _⟩

omit [CodeEnv] in
theorem set_take_eq (l : List UInt8) (j n : Nat) (b : UInt8) (hj : j < n) (hn : n ≤ l.length) :
    (l.set j b).take n = (l.take n).take j ++ [b] ++ (l.take n).drop (j + 1) := by
  apply List.ext_getElem
  · simp; omega
  · intro i h₁ h₂
    simp only [List.length_take, List.length_set] at h₁
    simp only [List.getElem_take, List.getElem_set, List.getElem_append, List.length_append,
      List.length_take, List.length_singleton, List.getElem_drop]
    split <;> split <;> (try split) <;> simp_all <;> (try omega) <;> (congr 1; omega)

omit [CodeEnv] in
theorem set_drop_eq (l : List UInt8) (i n : Nat) (b : UInt8) (hi : n + i < l.length) :
    (l.set (n + i) b).drop n = (l.drop n).take i ++ [b] ++ (l.drop n).drop (i + 1) := by
  apply List.ext_getElem
  · simp; omega
  · intro x h₁ h₂
    simp only [List.length_drop, List.length_set] at h₁
    simp only [List.getElem_drop, List.getElem_set, List.getElem_append, List.length_append,
      List.length_take, List.length_drop, List.length_singleton, List.getElem_take]
    split <;> split <;> (try split) <;> simp_all <;> (try omega) <;> (congr 1; omega)

/-- A byte store into the first four bytes of `spectrum_params`. -/
theorem um_storeSpT {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} (h : m =⋆ UM k A ra t₀ Lc Sg st)
    (hl : st.sp.length = 6) (j : Nat) (hj : j < 4) (a : BitVec 64)
    (ha : a = sA A.1.c + 0x1c#64 + BitVec.ofNat 64 j) (v : BitVec 8) :
    m.storeInt a 1 v.toInt
      =⋆ UM k A ra t₀ Lc Sg { st with sp := st.sp.set j (UInt8.ofBitVec v) } := by
  have he : (st.sp.set j (UInt8.ofBitVec v)).drop 4 = st.sp.drop 4 := by
    apply List.ext_getElem
    · simp
    · intro n h₁ h₂; simp only [List.getElem_drop, List.getElem_set]
      exact ite_eq_right (by omega)
  obtain ⟨R, hs, hs'⟩ := um_split_spT k A ra t₀ Lc Sg st _ he
  rw [hs']
  have hj' : (a - (sA A.1.c + 0x1c#64)).toNat = j := by
    rw [ha, show ∀ x y : BitVec 64, x + y - x = y from fun x y => by bv_omega,
      BitVec.toNat_ofNat]; omega
  have := Val.storeInt_slice_split (n := 1) h hs (by rw [hj']; simp [hl]; omega) (by simp [hl])
    v.toInt
  rw [hj', tb1] at this
  rw [set_take_eq _ _ _ _ hj (by omega)]
  exact this

/-- A byte store into the last two bytes of `spectrum_params`. -/
theorem um_storeSpD {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} (h : m =⋆ UM k A ra t₀ Lc Sg st)
    (hl : st.sp.length = 6) (i : Nat) (hi : i < 2) (a : BitVec 64)
    (ha : a = sA A.1.c + 0x20#64 + BitVec.ofNat 64 i) (v : BitVec 8) :
    m.storeInt a 1 v.toInt
      =⋆ UM k A ra t₀ Lc Sg { st with sp := st.sp.set (4 + i) (UInt8.ofBitVec v) } := by
  have he : (st.sp.set (4 + i) (UInt8.ofBitVec v)).take 4 = st.sp.take 4 := by
    apply List.ext_getElem
    · simp
    · intro n h₁ h₂; simp only [List.getElem_take, List.getElem_set]
      simp only [List.length_take, List.length_set] at h₁
      exact ite_eq_right (by omega)
  obtain ⟨R, hs, hs'⟩ := um_split_spD k A ra t₀ Lc Sg st _ he
  rw [hs']
  have hi' : (a - (sA A.1.c + 0x20#64)).toNat = i := by
    rw [ha, show ∀ x y : BitVec 64, x + y - x = y from fun x y => by bv_omega,
      BitVec.toNat_ofNat]; omega
  have := Val.storeInt_slice_split (n := 1) h hs (by rw [hi']; simp [hl]; omega) (by simp [hl])
    v.toInt
  rw [hi', tb1] at this
  rw [set_drop_eq _ _ _ _ (by omega)]
  exact this

/-- The raw `bs_intertes` slot (`sbr + 0x14`). -/
theorem um_split_r14 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) (Lc Sg : Mem 64 → Prop)
    (st : USt) : ∃ R, Split (4 ?@ (sA A.1.c + 0x14#64)) R (UM k A ra t₀ Lc Sg st) := by
  simp only [UM, UF, SHW]
  exact ⟨_, Split.right (Split.right (Split.left (Split.left (Split.right (Split.right
    (Split.right (Split.right (Split.right (Split.here _ _) _) _) _) _) _) _) _) _) _⟩

theorem um_storeR14 {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} (h : m =⋆ UM k A ra t₀ Lc Sg st) (a : BitVec 64)
    (ha : a = sA A.1.c + 0x14#64) (v : Int) :
    m.storeInt a 4 v =⋆ UM k A ra t₀ Lc Sg st := by
  obtain ⟨R, hs⟩ := um_split_r14 k A ra t₀ Lc Sg st
  exact Block.storeInt_split h hs (by rw [ha]; simp) v

/-- `reset` (`sbr + 0x18`). -/
theorem um_storeRst {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} (h : m =⋆ UM k A ra t₀ Lc Sg st) (a : BitVec 64)
    (ha : a = sA A.1.c + 0x18#64) (v : BitVec 32) :
    m.storeInt a 4 v.toInt =⋆ UM k A ra t₀ Lc Sg { st with x := { st.x with reset := v } } := by
  obtain ⟨R, hs, hs'⟩ : ∃ R, Split (cell4 (sA A.1.c + 0x18#64) st.x.reset) R (UM k A ra t₀ Lc Sg st)
      ∧ Split (cell4 (sA A.1.c + 0x18#64) v) R
        (UM k A ra t₀ Lc Sg { st with x := { st.x with reset := v } }) := by
    simp only [UM, UF, SHW]
    exact ⟨_, Split.right (Split.right (Split.left (Split.left (Split.right (Split.right
      (Split.right (Split.right (Split.right (Split.right (Split.here _ _) _) _) _) _) _) _) _)
      _) _) _,
      Split.right (Split.right (Split.left (Split.left (Split.right (Split.right
      (Split.right (Split.right (Split.right (Split.right (Split.here _ _) _) _) _) _) _) _) _)
      _) _) _⟩
  rw [hs', ha]
  exact Val.storeInt h hs (Int.toBytes_length 4 _) v.toInt

/-- `bs_limiter_bands` (`sbr + 0x2c`). -/
theorem um_storeLb {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} (h : m =⋆ UM k A ra t₀ Lc Sg st) (a : BitVec 64)
    (ha : a = sA A.1.c + 0x2c#64) (v : BitVec 32) (n : Nat) (hv : v = BitVec.ofNat 32 n) :
    m.storeInt a 4 v.toInt =⋆ UM k A ra t₀ Lc Sg { st with h := { st.h with lb := n } } := by
  obtain ⟨R, hs, hs'⟩ : ∃ R, Split (cell4 (sA A.1.c + 0x2c#64) (BitVec.ofNat 32 st.h.lb)) R
        (UM k A ra t₀ Lc Sg st)
      ∧ Split (cell4 (sA A.1.c + 0x2c#64) (BitVec.ofNat 32 n)) R
        (UM k A ra t₀ Lc Sg { st with h := { st.h with lb := n } }) := by
    simp only [UM, UF, SHW]
    exact ⟨_, Split.right (Split.right (Split.left (Split.left (Split.right (Split.right
      (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right
      (Split.right (Split.right (Split.right (Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _)
      _) _) _) _,
      Split.right (Split.right (Split.left (Split.left (Split.right (Split.right
      (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right
      (Split.right (Split.right (Split.right (Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _)
      _) _) _) _⟩
  rw [hs', ha, ← hv]
  exact Val.storeInt h hs (Int.toBytes_length 4 _) v.toInt

/-- `bs_limiter_gains` (`sbr + 0x30`). -/
theorem um_storeLg {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} (h : m =⋆ UM k A ra t₀ Lc Sg st) (a : BitVec 64)
    (ha : a = sA A.1.c + 0x30#64) (v : BitVec 32) (n : Nat) (hv : v.toInt = (n : Int)) :
    m.storeInt a 4 v.toInt
      =⋆ UM k A ra t₀ Lc Sg { st with x := { st.x with limGains := n } } := by
  obtain ⟨R, hs, hs'⟩ : ∃ R, Split (c4 (sA A.1.c + 0x30#64) st.x.limGains) R
        (UM k A ra t₀ Lc Sg st)
      ∧ Split (c4 (sA A.1.c + 0x30#64) n) R
        (UM k A ra t₀ Lc Sg { st with x := { st.x with limGains := n } }) := by
    simp only [UM, UF, SHW]
    exact ⟨_, Split.right (Split.right (Split.left (Split.left (Split.right (Split.right
      (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right
      (Split.right (Split.right (Split.right (Split.right (Split.here _ _) _) _) _) _) _) _) _)
      _) _) _) _) _) _) _) _) _) _,
      Split.right (Split.right (Split.left (Split.left (Split.right (Split.right
      (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right
      (Split.right (Split.right (Split.right (Split.right (Split.here _ _) _) _) _) _) _) _) _)
      _) _) _) _) _) _) _) _) _) _⟩
  rw [hs', ha]
  have := Val.storeInt h hs (Int.toBytes_length 4 _) v.toInt
  rw [show Int.toBytes 4 v.toInt = Int.toBytes 4 (n : Int) by rw [hv]] at this
  exact this

/-- `bs_interpol_freq` (`sbr + 0x34`). -/
theorem um_storeIp {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} (h : m =⋆ UM k A ra t₀ Lc Sg st) (a : BitVec 64)
    (ha : a = sA A.1.c + 0x34#64) (v : BitVec 32) :
    m.storeInt a 4 v.toInt =⋆ UM k A ra t₀ Lc Sg { st with x := { st.x with interpol := v } } := by
  obtain ⟨R, hs, hs'⟩ : ∃ R, Split (cell4 (sA A.1.c + 0x34#64) st.x.interpol) R
        (UM k A ra t₀ Lc Sg st)
      ∧ Split (cell4 (sA A.1.c + 0x34#64) v) R
        (UM k A ra t₀ Lc Sg { st with x := { st.x with interpol := v } }) := by
    simp only [UM, UF, SHW]
    exact ⟨_, Split.right (Split.right (Split.left (Split.left (Split.right (Split.right
      (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right
      (Split.right (Split.right (Split.right (Split.right (Split.right (Split.here _ _) _) _) _)
      _) _) _) _) _) _) _) _) _) _) _) _) _) _) _,
      Split.right (Split.right (Split.left (Split.left (Split.right (Split.right
      (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right
      (Split.right (Split.right (Split.right (Split.right (Split.right (Split.here _ _) _) _) _)
      _) _) _) _) _) _) _) _) _) _) _) _) _) _) _⟩
  rw [hs', ha]
  exact Val.storeInt h hs (Int.toBytes_length 4 _) v.toInt

/-- `bs_smoothing_mode` (`sbr + 0x38`). -/
theorem um_storeSm {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} (h : m =⋆ UM k A ra t₀ Lc Sg st) (a : BitVec 64)
    (ha : a = sA A.1.c + 0x38#64) (v : BitVec 32) :
    m.storeInt a 4 v.toInt =⋆ UM k A ra t₀ Lc Sg { st with x := { st.x with smooth := v } } := by
  obtain ⟨R, hs, hs'⟩ : ∃ R, Split (cell4 (sA A.1.c + 0x38#64) st.x.smooth) R
        (UM k A ra t₀ Lc Sg st)
      ∧ Split (cell4 (sA A.1.c + 0x38#64) v) R
        (UM k A ra t₀ Lc Sg { st with x := { st.x with smooth := v } }) := by
    simp only [UM, UF, SHW]
    exact ⟨_, Split.right (Split.right (Split.left (Split.left (Split.right (Split.right
      (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right
      (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right
      (Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _,
      Split.right (Split.right (Split.left (Split.left (Split.right (Split.right
      (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right
      (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right
      (Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _⟩
  rw [hs', ha]
  exact Val.storeInt h hs (Int.toBytes_length 4 _) v.toInt

/-- The locals: forgetting the old bytes (`LocT` back to `LocI`). -/
theorem um_forgetLoc {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Sg : Mem 64 → Prop} {st : USt} {iv : BitVec 32} {l4 l2 : List UInt8}
    (hl4 : l4.length = 4) (hl2 : l2.length = 2)
    (h : m =⋆ UM k A ra t₀ (LocT (t₀.regs.get64 .rsp) iv l4 l2) Sg st) :
    m =⋆ UM k A ra t₀ (LocI (t₀.regs.get64 .rsp) iv) Sg st := by
  obtain ⟨R, hs, hs'⟩ : ∃ R, Split (l4 =@ (t₀.regs.get64 .rsp - 0x3c#64)) R
        (UM k A ra t₀ (LocT (t₀.regs.get64 .rsp) iv l4 l2) Sg st)
      ∧ Split (4 ?@ (t₀.regs.get64 .rsp - 0x3c#64)) R
        (UM k A ra t₀ (LocM (t₀.regs.get64 .rsp) iv l2) Sg st) := by
    simp only [UM, LocM, LocT]
    exact ⟨_, Split.right (Split.right (Split.right (Split.left (Split.right
        (Split.here _ _) _) _) _) _) _,
      Split.right (Split.right (Split.right (Split.left (Split.right
        (Split.here _ _) _) _) _) _) _⟩
  have h1 := Val.forget h hs (by simp [hl4])
  rw [hl4, ← hs'] at h1
  obtain ⟨R, hs, hs'⟩ : ∃ R, Split (l2 =@ (t₀.regs.get64 .rsp - 0x38#64)) R
        (UM k A ra t₀ (LocM (t₀.regs.get64 .rsp) iv l2) Sg st)
      ∧ Split (2 ?@ (t₀.regs.get64 .rsp - 0x38#64)) R
        (UM k A ra t₀ (LocI (t₀.regs.get64 .rsp) iv) Sg st) := by
    simp only [UM, LocI, LocM]
    exact ⟨_, Split.right (Split.right (Split.right (Split.left (Split.right (Split.right
        (Split.here _ _) _) _) _) _) _) _,
      Split.right (Split.right (Split.right (Split.left (Split.right (Split.right
        (Split.here _ _) _) _) _) _) _) _⟩
  have h2 := Val.forget h1 hs (by simp [hl2])
  rw [hl2, ← hs'] at h2
  exact h2

/-- Loading the cell at `sbr + 0x18` succeeds. -/
theorem um_loadRst {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} (h : m =⋆ UM k A ra t₀ Lc Sg st) (a : BitVec 64)
    (ha : a = sA A.1.c + 0x18#64) : (m.loadInt a 4).isSome = true := by
  obtain ⟨R, hs⟩ : ∃ R, Split (cell4 (sA A.1.c + 0x18#64) st.x.reset) R
      (UM k A ra t₀ Lc Sg st) := by
    simp only [UM, UF, SHW]
    exact
    ⟨_, Split.right (Split.right (Split.left (Split.left (Split.right (Split.right
    (Split.right (Split.right (Split.right (Split.right (Split.here _ _) _) _) _) _) _) _)
    _) _) _) _⟩
  exact Val.loadInt_isSome_slice h hs (by rw [ha]; simp [Int.toBytes_length])
    (by simp [Int.toBytes_length])

/-- Loading the cell at `sbr + 0x2c` succeeds. -/
theorem um_loadLb {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} (h : m =⋆ UM k A ra t₀ Lc Sg st) (a : BitVec 64)
    (ha : a = sA A.1.c + 0x2c#64) : (m.loadInt a 4).isSome = true := by
  obtain ⟨R, hs⟩ : ∃ R, Split (cell4 (sA A.1.c + 0x2c#64) (BitVec.ofNat 32 st.h.lb)) R
      (UM k A ra t₀ Lc Sg st) := by
    simp only [UM, UF, SHW]
    exact
    ⟨_, Split.right (Split.right (Split.left (Split.left (Split.right (Split.right
    (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right
    (Split.right (Split.right (Split.right (Split.right (Split.here _ _) _) _) _) _) _) _)
    _) _) _) _) _) _) _) _) _) _⟩
  exact Val.loadInt_isSome_slice h hs (by rw [ha]; simp [Int.toBytes_length])
    (by simp [Int.toBytes_length])

/-- Loading the cell at `sbr + 0x30` succeeds. -/
theorem um_loadLg {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} (h : m =⋆ UM k A ra t₀ Lc Sg st) (a : BitVec 64)
    (ha : a = sA A.1.c + 0x30#64) : (m.loadInt a 4).isSome = true := by
  obtain ⟨R, hs⟩ : ∃ R, Split (c4 (sA A.1.c + 0x30#64) st.x.limGains) R
      (UM k A ra t₀ Lc Sg st) := by
    simp only [UM, UF, SHW]
    exact
    ⟨_, Split.right (Split.right (Split.left (Split.left (Split.right (Split.right
    (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right
    (Split.right (Split.right (Split.right (Split.right (Split.right (Split.here _ _) _)
    _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _⟩
  exact Val.loadInt_isSome_slice h hs (by rw [ha]; simp [Int.toBytes_length])
    (by simp [Int.toBytes_length])

/-- Loading the cell at `sbr + 0x34` succeeds. -/
theorem um_loadIp {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} (h : m =⋆ UM k A ra t₀ Lc Sg st) (a : BitVec 64)
    (ha : a = sA A.1.c + 0x34#64) : (m.loadInt a 4).isSome = true := by
  obtain ⟨R, hs⟩ : ∃ R, Split (cell4 (sA A.1.c + 0x34#64) st.x.interpol) R
      (UM k A ra t₀ Lc Sg st) := by
    simp only [UM, UF, SHW]
    exact
    ⟨_, Split.right (Split.right (Split.left (Split.left (Split.right (Split.right
    (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right
    (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right
    (Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _⟩
  exact Val.loadInt_isSome_slice h hs (by rw [ha]; simp [Int.toBytes_length])
    (by simp [Int.toBytes_length])

/-- Loading the cell at `sbr + 0x38` succeeds. -/
theorem um_loadSm {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} (h : m =⋆ UM k A ra t₀ Lc Sg st) (a : BitVec 64)
    (ha : a = sA A.1.c + 0x38#64) : (m.loadInt a 4).isSome = true := by
  obtain ⟨R, hs⟩ : ∃ R, Split (cell4 (sA A.1.c + 0x38#64) st.x.smooth) R
      (UM k A ra t₀ Lc Sg st) := by
    simp only [UM, UF, SHW]
    exact
    ⟨_, Split.right (Split.right (Split.left (Split.left (Split.right (Split.right
    (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right
    (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right
    (Split.right (Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _⟩
  exact Val.loadInt_isSome_slice h hs (by rw [ha]; simp [Int.toBytes_length])
    (by simp [Int.toBytes_length])

theorem um_loadR14 {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} (h : m =⋆ UM k A ra t₀ Lc Sg st) (a : BitVec 64)
    (ha : a = sA A.1.c + 0x14#64) : (m.loadInt a 4).isSome = true := by
  obtain ⟨R, hs⟩ := um_split_r14 k A ra t₀ Lc Sg st
  rw [hs] at h
  exact Block.loadInt_isSome h (by rw [ha]; simp)

/-- Loads inside the first four bytes of `spectrum_params`. -/
theorem um_loadSpT {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} (h : m =⋆ UM k A ra t₀ Lc Sg st)
    (hl : st.sp.length = 6) (j n : Nat) (hj : j + n ≤ 4) (a : BitVec 64)
    (ha : a = sA A.1.c + 0x1c#64 + BitVec.ofNat 64 j) :
    m.loadInt a n = some (Int.ofBytes (((st.sp.take 4).drop j).take n)) := by
  obtain ⟨R, hs, -⟩ := um_split_spT k A ra t₀ Lc Sg st st.sp rfl
  have hj' : (a - (sA A.1.c + 0x1c#64)).toNat = j := by
    rw [ha, show ∀ x y : BitVec 64, x + y - x = y from fun x y => by bv_omega,
      BitVec.toNat_ofNat]; omega
  rw [← hj']
  exact Val.loadInt_slice_split h hs (by rw [hj']; simp [hl]; omega) (by simp [hl])

/-- Loads inside the last two bytes of `spectrum_params`. -/
theorem um_loadSpD {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} (h : m =⋆ UM k A ra t₀ Lc Sg st)
    (hl : st.sp.length = 6) (j n : Nat) (hj : j + n ≤ 2) (a : BitVec 64)
    (ha : a = sA A.1.c + 0x20#64 + BitVec.ofNat 64 j) :
    m.loadInt a n = some (Int.ofBytes (((st.sp.drop 4).drop j).take n)) := by
  obtain ⟨R, hs, -⟩ := um_split_spD k A ra t₀ Lc Sg st st.sp rfl
  have hj' : (a - (sA A.1.c + 0x20#64)).toNat = j := by
    rw [ha, show ∀ x y : BitVec 64, x + y - x = y from fun x y => by bv_omega,
      BitVec.toNat_ofNat]; omega
  rw [← hj']
  exact Val.loadInt_slice_split h hs (by rw [hj']; simp [hl]; omega) (by simp [hl])

/-- Loads of `ue->sbr`. -/
theorem um_loadUe {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} (h : m =⋆ UM k A ra t₀ Lc Sg st)
    (hl : A.1.uev.length = 12) (j n : Nat) (hj : j + n ≤ 12) (a : BitVec 64)
    (ha : a = A.1.ue + 0xc#64 + BitVec.ofNat 64 j) :
    m.loadInt a n = some (Int.ofBytes ((A.1.uev.drop j).take n)) := by
  obtain ⟨R, hs⟩ : ∃ R, Split (A.1.uev =@ (A.1.ue + 0xc#64)) R (UM k A ra t₀ Lc Sg st) := by
    simp only [UM, UF, RdU]
    exact ⟨_, Split.right (Split.right (Split.left (Split.right (Split.right (Split.right
      (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right
      (Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _⟩
  have hj' : (a - (A.1.ue + 0xc#64)).toNat = j := by
    rw [ha, show ∀ x y : BitVec 64, x + y - x = y from fun x y => by bv_omega,
      BitVec.toNat_ofNat]; omega
  rw [← hj']
  exact Val.loadInt_slice_split h hs (by rw [hj']; omega) (by simp [hl])

omit [CodeEnv] in
theorem ob1 (b : UInt8) : UInt8.ofBitVec (BitVec.ofInt 8 (Int.ofBytes [b])) = b := by
  cases b with | ofBitVec v => ?_
  revert v; decide

omit [CodeEnv] in
theorem drop_take1 (l : List UInt8) (j : Nat) (hj : j < l.length) :
    (l.drop j).take 1 = [l.getD j 0] := by
  induction j generalizing l with
  | zero => cases l <;> simp_all
  | succ j ih =>
    cases l with
    | nil => simp at hj
    | cons x l =>
      simp only [List.drop_succ_cons, List.getD_cons_succ]
      exact ih l (by simp at hj; omega)

omit [CodeEnv] in
theorem sw8 (y : BitVec 8) : BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 y)) = y := by
  apply BitVec.eq_of_toNat_eq; simp

omit [CodeEnv] in
/-- A byte of `ue->sbr` loaded (`movzbl`) and stored (`mov %cl`). -/
theorem ub_byte (l : List UInt8) (j : Nat) (hj : j < l.length) :
    UInt8.ofBitVec (BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32
      (BitVec.ofInt 8 (Int.ofBytes ((l.drop j).take 1)))))) = l.getD j 0 := by
  rw [sw8, drop_take1 l j hj, ob1]

omit [CodeEnv] in
theorem ob1v (b : UInt8) : BitVec.ofInt 8 (Int.ofBytes [b]) = b.toBitVec :=
  congrArg UInt8.toBitVec (ob1 b)

omit [CodeEnv] in
/-- A byte of `ue->sbr` zero-extended (`movzbl`) into a 32-bit cell. -/
theorem ub_zx32 (l : List UInt8) (j : Nat) (hj : j < l.length) :
    BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32
      (BitVec.ofInt 8 (Int.ofBytes ((l.drop j).take 1))))) = BitVec.ofNat 32 (u8 l j) := by
  rw [drop_take1 l j hj, ob1v]
  simp only [u8]
  generalize l.getD j 0 = b
  cases b with | ofBitVec v => ?_
  apply BitVec.eq_of_toNat_eq
  have := v.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, UInt8.toNat_ofBitVec]
  omega

omit [CodeEnv] in
theorem ub_zx64 (l : List UInt8) (j : Nat) (hj : j < l.length) :
    BitVec.setWidth 64 (BitVec.setWidth 32
      (BitVec.ofInt 8 (Int.ofBytes ((l.drop j).take 1)))) = BitVec.ofNat 64 (u8 l j) := by
  rw [drop_take1 l j hj, ob1v]
  simp only [u8]
  generalize l.getD j 0 = b
  cases b with | ofBitVec v => ?_
  apply BitVec.eq_of_toNat_eq
  have := v.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, UInt8.toNat_ofBitVec]
  omega

omit [CodeEnv] in
theorem zx_toInt (n : Nat) (h : n < 256) : (BitVec.ofNat 32 n).toInt = (n : Int) := by
  have e : (BitVec.ofNat 32 n).toNat = n := by simp; omega
  rw [BitVec.toInt_eq_toNat_cond, e]; simp; omega

omit [CodeEnv] in
/-- `movzbl`, `and $1, %cl`, `mov %cl`. -/
theorem ub_and1 (l : List UInt8) (j : Nat) (hj : j < l.length) :
    UInt8.ofBitVec (BitVec.setWidth 8 ((BitVec.setWidth 64 (BitVec.setWidth 32
      (BitVec.ofInt 8 (Int.ofBytes ((l.drop j).take 1))))).replaceLow
      (BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32
        (BitVec.ofInt 8 (Int.ofBytes ((l.drop j).take 1))))) &&& BitVec.setWidth 8 1#64)))
      = l.getD j 0 &&& 1 := by
  have e : ∀ (o : BitVec 64) (nw : BitVec 8), BitVec.setWidth 8 (o.replaceLow nw) = nw := by
    intro o nw; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_replaceLow8]; omega
  rw [e, sw8, drop_take1 l j hj, ob1v]
  rfl

set_option maxRecDepth 20000 in
/-- `bs_intertes` (raw), `bs_start_freq` (byte 0 of `spectrum_params`). -/
theorem blk_L34f7 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L34f7" := by
  cfg_block
  measure_hb "L34f7"
    intro n
    simp only [tbl_L34f7, var_L34f7]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, hdx, st, hI, hS, -, hax, hm⟩, h15⟩ := hs₀.1
    obtain rfl := hs₀.2
    have hlen : A.1.uev.length = 12 := hF.1.2.2.2.2.1.1
    have hsl : st.sp.length = 6 := hI.2.1.1
    have hst : ∀ a (ha : a = sA A.1.c + 0x14#64) v a' (ha' : a' = sA A.1.c + 0x1c#64 + 0#64)
        (w : BitVec 8), UInt8.ofBitVec w = ub A.1 1 →
        UM k A ra t₀ (LocT (t₀.regs.get64 .rsp) (ivv t₀) (st.sp.take 4) (st.sp.drop 4)) (Sv t₀)
          (dhA A.1 st) ((s₀.dmem.storeInt a 4 v).storeInt a' 1 w.toInt) := by
      intro a ha v a' ha' w hw
      have := um_storeSpT (um_storeR14 hm a ha v) hsl 0 (by omega) a' ha' w
      rw [hw] at this
      exact this
    have lu4 : s₀.dmem.loadInt (A.1.ue + 12#64) 4
        = some (Int.ofBytes ((A.1.uev.drop 0).take 4)) :=
      um_loadUe hm hlen 0 4 (by omega) _ (by bv_omega)
    have lu1 : ∀ a (ha : a = sA A.1.c + 0x14#64) v,
        (s₀.dmem.storeInt a 4 v).loadInt (A.1.ue + 13#64) 1
          = some (Int.ofBytes ((A.1.uev.drop 1).take 1)) := fun a ha v =>
      um_loadUe (um_storeR14 hm a ha v) hlen 1 1 (by omega) _ (by bv_omega)
    have ld14 := fun a ha => um_loadR14 hm a ha
    have ld0 := fun a ha v a' ha' => um_loadSpT (um_storeR14 hm a ha v) hsl 0 1 (by omega) a' ha'
    have hbxc : PLift (s₀.regs.get64 .rbx = A.1.c) := ⟨hbx⟩
    have hdxc : PLift (s₀.regs.get64 .rdx = A.1.ue) := ⟨hdx⟩
    generalize UM k A ra t₀ (LocT (t₀.regs.get64 .rsp) (ivv t₀) (st.sp.take 4) (st.sp.drop 4))
      (Sv t₀) st = P at hm
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ofNat_eq_ofNat, BitVec.add_zero, hbxc.down, hdxc.down] at *
    all_goals try simp only [lu4, Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    · exact ld14 _ (by bv_omega)
    · rw [lu1 _ (by (try simp only [sA]); bv_omega)]; rfl
    · rw [ld0 _ (by (try simp only [sA]); bv_omega) _ _ (by (try simp only [sA]); bv_omega)]; rfl
    · rename_i hx
      rw [lu1 _ (by (try simp only [sA]); bv_omega), Option.some.injEq] at hx
      subst hx
      refine ⟨?_, by simp only [var_L350f]; omega⟩
      rw [tbl_L350f]
      unfold T_L350f AtDH
      refine ⟨⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, st, hI, hS, trivial, ?_, ?mem⟩, ?_⟩
      case mem =>
        exact hst _ (by (try simp only [sA]); bv_omega) _ _ (by (try simp only [sA]); bv_omega) _
          (ub_byte _ _ (by omega))
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]
      all_goals first
        | exact hsp | exact hbp | exact h12 | exact h14 | exact hbxc.down | exact hdxc.down
        | exact h13 | exact hax | exact h15

set_option maxRecDepth 20000 in
/-- `bs_stop_freq`, `bs_freq_scale` (bytes 1, 3). -/
theorem blk_L350f (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L350f" := by
  cfg_block
  measure_hb "L350f"
    intro n
    simp only [tbl_L350f, var_L350f]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, hdx, st, hI, hS, -, hax, hm⟩, h15⟩ := hs₀.1
    obtain rfl := hs₀.2
    have hlen : A.1.uev.length = 12 := hF.1.2.2.2.2.1.1
    have hsl : st.sp.length = 6 := hI.2.1.1
    have hsl' : (dhA A.1 st).sp.length = 6 := by simp [dhA, hsl]
    have m0 : s₀.dmem =⋆ UM k A ra t₀ (LocT (t₀.regs.get64 .rsp) (ivv t₀) (st.sp.take 4)
        (st.sp.drop 4)) (Sv t₀) (dhA A.1 st) := hm
    have lu2 : s₀.dmem.loadInt (A.1.ue + 14#64) 1 = some (Int.ofBytes ((A.1.uev.drop 2).take 1)) :=
      um_loadUe m0 hlen 2 1 (by omega) _ (by bv_omega)
    have lu3 : ∀ v : BitVec 8, (s₀.dmem.storeInt (A.1.c + 166205#64) 1 v.toInt).loadInt
        (A.1.ue + 15#64) 1
        = some (Int.ofBytes ((A.1.uev.drop 3).take 1)) := fun v =>
      um_loadUe (um_storeSpT m0 hsl' 1 (by omega) _ (by bv_omega) v) hlen 3 1
        (by omega) _ (by bv_omega)
    have ld1 : (s₀.dmem.loadInt (A.1.c + 166205#64) 1).isSome = true := by
      rw [um_loadSpT m0 hsl' 1 1 (by omega) _ (by (try simp only [sA]); bv_omega)]; rfl
    have ld3 : ∀ v : BitVec 8,
        ((s₀.dmem.storeInt (A.1.c + 166205#64) 1 v.toInt).loadInt (A.1.c + 166207#64) 1).isSome
          = true := by
      intro v
      rw [um_loadSpT (um_storeSpT m0 hsl' 1 (by omega) _ (by (try simp only [sA]); bv_omega) v)
        (by simp [hsl']) 3 1 (by omega) _ (by (try simp only [sA]); bv_omega)]; rfl
    have hst : ∀ w1 w2 : BitVec 8, UInt8.ofBitVec w1 = ub A.1 2 → UInt8.ofBitVec w2 = ub A.1 3 →
        UM k A ra t₀ (LocT (t₀.regs.get64 .rsp) (ivv t₀) (st.sp.take 4) (st.sp.drop 4)) (Sv t₀)
          (dhB A.1 st)
          ((s₀.dmem.storeInt (A.1.c + 166205#64) 1 w1.toInt).storeInt (A.1.c + 166207#64) 1
            w2.toInt) := by
      intro w1 w2 e1 e2
      have := um_storeSpT (um_storeSpT m0 hsl' 1 (by omega) (A.1.c + 166205#64)
        (by (try simp only [sA]); bv_omega) w1) (by simp [hsl']) 3 (by omega) (A.1.c + 166207#64)
        (by (try simp only [sA]); bv_omega) w2
      rw [e1, e2] at this
      exact this
    have hbxc : PLift (s₀.regs.get64 .rbx = A.1.c) := ⟨hbx⟩
    have hdxc : PLift (s₀.regs.get64 .rdx = A.1.ue) := ⟨hdx⟩
    generalize UM k A ra t₀ (LocT (t₀.regs.get64 .rsp) (ivv t₀) (st.sp.take 4) (st.sp.drop 4))
      (Sv t₀) (dhA A.1 st) = P at hm
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ofNat_eq_ofNat, BitVec.add_zero, hbxc.down, hdxc.down] at *
    all_goals try simp only [lu2, lu3, ld1, ld3, Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    refine ⟨?_, by simp only [var_L3523]; omega⟩
    rw [tbl_L3523]
    unfold T_L3523 AtDH
    refine ⟨⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, st, hI, hS, trivial, ?_, ?mem⟩, ?_⟩
    case mem => exact hst _ _ (ub_byte _ _ (by omega)) (ub_byte _ _ (by omega))
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]
    all_goals first
      | exact hsp | exact hbp | exact h12 | exact h14 | exact hbxc.down | exact hdxc.down
      | exact h13 | exact hax | exact h15

set_option maxRecDepth 20000 in
/-- `bs_alter_scale`, `bs_noise_bands` (bytes 4, 5). -/
theorem blk_L3523 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L3523" := by
  cfg_block
  measure_hb "L3523"
    intro n
    simp only [tbl_L3523, var_L3523]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, hdx, st, hI, hS, -, hax, hm⟩, h15⟩ := hs₀.1
    obtain rfl := hs₀.2
    have hlen : A.1.uev.length = 12 := hF.1.2.2.2.2.1.1
    have hsl : st.sp.length = 6 := hI.2.1.1
    have hsl' : (dhB A.1 st).sp.length = 6 := by simp [dhB, hsl]
    have m0 : s₀.dmem =⋆ UM k A ra t₀ (LocT (t₀.regs.get64 .rsp) (ivv t₀) (st.sp.take 4)
        (st.sp.drop 4)) (Sv t₀) (dhB A.1 st) := hm
    have lu4 : s₀.dmem.loadInt (A.1.ue + 16#64) 1 = some (Int.ofBytes ((A.1.uev.drop 4).take 1)) :=
      um_loadUe m0 hlen 4 1 (by omega) _ (by bv_omega)
    have lu5 : ∀ v : BitVec 8, (s₀.dmem.storeInt (A.1.c + 166208#64) 1 v.toInt).loadInt
        (A.1.ue + 17#64) 1 = some (Int.ofBytes ((A.1.uev.drop 5).take 1)) := fun v =>
      um_loadUe (um_storeSpD m0 hsl' 0 (by omega) _ (by (try simp only [sA]); bv_omega) v) hlen 5 1
        (by omega) _ (by bv_omega)
    have ld4 : (s₀.dmem.loadInt (A.1.c + 166208#64) 1).isSome = true := by
      rw [um_loadSpD m0 hsl' 0 1 (by omega) _ (by (try simp only [sA]); bv_omega)]; rfl
    have ld5 : ∀ v : BitVec 8,
        ((s₀.dmem.storeInt (A.1.c + 166208#64) 1 v.toInt).loadInt (A.1.c + 166209#64) 1).isSome
          = true := by
      intro v
      rw [um_loadSpD (um_storeSpD m0 hsl' 0 (by omega) _ (by (try simp only [sA]); bv_omega) v)
        (by simp [hsl']) 1 1 (by omega) _ (by (try simp only [sA]); bv_omega)]; rfl
    have hst : ∀ w1 w2 : BitVec 8, UInt8.ofBitVec w1 = ub A.1 4 &&& 1 →
        UInt8.ofBitVec w2 = ub A.1 5 →
        UM k A ra t₀ (LocT (t₀.regs.get64 .rsp) (ivv t₀) (st.sp.take 4) (st.sp.drop 4)) (Sv t₀)
          (dhC A.1 st)
          ((s₀.dmem.storeInt (A.1.c + 166208#64) 1 w1.toInt).storeInt (A.1.c + 166209#64) 1
            w2.toInt) := by
      intro w1 w2 e1 e2
      have := um_storeSpD (um_storeSpD m0 hsl' 0 (by omega) (A.1.c + 166208#64)
        (by (try simp only [sA]); bv_omega) w1) (by simp [hsl']) 1 (by omega) (A.1.c + 166209#64)
        (by (try simp only [sA]); bv_omega) w2
      rw [e1, e2] at this
      exact this
    have hbxc : PLift (s₀.regs.get64 .rbx = A.1.c) := ⟨hbx⟩
    have hdxc : PLift (s₀.regs.get64 .rdx = A.1.ue) := ⟨hdx⟩
    generalize UM k A ra t₀ (LocT (t₀.regs.get64 .rsp) (ivv t₀) (st.sp.take 4) (st.sp.drop 4))
      (Sv t₀) (dhB A.1 st) = P at hm
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ofNat_eq_ofNat, BitVec.add_zero, hbxc.down, hdxc.down] at *
    all_goals try simp only [lu4, lu5, ld4, ld5, Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    refine ⟨?_, by simp only [var_L353a]; omega⟩
    rw [tbl_L353a]
    unfold T_L353a AtDH
    refine ⟨⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, st, hI, hS, trivial, ?_, ?mem⟩, ?_⟩
    case mem => exact hst _ _ (ub_and1 _ _ (by omega)) (ub_byte _ _ (by omega))
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]
    all_goals first
      | exact hsp | exact hbp | exact h12 | exact h14 | exact hbxc.down | exact hdxc.down
      | exact h13 | exact hax | exact h15

set_option maxRecDepth 20000 in
/-- `bs_limiter_bands`, `bs_limiter_gains` (cells). -/
theorem blk_L353a (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L353a" := by
  cfg_block
  measure_hb "L353a"
    intro n
    simp only [tbl_L353a, var_L353a]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, hdx, st, hI, hS, -, hax, hm⟩, h15⟩ := hs₀.1
    obtain rfl := hs₀.2
    have hlen : A.1.uev.length = 12 := hF.1.2.2.2.2.1.1
    have m0 : s₀.dmem =⋆ UM k A ra t₀ (LocT (t₀.regs.get64 .rsp) (ivv t₀) (st.sp.take 4)
        (st.sp.drop 4)) (Sv t₀) (dhC A.1 st) := hm
    have lu6 : s₀.dmem.loadInt (A.1.ue + 18#64) 1 = some (Int.ofBytes ((A.1.uev.drop 6).take 1)) :=
      um_loadUe m0 hlen 6 1 (by omega) _ (by bv_omega)
    have lu7 : ∀ v : BitVec 32, (s₀.dmem.storeInt (A.1.c + 166220#64) 4 v.toInt).loadInt
        (A.1.ue + 19#64) 1 = some (Int.ofBytes ((A.1.uev.drop 7).take 1)) := fun v =>
      um_loadUe (um_storeLb m0 _ (by (try simp only [sA]); bv_omega) v v.toNat
        (by simp)) hlen 7 1 (by omega) _ (by bv_omega)
    have ldb : (s₀.dmem.loadInt (A.1.c + 166220#64) 4).isSome = true :=
      um_loadLb m0 _ (by (try simp only [sA]); bv_omega)
    have ldg : ∀ v : BitVec 32,
        ((s₀.dmem.storeInt (A.1.c + 166220#64) 4 v.toInt).loadInt (A.1.c + 166224#64) 4).isSome
          = true := fun v =>
      um_loadLg (um_storeLb m0 _ (by (try simp only [sA]); bv_omega) v v.toNat
        (by simp)) _ (by (try simp only [sA]); bv_omega)
    have hst : ∀ v1 v2 : BitVec 32, v1 = BitVec.ofNat 32 (u8 A.1.uev 6) →
        v2.toInt = (u8 A.1.uev 7 : Int) →
        UM k A ra t₀ (LocT (t₀.regs.get64 .rsp) (ivv t₀) (st.sp.take 4) (st.sp.drop 4)) (Sv t₀)
          (dhD A.1 st)
          ((s₀.dmem.storeInt (A.1.c + 166220#64) 4 v1.toInt).storeInt (A.1.c + 166224#64) 4
            v2.toInt) := fun v1 v2 e1 e2 =>
      um_storeLg (um_storeLb m0 (A.1.c + 166220#64) (by (try simp only [sA]); bv_omega) v1 _ e1)
        (A.1.c + 166224#64) (by (try simp only [sA]); bv_omega) v2 _ e2
    have hbxc : PLift (s₀.regs.get64 .rbx = A.1.c) := ⟨hbx⟩
    have hdxc : PLift (s₀.regs.get64 .rdx = A.1.ue) := ⟨hdx⟩
    generalize UM k A ra t₀ (LocT (t₀.regs.get64 .rsp) (ivv t₀) (st.sp.take 4) (st.sp.drop 4))
      (Sv t₀) (dhC A.1 st) = P at hm
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ofNat_eq_ofNat, BitVec.add_zero, hbxc.down, hdxc.down] at *
    all_goals try simp only [lu6, lu7, ldb, ldg, Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    refine ⟨?_, by simp only [var_L354e]; omega⟩
    rw [tbl_L354e]
    unfold T_L354e AtDH
    refine ⟨⟨⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, st, hI, hS, trivial, ?_, ?mem⟩, ?rcx⟩, ?_⟩
    case mem =>
      exact hst _ _ (ub_zx32 _ _ (by omega))
        (by rw [ub_zx32 _ _ (by omega), zx_toInt _ (UInt8.toNat_lt _)])
    case rcx =>
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]
      exact ub_zx64 _ _ (by omega)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]
    all_goals first
      | exact hsp | exact hbp | exact h12 | exact h14 | exact hbxc.down | exact hdxc.down
      | exact h13 | exact hax | exact h15

end Kraken.Examples.Sbr.Usac
