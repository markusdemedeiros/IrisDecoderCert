import Kraken.X64.Examples.Sbr.Parse.UsacGC1
import Kraken.X64.Examples.Sbr.Parse.UsacCpM
open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse
set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true
set_option linter.unusedSimpArgs false
/-! # `ff_aac_sbr_decode_usac_data`: the inlined `copy_sbr_grid` (memory helpers)

Loads from the cells of `data[0]`, stores into those of `data[1]` (`st.wd1 v`). -/
namespace Kraken.Examples.Sbr.Usac
variable [CodeEnv]

theorem um_split1Fr (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) (Lc Sg : Mem 64 → Prop)
    (st : USt) (v : DV) (l : List UInt8) :
    ∃ R, Split (v.freqRes =@ (dAc A.1.c 1 + 0xc#64)) R (UM k A ra t₀ Lc Sg (st.wd1 v))
      ∧ Split (l =@ (dAc A.1.c 1 + 0xc#64)) R
        (UM k A ra t₀ Lc Sg (st.wd1 { v with freqRes := l })) := by
  simp only [UM, UF, DSc]
  exact ⟨_, Split.right (Split.right (Split.left (Split.right (Split.right (Split.right (Split.right
    (Split.left (Split.right (Split.right (Split.right (Split.here _ _) _) _) _) _) _) _) _) _) _)
    _) _,
    Split.right (Split.right (Split.left (Split.right (Split.right (Split.right (Split.right
      (Split.left (Split.right (Split.right (Split.right (Split.here _ _) _) _) _) _) _) _) _) _) _)
      _) _⟩

/-- A store inside channel 1's `freqRes`. -/
theorem um_store1Fr {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} {v : DV} (h : m =⋆ UM k A ra t₀ Lc Sg (st.wd1 v))
    (hl : v.freqRes.length = 9) (j n : Nat) (hj : j + n ≤ 9) (a : BitVec 64)
    (ha : a = dAc A.1.c 1 + 0xc#64 + BitVec.ofNat 64 j) (val : Int) :
    m.storeInt a n val =⋆ UM k A ra t₀ Lc Sg (st.wd1 { v with
      freqRes := v.freqRes.take j ++ Int.toBytes n val ++ v.freqRes.drop (j + n) }) := by
  obtain ⟨R, hs, hs'⟩ := um_split1Fr k A ra t₀ Lc Sg st v
    (v.freqRes.take j ++ Int.toBytes n val ++ v.freqRes.drop (j + n))
  rw [hs']
  have hj' : (a - (dAc A.1.c 1 + 0xc#64)).toNat = j := by
    rw [ha, sub_base_add, BitVec.toNat_ofNat]; omega
  have := Val.storeInt_slice_split (n := n) h hs (by rw [hj', hl]; omega) (by rw [hl]; omega)
    val
  rw [hj'] at this
  exact this

/-- A load inside channel 1's `freqRes`. -/
theorem um_load1Fr {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} {v : DV} (h : m =⋆ UM k A ra t₀ Lc Sg (st.wd1 v))
    (hl : v.freqRes.length = 9) (j n : Nat) (hj : j + n ≤ 9) (a : BitVec 64)
    (ha : a = dAc A.1.c 1 + 0xc#64 + BitVec.ofNat 64 j) :
    m.loadInt a n = some (Int.ofBytes ((v.freqRes.drop j).take n)) := by
  obtain ⟨R, hs, -⟩ := um_split1Fr k A ra t₀ Lc Sg st v []
  have hj' : (a - (dAc A.1.c 1 + 0xc#64)).toNat = j := by
    rw [ha, sub_base_add, BitVec.toNat_ofNat]; omega
  have := Val.loadInt_slice_split (n := n) h hs (by rw [hj', hl]; omega) (by rw [hl]; omega)
  rw [hj'] at this
  exact this

theorem um_split1Iv (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) (Lc Sg : Mem 64 → Prop)
    (st : USt) (v : DV) (l : List UInt8) :
    ∃ R, Split (v.invf =@ (dAc A.1.c 1 + 0x27#64)) R (UM k A ra t₀ Lc Sg (st.wd1 v))
      ∧ Split (l =@ (dAc A.1.c 1 + 0x27#64)) R
        (UM k A ra t₀ Lc Sg (st.wd1 { v with invf := l })) := by
  simp only [UM, UF, DSc]
  exact ⟨_, Split.right (Split.right (Split.left (Split.right (Split.right (Split.right (Split.right
    (Split.left (Split.right (Split.right (Split.right (Split.right (Split.right (Split.here _ _) _)
    _) _) _) _) _) _) _) _) _) _) _) _,
    Split.right (Split.right (Split.left (Split.right (Split.right (Split.right (Split.right
      (Split.left (Split.right (Split.right (Split.right (Split.right (Split.right (Split.here _ _)
      _) _) _) _) _) _) _) _) _) _) _) _) _⟩

/-- A store inside channel 1's `invf`. -/
theorem um_store1Iv {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} {v : DV} (h : m =⋆ UM k A ra t₀ Lc Sg (st.wd1 v))
    (hl : v.invf.length = 10) (j n : Nat) (hj : j + n ≤ 10) (a : BitVec 64)
    (ha : a = dAc A.1.c 1 + 0x27#64 + BitVec.ofNat 64 j) (val : Int) :
    m.storeInt a n val =⋆ UM k A ra t₀ Lc Sg (st.wd1 { v with
      invf := v.invf.take j ++ Int.toBytes n val ++ v.invf.drop (j + n) }) := by
  obtain ⟨R, hs, hs'⟩ := um_split1Iv k A ra t₀ Lc Sg st v
    (v.invf.take j ++ Int.toBytes n val ++ v.invf.drop (j + n))
  rw [hs']
  have hj' : (a - (dAc A.1.c 1 + 0x27#64)).toNat = j := by
    rw [ha, sub_base_add, BitVec.toNat_ofNat]; omega
  have := Val.storeInt_slice_split (n := n) h hs (by rw [hj', hl]; omega) (by rw [hl]; omega)
    val
  rw [hj'] at this
  exact this

/-- A load inside channel 1's `invf`. -/
theorem um_load1Iv {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} {v : DV} (h : m =⋆ UM k A ra t₀ Lc Sg (st.wd1 v))
    (hl : v.invf.length = 10) (j n : Nat) (hj : j + n ≤ 10) (a : BitVec 64)
    (ha : a = dAc A.1.c 1 + 0x27#64 + BitVec.ofNat 64 j) :
    m.loadInt a n = some (Int.ofBytes ((v.invf.drop j).take n)) := by
  obtain ⟨R, hs, -⟩ := um_split1Iv k A ra t₀ Lc Sg st v []
  have hj' : (a - (dAc A.1.c 1 + 0x27#64)).toNat = j := by
    rw [ha, sub_base_add, BitVec.toNat_ofNat]; omega
  have := Val.loadInt_slice_split (n := n) h hs (by rw [hj', hl]; omega) (by rw [hl]; omega)
  rw [hj'] at this
  exact this

theorem um_split1Te (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) (Lc Sg : Mem 64 → Prop)
    (st : USt) (v : DV) (l : List UInt8) :
    ∃ R, Split (v.te =@ (dAc A.1.c 1 + 0x15a9c#64)) R (UM k A ra t₀ Lc Sg (st.wd1 v))
      ∧ Split (l =@ (dAc A.1.c 1 + 0x15a9c#64)) R
        (UM k A ra t₀ Lc Sg (st.wd1 { v with te := l })) := by
  simp only [UM, UF, DSc]
  exact ⟨_, Split.right (Split.right (Split.left (Split.right (Split.right (Split.right (Split.right
    (Split.left (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right
    (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right (Split.here _ _)
    _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _,
    Split.right (Split.right (Split.left (Split.right (Split.right (Split.right (Split.right
      (Split.left (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right
      (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right (Split.here _ _)
      _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _⟩

/-- A store inside channel 1's `te`. -/
theorem um_store1Te {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} {v : DV} (h : m =⋆ UM k A ra t₀ Lc Sg (st.wd1 v))
    (hl : v.te.length = 10) (j n : Nat) (hj : j + n ≤ 10) (a : BitVec 64)
    (ha : a = dAc A.1.c 1 + 0x15a9c#64 + BitVec.ofNat 64 j) (val : Int) :
    m.storeInt a n val =⋆ UM k A ra t₀ Lc Sg (st.wd1 { v with
      te := v.te.take j ++ Int.toBytes n val ++ v.te.drop (j + n) }) := by
  obtain ⟨R, hs, hs'⟩ := um_split1Te k A ra t₀ Lc Sg st v
    (v.te.take j ++ Int.toBytes n val ++ v.te.drop (j + n))
  rw [hs']
  have hj' : (a - (dAc A.1.c 1 + 0x15a9c#64)).toNat = j := by
    rw [ha, sub_base_add, BitVec.toNat_ofNat]; omega
  have := Val.storeInt_slice_split (n := n) h hs (by rw [hj', hl]; omega) (by rw [hl]; omega)
    val
  rw [hj'] at this
  exact this

/-- A load inside channel 1's `te`. -/
theorem um_load1Te {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} {v : DV} (h : m =⋆ UM k A ra t₀ Lc Sg (st.wd1 v))
    (hl : v.te.length = 10) (j n : Nat) (hj : j + n ≤ 10) (a : BitVec 64)
    (ha : a = dAc A.1.c 1 + 0x15a9c#64 + BitVec.ofNat 64 j) :
    m.loadInt a n = some (Int.ofBytes ((v.te.drop j).take n)) := by
  obtain ⟨R, hs, -⟩ := um_split1Te k A ra t₀ Lc Sg st v []
  have hj' : (a - (dAc A.1.c 1 + 0x15a9c#64)).toNat = j := by
    rw [ha, sub_base_add, BitVec.toNat_ofNat]; omega
  have := Val.loadInt_slice_split (n := n) h hs (by rw [hj', hl]; omega) (by rw [hl]; omega)
  rw [hj'] at this
  exact this

theorem um_split1Tq (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) (Lc Sg : Mem 64 → Prop)
    (st : USt) (v : DV) (l : List UInt8) :
    ∃ R, Split (v.tq =@ (dAc A.1.c 1 + 0x15aa6#64)) R (UM k A ra t₀ Lc Sg (st.wd1 v))
      ∧ Split (l =@ (dAc A.1.c 1 + 0x15aa6#64)) R
        (UM k A ra t₀ Lc Sg (st.wd1 { v with tq := l })) := by
  simp only [UM, UF, DSc]
  exact ⟨_, Split.right (Split.right (Split.left (Split.right (Split.right (Split.right (Split.right
    (Split.left (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right
    (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right
    (Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _,
    Split.right (Split.right (Split.left (Split.right (Split.right (Split.right (Split.right
      (Split.left (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right
      (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right
      (Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _⟩

/-- A store inside channel 1's `tq`. -/
theorem um_store1Tq {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} {v : DV} (h : m =⋆ UM k A ra t₀ Lc Sg (st.wd1 v))
    (hl : v.tq.length = 3) (j n : Nat) (hj : j + n ≤ 3) (a : BitVec 64)
    (ha : a = dAc A.1.c 1 + 0x15aa6#64 + BitVec.ofNat 64 j) (val : Int) :
    m.storeInt a n val =⋆ UM k A ra t₀ Lc Sg (st.wd1 { v with
      tq := v.tq.take j ++ Int.toBytes n val ++ v.tq.drop (j + n) }) := by
  obtain ⟨R, hs, hs'⟩ := um_split1Tq k A ra t₀ Lc Sg st v
    (v.tq.take j ++ Int.toBytes n val ++ v.tq.drop (j + n))
  rw [hs']
  have hj' : (a - (dAc A.1.c 1 + 0x15aa6#64)).toNat = j := by
    rw [ha, sub_base_add, BitVec.toNat_ofNat]; omega
  have := Val.storeInt_slice_split (n := n) h hs (by rw [hj', hl]; omega) (by rw [hl]; omega)
    val
  rw [hj'] at this
  exact this

/-- A load inside channel 1's `tq`. -/
theorem um_load1Tq {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} {v : DV} (h : m =⋆ UM k A ra t₀ Lc Sg (st.wd1 v))
    (hl : v.tq.length = 3) (j n : Nat) (hj : j + n ≤ 3) (a : BitVec 64)
    (ha : a = dAc A.1.c 1 + 0x15aa6#64 + BitVec.ofNat 64 j) :
    m.loadInt a n = some (Int.ofBytes ((v.tq.drop j).take n)) := by
  obtain ⟨R, hs, -⟩ := um_split1Tq k A ra t₀ Lc Sg st v []
  have hj' : (a - (dAc A.1.c 1 + 0x15aa6#64)).toNat = j := by
    rw [ha, sub_base_add, BitVec.toNat_ofNat]; omega
  have := Val.loadInt_slice_split (n := n) h hs (by rw [hj', hl]; omega) (by rw [hl]; omega)
  rw [hj'] at this
  exact this

theorem um_split0Fr (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) (Lc Sg : Mem 64 → Prop)
    (st : USt) :
    ∃ R, Split (st.x.d0.freqRes =@ (dAc A.1.c 0 + 0xc#64)) R (UM k A ra t₀ Lc Sg st) := by
  simp only [UM, UF, DSc]
  exact ⟨_, Split.right (Split.right (Split.left (Split.right (Split.right (Split.left (Split.right
    (Split.right (Split.right (Split.here _ _) _) _) _) _) _) _) _) _) _⟩

/-- A load inside channel 0's `freqRes`. -/
theorem um_load0Fr {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} (h : m =⋆ UM k A ra t₀ Lc Sg st)
    (hl : st.x.d0.freqRes.length = 9) (j n : Nat) (hj : j + n ≤ 9) (a : BitVec 64)
    (ha : a = dAc A.1.c 0 + 0xc#64 + BitVec.ofNat 64 j) :
    m.loadInt a n = some (Int.ofBytes ((st.x.d0.freqRes.drop j).take n)) := by
  obtain ⟨R, hs⟩ := um_split0Fr k A ra t₀ Lc Sg st
  have hj' : (a - (dAc A.1.c 0 + 0xc#64)).toNat = j := by
    rw [ha, sub_base_add, BitVec.toNat_ofNat]; omega
  have := Val.loadInt_slice_split (n := n) h hs (by rw [hj', hl]; omega) (by rw [hl]; omega)
  rw [hj'] at this
  exact this

theorem um_split0Iv (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) (Lc Sg : Mem 64 → Prop)
    (st : USt) :
    ∃ R, Split (st.x.d0.invf =@ (dAc A.1.c 0 + 0x27#64)) R (UM k A ra t₀ Lc Sg st) := by
  simp only [UM, UF, DSc]
  exact ⟨_, Split.right (Split.right (Split.left (Split.right (Split.right (Split.left (Split.right
    (Split.right (Split.right (Split.right (Split.right (Split.here _ _) _) _) _) _) _) _) _) _) _)
    _) _⟩

/-- A load inside channel 0's `invf`. -/
theorem um_load0Iv {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} (h : m =⋆ UM k A ra t₀ Lc Sg st)
    (hl : st.x.d0.invf.length = 10) (j n : Nat) (hj : j + n ≤ 10) (a : BitVec 64)
    (ha : a = dAc A.1.c 0 + 0x27#64 + BitVec.ofNat 64 j) :
    m.loadInt a n = some (Int.ofBytes ((st.x.d0.invf.drop j).take n)) := by
  obtain ⟨R, hs⟩ := um_split0Iv k A ra t₀ Lc Sg st
  have hj' : (a - (dAc A.1.c 0 + 0x27#64)).toNat = j := by
    rw [ha, sub_base_add, BitVec.toNat_ofNat]; omega
  have := Val.loadInt_slice_split (n := n) h hs (by rw [hj', hl]; omega) (by rw [hl]; omega)
  rw [hj'] at this
  exact this

theorem um_split0Te (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) (Lc Sg : Mem 64 → Prop)
    (st : USt) :
    ∃ R, Split (st.x.d0.te =@ (dAc A.1.c 0 + 0x15a9c#64)) R (UM k A ra t₀ Lc Sg st) := by
  simp only [UM, UF, DSc]
  exact ⟨_, Split.right (Split.right (Split.left (Split.right (Split.right (Split.left (Split.right
    (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right
    (Split.right (Split.right (Split.right (Split.right (Split.here _ _) _) _) _) _) _) _) _) _) _)
    _) _) _) _) _) _) _) _) _⟩

/-- A load inside channel 0's `te`. -/
theorem um_load0Te {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} (h : m =⋆ UM k A ra t₀ Lc Sg st)
    (hl : st.x.d0.te.length = 10) (j n : Nat) (hj : j + n ≤ 10) (a : BitVec 64)
    (ha : a = dAc A.1.c 0 + 0x15a9c#64 + BitVec.ofNat 64 j) :
    m.loadInt a n = some (Int.ofBytes ((st.x.d0.te.drop j).take n)) := by
  obtain ⟨R, hs⟩ := um_split0Te k A ra t₀ Lc Sg st
  have hj' : (a - (dAc A.1.c 0 + 0x15a9c#64)).toNat = j := by
    rw [ha, sub_base_add, BitVec.toNat_ofNat]; omega
  have := Val.loadInt_slice_split (n := n) h hs (by rw [hj', hl]; omega) (by rw [hl]; omega)
  rw [hj'] at this
  exact this

theorem um_split0Tq (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) (Lc Sg : Mem 64 → Prop)
    (st : USt) :
    ∃ R, Split (st.x.d0.tq =@ (dAc A.1.c 0 + 0x15aa6#64)) R (UM k A ra t₀ Lc Sg st) := by
  simp only [UM, UF, DSc]
  exact ⟨_, Split.right (Split.right (Split.left (Split.right (Split.right (Split.left (Split.right
    (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right
    (Split.right (Split.right (Split.right (Split.right (Split.right (Split.here _ _) _) _) _) _) _)
    _) _) _) _) _) _) _) _) _) _) _) _) _) _⟩

/-- A load inside channel 0's `tq`. -/
theorem um_load0Tq {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} (h : m =⋆ UM k A ra t₀ Lc Sg st)
    (hl : st.x.d0.tq.length = 3) (j n : Nat) (hj : j + n ≤ 3) (a : BitVec 64)
    (ha : a = dAc A.1.c 0 + 0x15aa6#64 + BitVec.ofNat 64 j) :
    m.loadInt a n = some (Int.ofBytes ((st.x.d0.tq.drop j).take n)) := by
  obtain ⟨R, hs⟩ := um_split0Tq k A ra t₀ Lc Sg st
  have hj' : (a - (dAc A.1.c 0 + 0x15aa6#64)).toNat = j := by
    rw [ha, sub_base_add, BitVec.toNat_ofNat]; omega
  have := Val.loadInt_slice_split (n := n) h hs (by rw [hj', hl]; omega) (by rw [hl]; omega)
  rw [hj'] at this
  exact this

theorem um_split1Ne (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) (Lc Sg : Mem 64 → Prop)
    (st : USt) (v : DV) (n : Nat) :
    ∃ R, Split (c4 (dAc A.1.c 1 + 0x8#64) v.nenv) R (UM k A ra t₀ Lc Sg (st.wd1 v))
      ∧ Split (c4 (dAc A.1.c 1 + 0x8#64) n) R
        (UM k A ra t₀ Lc Sg (st.wd1 { v with nenv := n })) := by
  simp only [UM, UF, DSc]
  exact ⟨_, Split.right (Split.right (Split.left (Split.right (Split.right (Split.right (Split.right
    (Split.left (Split.right (Split.right (Split.here _ _) _) _) _) _) _) _) _) _) _) _,
    Split.right (Split.right (Split.left (Split.right (Split.right (Split.right (Split.right
      (Split.left (Split.right (Split.right (Split.here _ _) _) _) _) _) _) _) _) _) _) _⟩

/-- A store of channel 1's `nenv`. -/
theorem um_store1Ne {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} {v : DV} (h : m =⋆ UM k A ra t₀ Lc Sg (st.wd1 v))
    (a : BitVec 64) (ha : a = dAc A.1.c 1 + 0x8#64) (val : Int) (n : Nat)
    (hv : Int.toBytes 4 val = Int.toBytes 4 (n : Int)) :
    m.storeInt a 4 val =⋆ UM k A ra t₀ Lc Sg (st.wd1 { v with nenv := n }) := by
  obtain ⟨R, hs, hs'⟩ := um_split1Ne k A ra t₀ Lc Sg st v n
  rw [hs', ha]
  have := Val.storeInt h hs (Int.toBytes_length 4 _) val
  rw [hv] at this
  exact this

/-- A load of channel 1's `nenv` succeeds. -/
theorem um_load1Ne {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} {v : DV} (h : m =⋆ UM k A ra t₀ Lc Sg (st.wd1 v))
    (a : BitVec 64) (ha : a = dAc A.1.c 1 + 0x8#64) :
    (m.loadInt a 4).isSome = true := by
  obtain ⟨R, hs, -⟩ := um_split1Ne k A ra t₀ Lc Sg st v 0
  exact Val.loadInt_isSome_slice h hs (by rw [ha, BitVec.sub_self, Int.toBytes_length]; simp)
    (by rw [Int.toBytes_length]; omega)

theorem um_split0Ne (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) (Lc Sg : Mem 64 → Prop)
    (st : USt) :
    ∃ R, Split (c4 (dAc A.1.c 0 + 0x8#64) st.x.d0.nenv) R (UM k A ra t₀ Lc Sg st) := by
  simp only [UM, UF, DSc]
  exact ⟨_, Split.right (Split.right (Split.left (Split.right (Split.right (Split.left (Split.right
    (Split.right (Split.here _ _) _) _) _) _) _) _) _) _⟩

/-- A load of channel 0's `nenv`. -/
theorem um_load0Ne {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} (h : m =⋆ UM k A ra t₀ Lc Sg st)
    (a : BitVec 64) (ha : a = dAc A.1.c 0 + 0x8#64) :
    m.loadInt a 4 = some (Int.ofBytes (Int.toBytes 4 (st.x.d0.nenv : Int))) := by
  obtain ⟨R, hs⟩ := um_split0Ne k A ra t₀ Lc Sg st
  have := Val.loadInt_slice_split (a := a) (n := 4) h hs
    (by rw [ha, BitVec.sub_self, Int.toBytes_length]; simp)
    (by rw [Int.toBytes_length]; omega)
  rw [ha, BitVec.sub_self, BitVec.toNat_zero, List.drop_zero,
    List.take_of_length_le (by rw [Int.toBytes_length]; exact Nat.le_refl _)] at this
  rw [ha]; exact this

theorem um_split1Nn (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) (Lc Sg : Mem 64 → Prop)
    (st : USt) (v : DV) (n : Nat) :
    ∃ R, Split (c4 (dAc A.1.c 1 + 0x18#64) v.nnoise) R (UM k A ra t₀ Lc Sg (st.wd1 v))
      ∧ Split (c4 (dAc A.1.c 1 + 0x18#64) n) R
        (UM k A ra t₀ Lc Sg (st.wd1 { v with nnoise := n })) := by
  simp only [UM, UF, DSc]
  exact ⟨_, Split.right (Split.right (Split.left (Split.right (Split.right (Split.right (Split.right
    (Split.left (Split.right (Split.right (Split.right (Split.right (Split.here _ _) _) _) _) _) _)
    _) _) _) _) _) _) _,
    Split.right (Split.right (Split.left (Split.right (Split.right (Split.right (Split.right
      (Split.left (Split.right (Split.right (Split.right (Split.right (Split.here _ _) _) _) _) _)
      _) _) _) _) _) _) _) _⟩

/-- A store of channel 1's `nnoise`. -/
theorem um_store1Nn {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} {v : DV} (h : m =⋆ UM k A ra t₀ Lc Sg (st.wd1 v))
    (a : BitVec 64) (ha : a = dAc A.1.c 1 + 0x18#64) (val : Int) (n : Nat)
    (hv : Int.toBytes 4 val = Int.toBytes 4 (n : Int)) :
    m.storeInt a 4 val =⋆ UM k A ra t₀ Lc Sg (st.wd1 { v with nnoise := n }) := by
  obtain ⟨R, hs, hs'⟩ := um_split1Nn k A ra t₀ Lc Sg st v n
  rw [hs', ha]
  have := Val.storeInt h hs (Int.toBytes_length 4 _) val
  rw [hv] at this
  exact this

/-- A load of channel 1's `nnoise` succeeds. -/
theorem um_load1Nn {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} {v : DV} (h : m =⋆ UM k A ra t₀ Lc Sg (st.wd1 v))
    (a : BitVec 64) (ha : a = dAc A.1.c 1 + 0x18#64) :
    (m.loadInt a 4).isSome = true := by
  obtain ⟨R, hs, -⟩ := um_split1Nn k A ra t₀ Lc Sg st v 0
  exact Val.loadInt_isSome_slice h hs (by rw [ha, BitVec.sub_self, Int.toBytes_length]; simp)
    (by rw [Int.toBytes_length]; omega)

theorem um_split0Nn (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) (Lc Sg : Mem 64 → Prop)
    (st : USt) :
    ∃ R, Split (c4 (dAc A.1.c 0 + 0x18#64) st.x.d0.nnoise) R (UM k A ra t₀ Lc Sg st) := by
  simp only [UM, UF, DSc]
  exact ⟨_, Split.right (Split.right (Split.left (Split.right (Split.right (Split.left (Split.right
    (Split.right (Split.right (Split.right (Split.here _ _) _) _) _) _) _) _) _) _) _) _⟩

/-- A load of channel 0's `nnoise`. -/
theorem um_load0Nn {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} (h : m =⋆ UM k A ra t₀ Lc Sg st)
    (a : BitVec 64) (ha : a = dAc A.1.c 0 + 0x18#64) :
    m.loadInt a 4 = some (Int.ofBytes (Int.toBytes 4 (st.x.d0.nnoise : Int))) := by
  obtain ⟨R, hs⟩ := um_split0Nn k A ra t₀ Lc Sg st
  have := Val.loadInt_slice_split (a := a) (n := 4) h hs
    (by rw [ha, BitVec.sub_self, Int.toBytes_length]; simp)
    (by rw [Int.toBytes_length]; omega)
  rw [ha, BitVec.sub_self, BitVec.toNat_zero, List.drop_zero,
    List.take_of_length_le (by rw [Int.toBytes_length]; exact Nat.le_refl _)] at this
  rw [ha]; exact this

theorem um_split1R0 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) (Lc Sg : Mem 64 → Prop)
    (st : USt) : ∃ R, Split (4 ?@ (dAc A.1.c 1)) R (UM k A ra t₀ Lc Sg st) := by
  simp only [UM, UF, DSc]
  exact ⟨_, Split.right (Split.right (Split.left (Split.right (Split.right (Split.right (Split.right
    (Split.left (Split.here _ _) _) _) _) _) _) _) _) _⟩

theorem um_load1R0 {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} (h : m =⋆ UM k A ra t₀ Lc Sg st)
    (a : BitVec 64) (ha : a = dAc A.1.c 1) :
    (m.loadInt a 4).isSome = true := by
  obtain ⟨R, hs⟩ := um_split1R0 k A ra t₀ Lc Sg st
  rw [hs] at h
  exact Block.loadInt_isSome h (by rw [ha, BitVec.sub_self]; simp)

theorem um_split0R0 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) (Lc Sg : Mem 64 → Prop)
    (st : USt) : ∃ R, Split (4 ?@ (dAc A.1.c 0)) R (UM k A ra t₀ Lc Sg st) := by
  simp only [UM, UF, DSc]
  exact ⟨_, Split.right (Split.right (Split.left (Split.right (Split.right (Split.left (Split.here _
    _) _) _) _) _) _) _⟩

theorem um_load0R0 {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} (h : m =⋆ UM k A ra t₀ Lc Sg st)
    (a : BitVec 64) (ha : a = dAc A.1.c 0) :
    (m.loadInt a 4).isSome = true := by
  obtain ⟨R, hs⟩ := um_split0R0 k A ra t₀ Lc Sg st
  rw [hs] at h
  exact Block.loadInt_isSome h (by rw [ha, BitVec.sub_self]; simp)

theorem um_store1R0 {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} (h : m =⋆ UM k A ra t₀ Lc Sg st)
    (a : BitVec 64) (ha : a = dAc A.1.c 1) (val : Int) :
    m.storeInt a 4 val =⋆ UM k A ra t₀ Lc Sg st := by
  obtain ⟨R, hs⟩ := um_split1R0 k A ra t₀ Lc Sg st
  exact Block.storeInt_split h hs (by rw [ha, BitVec.sub_self]; simp) val

theorem um_split1R64 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) (Lc Sg : Mem 64 → Prop)
    (st : USt) : ∃ R, Split (4 ?@ (dAc A.1.c 1 + 0x64#64)) R (UM k A ra t₀ Lc Sg st) := by
  simp only [UM, UF, DSc]
  exact ⟨_, Split.right (Split.right (Split.left (Split.right (Split.right (Split.right (Split.right
    (Split.left (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right
    (Split.right (Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _⟩

theorem um_load1R64 {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} (h : m =⋆ UM k A ra t₀ Lc Sg st)
    (a : BitVec 64) (ha : a = dAc A.1.c 1 + 0x64#64) :
    (m.loadInt a 4).isSome = true := by
  obtain ⟨R, hs⟩ := um_split1R64 k A ra t₀ Lc Sg st
  rw [hs] at h
  exact Block.loadInt_isSome h (by rw [ha, BitVec.sub_self]; simp)

theorem um_split0R64 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) (Lc Sg : Mem 64 → Prop)
    (st : USt) : ∃ R, Split (4 ?@ (dAc A.1.c 0 + 0x64#64)) R (UM k A ra t₀ Lc Sg st) := by
  simp only [UM, UF, DSc]
  exact ⟨_, Split.right (Split.right (Split.left (Split.right (Split.right (Split.left (Split.right
    (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right (Split.here _ _)
    _) _) _) _) _) _) _) _) _) _) _) _) _⟩

theorem um_load0R64 {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} (h : m =⋆ UM k A ra t₀ Lc Sg st)
    (a : BitVec 64) (ha : a = dAc A.1.c 0 + 0x64#64) :
    (m.loadInt a 4).isSome = true := by
  obtain ⟨R, hs⟩ := um_split0R64 k A ra t₀ Lc Sg st
  rw [hs] at h
  exact Block.loadInt_isSome h (by rw [ha, BitVec.sub_self]; simp)

theorem um_store1R64 {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} (h : m =⋆ UM k A ra t₀ Lc Sg st)
    (a : BitVec 64) (ha : a = dAc A.1.c 1 + 0x64#64) (val : Int) :
    m.storeInt a 4 val =⋆ UM k A ra t₀ Lc Sg st := by
  obtain ⟨R, hs⟩ := um_split1R64 k A ra t₀ Lc Sg st
  exact Block.storeInt_split h hs (by rw [ha, BitVec.sub_self]; simp) val

theorem um_split1R3904 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) (Lc Sg : Mem 64 → Prop)
    (st : USt) : ∃ R, Split (4 ?@ (dAc A.1.c 1 + 0x3904#64)) R (UM k A ra t₀ Lc Sg st) := by
  simp only [UM, UF, DSc]
  exact ⟨_, Split.right (Split.right (Split.left (Split.right (Split.right (Split.right (Split.right
    (Split.left (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right
    (Split.right (Split.right (Split.right (Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _)
    _) _) _) _⟩

theorem um_load1R3904 {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} (h : m =⋆ UM k A ra t₀ Lc Sg st)
    (a : BitVec 64) (ha : a = dAc A.1.c 1 + 0x3904#64) :
    (m.loadInt a 4).isSome = true := by
  obtain ⟨R, hs⟩ := um_split1R3904 k A ra t₀ Lc Sg st
  rw [hs] at h
  exact Block.loadInt_isSome h (by rw [ha, BitVec.sub_self]; simp)

theorem um_split0R3904 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) (Lc Sg : Mem 64 → Prop)
    (st : USt) : ∃ R, Split (4 ?@ (dAc A.1.c 0 + 0x3904#64)) R (UM k A ra t₀ Lc Sg st) := by
  simp only [UM, UF, DSc]
  exact ⟨_, Split.right (Split.right (Split.left (Split.right (Split.right (Split.left (Split.right
    (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right
    (Split.right (Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _⟩

theorem um_load0R3904 {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} (h : m =⋆ UM k A ra t₀ Lc Sg st)
    (a : BitVec 64) (ha : a = dAc A.1.c 0 + 0x3904#64) :
    (m.loadInt a 4).isSome = true := by
  obtain ⟨R, hs⟩ := um_split0R3904 k A ra t₀ Lc Sg st
  rw [hs] at h
  exact Block.loadInt_isSome h (by rw [ha, BitVec.sub_self]; simp)

theorem um_store1R3904 {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} (h : m =⋆ UM k A ra t₀ Lc Sg st)
    (a : BitVec 64) (ha : a = dAc A.1.c 1 + 0x3904#64) (val : Int) :
    m.storeInt a 4 val =⋆ UM k A ra t₀ Lc Sg st := by
  obtain ⟨R, hs⟩ := um_split1R3904 k A ra t₀ Lc Sg st
  exact Block.storeInt_split h hs (by rw [ha, BitVec.sub_self]; simp) val

theorem um_split1R3908 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) (Lc Sg : Mem 64 → Prop)
    (st : USt) : ∃ R, Split (4 ?@ (dAc A.1.c 1 + 0x3908#64)) R (UM k A ra t₀ Lc Sg st) := by
  simp only [UM, UF, DSc]
  exact ⟨_, Split.right (Split.right (Split.left (Split.right (Split.right (Split.right (Split.right
    (Split.left (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right
    (Split.right (Split.right (Split.right (Split.right (Split.here _ _) _) _) _) _) _) _) _) _) _)
    _) _) _) _) _) _) _) _) _⟩

theorem um_load1R3908 {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} (h : m =⋆ UM k A ra t₀ Lc Sg st)
    (a : BitVec 64) (ha : a = dAc A.1.c 1 + 0x3908#64) :
    (m.loadInt a 4).isSome = true := by
  obtain ⟨R, hs⟩ := um_split1R3908 k A ra t₀ Lc Sg st
  rw [hs] at h
  exact Block.loadInt_isSome h (by rw [ha, BitVec.sub_self]; simp)

theorem um_split0R3908 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) (Lc Sg : Mem 64 → Prop)
    (st : USt) : ∃ R, Split (4 ?@ (dAc A.1.c 0 + 0x3908#64)) R (UM k A ra t₀ Lc Sg st) := by
  simp only [UM, UF, DSc]
  exact ⟨_, Split.right (Split.right (Split.left (Split.right (Split.right (Split.left (Split.right
    (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right
    (Split.right (Split.right (Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _⟩

theorem um_load0R3908 {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} (h : m =⋆ UM k A ra t₀ Lc Sg st)
    (a : BitVec 64) (ha : a = dAc A.1.c 0 + 0x3908#64) :
    (m.loadInt a 4).isSome = true := by
  obtain ⟨R, hs⟩ := um_split0R3908 k A ra t₀ Lc Sg st
  rw [hs] at h
  exact Block.loadInt_isSome h (by rw [ha, BitVec.sub_self]; simp)

theorem um_store1R3908 {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} (h : m =⋆ UM k A ra t₀ Lc Sg st)
    (a : BitVec 64) (ha : a = dAc A.1.c 1 + 0x3908#64) (val : Int) :
    m.storeInt a 4 val =⋆ UM k A ra t₀ Lc Sg st := by
  obtain ⟨R, hs⟩ := um_split1R3908 k A ra t₀ Lc Sg st
  exact Block.storeInt_split h hs (by rw [ha, BitVec.sub_self]; simp) val

end Kraken.Examples.Sbr.Usac
