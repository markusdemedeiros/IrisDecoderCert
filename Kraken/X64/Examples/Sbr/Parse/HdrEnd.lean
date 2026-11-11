import Kraken.X64.Examples.Sbr.Parse.HdrStep

/-!
# `read_sbr_header`: the epilogue

The pops read the saved registers back; the frame's contents are then forgotten (`FrB`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.Hdr

open Kraken.Examples.Sbr.HdrLib

theorem fg {m : Mem 64} {bs : List UInt8} {a : BitVec 64} {n : Nat} {F : Mem 64 → Prop}
    (hl : bs.length = n) (hn : n ≤ 8) (h : m =⋆ (bs =@ a) ⋆ F) : m =⋆ (n ?@ a) ⋆ F :=
  Block.sep_intro hl (by omega) h

theorem forget5 {m : Mem 64} {l1 l2 l3 t d : List UInt8} {a1 a2 a3 a4 a5 a6 a7 : BitVec 64}
    {G : Mem 64 → Prop} (h1 : l1.length = 8) (h2 : l2.length = 8) (h3 : l3.length = 8)
    (ht : t.length = 4) (hd : d.length = 2)
    (h : m =⋆ (l1 =@ a1 ⋆ (l2 =@ a2 ⋆ (l3 =@ a3 ⋆ (8 ?@ a4 ⋆ (2 ?@ a5 ⋆ (t =@ a6 ⋆ d =@ a7))))))
      ⋆ G) :
    m =⋆ (8 ?@ a1 ⋆ (8 ?@ a2 ⋆ (8 ?@ a3 ⋆ (8 ?@ a4 ⋆ (2 ?@ a5 ⋆ (4 ?@ a6 ⋆ 2 ?@ a7)))))) ⋆ G := by
  have s1 := fg h1 (by omega) (Mem.ac h : m =⋆ l1 =@ a1 ⋆ (l2 =@ a2 ⋆ l3 =@ a3 ⋆ 8 ?@ a4
    ⋆ 2 ?@ a5 ⋆ t =@ a6 ⋆ d =@ a7 ⋆ G))
  have s2 := fg h2 (by omega) (Mem.ac s1 : m =⋆ l2 =@ a2 ⋆ (8 ?@ a1 ⋆ l3 =@ a3 ⋆ 8 ?@ a4
    ⋆ 2 ?@ a5 ⋆ t =@ a6 ⋆ d =@ a7 ⋆ G))
  have s3 := fg h3 (by omega) (Mem.ac s2 : m =⋆ l3 =@ a3 ⋆ (8 ?@ a2 ⋆ 8 ?@ a1 ⋆ 8 ?@ a4
    ⋆ 2 ?@ a5 ⋆ t =@ a6 ⋆ d =@ a7 ⋆ G))
  have s4 := fg ht (by omega) (Mem.ac s3 : m =⋆ t =@ a6 ⋆ (8 ?@ a3 ⋆ 8 ?@ a2 ⋆ 8 ?@ a1 ⋆ 8 ?@ a4
    ⋆ 2 ?@ a5 ⋆ d =@ a7 ⋆ G))
  have s5 := fg hd (by omega) (Mem.ac s4 : m =⋆ d =@ a7 ⋆ (4 ?@ a6 ⋆ 8 ?@ a3 ⋆ 8 ?@ a2 ⋆ 8 ?@ a1
    ⋆ 8 ?@ a4 ⋆ 2 ?@ a5 ⋆ G))
  exact Mem.ac s5

theorem hdrOut_of {x : HArgs} {u : BitVec 32} {st : HSt} {ret : BitVec 32} (h : Out x u st)
    (hr : ret = st.i - x.idx) : HdrOut x u st ret := by
  obtain ⟨h1, h2, ⟨a1, a2, a3, a4, a5⟩, ⟨b1, b2, b3⟩, h5, ⟨c1, c2, c3, c4⟩, d1, d2⟩ := h
  exact ⟨h1, h2, a1, a2, a3, a4, a5, b1, b2, b3, h5, c1, c2, c3, c4, d1, d2, hr⟩

section End

variable {m : Mem 64} {u : BitVec 32} {k : Nat} {x : HArgs} {ra : Int64} {t₀ : MachineData}
  {st : HSt} {Tl : Mem 64 → Prop}

/-- The frame's contents forgotten. -/
theorem M_forget {sp : List UInt8} (hl : sp.length = 6)
    (h : m =⋆ MU u k x ra t₀ (Fr t₀ (Lsp t₀ sp)) st Tl) : m =⋆ MU u k x ra t₀ (FrB t₀) st Tl := by
  rw [M_fm] at h ⊢
  simp only [Fr, FrB, Lsp, L0, c8] at h ⊢
  exact forget5 (Int.toBytes_length _ _) (Int.toBytes_length _ _) (Int.toBytes_length _ _)
    (by simp [hl]) (by simp [hl]) h

/-- The pops: the saved registers. -/
theorem M_pop (Lc : Mem 64 → Prop) (h : m =⋆ MU u k x ra t₀ (Fr t₀ Lc) st Tl) :
    let r := t₀.regs.get64 .rsp
    m.loadInt (r - 0x8#64) 8 = some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 .rbp).toInt))
    ∧ m.loadInt (r - 0x10#64) 8 = some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 .r14).toInt))
    ∧ m.loadInt (r - 0x18#64) 8 = some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 .rbx).toInt)) := by
  intro r
  rw [M_fr] at h
  simp only [FrX] at h
  generalize Mx_fm u k x ra t₀ (Fr t₀ Lc) st Tl = G at h
  have k1 := Int.toBytes_length 8 (t₀.regs.get64 .rbp).toInt
  have k2 := Int.toBytes_length 8 (t₀.regs.get64 .r14).toInt
  have k3 := Int.toBytes_length 8 (t₀.regs.get64 .rbx).toInt
  generalize Int.toBytes 8 (t₀.regs.get64 .rbp).toInt = l1 at h k1 ⊢
  generalize Int.toBytes 8 (t₀.regs.get64 .r14).toInt = l2 at h k2 ⊢
  generalize Int.toBytes 8 (t₀.regs.get64 .rbx).toInt = l3 at h k3 ⊢
  refine ⟨?_, ?_, ?_⟩
  · have h' : m =⋆ l1 =@ (r - 0x8#64) ⋆ (Lc ⋆ l2 =@ (r - 0x10#64) ⋆ l3 =@ (r - 0x18#64)
        ⋆ 8 ?@ (r - 0x28#64) ⋆ 2 ?@ (r - 0x1a#64) ⋆ G) := Mem.ac h
    have e := loadInt_sep _ _ _ _ m h' rfl (by omega); rw [k1] at e; exact e
  · have h' : m =⋆ l2 =@ (r - 0x10#64) ⋆ (Lc ⋆ l1 =@ (r - 0x8#64) ⋆ l3 =@ (r - 0x18#64)
        ⋆ 8 ?@ (r - 0x28#64) ⋆ 2 ?@ (r - 0x1a#64) ⋆ G) := Mem.ac h
    have e := loadInt_sep _ _ _ _ m h' rfl (by omega); rw [k2] at e; exact e
  · have h' : m =⋆ l3 =@ (r - 0x18#64) ⋆ (Lc ⋆ l1 =@ (r - 0x8#64) ⋆ l2 =@ (r - 0x10#64)
        ⋆ 8 ?@ (r - 0x28#64) ⋆ 2 ?@ (r - 0x1a#64) ⋆ G) := Mem.ac h
    have e := loadInt_sep _ _ _ _ m h' rfl (by omega); rw [k3] at e; exact e

end End

end Kraken.Examples.Sbr.Hdr
