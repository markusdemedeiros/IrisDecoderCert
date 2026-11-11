import Kraken.X64.Examples.Sbr.Parse.EnvStack
import Kraken.X64.Examples.Sbr.Parse.EnvBlk1

/-!
# `read_sbr_envelope`: the prologue

The top `0xb0` bytes of the reservation are cut into the six push slots, the frame cells (with
whatever contents they have: the frame values `fv`) and the call slot (`frame_split`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Vlc

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Env

/-- An 8-byte block holds some 64-bit value. -/
theorem blk_c8 {m : Mem 64} {b : BitVec 64} {F : Mem 64 → Prop} (h : m =⋆ 8 ?@ b ⋆ F) :
    ∃ v : BitVec 64, m =⋆ c8 b v ⋆ F := by
  obtain ⟨-, bs, hlen, h'⟩ := Block.sep_elim h
  refine ⟨BitVec.ofInt 64 (Int.ofBytes bs), ?_⟩
  have e : Int.toBytes 8 (BitVec.ofInt 64 (Int.ofBytes bs)).toInt = bs := by
    rw [BitVec.toInt_ofInt]; exact Int.toBytes_bmod_ofBytes 8 bs hlen
  show m =⋆ (Int.toBytes 8 (BitVec.ofInt 64 (Int.ofBytes bs)).toInt =@ b) ⋆ F
  rw [e]; exact h'

/-- A 4-byte block holds some 32-bit value. -/
theorem blk_c4 {m : Mem 64} {b : BitVec 64} {F : Mem 64 → Prop} (h : m =⋆ 4 ?@ b ⋆ F) :
    ∃ v : BitVec 32, m =⋆ cell4 b v ⋆ F := by
  obtain ⟨-, bs, hlen, h'⟩ := Block.sep_elim h
  refine ⟨BitVec.ofInt 32 (Int.ofBytes bs), ?_⟩
  have e : Int.toBytes 4 (BitVec.ofInt 32 (Int.ofBytes bs)).toInt = bs := by
    rw [BitVec.toInt_ofInt]; exact Int.toBytes_bmod_ofBytes 4 bs hlen
  show m =⋆ (Int.toBytes 4 (BitVec.ofInt 32 (Int.ofBytes bs)).toInt =@ b) ⋆ F
  rw [e]; exact h'

/-- Cut the last `k` bytes off a block. -/
theorem peelB {m : Mem 64} {a b : BitVec 64} {F : Mem 64 → Prop} (n k : Nat) {N : Nat}
    (hN : N = n + k) (hb : a + BitVec.ofNat 64 n = b) (hw : N ≤ 2 ^ 64) (h : m =⋆ N ?@ a ⋆ F) :
    m =⋆ n ?@ a ⋆ (k ?@ b ⋆ F) := by
  subst hN
  rw [Block.split a n k hw, hb] at h
  exact Mem.ac h

theorem peel8 {m : Mem 64} {a b : BitVec 64} {F : Mem 64 → Prop} (n : Nat) {N : Nat}
    (hN : N = n + 8) (hb : a + BitVec.ofNat 64 n = b) (hw : N ≤ 2 ^ 64) (h : m =⋆ N ?@ a ⋆ F) :
    ∃ v, m =⋆ n ?@ a ⋆ (c8 b v ⋆ F) := by
  have h1 := peelB n 8 hN hb hw h
  have h2 : m =⋆ 8 ?@ b ⋆ (n ?@ a ⋆ F) := Mem.ac h1
  obtain ⟨v, h3⟩ := blk_c8 h2
  exact ⟨v, Mem.ac h3⟩

theorem peel4 {m : Mem 64} {a b : BitVec 64} {F : Mem 64 → Prop} (n : Nat) {N : Nat}
    (hN : N = n + 4) (hb : a + BitVec.ofNat 64 n = b) (hw : N ≤ 2 ^ 64) (h : m =⋆ N ?@ a ⋆ F) :
    ∃ v, m =⋆ n ?@ a ⋆ (cell4 b v ⋆ F) := by
  have h1 := peelB n 4 hN hb hw h
  have h2 : m =⋆ 4 ?@ b ⋆ (n ?@ a ⋆ F) := Mem.ac h1
  obtain ⟨v, h3⟩ := blk_c4 h2
  exact ⟨v, Mem.ac h3⟩

/-- The top `0xb0` bytes as the six push slots, the frame (some `fv`) and the call slot. -/
theorem frame_split {m : Mem 64} (r : BitVec 64) (G : Mem 64 → Prop)
    (h : m =⋆ 0xb0 ?@ (r - 0xb0#64) ⋆ G) :
    ∃ fv : FV, m =⋆ 8 ?@ (r - 8#64) ⋆ (8 ?@ (r - 0x10#64) ⋆ (8 ?@ (r - 0x18#64)
      ⋆ (8 ?@ (r - 0x20#64) ⋆ (8 ?@ (r - 0x28#64) ⋆ (8 ?@ (r - 0x30#64)
      ⋆ (FrW r fv ⋆ (8 ?@ (r - 0xb0#64) ⋆ G))))))) := by
  have h := peelB 0xa8 8 (b := r - 8#64) rfl (by bv_omega) (by omega) h
  have h := peelB 0xa0 8 (b := r - 0x10#64) rfl (by bv_omega) (by omega) h
  have h := peelB 0x98 8 (b := r - 0x18#64) rfl (by bv_omega) (by omega) h
  have h := peelB 0x90 8 (b := r - 0x20#64) rfl (by bv_omega) (by omega) h
  have h := peelB 0x88 8 (b := r - 0x28#64) rfl (by bv_omega) (by omega) h
  have h := peelB 0x80 8 (b := r - 0x30#64) rfl (by bv_omega) (by omega) h
  have h := peelB 0x78 8 (b := r - 0x38#64) rfl (by bv_omega) (by omega) h
  obtain ⟨v38, h⟩ := peel8 0x70 (b := r - 0x40#64) rfl (by bv_omega) (by omega) h
  obtain ⟨v40, h⟩ := peel8 0x68 (b := r - 0x48#64) rfl (by bv_omega) (by omega) h
  obtain ⟨v48, h⟩ := peel8 0x60 (b := r - 0x50#64) rfl (by bv_omega) (by omega) h
  obtain ⟨v50, h⟩ := peel8 0x58 (b := r - 0x58#64) rfl (by bv_omega) (by omega) h
  obtain ⟨v58, h⟩ := peel8 0x50 (b := r - 0x60#64) rfl (by bv_omega) (by omega) h
  obtain ⟨v60, h⟩ := peel8 0x48 (b := r - 0x68#64) rfl (by bv_omega) (by omega) h
  obtain ⟨v68, h⟩ := peel8 0x40 (b := r - 0x70#64) rfl (by bv_omega) (by omega) h
  obtain ⟨v6c, h⟩ := peel4 0x3c (b := r - 0x74#64) rfl (by bv_omega) (by omega) h
  have h := peelB 0x38 4 (b := r - 0x78#64) rfl (by bv_omega) (by omega) h
  obtain ⟨v78, h⟩ := peel8 0x30 (b := r - 0x80#64) rfl (by bv_omega) (by omega) h
  obtain ⟨v80, h⟩ := peel8 0x28 (b := r - 0x88#64) rfl (by bv_omega) (by omega) h
  obtain ⟨v88, h⟩ := peel8 0x20 (b := r - 0x90#64) rfl (by bv_omega) (by omega) h
  obtain ⟨v90, h⟩ := peel8 0x18 (b := r - 0x98#64) rfl (by bv_omega) (by omega) h
  obtain ⟨v98, h⟩ := peel8 0x10 (b := r - 0xa0#64) rfl (by bv_omega) (by omega) h
  have h := peelB 8 8 (b := r - 0xa8#64) rfl (by bv_omega) (by omega) h
  refine ⟨⟨v98, v90, v88, v80, v78, v6c, v68, v60, v58, v50, v48, v40, v38⟩, ?_⟩
  simp only [FrW]
  exact Mem.ac h

/-- A store over a whole 8-byte block fixes its contents. -/
theorem st8 {m : Mem 64} {a : BitVec 64} {F : Mem 64 → Prop} (h : m =⋆ 8 ?@ a ⋆ F) (v : BitVec 64) :
    m.storeInt a 8 v.toInt =⋆ c8 a v ⋆ F := by
  obtain ⟨-, bs, hlen, h'⟩ := Block.sep_elim h
  exact storeInt_sep a 8 bs F m ⟨h', hlen⟩ v.toInt

theorem st8' {m : Mem 64} {a : BitVec 64} {X F : Mem 64 → Prop} (h : m =⋆ X ⋆ (8 ?@ a ⋆ F))
    (v : BitVec 64) : m.storeInt a 8 v.toInt =⋆ (X ⋆ c8 a v) ⋆ F := by
  have h1 : m =⋆ 8 ?@ a ⋆ (X ⋆ F) := Mem.ac h
  exact Mem.ac (st8 h1 v)

theorem ld8 {m : Mem 64} {a : BitVec 64} {F : Mem 64 → Prop} (h : m =⋆ 8 ?@ a ⋆ F) :
    (m.loadInt a 8).isSome = true :=
  Block.loadInt_isSome h (by simp)

theorem ld8' {m : Mem 64} {a : BitVec 64} {X F : Mem 64 → Prop} (h : m =⋆ X ⋆ (8 ?@ a ⋆ F)) :
    (m.loadInt a 8).isSome = true :=
  ld8 (F := X ⋆ F) (Mem.ac h)

variable [CodeEnv]

theorem blk_entry (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "read_sbr_envelope" := by
  cfg_block
  measure_hb "entry"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨rfl, hC, hm⟩, hn⟩ := hs₀
    have hw : 0xb0 ≤ (s₀.regs.get64 .rsp).toNat := by
      have := (show envNeed k ≤ (s₀.regs.get64 .rsp).toNat by
        obtain ⟨_, _, _, _, _, _, _, _, _, h1, _⟩ := hm; exact h1.1)
      unfold envNeed at this; omega
    rw [envNeed, Reserve_split 0xb0 k _ hw] at hm
    have h0 : s₀.dmem =⋆ 0xb0 ?@ (s₀.regs.get64 .rsp - 0xb0#64)
        ⋆ (Reserve k (s₀.regs.get64 .rsp - 0xb0#64) ⋆ (EF Ext x s₀ x.idx ⋆ Rest x.R ra s₀)) := by
      simp only [Rest]; exact Mem.ac hm
    obtain ⟨fv, hF⟩ := frame_split _ _ h0
    clear hm h0
    have m1 := st8 hF (s₀.regs.get64 .rbp)
    have m2 := st8' m1 (s₀.regs.get64 .r15)
    have m3 := st8' m2 (s₀.regs.get64 .r14)
    have m4 := st8' m3 (s₀.regs.get64 .r13)
    have m5 := st8' m4 (s₀.regs.get64 .r12)
    have m6 := st8' m5 (s₀.regs.get64 .rbx)
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals try simp only [BitVec.sub_sub_eight, BitVec.reduceAdd] at *
    case vc1 => exact ld8 hF
    case vc2 => exact ld8' m1
    case vc3 => exact ld8' m2
    case vc4 => exact ld8' m3
    case vc5 => exact ld8' m4
    case vc6 => exact ld8' m5
    case vc7 =>
      refine ⟨⟨fv, ⟨⟨hC, ?_, ?_, hC.2.2.2.1, ?_⟩, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_⟩
      all_goals try dsimp only
      all_goals try rsimp
      all_goals try rfl
      case refine_3 =>
        simp only [T, Sv, Rest, EF, c8] at m6 ⊢
        exact Mem.ac m6
      case refine_1 =>
        rw [show BitVec.setWidth 64 (Int64.toBitVec 120) = 120#64 from rfl]; bv_omega
      case refine_9 =>
        rw [var_L57c1, var_entry]; exact Nat.le_refl _

end Kraken.Examples.Sbr.Env
