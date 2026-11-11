import Kraken.X64.Examples.Sbr.Parse.PsBase

/-!
# `ff_ps_read_data`: the entry and exit conversions

`ps_pre`: `PsPre` gives the table's assertion at the entry (`qEntry`: the reservation cut into
the frame's pieces). `ps_post`: `Post'` (the frame, at the return) gives `PsPost` (the frame
forgotten into the reservation).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Parse

namespace Kraken.Examples.Sbr.Ps

/-- The reservation of `ff_ps_read_data`, cut: the locals, the six pushes, the call slot, the
callee's `k`. -/
theorem ps_res (k : Nat) (r : BitVec 64) (hr : 0xb0 ≤ r.toNat) (X P R : Mem 64 → Prop) :
    X ⋆ (Reserve (0xb0 + k) r ⋆ (P ⋆ R))
      = 0x78 ?@ (r - 0xa8#64) ⋆ ((8 ?@ (r - 8#64) ⋆ (8 ?@ (r - 0x10#64) ⋆ (8 ?@ (r - 0x18#64)
        ⋆ (8 ?@ (r - 0x20#64) ⋆ (8 ?@ (r - 0x28#64) ⋆ 8 ?@ (r - 0x30#64))))))
        ⋆ (8 ?@ (r - 0xb0#64) ⋆ (Reserve k (r - 0xb0#64) ⋆ (P ⋆ (X ⋆ R))))) := by
  rw [Reserve_split 0xb0 k r hr]
  rw [show (0xb0 : Nat) = 8 + (8 + (8 + (8 + (8 + (8 + (0x78 + 8)))))) by omega]
  repeat rw [block_split_top _ _ _ (by omega)]
  simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd]
  ac_rfl

theorem ent_sep {X X' Y Y' : Mem 64 → Prop} (e1 : Mem.Entails X X') (e2 : Mem.Entails Y Y') :
    Mem.Entails (X ⋆ Y) (X' ⋆ Y') :=
  fun _ ⟨m₁, m₂, hd, hm, h₁, h₂⟩ => ⟨m₁, m₂, hd, hm, e1 _ h₁, e2 _ h₂⟩

theorem ent_val (bs : List UInt8) (a : BitVec 64) (n : Nat) (hl : bs.length = n)
    (hw : n ≤ 2 ^ 64) : Mem.Entails (bs =@ a) (n ?@ a) :=
  fun _ h => ⟨hw, bs, hl, h⟩

theorem ent_c8 (a v : BitVec 64) : Mem.Entails (cell8 a v) (8 ?@ a) :=
  ent_val _ a 8 (Int.toBytes_length 8 _) (by decide)

variable [CodeEnv]

theorem ps_pre (k : Nat) (Ext : Mem 64 → Prop) :
    ∀ x ra t, PsPre k Ext x ra t → table k Ext x ra t "ff_ps_read_data" t := by
  intro x ra t ⟨hm, hC⟩
  have hr : 0xb0 ≤ (t.regs.get64 .rsp).toNat := by
    have := CallPre.le hm; unfold psNeed at this; omega
  rw [tab_Entry]
  refine ⟨rfl, hC, ?_⟩
  simp only [CallPre] at hm
  rw [ps_res k _ hr] at hm
  exact hm

theorem ps_post (k : Nat) (Ext : Mem 64 → Prop) :
    ∀ x ra t₀ s, PsPre k Ext x ra t₀ → Post' k Ext x ra t₀ s → PsPost k Ext x ra t₀ s := by
  intro x ra t₀ s ⟨hcall, _⟩ ⟨c, i, f, hO, hfl, hsp, hbp, hS, hm⟩
  have hr : 0xb0 ≤ (t₀.regs.get64 .rsp).toNat := by
    have := CallPre.le hcall; unfold psNeed at this; omega
  refine ⟨c, i, hO, hsp, hbp, hS, ?_⟩
  rw [ps_res k _ hr]
  simp only [Fr] at hm
  refine (ent_sep (ent_val f _ 0x78 hfl (by decide)) (ent_sep ?_ (ent_sep (Mem.Entails.refl _)
    (ent_sep (Mem.Entails.refl _) (ent_sep (Mem.Entails.refl _)
      (ent_sep (ent_val _ _ 8 (Int.toBytes_length 8 _) (by decide)) (Mem.Entails.refl _))))))) _ hm
  exact ent_sep (ent_c8 _ _) (ent_sep (ent_c8 _ _) (ent_sep (ent_c8 _ _) (ent_sep (ent_c8 _ _)
    (ent_sep (ent_c8 _ _) (ent_c8 _ _)))))

end Kraken.Examples.Sbr.Ps
