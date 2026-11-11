import Kraken.X64.Examples.Sbr.Parse.EnvMem

/-!
# `read_sbr_envelope`: the stack frame against the reservation

At the return the six saved registers, the frame cells and the call slot are folded back into
the `0xb0` bytes at the top of the caller's reservation (`frame_fold`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Vlc

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.Env

/-- Merge the head block with the next piece (a block at its end once forgotten). -/
theorem fold_step {m : Mem 64} {a b : BitVec 64} {n k : Nat} {X F : Mem 64 → Prop}
    (hX : ∀ (m' : Mem 64) (F' : Mem 64 → Prop), (m' =⋆ X ⋆ F') → m' =⋆ k ?@ b ⋆ F')
    (hb : a + BitVec.ofNat 64 n = b) (hw : n + k ≤ 2 ^ 64) (h : m =⋆ n ?@ a ⋆ (X ⋆ F)) :
    m =⋆ (n + k) ?@ a ⋆ F := by
  rw [Std.ExtHashMap.sep_comm_l] at h
  have h2 := hX _ _ h
  rw [Std.ExtHashMap.sep_comm_l, ← Std.ExtHashMap.sep_assoc, ← hb] at h2
  rw [Block.split_at a (n + k) n (by omega) hw, Nat.add_sub_cancel_left]
  exact h2

theorem X8 {v b : BitVec 64} : ∀ (m' : Mem 64) (F' : Mem 64 → Prop),
    (m' =⋆ c8 b v ⋆ F') → m' =⋆ 8 ?@ b ⋆ F' :=
  fun _ _ h => Block.sep_intro (Int.toBytes_length _ _) (by decide) h

theorem X4 {b : BitVec 64} {v : BitVec 32} : ∀ (m' : Mem 64) (F' : Mem 64 → Prop),
    (m' =⋆ cell4 b v ⋆ F') → m' =⋆ 4 ?@ b ⋆ F' :=
  fun _ _ h => Block.sep_intro (Int.toBytes_length _ _) (by decide) h

theorem XB {b : BitVec 64} {k : Nat} : ∀ (m' : Mem 64) (F' : Mem 64 → Prop),
    (m' =⋆ k ?@ b ⋆ F') → m' =⋆ k ?@ b ⋆ F' :=
  fun _ _ h => h

/-- The frame cells in address order. -/
theorem frame_order (t₀ : MachineData) (fv : FV) (G : Mem 64 → Prop) :
    let r := t₀.regs.get64 .rsp
    Sv t₀ ⋆ (FrW r fv ⋆ (8 ?@ (r - 0xb0#64) ⋆ G))
      = 8 ?@ (r - 0xb0#64) ⋆ (8 ?@ (r - 0xa8#64) ⋆ (c8 (r - 0xa0#64) fv.f98
        ⋆ (c8 (r - 0x98#64) fv.f90 ⋆ (c8 (r - 0x90#64) fv.f88 ⋆ (c8 (r - 0x88#64) fv.f80
        ⋆ (c8 (r - 0x80#64) fv.f78 ⋆ (4 ?@ (r - 0x78#64) ⋆ (cell4 (r - 0x74#64) fv.f6c
        ⋆ (c8 (r - 0x70#64) fv.f68 ⋆ (c8 (r - 0x68#64) fv.f60 ⋆ (c8 (r - 0x60#64) fv.f58
        ⋆ (c8 (r - 0x58#64) fv.f50 ⋆ (c8 (r - 0x50#64) fv.f48 ⋆ (c8 (r - 0x48#64) fv.f40
        ⋆ (c8 (r - 0x40#64) fv.f38 ⋆ (8 ?@ (r - 0x38#64)
        ⋆ (c8 (r - 0x30#64) (t₀.regs.get64 .rbx) ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
        ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13) ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
        ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15) ⋆ (c8 (r - 8#64) (t₀.regs.get64 .rbp)
        ⋆ G)))))))))))))))))))))) := by
  simp only [Sv, FrW]
  ac_rfl

/-- The six pushes, the frame and the call slot are the top `0xb0` bytes. -/
theorem frame_fold {m : Mem 64} (t₀ : MachineData) (fv : FV) (G : Mem 64 → Prop)
    (h : m =⋆ Sv t₀ ⋆ (FrW (t₀.regs.get64 .rsp) fv ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xb0#64) ⋆ G))) :
    m =⋆ 0xb0 ?@ (t₀.regs.get64 .rsp - 0xb0#64) ⋆ G := by
  rw [frame_order] at h
  generalize t₀.regs.get64 .rsp = r at h ⊢
  have h := fold_step XB (by bv_omega) (by omega) h
  have h := fold_step X8 (by bv_omega) (by omega) h
  have h := fold_step X8 (by bv_omega) (by omega) h
  have h := fold_step X8 (by bv_omega) (by omega) h
  have h := fold_step X8 (by bv_omega) (by omega) h
  have h := fold_step X8 (by bv_omega) (by omega) h
  have h := fold_step XB (by bv_omega) (by omega) h
  have h := fold_step X4 (by bv_omega) (by omega) h
  have h := fold_step X8 (by bv_omega) (by omega) h
  have h := fold_step X8 (by bv_omega) (by omega) h
  have h := fold_step X8 (by bv_omega) (by omega) h
  have h := fold_step X8 (by bv_omega) (by omega) h
  have h := fold_step X8 (by bv_omega) (by omega) h
  have h := fold_step X8 (by bv_omega) (by omega) h
  have h := fold_step X8 (by bv_omega) (by omega) h
  have h := fold_step XB (by bv_omega) (by omega) h
  have h := fold_step X8 (by bv_omega) (by omega) h
  have h := fold_step X8 (by bv_omega) (by omega) h
  have h := fold_step X8 (by bv_omega) (by omega) h
  have h := fold_step X8 (by bv_omega) (by omega) h
  have h := fold_step X8 (by bv_omega) (by omega) h
  have h := fold_step X8 (by bv_omega) (by omega) h
  exact h

variable [CodeEnv]

/-- The return: the frame and the saved registers given back as the reservation. -/
theorem post_of (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64)
    (t₀ s : MachineData) (hp : EnvPre k Ext x ra t₀) (h : Post' k Ext x ra t₀ s) :
    EnvPost k Ext x ra t₀ s := by
  have hw : 0xb0 ≤ (t₀.regs.get64 .rsp).toNat := by
    have := CallPre.le hp.1; unfold envNeed at this; omega
  obtain ⟨gi, hO, hsp, hbp, hsv, fv, hm⟩ := h
  refine ⟨gi, hO, hsp, hbp, hsv, ?_⟩
  generalize EF Ext x t₀ gi ⋆ x.R = K at hm ⊢
  have e1 : 8 ?@ t₀.regs.get64 .rsp ⋆ (Sv t₀ ⋆ (FrW (t₀.regs.get64 .rsp) fv
      ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xb0#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0xb0#64) ⋆ K))))
      = Sv t₀ ⋆ (FrW (t₀.regs.get64 .rsp) fv ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xb0#64)
        ⋆ (Reserve k (t₀.regs.get64 .rsp - 0xb0#64) ⋆ (8 ?@ t₀.regs.get64 .rsp ⋆ K)))) := by
    ac_rfl
  rw [e1] at hm
  have h2 := frame_fold t₀ fv _ hm
  rw [envNeed, Reserve_split 0xb0 k _ hw]
  have e2 : 8 ?@ t₀.regs.get64 .rsp ⋆ ((0xb0 ?@ (t₀.regs.get64 .rsp - BitVec.ofNat 64 0xb0)
      ⋆ Reserve k (t₀.regs.get64 .rsp - BitVec.ofNat 64 0xb0)) ⋆ K)
      = 0xb0 ?@ (t₀.regs.get64 .rsp - 0xb0#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0xb0#64)
        ⋆ (8 ?@ t₀.regs.get64 .rsp ⋆ K)) := by
    ac_rfl
  rw [e2]
  exact h2

end Kraken.Examples.Sbr.Env
