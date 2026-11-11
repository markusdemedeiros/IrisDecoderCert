import Kraken.X64.Examples.Sbr.Parse.TlimMem

/-!
# `sbr_make_f_tablelim`: entry and exit glue

`pre_glue`: the caller's reservation of `0x450 + k` bytes is the frame of `T` (the save slots,
the `AV_QSORT` stack, `patch_borders`, the untracked locals, the return slot of a call) and the
callee's `k`. `post_glue`: the footprint at the return is `TlimPost`.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.Tlim

theorem bsplit' (a b : BitVec 64) (i j : Nat) (hb : a + BitVec.ofNat 64 i = b)
    (hw : i + j ≤ 2 ^ 64) : ((i + j) ?@ a) = i ?@ a ⋆ j ?@ b := by
  rw [Block.split a i j hw, hb]

/-- The frame's `0x450` bytes as the routine's cells. -/
theorem frame_eq (r : BitVec 64) :
    (0x450 ?@ (r - 0x450#64)) = 8 ?@ (r - 0x450#64) ⋆ (1024 ?@ (r - 0x448#64) ⋆ (Junk r
      ⋆ (14 ?@ (r - 0x36#64) ⋆ (8 ?@ (r - 0x28#64) ⋆ (8 ?@ (r - 0x20#64) ⋆ (8 ?@ (r - 0x18#64)
      ⋆ (8 ?@ (r - 0x10#64) ⋆ 8 ?@ (r - 0x8#64)))))))) := by
  rw [bsplit' (r - 0x450#64) (r - 0x448#64) 8 0x448 (by bv_omega) (by omega),
    bsplit' (r - 0x448#64) (r - 0x48#64) 1024 0x48 (by bv_omega) (by omega),
    bsplit' (r - 0x48#64) (r - 0x3c#64) 12 0x3c (by bv_omega) (by omega),
    bsplit' (r - 0x3c#64) (r - 0x38#64) 4 0x38 (by bv_omega) (by omega),
    bsplit' (r - 0x38#64) (r - 0x36#64) 2 0x36 (by bv_omega) (by omega),
    bsplit' (r - 0x36#64) (r - 0x28#64) 14 0x28 (by bv_omega) (by omega),
    bsplit' (r - 0x28#64) (r - 0x20#64) 8 0x20 (by bv_omega) (by omega),
    bsplit' (r - 0x20#64) (r - 0x18#64) 8 0x18 (by bv_omega) (by omega),
    bsplit' (r - 0x18#64) (r - 0x10#64) 8 0x10 (by bv_omega) (by omega),
    bsplit' (r - 0x10#64) (r - 0x8#64) 8 8 (by bv_omega) (by omega)]
  simp only [Junk]; ac_rfl

variable [CodeEnv]

theorem pre_glue {k : Nat} {x : TArgs} {ra : Int64} {t : MachineData}
    (h : CallPre (tlimNeed k) (TlimF x.lb x.a t ⋆ x.R) ra t) :
    ∃ stk pb, stk.length = 1024 ∧ pb.length = 14
      ∧ (t.dmem =⋆ T k x ra t (BlankS (rS t)) (st0 x stk pb)) := by
  have hr : 0x450 ≤ (t.regs.get64 .rsp).toNat := by
    have := CallPre.le h; unfold tlimNeed at this; omega
  simp only [CallPre, tlimNeed] at h
  rw [Reserve_split 0x450 k _ hr] at h
  have e : t.regs.get64 .rsp - BitVec.ofNat 64 0x450 = t.regs.get64 .rsp - 0x450#64 := rfl
  rw [e, frame_eq] at h
  have h1 := Mem.ac h (H₂ := 1024 ?@ (t.regs.get64 .rsp - 0x448#64) ⋆ (14 ?@ (t.regs.get64 .rsp - 0x36#64)
    ⋆ (8 ?@ (t.regs.get64 .rsp - 0x450#64) ⋆ (Reserve k (t.regs.get64 .rsp - 0x450#64)
    ⋆ (Junk (t.regs.get64 .rsp) ⋆ (BlankS (t.regs.get64 .rsp) (RetCell ra (t.regs.get64 .rsp))
    ⋆ (TlimF x.lb x.a t ⋆ x.R)))))))
    (by simp only [BlankS]; ac_rfl)
  obtain ⟨-, stk, hs, h2⟩ := Block.sep_elim h1
  rw [Std.ExtHashMap.sep_comm_l] at h2
  obtain ⟨-, pb, hp, h3⟩ := Block.sep_elim h2
  refine ⟨stk, pb, hs, hp, Mem.ac h3 ?_⟩
  simp only [T, TlimF, RO, Rest, BlankS, Mem.Val.eq]; ac_rfl

end Kraken.Examples.Sbr.Tlim

namespace Kraken.Examples.Sbr.Tlim

variable [CodeEnv]

omit [CodeEnv] in
theorem fv {m : Mem 64} {bs : List UInt8} {a : BitVec 64} {F G : Mem 64 → Prop}
    (hw : bs.length ≤ 2 ^ 64) (h : m =⋆ (bs =@ a ⋆ F) ⋆ G) : m =⋆ F ⋆ (bs.length ?@ a ⋆ G) := by
  rw [Std.ExtHashMap.sep_assoc] at h
  have := Block.sep_intro rfl hw h
  rwa [Std.ExtHashMap.sep_comm_l] at this

theorem post_glue {k : Nat} {x : TArgs} {ra : Int64} {t₀ s : MachineData}
    (hc : CallPre (tlimNeed k) (TlimF x.lb x.a t₀ ⋆ x.R) ra t₀)
    (h : Post' k x ra t₀ s) : TlimPost k x ra t₀ s := by
  have hr : 0x450 ≤ (t₀.regs.get64 .rsp).toNat := by
    have := CallPre.le hc; unfold tlimNeed at this; omega
  obtain ⟨y, stk, pb, hT, hy, ⟨hfl, hs, hp⟩, hsp, hbp, hsv, hm⟩ := h
  refine ⟨y, hT, hsp, hbp, hsv, ?_⟩
  simp only at hfl hs hp
  have ekx : y.kx1 = x.a.kx1 := by rw [hy]
  have en0 : y.n0 = x.a.n0 := by rw [hy]
  have elo : y.ftLow = x.a.ftLow := by rw [hy]
  have enp : y.npatch = x.a.npatch := by rw [hy]
  have epn : y.pnum = x.a.pnum := by rw [hy]
  have h1 := Mem.ac hm (H₂ := (stk =@ (rS t₀ - 0x448#64) ⋆ (pb =@ (rS t₀ - 0x36#64)
    ⋆ (c8 (rS t₀ - 0x28#64) (t₀.regs.get64 .rbx) ⋆ (c8 (rS t₀ - 0x20#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (rS t₀ - 0x18#64) (t₀.regs.get64 .r14) ⋆ (c8 (rS t₀ - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (rS t₀ - 0x8#64) (t₀.regs.get64 .rbp)
    ⋆ (8 ?@ (rS t₀ - 0x450#64) ⋆ (Reserve k (rS t₀ - 0x450#64) ⋆ (Junk (rS t₀)
    ⋆ (TlimF x.lb y t₀ ⋆ x.R))))))))))) ⋆ 8 ?@ rS t₀)
    (by simp only [T, TlimF, RO, Saved, ekx, en0, elo, enp, epn, rS, sA, pA]; ac_rfl)
  have h8 := fv (by rw [Int.toBytes_length]; decide) (fv (by rw [Int.toBytes_length]; decide) (fv (by rw [Int.toBytes_length]; decide) (fv (by rw [Int.toBytes_length]; decide) (fv (by rw [Int.toBytes_length]; decide)
    (fv (by omega) (fv (by omega) h1))))))
  simp only [Int.toBytes_length, hs, hp] at h8
  simp only [tlimNeed]
  rw [Reserve_split 0x450 k _ hr]
  have e : t₀.regs.get64 .rsp - BitVec.ofNat 64 0x450 = t₀.regs.get64 .rsp - 0x450#64 := rfl
  rw [e, frame_eq]
  exact Mem.ac h8 (by simp only [Junk]; ac_rfl)

end Kraken.Examples.Sbr.Tlim
