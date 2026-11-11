import Kraken.X64.Examples.Sbr.Parse.NoiseFrame

/-!
# `read_sbr_noise`: the table reads of the `get_vlc2` walks

`vlc_at`: the entry `j` of table `K` (`sym` at `p + 4 j`, `len` at `p + 4 j + 2`) for an index
`j` the walk reaches (`VWalk`), from the footprint.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Vlc

namespace Kraken.Examples.Sbr.Noise

variable [CodeEnv]

variable {k : Nat} {Ext : Mem 64 → Prop} {x : NArgs} {ra : Int64} {t₀ : MachineData}
  {LF : Mem 64 → Prop} {FR : (Mem 64 → Prop) → Mem 64 → Prop} {i : BitVec 32} {m : Mem 64}

/-- The two loads of entry `j` (a 32-bit index) of table `K`, reached by a walk. -/
theorem vlc_at (h : m =⋆ T k Ext x ra t₀ LF FR i) (hC : VlcC x.v) (K : Nat) (hK : K < 10)
    (d : Nat) (j : BitVec 32) (hw : VWalk (x.v K).es d j.toNat) :
    m.loadInt ((x.v K).p + j.setWidth 64 * 4#64) 2
      = some (Int.ofBytes (((x.v K).es.drop (4 * j.toNat)).take 2))
    ∧ m.loadInt ((x.v K).p + j.setWidth 64 * 4#64 + 2#64) 2
      = some (Int.ofBytes (((x.v K).es.drop (4 * j.toNat + 2)).take 2)) := by
  obtain ⟨F, hF⟩ := T_vlcw h
  have hN := VWalk.lt hw
  have h28 : j.toNat < 2 ^ 28 := by
    have := (hC K hK).2.1; simp only [VlcTab.N] at this; omega
  exact ⟨vlc_load_sym hF hC K hK hN (vlc_addr _ j h28),
    vlc_load_len hF hC K hK hN (vlc_addr2 _ j h28)⟩

omit [CodeEnv] in
/-- The first-level index (the 9-bit window, zero-extended twice). -/
theorem win_walk (hC : VlcC x.v) (K : Nat) (hK : K < 10) (w : BitVec 64) (hw : w.toNat < 512) :
    VWalk (x.v K).es 3 (w.setWidth 32).toNat :=
  vlc_walk1 (hC K hK) (by rw [BitVec.toNat_setWidth]; omega)

omit [CodeEnv] in
theorem kt_lt : kt x t₀ < 10 := by simp only [kt, kb]; split <;> omega

omit [CodeEnv] in
theorem kf_lt : kf x t₀ < 10 := by simp only [kf, kb]; split <;> omega

omit [CodeEnv] in
/-- `movswl %r9w` of a zero-extended `sym`: back to `sym`. -/
theorem zs16 (y : BitVec 16) : BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32 y)) = y := by
  apply BitVec.eq_of_toNat_eq
  have := y.isLt
  simp only [BitVec.toNat_setWidth]
  omega

section Shr

variable {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop} {p : Program}

/-- `shr %cl, %r32`: the low 32 bits are the shifted value (count `%cl` mod 32); the upper
bits and the flags are forgotten (the second-level index of the walk). -/
theorem shr_cl32_lo (asz : Width) (r : Reg64) :
    ⦃ fun s => ∀ v : BitVec 64, ∀ st : StatusFlags,
        v.setWidth 32 = ((s.regs.get64 r).setWidth 32).ushiftRight ((s.regs.get64 .rcx).toNat % 256 % 32) →
        WP.wp p Q E { s with regs := s.regs.set64 r v, status := st } ⦄
      (Directive.instr (.regular asz .W32 (.shr (.reg (.low r .W32)) .cl)) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s hs => (MachineWP.shr_reg_cl_w32_spec (p := p) (Q := Q) (E := E) asz r).le_wp s
    (fun cf af of => by
      split
      · rename_i h0
        have h := hs (s.regs.get64 r) s.status (by rw [h0]; simp)
        rw [Kraken.Examples.Sbr.Parse.regs_set_get] at h; exact h
      · exact hs _ _ (by
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight]
          have := ((s.regs.get64 r).setWidth 32).isLt
          rw [Nat.mod_eq_of_lt (by
            have : (BitVec.setWidth 32 (s.regs.get64 r)).toNat >>> ((s.regs.get64 .rcx).toNat % 256 % 32)
                ≤ (BitVec.setWidth 32 (s.regs.get64 r)).toNat := Nat.shiftRight_le _ _
            simp only [BitVec.toNat_setWidth] at this ⊢; omega)]
          rw [Nat.mod_eq_of_lt (by
            have : (BitVec.setWidth 32 (s.regs.get64 r)).toNat >>> ((s.regs.get64 .rcx).toNat % 256 % 32)
                ≤ (BitVec.setWidth 32 (s.regs.get64 r)).toNat := Nat.shiftRight_le _ _
            simp only [BitVec.toNat_setWidth] at this ⊢; omega)]))

end Shr

end Kraken.Examples.Sbr.Noise
