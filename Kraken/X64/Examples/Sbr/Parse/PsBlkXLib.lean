import Kraken.X64.Examples.Sbr.Parse.PsFrame

/-!
# `ff_ps_read_data`, the extension: lemmas for the blocks of `PsBlkX*`

* Stores into `*ps` by the extension (`enable_ipdopd` at offset 48, the `ipd`/`opd` entries in
  `[416, 756)`) keep `PsInv` and `XI` (`XI_wr48`, `XI_wrpar`).
* The `ipd`/`opd` tables (`vlc_ps[6..9]`, depth 1): every 5-bit index is an entry, with
  `len ≥ 0` (`vlc1`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Parse

namespace Kraken.Examples.Sbr.Ps

/-! ## `inc %r32` (no `vcgen` rule for it in `Kraken.Rules`) -/

section
variable [CodeEnv] {p : Program} {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}

/-- `inc %r32`: the low half plus one, zero-extended. -/
@[spec] theorem inc_reg_w32_spec (asz : Width) (r : Reg64) :
    ⦃ fun s =>
        let a := (s.regs.get64 r).setWidth 32
        let v := a + 1
        WP.wp p Q E
          { s with
              regs := s.regs.set64 r (v.setWidth 64),
              status := StatusFlags.from_result v
                  { cf := s.status.cf,
                    af := (v.take 4).unsigned != (a.take 4).unsigned + 1,
                    of := v.signed != a.signed + 1 } } ⦄
      (Directive.instr (.regular asz .W32 (.inc (.reg (.low r .W32)))) :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by
    simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp,
      MachineData.set, MachineData.setReg, Effects.All]
    (try simp only [Reg64s.get_low32, Reg64s.set_low32])
    exact hP)

end


/-! ## Stores into `*ps` -/

theorem XI_wr48 {t₀ : MachineData} {x : PArgs} {c f : List UInt8} (v : Int)
    (hP : PsInv c) (hI : XI t₀ x c f) : PsInv (wr c 48 4 v) ∧ XI t₀ x (wr c 48 4 v) f := by
  have hl : c.length = 764 := hP.1
  have e32 : ∀ o', (o' + 4 ≤ 48 ∨ 52 ≤ o') → i32 (wr c 48 4 v) o' = i32 c o' :=
    fun o' hd => i32_wr c 48 4 o' v (by omega) hd
  have e8 : ∀ j, (j + 1 ≤ 48 ∨ 52 ≤ j) → i8 (wr c 48 4 v) j = i8 c j :=
    fun j hd => i8_wr c 48 4 j v (by omega) hd
  obtain ⟨hl', h12, h16, h28, h40, h44, h8⟩ := hP
  obtain ⟨⟨⟨n0, n4, n58, n38⟩, n34, n68, n40⟩, n1c, hG⟩ := hI
  refine ⟨⟨by rw [wr_length _ _ _ _ (by omega)]; exact hl', ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨⟨⟨?_, ?_, ?_, ?_⟩, ?_, n68, ?_⟩, ?_, ?_⟩⟩
  all_goals try simp only [ne, e32 12 (by omega), e32 16 (by omega), e32 28 (by omega),
    e32 40 (by omega), e32 44 (by omega), e32 8 (by omega), e32 4 (by omega),
    e32 20 (by omega)]
  all_goals try assumption
  intro hw
  obtain ⟨⟨r756, r8, ricc, rpar⟩, ⟨d0, d4, db0, dmono, d31⟩, hs, hb, hz⟩ := hG hw
  simp only [IidS, IidB, IidZ] at hs hb hz
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  all_goals try simp only [ne, bord, IidS, IidB, e32 756 (by omega), e32 8 (by omega),
    e32 44 (by omega), e32 52 (by omega), e32 0 (by omega), e32 4 (by omega), e32 12 (by omega)]
  all_goals try assumption
  · intro e he b hb'
    rw [e8 _ (by omega)]; exact ricc e he b hb'
  · intro e he b hb'
    rw [e8 _ (by omega), e8 _ (by omega)]; exact rpar e he b hb'
  · intro e he
    rw [e32 _ (by omega), e32 _ (by omega)]; exact dmono e he
  · intro e he
    rw [e32 _ (by omega)]; exact d31 e he
  · intro e he b hb' hc
    rw [e8 _ (by omega)]; exact hb e he b hb' hc
  · simp only [IidZ, IidB, e32 4 (by omega), e32 12 (by omega), e32 8 (by omega)]
    intro h4 e he b hb' hc
    rw [e8 _ (by omega)]; exact hz h4 e he b hb' hc

end Kraken.Examples.Sbr.Ps

namespace Kraken.Examples.Sbr.Ps

/-! ## The `ipd`/`opd` tables -/

/-- A depth-1 table: every 5-bit index is an entry with `len ≥ 0`. -/
theorem vlc1 {v : Nat → VlcTab} (hv : VlcC v) {j : Nat} (hj6 : 6 ≤ j) (hj : j < 10) {i : Nat}
    (hi : i < 32) :
    4 * i + 4 ≤ (v j).es.length ∧ (v j).es.length < 2 ^ 32 ∧ (vlen (v j).es i).msb = false := by
  have h := hv j hj
  have hb : vbits j = 5 := by simp only [vbits]; split <;> omega
  have hd : vdepth j = 1 := by simp only [vdepth]; split <;> (try split) <;> omega
  rw [hb, hd] at h
  obtain ⟨h4, hN, hw⟩ := h
  have hW := hw i (by omega)
  simp only [VWalk] at hW
  obtain ⟨hlt, hm⟩ := hW
  simp only [VlcTab.N] at hN
  refine ⟨by omega, by omega, ?_⟩
  rcases hm with hm | hm
  · exact hm
  · exact absurd (hm 0 (Nat.two_pow_pos _)) id

end Kraken.Examples.Sbr.Ps

namespace Kraken.Examples.Sbr.Ps

/-! ## The bit reader (copies of `LibGb`'s lemmas, which this chain does not import) -/

theorem xrd_off (i : BitVec 32) (p : BitVec 32) (L : Nat) (hi : i.toNat ≤ p.toNat)
    (hL : p.toNat / 8 + 4 ≤ L) : ((i.ushiftRight 3).setWidth 64).toNat + 4 ≤ L := by
  rw [BitVec.toNat_setWidth, BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight]
  have := i.isLt
  rw [Nat.mod_eq_of_lt (by omega)]; omega

theorem xshr_lt (v : BitVec 32) (n : Nat) (hn : n ≤ 32) : (v >>> (32 - n)).toNat < 2 ^ n := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := v.isLt
  apply Nat.div_lt_of_lt_mul
  rw [← Nat.pow_add, Nat.sub_add_cancel hn]; exact this

end Kraken.Examples.Sbr.Ps

namespace Kraken.Examples.Sbr.Ps

theorem zx_shr_lt (w : BitVec 32) (n : Nat) (hn : n ≤ 32) :
    (BitVec.setWidth 64 (w.ushiftRight n)).toNat < 2 ^ (32 - n) := by
  simp only [BitVec.toNat_setWidth, BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  have := w.isLt
  have h2 : 2 ^ (32 - n) * 2 ^ n = 2 ^ 32 := by rw [← Nat.pow_add]; congr 1; omega
  have h3 : w.toNat / 2 ^ n < 2 ^ (32 - n) :=
    Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm, h2]; exact this)
  have h4 : 2 ^ (32 - n) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) (by omega)
  rw [Nat.mod_eq_of_lt (by omega)]; exact h3

end Kraken.Examples.Sbr.Ps

namespace Kraken.Examples.Sbr.Ps

variable [CodeEnv]

/-- `XB` depends on the state only through the memory and `rsp`, `rbp`, `r13`, `r12`. -/
theorem XB_regs {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64} {t₀ s s' : MachineData}
    {c f : List UInt8} (h : XB k Ext x ra t₀ s c f) (hm : s'.dmem = s.dmem)
    (hsp : s'.regs.get64 .rsp = s.regs.get64 .rsp) (hbp : s'.regs.get64 .rbp = s.regs.get64 .rbp)
    (h13 : s'.regs.get64 .r13 = s.regs.get64 .r13) (h12 : s'.regs.get64 .r12 = s.regs.get64 .r12) :
    XB k Ext x ra t₀ s' c f := by
  obtain ⟨⟨hC, ⟨a1, a2, a3⟩, hm'⟩, ⟨r1, r2⟩, hI⟩ := h
  exact ⟨⟨hC, ⟨by rw [hsp]; exact a1, by rw [hbp]; exact a2, a3⟩, by rw [hm]; exact hm'⟩,
    ⟨by rw [h13]; exact r1, by rw [h12]; exact r2⟩, hI⟩

omit [CodeEnv] in
theorem xrd_wr_self (l : List UInt8) (o n w : Nat) (v : Int) (h : o + n ≤ l.length)
    (hw : w = 8 * n) : BitVec.ofInt w (rd (wr l o n v) o n) = BitVec.ofInt w v := by
  rw [rd_wr_same l o n v h, BitVec.ofInt_ofBytes_toBytes_eq w n hw]

omit [CodeEnv] in
/-- The low half of a small 8-byte slot. -/
theorem rd_lo4 (f : List UInt8) (o : Nat) (v : Int) (hl : o + 8 ≤ f.length) (h : rd f o 8 = v)
    (hv : v < 2 ^ 32) : rd f o 4 = v := by
  have e : (f.drop o).take 8 = (f.drop o).take 4 ++ ((f.drop o).drop 4).take 4 :=
    by rw [show (8 : Nat) = 4 + 4 from rfl, List.take_add]
  have hl4 : ((f.drop o).take 4).length = 4 := by simp only [List.length_take, List.length_drop]; omega
  simp only [rd] at h ⊢
  rw [e, Int.ofBytes_append, hl4] at h
  have a1 := Int.ofBytes_ge_zero ((f.drop o).take 4)
  have a2 := Int.ofBytes_ge_zero (((f.drop o).drop 4).take 4)
  have a3 := Int.ofBytes_lt ((f.drop o).take 4)
  rw [hl4] at a3
  have a4 := a2
  omega

omit [CodeEnv] in
/-- `num_env ∈ [0, 4]` zero-extended. -/
theorem zx_ofInt_small (z : Int) (h0 : 0 ≤ z) (h4 : z ≤ 4) :
    BitVec.setWidth 64 (BitVec.ofInt 32 z) = BitVec.ofNat 64 z.toNat := by
  have : z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 3 ∨ z = 4 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The frame slots `Bs`, `LSlots` and `XI` read: `(offset, width)`. -/
abbrev fslots : List (Nat × Nat) :=
  [(0x74, 4), (0x08, 8), (0x14, 4), (0x58, 8), (0x38, 8), (0x34, 4), (0x68, 8), (0x40, 8),
    (0x1c, 4), (0x18, 4)]

/-- A store into a frame slot outside `fslots` keeps `XB`. -/
theorem XB_wrf {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64} {t₀ s s' : MachineData}
    {c f : List UInt8} (h : XB k Ext x ra t₀ s c f) (o n : Nat) (v : Int) (hin : o + n ≤ 0x78)
    (hd : ∀ p ∈ fslots, p.1 + p.2 ≤ o ∨ o + n ≤ p.1)
    (hm : s'.dmem = s.dmem.storeInt (rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 o) n v)
    (hsp : s'.regs.get64 .rsp = s.regs.get64 .rsp) (hbp : s'.regs.get64 .rbp = s.regs.get64 .rbp)
    (h13 : s'.regs.get64 .r13 = s.regs.get64 .r13) (h12 : s'.regs.get64 .r12 = s.regs.get64 .r12) :
    XB k Ext x ra t₀ s' c (wr f o n v) := by
  obtain ⟨⟨hC, ⟨a1, a2, a3, a4, a5, a6, a7⟩, hm'⟩, ⟨r1, r2⟩, hI⟩ := h
  have e : ∀ p ∈ fslots, rd (wr f o n v) p.1 p.2 = rd f p.1 p.2 :=
    fun p hp => rd_wr f o n p.1 p.2 v (by omega) (hd p hp)
  obtain ⟨⟨⟨n0, n4, n58, n38⟩, n34, n68, n40⟩, n1c, hG⟩ := hI
  refine ⟨⟨hC, ⟨by rw [hsp]; exact a1, by rw [hbp]; exact a2, ?_, a4, ?_, ?_, ?_⟩, ?_⟩,
    ⟨by rw [h13]; exact r1, by rw [h12]; exact r2⟩,
    ⟨⟨⟨n0, n4, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_⟩⟩
  · rw [wr_length _ _ _ _ (by omega)]; exact a3
  · rw [e (0x74, 4) (by decide)]; exact a5
  · rw [e (0x08, 8) (by decide)]; exact a6
  · rw [e (0x14, 4) (by decide)]; exact a7
  · rw [hm]; exact Fr_f_store hm' a3 o n hin v
  · rw [e (0x58, 8) (by decide)]; exact n58
  · rw [e (0x38, 8) (by decide)]; exact n38
  · rw [e (0x34, 4) (by decide)]; exact n34
  · rw [e (0x68, 8) (by decide)]; exact n68
  · rw [e (0x40, 8) (by decide)]; exact n40
  · rw [e (0x1c, 4) (by decide)]; exact n1c
  · rw [e (0x18, 4) (by decide)]; exact hG

/-- The `enable_ipdopd` store (`*ps` offset 48) keeps `XB`. -/
theorem XB_wrc48 {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64} {t₀ s s' : MachineData}
    {c f : List UInt8} (h : XB k Ext x ra t₀ s c f) (v : Int)
    (hm : s'.dmem = s.dmem.storeInt (arg2 t₀ + BitVec.ofNat 64 48) 4 v)
    (hsp : s'.regs.get64 .rsp = s.regs.get64 .rsp) (hbp : s'.regs.get64 .rbp = s.regs.get64 .rbp)
    (h13 : s'.regs.get64 .r13 = s.regs.get64 .r13) (h12 : s'.regs.get64 .r12 = s.regs.get64 .r12) :
    XB k Ext x ra t₀ s' (wr c 48 4 v) f := by
  obtain ⟨⟨hC, ⟨a1, a2, a3, a4, a5, a6, a7⟩, hm'⟩, ⟨r1, r2⟩, hI⟩ := h
  have hw := XI_wr48 v a4 hI
  exact ⟨⟨hC, ⟨by rw [hsp]; exact a1, by rw [hbp]; exact a2, a3, hw.1, a5, a6, a7⟩,
    by rw [hm]; exact Fr_c_store hm' a4.1 48 4 (by omega) v⟩,
    ⟨by rw [h13]; exact r1, by rw [h12]; exact r2⟩, hw.2⟩

/-- A 4-byte frame slot as `slot32` sees it. -/
theorem slot32_Fr {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64} {t₀ s : MachineData}
    {c f : List UInt8} {i : BitVec 32} (hm : s.dmem =⋆ Fr k Ext x ra t₀ f c i)
    (hfl : f.length = 0x78) (hbp : s.regs.get64 .rbp = rsp0 t₀ - 8#64) (o : Nat)
    (ho : o + 4 ≤ 0x78) :
    slot32 s (0xa0 - o) = BitVec.ofInt 32 (rd f o 4) := by
  apply slot32_of_load
  have e : s.regs.get64 .rbp - BitVec.ofNat 64 (0xa0 - o) = rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 o := by
    rw [hbp]; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [e]; exact Fr_f_load hm hfl o 4 ho

/-- An 8-byte frame slot as `slot64` sees it. -/
theorem slot64_Fr {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64} {t₀ s : MachineData}
    {c f : List UInt8} {i : BitVec 32} (hm : s.dmem =⋆ Fr k Ext x ra t₀ f c i)
    (hfl : f.length = 0x78) (hbp : s.regs.get64 .rbp = rsp0 t₀ - 8#64) (o : Nat)
    (ho : o + 8 ≤ 0x78) :
    slot64 s (0xa0 - o) = BitVec.ofInt 64 (rd f o 8) := by
  apply slot64_of_load
  have e : s.regs.get64 .rbp - BitVec.ofNat 64 (0xa0 - o) = rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 o := by
    rw [hbp]; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [e]; exact Fr_f_load hm hfl o 8 ho


/-- The two stores of `0xdc6` (`enable_ipdopd`, the count slot) keep `XB` and `XL`; the count
slot then holds `cnt`. -/
theorem XB_dc6 {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64} {t₀ s s' : MachineData}
    {c f : List UInt8} (h : XB k Ext x ra t₀ s c f) (hL : XL t₀ c f) (v : Int) (w : BitVec 32)
    (hw : 8 ≤ w.toInt)
    (hm : s'.dmem = (s.dmem.storeInt (arg2 t₀ + BitVec.ofNat 64 48) 4 v).storeInt
      (rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 0x20) 4 w.toInt)
    (hsp : s'.regs.get64 .rsp = s.regs.get64 .rsp) (hbp : s'.regs.get64 .rbp = s.regs.get64 .rbp)
    (h13 : s'.regs.get64 .r13 = s.regs.get64 .r13) (h12 : s'.regs.get64 .r12 = s.regs.get64 .r12) :
    XB k Ext x ra t₀ s' (wr c 48 4 v) (wr f 0x20 4 w.toInt)
    ∧ XL t₀ (wr c 48 4 v) (wr f 0x20 4 w.toInt) ∧ XN (wr f 0x20 4 w.toInt)
    ∧ slot32 s' 0x80 = w ∧ ne (wr c 48 4 v) = ne c := by
  have hcl : c.length = 764 := h.1.2.1.2.2.2.1.1
  have hfl : f.length = 0x78 := h.1.2.1.2.2.1
  have h1 := XB_wrc48 (s' := ({ s with dmem := s.dmem.storeInt (arg2 t₀ + BitVec.ofNat 64 48) 4 v } : MachineData)) h v rfl rfl rfl rfl rfl
  have h2 := XB_wrf h1 0x20 4 w.toInt (by omega) (by decide) hm hsp hbp h13 h12
  have hne : ne (wr c 48 4 v) = ne c := i32_wr c 48 4 44 v (by omega) (Or.inl (by omega))
  have e1 : ∀ o', o' + 8 ≤ 0x20 ∨ 0x24 ≤ o' → rd (wr f 0x20 4 w.toInt) o' 8 = rd f o' 8 :=
    fun o' ho => rd_wr f 0x20 4 o' 8 _ (by omega) ho
  have hs : BitVec.ofInt 32 (rd (wr f 0x20 4 w.toInt) 0x20 4) = w := by
    rw [xrd_wr_self _ 0x20 4 32 _ (by omega) rfl, BitVec.ofInt_toInt]
  refine ⟨h2, ⟨⟨?_, ?_⟩, ?_⟩, ?_, ?_, hne⟩
  · rw [e1 0x50 (by omega)]; exact hL.1.1
  · rw [e1 0x28 (by omega)]; exact hL.1.2
  · rw [e1 0x48 (by omega), hne]; exact hL.2
  · show 8 ≤ (BitVec.ofInt 32 (rd (wr f 0x20 4 w.toInt) 0x20 4)).toInt
    rw [hs]; exact hw
  · have := slot32_Fr h2.1.2.2 h2.1.2.1.2.2.1 h2.1.2.1.2.1 0x20 (by omega)
    rw [hs] at this; exact this


theorem dc6_d50 {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64} {t₀ s s' : MachineData}
    {c f : List UInt8} (h : XB k Ext x ra t₀ s c f) (hL : XL t₀ c f) (v : Int) (w : BitVec 32)
    (hw : 8 ≤ w.toInt)
    (hm : s'.dmem = (s.dmem.storeInt (arg2 t₀ + BitVec.ofNat 64 48) 4 v).storeInt
      (rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 0x20) 4 w.toInt)
    (hsp : s'.regs.get64 .rsp = s.regs.get64 .rsp) (hbp : s'.regs.get64 .rbp = s.regs.get64 .rbp)
    (h13 : s'.regs.get64 .r13 = s.regs.get64 .r13) (h12 : s'.regs.get64 .r12 = s.regs.get64 .r12)
    (hJ : XJ x s' (s'.regs.get64 .rdx)) : qd50 k Ext x ra t₀ s' :=
  have H := XB_dc6 h hL v w hw hm hsp hbp h13 h12
  ⟨_, _, H.1, H.2.1, H.2.2.1, hJ⟩

theorem dc6_dd8 {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64} {t₀ s s' : MachineData}
    {c f : List UInt8} (h : XB k Ext x ra t₀ s c f) (hL : XL t₀ c f) (v : Int) (w : BitVec 32)
    (hw : 8 ≤ w.toInt)
    (hm : s'.dmem = (s.dmem.storeInt (arg2 t₀ + BitVec.ofNat 64 48) 4 v).storeInt
      (rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 0x20) 4 w.toInt)
    (hsp : s'.regs.get64 .rsp = s.regs.get64 .rsp) (hbp : s'.regs.get64 .rbp = s.regs.get64 .rbp)
    (h13 : s'.regs.get64 .r13 = s.regs.get64 .r13) (h12 : s'.regs.get64 .r12 = s.regs.get64 .r12)
    (hR : XR x t₀ s' c) (hJ : XJ x s' (s'.regs.get64 .rdx)) : qdd8 k Ext x ra t₀ s' :=
  have H := XB_dc6 h hL v w hw hm hsp hbp h13 h12
  ⟨_, _, H.1, ⟨hR.1, by rw [H.2.2.2.2]; exact hR.2.1, hR.2.2⟩, H.2.1, H.2.2.1, hJ⟩

theorem dc6_slot {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64} {t₀ s s' : MachineData}
    {c f : List UInt8} (h : XB k Ext x ra t₀ s c f) (hL : XL t₀ c f) (v : Int) (w : BitVec 32)
    (hw : 8 ≤ w.toInt)
    (hm : s'.dmem = (s.dmem.storeInt (arg2 t₀ + BitVec.ofNat 64 48) 4 v).storeInt
      (rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 0x20) 4 w.toInt)
    (hsp : s'.regs.get64 .rsp = s.regs.get64 .rsp) (hbp : s'.regs.get64 .rbp = s.regs.get64 .rbp)
    (h13 : s'.regs.get64 .r13 = s.regs.get64 .r13) (h12 : s'.regs.get64 .r12 = s.regs.get64 .r12) :
    (slot32 s' 0x80).toInt.toNat = w.toInt.toNat := by
  rw [(XB_dc6 h hL v w hw hm hsp hbp h13 h12).2.2.2.1]


end Kraken.Examples.Sbr.Ps

/-- The normalisation of `vcgen`'s states the extension blocks use (goal only). -/
macro "xsimp" : tactic => `(tactic| simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
    AddrIndex.offset64_scale1, AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm,
    Int64.toBitVec_ofNat_lit, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
    Int64.toBitVec_neg_ofNat_norm, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
    BitVec.setWidth_32_64_32, ite_true, ite_false])

/-- `xsimp` at a hypothesis (a load's address and value). -/
macro "xsimp_at " h:ident : tactic => `(tactic| simp only [reduceCtorEq, ↓reduceIte,
    Reg64s.get64_set64, AddrIndex.offset64_scale1, AddrIndex.offset64_none,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_ofNat_lit, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
    Int64.toBitVec_neg_ofNat_norm, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
    BitVec.setWidth_32_64_32, ite_true, ite_false] at $h:ident)

namespace Kraken.Examples.Sbr.Ps

/-- `index' = min(index + d, plus8)` (`add $d; cmp; cmovb`), as `vcgen` leaves it: a reader
index again, at least the old one. -/
theorem ix_clamp (x : PArgs) (r d : BitVec 64) (hd : (BitVec.setWidth 32 d).toNat ≤ 256) (hr : Ix x r)
    (hp : x.p8.toNat < 2 ^ 31) (hi : x.idx.toNat ≤ x.p8.toNat) (af of : Bool) :
    Ix x (BitVec.setWidth 64 (if CondCode.c.interp (StatusFlags.from_result
        (x.p8 - (BitVec.setWidth 32 d + BitVec.setWidth 32 r))
        { cf := (x.p8 - (BitVec.setWidth 32 d + BitVec.setWidth 32 r)).unsigned !=
            x.p8.unsigned - (BitVec.setWidth 32 d + BitVec.setWidth 32 r).unsigned,
          af := af, of := of }) = true
      then x.p8 else BitVec.setWidth 32 d + BitVec.setWidth 32 r))
    ∧ r.toNat ≤ (BitVec.setWidth 64 (if CondCode.c.interp (StatusFlags.from_result
        (x.p8 - (BitVec.setWidth 32 d + BitVec.setWidth 32 r))
        { cf := (x.p8 - (BitVec.setWidth 32 d + BitVec.setWidth 32 r)).unsigned !=
            x.p8.unsigned - (BitVec.setWidth 32 d + BitVec.setWidth 32 r).unsigned,
          af := af, of := of }) = true
      then x.p8 else BitVec.setWidth 32 d + BitVec.setWidth 32 r)).toNat := by
  obtain ⟨h1, h2⟩ := hr
  have e : (BitVec.setWidth 32 d + BitVec.setWidth 32 r).toNat
      = (BitVec.setWidth 32 d).toNat + r.toNat := by
    have : (BitVec.setWidth 32 r).toNat = r.toNat % 2 ^ 32 := by simp [BitVec.toNat_setWidth]
    have := (BitVec.setWidth 32 d).isLt
    rw [BitVec.toNat_add]; omega
  have h64 : ∀ y : BitVec 32, (BitVec.setWidth 64 y).toNat = y.toNat := fun y => by
    rw [BitVec.toNat_setWidth]; have := y.isLt; omega
  simp only [Ix, h64]
  split
  · have := x.p8.isLt
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> omega
  · rename_i h
    simp only [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, bne_iff_ne, ne_eq,
      Decidable.not_not] at h
    rw [BitVec.toNat_sub] at h
    rw [e] at h ⊢
    have := x.p8.isLt
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> omega

/-- `ix_clamp` with the addends swapped (`add %r8d,%eax`). -/
theorem x_ix_clamp2 (x : PArgs) (r d : BitVec 64) (hd : (BitVec.setWidth 32 d).toNat ≤ 256)
    (hr : Ix x r) (hp : x.p8.toNat < 2 ^ 31) (hi : x.idx.toNat ≤ x.p8.toNat) (af of : Bool) :
    Ix x (BitVec.setWidth 64 (if CondCode.c.interp (StatusFlags.from_result
        (x.p8 - (BitVec.setWidth 32 r + BitVec.setWidth 32 d))
        { cf := (x.p8 - (BitVec.setWidth 32 r + BitVec.setWidth 32 d)).unsigned !=
            x.p8.unsigned - (BitVec.setWidth 32 r + BitVec.setWidth 32 d).unsigned,
          af := af, of := of }) = true
      then x.p8 else BitVec.setWidth 32 r + BitVec.setWidth 32 d)) := by
  rw [BitVec.add_comm (BitVec.setWidth 32 r)]
  exact (ix_clamp x r d hd hr hp hi af of).1

/-- `get_bits1`'s index: `index + (index < plus8)` (`xor; cmp; setl; add`). -/
theorem ix_setl (x : PArgs) (r z : BitVec 64) (hr : Ix x r) (hp : x.p8.toNat < 2 ^ 31)
    (cf af : Bool) :
    Ix x (BitVec.setWidth 64 (BitVec.setWidth 32 r + BitVec.setWidth 32
      ((BitVec.setWidth 64 (BitVec.setWidth 32 z ^^^ BitVec.setWidth 32 z)).replaceLow
        (BitVec.ofNat 8 (CondCode.l.interp (StatusFlags.from_result (BitVec.setWidth 32 r - x.p8)
          { cf := cf, af := af,
            of := (BitVec.setWidth 32 r - x.p8).signed !=
              (BitVec.setWidth 32 r).signed - x.p8.signed })).toNat))))
    ∧ r.toNat ≤ (BitVec.setWidth 64 (BitVec.setWidth 32 r + BitVec.setWidth 32
      ((BitVec.setWidth 64 (BitVec.setWidth 32 z ^^^ BitVec.setWidth 32 z)).replaceLow
        (BitVec.ofNat 8 (CondCode.l.interp (StatusFlags.from_result (BitVec.setWidth 32 r - x.p8)
          { cf := cf, af := af,
            of := (BitVec.setWidth 32 r - x.p8).signed !=
              (BitVec.setWidth 32 r).signed - x.p8.signed })).toNat)))).toNat := by
  obtain ⟨h1, h2⟩ := hr
  rw [CondCode.interp_l_cmp_toInt32, BitVec.xor_self]
  have e0 : (BitVec.setWidth 64 (0#32)) = 0#64 := rfl
  rw [e0]
  have hr32 : (BitVec.setWidth 32 r).toNat = r.toNat := by
    rw [BitVec.toNat_setWidth]; omega
  have hlt : (BitVec.setWidth 32 r).toInt < x.p8.toInt ↔ r.toNat < x.p8.toNat := by
    rw [BitVec.toInt_eq_toNat_of_msb, BitVec.toInt_eq_toNat_of_msb]
    · omega
    · rw [BitVec.msb_eq_decide]; simp only [decide_eq_false_iff_not]; omega
    · rw [BitVec.msb_eq_decide]; simp only [decide_eq_false_iff_not]; omega
  have key : ∀ b : Bool, (BitVec.setWidth 64 (BitVec.setWidth 32 r + BitVec.setWidth 32
      ((0#64).replaceLow (BitVec.ofNat 8 b.toNat)))).toNat = r.toNat + b.toNat := by
    intro b
    have hb : b.toNat ≤ 1 := by cases b <;> decide
    have hz : (BitVec.setWidth 32 ((0#64).replaceLow (BitVec.ofNat 8 b.toNat))).toNat
        = b.toNat := by
      rw [BitVec.toNat_setWidth, BitVec.toNat_replaceLow8]
      simp only [BitVec.toNat_ofNat]; omega
    rw [BitVec.toNat_setWidth, BitVec.toNat_add, hz, hr32]
    omega
  simp only [Ix, key]
  by_cases h : r.toNat < x.p8.toNat
  · have : decide ((BitVec.setWidth 32 r).toInt < x.p8.toInt) = true := by
      simp only [decide_eq_true_eq]; exact hlt.mpr h
    rw [this]; simp only [Bool.toNat_true]; omega
  · have : decide ((BitVec.setWidth 32 r).toInt < x.p8.toInt) = false := by
      simp only [decide_eq_false_iff_not]; exact fun h' => h (hlt.mp h')
    rw [this]; simp only [Bool.toNat_false]; omega

/-- `index' = min(S, plus8)` for a sum `S` a little above a reader index `r`. -/
theorem ix_clampS (x : PArgs) (r : BitVec 64) (S : BitVec 32) (hr : Ix x r)
    (hS1 : r.toNat ≤ S.toNat) (hS2 : S.toNat ≤ r.toNat + 256)
    (af of : Bool) :
    Ix x (BitVec.setWidth 64 (if CondCode.c.interp (StatusFlags.from_result (x.p8 - S)
        { cf := (x.p8 - S).unsigned != x.p8.unsigned - S.unsigned, af := af, of := of }) = true
      then x.p8 else S))
    ∧ r.toNat ≤ (BitVec.setWidth 64 (if CondCode.c.interp (StatusFlags.from_result (x.p8 - S)
        { cf := (x.p8 - S).unsigned != x.p8.unsigned - S.unsigned, af := af, of := of }) = true
      then x.p8 else S)).toNat := by
  obtain ⟨h1, h2⟩ := hr
  have h64 : ∀ y : BitVec 32, (BitVec.setWidth 64 y).toNat = y.toNat := fun y => by
    rw [BitVec.toNat_setWidth]; have := y.isLt; omega
  simp only [Ix, h64]
  split
  · have := x.p8.isLt
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> omega
  · rename_i h
    simp only [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, bne_iff_ne, ne_eq,
      Decidable.not_not] at h
    rw [BitVec.toNat_sub] at h
    have := x.p8.isLt
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> omega

/-- The count after an iteration: `cnt + (-2 + (r8 - index'))` is at most `cnt - 2`. -/
theorem d50_var (C a e : BitVec 32) (hC : 8 ≤ C.toInt) (h1 : a.toNat ≤ e.toNat)
    (h2 : e.toNat < 2 ^ 31) :
    (C + (BitVec.setWidth 32 4294967294#64 + (a - e))).toInt.toNat + 1 ≤ C.toInt.toNat := by
  have hm : (BitVec.setWidth 32 4294967294#64).toNat = 4294967294 := by decide
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toInt_eq_toNat_cond (x := C)] at *
  simp only [BitVec.toNat_add, BitVec.toNat_sub, hm] at *
  have := C.isLt
  split at hC <;> split <;> omega

theorem ofInt_ne_toNat (z : Int) (h0 : 0 ≤ z) (h4 : z ≤ 4) :
    (BitVec.ofInt 64 z).toNat = z.toNat := by
  rw [BitVec.toNat_ofInt]; omega

/-- `inc %edx; cmp; cmovb`: the clamped `index + 1`. -/
theorem ix_inc (x : PArgs) (r : BitVec 64) (hr : Ix x r) (hp : x.p8.toNat < 2 ^ 31)
    (af of : Bool) :
    Ix x (BitVec.setWidth 64 (if CondCode.c.interp (StatusFlags.from_result
        (x.p8 - (BitVec.setWidth 32 r + 1#32))
        { cf := (x.p8 - (BitVec.setWidth 32 r + 1#32)).unsigned !=
            x.p8.unsigned - (BitVec.setWidth 32 r + 1#32).unsigned, af := af, of := of }) = true
      then x.p8 else BitVec.setWidth 32 r + 1#32))
    ∧ r.toNat ≤ (BitVec.setWidth 64 (if CondCode.c.interp (StatusFlags.from_result
        (x.p8 - (BitVec.setWidth 32 r + 1#32))
        { cf := (x.p8 - (BitVec.setWidth 32 r + 1#32)).unsigned !=
            x.p8.unsigned - (BitVec.setWidth 32 r + 1#32).unsigned, af := af, of := of }) = true
      then x.p8 else BitVec.setWidth 32 r + 1#32)).toNat := by
  have e : (BitVec.setWidth 32 r + 1#32).toNat = r.toNat + 1 := by
    have := hr.2
    rw [BitVec.toNat_add, BitVec.toNat_setWidth]; simp only [BitVec.toNat_ofNat]; omega
  exact ix_clampS x r _ hr (by omega) (by omega) af of

/-- The `Ld50 → Ld70` count step. -/
theorem d50_le (x : PArgs) (C : BitVec 32) (r8 r : BitVec 64) (hC : 8 ≤ C.toInt)
    (h8 : Ix x r8) (hr : Ix x r) (h8r : r8.toNat ≤ r.toNat) (hp : x.p8.toNat < 2 ^ 31)
    (af of : Bool) :
    (C + (BitVec.setWidth 32 4294967294#64 + (BitVec.setWidth 32 r8 -
      if CondCode.c.interp (StatusFlags.from_result
        (x.p8 - (BitVec.setWidth 32 r + 1#32))
        { cf := (x.p8 - (BitVec.setWidth 32 r + 1#32)).unsigned !=
            x.p8.unsigned - (BitVec.setWidth 32 r + 1#32).unsigned, af := af, of := of }) = true
      then x.p8 else BitVec.setWidth 32 r + 1#32))).toInt.toNat + 1 ≤ C.toInt.toNat := by
  have hE := ix_inc x r hr hp af of
  generalize (if CondCode.c.interp (StatusFlags.from_result
        (x.p8 - (BitVec.setWidth 32 r + 1#32))
        { cf := (x.p8 - (BitVec.setWidth 32 r + 1#32)).unsigned !=
            x.p8.unsigned - (BitVec.setWidth 32 r + 1#32).unsigned, af := af, of := of }) = true
      then x.p8 else BitVec.setWidth 32 r + 1#32) = E at hE ⊢
  have h64 : (BitVec.setWidth 64 E).toNat = E.toNat := by
    rw [BitVec.toNat_setWidth]; have := E.isLt; omega
  have h32 : (BitVec.setWidth 32 r8).toNat = r8.toNat := by
    rw [BitVec.toNat_setWidth]; have := h8.2; omega
  rw [h64] at hE
  exact d50_var C _ E hC (by rw [h32]; omega) (by have := hE.1.2; omega)

/-- `test %eax,%eax; js`. -/
theorem test_s32 (w : BitVec 32) (a : Bool) :
    CondCode.s.interp (StatusFlags.from_result (w &&& w) { cf := false, af := a, of := false })
      = w.msb := by
  simp only [CondCode.interp, StatusFlags.from_result, BitVec.and_self]

/-- A 32-bit count as a variant digit is small. -/
theorem toInt_toNat_lt (w : BitVec 32) : w.toInt.toNat + 1 < 2 ^ 64 := by
  have := BitVec.toInt_lt (x := w); simp at this; omega

theorem toInt_toNat_lt' (w : BitVec 32) : w.toInt.toNat < 2 ^ 64 := by
  have := toInt_toNat_lt w; omega

/-- A lexicographic step on the second digit, or on the third with the second equal. -/
theorem lex3_lt {d a b x y : Nat} {r1 r2 : List Nat} (hl : r1.length = r2.length)
    (hb : b < 2 ^ 64) (hy : y < 2 ^ 64) (h : a < b ∨ (a = b ∧ x < y)) :
    lex (d :: a :: x :: r1) < lex (d :: b :: y :: r2) := by
  rcases h with h | ⟨rfl, h⟩
  · exact lex_cons_lt_cons (by simp [hl]) (lex_cons_lt_of_lt (by simp [hl]) (by omega))
  · exact lex_cons_lt_cons (by simp [hl]) (lex_cons_lt_cons (by simp [hl])
      (lex_cons_lt_of_lt hl (by omega)))

/-- `lex3_lt` with the second digits `≤` and the third `<`. -/
theorem lex3_le {d a b x y : Nat} {r1 r2 : List Nat} (hl : r1.length = r2.length)
    (hb : b < 2 ^ 64) (hy : y < 2 ^ 64) (h : a ≤ b) (hxy : x < y) :
    lex (d :: a :: x :: r1) < lex (d :: b :: y :: r2) := by
  rcases Nat.lt_or_eq_of_le h with h | h
  · exact lex3_lt hl hb hy (Or.inl h)
  · exact lex3_lt hl hb hy (Or.inr ⟨h, hxy⟩)

/-- `add $-2` on a count `≥ 8` (the `Ld93 → Ld70` edge). -/
theorem sub2_lt (w : BitVec 32) (h : 8 ≤ w.toInt) :
    (w + BitVec.setWidth 32 4294967294#64).toInt.toNat + 1 < w.toInt.toNat := by
  have e : BitVec.setWidth 32 4294967294#64 = -2#32 := by decide
  have := BitVec.toInt_lt (x := w)
  rw [e, BitVec.toInt_add, Int.bmod_def]
  have : (-2#32 : BitVec 32).toInt = -2 := by decide
  rw [this]
  split <;> omega

/-- `test %edx,%edx; jle` on a small nonnegative `rdx`. -/
theorem test_le_small (d : BitVec 64) (hd : d.toNat < 2 ^ 31) (a : Bool) :
    CondCode.le.interp (StatusFlags.from_result (BitVec.setWidth 32 d &&& BitVec.setWidth 32 d)
      { cf := false, af := a, of := false }) = decide (d.toNat = 0) := by
  have h1 : (BitVec.setWidth 32 d).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_setWidth, decide_eq_false_iff_not]; omega
  have h2 : ((BitVec.setWidth 32 d) == BitVec.zero 32) = decide (d.toNat = 0) := by
    have : (BitVec.setWidth 32 d = BitVec.zero 32) ↔ d.toNat = 0 := by
      have z : (BitVec.zero 32).toNat = 0 := rfl
      rw [← BitVec.toNat_inj, z, BitVec.toNat_setWidth]; omega
    rw [Bool.eq_iff_iff]; simp only [beq_iff_eq, decide_eq_true_eq, this]
  simp only [CondCode.interp, StatusFlags.from_result, BitVec.and_self, h1, h2]
  cases decide (d.toNat = 0) <;> rfl

/-- `lea (,%rdx,8),%eax` on a small `rdx`. -/
theorem toInt_x8 (d : BitVec 64) (hd : d.toNat < 271) :
    (BitVec.setWidth 32 (d * 8#64)).toInt = 8 * d.toNat := by
  rw [BitVec.toInt_eq_toNat_of_msb]
  · simp only [BitVec.toNat_setWidth, BitVec.toNat_mul, BitVec.toNat_ofNat]; omega
  · rw [BitVec.msb_eq_decide]
    simp only [BitVec.toNat_setWidth, BitVec.toNat_mul, BitVec.toNat_ofNat, decide_eq_false_iff_not]
    omega

theorem ofBytes_nat (l : List UInt8) : Int.ofBytes l = (Nat.ofBytes l : Int) := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    unfold Int.ofBytes Nat.ofBytes at *
    rw [List.foldr_cons, List.foldr_cons, ih]; omega

theorem x_rd_i32 (c : List UInt8) (o : Nat) : (BitVec.ofInt 32 (rd c o 4)).toInt = i32 c o := by
  show (BitVec.ofInt 32 (Int.ofBytes ((c.drop o).take 4))).toInt = _
  rw [ofBytes_nat, BitVec.ofInt_natCast]

/-- `test %r10b,%r10b; jle` on a small `r10`. -/
theorem test_le8 (d : BitVec 64) (hd : d.toNat < 128) (a : Bool) :
    CondCode.le.interp (StatusFlags.from_result (BitVec.setWidth 8 d &&& BitVec.setWidth 8 d)
      { cf := false, af := a, of := false }) = decide (d.toNat = 0) := by
  have h1 : (BitVec.setWidth 8 d).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_setWidth, decide_eq_false_iff_not]; omega
  have h2 : ((BitVec.setWidth 8 d) == BitVec.zero 8) = decide (d.toNat = 0) := by
    have : (BitVec.setWidth 8 d = BitVec.zero 8) ↔ d.toNat = 0 := by
      have z : (BitVec.zero 8).toNat = 0 := rfl
      rw [← BitVec.toNat_inj, z, BitVec.toNat_setWidth]; omega
    rw [Bool.eq_iff_iff]; simp only [beq_iff_eq, decide_eq_true_eq, this]
  simp only [CondCode.interp, StatusFlags.from_result, BitVec.and_self, h1, h2]
  cases decide (d.toNat = 0) <;> rfl

theorem slot32_regs {s s' : MachineData} (hm : s'.dmem = s.dmem)
    (hbp : s'.regs.get64 .rbp = s.regs.get64 .rbp) (o : Nat) : slot32 s' o = slot32 s o := by
  simp only [slot32, hm, hbp]

variable [CodeEnv] in
/-- Two states with `XB` at the same locals have the same count slot. -/
theorem XB_slot {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64} {t₀ s s' : MachineData}
    {c f : List UInt8} (h : XB k Ext x ra t₀ s c f) (h' : XB k Ext x ra t₀ s' c f) :
    slot32 s' 0x80 = slot32 s 0x80 :=
  (slot32_Fr h'.1.2.2 h'.1.2.1.2.2.1 h'.1.2.1.2.1 0x20 (by omega)).trans
    (slot32_Fr h.1.2.2 h.1.2.1.2.2.1 h.1.2.1.2.1 0x20 (by omega)).symm


theorem slot64_regs {s s' : MachineData} (hm : s'.dmem = s.dmem)
    (hbp : s'.regs.get64 .rbp = s.regs.get64 .rbp) (o : Nat) : slot64 s' o = slot64 s o := by
  simp only [slot64, hm, hbp]

/-- `cmp b, a; je`. -/
theorem z_sub (a b : BitVec 64) (f : StatusFlags.from_result.Remaining) :
    CondCode.z.interp (StatusFlags.from_result (a - b) f) = decide (a = b) := by
  rw [CondCode.interp_z, StatusFlags.zf_from_result, Bool.eq_iff_iff]
  simp only [beq_iff_eq, decide_eq_true_eq]
  have z : BitVec.zero 64 = 0#64 := rfl
  rw [z]; constructor <;> intro h <;> bv_omega

/-- The envelope latch: the next row. -/
theorem x_row_step (a r p : BitVec 64) (base : Nat) (hr : r.toNat < 5)
    (hp : p = a + BitVec.ofNat 64 (base + 34 * r.toNat)) :
    BitVec.setWidth 64 34#64 + p = a + BitVec.ofNat 64 (base + 34 * (r + 1#64).toNat) := by
  subst hp
  have h1 : (r + 1#64).toNat = r.toNat + 1 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [h1]; apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth]; omega

theorem e00_dec (N N' r : BitVec 64) (hN : N' = N) (h : r.toNat < N.toNat) :
    (N' - (r + 1#64)).toNat < (N - r).toNat := by subst hN; bv_omega

/-- A lexicographic step on the fourth digit. -/
theorem lex4_lt {d a a' b x y : Nat} {r1 r2 : List Nat} (hl : r1.length = r2.length)
    (ha : a' = a) (hy : y < 2 ^ 64) (h : x < y) :
    lex (d :: a' :: b :: x :: r1) < lex (d :: a :: b :: y :: r2) :=
  ha ▸ lex_cons_lt_cons (by simp [hl]) (lex_cons_lt_cons (by simp [hl])
    (lex_cons_lt_cons (by simp [hl]) (lex_cons_lt_of_lt hl (by omega))))

theorem vq1 {s s' : MachineData} {B : BitVec 64} (_ : s.regs.get64 .rbp = B) (hm : s'.dmem = s.dmem)
    (hbp : s'.regs.get64 .rbp = s.regs.get64 .rbp) :
    (slot32 s' 0x80).toInt.toNat = (slot32 s 0x80).toInt.toNat := by
  rw [slot32_regs hm hbp]

theorem vq2 {s s' : MachineData} {B : BitVec 64} (_ : s.regs.get64 .rbp = B) (hm : s'.dmem = s.dmem)
    (hbp : s'.regs.get64 .rbp = s.regs.get64 .rbp) :
    (slot64 s' 0x58 - s.regs.get64 .r15).toNat = (slot64 s 0x58 - s.regs.get64 .r15).toNat := by
  rw [slot64_regs hm hbp]

/-- A lexicographic step on the fifth digit. -/
theorem lex5_lt {d a a' b x x' y y' : Nat} {r1 r2 : List Nat} (hl : r1.length = r2.length)
    (ha : a' = a) (hx : x' = x) (hy : y < 2 ^ 64) (h : y' < y) :
    lex (d :: a' :: b :: x' :: y' :: r1) < lex (d :: a :: b :: x :: y :: r2) :=
  ha ▸ hx ▸ lex_cons_lt_cons (by simp [hl]) (lex_cons_lt_cons (by simp [hl])
    (lex_cons_lt_cons (by simp [hl]) (lex_cons_lt_cons (by simp [hl])
      (lex_cons_lt_of_lt hl (by omega)))))

theorem sel8 (w : BitVec 32) : (w.ushiftRight 4 &&& 8#32) = 0#32 ∨ (w.ushiftRight 4 &&& 8#32) = 8#32 := by
  have t8 : ∀ i, i ≠ 3 → Nat.testBit 8 i = false := by
    intro i h3; rw [show (8:Nat) = 2^3 by rfl, Nat.testBit_two_pow]; simp; omega
  by_cases h : w.getLsbD 7
  · right; apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_and, BitVec.ushiftRight_eq, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ofNat]
    by_cases h3 : i = 3
    · subst h3; simp [h]
    · simp [t8 i h3]
  · left; apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_and, BitVec.ushiftRight_eq, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ofNat]
    by_cases h3 : i = 3
    · subst h3; simp at h ⊢; simp [h]
    · simp [t8 i h3]

variable [CodeEnv] in
theorem vsel (w : BitVec 32) (o : Nat) : ∃ j, j < 2 ∧ BitVec.setWidth 64 (w.ushiftRight 4 &&& BitVec.setWidth 32 8#64)
    + lab "vlc_ps" + BitVec.ofNat 64 o = lab "vlc_ps" + BitVec.ofNat 64 (o + 8 * j) := by
  have h8 : BitVec.setWidth 32 8#64 = 8#32 := rfl
  rw [h8]
  rcases sel8 w with h | h <;> rw [h]
  · refine ⟨0, by decide, ?_⟩
    bv_omega
  · refine ⟨1, by decide, ?_⟩
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

theorem XP_regs {t₀ s s' : MachineData} {c : List UInt8} (h : XP t₀ s c)
    (hb : s'.regs.get64 .rbx = s.regs.get64 .rbx) (h15 : s'.regs.get64 .r15 = s.regs.get64 .r15)
    (h11 : s'.regs.get64 .r11 = s.regs.get64 .r11) (h9 : s'.regs.get64 .r9 = s.regs.get64 .r9) :
    XP t₀ s' c := by
  simp only [XP, hb, h15, h11, h9]; exact h

theorem XJ_regs {x : PArgs} {s s' : MachineData} {cur : BitVec 64} (h : XJ x s cur)
    (h8 : s'.regs.get64 .r8 = s.regs.get64 .r8) : XJ x s' cur := by
  simp only [XJ, h8]; exact h

theorem test_le32 (d : BitVec 64) (hd : d.toNat < 2 ^ 32) (h34 : (BitVec.setWidth 32 d).toInt ≤ 34)
    (a : Bool)
    (h : CondCode.le.interp (StatusFlags.from_result (BitVec.setWidth 32 d &&& BitVec.setWidth 32 d)
      { cf := false, af := a, of := false }) = false) : 1 ≤ d.toNat ∧ d.toNat ≤ 34 := by
  simp only [CondCode.interp, StatusFlags.from_result, BitVec.and_self] at h
  have h32 : (BitVec.setWidth 32 d).toNat = d.toNat := by rw [BitVec.toNat_setWidth]; omega
  simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq, beq_eq_false_iff_ne] at h
  obtain ⟨h1, h2⟩ := h
  rw [BitVec.toInt_eq_toNat_of_msb h1, h32] at h34
  have : d.toNat ≠ 0 := by
    intro h0; apply h2; apply BitVec.eq_of_toNat_eq; rw [h32, h0]; rfl
  omega

theorem lo4_eq (f : List UInt8) (o : Nat) (z : Int)
    (h : BitVec.ofInt 64 (rd f o 8) = BitVec.ofInt 64 z) : BitVec.ofInt 32 (rd f o 4) = BitVec.ofInt 32 z := by
  have e1 : BitVec.ofInt 32 (rd f o 8) = BitVec.ofInt 32 (rd f o 4) := by
    simp only [rd]; rw [BitVec.ofInt_ofBytes_take 32 4 rfl, List.take_take]; rfl
  have e2 : ∀ z : Int, BitVec.ofInt 32 z = BitVec.setWidth 32 (BitVec.ofInt 64 z) := by
    intro z; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofInt, BitVec.toNat_setWidth]
    omega
  rw [← e1, e2, h, ← e2]

theorem ec_rng (a : BitVec 32) (ha0 : 0 ≤ a.toInt) (ha5 : a.toInt ≤ 5) (cf af : Bool) :
    1 ≤ (BitVec.setWidth 64 (if CondCode.l.interp (StatusFlags.from_result (a - BitVec.setWidth 32 2#64)
      { cf := cf, af := af, of := (a - BitVec.setWidth 32 2#64).signed != a.signed - (BitVec.setWidth 32 2#64).signed }) = true
      then BitVec.setWidth 32 1#64 else a)).toNat
    ∧ (BitVec.setWidth 64 (if CondCode.l.interp (StatusFlags.from_result (a - BitVec.setWidth 32 2#64)
      { cf := cf, af := af, of := (a - BitVec.setWidth 32 2#64).signed != a.signed - (BitVec.setWidth 32 2#64).signed }) = true
      then BitVec.setWidth 32 1#64 else a)).toNat ≤ 5 := by
  rw [CondCode.interp_l_cmp_toInt32]
  have h2 : (BitVec.setWidth 32 2#64).toInt = 2 := by decide
  rw [h2]
  have hc := BitVec.toInt_eq_toNat_cond a
  by_cases h : a.toInt < 2
  · simp only [h, decide_true, ↓reduceIte]; decide
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, BitVec.toNat_setWidth]
    split at hc <;> omega

/-- The `cmove` operand: `r15` or `num_env_old`, in `[0, 5]`. -/
theorem ec_src (r : BitVec 64) (v : Int) (hr : r.toNat < 5) (h0 : 0 ≤ v) (h5 : v ≤ 5) (b : Bool) :
    0 ≤ (if b = true then BitVec.ofInt 32 v else BitVec.setWidth 32 r).toInt
    ∧ (if b = true then BitVec.ofInt 32 v else BitVec.setWidth 32 r).toInt ≤ 5 := by
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [BitVec.toInt_eq_toNat_of_msb]
    · rw [BitVec.toNat_setWidth]; omega
    · rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_setWidth, decide_eq_false_iff_not]; omega
  · simp only [↓reduceIte]
    rw [BitVec.toInt_ofInt]; simp only [Int.bmod_def]; split <;> omega

theorem offs2 (i : Reg64) (r : Reg64s) :
    AddrIndex.offset64 (some { reg := i, scale := Width.W16 }) r = r.get64 i * 2#64 := by
  simp [AddrIndex.offset64]

/-- `shl $5; lea (,c,2)`: the row `34 c` past `base`. -/
theorem rowq (A c : BitVec 64) (b : Nat) :
    (A + BitVec.ofNat 64 b) + (c <<< 5 + c * 2#64) = A + BitVec.ofNat 64 (b + 34 * c.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.shiftLeft_eq, BitVec.toNat_ofInt]
  omega

theorem XJ_zx {x : PArgs} {s s' : MachineData} {r : BitVec 64} (h : XJ x s r) (hp : x.p8.toNat < 2 ^ 31)
    (h8 : s'.regs.get64 .r8 = s.regs.get64 .r8) : XJ x s' (BitVec.setWidth 64 (BitVec.setWidth 32 r)) := by
  have e : (BitVec.setWidth 64 (BitVec.setWidth 32 r)).toNat = r.toNat := by
    simp only [BitVec.toNat_setWidth]; have := h.2.1.2; omega
  simp only [XJ, Ix, h8, e]; exact h

theorem lex6_eq {d a a' b x x' y z z' : Nat} (ha : a' = a) (hx : x' = x) (hz : z' = z) :
    lex [d, a', b, x', y, z'] = lex [d, a, b, x, y, z] := by subst ha hx hz; rfl

/-- `cmp $0x22, r; je` on a band index below `nr_ipdopd_par ≤ 34`: not taken. -/
theorem trap34 {s : MachineData} {r : BitVec 64} (h : XBd s r) (f : StatusFlags.from_result.Remaining)
    (hc : CondCode.z.interp (StatusFlags.from_result (r - BitVec.setWidth 64 34#64) f) = true) : False := by
  rw [z_sub] at hc
  have e := of_decide_eq_true hc
  have : r.toNat = 34 := by rw [e]; rfl
  have := h.1; have := h.2; omega

theorem prev_addr (A r : BitVec 64) (b j : Nat) (hj1 : 1 ≤ j) (hj5 : j ≤ 5) (_hb : b ≤ 586) (_hr : r.toNat < 34) :
    A + BitVec.ofNat 64 (b + 34 * j) + r + BitVec.ofNat 64 (18446744073709551616 - 34)
      = A + BitVec.ofNat 64 (b + 34 * (j - 1) + r.toNat) := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have e1 : BitVec.ofNat 64 (b + 34 * (j' + 1)) = BitVec.ofNat 64 (b + 34 * j') + 34#64 := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have e2 : BitVec.ofNat 64 (b + 34 * (j' + 1 - 1) + r.toNat) = BitVec.ofNat 64 (b + 34 * j') + r := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [e1, e2]
  have e3 : (34#64 : BitVec 64) + BitVec.ofNat 64 (18446744073709551616 - 34) = 0#64 := by decide
  calc A + (BitVec.ofNat 64 (b + 34 * j') + 34#64) + r + BitVec.ofNat 64 (18446744073709551616 - 34)
      = A + (BitVec.ofNat 64 (b + 34 * j') + r) + (34#64 + BitVec.ofNat 64 (18446744073709551616 - 34)) := by ac_rfl
    _ = _ := by rw [e3, BitVec.add_zero]

variable [CodeEnv] in
/-- The previous row's byte `par[e_prev][b]` (`movzbl -0x22(%r14,%r10)`). -/
theorem prev_load {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64}
    {t₀ : MachineData} {f c : List UInt8} {i : BitVec 32} (h : m =⋆ Fr k Ext x ra t₀ f c i)
    (hcl : c.length = 764) {r14 r10 : BitVec 64} {b j : Nat}
    (hr14 : r14 = arg2 t₀ + BitVec.ofNat 64 (b + 34 * j)) (hj1 : 1 ≤ j) (hj5 : j ≤ 5)
    (hb : b ≤ 586) (hr : r10.toNat < 34) :
    m.loadInt (r14 + r10 + BitVec.ofNat 64 (18446744073709551616 - 34)) 1
      = some (rd c (b + 34 * (j - 1) + r10.toNat) 1) := by
  have e : r14 + r10 + BitVec.ofNat 64 (18446744073709551616 - 34)
      = arg2 t₀ + BitVec.ofNat 64 (b + 34 * (j - 1) + r10.toNat) := by
    subst hr14; exact prev_addr _ _ _ _ hj1 hj5 hb hr
  rw [e]; exact Fr_c_load h hcl _ 1 (by omega)

theorem offs4 (i : Reg64) (r : Reg64s) :
    AddrIndex.offset64 (some { reg := i, scale := Width.W32 }) r = r.get64 i * 4#64 := by
  simp [AddrIndex.offset64]

theorem tab_addr2 (p r : BitVec 64) (h : r.toNat < 32) :
    p + BitVec.setWidth 64 (BitVec.setWidth 32 r) * 4#64 + 2#64 = p + BitVec.ofNat 64 (4 * r.toNat + 2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

theorem tab_addr0 (p r : BitVec 64) (h : r.toNat < 32) :
    p + BitVec.setWidth 64 (BitVec.setWidth 32 r) * 4#64 = p + BitVec.ofNat 64 (4 * r.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

theorem par_addr {A r11 r : BitVec 64} {b e : Nat} (hr11 : r11 = A + BitVec.ofNat 64 (b + 34 * e))
    (he : e < 5) (hr : r.toNat < 34) (hb : b ≤ 586) :
    r11 + r = A + BitVec.ofNat 64 (b + 34 * e + r.toNat) := by
  subst hr11; apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem b8_lt (z : BitVec 64) (y : BitVec 8) :
    (BitVec.setWidth 8 (z.replaceLow (y &&& BitVec.setWidth 8 7#64))).toNat < 8 := by
  have h7 : BitVec.setWidth 8 7#64 = 7#8 := rfl
  rw [h7]
  have e : (BitVec.setWidth 8 (z.replaceLow (y &&& 7#8))).toNat = (y &&& 7#8).toNat := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_replaceLow8]; have := (y &&& 7#8).isLt; omega
  rw [e, BitVec.toNat_and]
  exact Nat.lt_of_le_of_lt (Nat.and_le_right) (by decide)

theorem sx_add (w : BitVec 16) (hw : w.msb = false) (r : BitVec 64) (hr : r.toNat < 2 ^ 31) :
    (BitVec.signExtend 32 w + BitVec.setWidth 32 r).toNat = w.toNat + r.toNat := by
  rw [BitVec.toNat_add, BitVec.signExtend_eq_setWidth_of_msb_false hw, BitVec.toNat_setWidth,
    BitVec.toNat_setWidth]
  have := w.isLt; omega

theorem nz_sub (a b : BitVec 64) (f : StatusFlags.from_result.Remaining) :
    CondCode.nz.interp (StatusFlags.from_result (a - b) f) = !decide (a = b) := by
  rw [CondCode.interp_nz, ← CondCode.interp_z, z_sub]

theorem lex6_lt {d a a' b x x' y z z' : Nat} (ha : a' = a) (hx : x' = x) (hz : z < 2 ^ 64) (h : z' < z) :
    lex [d, a', b, x', y, z'] < lex [d, a, b, x, y, z] := by
  subst ha hx
  exact lex_cons_lt_cons (by simp) (lex_cons_lt_cons (by simp) (lex_cons_lt_cons (by simp)
    (lex_cons_lt_cons (by simp) (lex_cons_lt_cons (by simp) (lex_cons_lt_of_lt rfl (by omega))))))

theorem XL_ne {t₀ : MachineData} {c c' f : List UInt8} (h : XL t₀ c f) (hn : ne c' = ne c) : XL t₀ c' f := by
  simp only [XL, hn]; exact h

theorem XP_ne {t₀ s : MachineData} {c c' : List UInt8} (h : XP t₀ s c) (hn : ne c' = ne c) : XP t₀ s c' := by
  simp only [XP, hn]; exact h

/-- `index' = min(S, plus8)` for any sum `S` at least the old index. -/
theorem ix_clampS' (x : PArgs) (r : BitVec 64) (S : BitVec 32) (hr : Ix x r)
    (hS1 : r.toNat ≤ S.toNat) (af of : Bool) :
    Ix x (BitVec.setWidth 64 (if CondCode.c.interp (StatusFlags.from_result (x.p8 - S)
        { cf := (x.p8 - S).unsigned != x.p8.unsigned - S.unsigned, af := af, of := of }) = true
      then x.p8 else S))
    ∧ r.toNat ≤ (BitVec.setWidth 64 (if CondCode.c.interp (StatusFlags.from_result (x.p8 - S)
        { cf := (x.p8 - S).unsigned != x.p8.unsigned - S.unsigned, af := af, of := of }) = true
      then x.p8 else S)).toNat := by
  obtain ⟨h1, h2⟩ := hr
  have h64 : ∀ y : BitVec 32, (BitVec.setWidth 64 y).toNat = y.toNat := fun y => by
    rw [BitVec.toNat_setWidth]; have := y.isLt; omega
  simp only [Ix, h64]
  split
  · have := x.p8.isLt
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> omega
  · rename_i h
    simp only [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, bne_iff_ne, ne_eq,
      Decidable.not_not] at h
    rw [BitVec.toNat_sub] at h
    have := x.p8.isLt
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> omega


theorem ne_wrpar (c : List UInt8) (o : Nat) (v : Int) (hl : c.length = 764) (ho : 416 ≤ o) (ho2 : o < 756) :
    ne (wr c o 1 v) = ne c := i32_wr c o 1 44 v (by omega) (Or.inl (by omega))

theorem XI_wrpar {t₀ : MachineData} {x : PArgs} {c f : List UInt8} (o : Nat) (ho : 416 ≤ o)
    (ho2 : o < 756) (b : BitVec 8) (hb : b.toNat < 8)
    (hP : PsInv c) (hI : XI t₀ x c f) :
    PsInv (wr c o 1 b.toInt) ∧ XI t₀ x (wr c o 1 b.toInt) f := by
  have hl : c.length = 764 := hP.1
  have e32 : ∀ o', (o' + 4 ≤ o ∨ o + 1 ≤ o') → i32 (wr c o 1 b.toInt) o' = i32 c o' :=
    fun o' hd => i32_wr c o 1 o' _ (by omega) hd
  have e8 : ∀ j, (j + 1 ≤ o ∨ o + 1 ≤ j) → i8 (wr c o 1 b.toInt) j = i8 c j :=
    fun j hd => i8_wr c o 1 j _ (by omega) hd
  have e8' : ∀ j, (0 ≤ i8 c j ∧ i8 c j ≤ 7) →
      0 ≤ i8 (wr c o 1 b.toInt) j ∧ i8 (wr c o 1 b.toInt) j ≤ 7 := by
    intro j hj
    by_cases hjo : j = o
    · subst hjo; rw [i8_wr_same c j b (by omega) hb]; omega
    · rw [e8 j (by omega)]; exact hj
  obtain ⟨hl', h12, h16, h28, h40, h44, h8⟩ := hP
  obtain ⟨⟨⟨n0, n4, n58, n38⟩, n34, n68, n40⟩, n1c, hG⟩ := hI
  refine ⟨⟨by rw [wr_length _ _ _ _ (by omega)]; exact hl', ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨⟨⟨?_, ?_, ?_, ?_⟩, ?_, n68, ?_⟩, ?_, ?_⟩⟩
  all_goals try simp only [ne, e32 12 (by omega), e32 16 (by omega), e32 28 (by omega),
    e32 40 (by omega), e32 44 (by omega), e32 8 (by omega), e32 4 (by omega),
    e32 20 (by omega)]
  all_goals try assumption
  intro hw
  obtain ⟨⟨r756, r8, ricc, rpar⟩, ⟨d0, d4, db0, dmono, d31⟩, hs, hb', hz⟩ := hG hw
  simp only [IidS, IidB, IidZ] at hs hb' hz
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  all_goals try simp only [ne, bord, IidS, IidB, e32 756 (by omega), e32 8 (by omega),
    e32 44 (by omega), e32 52 (by omega), e32 0 (by omega), e32 4 (by omega), e32 12 (by omega)]
  all_goals try assumption
  · intro e he j hj
    rw [e8 _ (by omega)]; exact ricc e he j hj
  · intro e he j hj
    obtain ⟨a1, a2, a3, a4⟩ := rpar e he j hj
    exact ⟨(e8' _ ⟨a1, a2⟩).1, (e8' _ ⟨a1, a2⟩).2, (e8' _ ⟨a3, a4⟩).1, (e8' _ ⟨a3, a4⟩).2⟩
  · intro e he
    simp only [ne] at d4 he
    rw [e32 _ (by omega), e32 _ (by omega)]; exact dmono e he
  · intro e he
    simp only [ne] at d4 he
    rw [e32 _ (by omega)]; exact d31 e he
  · intro e he j hj hc
    simp only [ne] at d4 he
    rw [e8 _ (by omega)]; exact hb' e he j hj hc
  · simp only [IidZ, IidB, e32 4 (by omega), e32 12 (by omega), e32 8 (by omega)]
    intro h4 e he j hj hc
    rw [e8 _ (by omega)]; exact hz h4 e he j hj hc

variable [CodeEnv] in
/-- A band store into an `ipd`/`opd` row keeps `XB`. -/
theorem XB_wrpar {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64} {t₀ s s' : MachineData}
    {c f : List UInt8} (h : XB k Ext x ra t₀ s c f) (o : Nat) (ho : 416 ≤ o) (ho2 : o < 756)
    (b : BitVec 8) (hb : b.toNat < 8)
    (hm : s'.dmem = s.dmem.storeInt (arg2 t₀ + BitVec.ofNat 64 o) 1 b.toInt)
    (hsp : s'.regs.get64 .rsp = s.regs.get64 .rsp) (hbp : s'.regs.get64 .rbp = s.regs.get64 .rbp)
    (h13 : s'.regs.get64 .r13 = s.regs.get64 .r13) (h12 : s'.regs.get64 .r12 = s.regs.get64 .r12) :
    XB k Ext x ra t₀ s' (wr c o 1 b.toInt) f := by
  obtain ⟨⟨hC, ⟨a1, a2, a3, a4, a5, a6, a7⟩, hm'⟩, ⟨r1, r2⟩, hI⟩ := h
  have hw := XI_wrpar o ho ho2 b hb a4 hI
  exact ⟨⟨hC, ⟨by rw [hsp]; exact a1, by rw [hbp]; exact a2, a3, hw.1, a5, a6, a7⟩,
    by rw [hm]; exact Fr_c_store hm' a4.1 o 1 (by omega) b.toInt⟩,
    ⟨by rw [h13]; exact r1, by rw [h12]; exact r2⟩, hw.2⟩

variable [CodeEnv] in
theorem vqF1 {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64} {t₀ s s' : MachineData}
    {c c' f : List UInt8} (h : XB k Ext x ra t₀ s c f) (h' : XB k Ext x ra t₀ s' c' f) :
    (slot32 s' 0x80).toInt.toNat = (slot32 s 0x80).toInt.toNat := by
  rw [slot32_Fr h'.1.2.2 h'.1.2.1.2.2.1 h'.1.2.1.2.1 0x20 (by omega),
    slot32_Fr h.1.2.2 h.1.2.1.2.2.1 h.1.2.1.2.1 0x20 (by omega)]

variable [CodeEnv] in
theorem vqF2 {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64} {t₀ s s' : MachineData}
    {c c' f : List UInt8} (h : XB k Ext x ra t₀ s c f) (h' : XB k Ext x ra t₀ s' c' f) :
    (slot64 s' 0x58 - s.regs.get64 .r15).toNat = (slot64 s 0x58 - s.regs.get64 .r15).toNat := by
  rw [slot64_Fr h'.1.2.2 h'.1.2.1.2.2.1 h'.1.2.1.2.1 0x48 (by omega),
    slot64_Fr h.1.2.2 h.1.2.1.2.2.1 h.1.2.1.2.1 0x48 (by omega)]

/-- `inc r14` in a band loop: the band digit drops. -/
theorem band_dec (B r : BitVec 64) (h : r.toNat < B.toNat) : (B - (r + 1#64)).toNat < (B - r).toNat := by
  bv_omega

theorem band_next (r B : BitVec 64) (h : r.toNat < B.toNat) (hn : ¬ r + 1#64 = B) :
    (r + 1#64).toNat < B.toNat := by
  bv_omega

theorem sx_add2 (w : BitVec 16) (hw : w.msb = false) (r : BitVec 64) (hr : r.toNat < 2 ^ 31) :
    (BitVec.setWidth 32 r + BitVec.signExtend 32 w).toNat = w.toNat + r.toNat := by
  rw [BitVec.add_comm]; exact sx_add w hw r hr

end Kraken.Examples.Sbr.Ps
