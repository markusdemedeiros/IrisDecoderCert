import Kraken.X64.Examples.Sbr.Parse.PsBlkT1Lib

/-!
# `ff_ps_read_data`, the checks, the error path and the return: lemmas for `PsBlkT2_*`
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Parse

namespace Kraken.Examples.Sbr.Ps

/-- The address of byte `j` of row `N` of `icc`. -/
theorem t2_addr (a : BitVec 64) (o j : Nat) :
    a + BitVec.ofNat 64 o + BitVec.ofNat 64 j = a + BitVec.ofNat 64 (o + j) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

section
variable [CodeEnv]

/-- A byte of `*ps` is readable. -/
theorem t2_ld {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64} {t₀ s : MachineData}
    {c f : List UInt8} {N : Nat} (h : T1B k Ext x ra t₀ s c f N) (o : Nat) (ho : o + 1 ≤ 764) :
    (loadInt s.dmem (t₀.regs.get64 .rdx + BitVec.ofNat 64 o) 1).isSome = true := by
  have L := t1_B_load h o 1 ho
  simp only [arg2] at L
  rw [L]; rfl

end

end Kraken.Examples.Sbr.Ps

namespace Kraken.Examples.Sbr.Ps

/-- `cmp $j, %ecx` with `ecx = m` (both small): equal iff `m = j`. -/
theorem t2_cmp_iff (m j : Nat) (hm : m < 2 ^ 32) (hj : j < 2 ^ 32) :
    (BitVec.setWidth 32 (BitVec.ofNat 64 m) - BitVec.setWidth 32 (BitVec.ofNat 64 j) = 0#32)
      ↔ m = j := by
  have e : ∀ a b : BitVec 32, a - b = 0#32 ↔ a = b := fun a b => by
    constructor <;> intro h <;> bv_omega
  rw [e]
  constructor
  · intro h
    have h' := congrArg BitVec.toNat h
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at h'
    omega
  · intro h; subst h; rfl

theorem t2_cmp32 (m : Nat) (j : BitVec 64) (hm : m < 2 ^ 32) :
    (BitVec.ofNat 32 m - BitVec.setWidth 32 j = 0#32) ↔ m = j.toNat % 2 ^ 32 := by
  have e : ∀ a b : BitVec 32, a - b = 0#32 ↔ a = b := fun a b => by
    constructor <;> intro h <;> bv_omega
  rw [e]
  constructor
  · intro h
    have h' := congrArg BitVec.toNat h
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at h'
    omega
  · intro h; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

theorem t2_sw32 (r : BitVec 64) (m : Nat) (h : r = BitVec.ofNat 64 m) (hm : m < 2 ^ 32) :
    BitVec.setWidth 32 r = BitVec.ofNat 32 m := by
  subst h; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

theorem t2_lt {c : List UInt8} {m : Nat} (h : i32 c 12 = (m : Int)) (b : Nat) (hb : b < m) :
    (b : Int) < i32 c 12 := by omega

theorem t2_rcx {c : List UInt8} {m : Nat} {r : BitVec 64} (h : i32 c 12 = (m : Int))
    (hc : r = BitVec.ofNat 64 m) : r = BitVec.ofNat 64 (i32 c 12).toNat := by
  rw [hc, h, Int.toNat_natCast]

theorem t2_ne {r : BitVec 64} {m j : Nat} (hr : r = BitVec.ofNat 64 m) (hm : m < 2 ^ 32)
    (h : ¬BitVec.setWidth 32 r - BitVec.setWidth 32 (BitVec.ofNat 64 j) = 0#32) (hj : j < 2 ^ 32 := by omega) :
    m ≠ j := fun e => h (by subst hr; exact (t2_cmp_iff m j hm hj).2 e)

theorem t2_inc (N : Nat) (h : N < 2 ^ 31) :
    BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 N) + 1#32))
      = BitVec.ofNat 32 (N + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem t2_lt3 {b m : Nat} (h1 : b < m) (a1 : m ≠ b + 1) (a2 : m ≠ b + 2) (a3 : m ≠ b + 3) :
    b + 3 < m := by omega

section
variable [CodeEnv]

theorem t2_ldr {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64} {t₀ s : MachineData}
    {c f : List UInt8} {N : Nat} (h : T1B k Ext x ra t₀ s c f N)
    (hdx : s.regs.get64 .rdx = t₀.regs.get64 .rdx + BitVec.ofNat 64 (34 * N + 246)) (j : Nat)
    (hj : 34 * N + 246 + j + 1 ≤ 764) :
    (loadInt s.dmem (s.regs.get64 .rdx + BitVec.ofNat 64 j) 1).isSome = true := by
  rw [hdx, t2_addr]; exact t2_ld h _ hj

theorem t2_C_eq {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64}
    {t₀ s s' : MachineData} {c f : List UInt8} (h : Cm k Ext x ra t₀ s c f)
    (hm : s'.dmem = s.dmem)
    (hsp : s'.regs.get64 .rsp = s.regs.get64 .rsp) (hbp : s'.regs.get64 .rbp = s.regs.get64 .rbp) :
    Cm k Ext x ra t₀ s' c f := by
  obtain ⟨hC, ⟨a1, a2, a3⟩, hM⟩ := h
  exact ⟨hC, ⟨by rw [hsp]; exact a1, by rw [hbp]; exact a2, a3⟩, by rw [hm]; exact hM⟩

omit [CodeEnv] in
theorem t2_sw3264 (v : BitVec 32) : BitVec.setWidth 32 (BitVec.setWidth 64 v) = v := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth]; have := v.isLt; omega

/-- A load of the locals at `rbp - d` under `Cm`. -/
theorem t2_fload {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64}
    {t₀ s : MachineData} {c f : List UInt8} (h : Cm k Ext x ra t₀ s c f)
    (a : BitVec 64) (d n : Nat) (ha : a.toNat = 2 ^ 64 - d) (h1 : 8 < d) (h2 : d ≤ 0xa0)
    (hn : 0xa0 - d + n ≤ 0x78) :
    s.dmem.loadInt (s.regs.get64 .rbp + a) n = some (rd f (0xa0 - d) n) := by
  obtain ⟨_, ⟨_, hbp, hfl, _⟩, hm⟩ := h
  have e : s.regs.get64 .rbp + a = rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 (0xa0 - d) := by
    rw [hbp, show a = BitVec.ofNat 64 (2 ^ 64 - d) from BitVec.eq_of_toNat_eq (by simp [ha]; omega)]
    exact fr_addr _ d h1 h2
  rw [e]; exact Fr_f_load hm hfl _ n hn

end

end Kraken.Examples.Sbr.Ps

/-! The exits of the blocks of the `icc` check of the extra envelope (`0x14ec`–`0x171b`), after
`vcgen`. Names: `c f N hB hW hne h12 hbx hm hnr hcx hdx` as the blocks' `obtain`. -/

set_option hygiene false in
/-- A byte of row `N` of `icc` is readable. -/
macro "t2_ld" : tactic => `(tactic|
  exact Kraken.Examples.Sbr.Ps.t2_ldr hB hdx _ (by omega))

set_option hygiene false in
/-- `ja 0x132a`: the error path. -/
macro "t2_ja" : tactic => `(tactic| (
    t1_jump "ff_ps_read_data.L132a"
    show Kraken.Examples.Sbr.Ps.q132a _ _ _ _ _ _
    exact ⟨⟨c, f, (Kraken.Examples.Sbr.Ps.t1_B_eq hB rfl rfl rfl rfl rfl).1, hbx,
    fun hp => ⟨(hW hp).1.1, (hW hp).1.2.1⟩⟩, (Kraken.Examples.Sbr.Ps.t1_B_eq hB rfl rfl rfl rfl rfl).2.2.1⟩))

set_option hygiene false in
/-- `je 0x14f1`: the row is checked. -/
macro "t2_je" : tactic => `(tactic| (
    t1_jump "ff_ps_read_data.L14f1"
    show Kraken.Examples.Sbr.Ps.q14f1 _ _ _ _ _ _
    exact ⟨c, f, N, ⟨Kraken.Examples.Sbr.Ps.t1_B_eq hB rfl rfl rfl rfl rfl, hW⟩, ⟨hne, h12⟩, hbx⟩))

set_option hygiene false in
/-- The fallthrough into the next check (`T2C`), after three `cmp $j, %ecx` not equal. -/
macro "t2_ft" b:num j1:num j2:num j3:num : tactic => `(tactic| (
  have a1 := Kraken.Examples.Sbr.Ps.t2_ne (j := $j1) hcx (by omega)
    ‹¬BitVec.setWidth 32 _ - BitVec.setWidth 32 (BitVec.ofNat 64 $j1) = 0#32› (by omega)
  have a2 := Kraken.Examples.Sbr.Ps.t2_ne (j := $j2) hcx (by omega)
    ‹¬BitVec.setWidth 32 _ - BitVec.setWidth 32 (BitVec.ofNat 64 $j2) = 0#32› (by omega)
  have a3 := Kraken.Examples.Sbr.Ps.t2_ne (j := $j3) hcx (by omega)
    ‹¬BitVec.setWidth 32 _ - BitVec.setWidth 32 (BitVec.ofNat 64 $j3) = 0#32› (by omega)
  have hlt := Kraken.Examples.Sbr.Ps.t2_lt3 (b := $b) hmb a1 a2 a3
  exact ⟨⟨c, f, N, ⟨Kraken.Examples.Sbr.Ps.t1_B_eq hB rfl rfl rfl rfl rfl, hW⟩, ⟨hne, h12⟩, hbx,
    Kraken.Examples.Sbr.Ps.t2_lt hm _ hlt, Kraken.Examples.Sbr.Ps.t2_rcx hm hcx, hdx⟩,
    by var_step⟩))
