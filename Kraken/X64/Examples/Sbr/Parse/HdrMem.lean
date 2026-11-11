import Kraken.X64.Examples.Sbr.Parse.HdrBase

/-!
# `read_sbr_header`: footprint access lemmas

`M` (`MU u` at `u = is_usac`) is `SbWu ⋆ (GbW ⋆ (Blocks ⋆ (Tl ⋆ (Fm ⋆ …))))`. An access to a field of `*sbr` is a lemma on
`SbWu s u st ⋆ F` (an AC equation over the 10 fields); one to `*gb` or the buffer is a lemma on
`GbW ⋆ F` after `M_gb`; one to the frame is a lemma on `Fm ⋆ F` after `M_fm`. Each is proved
once here.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.Hdr

open Kraken.Examples.Sbr.HdrLib
open Kraken.Examples.Sbr.Parse (cell4_load cell4_store cell8_load slot_load slot_store)

variable [CodeEnv]

/-! ## Generic cells -/

omit [CodeEnv] in
/-- A store of the whole of a raw slot. -/
theorem slot_set {m : Mem 64} {a : BitVec 64} {n : Nat} {F : Mem 64 → Prop}
    (h : m =⋆ n ?@ a ⋆ F) (v : Int) : m.storeInt a n v =⋆ (Int.toBytes n v =@ a) ⋆ F := by
  obtain ⟨_, bs, hlen, h'⟩ := Block.sep_elim h
  exact storeInt_sep a n bs F m ⟨h', hlen⟩ v

omit [CodeEnv] in
theorem val_load0 {m : Mem 64} {a : BitVec 64} {l : List UInt8} {F : Mem 64 → Prop}
    (h : m =⋆ (l =@ a) ⋆ F) (hl : l.length < 2 ^ 32) :
    m.loadInt a l.length = some (Int.ofBytes l) :=
  loadInt_sep _ _ _ F m h rfl (by omega)

omit [CodeEnv] in
theorem val_ok0 {m : Mem 64} {a : BitVec 64} {l : List UInt8} {F : Mem 64 → Prop}
    (h : m =⋆ (l =@ a) ⋆ F) (hl : l.length < 2 ^ 32) : (m.loadInt a l.length).isSome = true := by
  rw [val_load0 h hl]; rfl

omit [CodeEnv] in
/-- Two adjacent 4-byte cells as one 8-byte region. -/
theorem cell44 (a : BitVec 64) (u w : BitVec 32) :
    (cell4 a u ⋆ cell4 (a + 4#64) w : Mem 64 → Prop)
      = (Int.toBytes 4 u.toInt ++ Int.toBytes 4 w.toInt) =@ a := by
  simp only [cell4, Val]
  rw [At_append_sep _ _ _ (by simp [Int.toBytes_length]), Int.toBytes_length]

omit [CodeEnv] in
/-- An 8-byte store over two adjacent 4-byte cells. -/
theorem cell44_store {m : Mem 64} {a : BitVec 64} {u w : BitVec 32} {F : Mem 64 → Prop}
    (h : m =⋆ cell4 a u ⋆ (cell4 (a + 4#64) w ⋆ F)) (lo hi : BitVec 32) (V : Int)
    (hV : Int.toBytes 8 V = Int.toBytes 4 lo.toInt ++ Int.toBytes 4 hi.toInt) :
    m.storeInt a 8 V =⋆ cell4 a lo ⋆ (cell4 (a + 4#64) hi ⋆ F) := by
  rw [← Std.ExtHashMap.sep_assoc, cell44] at h ⊢
  have := storeInt_sep a 8 _ F m ⟨h, by simp [Int.toBytes_length]⟩ V
  rw [hV] at this
  exact this

omit [CodeEnv] in
theorem cell44_ok {m : Mem 64} {a : BitVec 64} {u w : BitVec 32} {F : Mem 64 → Prop}
    (h : m =⋆ cell4 a u ⋆ (cell4 (a + 4#64) w ⋆ F)) : (m.loadInt a 8).isSome = true := by
  rw [← Std.ExtHashMap.sep_assoc, cell44] at h
  have := val_ok0 h (by simp [Int.toBytes_length])
  simp only [List.length_append, Int.toBytes_length] at this
  exact this

/-! ## Focus equations -/

/-- `SbWu` without `start`, `ready`. -/
abbrev SbX_sr (s : BitVec 64) (u : BitVec 32) (st : HSt) : Mem 64 → Prop :=
  cell4 (s + 0x10#64) u ⋆ (cell4 (s + 0x18#64) st.reset ⋆ (st.sp =@ (s + 0x1c#64) ⋆ (cell4 (s + 0x24#64) st.amp ⋆ (cell4 (s + 0x2c#64) st.lb ⋆ (cell4 (s + 0x30#64) st.lg ⋆ (cell4 (s + 0x34#64) st.ip ⋆ (cell4 (s + 0x38#64) st.sm)))))))

omit [CodeEnv] in
theorem SbW_sr (s : BitVec 64) (u : BitVec 32) (st : HSt) :
    SbWu s u st = cell4 (s + 0x4#64) st.start ⋆ (cell4 (s + 0x8#64) st.ready ⋆ (SbX_sr s u st)) := by
  simp only [SbWu, SbX_sr] <;> ac_rfl

/-- `SbWu` without `us`. -/
abbrev SbX_us (s : BitVec 64) (u : BitVec 32) (st : HSt) : Mem 64 → Prop :=
  cell4 (s + 0x4#64) st.start ⋆ (cell4 (s + 0x8#64) st.ready ⋆ (cell4 (s + 0x18#64) st.reset ⋆ (st.sp =@ (s + 0x1c#64) ⋆ (cell4 (s + 0x24#64) st.amp ⋆ (cell4 (s + 0x2c#64) st.lb ⋆ (cell4 (s + 0x30#64) st.lg ⋆ (cell4 (s + 0x34#64) st.ip ⋆ (cell4 (s + 0x38#64) st.sm))))))))

omit [CodeEnv] in
theorem SbW_us (s : BitVec 64) (u : BitVec 32) (st : HSt) :
    SbWu s u st = cell4 (s + 0x10#64) u ⋆ (SbX_us s u st) := by
  simp only [SbWu, SbX_us] <;> ac_rfl

/-- `SbWu` without `reset`. -/
abbrev SbX_reset (s : BitVec 64) (u : BitVec 32) (st : HSt) : Mem 64 → Prop :=
  cell4 (s + 0x4#64) st.start ⋆ (cell4 (s + 0x8#64) st.ready ⋆ (cell4 (s + 0x10#64) u ⋆ (st.sp =@ (s + 0x1c#64) ⋆ (cell4 (s + 0x24#64) st.amp ⋆ (cell4 (s + 0x2c#64) st.lb ⋆ (cell4 (s + 0x30#64) st.lg ⋆ (cell4 (s + 0x34#64) st.ip ⋆ (cell4 (s + 0x38#64) st.sm))))))))

omit [CodeEnv] in
theorem SbW_reset (s : BitVec 64) (u : BitVec 32) (st : HSt) :
    SbWu s u st = cell4 (s + 0x18#64) st.reset ⋆ (SbX_reset s u st) := by
  simp only [SbWu, SbX_reset] <;> ac_rfl

/-- `SbWu` without `sp`. -/
abbrev SbX_sp (s : BitVec 64) (u : BitVec 32) (st : HSt) : Mem 64 → Prop :=
  cell4 (s + 0x4#64) st.start ⋆ (cell4 (s + 0x8#64) st.ready ⋆ (cell4 (s + 0x10#64) u ⋆ (cell4 (s + 0x18#64) st.reset ⋆ (cell4 (s + 0x24#64) st.amp ⋆ (cell4 (s + 0x2c#64) st.lb ⋆ (cell4 (s + 0x30#64) st.lg ⋆ (cell4 (s + 0x34#64) st.ip ⋆ (cell4 (s + 0x38#64) st.sm))))))))

omit [CodeEnv] in
theorem SbW_sp (s : BitVec 64) (u : BitVec 32) (st : HSt) :
    SbWu s u st = st.sp =@ (s + 0x1c#64) ⋆ (SbX_sp s u st) := by
  simp only [SbWu, SbX_sp] <;> ac_rfl

/-- `SbWu` without `amp`. -/
abbrev SbX_amp (s : BitVec 64) (u : BitVec 32) (st : HSt) : Mem 64 → Prop :=
  cell4 (s + 0x4#64) st.start ⋆ (cell4 (s + 0x8#64) st.ready ⋆ (cell4 (s + 0x10#64) u ⋆ (cell4 (s + 0x18#64) st.reset ⋆ (st.sp =@ (s + 0x1c#64) ⋆ (cell4 (s + 0x2c#64) st.lb ⋆ (cell4 (s + 0x30#64) st.lg ⋆ (cell4 (s + 0x34#64) st.ip ⋆ (cell4 (s + 0x38#64) st.sm))))))))

omit [CodeEnv] in
theorem SbW_amp (s : BitVec 64) (u : BitVec 32) (st : HSt) :
    SbWu s u st = cell4 (s + 0x24#64) st.amp ⋆ (SbX_amp s u st) := by
  simp only [SbWu, SbX_amp] <;> ac_rfl

/-- `SbWu` without `lb`. -/
abbrev SbX_lb (s : BitVec 64) (u : BitVec 32) (st : HSt) : Mem 64 → Prop :=
  cell4 (s + 0x4#64) st.start ⋆ (cell4 (s + 0x8#64) st.ready ⋆ (cell4 (s + 0x10#64) u ⋆ (cell4 (s + 0x18#64) st.reset ⋆ (st.sp =@ (s + 0x1c#64) ⋆ (cell4 (s + 0x24#64) st.amp ⋆ (cell4 (s + 0x30#64) st.lg ⋆ (cell4 (s + 0x34#64) st.ip ⋆ (cell4 (s + 0x38#64) st.sm))))))))

omit [CodeEnv] in
theorem SbW_lb (s : BitVec 64) (u : BitVec 32) (st : HSt) :
    SbWu s u st = cell4 (s + 0x2c#64) st.lb ⋆ (SbX_lb s u st) := by
  simp only [SbWu, SbX_lb] <;> ac_rfl

/-- `SbWu` without `lg`. -/
abbrev SbX_lg (s : BitVec 64) (u : BitVec 32) (st : HSt) : Mem 64 → Prop :=
  cell4 (s + 0x4#64) st.start ⋆ (cell4 (s + 0x8#64) st.ready ⋆ (cell4 (s + 0x10#64) u ⋆ (cell4 (s + 0x18#64) st.reset ⋆ (st.sp =@ (s + 0x1c#64) ⋆ (cell4 (s + 0x24#64) st.amp ⋆ (cell4 (s + 0x2c#64) st.lb ⋆ (cell4 (s + 0x34#64) st.ip ⋆ (cell4 (s + 0x38#64) st.sm))))))))

omit [CodeEnv] in
theorem SbW_lg (s : BitVec 64) (u : BitVec 32) (st : HSt) :
    SbWu s u st = cell4 (s + 0x30#64) st.lg ⋆ (SbX_lg s u st) := by
  simp only [SbWu, SbX_lg] <;> ac_rfl

/-- `SbWu` without `ip`. -/
abbrev SbX_ip (s : BitVec 64) (u : BitVec 32) (st : HSt) : Mem 64 → Prop :=
  cell4 (s + 0x4#64) st.start ⋆ (cell4 (s + 0x8#64) st.ready ⋆ (cell4 (s + 0x10#64) u ⋆ (cell4 (s + 0x18#64) st.reset ⋆ (st.sp =@ (s + 0x1c#64) ⋆ (cell4 (s + 0x24#64) st.amp ⋆ (cell4 (s + 0x2c#64) st.lb ⋆ (cell4 (s + 0x30#64) st.lg ⋆ (cell4 (s + 0x38#64) st.sm))))))))

omit [CodeEnv] in
theorem SbW_ip (s : BitVec 64) (u : BitVec 32) (st : HSt) :
    SbWu s u st = cell4 (s + 0x34#64) st.ip ⋆ (SbX_ip s u st) := by
  simp only [SbWu, SbX_ip] <;> ac_rfl

/-- `SbWu` without `sm`. -/
abbrev SbX_sm (s : BitVec 64) (u : BitVec 32) (st : HSt) : Mem 64 → Prop :=
  cell4 (s + 0x4#64) st.start ⋆ (cell4 (s + 0x8#64) st.ready ⋆ (cell4 (s + 0x10#64) u ⋆ (cell4 (s + 0x18#64) st.reset ⋆ (st.sp =@ (s + 0x1c#64) ⋆ (cell4 (s + 0x24#64) st.amp ⋆ (cell4 (s + 0x2c#64) st.lb ⋆ (cell4 (s + 0x30#64) st.lg ⋆ (cell4 (s + 0x34#64) st.ip))))))))

omit [CodeEnv] in
theorem SbW_sm (s : BitVec 64) (u : BitVec 32) (st : HSt) :
    SbWu s u st = cell4 (s + 0x38#64) st.sm ⋆ (SbX_sm s u st) := by
  simp only [SbWu, SbX_sm] <;> ac_rfl

/-- `SbWu` without `lb`, `lg`. -/
abbrev SbX_lblg (s : BitVec 64) (u : BitVec 32) (st : HSt) : Mem 64 → Prop :=
  cell4 (s + 0x4#64) st.start ⋆ (cell4 (s + 0x8#64) st.ready ⋆ (cell4 (s + 0x10#64) u ⋆ (cell4 (s + 0x18#64) st.reset ⋆ (st.sp =@ (s + 0x1c#64) ⋆ (cell4 (s + 0x24#64) st.amp ⋆ (cell4 (s + 0x34#64) st.ip ⋆ (cell4 (s + 0x38#64) st.sm)))))))

omit [CodeEnv] in
theorem SbW_lblg (s : BitVec 64) (u : BitVec 32) (st : HSt) :
    SbWu s u st = cell4 (s + 0x2c#64) st.lb ⋆ (cell4 (s + 0x30#64) st.lg ⋆ (SbX_lblg s u st)) := by
  simp only [SbWu, SbX_lblg] <;> ac_rfl

abbrev Mx_i (u : BitVec 32) (k : Nat) (x : HArgs) (ra : Int64) (t₀ : MachineData) (Fm : Mem 64 → Prop) (st : HSt)
    (Tl : Mem 64 → Prop) : Mem 64 → Prop :=
  SbWu (arg0 t₀) u st ⋆ (Int.toBytes 8 x.buf.toInt =@ arg1 t₀ ⋆ (4 ?@ (arg1 t₀ + 0xc#64) ⋆ (cell4 (arg1 t₀ + 0x10#64) x.p8 ⋆ (Blocks [(x.buf, x.L)] ⋆ (Tl ⋆ (Fm ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x30#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x30#64) ⋆ (Rest x.R ra t₀)))))))))

omit [CodeEnv] in
theorem M_i (u : BitVec 32) (k : Nat) (x : HArgs) (ra : Int64) (t₀ : MachineData) (Fm : Mem 64 → Prop) (st : HSt)
    (Tl : Mem 64 → Prop) :
    MU u k x ra t₀ Fm st Tl = cell4 (arg1 t₀ + 8#64) st.i ⋆ (Mx_i u k x ra t₀ Fm st Tl) := by
  simp only [MU, MtU, Mx_i, GbW] <;> ac_rfl

abbrev Mx_p8 (u : BitVec 32) (k : Nat) (x : HArgs) (ra : Int64) (t₀ : MachineData) (Fm : Mem 64 → Prop) (st : HSt)
    (Tl : Mem 64 → Prop) : Mem 64 → Prop :=
  SbWu (arg0 t₀) u st ⋆ (Int.toBytes 8 x.buf.toInt =@ arg1 t₀ ⋆ (cell4 (arg1 t₀ + 8#64) st.i ⋆ (4 ?@ (arg1 t₀ + 0xc#64) ⋆ (Blocks [(x.buf, x.L)] ⋆ (Tl ⋆ (Fm ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x30#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x30#64) ⋆ (Rest x.R ra t₀)))))))))

omit [CodeEnv] in
theorem M_p8 (u : BitVec 32) (k : Nat) (x : HArgs) (ra : Int64) (t₀ : MachineData) (Fm : Mem 64 → Prop) (st : HSt)
    (Tl : Mem 64 → Prop) :
    MU u k x ra t₀ Fm st Tl = cell4 (arg1 t₀ + 0x10#64) x.p8 ⋆ (Mx_p8 u k x ra t₀ Fm st Tl) := by
  simp only [MU, MtU, Mx_p8, GbW] <;> ac_rfl

abbrev Mx_buf (u : BitVec 32) (k : Nat) (x : HArgs) (ra : Int64) (t₀ : MachineData) (Fm : Mem 64 → Prop) (st : HSt)
    (Tl : Mem 64 → Prop) : Mem 64 → Prop :=
  SbWu (arg0 t₀) u st ⋆ (cell4 (arg1 t₀ + 8#64) st.i ⋆ (4 ?@ (arg1 t₀ + 0xc#64) ⋆ (cell4 (arg1 t₀ + 0x10#64) x.p8 ⋆ (Blocks [(x.buf, x.L)] ⋆ (Tl ⋆ (Fm ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x30#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x30#64) ⋆ (Rest x.R ra t₀)))))))))

omit [CodeEnv] in
theorem M_buf (u : BitVec 32) (k : Nat) (x : HArgs) (ra : Int64) (t₀ : MachineData) (Fm : Mem 64 → Prop) (st : HSt)
    (Tl : Mem 64 → Prop) :
    MU u k x ra t₀ Fm st Tl = Int.toBytes 8 x.buf.toInt =@ arg1 t₀ ⋆ (Mx_buf u k x ra t₀ Fm st Tl) := by
  simp only [MU, MtU, Mx_buf, GbW] <;> ac_rfl

abbrev Mx_blk (u : BitVec 32) (k : Nat) (x : HArgs) (ra : Int64) (t₀ : MachineData) (Fm : Mem 64 → Prop) (st : HSt)
    (Tl : Mem 64 → Prop) : Mem 64 → Prop :=
  SbWu (arg0 t₀) u st ⋆ (Int.toBytes 8 x.buf.toInt =@ arg1 t₀ ⋆ (cell4 (arg1 t₀ + 8#64) st.i ⋆ (4 ?@ (arg1 t₀ + 0xc#64) ⋆ (cell4 (arg1 t₀ + 0x10#64) x.p8 ⋆ (Tl ⋆ (Fm ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x30#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x30#64) ⋆ (Rest x.R ra t₀)))))))))

omit [CodeEnv] in
theorem M_blk (u : BitVec 32) (k : Nat) (x : HArgs) (ra : Int64) (t₀ : MachineData) (Fm : Mem 64 → Prop) (st : HSt)
    (Tl : Mem 64 → Prop) :
    MU u k x ra t₀ Fm st Tl = Blocks [(x.buf, x.L)] ⋆ (Mx_blk u k x ra t₀ Fm st Tl) := by
  simp only [MU, MtU, Mx_blk, GbW] <;> ac_rfl

abbrev Mx_fm (u : BitVec 32) (k : Nat) (x : HArgs) (ra : Int64) (t₀ : MachineData) (Fm : Mem 64 → Prop) (st : HSt)
    (Tl : Mem 64 → Prop) : Mem 64 → Prop :=
  SbWu (arg0 t₀) u st ⋆ (Int.toBytes 8 x.buf.toInt =@ arg1 t₀ ⋆ (cell4 (arg1 t₀ + 8#64) st.i ⋆ (4 ?@ (arg1 t₀ + 0xc#64) ⋆ (cell4 (arg1 t₀ + 0x10#64) x.p8 ⋆ (Blocks [(x.buf, x.L)] ⋆ (Tl ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x30#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x30#64) ⋆ (Rest x.R ra t₀)))))))))

omit [CodeEnv] in
theorem M_fm (u : BitVec 32) (k : Nat) (x : HArgs) (ra : Int64) (t₀ : MachineData) (Fm : Mem 64 → Prop) (st : HSt)
    (Tl : Mem 64 → Prop) :
    MU u k x ra t₀ Fm st Tl = Fm ⋆ (Mx_fm u k x ra t₀ Fm st Tl) := by
  simp only [MU, MtU, Mx_fm, GbW] <;> ac_rfl

abbrev Mx_call (u : BitVec 32) (k : Nat) (x : HArgs) (ra : Int64) (t₀ : MachineData) (Fm : Mem 64 → Prop) (st : HSt)
    (Tl : Mem 64 → Prop) : Mem 64 → Prop :=
  SbWu (arg0 t₀) u st ⋆ (Int.toBytes 8 x.buf.toInt =@ arg1 t₀ ⋆ (cell4 (arg1 t₀ + 8#64) st.i ⋆ (4 ?@ (arg1 t₀ + 0xc#64) ⋆ (cell4 (arg1 t₀ + 0x10#64) x.p8 ⋆ (Blocks [(x.buf, x.L)] ⋆ (Fm ⋆ (Rest x.R ra t₀)))))))

omit [CodeEnv] in
theorem M_call (u : BitVec 32) (k : Nat) (x : HArgs) (ra : Int64) (t₀ : MachineData) (Fm : Mem 64 → Prop) (st : HSt)
    (Tl : Mem 64 → Prop) :
    MU u k x ra t₀ Fm st Tl = Tl ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x30#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x30#64) ⋆ (Mx_call u k x ra t₀ Fm st Tl))) := by
  simp only [MU, MtU, Mx_call, GbW] <;> ac_rfl


/-! ## Accesses through `M` -/

section Acc

variable {m : Mem 64} {u : BitVec 32} {k : Nat} {x : HArgs} {ra : Int64} {t₀ : MachineData}
  {Fm : Mem 64 → Prop} {st : HSt} {Tl : Mem 64 → Prop}

omit [CodeEnv]

theorem M_sbw : MU u k x ra t₀ Fm st Tl = SbWu (arg0 t₀) u st ⋆ (GbW (arg1 t₀) x st.i
    ⋆ (Blocks [(x.buf, x.L)] ⋆ (Tl ⋆ (Fm ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x30#64)
    ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x30#64) ⋆ Rest x.R ra t₀)))))) := rfl

theorem M_ld_i (h : m =⋆ MU u k x ra t₀ Fm st Tl) :
    m.loadInt (arg1 t₀ + 8#64) 4 = some (Int.ofBytes (Int.toBytes 4 st.i.toInt)) := by
  rw [M_i] at h; exact cell4_load h

theorem M_ld_p8 (h : m =⋆ MU u k x ra t₀ Fm st Tl) :
    m.loadInt (arg1 t₀ + 0x10#64) 4 = some (Int.ofBytes (Int.toBytes 4 x.p8.toInt)) := by
  rw [M_p8] at h; exact cell4_load h

theorem M_ld_buf (h : m =⋆ MU u k x ra t₀ Fm st Tl) :
    m.loadInt (arg1 t₀) 8 = some (Int.ofBytes (Int.toBytes 8 x.buf.toInt)) := by
  rw [M_buf] at h; exact loadInt_sep _ _ 8 _ m h (Int.toBytes_length 8 _) (by omega)

theorem M_st_i (h : m =⋆ MU u k x ra t₀ Fm st Tl) (v : BitVec 32) :
    m.storeInt (arg1 t₀ + 8#64) 4 v.toInt =⋆ MU u k x ra t₀ Fm { st with i := v } Tl := by
  rw [M_i] at h; rw [M_i]; exact cell4_store h v

theorem M_ok_i (h : m =⋆ MU u k x ra t₀ Fm st Tl) : (m.loadInt (arg1 t₀ + 8#64) 4).isSome = true := by
  rw [M_ld_i h]; rfl

theorem M_ld_bytes (h : m =⋆ MU u k x ra t₀ Fm st Tl) (off : BitVec 64) (n : Nat)
    (hin : off.toNat + n ≤ x.L) : (m.loadInt (x.buf + off) n).isSome = true := by
  rw [M_blk] at h; exact Kraken.Examples.Sbr.Parse.blocks_load h hin

theorem M_ld_lb (h : m =⋆ MU u k x ra t₀ Fm st Tl) :
    m.loadInt (arg0 t₀ + 0x2c#64) 4 = some (Int.ofBytes (Int.toBytes 4 st.lb.toInt)) := by
  rw [M_sbw, SbW_lb, Std.ExtHashMap.sep_assoc] at h; exact cell4_load h

theorem M_ld_reset (h : m =⋆ MU u k x ra t₀ Fm st Tl) :
    m.loadInt (arg0 t₀ + 0x18#64) 4 = some (Int.ofBytes (Int.toBytes 4 st.reset.toInt)) := by
  rw [M_sbw, SbW_reset, Std.ExtHashMap.sep_assoc] at h; exact cell4_load h

theorem M_st_reset (h : m =⋆ MU u k x ra t₀ Fm st Tl) (v : BitVec 32) :
    m.storeInt (arg0 t₀ + 0x18#64) 4 v.toInt =⋆ MU u k x ra t₀ Fm { st with reset := v } Tl := by
  rw [M_sbw, SbW_reset, Std.ExtHashMap.sep_assoc] at h; rw [M_sbw, SbW_reset, Std.ExtHashMap.sep_assoc]; exact cell4_store h v

theorem M_st_amp (h : m =⋆ MU u k x ra t₀ Fm st Tl) (v : BitVec 32) :
    m.storeInt (arg0 t₀ + 0x24#64) 4 v.toInt =⋆ MU u k x ra t₀ Fm { st with amp := v } Tl := by
  rw [M_sbw, SbW_amp, Std.ExtHashMap.sep_assoc] at h; rw [M_sbw, SbW_amp, Std.ExtHashMap.sep_assoc]; exact cell4_store h v

theorem M_st_lb (h : m =⋆ MU u k x ra t₀ Fm st Tl) (v : BitVec 32) :
    m.storeInt (arg0 t₀ + 0x2c#64) 4 v.toInt =⋆ MU u k x ra t₀ Fm { st with lb := v } Tl := by
  rw [M_sbw, SbW_lb, Std.ExtHashMap.sep_assoc] at h; rw [M_sbw, SbW_lb, Std.ExtHashMap.sep_assoc]; exact cell4_store h v

theorem M_st_lg (h : m =⋆ MU u k x ra t₀ Fm st Tl) (v : BitVec 32) :
    m.storeInt (arg0 t₀ + 0x30#64) 4 v.toInt =⋆ MU u k x ra t₀ Fm { st with lg := v } Tl := by
  rw [M_sbw, SbW_lg, Std.ExtHashMap.sep_assoc] at h; rw [M_sbw, SbW_lg, Std.ExtHashMap.sep_assoc]; exact cell4_store h v

theorem M_st_ip (h : m =⋆ MU u k x ra t₀ Fm st Tl) (v : BitVec 32) :
    m.storeInt (arg0 t₀ + 0x34#64) 4 v.toInt =⋆ MU u k x ra t₀ Fm { st with ip := v } Tl := by
  rw [M_sbw, SbW_ip, Std.ExtHashMap.sep_assoc] at h; rw [M_sbw, SbW_ip, Std.ExtHashMap.sep_assoc]; exact cell4_store h v

theorem M_st_sm (h : m =⋆ MU u k x ra t₀ Fm st Tl) (v : BitVec 32) :
    m.storeInt (arg0 t₀ + 0x38#64) 4 v.toInt =⋆ MU u k x ra t₀ Fm { st with sm := v } Tl := by
  rw [M_sbw, SbW_sm, Std.ExtHashMap.sep_assoc] at h; rw [M_sbw, SbW_sm, Std.ExtHashMap.sep_assoc]; exact cell4_store h v

theorem M_ok_reset (h : m =⋆ MU u k x ra t₀ Fm st Tl) :
    (m.loadInt (arg0 t₀ + 0x18#64) 4).isSome = true := by rw [M_ld_reset h]; rfl
theorem M_ok_amp (h : m =⋆ MU u k x ra t₀ Fm st Tl) :
    (m.loadInt (arg0 t₀ + 0x24#64) 4).isSome = true := by
  rw [M_sbw, SbW_amp, Std.ExtHashMap.sep_assoc] at h; rw [cell4_load h]; rfl
theorem M_ok_lb (h : m =⋆ MU u k x ra t₀ Fm st Tl) :
    (m.loadInt (arg0 t₀ + 0x2c#64) 4).isSome = true := by rw [M_ld_lb h]; rfl
theorem M_ok_lg (h : m =⋆ MU u k x ra t₀ Fm st Tl) :
    (m.loadInt (arg0 t₀ + 0x30#64) 4).isSome = true := by
  rw [M_sbw, SbW_lg, Std.ExtHashMap.sep_assoc] at h; rw [cell4_load h]; rfl
theorem M_ok_ip (h : m =⋆ MU u k x ra t₀ Fm st Tl) :
    (m.loadInt (arg0 t₀ + 0x34#64) 4).isSome = true := by
  rw [M_sbw, SbW_ip, Std.ExtHashMap.sep_assoc] at h; rw [cell4_load h]; rfl
theorem M_ok_sm (h : m =⋆ MU u k x ra t₀ Fm st Tl) :
    (m.loadInt (arg0 t₀ + 0x38#64) 4).isSome = true := by
  rw [M_sbw, SbW_sm, Std.ExtHashMap.sep_assoc] at h; rw [cell4_load h]; rfl

/-- `mov %edx, 0x10(%rdi)`: `sbr->usac = v`. -/
theorem M_st_us (h : m =⋆ MU u k x ra t₀ Fm st Tl) (v : BitVec 32) :
    m.storeInt (arg0 t₀ + 0x10#64) 4 v.toInt =⋆ MU v k x ra t₀ Fm st Tl := by
  rw [M_sbw, SbW_us, Std.ExtHashMap.sep_assoc] at h; rw [M_sbw, SbW_us, Std.ExtHashMap.sep_assoc]; exact cell4_store h v

theorem M_ok_us (h : m =⋆ MU u k x ra t₀ Fm st Tl) :
    (m.loadInt (arg0 t₀ + 0x10#64) 4).isSome = true := by
  rw [M_sbw, SbW_us, Std.ExtHashMap.sep_assoc] at h; rw [cell4_load h]; rfl

/-- `movq $1, 4(%rdi)`: `start = 1`, `ready_for_dequant = 0`. -/
theorem M_st_sr (h : m =⋆ MU u k x ra t₀ Fm st Tl) :
    m.storeInt (arg0 t₀ + 0x4#64) 8 (1 : Int)
      =⋆ MU u k x ra t₀ Fm { st with start := 1#32, ready := 0#32 } Tl := by
  rw [M_sbw, SbW_sr, Std.ExtHashMap.sep_assoc, Std.ExtHashMap.sep_assoc, show arg0 t₀ + 0x8#64 = arg0 t₀ + 0x4#64 + 4#64 by
    rw [BitVec.add_assoc]; rfl] at h
  rw [M_sbw, SbW_sr, Std.ExtHashMap.sep_assoc, Std.ExtHashMap.sep_assoc, show arg0 t₀ + 0x8#64 = arg0 t₀ + 0x4#64 + 4#64 by
    rw [BitVec.add_assoc]; rfl]
  exact cell44_store h (1#32) (0#32) _ (by decide)

theorem M_ok_sr (h : m =⋆ MU u k x ra t₀ Fm st Tl) :
    (m.loadInt (arg0 t₀ + 0x4#64) 8).isSome = true := by
  rw [M_sbw, SbW_sr, Std.ExtHashMap.sep_assoc, Std.ExtHashMap.sep_assoc, show arg0 t₀ + 0x8#64 = arg0 t₀ + 0x4#64 + 4#64 by
    rw [BitVec.add_assoc]; rfl] at h
  exact cell44_ok h

/-- `movabs $0x200000002; mov %rax, 0x2c(%rdi)`: `bs_limiter_bands = bs_limiter_gains = 2`. -/
theorem M_st_lblg (h : m =⋆ MU u k x ra t₀ Fm st Tl) :
    m.storeInt (arg0 t₀ + 0x2c#64) 8 (0x200000002 : Int)
      =⋆ MU u k x ra t₀ Fm { st with lb := 2#32, lg := 2#32 } Tl := by
  rw [M_sbw, SbW_lblg, Std.ExtHashMap.sep_assoc, Std.ExtHashMap.sep_assoc, show arg0 t₀ + 0x30#64 = arg0 t₀ + 0x2c#64 + 4#64 by
    rw [BitVec.add_assoc]; rfl] at h
  rw [M_sbw, SbW_lblg, Std.ExtHashMap.sep_assoc, Std.ExtHashMap.sep_assoc, show arg0 t₀ + 0x30#64 = arg0 t₀ + 0x2c#64 + 4#64 by
    rw [BitVec.add_assoc]; rfl]
  exact cell44_store h (2#32) (2#32) _ (by decide)

theorem M_ok_lblg (h : m =⋆ MU u k x ra t₀ Fm st Tl) :
    (m.loadInt (arg0 t₀ + 0x2c#64) 8).isSome = true := by
  rw [M_sbw, SbW_lblg, Std.ExtHashMap.sep_assoc, Std.ExtHashMap.sep_assoc, show arg0 t₀ + 0x30#64 = arg0 t₀ + 0x2c#64 + 4#64 by
    rw [BitVec.add_assoc]; rfl] at h
  exact cell44_ok h

/-- `spectrum_params`, `n` bytes at offset `o`. -/
theorem M_ld_sp (h : m =⋆ MU u k x ra t₀ Fm st Tl) (o n : Nat) (hin : o + n ≤ st.sp.length)
    (hl : st.sp.length < 2 ^ 32) :
    m.loadInt (arg0 t₀ + BitVec.ofNat 64 (0x1c + o)) n
      = some (Int.ofBytes ((st.sp.drop o).take n)) := by
  rw [M_sbw, SbW_sp, Std.ExtHashMap.sep_assoc] at h
  rw [BitVec.ofNat_add, ← BitVec.add_assoc]
  exact val_load h o n hin hl

theorem M_st_sp (h : m =⋆ MU u k x ra t₀ Fm st Tl) (o n : Nat) (hin : o + n ≤ st.sp.length)
    (hl : st.sp.length < 2 ^ 32) (v : Int) :
    m.storeInt (arg0 t₀ + BitVec.ofNat 64 (0x1c + o)) n v
      =⋆ MU u k x ra t₀ Fm { st with sp := st.sp.take o ++ Int.toBytes n v ++ st.sp.drop (o + n) } Tl := by
  rw [M_sbw, SbW_sp, Std.ExtHashMap.sep_assoc] at h
  rw [BitVec.ofNat_add, ← BitVec.add_assoc, M_sbw, SbW_sp, Std.ExtHashMap.sep_assoc]
  exact val_store h o n hin hl v

theorem M_ok_sp (h : m =⋆ MU u k x ra t₀ Fm st Tl) (o n : Nat) (hin : o + n ≤ st.sp.length)
    (hl : st.sp.length < 2 ^ 32) :
    (m.loadInt (arg0 t₀ + BitVec.ofNat 64 (0x1c + o)) n).isSome = true := by
  rw [M_ld_sp h o n hin hl]; rfl

end Acc

end Kraken.Examples.Sbr.Hdr
