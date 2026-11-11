import Kraken.X64.Examples.Sbr.ApplyText
import Kraken.X64.Examples.Sbr.ApplySpec

/-!
# `ff_aac_sbr_apply`: the control flow, the footprint, the table

`libavcodec/aacsbr_template.c` (FFmpeg n8.1), `ff_aac_sbr_apply(ac, che, id_aac, L, R)`
from the `-c opt` object (`aacsbr.o`). The text (`ApplyText.lean`) is cut into 434 blocks (a
label at every jump target, after every call, and inside long runs); each block's body is a
separate definition `B.<id>` and the text is their concatenation, so the control-flow
rule reads the block list without reducing the text (`Kraken/Rules/CfgTable.lean`).

The table is position-indexed (`Program.LTable`): the entry of the `i`-th label is the
`i`-th entry of `ENT`; `T.<id>` rewrites the table at a literal label to its entry.
Block obligations (`BlockOb`) are stated on the literal block and proved in the
phase files `Apply/<Phase>.lean`; `Apply.lean` assembles them with
`ProcSpec.of_cfg_post_pre`.
-/

open Kraken Kraken.X64.Parser Std.WP MachineWP Kraken.SysV Mem

namespace Kraken.Examples.Sbr.Apply

/-- The `hlive` argument of `env_wf` / `ga_facts`. -/
theorem ChLive.live {t : MachineData} {ch : Nat} {y : Args} (h : ChLive t ch y)
    (hs : y.start ≠ 0) : ch ≠ 0 → y.idAac = 1#32 := fun hc => (h.1 hs).trans (h.2 hc)
theorem IdLive.turnoff {t : MachineData} {y : Args} : IdLive t y.turnoff := fun h => absurd rfl h
theorem IdLive.of_start0 {t : MachineData} {y : Args} (h : y.start = 0) : IdLive t y :=
  fun h' => absurd h h'
theorem IdLive.of_eq {t : MachineData} {y : Args} (h : y.idAac = BitVec.setWidth 32 (arg2 t)) :
    IdLive t y := fun _ => h
theorem ChLive.turnoff {t : MachineData} {ch : Nat} {y : Args} (h : ChLive t ch y) :
    ChLive t ch y.turnoff := ⟨IdLive.turnoff, h.2⟩
theorem ChLive.zero {t : MachineData} {y : Args} (h : IdLive t y) : ChLive t 0 y :=
  ⟨h, fun h0 => absurd rfl h0⟩
theorem ChLive.one {t : MachineData} {y : Args} (h : IdLive t y)
    (hc : BitVec.setWidth 32 (arg2 t) = 1#32) : ChLive t 1 y := ⟨h, fun _ => hc⟩

variable [CodeEnv]

theorem Args.KeepT.rfl' {x : Args} : x.KeepT x := by
  unfold Args.KeepT
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Or.inr ⟨rfl, rfl, rfl⟩⟩

/-- `sbr_turnoff` (with its `spectrum_params` memset) keeps the tables and clears `start`. -/
theorem Args.KeepT.turnoff {x y : Args} (h : x.KeepT y) : x.KeepT y.turnoff.spSet := by
  unfold Args.KeepT at h ⊢
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, -⟩ := h
  exact ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, Or.inl ⟨rfl, rfl, rfl⟩⟩

theorem Args.KeepD.rfl' {x : Args} : x.KeepD x :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Args.KeepT.rfl'⟩

theorem Args.Keep.rfl' {x : Args} : x.Keep x :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Args.KeepD.rfl'⟩

/-- `sbr_turnoff` keeps what `Keep` fixes (`start = 0`: the clear case of `KeepT`). -/
theorem Args.Keep.turnoff {x y : Args} (h : x.Keep y) : x.Keep y.turnoff.spSet := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, d1, d2, d3, d4, d5, d6, d7, d8, d9, ht⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, d1, d2, d3, d4, d5, d6, d7, d8, d9, ht.turnoff⟩

/-- The `kx_and_m_pushed` step keeps what `Keep` fixes. -/
theorem Args.Keep.push {x y : Args} (h : x.Keep y) : x.Keep y.push := h

/-- `DWF` with a stronger liveness guard. -/
theorem DWF.mono {L L' : Prop} {v : DV} (hL : L' → L) (h : DWF L v) : DWF L' v := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, fun h => a16 (hL h)⟩

/-- `sbr_turnoff` keeps the invariant (`kx[1] = 32`, `m[1] = 0`; the clauses under
`start ≠ 0` become vacuous). -/
theorem ApplyC.turnoff {y : Args} {t : MachineData} (h : ApplyC y t) : ApplyC y.turnoff t := by
  obtain ⟨⟨h1, -, h3, -, -, h6, h7, h8, h9, h10, h11, h12, -, hd0, hd1, hps⟩, hL⟩ := h
  exact ⟨⟨h1, Nat.le_refl _, h3, (by decide : 32 + 0 ≤ 64), Nat.zero_le _, h6, h7, h8, h9, h10, h11, h12,
    fun h => (h rfl).elim, hd0.mono fun h => (h rfl).elim, hd1.mono fun h => (h.1 rfl).elim, hps⟩, hL⟩

/-- A 4-byte cell loaded into a 32-bit register and stored back: the same bytes. -/
theorem Int.toBytes4_reload (v : Int) :
    Int.toBytes 4 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.ofInt 32 (Int.ofBytes (Int.toBytes 4 v))))).toInt
      = Int.toBytes 4 v := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq, BitVec.toInt_ofInt,
    ← Int.toBytes_emod, Int.take]
  have h : (Int.ofBytes (Int.toBytes 4 v)).bmod (2 ^ 32) % (2 ^ (8 * 4) : Int)
      = Int.ofBytes (Int.toBytes 4 v) % 2 ^ (8 * 4) := Int.bmod_emod
  rw [h, show Int.ofBytes (Int.toBytes 4 v) % 2 ^ (8 * 4) = (Int.ofBytes (Int.toBytes 4 v)).take (8 * 4)
    from rfl, Int.toBytes_emod, Int.toBytes_ofBytes_toBytes]

/-- The `kx_and_m_pushed` step keeps the invariant: the new `kx[0]`, `m[0]` are `kx[1]`, `m[1]`
(bounded by the `kx[1]`/`m[1]` clauses) or unchanged. -/
theorem ApplyC.push {y : Args} {t : MachineData} (h : ApplyC y t) : ApplyC y.push t := by
  obtain ⟨⟨h1, h2, h3, h4, rest⟩, hL⟩ := h
  by_cases hp : y.pushed = 0
  · exact ⟨⟨by simpa only [hp, if_true] using h2, h2, by simpa only [hp, if_true] using h4, h4, rest⟩, hL⟩
  · exact ⟨⟨by simpa only [hp, if_false] using h1, h2, by simpa only [hp, if_false] using h3, h4, rest⟩, hL⟩

/-- The `push` step touches only `kx[0]`, `m[0]`, `pushed`: the other groups do not see it. -/
@[simp] theorem TabW_push (x : Args) (t : MachineData) : TabW x.push t = TabW x t := rfl
@[simp] theorem FnW_push (e : Env) (x : Args) (t : MachineData) : FnW e x.push t = FnW e x t := rfl
@[simp] theorem AcW_push (x : Args) (t : MachineData) : AcW x.push t = AcW x t := rfl
@[simp] theorem OutW_push (x : Args) (t : MachineData) : OutW x.push t = OutW x t := rfl
/-- `PsW` reads only `psc`/`psh`: `push` and `turnoff` do not change it (not `@[simp]`, so the
plain `simp` calls of already-checked blocks are unaffected; use by name). -/
theorem PsW_push (x : Args) (t : MachineData) : PsW x.push t = PsW x t := rfl
theorem PsW_turnoff (x : Args) (t : MachineData) : PsW x.turnoff t = PsW x t := rfl

/-- The `spectrum_params` memset touches no field `ApplyC`, `IdLive`, `ChLive` read. -/
theorem ApplyC.spSet {y : Args} {t : MachineData} (h : ApplyC y t) : ApplyC y.spSet t := h
theorem IdLive.spSet {t : MachineData} {y : Args} (h : IdLive t y) : IdLive t y.spSet := h
theorem ChLive.spSet {t : MachineData} {ch : Nat} {y : Args} (h : ChLive t ch y) :
    ChLive t ch y.spSet := h

/-- The low byte after an 8-bit write (`mov $1,%bl`) is the byte written. -/
@[simp] theorem setWidth8_replaceLow (old : BitVec 64) (new : BitVec 8) :
    (old.replaceLow new).setWidth 8 = new := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth]
  exact BitVec.toNat_replaceLow8_mod old new

/-- `setl` after `cmp b, a` (32 bit): signed `a < b`. -/
theorem flags_l_sub32 (a b : BitVec 32) :
    ((a - b).msb != ((a - b).signed != a.signed - b.signed)) = decide (a.toInt < b.toInt) := by
  simp only [BitVec.signed]
  have h1 := BitVec.toInt_sub (x := a) (y := b)
  have h2 : (a - b).msb = decide ((a - b).toInt < 0) := by
    rw [BitVec.msb_eq_toInt]
  have ha := BitVec.toInt_lt (x := a); have ha' := BitVec.le_toInt (x := a)
  have hb := BitVec.toInt_lt (x := b); have hb' := BitVec.le_toInt (x := b)
  rw [h2]
  rw [h1] at *
  simp only [Int.bmod] at *
  generalize a.toInt = x at *
  generalize b.toInt = y at *
  simp only [Nat.reducePow] at *
  have hc : ((4294967296 : Nat) : Int) = 4294967296 := rfl
  simp only [hc] at *
  split
  · by_cases h : (x - y) % 4294967296 = x - y
    · simp only [h, bne_self_eq_false, Bool.bne_false, decide_eq_decide]
      omega
    · have h' : ((x - y) % 4294967296 != x - y) = true := bne_iff_ne.mpr h
      simp only [h', Bool.bne_true, ← decide_not, decide_eq_decide]
      omega
  · by_cases h : (x - y) % 4294967296 - 4294967296 = x - y
    · simp only [h, bne_self_eq_false, Bool.bne_false, decide_eq_decide]
      omega
    · have h' : ((x - y) % 4294967296 - 4294967296 != x - y) = true := bne_iff_ne.mpr h
      simp only [h', Bool.bne_true, ← decide_not, decide_eq_decide]
      omega

/-- `incl %r` (32-bit; the upper half is zeroed). Missing from `IntMisc` (which has `decl`). -/
@[spec low] theorem inc_reg_w32_spec {p : Program} {Q : Unit → MachineData → Prop}
    {E : Int64 → MachineData → Prop} (asz : Width) (r : Reg64) :
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
      MachineData.set, MachineData.setReg, Reg64s.get_low64, Reg64s.set_low64, Effects.All]
    (try simp only [Reg64s.get_low32, Reg64s.set_low32])
    exact hP)

/-- The `setl` byte after `cmp b, a` (32 bit). -/
theorem setl_byte (a b : BitVec 32) (f : StatusFlags.from_result.Remaining)
    (hf : f.of = ((a - b).signed != a.signed - b.signed)) :
    (BitVec.ofNat 8 (CondCode.l.interp (StatusFlags.from_result (a - b) f)).toNat).toInt
      = (((if a.toInt < b.toInt then 1 else 0 : Nat)) : Int) := by
  simp only [CondCode.interp_l, StatusFlags.sf_from_result, StatusFlags.of_from_result, hf, flags_l_sub32]
  by_cases h : a.toInt < b.toInt
  · simp only [h, decide_true, Bool.toNat_true, ite_true]; decide
  · simp only [h, decide_false, Bool.toNat_false, ite_false]; decide

/-! ## The control flow of the text (`ApplyText.lean`) -/

set_option maxRecDepth 200000 in
theorem blocks_free : ∀ lb ∈ blocks, ∀ d ∈ lb.2, d.isLabel = false := by decide +kernel

theorem view_body : Program.view body = ([], blocks) := Program.view_flatMap blocks blocks_free

set_option maxRecDepth 200000 in
theorem labels_body : Program.labels body = labelList := by
  rw [Program.labels_eq_view, view_body]; rfl

/-- A key per label (distinct keys, distinct labels: `labelList_nodup`). -/
def labelKey (s : String) : Nat := s.toList.foldl (fun n c => n * 256 + c.toNat) 0

set_option maxRecDepth 200000 in
theorem labelList_nodup : labelList.Nodup :=
  (List.pairwise_map.mp (show (labelList.map labelKey).Nodup by decide +kernel)).imp
    fun h e => h (congrArg labelKey e)

theorem body_wf : Program.WF body := ⟨labels_body ▸ labelList_nodup⟩

/-- The label questions of a jump to the `i`-th label. -/
theorem blockIdx_at {i : Nat} {l : Label} (h : labelList[i]? = some l) : Program.blockIdx body l = i :=
  Program.blockIdx_of_getElem? body_wf (labels_body ▸ h)

theorem isSome_at {i : Nat} {l : Label} (h : labelList[i]? = some l) :
    (Program.blockAt body l).isSome = true :=
  Program.isSome_blockAt_of_getElem? (labels_body ▸ h)

/-! ## Frames -/

omit [CodeEnv] in
/-- The own slot area as its slots. -/
theorem frame_split (r : BitVec 64) (K : Mem 64 → Prop) :
    0x198 ?@ (r - 0x1c8#64) ⋆ K =
    8 ?@ (r - 0x1c8#64)
    ⋆ (8 ?@ (r - 0x1c0#64)
    ⋆ (8 ?@ (r - 0x1b8#64)
    ⋆ (8 ?@ (r - 0x1b0#64)
    ⋆ (8 ?@ (r - 0x1a8#64)
    ⋆ (8 ?@ (r - 0x1a0#64)
    ⋆ (8 ?@ (r - 0x198#64)
    ⋆ (8 ?@ (r - 0x190#64)
    ⋆ (8 ?@ (r - 0x188#64)
    ⋆ (8 ?@ (r - 0x180#64)
    ⋆ (8 ?@ (r - 0x178#64)
    ⋆ (8 ?@ (r - 0x170#64)
    ⋆ (8 ?@ (r - 0x168#64)
    ⋆ (8 ?@ (r - 0x160#64)
    ⋆ (8 ?@ (r - 0x158#64)
    ⋆ (8 ?@ (r - 0x150#64)
    ⋆ (8 ?@ (r - 0x148#64)
    ⋆ (8 ?@ (r - 0x140#64)
    ⋆ (8 ?@ (r - 0x138#64)
    ⋆ (8 ?@ (r - 0x130#64)
    ⋆ (8 ?@ (r - 0x128#64)
    ⋆ (8 ?@ (r - 0x120#64)
    ⋆ (8 ?@ (r - 0x118#64)
    ⋆ (8 ?@ (r - 0x110#64)
    ⋆ (8 ?@ (r - 0x108#64)
    ⋆ (4 ?@ (r - 0x100#64)
    ⋆ (4 ?@ (r - 0xfc#64)
    ⋆ (8 ?@ (r - 0xf8#64)
    ⋆ (8 ?@ (r - 0xf0#64)
    ⋆ (8 ?@ (r - 0xe8#64)
    ⋆ (8 ?@ (r - 0xe0#64)
    ⋆ (8 ?@ (r - 0xd8#64)
    ⋆ (8 ?@ (r - 0xd0#64)
    ⋆ (8 ?@ (r - 0xc8#64)
    ⋆ (8 ?@ (r - 0xc0#64)
    ⋆ (8 ?@ (r - 0xb8#64)
    ⋆ (8 ?@ (r - 0xb0#64)
    ⋆ (4 ?@ (r - 0xa8#64)
    ⋆ (4 ?@ (r - 0xa4#64)
    ⋆ (8 ?@ (r - 0xa0#64)
    ⋆ (8 ?@ (r - 0x98#64)
    ⋆ (6 ?@ (r - 0x90#64)
    ⋆ (2 ?@ (r - 0x8a#64)
    ⋆ (8 ?@ (r - 0x88#64)
    ⋆ (8 ?@ (r - 0x80#64)
    ⋆ (8 ?@ (r - 0x78#64)
    ⋆ (8 ?@ (r - 0x70#64)
    ⋆ (8 ?@ (r - 0x68#64)
    ⋆ (8 ?@ (r - 0x60#64)
    ⋆ (8 ?@ (r - 0x58#64)
    ⋆ (8 ?@ (r - 0x50#64)
    ⋆ (7 ?@ (r - 0x48#64)
    ⋆ (1 ?@ (r - 0x41#64)
    ⋆ (8 ?@ (r - 0x40#64)
    ⋆ (8 ?@ (r - 0x38#64) ⋆ K)))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  rw [show (0x198 ?@ (r - 0x1c8#64) : Mem 64 → Prop) = 408 ?@ (r - 0x1c8#64) from rfl]
  rw [show (408 ?@ (r - 0x1c8#64) : Mem 64 → Prop) = (8 + 400) ?@ (r - 0x1c8#64) from rfl,
    Block.split (r - 0x1c8#64) 8 400 (by decide), show r - 0x1c8#64 + BitVec.ofNat 64 8 = r - 0x1c0#64 by bv_omega, Std.ExtHashMap.sep_assoc]
  rw [show (400 ?@ (r - 0x1c0#64) : Mem 64 → Prop) = (8 + 392) ?@ (r - 0x1c0#64) from rfl,
    Block.split (r - 0x1c0#64) 8 392 (by decide), show r - 0x1c0#64 + BitVec.ofNat 64 8 = r - 0x1b8#64 by bv_omega, Std.ExtHashMap.sep_assoc]
  rw [show (392 ?@ (r - 0x1b8#64) : Mem 64 → Prop) = (8 + 384) ?@ (r - 0x1b8#64) from rfl,
    Block.split (r - 0x1b8#64) 8 384 (by decide), show r - 0x1b8#64 + BitVec.ofNat 64 8 = r - 0x1b0#64 by bv_omega, Std.ExtHashMap.sep_assoc]
  rw [show (384 ?@ (r - 0x1b0#64) : Mem 64 → Prop) = (8 + 376) ?@ (r - 0x1b0#64) from rfl,
    Block.split (r - 0x1b0#64) 8 376 (by decide), show r - 0x1b0#64 + BitVec.ofNat 64 8 = r - 0x1a8#64 by bv_omega, Std.ExtHashMap.sep_assoc]
  rw [show (376 ?@ (r - 0x1a8#64) : Mem 64 → Prop) = (8 + 368) ?@ (r - 0x1a8#64) from rfl,
    Block.split (r - 0x1a8#64) 8 368 (by decide), show r - 0x1a8#64 + BitVec.ofNat 64 8 = r - 0x1a0#64 by bv_omega, Std.ExtHashMap.sep_assoc]
  rw [show (368 ?@ (r - 0x1a0#64) : Mem 64 → Prop) = (8 + 360) ?@ (r - 0x1a0#64) from rfl,
    Block.split (r - 0x1a0#64) 8 360 (by decide), show r - 0x1a0#64 + BitVec.ofNat 64 8 = r - 0x198#64 by bv_omega, Std.ExtHashMap.sep_assoc]
  rw [show (360 ?@ (r - 0x198#64) : Mem 64 → Prop) = (8 + 352) ?@ (r - 0x198#64) from rfl,
    Block.split (r - 0x198#64) 8 352 (by decide), show r - 0x198#64 + BitVec.ofNat 64 8 = r - 0x190#64 by bv_omega, Std.ExtHashMap.sep_assoc]
  rw [show (352 ?@ (r - 0x190#64) : Mem 64 → Prop) = (8 + 344) ?@ (r - 0x190#64) from rfl,
    Block.split (r - 0x190#64) 8 344 (by decide), show r - 0x190#64 + BitVec.ofNat 64 8 = r - 0x188#64 by bv_omega, Std.ExtHashMap.sep_assoc]
  rw [show (344 ?@ (r - 0x188#64) : Mem 64 → Prop) = (8 + 336) ?@ (r - 0x188#64) from rfl,
    Block.split (r - 0x188#64) 8 336 (by decide), show r - 0x188#64 + BitVec.ofNat 64 8 = r - 0x180#64 by bv_omega, Std.ExtHashMap.sep_assoc]
  rw [show (336 ?@ (r - 0x180#64) : Mem 64 → Prop) = (8 + 328) ?@ (r - 0x180#64) from rfl,
    Block.split (r - 0x180#64) 8 328 (by decide), show r - 0x180#64 + BitVec.ofNat 64 8 = r - 0x178#64 by bv_omega, Std.ExtHashMap.sep_assoc]
  rw [show (328 ?@ (r - 0x178#64) : Mem 64 → Prop) = (8 + 320) ?@ (r - 0x178#64) from rfl,
    Block.split (r - 0x178#64) 8 320 (by decide), show r - 0x178#64 + BitVec.ofNat 64 8 = r - 0x170#64 by bv_omega, Std.ExtHashMap.sep_assoc]
  rw [show (320 ?@ (r - 0x170#64) : Mem 64 → Prop) = (8 + 312) ?@ (r - 0x170#64) from rfl,
    Block.split (r - 0x170#64) 8 312 (by decide), show r - 0x170#64 + BitVec.ofNat 64 8 = r - 0x168#64 by bv_omega, Std.ExtHashMap.sep_assoc]
  rw [show (312 ?@ (r - 0x168#64) : Mem 64 → Prop) = (8 + 304) ?@ (r - 0x168#64) from rfl,
    Block.split (r - 0x168#64) 8 304 (by decide), show r - 0x168#64 + BitVec.ofNat 64 8 = r - 0x160#64 by bv_omega, Std.ExtHashMap.sep_assoc]
  rw [show (304 ?@ (r - 0x160#64) : Mem 64 → Prop) = (8 + 296) ?@ (r - 0x160#64) from rfl,
    Block.split (r - 0x160#64) 8 296 (by decide), show r - 0x160#64 + BitVec.ofNat 64 8 = r - 0x158#64 by bv_omega, Std.ExtHashMap.sep_assoc]
  rw [show (296 ?@ (r - 0x158#64) : Mem 64 → Prop) = (8 + 288) ?@ (r - 0x158#64) from rfl,
    Block.split (r - 0x158#64) 8 288 (by decide), show r - 0x158#64 + BitVec.ofNat 64 8 = r - 0x150#64 by bv_omega, Std.ExtHashMap.sep_assoc]
  rw [show (288 ?@ (r - 0x150#64) : Mem 64 → Prop) = (8 + 280) ?@ (r - 0x150#64) from rfl,
    Block.split (r - 0x150#64) 8 280 (by decide), show r - 0x150#64 + BitVec.ofNat 64 8 = r - 0x148#64 by bv_omega, Std.ExtHashMap.sep_assoc]
  rw [show (280 ?@ (r - 0x148#64) : Mem 64 → Prop) = (8 + 272) ?@ (r - 0x148#64) from rfl,
    Block.split (r - 0x148#64) 8 272 (by decide), show r - 0x148#64 + BitVec.ofNat 64 8 = r - 0x140#64 by bv_omega, Std.ExtHashMap.sep_assoc]
  rw [show (272 ?@ (r - 0x140#64) : Mem 64 → Prop) = (8 + 264) ?@ (r - 0x140#64) from rfl,
    Block.split (r - 0x140#64) 8 264 (by decide), show r - 0x140#64 + BitVec.ofNat 64 8 = r - 0x138#64 by bv_omega, Std.ExtHashMap.sep_assoc]
  rw [show (264 ?@ (r - 0x138#64) : Mem 64 → Prop) = (8 + 256) ?@ (r - 0x138#64) from rfl,
    Block.split (r - 0x138#64) 8 256 (by decide), show r - 0x138#64 + BitVec.ofNat 64 8 = r - 0x130#64 by bv_omega, Std.ExtHashMap.sep_assoc]
  rw [show (256 ?@ (r - 0x130#64) : Mem 64 → Prop) = (8 + 248) ?@ (r - 0x130#64) from rfl,
    Block.split (r - 0x130#64) 8 248 (by decide), show r - 0x130#64 + BitVec.ofNat 64 8 = r - 0x128#64 by bv_omega, Std.ExtHashMap.sep_assoc]
  rw [show (248 ?@ (r - 0x128#64) : Mem 64 → Prop) = (8 + 240) ?@ (r - 0x128#64) from rfl,
    Block.split (r - 0x128#64) 8 240 (by decide), show r - 0x128#64 + BitVec.ofNat 64 8 = r - 0x120#64 by bv_omega, Std.ExtHashMap.sep_assoc]
  rw [show (240 ?@ (r - 0x120#64) : Mem 64 → Prop) = (8 + 232) ?@ (r - 0x120#64) from rfl,
    Block.split (r - 0x120#64) 8 232 (by decide), show r - 0x120#64 + BitVec.ofNat 64 8 = r - 0x118#64 by bv_omega, Std.ExtHashMap.sep_assoc]
  rw [show (232 ?@ (r - 0x118#64) : Mem 64 → Prop) = (8 + 224) ?@ (r - 0x118#64) from rfl,
    Block.split (r - 0x118#64) 8 224 (by decide), show r - 0x118#64 + BitVec.ofNat 64 8 = r - 0x110#64 by bv_omega, Std.ExtHashMap.sep_assoc]
  rw [show (224 ?@ (r - 0x110#64) : Mem 64 → Prop) = (8 + 216) ?@ (r - 0x110#64) from rfl,
    Block.split (r - 0x110#64) 8 216 (by decide), show r - 0x110#64 + BitVec.ofNat 64 8 = r - 0x108#64 by bv_omega, Std.ExtHashMap.sep_assoc]
  rw [show (216 ?@ (r - 0x108#64) : Mem 64 → Prop) = (8 + 208) ?@ (r - 0x108#64) from rfl,
    Block.split (r - 0x108#64) 8 208 (by decide), show r - 0x108#64 + BitVec.ofNat 64 8 = r - 0x100#64 by bv_omega, Std.ExtHashMap.sep_assoc]
  rw [show (208 ?@ (r - 0x100#64) : Mem 64 → Prop) = (4 + 204) ?@ (r - 0x100#64) from rfl,
    Block.split (r - 0x100#64) 4 204 (by decide), show r - 0x100#64 + BitVec.ofNat 64 4 = r - 0xfc#64 by bv_omega, Std.ExtHashMap.sep_assoc]
  rw [show (204 ?@ (r - 0xfc#64) : Mem 64 → Prop) = (4 + 200) ?@ (r - 0xfc#64) from rfl,
    Block.split (r - 0xfc#64) 4 200 (by decide), show r - 0xfc#64 + BitVec.ofNat 64 4 = r - 0xf8#64 by bv_omega, Std.ExtHashMap.sep_assoc]
  rw [show (200 ?@ (r - 0xf8#64) : Mem 64 → Prop) = (8 + 192) ?@ (r - 0xf8#64) from rfl,
    Block.split (r - 0xf8#64) 8 192 (by decide), show r - 0xf8#64 + BitVec.ofNat 64 8 = r - 0xf0#64 by bv_omega, Std.ExtHashMap.sep_assoc]
  rw [show (192 ?@ (r - 0xf0#64) : Mem 64 → Prop) = (8 + 184) ?@ (r - 0xf0#64) from rfl,
    Block.split (r - 0xf0#64) 8 184 (by decide), show r - 0xf0#64 + BitVec.ofNat 64 8 = r - 0xe8#64 by bv_omega, Std.ExtHashMap.sep_assoc]
  rw [show (184 ?@ (r - 0xe8#64) : Mem 64 → Prop) = (8 + 176) ?@ (r - 0xe8#64) from rfl,
    Block.split (r - 0xe8#64) 8 176 (by decide), show r - 0xe8#64 + BitVec.ofNat 64 8 = r - 0xe0#64 by bv_omega, Std.ExtHashMap.sep_assoc]
  rw [show (176 ?@ (r - 0xe0#64) : Mem 64 → Prop) = (8 + 168) ?@ (r - 0xe0#64) from rfl,
    Block.split (r - 0xe0#64) 8 168 (by decide), show r - 0xe0#64 + BitVec.ofNat 64 8 = r - 0xd8#64 by bv_omega, Std.ExtHashMap.sep_assoc]
  rw [show (168 ?@ (r - 0xd8#64) : Mem 64 → Prop) = (8 + 160) ?@ (r - 0xd8#64) from rfl,
    Block.split (r - 0xd8#64) 8 160 (by decide), show r - 0xd8#64 + BitVec.ofNat 64 8 = r - 0xd0#64 by bv_omega, Std.ExtHashMap.sep_assoc]
  rw [show (160 ?@ (r - 0xd0#64) : Mem 64 → Prop) = (8 + 152) ?@ (r - 0xd0#64) from rfl,
    Block.split (r - 0xd0#64) 8 152 (by decide), show r - 0xd0#64 + BitVec.ofNat 64 8 = r - 0xc8#64 by bv_omega, Std.ExtHashMap.sep_assoc]
  rw [show (152 ?@ (r - 0xc8#64) : Mem 64 → Prop) = (8 + 144) ?@ (r - 0xc8#64) from rfl,
    Block.split (r - 0xc8#64) 8 144 (by decide), show r - 0xc8#64 + BitVec.ofNat 64 8 = r - 0xc0#64 by bv_omega, Std.ExtHashMap.sep_assoc]
  rw [show (144 ?@ (r - 0xc0#64) : Mem 64 → Prop) = (8 + 136) ?@ (r - 0xc0#64) from rfl,
    Block.split (r - 0xc0#64) 8 136 (by decide), show r - 0xc0#64 + BitVec.ofNat 64 8 = r - 0xb8#64 by bv_omega, Std.ExtHashMap.sep_assoc]
  rw [show (136 ?@ (r - 0xb8#64) : Mem 64 → Prop) = (8 + 128) ?@ (r - 0xb8#64) from rfl,
    Block.split (r - 0xb8#64) 8 128 (by decide), show r - 0xb8#64 + BitVec.ofNat 64 8 = r - 0xb0#64 by bv_omega, Std.ExtHashMap.sep_assoc]
  rw [show (128 ?@ (r - 0xb0#64) : Mem 64 → Prop) = (8 + 120) ?@ (r - 0xb0#64) from rfl,
    Block.split (r - 0xb0#64) 8 120 (by decide), show r - 0xb0#64 + BitVec.ofNat 64 8 = r - 0xa8#64 by bv_omega, Std.ExtHashMap.sep_assoc]
  rw [show (120 ?@ (r - 0xa8#64) : Mem 64 → Prop) = (4 + 116) ?@ (r - 0xa8#64) from rfl,
    Block.split (r - 0xa8#64) 4 116 (by decide), show r - 0xa8#64 + BitVec.ofNat 64 4 = r - 0xa4#64 by bv_omega, Std.ExtHashMap.sep_assoc]
  rw [show (116 ?@ (r - 0xa4#64) : Mem 64 → Prop) = (4 + 112) ?@ (r - 0xa4#64) from rfl,
    Block.split (r - 0xa4#64) 4 112 (by decide), show r - 0xa4#64 + BitVec.ofNat 64 4 = r - 0xa0#64 by bv_omega, Std.ExtHashMap.sep_assoc]
  rw [show (112 ?@ (r - 0xa0#64) : Mem 64 → Prop) = (8 + 104) ?@ (r - 0xa0#64) from rfl,
    Block.split (r - 0xa0#64) 8 104 (by decide), show r - 0xa0#64 + BitVec.ofNat 64 8 = r - 0x98#64 by bv_omega, Std.ExtHashMap.sep_assoc]
  rw [show (104 ?@ (r - 0x98#64) : Mem 64 → Prop) = (8 + 96) ?@ (r - 0x98#64) from rfl,
    Block.split (r - 0x98#64) 8 96 (by decide), show r - 0x98#64 + BitVec.ofNat 64 8 = r - 0x90#64 by bv_omega, Std.ExtHashMap.sep_assoc]
  rw [show (96 ?@ (r - 0x90#64) : Mem 64 → Prop) = (6 + 90) ?@ (r - 0x90#64) from rfl,
    Block.split (r - 0x90#64) 6 90 (by decide), show r - 0x90#64 + BitVec.ofNat 64 6 = r - 0x8a#64 by bv_omega, Std.ExtHashMap.sep_assoc]
  rw [show (90 ?@ (r - 0x8a#64) : Mem 64 → Prop) = (2 + 88) ?@ (r - 0x8a#64) from rfl,
    Block.split (r - 0x8a#64) 2 88 (by decide), show r - 0x8a#64 + BitVec.ofNat 64 2 = r - 0x88#64 by bv_omega, Std.ExtHashMap.sep_assoc]
  rw [show (88 ?@ (r - 0x88#64) : Mem 64 → Prop) = (8 + 80) ?@ (r - 0x88#64) from rfl,
    Block.split (r - 0x88#64) 8 80 (by decide), show r - 0x88#64 + BitVec.ofNat 64 8 = r - 0x80#64 by bv_omega, Std.ExtHashMap.sep_assoc]
  rw [show (80 ?@ (r - 0x80#64) : Mem 64 → Prop) = (8 + 72) ?@ (r - 0x80#64) from rfl,
    Block.split (r - 0x80#64) 8 72 (by decide), show r - 0x80#64 + BitVec.ofNat 64 8 = r - 0x78#64 by bv_omega, Std.ExtHashMap.sep_assoc]
  rw [show (72 ?@ (r - 0x78#64) : Mem 64 → Prop) = (8 + 64) ?@ (r - 0x78#64) from rfl,
    Block.split (r - 0x78#64) 8 64 (by decide), show r - 0x78#64 + BitVec.ofNat 64 8 = r - 0x70#64 by bv_omega, Std.ExtHashMap.sep_assoc]
  rw [show (64 ?@ (r - 0x70#64) : Mem 64 → Prop) = (8 + 56) ?@ (r - 0x70#64) from rfl,
    Block.split (r - 0x70#64) 8 56 (by decide), show r - 0x70#64 + BitVec.ofNat 64 8 = r - 0x68#64 by bv_omega, Std.ExtHashMap.sep_assoc]
  rw [show (56 ?@ (r - 0x68#64) : Mem 64 → Prop) = (8 + 48) ?@ (r - 0x68#64) from rfl,
    Block.split (r - 0x68#64) 8 48 (by decide), show r - 0x68#64 + BitVec.ofNat 64 8 = r - 0x60#64 by bv_omega, Std.ExtHashMap.sep_assoc]
  rw [show (48 ?@ (r - 0x60#64) : Mem 64 → Prop) = (8 + 40) ?@ (r - 0x60#64) from rfl,
    Block.split (r - 0x60#64) 8 40 (by decide), show r - 0x60#64 + BitVec.ofNat 64 8 = r - 0x58#64 by bv_omega, Std.ExtHashMap.sep_assoc]
  rw [show (40 ?@ (r - 0x58#64) : Mem 64 → Prop) = (8 + 32) ?@ (r - 0x58#64) from rfl,
    Block.split (r - 0x58#64) 8 32 (by decide), show r - 0x58#64 + BitVec.ofNat 64 8 = r - 0x50#64 by bv_omega, Std.ExtHashMap.sep_assoc]
  rw [show (32 ?@ (r - 0x50#64) : Mem 64 → Prop) = (8 + 24) ?@ (r - 0x50#64) from rfl,
    Block.split (r - 0x50#64) 8 24 (by decide), show r - 0x50#64 + BitVec.ofNat 64 8 = r - 0x48#64 by bv_omega, Std.ExtHashMap.sep_assoc]
  rw [show (24 ?@ (r - 0x48#64) : Mem 64 → Prop) = (7 + 17) ?@ (r - 0x48#64) from rfl,
    Block.split (r - 0x48#64) 7 17 (by decide), show r - 0x48#64 + BitVec.ofNat 64 7 = r - 0x41#64 by bv_omega, Std.ExtHashMap.sep_assoc]
  rw [show (17 ?@ (r - 0x41#64) : Mem 64 → Prop) = (1 + 16) ?@ (r - 0x41#64) from rfl,
    Block.split (r - 0x41#64) 1 16 (by decide), show r - 0x41#64 + BitVec.ofNat 64 1 = r - 0x40#64 by bv_omega, Std.ExtHashMap.sep_assoc]
  rw [show (16 ?@ (r - 0x40#64) : Mem 64 → Prop) = (8 + 8) ?@ (r - 0x40#64) from rfl,
    Block.split (r - 0x40#64) 8 8 (by decide), show r - 0x40#64 + BitVec.ofNat 64 8 = r - 0x38#64 by bv_omega, Std.ExtHashMap.sep_assoc]


/-- The frame with every slot raw. -/
abbrev FrRaw (t₀ : MachineData) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x1c8#64)
    ⋆ (8 ?@ (r - 0x1c0#64)
    ⋆ (8 ?@ (r - 0x1b8#64)
    ⋆ (8 ?@ (r - 0x1b0#64)
    ⋆ (8 ?@ (r - 0x1a8#64)
    ⋆ (8 ?@ (r - 0x1a0#64)
    ⋆ (8 ?@ (r - 0x198#64)
    ⋆ (8 ?@ (r - 0x190#64)
    ⋆ (8 ?@ (r - 0x188#64)
    ⋆ (8 ?@ (r - 0x180#64)
    ⋆ (8 ?@ (r - 0x178#64)
    ⋆ (8 ?@ (r - 0x170#64)
    ⋆ (8 ?@ (r - 0x168#64)
    ⋆ (8 ?@ (r - 0x160#64)
    ⋆ (8 ?@ (r - 0x158#64)
    ⋆ (8 ?@ (r - 0x150#64)
    ⋆ (8 ?@ (r - 0x148#64)
    ⋆ (8 ?@ (r - 0x140#64)
    ⋆ (8 ?@ (r - 0x138#64)
    ⋆ (8 ?@ (r - 0x130#64)
    ⋆ (8 ?@ (r - 0x128#64)
    ⋆ (8 ?@ (r - 0x120#64)
    ⋆ (8 ?@ (r - 0x118#64)
    ⋆ (8 ?@ (r - 0x110#64)
    ⋆ (8 ?@ (r - 0x108#64)
    ⋆ (4 ?@ (r - 0x100#64)
    ⋆ (4 ?@ (r - 0xfc#64)
    ⋆ (8 ?@ (r - 0xf8#64)
    ⋆ (8 ?@ (r - 0xf0#64)
    ⋆ (8 ?@ (r - 0xe8#64)
    ⋆ (8 ?@ (r - 0xe0#64)
    ⋆ (8 ?@ (r - 0xd8#64)
    ⋆ (8 ?@ (r - 0xd0#64)
    ⋆ (8 ?@ (r - 0xc8#64)
    ⋆ (8 ?@ (r - 0xc0#64)
    ⋆ (8 ?@ (r - 0xb8#64)
    ⋆ (8 ?@ (r - 0xb0#64)
    ⋆ (4 ?@ (r - 0xa8#64)
    ⋆ (4 ?@ (r - 0xa4#64)
    ⋆ (8 ?@ (r - 0xa0#64)
    ⋆ (8 ?@ (r - 0x98#64)
    ⋆ (6 ?@ (r - 0x90#64)
    ⋆ (2 ?@ (r - 0x8a#64)
    ⋆ (8 ?@ (r - 0x88#64)
    ⋆ (8 ?@ (r - 0x80#64)
    ⋆ (8 ?@ (r - 0x78#64)
    ⋆ (8 ?@ (r - 0x70#64)
    ⋆ (8 ?@ (r - 0x68#64)
    ⋆ (8 ?@ (r - 0x60#64)
    ⋆ (8 ?@ (r - 0x58#64)
    ⋆ (8 ?@ (r - 0x50#64)
    ⋆ (7 ?@ (r - 0x48#64)
    ⋆ (1 ?@ (r - 0x41#64)
    ⋆ (8 ?@ (r - 0x40#64)
    ⋆ (8 ?@ (r - 0x38#64)
    ⋆ (c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ Kt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

abbrev FrC (x : Args) (t₀ : MachineData) (ch : Nat) (c0 : BitVec 32) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x1c8#64)
    ⋆ (c8 (r - 0x1c0#64) (sbrA t₀ + 0x4c284#64)
    ⋆ (c8 (r - 0x1b8#64) (sbrA t₀ + 0x4c252#64)
    ⋆ (c8 (r - 0x1b0#64) (sbrA t₀ + 0x5e340#64)
    ⋆ (c8 (r - 0x1a8#64) (BitVec.ofNat 64 ch)
    ⋆ (c8 (r - 0x1a0#64) (sbrA t₀ + 0x4c288#64)
    ⋆ (c8 (r - 0x198#64) (sbrA t₀ + 0x4eb50#64)
    ⋆ (c8 (r - 0x190#64) (sbrA t₀ + 0x5dd40#64)
    ⋆ (c8 (r - 0x188#64) (sbrA t₀ + 0xb2#64)
    ⋆ (c8 (r - 0x180#64) (sbrA t₀ + 0x5e4c0#64)
    ⋆ (c8 (r - 0x178#64) (sbrA t₀ + 0x5f0c0#64)
    ⋆ (c8 (r - 0x170#64) (sbrA t₀ + 0x1c#64)
    ⋆ (c8 (r - 0x168#64) (sbrA t₀ + 0x150e0#64)
    ⋆ (c8 (r - 0x160#64) (sbrA t₀ + 0x5f6c4#64)
    ⋆ (c8 (r - 0x158#64) (BitVec.ofNat 64 (dsN x))
    ⋆ (c8 (r - 0x150#64) (sbrA t₀ + 0x5d340#64)
    ⋆ (c8 (r - 0x148#64) (sbrA t₀ + 0x5d540#64)
    ⋆ (c8 (r - 0x140#64) (sbrA t₀ + 0x80#64)
    ⋆ (c8 (r - 0x138#64) (arg3 t₀)
    ⋆ (c8 (r - 0x130#64) (arg4 t₀)
    ⋆ (c8 (r - 0x128#64) (sbrA t₀ + 0x601e0#64)
    ⋆ (c8 (r - 0x120#64) (sbrA t₀ + 0x5fcc0#64)
    ⋆ (8 ?@ (r - 0x118#64)
    ⋆ (c8 (r - 0x110#64) (sbrA t₀ + 0x5eac0#64)
    ⋆ (c8 (r - 0x108#64) (sbrA t₀ + 0x5f6c0#64)
    ⋆ (Int.toBytes 4 (c0.toInt) =@ (r - 0x100#64)
    ⋆ (4 ?@ (r - 0xfc#64)
    ⋆ (c8 (r - 0xf8#64) (lab "sbr_qmf_window_ds")
    ⋆ (8 ?@ (r - 0xf0#64)
    ⋆ (8 ?@ (r - 0xe8#64)
    ⋆ (8 ?@ (r - 0xe0#64)
    ⋆ (c8 (r - 0xd8#64) (sbrA t₀ + 0x5d740#64)
    ⋆ (c8 (r - 0xd0#64) (sbrA t₀ + 0x5fdc0#64)
    ⋆ (c8 (r - 0xc8#64) (sbrA t₀ + 0x4c340#64)
    ⋆ (c8 (r - 0xc0#64) (sbrA t₀ + 0x4eb40#64)
    ⋆ (c8 (r - 0xb8#64) (sbrA t₀)
    ⋆ (c8 (r - 0xb0#64) (sbrA t₀ + 0x53b40#64)
    ⋆ (4 ?@ (r - 0xa8#64)
    ⋆ (Int.toBytes 4 ((BitVec.setWidth 32 (arg2 t₀)).toInt) =@ (r - 0xa4#64)
    ⋆ (c8 (r - 0xa0#64) (BitVec.ofNat 64 (0x15ac0 * ch))
    ⋆ (c8 (r - 0x98#64) (arg0 t₀)
    ⋆ (6 ?@ (r - 0x90#64)
    ⋆ (2 ?@ (r - 0x8a#64)
    ⋆ (8 ?@ (r - 0x88#64)
    ⋆ (8 ?@ (r - 0x80#64)
    ⋆ (c8 (r - 0x78#64) (sbrA t₀ + 0x4ec90#64)
    ⋆ (8 ?@ (r - 0x70#64)
    ⋆ (8 ?@ (r - 0x68#64)
    ⋆ (8 ?@ (r - 0x60#64)
    ⋆ (8 ?@ (r - 0x58#64)
    ⋆ (c8 (r - 0x50#64) (dA t₀ ch)
    ⋆ (7 ?@ (r - 0x48#64)
    ⋆ (1 ?@ (r - 0x41#64)
    ⋆ (c8 (r - 0x40#64) (arg1 t₀)
    ⋆ (8 ?@ (r - 0x38#64)
    ⋆ (c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ Kt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

abbrev FrL (x : Args) (t₀ : MachineData) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x1c8#64)
    ⋆ (c8 (r - 0x1c0#64) (sbrA t₀ + 0x4c284#64)
    ⋆ (c8 (r - 0x1b8#64) (sbrA t₀ + 0x4c252#64)
    ⋆ (c8 (r - 0x1b0#64) (sbrA t₀ + 0x5e340#64)
    ⋆ (8 ?@ (r - 0x1a8#64)
    ⋆ (c8 (r - 0x1a0#64) (sbrA t₀ + 0x4c288#64)
    ⋆ (c8 (r - 0x198#64) (sbrA t₀ + 0x4eb50#64)
    ⋆ (c8 (r - 0x190#64) (sbrA t₀ + 0x5dd40#64)
    ⋆ (c8 (r - 0x188#64) (sbrA t₀ + 0xb2#64)
    ⋆ (c8 (r - 0x180#64) (sbrA t₀ + 0x5e4c0#64)
    ⋆ (c8 (r - 0x178#64) (sbrA t₀ + 0x5f0c0#64)
    ⋆ (c8 (r - 0x170#64) (sbrA t₀ + 0x1c#64)
    ⋆ (c8 (r - 0x168#64) (sbrA t₀ + 0x150e0#64)
    ⋆ (c8 (r - 0x160#64) (sbrA t₀ + 0x5f6c4#64)
    ⋆ (c8 (r - 0x158#64) (BitVec.ofNat 64 (dsN x))
    ⋆ (c8 (r - 0x150#64) (sbrA t₀ + 0x5d340#64)
    ⋆ (c8 (r - 0x148#64) (sbrA t₀ + 0x5d540#64)
    ⋆ (c8 (r - 0x140#64) (sbrA t₀ + 0x80#64)
    ⋆ (c8 (r - 0x138#64) (arg3 t₀)
    ⋆ (c8 (r - 0x130#64) (arg4 t₀)
    ⋆ (c8 (r - 0x128#64) (sbrA t₀ + 0x601e0#64)
    ⋆ (c8 (r - 0x120#64) (sbrA t₀ + 0x5fcc0#64)
    ⋆ (8 ?@ (r - 0x118#64)
    ⋆ (c8 (r - 0x110#64) (sbrA t₀ + 0x5eac0#64)
    ⋆ (c8 (r - 0x108#64) (sbrA t₀ + 0x5f6c0#64)
    ⋆ (4 ?@ (r - 0x100#64)
    ⋆ (4 ?@ (r - 0xfc#64)
    ⋆ (c8 (r - 0xf8#64) (lab "sbr_qmf_window_ds")
    ⋆ (8 ?@ (r - 0xf0#64)
    ⋆ (8 ?@ (r - 0xe8#64)
    ⋆ (8 ?@ (r - 0xe0#64)
    ⋆ (c8 (r - 0xd8#64) (sbrA t₀ + 0x5d740#64)
    ⋆ (c8 (r - 0xd0#64) (sbrA t₀ + 0x5fdc0#64)
    ⋆ (c8 (r - 0xc8#64) (sbrA t₀ + 0x4c340#64)
    ⋆ (c8 (r - 0xc0#64) (sbrA t₀ + 0x4eb40#64)
    ⋆ (c8 (r - 0xb8#64) (sbrA t₀)
    ⋆ (c8 (r - 0xb0#64) (sbrA t₀ + 0x53b40#64)
    ⋆ (4 ?@ (r - 0xa8#64)
    ⋆ (Int.toBytes 4 ((BitVec.setWidth 32 (arg2 t₀)).toInt) =@ (r - 0xa4#64)
    ⋆ (8 ?@ (r - 0xa0#64)
    ⋆ (c8 (r - 0x98#64) (arg0 t₀)
    ⋆ (6 ?@ (r - 0x90#64)
    ⋆ (2 ?@ (r - 0x8a#64)
    ⋆ (8 ?@ (r - 0x88#64)
    ⋆ (8 ?@ (r - 0x80#64)
    ⋆ (c8 (r - 0x78#64) (sbrA t₀ + 0x4ec90#64)
    ⋆ (8 ?@ (r - 0x70#64)
    ⋆ (8 ?@ (r - 0x68#64)
    ⋆ (8 ?@ (r - 0x60#64)
    ⋆ (8 ?@ (r - 0x58#64)
    ⋆ (8 ?@ (r - 0x50#64)
    ⋆ (7 ?@ (r - 0x48#64)
    ⋆ (1 ?@ (r - 0x41#64)
    ⋆ (c8 (r - 0x40#64) (arg1 t₀)
    ⋆ (8 ?@ (r - 0x38#64)
    ⋆ (c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ Kt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

abbrev FrO (x : Args) (t₀ : MachineData) (ch : Nat) (c0 : BitVec 32) (y : Args) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x1c8#64)
    ⋆ (c8 (r - 0x1c0#64) (sbrA t₀ + 0x4c284#64)
    ⋆ (c8 (r - 0x1b8#64) (sbrA t₀ + 0x4c252#64)
    ⋆ (c8 (r - 0x1b0#64) (sbrA t₀ + 0x5e340#64)
    ⋆ (c8 (r - 0x1a8#64) (BitVec.ofNat 64 ch)
    ⋆ (c8 (r - 0x1a0#64) (sbrA t₀ + 0x4c288#64)
    ⋆ (c8 (r - 0x198#64) (sbrA t₀ + 0x4eb50#64)
    ⋆ (c8 (r - 0x190#64) (sbrA t₀ + 0x5dd40#64)
    ⋆ (c8 (r - 0x188#64) (sbrA t₀ + 0xb2#64)
    ⋆ (c8 (r - 0x180#64) (sbrA t₀ + 0x5e4c0#64)
    ⋆ (c8 (r - 0x178#64) (sbrA t₀ + 0x5f0c0#64)
    ⋆ (c8 (r - 0x170#64) (sbrA t₀ + 0x1c#64)
    ⋆ (c8 (r - 0x168#64) (sbrA t₀ + 0x150e0#64)
    ⋆ (c8 (r - 0x160#64) (sbrA t₀ + 0x5f6c4#64)
    ⋆ (c8 (r - 0x158#64) (BitVec.ofNat 64 (dsN x))
    ⋆ (c8 (r - 0x150#64) (sbrA t₀ + 0x5d340#64)
    ⋆ (c8 (r - 0x148#64) (sbrA t₀ + 0x5d540#64)
    ⋆ (c8 (r - 0x140#64) (sbrA t₀ + 0x80#64)
    ⋆ (c8 (r - 0x138#64) (arg3 t₀)
    ⋆ (c8 (r - 0x130#64) (arg4 t₀)
    ⋆ (c8 (r - 0x128#64) (sbrA t₀ + 0x601e0#64)
    ⋆ (c8 (r - 0x120#64) (sbrA t₀ + 0x5fcc0#64)
    ⋆ (8 ?@ (r - 0x118#64)
    ⋆ (c8 (r - 0x110#64) (sbrA t₀ + 0x5eac0#64)
    ⋆ (c8 (r - 0x108#64) (sbrA t₀ + 0x5f6c0#64)
    ⋆ (Int.toBytes 4 (c0.toInt) =@ (r - 0x100#64)
    ⋆ (4 ?@ (r - 0xfc#64)
    ⋆ (c8 (r - 0xf8#64) (lab "sbr_qmf_window_ds")
    ⋆ (8 ?@ (r - 0xf0#64)
    ⋆ (8 ?@ (r - 0xe8#64)
    ⋆ (8 ?@ (r - 0xe0#64)
    ⋆ (c8 (r - 0xd8#64) (sbrA t₀ + 0x5d740#64)
    ⋆ (c8 (r - 0xd0#64) (sbrA t₀ + 0x5fdc0#64)
    ⋆ (c8 (r - 0xc8#64) (sbrA t₀ + 0x4c340#64)
    ⋆ (c8 (r - 0xc0#64) (sbrA t₀ + 0x4eb40#64)
    ⋆ (c8 (r - 0xb8#64) (sbrA t₀)
    ⋆ (c8 (r - 0xb0#64) (sbrA t₀ + 0x53b40#64)
    ⋆ (4 ?@ (r - 0xa8#64)
    ⋆ (Int.toBytes 4 ((BitVec.setWidth 32 (arg2 t₀)).toInt) =@ (r - 0xa4#64)
    ⋆ (c8 (r - 0xa0#64) (BitVec.ofNat 64 (0x15ac0 * ch))
    ⋆ (c8 (r - 0x98#64) (arg0 t₀)
    ⋆ (6 ?@ (r - 0x90#64)
    ⋆ (2 ?@ (r - 0x8a#64)
    ⋆ (8 ?@ (r - 0x88#64)
    ⋆ (8 ?@ (r - 0x80#64)
    ⋆ (c8 (r - 0x78#64) (sbrA t₀ + 0x4ec90#64)
    ⋆ (8 ?@ (r - 0x70#64)
    ⋆ (8 ?@ (r - 0x68#64)
    ⋆ (8 ?@ (r - 0x60#64)
    ⋆ (8 ?@ (r - 0x58#64)
    ⋆ (c8 (r - 0x50#64) (dA t₀ ch)
    ⋆ (7 ?@ (r - 0x48#64)
    ⋆ (1 ?@ (r - 0x41#64)
    ⋆ (c8 (r - 0x40#64) (arg1 t₀)
    ⋆ (Int.toBytes 4 (BitVec.ofNat 32 y.kx1).toInt =@ (r - 0x38#64) ⋆ 4 ?@ (r - 0x34#64)
    ⋆ (c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ Kt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

abbrev FrO8 (x : Args) (t₀ : MachineData) (ch : Nat) (c0 : BitVec 32) (y : Args) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x1c8#64)
    ⋆ (c8 (r - 0x1c0#64) (sbrA t₀ + 0x4c284#64)
    ⋆ (c8 (r - 0x1b8#64) (sbrA t₀ + 0x4c252#64)
    ⋆ (c8 (r - 0x1b0#64) (sbrA t₀ + 0x5e340#64)
    ⋆ (c8 (r - 0x1a8#64) (BitVec.ofNat 64 ch)
    ⋆ (c8 (r - 0x1a0#64) (sbrA t₀ + 0x4c288#64)
    ⋆ (c8 (r - 0x198#64) (sbrA t₀ + 0x4eb50#64)
    ⋆ (c8 (r - 0x190#64) (sbrA t₀ + 0x5dd40#64)
    ⋆ (c8 (r - 0x188#64) (sbrA t₀ + 0xb2#64)
    ⋆ (c8 (r - 0x180#64) (sbrA t₀ + 0x5e4c0#64)
    ⋆ (c8 (r - 0x178#64) (sbrA t₀ + 0x5f0c0#64)
    ⋆ (c8 (r - 0x170#64) (sbrA t₀ + 0x1c#64)
    ⋆ (c8 (r - 0x168#64) (sbrA t₀ + 0x150e0#64)
    ⋆ (c8 (r - 0x160#64) (sbrA t₀ + 0x5f6c4#64)
    ⋆ (c8 (r - 0x158#64) (BitVec.ofNat 64 (dsN x))
    ⋆ (c8 (r - 0x150#64) (sbrA t₀ + 0x5d340#64)
    ⋆ (c8 (r - 0x148#64) (sbrA t₀ + 0x5d540#64)
    ⋆ (c8 (r - 0x140#64) (sbrA t₀ + 0x80#64)
    ⋆ (c8 (r - 0x138#64) (arg3 t₀)
    ⋆ (c8 (r - 0x130#64) (arg4 t₀)
    ⋆ (c8 (r - 0x128#64) (sbrA t₀ + 0x601e0#64)
    ⋆ (c8 (r - 0x120#64) (sbrA t₀ + 0x5fcc0#64)
    ⋆ (8 ?@ (r - 0x118#64)
    ⋆ (c8 (r - 0x110#64) (sbrA t₀ + 0x5eac0#64)
    ⋆ (c8 (r - 0x108#64) (sbrA t₀ + 0x5f6c0#64)
    ⋆ (Int.toBytes 4 (c0.toInt) =@ (r - 0x100#64)
    ⋆ (4 ?@ (r - 0xfc#64)
    ⋆ (c8 (r - 0xf8#64) (lab "sbr_qmf_window_ds")
    ⋆ (8 ?@ (r - 0xf0#64)
    ⋆ (8 ?@ (r - 0xe8#64)
    ⋆ (8 ?@ (r - 0xe0#64)
    ⋆ (c8 (r - 0xd8#64) (sbrA t₀ + 0x5d740#64)
    ⋆ (c8 (r - 0xd0#64) (sbrA t₀ + 0x5fdc0#64)
    ⋆ (c8 (r - 0xc8#64) (sbrA t₀ + 0x4c340#64)
    ⋆ (c8 (r - 0xc0#64) (sbrA t₀ + 0x4eb40#64)
    ⋆ (c8 (r - 0xb8#64) (sbrA t₀)
    ⋆ (c8 (r - 0xb0#64) (sbrA t₀ + 0x53b40#64)
    ⋆ (4 ?@ (r - 0xa8#64)
    ⋆ (Int.toBytes 4 ((BitVec.setWidth 32 (arg2 t₀)).toInt) =@ (r - 0xa4#64)
    ⋆ (c8 (r - 0xa0#64) (BitVec.ofNat 64 (0x15ac0 * ch))
    ⋆ (c8 (r - 0x98#64) (arg0 t₀)
    ⋆ (6 ?@ (r - 0x90#64)
    ⋆ (2 ?@ (r - 0x8a#64)
    ⋆ (c8 (r - 0x88#64) (dA t₀ ch + 0x15030#64)
    ⋆ (8 ?@ (r - 0x80#64)
    ⋆ (c8 (r - 0x78#64) (sbrA t₀ + 0x4ec90#64)
    ⋆ (8 ?@ (r - 0x70#64)
    ⋆ (8 ?@ (r - 0x68#64)
    ⋆ (8 ?@ (r - 0x60#64)
    ⋆ (8 ?@ (r - 0x58#64)
    ⋆ (c8 (r - 0x50#64) (dA t₀ ch)
    ⋆ (7 ?@ (r - 0x48#64)
    ⋆ (1 ?@ (r - 0x41#64)
    ⋆ (c8 (r - 0x40#64) (arg1 t₀)
    ⋆ (Int.toBytes 4 (BitVec.ofNat 32 y.kx1).toInt =@ (r - 0x38#64) ⋆ 4 ?@ (r - 0x34#64)
    ⋆ (c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ Kt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

abbrev FrCs (x : Args) (t₀ : MachineData) (ch : Nat) (c0 : BitVec 32) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x1c8#64)
    ⋆ (c8 (r - 0x1c0#64) (sbrA t₀ + 0x4c284#64)
    ⋆ (c8 (r - 0x1b8#64) (sbrA t₀ + 0x4c252#64)
    ⋆ (c8 (r - 0x1b0#64) (sbrA t₀ + 0x5e340#64)
    ⋆ (c8 (r - 0x1a8#64) (BitVec.ofNat 64 ch)
    ⋆ (c8 (r - 0x1a0#64) (sbrA t₀ + 0x4c288#64)
    ⋆ (c8 (r - 0x198#64) (sbrA t₀ + 0x4eb50#64)
    ⋆ (c8 (r - 0x190#64) (sbrA t₀ + 0x5dd40#64)
    ⋆ (c8 (r - 0x188#64) (sbrA t₀ + 0xb2#64)
    ⋆ (c8 (r - 0x180#64) (sbrA t₀ + 0x5e4c0#64)
    ⋆ (c8 (r - 0x178#64) (sbrA t₀ + 0x5f0c0#64)
    ⋆ (c8 (r - 0x170#64) (sbrA t₀ + 0x1c#64)
    ⋆ (c8 (r - 0x168#64) (sbrA t₀ + 0x150e0#64)
    ⋆ (c8 (r - 0x160#64) (sbrA t₀ + 0x5f6c4#64)
    ⋆ (c8 (r - 0x158#64) (BitVec.ofNat 64 (dsN x))
    ⋆ (c8 (r - 0x150#64) (sbrA t₀ + 0x5d340#64)
    ⋆ (c8 (r - 0x148#64) (sbrA t₀ + 0x5d540#64)
    ⋆ (c8 (r - 0x140#64) (sbrA t₀ + 0x80#64)
    ⋆ (c8 (r - 0x138#64) (arg3 t₀)
    ⋆ (c8 (r - 0x130#64) (arg4 t₀)
    ⋆ (c8 (r - 0x128#64) (sbrA t₀ + 0x601e0#64)
    ⋆ (c8 (r - 0x120#64) (sbrA t₀ + 0x5fcc0#64)
    ⋆ (8 ?@ (r - 0x118#64)
    ⋆ (c8 (r - 0x110#64) (sbrA t₀ + 0x5eac0#64)
    ⋆ (c8 (r - 0x108#64) (sbrA t₀ + 0x5f6c0#64)
    ⋆ (Int.toBytes 4 (c0.toInt) =@ (r - 0x100#64)
    ⋆ (4 ?@ (r - 0xfc#64)
    ⋆ (c8 (r - 0xf8#64) (lab "sbr_qmf_window_ds")
    ⋆ (8 ?@ (r - 0xf0#64)
    ⋆ (8 ?@ (r - 0xe8#64)
    ⋆ (8 ?@ (r - 0xe0#64)
    ⋆ (c8 (r - 0xd8#64) (sbrA t₀ + 0x5d740#64)
    ⋆ (c8 (r - 0xd0#64) (sbrA t₀ + 0x5fdc0#64)
    ⋆ (c8 (r - 0xc8#64) (sbrA t₀ + 0x4c340#64)
    ⋆ (c8 (r - 0xc0#64) (sbrA t₀ + 0x4eb40#64)
    ⋆ (c8 (r - 0xb8#64) (sbrA t₀)
    ⋆ (c8 (r - 0xb0#64) (sbrA t₀ + 0x53b40#64)
    ⋆ (4 ?@ (r - 0xa8#64)
    ⋆ (Int.toBytes 4 ((BitVec.setWidth 32 (arg2 t₀)).toInt) =@ (r - 0xa4#64)
    ⋆ (8 ?@ (r - 0xa0#64)
    ⋆ (c8 (r - 0x98#64) (arg0 t₀)
    ⋆ (6 ?@ (r - 0x90#64)
    ⋆ (2 ?@ (r - 0x8a#64)
    ⋆ (8 ?@ (r - 0x88#64)
    ⋆ (8 ?@ (r - 0x80#64)
    ⋆ (c8 (r - 0x78#64) (sbrA t₀ + 0x4ec90#64)
    ⋆ (8 ?@ (r - 0x70#64)
    ⋆ (8 ?@ (r - 0x68#64)
    ⋆ (8 ?@ (r - 0x60#64)
    ⋆ (8 ?@ (r - 0x58#64)
    ⋆ (c8 (r - 0x50#64) (dA t₀ ch)
    ⋆ (7 ?@ (r - 0x48#64)
    ⋆ (1 ?@ (r - 0x41#64)
    ⋆ (c8 (r - 0x40#64) (arg1 t₀)
    ⋆ (8 ?@ (r - 0x38#64)
    ⋆ (c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ Kt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

abbrev FrX (x : Args) (t₀ : MachineData) (ch : Nat) (c0 : BitVec 32) (y : Args) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x1c8#64)
    ⋆ (c8 (r - 0x1c0#64) (sbrA t₀ + 0x4c284#64)
    ⋆ (c8 (r - 0x1b8#64) (sbrA t₀ + 0x4c252#64)
    ⋆ (c8 (r - 0x1b0#64) (sbrA t₀ + 0x5e340#64)
    ⋆ (c8 (r - 0x1a8#64) (BitVec.ofNat 64 ch)
    ⋆ (c8 (r - 0x1a0#64) (sbrA t₀ + 0x4c288#64)
    ⋆ (c8 (r - 0x198#64) (sbrA t₀ + 0x4eb50#64)
    ⋆ (c8 (r - 0x190#64) (sbrA t₀ + 0x5dd40#64)
    ⋆ (c8 (r - 0x188#64) (sbrA t₀ + 0xb2#64)
    ⋆ (c8 (r - 0x180#64) (sbrA t₀ + 0x5e4c0#64)
    ⋆ (c8 (r - 0x178#64) (sbrA t₀ + 0x5f0c0#64)
    ⋆ (c8 (r - 0x170#64) (sbrA t₀ + 0x1c#64)
    ⋆ (c8 (r - 0x168#64) (sbrA t₀ + 0x150e0#64)
    ⋆ (c8 (r - 0x160#64) (sbrA t₀ + 0x5f6c4#64)
    ⋆ (c8 (r - 0x158#64) (BitVec.ofNat 64 (dsN x))
    ⋆ (c8 (r - 0x150#64) (sbrA t₀ + 0x5d340#64)
    ⋆ (c8 (r - 0x148#64) (sbrA t₀ + 0x5d540#64)
    ⋆ (c8 (r - 0x140#64) (sbrA t₀ + 0x80#64)
    ⋆ (c8 (r - 0x138#64) (arg3 t₀)
    ⋆ (c8 (r - 0x130#64) (arg4 t₀)
    ⋆ (c8 (r - 0x128#64) (sbrA t₀ + 0x601e0#64)
    ⋆ (c8 (r - 0x120#64) (sbrA t₀ + 0x5fcc0#64)
    ⋆ (c8 (r - 0x118#64) (dA t₀ ch + 0x3904#64)
    ⋆ (c8 (r - 0x110#64) (sbrA t₀ + 0x5eac0#64)
    ⋆ (c8 (r - 0x108#64) (sbrA t₀ + 0x5f6c0#64)
    ⋆ (Int.toBytes 4 (c0.toInt) =@ (r - 0x100#64)
    ⋆ (4 ?@ (r - 0xfc#64)
    ⋆ (c8 (r - 0xf8#64) (lab "sbr_qmf_window_ds")
    ⋆ (8 ?@ (r - 0xf0#64)
    ⋆ (8 ?@ (r - 0xe8#64)
    ⋆ (8 ?@ (r - 0xe0#64)
    ⋆ (c8 (r - 0xd8#64) (sbrA t₀ + 0x5d740#64)
    ⋆ (c8 (r - 0xd0#64) (sbrA t₀ + 0x5fdc0#64)
    ⋆ (c8 (r - 0xc8#64) (sbrA t₀ + 0x4c340#64)
    ⋆ (c8 (r - 0xc0#64) (sbrA t₀ + 0x4eb40#64)
    ⋆ (c8 (r - 0xb8#64) (sbrA t₀)
    ⋆ (c8 (r - 0xb0#64) (sbrA t₀ + 0x53b40#64)
    ⋆ (4 ?@ (r - 0xa8#64)
    ⋆ (Int.toBytes 4 ((BitVec.setWidth 32 (arg2 t₀)).toInt) =@ (r - 0xa4#64)
    ⋆ (c8 (r - 0xa0#64) (BitVec.ofNat 64 (0x15ac0 * ch))
    ⋆ (c8 (r - 0x98#64) (arg0 t₀)
    ⋆ (6 ?@ (r - 0x90#64)
    ⋆ (2 ?@ (r - 0x8a#64)
    ⋆ (8 ?@ (r - 0x88#64)
    ⋆ (8 ?@ (r - 0x80#64)
    ⋆ (c8 (r - 0x78#64) (sbrA t₀ + 0x4ec90#64)
    ⋆ (8 ?@ (r - 0x70#64)
    ⋆ (8 ?@ (r - 0x68#64)
    ⋆ (8 ?@ (r - 0x60#64)
    ⋆ (8 ?@ (r - 0x58#64)
    ⋆ (c8 (r - 0x50#64) (dA t₀ ch)
    ⋆ (7 ?@ (r - 0x48#64)
    ⋆ (1 ?@ (r - 0x41#64)
    ⋆ (c8 (r - 0x40#64) (arg1 t₀)
    ⋆ (4 ?@ (r - 0x38#64) ⋆ 4 ?@ (r - 0x34#64)
    ⋆ (c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ Kt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

abbrev FrA (x : Args) (t₀ : MachineData) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x1c8#64)
    ⋆ (8 ?@ (r - 0x1c0#64)
    ⋆ (8 ?@ (r - 0x1b8#64)
    ⋆ (8 ?@ (r - 0x1b0#64)
    ⋆ (8 ?@ (r - 0x1a8#64)
    ⋆ (8 ?@ (r - 0x1a0#64)
    ⋆ (8 ?@ (r - 0x198#64)
    ⋆ (8 ?@ (r - 0x190#64)
    ⋆ (8 ?@ (r - 0x188#64)
    ⋆ (8 ?@ (r - 0x180#64)
    ⋆ (8 ?@ (r - 0x178#64)
    ⋆ (8 ?@ (r - 0x170#64)
    ⋆ (8 ?@ (r - 0x168#64)
    ⋆ (8 ?@ (r - 0x160#64)
    ⋆ (8 ?@ (r - 0x158#64)
    ⋆ (8 ?@ (r - 0x150#64)
    ⋆ (8 ?@ (r - 0x148#64)
    ⋆ (8 ?@ (r - 0x140#64)
    ⋆ (c8 (r - 0x138#64) (arg3 t₀)
    ⋆ (c8 (r - 0x130#64) (arg4 t₀)
    ⋆ (8 ?@ (r - 0x128#64)
    ⋆ (8 ?@ (r - 0x120#64)
    ⋆ (8 ?@ (r - 0x118#64)
    ⋆ (8 ?@ (r - 0x110#64)
    ⋆ (8 ?@ (r - 0x108#64)
    ⋆ (4 ?@ (r - 0x100#64)
    ⋆ (4 ?@ (r - 0xfc#64)
    ⋆ (8 ?@ (r - 0xf8#64)
    ⋆ (8 ?@ (r - 0xf0#64)
    ⋆ (8 ?@ (r - 0xe8#64)
    ⋆ (8 ?@ (r - 0xe0#64)
    ⋆ (8 ?@ (r - 0xd8#64)
    ⋆ (8 ?@ (r - 0xd0#64)
    ⋆ (8 ?@ (r - 0xc8#64)
    ⋆ (8 ?@ (r - 0xc0#64)
    ⋆ (8 ?@ (r - 0xb8#64)
    ⋆ (8 ?@ (r - 0xb0#64)
    ⋆ (4 ?@ (r - 0xa8#64)
    ⋆ (4 ?@ (r - 0xa4#64)
    ⋆ (8 ?@ (r - 0xa0#64)
    ⋆ (8 ?@ (r - 0x98#64)
    ⋆ (6 ?@ (r - 0x90#64)
    ⋆ (2 ?@ (r - 0x8a#64)
    ⋆ (8 ?@ (r - 0x88#64)
    ⋆ (8 ?@ (r - 0x80#64)
    ⋆ (8 ?@ (r - 0x78#64)
    ⋆ (8 ?@ (r - 0x70#64)
    ⋆ (8 ?@ (r - 0x68#64)
    ⋆ (8 ?@ (r - 0x60#64)
    ⋆ (8 ?@ (r - 0x58#64)
    ⋆ (8 ?@ (r - 0x50#64)
    ⋆ (7 ?@ (r - 0x48#64)
    ⋆ (1 ?@ (r - 0x41#64)
    ⋆ (8 ?@ (r - 0x40#64)
    ⋆ (8 ?@ (r - 0x38#64)
    ⋆ (c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ Kt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

abbrev FrA1 (x : Args) (t₀ : MachineData) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x1c8#64)
    ⋆ (8 ?@ (r - 0x1c0#64)
    ⋆ (8 ?@ (r - 0x1b8#64)
    ⋆ (8 ?@ (r - 0x1b0#64)
    ⋆ (8 ?@ (r - 0x1a8#64)
    ⋆ (8 ?@ (r - 0x1a0#64)
    ⋆ (8 ?@ (r - 0x198#64)
    ⋆ (8 ?@ (r - 0x190#64)
    ⋆ (8 ?@ (r - 0x188#64)
    ⋆ (8 ?@ (r - 0x180#64)
    ⋆ (8 ?@ (r - 0x178#64)
    ⋆ (8 ?@ (r - 0x170#64)
    ⋆ (8 ?@ (r - 0x168#64)
    ⋆ (8 ?@ (r - 0x160#64)
    ⋆ (8 ?@ (r - 0x158#64)
    ⋆ (8 ?@ (r - 0x150#64)
    ⋆ (8 ?@ (r - 0x148#64)
    ⋆ (8 ?@ (r - 0x140#64)
    ⋆ (c8 (r - 0x138#64) (arg3 t₀)
    ⋆ (c8 (r - 0x130#64) (arg4 t₀)
    ⋆ (8 ?@ (r - 0x128#64)
    ⋆ (8 ?@ (r - 0x120#64)
    ⋆ (8 ?@ (r - 0x118#64)
    ⋆ (8 ?@ (r - 0x110#64)
    ⋆ (8 ?@ (r - 0x108#64)
    ⋆ (4 ?@ (r - 0x100#64)
    ⋆ (4 ?@ (r - 0xfc#64)
    ⋆ (Int.toBytes 1 (dsN x : Int) =@ (r - 0xf8#64) ⋆ 7 ?@ (r - 0xf7#64)
    ⋆ (8 ?@ (r - 0xf0#64)
    ⋆ (8 ?@ (r - 0xe8#64)
    ⋆ (8 ?@ (r - 0xe0#64)
    ⋆ (8 ?@ (r - 0xd8#64)
    ⋆ (8 ?@ (r - 0xd0#64)
    ⋆ (8 ?@ (r - 0xc8#64)
    ⋆ (8 ?@ (r - 0xc0#64)
    ⋆ (8 ?@ (r - 0xb8#64)
    ⋆ (8 ?@ (r - 0xb0#64)
    ⋆ (4 ?@ (r - 0xa8#64)
    ⋆ (4 ?@ (r - 0xa4#64)
    ⋆ (8 ?@ (r - 0xa0#64)
    ⋆ (8 ?@ (r - 0x98#64)
    ⋆ (6 ?@ (r - 0x90#64)
    ⋆ (2 ?@ (r - 0x8a#64)
    ⋆ (8 ?@ (r - 0x88#64)
    ⋆ (8 ?@ (r - 0x80#64)
    ⋆ (8 ?@ (r - 0x78#64)
    ⋆ (8 ?@ (r - 0x70#64)
    ⋆ (8 ?@ (r - 0x68#64)
    ⋆ (8 ?@ (r - 0x60#64)
    ⋆ (8 ?@ (r - 0x58#64)
    ⋆ (8 ?@ (r - 0x50#64)
    ⋆ (7 ?@ (r - 0x48#64)
    ⋆ (1 ?@ (r - 0x41#64)
    ⋆ (8 ?@ (r - 0x40#64)
    ⋆ (8 ?@ (r - 0x38#64)
    ⋆ (c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ Kt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

abbrev FrD (x : Args) (t₀ : MachineData) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x1c8#64)
    ⋆ (8 ?@ (r - 0x1c0#64)
    ⋆ (8 ?@ (r - 0x1b8#64)
    ⋆ (8 ?@ (r - 0x1b0#64)
    ⋆ (8 ?@ (r - 0x1a8#64)
    ⋆ (8 ?@ (r - 0x1a0#64)
    ⋆ (8 ?@ (r - 0x198#64)
    ⋆ (8 ?@ (r - 0x190#64)
    ⋆ (8 ?@ (r - 0x188#64)
    ⋆ (8 ?@ (r - 0x180#64)
    ⋆ (8 ?@ (r - 0x178#64)
    ⋆ (8 ?@ (r - 0x170#64)
    ⋆ (8 ?@ (r - 0x168#64)
    ⋆ (8 ?@ (r - 0x160#64)
    ⋆ (8 ?@ (r - 0x158#64)
    ⋆ (8 ?@ (r - 0x150#64)
    ⋆ (8 ?@ (r - 0x148#64)
    ⋆ (8 ?@ (r - 0x140#64)
    ⋆ (c8 (r - 0x138#64) (arg3 t₀)
    ⋆ (c8 (r - 0x130#64) (arg4 t₀)
    ⋆ (8 ?@ (r - 0x128#64)
    ⋆ (8 ?@ (r - 0x120#64)
    ⋆ (8 ?@ (r - 0x118#64)
    ⋆ (8 ?@ (r - 0x110#64)
    ⋆ (8 ?@ (r - 0x108#64)
    ⋆ (4 ?@ (r - 0x100#64)
    ⋆ (4 ?@ (r - 0xfc#64)
    ⋆ (Int.toBytes 1 (dsN x : Int) =@ (r - 0xf8#64) ⋆ 7 ?@ (r - 0xf7#64)
    ⋆ (8 ?@ (r - 0xf0#64)
    ⋆ (8 ?@ (r - 0xe8#64)
    ⋆ (8 ?@ (r - 0xe0#64)
    ⋆ (8 ?@ (r - 0xd8#64)
    ⋆ (8 ?@ (r - 0xd0#64)
    ⋆ (8 ?@ (r - 0xc8#64)
    ⋆ (8 ?@ (r - 0xc0#64)
    ⋆ (8 ?@ (r - 0xb8#64)
    ⋆ (8 ?@ (r - 0xb0#64)
    ⋆ (4 ?@ (r - 0xa8#64)
    ⋆ (Int.toBytes 4 ((BitVec.setWidth 32 (arg2 t₀)).toInt) =@ (r - 0xa4#64)
    ⋆ (8 ?@ (r - 0xa0#64)
    ⋆ (c8 (r - 0x98#64) (arg0 t₀)
    ⋆ (6 ?@ (r - 0x90#64)
    ⋆ (2 ?@ (r - 0x8a#64)
    ⋆ (8 ?@ (r - 0x88#64)
    ⋆ (8 ?@ (r - 0x80#64)
    ⋆ (8 ?@ (r - 0x78#64)
    ⋆ (8 ?@ (r - 0x70#64)
    ⋆ (8 ?@ (r - 0x68#64)
    ⋆ (8 ?@ (r - 0x60#64)
    ⋆ (8 ?@ (r - 0x58#64)
    ⋆ (8 ?@ (r - 0x50#64)
    ⋆ (7 ?@ (r - 0x48#64)
    ⋆ (1 ?@ (r - 0x41#64)
    ⋆ (c8 (r - 0x40#64) (arg1 t₀)
    ⋆ (8 ?@ (r - 0x38#64)
    ⋆ (c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ Kt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

abbrev FrE (x : Args) (t₀ : MachineData) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x1c8#64)
    ⋆ (8 ?@ (r - 0x1c0#64)
    ⋆ (8 ?@ (r - 0x1b8#64)
    ⋆ (8 ?@ (r - 0x1b0#64)
    ⋆ (8 ?@ (r - 0x1a8#64)
    ⋆ (8 ?@ (r - 0x1a0#64)
    ⋆ (8 ?@ (r - 0x198#64)
    ⋆ (8 ?@ (r - 0x190#64)
    ⋆ (8 ?@ (r - 0x188#64)
    ⋆ (8 ?@ (r - 0x180#64)
    ⋆ (8 ?@ (r - 0x178#64)
    ⋆ (8 ?@ (r - 0x170#64)
    ⋆ (8 ?@ (r - 0x168#64)
    ⋆ (8 ?@ (r - 0x160#64)
    ⋆ (8 ?@ (r - 0x158#64)
    ⋆ (8 ?@ (r - 0x150#64)
    ⋆ (8 ?@ (r - 0x148#64)
    ⋆ (8 ?@ (r - 0x140#64)
    ⋆ (c8 (r - 0x138#64) (arg3 t₀)
    ⋆ (c8 (r - 0x130#64) (arg4 t₀)
    ⋆ (8 ?@ (r - 0x128#64)
    ⋆ (8 ?@ (r - 0x120#64)
    ⋆ (8 ?@ (r - 0x118#64)
    ⋆ (8 ?@ (r - 0x110#64)
    ⋆ (8 ?@ (r - 0x108#64)
    ⋆ (4 ?@ (r - 0x100#64)
    ⋆ (4 ?@ (r - 0xfc#64)
    ⋆ (Int.toBytes 1 (dsN x : Int) =@ (r - 0xf8#64) ⋆ 7 ?@ (r - 0xf7#64)
    ⋆ (8 ?@ (r - 0xf0#64)
    ⋆ (8 ?@ (r - 0xe8#64)
    ⋆ (8 ?@ (r - 0xe0#64)
    ⋆ (8 ?@ (r - 0xd8#64)
    ⋆ (c8 (r - 0xd0#64) (BitVec.ofNat 64 1)
    ⋆ (8 ?@ (r - 0xc8#64)
    ⋆ (8 ?@ (r - 0xc0#64)
    ⋆ (8 ?@ (r - 0xb8#64)
    ⋆ (8 ?@ (r - 0xb0#64)
    ⋆ (4 ?@ (r - 0xa8#64)
    ⋆ (Int.toBytes 4 ((BitVec.setWidth 32 (arg2 t₀)).toInt) =@ (r - 0xa4#64)
    ⋆ (8 ?@ (r - 0xa0#64)
    ⋆ (c8 (r - 0x98#64) (arg0 t₀)
    ⋆ (6 ?@ (r - 0x90#64)
    ⋆ (2 ?@ (r - 0x8a#64)
    ⋆ (8 ?@ (r - 0x88#64)
    ⋆ (8 ?@ (r - 0x80#64)
    ⋆ (8 ?@ (r - 0x78#64)
    ⋆ (8 ?@ (r - 0x70#64)
    ⋆ (8 ?@ (r - 0x68#64)
    ⋆ (8 ?@ (r - 0x60#64)
    ⋆ (8 ?@ (r - 0x58#64)
    ⋆ (8 ?@ (r - 0x50#64)
    ⋆ (7 ?@ (r - 0x48#64)
    ⋆ (1 ?@ (r - 0x41#64)
    ⋆ (c8 (r - 0x40#64) (arg1 t₀)
    ⋆ (8 ?@ (r - 0x38#64)
    ⋆ (c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ Kt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

abbrev FrS1 (x : Args) (t₀ : MachineData) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x1c8#64)
    ⋆ (8 ?@ (r - 0x1c0#64)
    ⋆ (8 ?@ (r - 0x1b8#64)
    ⋆ (8 ?@ (r - 0x1b0#64)
    ⋆ (8 ?@ (r - 0x1a8#64)
    ⋆ (8 ?@ (r - 0x1a0#64)
    ⋆ (8 ?@ (r - 0x198#64)
    ⋆ (8 ?@ (r - 0x190#64)
    ⋆ (8 ?@ (r - 0x188#64)
    ⋆ (8 ?@ (r - 0x180#64)
    ⋆ (8 ?@ (r - 0x178#64)
    ⋆ (8 ?@ (r - 0x170#64)
    ⋆ (8 ?@ (r - 0x168#64)
    ⋆ (8 ?@ (r - 0x160#64)
    ⋆ (8 ?@ (r - 0x158#64)
    ⋆ (8 ?@ (r - 0x150#64)
    ⋆ (8 ?@ (r - 0x148#64)
    ⋆ (8 ?@ (r - 0x140#64)
    ⋆ (c8 (r - 0x138#64) (arg3 t₀)
    ⋆ (c8 (r - 0x130#64) (arg4 t₀)
    ⋆ (8 ?@ (r - 0x128#64)
    ⋆ (8 ?@ (r - 0x120#64)
    ⋆ (8 ?@ (r - 0x118#64)
    ⋆ (8 ?@ (r - 0x110#64)
    ⋆ (8 ?@ (r - 0x108#64)
    ⋆ (4 ?@ (r - 0x100#64)
    ⋆ (4 ?@ (r - 0xfc#64)
    ⋆ (Int.toBytes 1 (dsN x : Int) =@ (r - 0xf8#64) ⋆ 7 ?@ (r - 0xf7#64)
    ⋆ (8 ?@ (r - 0xf0#64)
    ⋆ (8 ?@ (r - 0xe8#64)
    ⋆ (8 ?@ (r - 0xe0#64)
    ⋆ (8 ?@ (r - 0xd8#64)
    ⋆ (8 ?@ (r - 0xd0#64)
    ⋆ (8 ?@ (r - 0xc8#64)
    ⋆ (8 ?@ (r - 0xc0#64)
    ⋆ (c8 (r - 0xb8#64) (sbrA t₀)
    ⋆ (8 ?@ (r - 0xb0#64)
    ⋆ (4 ?@ (r - 0xa8#64)
    ⋆ (Int.toBytes 4 ((BitVec.setWidth 32 (arg2 t₀)).toInt) =@ (r - 0xa4#64)
    ⋆ (8 ?@ (r - 0xa0#64)
    ⋆ (c8 (r - 0x98#64) (arg0 t₀)
    ⋆ (6 ?@ (r - 0x90#64)
    ⋆ (2 ?@ (r - 0x8a#64)
    ⋆ (8 ?@ (r - 0x88#64)
    ⋆ (8 ?@ (r - 0x80#64)
    ⋆ (8 ?@ (r - 0x78#64)
    ⋆ (8 ?@ (r - 0x70#64)
    ⋆ (8 ?@ (r - 0x68#64)
    ⋆ (8 ?@ (r - 0x60#64)
    ⋆ (8 ?@ (r - 0x58#64)
    ⋆ (8 ?@ (r - 0x50#64)
    ⋆ (7 ?@ (r - 0x48#64)
    ⋆ (1 ?@ (r - 0x41#64)
    ⋆ (c8 (r - 0x40#64) (arg1 t₀)
    ⋆ (8 ?@ (r - 0x38#64)
    ⋆ (c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ Kt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

abbrev FrS2 (x : Args) (t₀ : MachineData) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x1c8#64)
    ⋆ (8 ?@ (r - 0x1c0#64)
    ⋆ (8 ?@ (r - 0x1b8#64)
    ⋆ (8 ?@ (r - 0x1b0#64)
    ⋆ (8 ?@ (r - 0x1a8#64)
    ⋆ (8 ?@ (r - 0x1a0#64)
    ⋆ (8 ?@ (r - 0x198#64)
    ⋆ (8 ?@ (r - 0x190#64)
    ⋆ (8 ?@ (r - 0x188#64)
    ⋆ (8 ?@ (r - 0x180#64)
    ⋆ (8 ?@ (r - 0x178#64)
    ⋆ (8 ?@ (r - 0x170#64)
    ⋆ (8 ?@ (r - 0x168#64)
    ⋆ (8 ?@ (r - 0x160#64)
    ⋆ (c8 (r - 0x158#64) (BitVec.ofNat 64 (dsN x))
    ⋆ (c8 (r - 0x150#64) (sbrA t₀ + 0x5d340#64)
    ⋆ (c8 (r - 0x148#64) (sbrA t₀ + 0x5d540#64)
    ⋆ (c8 (r - 0x140#64) (sbrA t₀ + 0x80#64)
    ⋆ (c8 (r - 0x138#64) (arg3 t₀)
    ⋆ (c8 (r - 0x130#64) (arg4 t₀)
    ⋆ (c8 (r - 0x128#64) (sbrA t₀ + 0x601e0#64)
    ⋆ (8 ?@ (r - 0x120#64)
    ⋆ (8 ?@ (r - 0x118#64)
    ⋆ (8 ?@ (r - 0x110#64)
    ⋆ (8 ?@ (r - 0x108#64)
    ⋆ (4 ?@ (r - 0x100#64)
    ⋆ (4 ?@ (r - 0xfc#64)
    ⋆ (1 ?@ (r - 0xf8#64) ⋆ 7 ?@ (r - 0xf7#64)
    ⋆ (8 ?@ (r - 0xf0#64)
    ⋆ (8 ?@ (r - 0xe8#64)
    ⋆ (8 ?@ (r - 0xe0#64)
    ⋆ (8 ?@ (r - 0xd8#64)
    ⋆ (8 ?@ (r - 0xd0#64)
    ⋆ (c8 (r - 0xc8#64) (sbrA t₀ + 0x4c340#64)
    ⋆ (8 ?@ (r - 0xc0#64)
    ⋆ (c8 (r - 0xb8#64) (sbrA t₀)
    ⋆ (8 ?@ (r - 0xb0#64)
    ⋆ (4 ?@ (r - 0xa8#64)
    ⋆ (Int.toBytes 4 ((BitVec.setWidth 32 (arg2 t₀)).toInt) =@ (r - 0xa4#64)
    ⋆ (8 ?@ (r - 0xa0#64)
    ⋆ (c8 (r - 0x98#64) (arg0 t₀)
    ⋆ (6 ?@ (r - 0x90#64)
    ⋆ (2 ?@ (r - 0x8a#64)
    ⋆ (8 ?@ (r - 0x88#64)
    ⋆ (8 ?@ (r - 0x80#64)
    ⋆ (8 ?@ (r - 0x78#64)
    ⋆ (8 ?@ (r - 0x70#64)
    ⋆ (8 ?@ (r - 0x68#64)
    ⋆ (8 ?@ (r - 0x60#64)
    ⋆ (8 ?@ (r - 0x58#64)
    ⋆ (8 ?@ (r - 0x50#64)
    ⋆ (7 ?@ (r - 0x48#64)
    ⋆ (1 ?@ (r - 0x41#64)
    ⋆ (c8 (r - 0x40#64) (arg1 t₀)
    ⋆ (8 ?@ (r - 0x38#64)
    ⋆ (c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ Kt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

abbrev FrS3 (x : Args) (t₀ : MachineData) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x1c8#64)
    ⋆ (c8 (r - 0x1c0#64) (sbrA t₀ + 0x4c284#64)
    ⋆ (c8 (r - 0x1b8#64) (sbrA t₀ + 0x4c252#64)
    ⋆ (c8 (r - 0x1b0#64) (sbrA t₀ + 0x5e340#64)
    ⋆ (8 ?@ (r - 0x1a8#64)
    ⋆ (8 ?@ (r - 0x1a0#64)
    ⋆ (8 ?@ (r - 0x198#64)
    ⋆ (c8 (r - 0x190#64) (sbrA t₀ + 0x5dd40#64)
    ⋆ (8 ?@ (r - 0x188#64)
    ⋆ (8 ?@ (r - 0x180#64)
    ⋆ (8 ?@ (r - 0x178#64)
    ⋆ (8 ?@ (r - 0x170#64)
    ⋆ (8 ?@ (r - 0x168#64)
    ⋆ (8 ?@ (r - 0x160#64)
    ⋆ (c8 (r - 0x158#64) (BitVec.ofNat 64 (dsN x))
    ⋆ (c8 (r - 0x150#64) (sbrA t₀ + 0x5d340#64)
    ⋆ (c8 (r - 0x148#64) (sbrA t₀ + 0x5d540#64)
    ⋆ (c8 (r - 0x140#64) (sbrA t₀ + 0x80#64)
    ⋆ (c8 (r - 0x138#64) (arg3 t₀)
    ⋆ (c8 (r - 0x130#64) (arg4 t₀)
    ⋆ (c8 (r - 0x128#64) (sbrA t₀ + 0x601e0#64)
    ⋆ (8 ?@ (r - 0x120#64)
    ⋆ (8 ?@ (r - 0x118#64)
    ⋆ (8 ?@ (r - 0x110#64)
    ⋆ (8 ?@ (r - 0x108#64)
    ⋆ (4 ?@ (r - 0x100#64)
    ⋆ (4 ?@ (r - 0xfc#64)
    ⋆ (1 ?@ (r - 0xf8#64) ⋆ 7 ?@ (r - 0xf7#64)
    ⋆ (8 ?@ (r - 0xf0#64)
    ⋆ (8 ?@ (r - 0xe8#64)
    ⋆ (8 ?@ (r - 0xe0#64)
    ⋆ (c8 (r - 0xd8#64) (sbrA t₀ + 0x5d740#64)
    ⋆ (8 ?@ (r - 0xd0#64)
    ⋆ (c8 (r - 0xc8#64) (sbrA t₀ + 0x4c340#64)
    ⋆ (c8 (r - 0xc0#64) (sbrA t₀ + 0x4eb40#64)
    ⋆ (c8 (r - 0xb8#64) (sbrA t₀)
    ⋆ (8 ?@ (r - 0xb0#64)
    ⋆ (4 ?@ (r - 0xa8#64)
    ⋆ (Int.toBytes 4 ((BitVec.setWidth 32 (arg2 t₀)).toInt) =@ (r - 0xa4#64)
    ⋆ (8 ?@ (r - 0xa0#64)
    ⋆ (c8 (r - 0x98#64) (arg0 t₀)
    ⋆ (6 ?@ (r - 0x90#64)
    ⋆ (2 ?@ (r - 0x8a#64)
    ⋆ (8 ?@ (r - 0x88#64)
    ⋆ (8 ?@ (r - 0x80#64)
    ⋆ (8 ?@ (r - 0x78#64)
    ⋆ (8 ?@ (r - 0x70#64)
    ⋆ (8 ?@ (r - 0x68#64)
    ⋆ (8 ?@ (r - 0x60#64)
    ⋆ (8 ?@ (r - 0x58#64)
    ⋆ (8 ?@ (r - 0x50#64)
    ⋆ (7 ?@ (r - 0x48#64)
    ⋆ (1 ?@ (r - 0x41#64)
    ⋆ (c8 (r - 0x40#64) (arg1 t₀)
    ⋆ (8 ?@ (r - 0x38#64)
    ⋆ (c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ Kt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

abbrev FrS4 (x : Args) (t₀ : MachineData) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x1c8#64)
    ⋆ (c8 (r - 0x1c0#64) (sbrA t₀ + 0x4c284#64)
    ⋆ (c8 (r - 0x1b8#64) (sbrA t₀ + 0x4c252#64)
    ⋆ (c8 (r - 0x1b0#64) (sbrA t₀ + 0x5e340#64)
    ⋆ (8 ?@ (r - 0x1a8#64)
    ⋆ (c8 (r - 0x1a0#64) (sbrA t₀ + 0x4c288#64)
    ⋆ (8 ?@ (r - 0x198#64)
    ⋆ (c8 (r - 0x190#64) (sbrA t₀ + 0x5dd40#64)
    ⋆ (c8 (r - 0x188#64) (sbrA t₀ + 0xb2#64)
    ⋆ (c8 (r - 0x180#64) (sbrA t₀ + 0x5e4c0#64)
    ⋆ (c8 (r - 0x178#64) (sbrA t₀ + 0x5f0c0#64)
    ⋆ (c8 (r - 0x170#64) (sbrA t₀ + 0x1c#64)
    ⋆ (8 ?@ (r - 0x168#64)
    ⋆ (8 ?@ (r - 0x160#64)
    ⋆ (c8 (r - 0x158#64) (BitVec.ofNat 64 (dsN x))
    ⋆ (c8 (r - 0x150#64) (sbrA t₀ + 0x5d340#64)
    ⋆ (c8 (r - 0x148#64) (sbrA t₀ + 0x5d540#64)
    ⋆ (c8 (r - 0x140#64) (sbrA t₀ + 0x80#64)
    ⋆ (c8 (r - 0x138#64) (arg3 t₀)
    ⋆ (c8 (r - 0x130#64) (arg4 t₀)
    ⋆ (c8 (r - 0x128#64) (sbrA t₀ + 0x601e0#64)
    ⋆ (8 ?@ (r - 0x120#64)
    ⋆ (8 ?@ (r - 0x118#64)
    ⋆ (c8 (r - 0x110#64) (sbrA t₀ + 0x5eac0#64)
    ⋆ (c8 (r - 0x108#64) (sbrA t₀ + 0x5f6c0#64)
    ⋆ (4 ?@ (r - 0x100#64)
    ⋆ (4 ?@ (r - 0xfc#64)
    ⋆ (1 ?@ (r - 0xf8#64) ⋆ 7 ?@ (r - 0xf7#64)
    ⋆ (8 ?@ (r - 0xf0#64)
    ⋆ (8 ?@ (r - 0xe8#64)
    ⋆ (8 ?@ (r - 0xe0#64)
    ⋆ (c8 (r - 0xd8#64) (sbrA t₀ + 0x5d740#64)
    ⋆ (8 ?@ (r - 0xd0#64)
    ⋆ (c8 (r - 0xc8#64) (sbrA t₀ + 0x4c340#64)
    ⋆ (c8 (r - 0xc0#64) (sbrA t₀ + 0x4eb40#64)
    ⋆ (c8 (r - 0xb8#64) (sbrA t₀)
    ⋆ (c8 (r - 0xb0#64) (sbrA t₀ + 0x53b40#64)
    ⋆ (4 ?@ (r - 0xa8#64)
    ⋆ (Int.toBytes 4 ((BitVec.setWidth 32 (arg2 t₀)).toInt) =@ (r - 0xa4#64)
    ⋆ (8 ?@ (r - 0xa0#64)
    ⋆ (c8 (r - 0x98#64) (arg0 t₀)
    ⋆ (6 ?@ (r - 0x90#64)
    ⋆ (2 ?@ (r - 0x8a#64)
    ⋆ (8 ?@ (r - 0x88#64)
    ⋆ (8 ?@ (r - 0x80#64)
    ⋆ (8 ?@ (r - 0x78#64)
    ⋆ (8 ?@ (r - 0x70#64)
    ⋆ (8 ?@ (r - 0x68#64)
    ⋆ (8 ?@ (r - 0x60#64)
    ⋆ (8 ?@ (r - 0x58#64)
    ⋆ (8 ?@ (r - 0x50#64)
    ⋆ (7 ?@ (r - 0x48#64)
    ⋆ (1 ?@ (r - 0x41#64)
    ⋆ (c8 (r - 0x40#64) (arg1 t₀)
    ⋆ (8 ?@ (r - 0x38#64)
    ⋆ (c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ Kt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

abbrev FrS0 (nch : Nat) (x : Args) (t₀ : MachineData) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x1c8#64)
    ⋆ (8 ?@ (r - 0x1c0#64)
    ⋆ (8 ?@ (r - 0x1b8#64)
    ⋆ (8 ?@ (r - 0x1b0#64)
    ⋆ (8 ?@ (r - 0x1a8#64)
    ⋆ (8 ?@ (r - 0x1a0#64)
    ⋆ (8 ?@ (r - 0x198#64)
    ⋆ (8 ?@ (r - 0x190#64)
    ⋆ (8 ?@ (r - 0x188#64)
    ⋆ (8 ?@ (r - 0x180#64)
    ⋆ (8 ?@ (r - 0x178#64)
    ⋆ (8 ?@ (r - 0x170#64)
    ⋆ (8 ?@ (r - 0x168#64)
    ⋆ (8 ?@ (r - 0x160#64)
    ⋆ (8 ?@ (r - 0x158#64)
    ⋆ (8 ?@ (r - 0x150#64)
    ⋆ (8 ?@ (r - 0x148#64)
    ⋆ (8 ?@ (r - 0x140#64)
    ⋆ (c8 (r - 0x138#64) (arg3 t₀)
    ⋆ (c8 (r - 0x130#64) (arg4 t₀)
    ⋆ (8 ?@ (r - 0x128#64)
    ⋆ (8 ?@ (r - 0x120#64)
    ⋆ (8 ?@ (r - 0x118#64)
    ⋆ (8 ?@ (r - 0x110#64)
    ⋆ (8 ?@ (r - 0x108#64)
    ⋆ (4 ?@ (r - 0x100#64)
    ⋆ (4 ?@ (r - 0xfc#64)
    ⋆ (Int.toBytes 1 (dsN x : Int) =@ (r - 0xf8#64) ⋆ 7 ?@ (r - 0xf7#64)
    ⋆ (8 ?@ (r - 0xf0#64)
    ⋆ (8 ?@ (r - 0xe8#64)
    ⋆ (8 ?@ (r - 0xe0#64)
    ⋆ (8 ?@ (r - 0xd8#64)
    ⋆ (c8 (r - 0xd0#64) (BitVec.ofNat 64 nch)
    ⋆ (8 ?@ (r - 0xc8#64)
    ⋆ (8 ?@ (r - 0xc0#64)
    ⋆ (8 ?@ (r - 0xb8#64)
    ⋆ (8 ?@ (r - 0xb0#64)
    ⋆ (4 ?@ (r - 0xa8#64)
    ⋆ (Int.toBytes 4 ((BitVec.setWidth 32 (arg2 t₀)).toInt) =@ (r - 0xa4#64)
    ⋆ (8 ?@ (r - 0xa0#64)
    ⋆ (c8 (r - 0x98#64) (arg0 t₀)
    ⋆ (6 ?@ (r - 0x90#64)
    ⋆ (2 ?@ (r - 0x8a#64)
    ⋆ (8 ?@ (r - 0x88#64)
    ⋆ (8 ?@ (r - 0x80#64)
    ⋆ (8 ?@ (r - 0x78#64)
    ⋆ (8 ?@ (r - 0x70#64)
    ⋆ (8 ?@ (r - 0x68#64)
    ⋆ (8 ?@ (r - 0x60#64)
    ⋆ (8 ?@ (r - 0x58#64)
    ⋆ (8 ?@ (r - 0x50#64)
    ⋆ (7 ?@ (r - 0x48#64)
    ⋆ (1 ?@ (r - 0x41#64)
    ⋆ (c8 (r - 0x40#64) (arg1 t₀)
    ⋆ (8 ?@ (r - 0x38#64)
    ⋆ (c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ Kt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

abbrev FrM (ch nch : Nat) (x : Args) (t₀ : MachineData) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x1c8#64)
    ⋆ (8 ?@ (r - 0x1c0#64)
    ⋆ (8 ?@ (r - 0x1b8#64)
    ⋆ (8 ?@ (r - 0x1b0#64)
    ⋆ (8 ?@ (r - 0x1a8#64)
    ⋆ (8 ?@ (r - 0x1a0#64)
    ⋆ (8 ?@ (r - 0x198#64)
    ⋆ (8 ?@ (r - 0x190#64)
    ⋆ (8 ?@ (r - 0x188#64)
    ⋆ (8 ?@ (r - 0x180#64)
    ⋆ (8 ?@ (r - 0x178#64)
    ⋆ (8 ?@ (r - 0x170#64)
    ⋆ (8 ?@ (r - 0x168#64)
    ⋆ (8 ?@ (r - 0x160#64)
    ⋆ (8 ?@ (r - 0x158#64)
    ⋆ (8 ?@ (r - 0x150#64)
    ⋆ (8 ?@ (r - 0x148#64)
    ⋆ (8 ?@ (r - 0x140#64)
    ⋆ (c8 (r - 0x138#64) (arg3 t₀)
    ⋆ (c8 (r - 0x130#64) (arg4 t₀)
    ⋆ (8 ?@ (r - 0x128#64)
    ⋆ (8 ?@ (r - 0x120#64)
    ⋆ (8 ?@ (r - 0x118#64)
    ⋆ (8 ?@ (r - 0x110#64)
    ⋆ (8 ?@ (r - 0x108#64)
    ⋆ (4 ?@ (r - 0x100#64)
    ⋆ (4 ?@ (r - 0xfc#64)
    ⋆ (Int.toBytes 1 (dsN x : Int) =@ (r - 0xf8#64) ⋆ 7 ?@ (r - 0xf7#64)
    ⋆ (8 ?@ (r - 0xf0#64)
    ⋆ (8 ?@ (r - 0xe8#64)
    ⋆ (8 ?@ (r - 0xe0#64)
    ⋆ (8 ?@ (r - 0xd8#64)
    ⋆ (c8 (r - 0xd0#64) (BitVec.ofNat 64 nch)
    ⋆ (8 ?@ (r - 0xc8#64)
    ⋆ (8 ?@ (r - 0xc0#64)
    ⋆ (8 ?@ (r - 0xb8#64)
    ⋆ (8 ?@ (r - 0xb0#64)
    ⋆ (4 ?@ (r - 0xa8#64)
    ⋆ (Int.toBytes 4 ((BitVec.setWidth 32 (arg2 t₀)).toInt) =@ (r - 0xa4#64)
    ⋆ (8 ?@ (r - 0xa0#64)
    ⋆ (c8 (r - 0x98#64) (arg0 t₀)
    ⋆ (6 ?@ (r - 0x90#64)
    ⋆ (2 ?@ (r - 0x8a#64)
    ⋆ (8 ?@ (r - 0x88#64)
    ⋆ (8 ?@ (r - 0x80#64)
    ⋆ (8 ?@ (r - 0x78#64)
    ⋆ (8 ?@ (r - 0x70#64)
    ⋆ (8 ?@ (r - 0x68#64)
    ⋆ (c8 (r - 0x60#64) (dA t₀ 0)
    ⋆ (c8 (r - 0x58#64) (dA t₀ ch + 0x15210#64)
    ⋆ (c8 (r - 0x50#64) (dA t₀ ch + 0x15450#64)
    ⋆ (7 ?@ (r - 0x48#64)
    ⋆ (1 ?@ (r - 0x41#64)
    ⋆ (c8 (r - 0x40#64) (arg1 t₀)
    ⋆ (8 ?@ (r - 0x38#64)
    ⋆ (c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ Kt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

abbrev FrDq (ch nch : Nat) (x : Args) (t₀ : MachineData) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x1c8#64)
    ⋆ (8 ?@ (r - 0x1c0#64)
    ⋆ (8 ?@ (r - 0x1b8#64)
    ⋆ (8 ?@ (r - 0x1b0#64)
    ⋆ (8 ?@ (r - 0x1a8#64)
    ⋆ (8 ?@ (r - 0x1a0#64)
    ⋆ (8 ?@ (r - 0x198#64)
    ⋆ (8 ?@ (r - 0x190#64)
    ⋆ (8 ?@ (r - 0x188#64)
    ⋆ (8 ?@ (r - 0x180#64)
    ⋆ (8 ?@ (r - 0x178#64)
    ⋆ (8 ?@ (r - 0x170#64)
    ⋆ (8 ?@ (r - 0x168#64)
    ⋆ (8 ?@ (r - 0x160#64)
    ⋆ (8 ?@ (r - 0x158#64)
    ⋆ (8 ?@ (r - 0x150#64)
    ⋆ (8 ?@ (r - 0x148#64)
    ⋆ (8 ?@ (r - 0x140#64)
    ⋆ (c8 (r - 0x138#64) (arg3 t₀)
    ⋆ (c8 (r - 0x130#64) (arg4 t₀)
    ⋆ (8 ?@ (r - 0x128#64)
    ⋆ (8 ?@ (r - 0x120#64)
    ⋆ (8 ?@ (r - 0x118#64)
    ⋆ (8 ?@ (r - 0x110#64)
    ⋆ (8 ?@ (r - 0x108#64)
    ⋆ (4 ?@ (r - 0x100#64)
    ⋆ (4 ?@ (r - 0xfc#64)
    ⋆ (Int.toBytes 1 (dsN x : Int) =@ (r - 0xf8#64) ⋆ 7 ?@ (r - 0xf7#64)
    ⋆ (8 ?@ (r - 0xf0#64)
    ⋆ (8 ?@ (r - 0xe8#64)
    ⋆ (8 ?@ (r - 0xe0#64)
    ⋆ (8 ?@ (r - 0xd8#64)
    ⋆ (c8 (r - 0xd0#64) (BitVec.ofNat 64 nch)
    ⋆ (8 ?@ (r - 0xc8#64)
    ⋆ (8 ?@ (r - 0xc0#64)
    ⋆ (8 ?@ (r - 0xb8#64)
    ⋆ (8 ?@ (r - 0xb0#64)
    ⋆ (4 ?@ (r - 0xa8#64)
    ⋆ (Int.toBytes 4 ((BitVec.setWidth 32 (arg2 t₀)).toInt) =@ (r - 0xa4#64)
    ⋆ (8 ?@ (r - 0xa0#64)
    ⋆ (c8 (r - 0x98#64) (arg0 t₀)
    ⋆ (6 ?@ (r - 0x90#64)
    ⋆ (2 ?@ (r - 0x8a#64)
    ⋆ (8 ?@ (r - 0x88#64)
    ⋆ (8 ?@ (r - 0x80#64)
    ⋆ (8 ?@ (r - 0x78#64)
    ⋆ (8 ?@ (r - 0x70#64)
    ⋆ (8 ?@ (r - 0x68#64)
    ⋆ (c8 (r - 0x60#64) (dA t₀ 0)
    ⋆ (c8 (r - 0x58#64) (dA t₀ ch + 0x15210#64)
    ⋆ (c8 (r - 0x50#64) (dA t₀ ch + 0x15450#64)
    ⋆ (7 ?@ (r - 0x48#64)
    ⋆ (1 ?@ (r - 0x41#64)
    ⋆ (c8 (r - 0x40#64) (arg1 t₀)
    ⋆ (c8 (r - 0x38#64) (BitVec.ofNat 64 ch)
    ⋆ (c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ Kt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

abbrev FrL1 (ch nch : Nat) (x : Args) (t₀ : MachineData) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x1c8#64)
    ⋆ (8 ?@ (r - 0x1c0#64)
    ⋆ (8 ?@ (r - 0x1b8#64)
    ⋆ (8 ?@ (r - 0x1b0#64)
    ⋆ (8 ?@ (r - 0x1a8#64)
    ⋆ (8 ?@ (r - 0x1a0#64)
    ⋆ (8 ?@ (r - 0x198#64)
    ⋆ (8 ?@ (r - 0x190#64)
    ⋆ (8 ?@ (r - 0x188#64)
    ⋆ (8 ?@ (r - 0x180#64)
    ⋆ (8 ?@ (r - 0x178#64)
    ⋆ (8 ?@ (r - 0x170#64)
    ⋆ (8 ?@ (r - 0x168#64)
    ⋆ (8 ?@ (r - 0x160#64)
    ⋆ (8 ?@ (r - 0x158#64)
    ⋆ (8 ?@ (r - 0x150#64)
    ⋆ (8 ?@ (r - 0x148#64)
    ⋆ (8 ?@ (r - 0x140#64)
    ⋆ (c8 (r - 0x138#64) (arg3 t₀)
    ⋆ (c8 (r - 0x130#64) (arg4 t₀)
    ⋆ (8 ?@ (r - 0x128#64)
    ⋆ (8 ?@ (r - 0x120#64)
    ⋆ (8 ?@ (r - 0x118#64)
    ⋆ (8 ?@ (r - 0x110#64)
    ⋆ (8 ?@ (r - 0x108#64)
    ⋆ (4 ?@ (r - 0x100#64)
    ⋆ (4 ?@ (r - 0xfc#64)
    ⋆ (Int.toBytes 1 (dsN x : Int) =@ (r - 0xf8#64) ⋆ 7 ?@ (r - 0xf7#64)
    ⋆ (8 ?@ (r - 0xf0#64)
    ⋆ (8 ?@ (r - 0xe8#64)
    ⋆ (8 ?@ (r - 0xe0#64)
    ⋆ (8 ?@ (r - 0xd8#64)
    ⋆ (c8 (r - 0xd0#64) (BitVec.ofNat 64 nch)
    ⋆ (8 ?@ (r - 0xc8#64)
    ⋆ (8 ?@ (r - 0xc0#64)
    ⋆ (8 ?@ (r - 0xb8#64)
    ⋆ (8 ?@ (r - 0xb0#64)
    ⋆ (4 ?@ (r - 0xa8#64)
    ⋆ (Int.toBytes 4 ((BitVec.setWidth 32 (arg2 t₀)).toInt) =@ (r - 0xa4#64)
    ⋆ (8 ?@ (r - 0xa0#64)
    ⋆ (c8 (r - 0x98#64) (arg0 t₀)
    ⋆ (6 ?@ (r - 0x90#64)
    ⋆ (2 ?@ (r - 0x8a#64)
    ⋆ (8 ?@ (r - 0x88#64)
    ⋆ (8 ?@ (r - 0x80#64)
    ⋆ (8 ?@ (r - 0x78#64)
    ⋆ (8 ?@ (r - 0x70#64)
    ⋆ (8 ?@ (r - 0x68#64)
    ⋆ (c8 (r - 0x60#64) (dA t₀ 0)
    ⋆ (c8 (r - 0x58#64) (dA t₀ (ch + 1) + 0x15210#64)
    ⋆ (c8 (r - 0x50#64) (dA t₀ ch + 0x15450#64)
    ⋆ (7 ?@ (r - 0x48#64)
    ⋆ (1 ?@ (r - 0x41#64)
    ⋆ (c8 (r - 0x40#64) (arg1 t₀)
    ⋆ (c8 (r - 0x38#64) (BitVec.ofNat 64 ch)
    ⋆ (c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ Kt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

abbrev FrL2 (ch nch : Nat) (x : Args) (t₀ : MachineData) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x1c8#64)
    ⋆ (8 ?@ (r - 0x1c0#64)
    ⋆ (8 ?@ (r - 0x1b8#64)
    ⋆ (8 ?@ (r - 0x1b0#64)
    ⋆ (8 ?@ (r - 0x1a8#64)
    ⋆ (8 ?@ (r - 0x1a0#64)
    ⋆ (8 ?@ (r - 0x198#64)
    ⋆ (8 ?@ (r - 0x190#64)
    ⋆ (8 ?@ (r - 0x188#64)
    ⋆ (8 ?@ (r - 0x180#64)
    ⋆ (8 ?@ (r - 0x178#64)
    ⋆ (8 ?@ (r - 0x170#64)
    ⋆ (8 ?@ (r - 0x168#64)
    ⋆ (8 ?@ (r - 0x160#64)
    ⋆ (8 ?@ (r - 0x158#64)
    ⋆ (8 ?@ (r - 0x150#64)
    ⋆ (8 ?@ (r - 0x148#64)
    ⋆ (8 ?@ (r - 0x140#64)
    ⋆ (c8 (r - 0x138#64) (arg3 t₀)
    ⋆ (c8 (r - 0x130#64) (arg4 t₀)
    ⋆ (8 ?@ (r - 0x128#64)
    ⋆ (8 ?@ (r - 0x120#64)
    ⋆ (8 ?@ (r - 0x118#64)
    ⋆ (8 ?@ (r - 0x110#64)
    ⋆ (8 ?@ (r - 0x108#64)
    ⋆ (4 ?@ (r - 0x100#64)
    ⋆ (4 ?@ (r - 0xfc#64)
    ⋆ (Int.toBytes 1 (dsN x : Int) =@ (r - 0xf8#64) ⋆ 7 ?@ (r - 0xf7#64)
    ⋆ (8 ?@ (r - 0xf0#64)
    ⋆ (8 ?@ (r - 0xe8#64)
    ⋆ (8 ?@ (r - 0xe0#64)
    ⋆ (8 ?@ (r - 0xd8#64)
    ⋆ (c8 (r - 0xd0#64) (BitVec.ofNat 64 nch)
    ⋆ (8 ?@ (r - 0xc8#64)
    ⋆ (8 ?@ (r - 0xc0#64)
    ⋆ (8 ?@ (r - 0xb8#64)
    ⋆ (8 ?@ (r - 0xb0#64)
    ⋆ (4 ?@ (r - 0xa8#64)
    ⋆ (Int.toBytes 4 ((BitVec.setWidth 32 (arg2 t₀)).toInt) =@ (r - 0xa4#64)
    ⋆ (8 ?@ (r - 0xa0#64)
    ⋆ (c8 (r - 0x98#64) (arg0 t₀)
    ⋆ (6 ?@ (r - 0x90#64)
    ⋆ (2 ?@ (r - 0x8a#64)
    ⋆ (8 ?@ (r - 0x88#64)
    ⋆ (8 ?@ (r - 0x80#64)
    ⋆ (8 ?@ (r - 0x78#64)
    ⋆ (8 ?@ (r - 0x70#64)
    ⋆ (8 ?@ (r - 0x68#64)
    ⋆ (c8 (r - 0x60#64) (dA t₀ 0)
    ⋆ (c8 (r - 0x58#64) (dA t₀ (ch + 1) + 0x15210#64)
    ⋆ (c8 (r - 0x50#64) (dA t₀ (ch + 1) + 0x15450#64)
    ⋆ (7 ?@ (r - 0x48#64)
    ⋆ (1 ?@ (r - 0x41#64)
    ⋆ (c8 (r - 0x40#64) (arg1 t₀)
    ⋆ (c8 (r - 0x38#64) (BitVec.ofNat 64 ch)
    ⋆ (c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ Kt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

abbrev FrAn1 (x : Args) (t₀ : MachineData) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x1c8#64)
    ⋆ (c8 (r - 0x1c0#64) (sbrA t₀ + 0x4c284#64)
    ⋆ (c8 (r - 0x1b8#64) (sbrA t₀ + 0x4c252#64)
    ⋆ (c8 (r - 0x1b0#64) (sbrA t₀ + 0x5e340#64)
    ⋆ (8 ?@ (r - 0x1a8#64)
    ⋆ (c8 (r - 0x1a0#64) (sbrA t₀ + 0x4c288#64)
    ⋆ (c8 (r - 0x198#64) (sbrA t₀ + 0x4eb50#64)
    ⋆ (c8 (r - 0x190#64) (sbrA t₀ + 0x5dd40#64)
    ⋆ (c8 (r - 0x188#64) (sbrA t₀ + 0xb2#64)
    ⋆ (c8 (r - 0x180#64) (sbrA t₀ + 0x5e4c0#64)
    ⋆ (c8 (r - 0x178#64) (sbrA t₀ + 0x5f0c0#64)
    ⋆ (c8 (r - 0x170#64) (sbrA t₀ + 0x1c#64)
    ⋆ (c8 (r - 0x168#64) (sbrA t₀ + 0x150e0#64)
    ⋆ (c8 (r - 0x160#64) (sbrA t₀ + 0x5f6c4#64)
    ⋆ (c8 (r - 0x158#64) (BitVec.ofNat 64 (dsN x))
    ⋆ (c8 (r - 0x150#64) (sbrA t₀ + 0x5d340#64)
    ⋆ (c8 (r - 0x148#64) (sbrA t₀ + 0x5d540#64)
    ⋆ (c8 (r - 0x140#64) (sbrA t₀ + 0x80#64)
    ⋆ (c8 (r - 0x138#64) (arg3 t₀)
    ⋆ (c8 (r - 0x130#64) (arg4 t₀)
    ⋆ (c8 (r - 0x128#64) (sbrA t₀ + 0x601e0#64)
    ⋆ (c8 (r - 0x120#64) (sbrA t₀ + 0x5fcc0#64)
    ⋆ (8 ?@ (r - 0x118#64)
    ⋆ (c8 (r - 0x110#64) (sbrA t₀ + 0x5eac0#64)
    ⋆ (c8 (r - 0x108#64) (sbrA t₀ + 0x5f6c0#64)
    ⋆ (4 ?@ (r - 0x100#64)
    ⋆ (4 ?@ (r - 0xfc#64)
    ⋆ (c8 (r - 0xf8#64) (lab "sbr_qmf_window_ds")
    ⋆ (8 ?@ (r - 0xf0#64)
    ⋆ (8 ?@ (r - 0xe8#64)
    ⋆ (8 ?@ (r - 0xe0#64)
    ⋆ (c8 (r - 0xd8#64) (sbrA t₀ + 0x5d740#64)
    ⋆ (c8 (r - 0xd0#64) (sbrA t₀ + 0x5fdc0#64)
    ⋆ (c8 (r - 0xc8#64) (sbrA t₀ + 0x4c340#64)
    ⋆ (c8 (r - 0xc0#64) (sbrA t₀ + 0x4eb40#64)
    ⋆ (c8 (r - 0xb8#64) (sbrA t₀)
    ⋆ (c8 (r - 0xb0#64) (sbrA t₀ + 0x53b40#64)
    ⋆ (4 ?@ (r - 0xa8#64)
    ⋆ (Int.toBytes 4 ((BitVec.setWidth 32 (arg2 t₀)).toInt) =@ (r - 0xa4#64)
    ⋆ (8 ?@ (r - 0xa0#64)
    ⋆ (c8 (r - 0x98#64) (arg0 t₀)
    ⋆ (6 ?@ (r - 0x90#64)
    ⋆ (2 ?@ (r - 0x8a#64)
    ⋆ (8 ?@ (r - 0x88#64)
    ⋆ (8 ?@ (r - 0x80#64)
    ⋆ (c8 (r - 0x78#64) (sbrA t₀ + 0x4ec90#64)
    ⋆ (8 ?@ (r - 0x70#64)
    ⋆ (8 ?@ (r - 0x68#64)
    ⋆ (8 ?@ (r - 0x60#64)
    ⋆ (8 ?@ (r - 0x58#64)
    ⋆ (8 ?@ (r - 0x50#64)
    ⋆ (7 ?@ (r - 0x48#64)
    ⋆ (1 ?@ (r - 0x41#64)
    ⋆ (c8 (r - 0x40#64) (arg1 t₀)
    ⋆ (c8 (r - 0x38#64) (x.fdsp)
    ⋆ (c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ Kt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

abbrev FrA2 (x : Args) (t₀ : MachineData) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x1c8#64)
    ⋆ (c8 (r - 0x1c0#64) (sbrA t₀ + 0x4c284#64)
    ⋆ (c8 (r - 0x1b8#64) (sbrA t₀ + 0x4c252#64)
    ⋆ (c8 (r - 0x1b0#64) (sbrA t₀ + 0x5e340#64)
    ⋆ (8 ?@ (r - 0x1a8#64)
    ⋆ (c8 (r - 0x1a0#64) (sbrA t₀ + 0x4c288#64)
    ⋆ (c8 (r - 0x198#64) (sbrA t₀ + 0x4eb50#64)
    ⋆ (c8 (r - 0x190#64) (sbrA t₀ + 0x5dd40#64)
    ⋆ (c8 (r - 0x188#64) (sbrA t₀ + 0xb2#64)
    ⋆ (c8 (r - 0x180#64) (sbrA t₀ + 0x5e4c0#64)
    ⋆ (c8 (r - 0x178#64) (sbrA t₀ + 0x5f0c0#64)
    ⋆ (c8 (r - 0x170#64) (sbrA t₀ + 0x1c#64)
    ⋆ (c8 (r - 0x168#64) (sbrA t₀ + 0x150e0#64)
    ⋆ (c8 (r - 0x160#64) (sbrA t₀ + 0x5f6c4#64)
    ⋆ (c8 (r - 0x158#64) (BitVec.ofNat 64 (dsN x))
    ⋆ (c8 (r - 0x150#64) (sbrA t₀ + 0x5d340#64)
    ⋆ (c8 (r - 0x148#64) (sbrA t₀ + 0x5d540#64)
    ⋆ (c8 (r - 0x140#64) (sbrA t₀ + 0x80#64)
    ⋆ (c8 (r - 0x138#64) (arg3 t₀)
    ⋆ (c8 (r - 0x130#64) (arg4 t₀)
    ⋆ (c8 (r - 0x128#64) (sbrA t₀ + 0x601e0#64)
    ⋆ (c8 (r - 0x120#64) (sbrA t₀ + 0x5fcc0#64)
    ⋆ (8 ?@ (r - 0x118#64)
    ⋆ (c8 (r - 0x110#64) (sbrA t₀ + 0x5eac0#64)
    ⋆ (c8 (r - 0x108#64) (sbrA t₀ + 0x5f6c0#64)
    ⋆ (4 ?@ (r - 0x100#64)
    ⋆ (4 ?@ (r - 0xfc#64)
    ⋆ (c8 (r - 0xf8#64) (lab "sbr_qmf_window_ds")
    ⋆ (8 ?@ (r - 0xf0#64)
    ⋆ (8 ?@ (r - 0xe8#64)
    ⋆ (8 ?@ (r - 0xe0#64)
    ⋆ (c8 (r - 0xd8#64) (sbrA t₀ + 0x5d740#64)
    ⋆ (c8 (r - 0xd0#64) (sbrA t₀ + 0x5fdc0#64)
    ⋆ (c8 (r - 0xc8#64) (sbrA t₀ + 0x4c340#64)
    ⋆ (c8 (r - 0xc0#64) (sbrA t₀ + 0x4eb40#64)
    ⋆ (c8 (r - 0xb8#64) (sbrA t₀)
    ⋆ (c8 (r - 0xb0#64) (sbrA t₀ + 0x53b40#64)
    ⋆ (4 ?@ (r - 0xa8#64)
    ⋆ (Int.toBytes 4 ((BitVec.setWidth 32 (arg2 t₀)).toInt) =@ (r - 0xa4#64)
    ⋆ (8 ?@ (r - 0xa0#64)
    ⋆ (c8 (r - 0x98#64) (arg0 t₀)
    ⋆ (6 ?@ (r - 0x90#64)
    ⋆ (2 ?@ (r - 0x8a#64)
    ⋆ (8 ?@ (r - 0x88#64)
    ⋆ (8 ?@ (r - 0x80#64)
    ⋆ (c8 (r - 0x78#64) (sbrA t₀ + 0x4ec90#64)
    ⋆ (8 ?@ (r - 0x70#64)
    ⋆ (8 ?@ (r - 0x68#64)
    ⋆ (c8 (r - 0x60#64) (x.anaCtx)
    ⋆ (8 ?@ (r - 0x58#64)
    ⋆ (8 ?@ (r - 0x50#64)
    ⋆ (7 ?@ (r - 0x48#64)
    ⋆ (1 ?@ (r - 0x41#64)
    ⋆ (c8 (r - 0x40#64) (arg1 t₀)
    ⋆ (c8 (r - 0x38#64) (x.fdsp)
    ⋆ (c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ Kt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

abbrev FrA3 (x : Args) (t₀ : MachineData) (e : Env) (ch : Nat) (c0 : BitVec 32) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x1c8#64)
    ⋆ (c8 (r - 0x1c0#64) (sbrA t₀ + 0x4c284#64)
    ⋆ (c8 (r - 0x1b8#64) (sbrA t₀ + 0x4c252#64)
    ⋆ (c8 (r - 0x1b0#64) (sbrA t₀ + 0x5e340#64)
    ⋆ (8 ?@ (r - 0x1a8#64)
    ⋆ (c8 (r - 0x1a0#64) (sbrA t₀ + 0x4c288#64)
    ⋆ (c8 (r - 0x198#64) (sbrA t₀ + 0x4eb50#64)
    ⋆ (c8 (r - 0x190#64) (sbrA t₀ + 0x5dd40#64)
    ⋆ (c8 (r - 0x188#64) (sbrA t₀ + 0xb2#64)
    ⋆ (c8 (r - 0x180#64) (sbrA t₀ + 0x5e4c0#64)
    ⋆ (c8 (r - 0x178#64) (sbrA t₀ + 0x5f0c0#64)
    ⋆ (c8 (r - 0x170#64) (sbrA t₀ + 0x1c#64)
    ⋆ (c8 (r - 0x168#64) (sbrA t₀ + 0x150e0#64)
    ⋆ (c8 (r - 0x160#64) (sbrA t₀ + 0x5f6c4#64)
    ⋆ (c8 (r - 0x158#64) (BitVec.ofNat 64 (dsN x))
    ⋆ (c8 (r - 0x150#64) (sbrA t₀ + 0x5d340#64)
    ⋆ (c8 (r - 0x148#64) (sbrA t₀ + 0x5d540#64)
    ⋆ (c8 (r - 0x140#64) (sbrA t₀ + 0x80#64)
    ⋆ (c8 (r - 0x138#64) (arg3 t₀)
    ⋆ (c8 (r - 0x130#64) (arg4 t₀)
    ⋆ (c8 (r - 0x128#64) (sbrA t₀ + 0x601e0#64)
    ⋆ (c8 (r - 0x120#64) (sbrA t₀ + 0x5fcc0#64)
    ⋆ (8 ?@ (r - 0x118#64)
    ⋆ (c8 (r - 0x110#64) (sbrA t₀ + 0x5eac0#64)
    ⋆ (c8 (r - 0x108#64) (sbrA t₀ + 0x5f6c0#64)
    ⋆ (Int.toBytes 4 (c0.toInt) =@ (r - 0x100#64)
    ⋆ (4 ?@ (r - 0xfc#64)
    ⋆ (c8 (r - 0xf8#64) (lab "sbr_qmf_window_ds")
    ⋆ (8 ?@ (r - 0xf0#64)
    ⋆ (8 ?@ (r - 0xe8#64)
    ⋆ (8 ?@ (r - 0xe0#64)
    ⋆ (c8 (r - 0xd8#64) (sbrA t₀ + 0x5d740#64)
    ⋆ (c8 (r - 0xd0#64) (sbrA t₀ + 0x5fdc0#64)
    ⋆ (c8 (r - 0xc8#64) (sbrA t₀ + 0x4c340#64)
    ⋆ (c8 (r - 0xc0#64) (sbrA t₀ + 0x4eb40#64)
    ⋆ (c8 (r - 0xb8#64) (sbrA t₀)
    ⋆ (c8 (r - 0xb0#64) (sbrA t₀ + 0x53b40#64)
    ⋆ (4 ?@ (r - 0xa8#64)
    ⋆ (Int.toBytes 4 ((BitVec.setWidth 32 (arg2 t₀)).toInt) =@ (r - 0xa4#64)
    ⋆ (8 ?@ (r - 0xa0#64)
    ⋆ (c8 (r - 0x98#64) (arg0 t₀)
    ⋆ (6 ?@ (r - 0x90#64)
    ⋆ (2 ?@ (r - 0x8a#64)
    ⋆ (8 ?@ (r - 0x88#64)
    ⋆ (8 ?@ (r - 0x80#64)
    ⋆ (c8 (r - 0x78#64) (sbrA t₀ + 0x4ec90#64)
    ⋆ (8 ?@ (r - 0x70#64)
    ⋆ (8 ?@ (r - 0x68#64)
    ⋆ (c8 (r - 0x60#64) (x.anaCtx)
    ⋆ (c8 (r - 0x58#64) (e.fs.mdctAna.toBitVec)
    ⋆ (8 ?@ (r - 0x50#64)
    ⋆ (7 ?@ (r - 0x48#64)
    ⋆ (1 ?@ (r - 0x41#64)
    ⋆ (c8 (r - 0x40#64) (arg1 t₀)
    ⋆ (c8 (r - 0x38#64) (x.fdsp)
    ⋆ (c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ Kt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

abbrev FrA4 (x : Args) (t₀ : MachineData) (e : Env) (ch : Nat) (c0 : BitVec 32) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x1c8#64)
    ⋆ (c8 (r - 0x1c0#64) (sbrA t₀ + 0x4c284#64)
    ⋆ (c8 (r - 0x1b8#64) (sbrA t₀ + 0x4c252#64)
    ⋆ (c8 (r - 0x1b0#64) (sbrA t₀ + 0x5e340#64)
    ⋆ (c8 (r - 0x1a8#64) (BitVec.ofNat 64 ch)
    ⋆ (c8 (r - 0x1a0#64) (sbrA t₀ + 0x4c288#64)
    ⋆ (c8 (r - 0x198#64) (sbrA t₀ + 0x4eb50#64)
    ⋆ (c8 (r - 0x190#64) (sbrA t₀ + 0x5dd40#64)
    ⋆ (c8 (r - 0x188#64) (sbrA t₀ + 0xb2#64)
    ⋆ (c8 (r - 0x180#64) (sbrA t₀ + 0x5e4c0#64)
    ⋆ (c8 (r - 0x178#64) (sbrA t₀ + 0x5f0c0#64)
    ⋆ (c8 (r - 0x170#64) (sbrA t₀ + 0x1c#64)
    ⋆ (c8 (r - 0x168#64) (sbrA t₀ + 0x150e0#64)
    ⋆ (c8 (r - 0x160#64) (sbrA t₀ + 0x5f6c4#64)
    ⋆ (c8 (r - 0x158#64) (BitVec.ofNat 64 (dsN x))
    ⋆ (c8 (r - 0x150#64) (sbrA t₀ + 0x5d340#64)
    ⋆ (c8 (r - 0x148#64) (sbrA t₀ + 0x5d540#64)
    ⋆ (c8 (r - 0x140#64) (sbrA t₀ + 0x80#64)
    ⋆ (c8 (r - 0x138#64) (arg3 t₀)
    ⋆ (c8 (r - 0x130#64) (arg4 t₀)
    ⋆ (c8 (r - 0x128#64) (sbrA t₀ + 0x601e0#64)
    ⋆ (c8 (r - 0x120#64) (sbrA t₀ + 0x5fcc0#64)
    ⋆ (8 ?@ (r - 0x118#64)
    ⋆ (c8 (r - 0x110#64) (sbrA t₀ + 0x5eac0#64)
    ⋆ (c8 (r - 0x108#64) (sbrA t₀ + 0x5f6c0#64)
    ⋆ (Int.toBytes 4 (c0.toInt) =@ (r - 0x100#64)
    ⋆ (4 ?@ (r - 0xfc#64)
    ⋆ (c8 (r - 0xf8#64) (lab "sbr_qmf_window_ds")
    ⋆ (8 ?@ (r - 0xf0#64)
    ⋆ (8 ?@ (r - 0xe8#64)
    ⋆ (8 ?@ (r - 0xe0#64)
    ⋆ (c8 (r - 0xd8#64) (sbrA t₀ + 0x5d740#64)
    ⋆ (c8 (r - 0xd0#64) (sbrA t₀ + 0x5fdc0#64)
    ⋆ (c8 (r - 0xc8#64) (sbrA t₀ + 0x4c340#64)
    ⋆ (c8 (r - 0xc0#64) (sbrA t₀ + 0x4eb40#64)
    ⋆ (c8 (r - 0xb8#64) (sbrA t₀)
    ⋆ (c8 (r - 0xb0#64) (sbrA t₀ + 0x53b40#64)
    ⋆ (4 ?@ (r - 0xa8#64)
    ⋆ (Int.toBytes 4 ((BitVec.setWidth 32 (arg2 t₀)).toInt) =@ (r - 0xa4#64)
    ⋆ (8 ?@ (r - 0xa0#64)
    ⋆ (c8 (r - 0x98#64) (arg0 t₀)
    ⋆ (6 ?@ (r - 0x90#64)
    ⋆ (2 ?@ (r - 0x8a#64)
    ⋆ (8 ?@ (r - 0x88#64)
    ⋆ (8 ?@ (r - 0x80#64)
    ⋆ (c8 (r - 0x78#64) (sbrA t₀ + 0x4ec90#64)
    ⋆ (c8 (r - 0x70#64) (if ch = 0 then arg3 t₀ else arg4 t₀)
    ⋆ (8 ?@ (r - 0x68#64)
    ⋆ (c8 (r - 0x60#64) (x.anaCtx)
    ⋆ (c8 (r - 0x58#64) (e.fs.mdctAna.toBitVec)
    ⋆ (8 ?@ (r - 0x50#64)
    ⋆ (7 ?@ (r - 0x48#64)
    ⋆ (1 ?@ (r - 0x41#64)
    ⋆ (c8 (r - 0x40#64) (arg1 t₀)
    ⋆ (c8 (r - 0x38#64) (x.fdsp)
    ⋆ (c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ Kt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

abbrev FrA5 (x : Args) (t₀ : MachineData) (e : Env) (ch : Nat) (c0 : BitVec 32) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x1c8#64)
    ⋆ (c8 (r - 0x1c0#64) (sbrA t₀ + 0x4c284#64)
    ⋆ (c8 (r - 0x1b8#64) (sbrA t₀ + 0x4c252#64)
    ⋆ (c8 (r - 0x1b0#64) (sbrA t₀ + 0x5e340#64)
    ⋆ (c8 (r - 0x1a8#64) (BitVec.ofNat 64 ch)
    ⋆ (c8 (r - 0x1a0#64) (sbrA t₀ + 0x4c288#64)
    ⋆ (c8 (r - 0x198#64) (sbrA t₀ + 0x4eb50#64)
    ⋆ (c8 (r - 0x190#64) (sbrA t₀ + 0x5dd40#64)
    ⋆ (c8 (r - 0x188#64) (sbrA t₀ + 0xb2#64)
    ⋆ (c8 (r - 0x180#64) (sbrA t₀ + 0x5e4c0#64)
    ⋆ (c8 (r - 0x178#64) (sbrA t₀ + 0x5f0c0#64)
    ⋆ (c8 (r - 0x170#64) (sbrA t₀ + 0x1c#64)
    ⋆ (c8 (r - 0x168#64) (sbrA t₀ + 0x150e0#64)
    ⋆ (c8 (r - 0x160#64) (sbrA t₀ + 0x5f6c4#64)
    ⋆ (c8 (r - 0x158#64) (BitVec.ofNat 64 (dsN x))
    ⋆ (c8 (r - 0x150#64) (sbrA t₀ + 0x5d340#64)
    ⋆ (c8 (r - 0x148#64) (sbrA t₀ + 0x5d540#64)
    ⋆ (c8 (r - 0x140#64) (sbrA t₀ + 0x80#64)
    ⋆ (c8 (r - 0x138#64) (arg3 t₀)
    ⋆ (c8 (r - 0x130#64) (arg4 t₀)
    ⋆ (c8 (r - 0x128#64) (sbrA t₀ + 0x601e0#64)
    ⋆ (c8 (r - 0x120#64) (sbrA t₀ + 0x5fcc0#64)
    ⋆ (8 ?@ (r - 0x118#64)
    ⋆ (c8 (r - 0x110#64) (sbrA t₀ + 0x5eac0#64)
    ⋆ (c8 (r - 0x108#64) (sbrA t₀ + 0x5f6c0#64)
    ⋆ (Int.toBytes 4 (c0.toInt) =@ (r - 0x100#64)
    ⋆ (4 ?@ (r - 0xfc#64)
    ⋆ (c8 (r - 0xf8#64) (lab "sbr_qmf_window_ds")
    ⋆ (8 ?@ (r - 0xf0#64)
    ⋆ (8 ?@ (r - 0xe8#64)
    ⋆ (8 ?@ (r - 0xe0#64)
    ⋆ (c8 (r - 0xd8#64) (sbrA t₀ + 0x5d740#64)
    ⋆ (c8 (r - 0xd0#64) (sbrA t₀ + 0x5fdc0#64)
    ⋆ (c8 (r - 0xc8#64) (sbrA t₀ + 0x4c340#64)
    ⋆ (c8 (r - 0xc0#64) (sbrA t₀ + 0x4eb40#64)
    ⋆ (c8 (r - 0xb8#64) (sbrA t₀)
    ⋆ (c8 (r - 0xb0#64) (sbrA t₀ + 0x53b40#64)
    ⋆ (4 ?@ (r - 0xa8#64)
    ⋆ (Int.toBytes 4 ((BitVec.setWidth 32 (arg2 t₀)).toInt) =@ (r - 0xa4#64)
    ⋆ (8 ?@ (r - 0xa0#64)
    ⋆ (c8 (r - 0x98#64) (arg0 t₀)
    ⋆ (6 ?@ (r - 0x90#64)
    ⋆ (2 ?@ (r - 0x8a#64)
    ⋆ (8 ?@ (r - 0x88#64)
    ⋆ (c8 (r - 0x80#64) (dA t₀ ch + 0x3920#64)
    ⋆ (c8 (r - 0x78#64) (sbrA t₀ + 0x4ec90#64)
    ⋆ (c8 (r - 0x70#64) (if ch = 0 then arg3 t₀ else arg4 t₀)
    ⋆ (8 ?@ (r - 0x68#64)
    ⋆ (c8 (r - 0x60#64) (x.anaCtx)
    ⋆ (c8 (r - 0x58#64) (e.fs.mdctAna.toBitVec)
    ⋆ (c8 (r - 0x50#64) (dA t₀ ch)
    ⋆ (7 ?@ (r - 0x48#64)
    ⋆ (1 ?@ (r - 0x41#64)
    ⋆ (c8 (r - 0x40#64) (arg1 t₀)
    ⋆ (c8 (r - 0x38#64) (x.fdsp)
    ⋆ (c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ Kt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

abbrev FrA6 (x : Args) (t₀ : MachineData) (e : Env) (ch : Nat) (c0 : BitVec 32) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x1c8#64)
    ⋆ (c8 (r - 0x1c0#64) (sbrA t₀ + 0x4c284#64)
    ⋆ (c8 (r - 0x1b8#64) (sbrA t₀ + 0x4c252#64)
    ⋆ (c8 (r - 0x1b0#64) (sbrA t₀ + 0x5e340#64)
    ⋆ (c8 (r - 0x1a8#64) (BitVec.ofNat 64 ch)
    ⋆ (c8 (r - 0x1a0#64) (sbrA t₀ + 0x4c288#64)
    ⋆ (c8 (r - 0x198#64) (sbrA t₀ + 0x4eb50#64)
    ⋆ (c8 (r - 0x190#64) (sbrA t₀ + 0x5dd40#64)
    ⋆ (c8 (r - 0x188#64) (sbrA t₀ + 0xb2#64)
    ⋆ (c8 (r - 0x180#64) (sbrA t₀ + 0x5e4c0#64)
    ⋆ (c8 (r - 0x178#64) (sbrA t₀ + 0x5f0c0#64)
    ⋆ (c8 (r - 0x170#64) (sbrA t₀ + 0x1c#64)
    ⋆ (c8 (r - 0x168#64) (sbrA t₀ + 0x150e0#64)
    ⋆ (c8 (r - 0x160#64) (sbrA t₀ + 0x5f6c4#64)
    ⋆ (c8 (r - 0x158#64) (BitVec.ofNat 64 (dsN x))
    ⋆ (c8 (r - 0x150#64) (sbrA t₀ + 0x5d340#64)
    ⋆ (c8 (r - 0x148#64) (sbrA t₀ + 0x5d540#64)
    ⋆ (c8 (r - 0x140#64) (sbrA t₀ + 0x80#64)
    ⋆ (c8 (r - 0x138#64) (arg3 t₀)
    ⋆ (c8 (r - 0x130#64) (arg4 t₀)
    ⋆ (c8 (r - 0x128#64) (sbrA t₀ + 0x601e0#64)
    ⋆ (c8 (r - 0x120#64) (sbrA t₀ + 0x5fcc0#64)
    ⋆ (8 ?@ (r - 0x118#64)
    ⋆ (c8 (r - 0x110#64) (sbrA t₀ + 0x5eac0#64)
    ⋆ (c8 (r - 0x108#64) (sbrA t₀ + 0x5f6c0#64)
    ⋆ (Int.toBytes 4 (c0.toInt) =@ (r - 0x100#64)
    ⋆ (4 ?@ (r - 0xfc#64)
    ⋆ (c8 (r - 0xf8#64) (lab "sbr_qmf_window_ds")
    ⋆ (8 ?@ (r - 0xf0#64)
    ⋆ (8 ?@ (r - 0xe8#64)
    ⋆ (8 ?@ (r - 0xe0#64)
    ⋆ (c8 (r - 0xd8#64) (sbrA t₀ + 0x5d740#64)
    ⋆ (c8 (r - 0xd0#64) (sbrA t₀ + 0x5fdc0#64)
    ⋆ (c8 (r - 0xc8#64) (sbrA t₀ + 0x4c340#64)
    ⋆ (c8 (r - 0xc0#64) (sbrA t₀ + 0x4eb40#64)
    ⋆ (c8 (r - 0xb8#64) (sbrA t₀)
    ⋆ (c8 (r - 0xb0#64) (sbrA t₀ + 0x53b40#64)
    ⋆ (4 ?@ (r - 0xa8#64)
    ⋆ (Int.toBytes 4 ((BitVec.setWidth 32 (arg2 t₀)).toInt) =@ (r - 0xa4#64)
    ⋆ (c8 (r - 0xa0#64) (BitVec.ofNat 64 (0x15ac0 * ch))
    ⋆ (c8 (r - 0x98#64) (arg0 t₀)
    ⋆ (6 ?@ (r - 0x90#64)
    ⋆ (2 ?@ (r - 0x8a#64)
    ⋆ (8 ?@ (r - 0x88#64)
    ⋆ (c8 (r - 0x80#64) (dA t₀ ch + 0x3920#64)
    ⋆ (c8 (r - 0x78#64) (sbrA t₀ + 0x4ec90#64)
    ⋆ (c8 (r - 0x70#64) (if ch = 0 then arg3 t₀ else arg4 t₀)
    ⋆ (8 ?@ (r - 0x68#64)
    ⋆ (c8 (r - 0x60#64) (x.anaCtx)
    ⋆ (c8 (r - 0x58#64) (e.fs.mdctAna.toBitVec)
    ⋆ (c8 (r - 0x50#64) (dA t₀ ch)
    ⋆ (7 ?@ (r - 0x48#64)
    ⋆ (1 ?@ (r - 0x41#64)
    ⋆ (c8 (r - 0x40#64) (arg1 t₀)
    ⋆ (c8 (r - 0x38#64) (x.fdsp)
    ⋆ (c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ Kt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

abbrev FrH (x : Args) (t₀ : MachineData) (e : Env) (ch : Nat) (c0 : BitVec 32) (ne : Nat) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x1c8#64)
    ⋆ (c8 (r - 0x1c0#64) (sbrA t₀ + 0x4c284#64)
    ⋆ (c8 (r - 0x1b8#64) (sbrA t₀ + 0x4c252#64)
    ⋆ (c8 (r - 0x1b0#64) (sbrA t₀ + 0x5e340#64)
    ⋆ (c8 (r - 0x1a8#64) (BitVec.ofNat 64 ch)
    ⋆ (c8 (r - 0x1a0#64) (sbrA t₀ + 0x4c288#64)
    ⋆ (c8 (r - 0x198#64) (sbrA t₀ + 0x4eb50#64)
    ⋆ (c8 (r - 0x190#64) (sbrA t₀ + 0x5dd40#64)
    ⋆ (c8 (r - 0x188#64) (sbrA t₀ + 0xb2#64)
    ⋆ (c8 (r - 0x180#64) (sbrA t₀ + 0x5e4c0#64)
    ⋆ (c8 (r - 0x178#64) (sbrA t₀ + 0x5f0c0#64)
    ⋆ (c8 (r - 0x170#64) (sbrA t₀ + 0x1c#64)
    ⋆ (c8 (r - 0x168#64) (sbrA t₀ + 0x150e0#64)
    ⋆ (c8 (r - 0x160#64) (sbrA t₀ + 0x5f6c4#64)
    ⋆ (c8 (r - 0x158#64) (BitVec.ofNat 64 (dsN x))
    ⋆ (c8 (r - 0x150#64) (sbrA t₀ + 0x5d340#64)
    ⋆ (c8 (r - 0x148#64) (sbrA t₀ + 0x5d540#64)
    ⋆ (c8 (r - 0x140#64) (sbrA t₀ + 0x80#64)
    ⋆ (c8 (r - 0x138#64) (arg3 t₀)
    ⋆ (c8 (r - 0x130#64) (arg4 t₀)
    ⋆ (c8 (r - 0x128#64) (sbrA t₀ + 0x601e0#64)
    ⋆ (c8 (r - 0x120#64) (sbrA t₀ + 0x5fcc0#64)
    ⋆ (8 ?@ (r - 0x118#64)
    ⋆ (c8 (r - 0x110#64) (sbrA t₀ + 0x5eac0#64)
    ⋆ (c8 (r - 0x108#64) (sbrA t₀ + 0x5f6c0#64)
    ⋆ (Int.toBytes 4 (c0.toInt) =@ (r - 0x100#64)
    ⋆ (4 ?@ (r - 0xfc#64)
    ⋆ (c8 (r - 0xf8#64) (lab "sbr_qmf_window_ds")
    ⋆ (8 ?@ (r - 0xf0#64)
    ⋆ (8 ?@ (r - 0xe8#64)
    ⋆ (8 ?@ (r - 0xe0#64)
    ⋆ (c8 (r - 0xd8#64) (sbrA t₀ + 0x5d740#64)
    ⋆ (c8 (r - 0xd0#64) (sbrA t₀ + 0x5fdc0#64)
    ⋆ (c8 (r - 0xc8#64) (sbrA t₀ + 0x4c340#64)
    ⋆ (c8 (r - 0xc0#64) (sbrA t₀ + 0x4eb40#64)
    ⋆ (c8 (r - 0xb8#64) (sbrA t₀)
    ⋆ (c8 (r - 0xb0#64) (sbrA t₀ + 0x53b40#64)
    ⋆ (4 ?@ (r - 0xa8#64)
    ⋆ (Int.toBytes 4 ((BitVec.setWidth 32 (arg2 t₀)).toInt) =@ (r - 0xa4#64)
    ⋆ (c8 (r - 0xa0#64) (BitVec.ofNat 64 (0x15ac0 * ch))
    ⋆ (c8 (r - 0x98#64) (arg0 t₀)
    ⋆ (6 ?@ (r - 0x90#64)
    ⋆ (2 ?@ (r - 0x8a#64)
    ⋆ (8 ?@ (r - 0x88#64)
    ⋆ (c8 (r - 0x80#64) (dA t₀ ch + 0x3920#64)
    ⋆ (c8 (r - 0x78#64) (sbrA t₀ + 0x4ec90#64)
    ⋆ (c8 (r - 0x70#64) (if ch = 0 then arg3 t₀ else arg4 t₀)
    ⋆ (8 ?@ (r - 0x68#64)
    ⋆ (c8 (r - 0x60#64) (x.anaCtx)
    ⋆ (c8 (r - 0x58#64) (e.fs.mdctAna.toBitVec)
    ⋆ (c8 (r - 0x50#64) (dA t₀ ch)
    ⋆ (7 ?@ (r - 0x48#64)
    ⋆ (1 ?@ (r - 0x41#64)
    ⋆ (c8 (r - 0x40#64) (arg1 t₀)
    ⋆ (c8 (r - 0x38#64) (BitVec.ofNat 64 ne)
    ⋆ (c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ Kt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

abbrev FrMA1 (x : Args) (t₀ : MachineData) (ch : Nat) (c0 : BitVec 32) (y : Args) (j : Nat) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x1c8#64)
    ⋆ (c8 (r - 0x1c0#64) (sbrA t₀ + 0x4c284#64)
    ⋆ (c8 (r - 0x1b8#64) (sbrA t₀ + 0x4c252#64)
    ⋆ (c8 (r - 0x1b0#64) (sbrA t₀ + 0x5e340#64)
    ⋆ (c8 (r - 0x1a8#64) (BitVec.ofNat 64 ch)
    ⋆ (c8 (r - 0x1a0#64) (sbrA t₀ + 0x4c288#64)
    ⋆ (c8 (r - 0x198#64) (sbrA t₀ + 0x4eb50#64)
    ⋆ (c8 (r - 0x190#64) (sbrA t₀ + 0x5dd40#64)
    ⋆ (c8 (r - 0x188#64) (sbrA t₀ + 0xb2#64)
    ⋆ (c8 (r - 0x180#64) (sbrA t₀ + 0x5e4c0#64)
    ⋆ (c8 (r - 0x178#64) (sbrA t₀ + 0x5f0c0#64)
    ⋆ (c8 (r - 0x170#64) (sbrA t₀ + 0x1c#64)
    ⋆ (c8 (r - 0x168#64) (sbrA t₀ + 0x150e0#64)
    ⋆ (c8 (r - 0x160#64) (sbrA t₀ + 0x5f6c4#64)
    ⋆ (c8 (r - 0x158#64) (BitVec.ofNat 64 (dsN x))
    ⋆ (c8 (r - 0x150#64) (sbrA t₀ + 0x5d340#64)
    ⋆ (c8 (r - 0x148#64) (sbrA t₀ + 0x5d540#64)
    ⋆ (c8 (r - 0x140#64) (sbrA t₀ + 0x80#64)
    ⋆ (c8 (r - 0x138#64) (arg3 t₀)
    ⋆ (c8 (r - 0x130#64) (arg4 t₀)
    ⋆ (c8 (r - 0x128#64) (sbrA t₀ + 0x601e0#64)
    ⋆ (c8 (r - 0x120#64) (sbrA t₀ + 0x5fcc0#64)
    ⋆ (8 ?@ (r - 0x118#64)
    ⋆ (c8 (r - 0x110#64) (sbrA t₀ + 0x5eac0#64)
    ⋆ (c8 (r - 0x108#64) (sbrA t₀ + 0x5f6c0#64)
    ⋆ (Int.toBytes 4 (c0.toInt) =@ (r - 0x100#64)
    ⋆ (4 ?@ (r - 0xfc#64)
    ⋆ (c8 (r - 0xf8#64) (lab "sbr_qmf_window_ds")
    ⋆ (8 ?@ (r - 0xf0#64)
    ⋆ (c8 (r - 0xe8#64) (dA t₀ ch + 0x15390#64)
    ⋆ (c8 (r - 0xe0#64) (dA t₀ ch + 0x15a60#64)
    ⋆ (c8 (r - 0xd8#64) (sbrA t₀ + 0x5d740#64)
    ⋆ (c8 (r - 0xd0#64) (sbrA t₀ + 0x5fdc0#64)
    ⋆ (c8 (r - 0xc8#64) (sbrA t₀ + 0x4c340#64)
    ⋆ (c8 (r - 0xc0#64) (sbrA t₀ + 0x4eb40#64)
    ⋆ (c8 (r - 0xb8#64) (sbrA t₀)
    ⋆ (c8 (r - 0xb0#64) (sbrA t₀ + 0x53b40#64)
    ⋆ (4 ?@ (r - 0xa8#64)
    ⋆ (Int.toBytes 4 ((BitVec.setWidth 32 (arg2 t₀)).toInt) =@ (r - 0xa4#64)
    ⋆ (c8 (r - 0xa0#64) (BitVec.ofNat 64 (0x15ac0 * ch))
    ⋆ (c8 (r - 0x98#64) (arg0 t₀)
    ⋆ (6 ?@ (r - 0x90#64)
    ⋆ (2 ?@ (r - 0x8a#64)
    ⋆ (8 ?@ (r - 0x88#64)
    ⋆ (8 ?@ (r - 0x80#64)
    ⋆ (c8 (r - 0x78#64) (sbrA t₀ + 0x4ec90#64)
    ⋆ (8 ?@ (r - 0x70#64)
    ⋆ (8 ?@ (r - 0x68#64)
    ⋆ (8 ?@ (r - 0x60#64)
    ⋆ (8 ?@ (r - 0x58#64)
    ⋆ (c8 (r - 0x50#64) (dA t₀ ch)
    ⋆ (7 ?@ (r - 0x48#64)
    ⋆ (1 ?@ (r - 0x41#64)
    ⋆ (c8 (r - 0x40#64) (arg1 t₀)
    ⋆ (8 ?@ (r - 0x38#64)
    ⋆ (c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ Kt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

abbrev FrMA2 (x : Args) (t₀ : MachineData) (ch : Nat) (c0 : BitVec 32) (y : Args) (j : Nat) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x1c8#64)
    ⋆ (c8 (r - 0x1c0#64) (sbrA t₀ + 0x4c284#64)
    ⋆ (c8 (r - 0x1b8#64) (sbrA t₀ + 0x4c252#64)
    ⋆ (c8 (r - 0x1b0#64) (sbrA t₀ + 0x5e340#64)
    ⋆ (c8 (r - 0x1a8#64) (BitVec.ofNat 64 ch)
    ⋆ (c8 (r - 0x1a0#64) (sbrA t₀ + 0x4c288#64)
    ⋆ (c8 (r - 0x198#64) (sbrA t₀ + 0x4eb50#64)
    ⋆ (c8 (r - 0x190#64) (sbrA t₀ + 0x5dd40#64)
    ⋆ (c8 (r - 0x188#64) (sbrA t₀ + 0xb2#64)
    ⋆ (c8 (r - 0x180#64) (sbrA t₀ + 0x5e4c0#64)
    ⋆ (c8 (r - 0x178#64) (sbrA t₀ + 0x5f0c0#64)
    ⋆ (c8 (r - 0x170#64) (sbrA t₀ + 0x1c#64)
    ⋆ (c8 (r - 0x168#64) (sbrA t₀ + 0x150e0#64)
    ⋆ (c8 (r - 0x160#64) (sbrA t₀ + 0x5f6c4#64)
    ⋆ (c8 (r - 0x158#64) (BitVec.ofNat 64 (dsN x))
    ⋆ (c8 (r - 0x150#64) (sbrA t₀ + 0x5d340#64)
    ⋆ (c8 (r - 0x148#64) (sbrA t₀ + 0x5d540#64)
    ⋆ (c8 (r - 0x140#64) (sbrA t₀ + 0x80#64)
    ⋆ (c8 (r - 0x138#64) (arg3 t₀)
    ⋆ (c8 (r - 0x130#64) (arg4 t₀)
    ⋆ (c8 (r - 0x128#64) (sbrA t₀ + 0x601e0#64)
    ⋆ (c8 (r - 0x120#64) (sbrA t₀ + 0x5fcc0#64)
    ⋆ (8 ?@ (r - 0x118#64)
    ⋆ (c8 (r - 0x110#64) (sbrA t₀ + 0x5eac0#64)
    ⋆ (c8 (r - 0x108#64) (sbrA t₀ + 0x5f6c0#64)
    ⋆ (Int.toBytes 4 (c0.toInt) =@ (r - 0x100#64)
    ⋆ (4 ?@ (r - 0xfc#64)
    ⋆ (c8 (r - 0xf8#64) (lab "sbr_qmf_window_ds")
    ⋆ (8 ?@ (r - 0xf0#64)
    ⋆ (c8 (r - 0xe8#64) (dA t₀ ch + 0x15390#64)
    ⋆ (c8 (r - 0xe0#64) (dA t₀ ch + 0x15a60#64)
    ⋆ (c8 (r - 0xd8#64) (sbrA t₀ + 0x5d740#64)
    ⋆ (c8 (r - 0xd0#64) (sbrA t₀ + 0x5fdc0#64)
    ⋆ (c8 (r - 0xc8#64) (sbrA t₀ + 0x4c340#64)
    ⋆ (c8 (r - 0xc0#64) (sbrA t₀ + 0x4eb40#64)
    ⋆ (c8 (r - 0xb8#64) (sbrA t₀)
    ⋆ (c8 (r - 0xb0#64) (sbrA t₀ + 0x53b40#64)
    ⋆ (4 ?@ (r - 0xa8#64)
    ⋆ (Int.toBytes 4 ((BitVec.setWidth 32 (arg2 t₀)).toInt) =@ (r - 0xa4#64)
    ⋆ (c8 (r - 0xa0#64) (BitVec.ofNat 64 (0x15ac0 * ch))
    ⋆ (c8 (r - 0x98#64) (arg0 t₀)
    ⋆ (6 ?@ (r - 0x90#64)
    ⋆ (2 ?@ (r - 0x8a#64)
    ⋆ (8 ?@ (r - 0x88#64)
    ⋆ (8 ?@ (r - 0x80#64)
    ⋆ (c8 (r - 0x78#64) (sbrA t₀ + 0x4ec90#64)
    ⋆ (8 ?@ (r - 0x70#64)
    ⋆ (c8 (r - 0x68#64) (arg1 t₀ + BitVec.ofNat 64 (0xc0 * j))
    ⋆ (8 ?@ (r - 0x60#64)
    ⋆ (8 ?@ (r - 0x58#64)
    ⋆ (c8 (r - 0x50#64) (dA t₀ ch)
    ⋆ (7 ?@ (r - 0x48#64)
    ⋆ (1 ?@ (r - 0x41#64)
    ⋆ (c8 (r - 0x40#64) (arg1 t₀)
    ⋆ (8 ?@ (r - 0x38#64)
    ⋆ (c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ Kt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

abbrev FrMA3 (x : Args) (t₀ : MachineData) (ch : Nat) (c0 : BitVec 32) (y : Args) (j : Nat) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x1c8#64)
    ⋆ (c8 (r - 0x1c0#64) (sbrA t₀ + 0x4c284#64)
    ⋆ (c8 (r - 0x1b8#64) (sbrA t₀ + 0x4c252#64)
    ⋆ (c8 (r - 0x1b0#64) (sbrA t₀ + 0x5e340#64)
    ⋆ (c8 (r - 0x1a8#64) (BitVec.ofNat 64 ch)
    ⋆ (c8 (r - 0x1a0#64) (sbrA t₀ + 0x4c288#64)
    ⋆ (c8 (r - 0x198#64) (sbrA t₀ + 0x4eb50#64)
    ⋆ (c8 (r - 0x190#64) (sbrA t₀ + 0x5dd40#64)
    ⋆ (c8 (r - 0x188#64) (sbrA t₀ + 0xb2#64)
    ⋆ (c8 (r - 0x180#64) (sbrA t₀ + 0x5e4c0#64)
    ⋆ (c8 (r - 0x178#64) (sbrA t₀ + 0x5f0c0#64)
    ⋆ (c8 (r - 0x170#64) (sbrA t₀ + 0x1c#64)
    ⋆ (c8 (r - 0x168#64) (sbrA t₀ + 0x150e0#64)
    ⋆ (c8 (r - 0x160#64) (sbrA t₀ + 0x5f6c4#64)
    ⋆ (c8 (r - 0x158#64) (BitVec.ofNat 64 (dsN x))
    ⋆ (c8 (r - 0x150#64) (sbrA t₀ + 0x5d340#64)
    ⋆ (c8 (r - 0x148#64) (sbrA t₀ + 0x5d540#64)
    ⋆ (c8 (r - 0x140#64) (sbrA t₀ + 0x80#64)
    ⋆ (c8 (r - 0x138#64) (arg3 t₀)
    ⋆ (c8 (r - 0x130#64) (arg4 t₀)
    ⋆ (c8 (r - 0x128#64) (sbrA t₀ + 0x601e0#64)
    ⋆ (c8 (r - 0x120#64) (sbrA t₀ + 0x5fcc0#64)
    ⋆ (8 ?@ (r - 0x118#64)
    ⋆ (c8 (r - 0x110#64) (sbrA t₀ + 0x5eac0#64)
    ⋆ (c8 (r - 0x108#64) (sbrA t₀ + 0x5f6c0#64)
    ⋆ (Int.toBytes 4 (c0.toInt) =@ (r - 0x100#64)
    ⋆ (4 ?@ (r - 0xfc#64)
    ⋆ (c8 (r - 0xf8#64) (lab "sbr_qmf_window_ds")
    ⋆ (8 ?@ (r - 0xf0#64)
    ⋆ (c8 (r - 0xe8#64) (dA t₀ ch + 0x15390#64)
    ⋆ (c8 (r - 0xe0#64) (dA t₀ ch + 0x15a60#64)
    ⋆ (c8 (r - 0xd8#64) (sbrA t₀ + 0x5d740#64)
    ⋆ (c8 (r - 0xd0#64) (sbrA t₀ + 0x5fdc0#64)
    ⋆ (c8 (r - 0xc8#64) (sbrA t₀ + 0x4c340#64)
    ⋆ (c8 (r - 0xc0#64) (sbrA t₀ + 0x4eb40#64)
    ⋆ (c8 (r - 0xb8#64) (sbrA t₀)
    ⋆ (c8 (r - 0xb0#64) (sbrA t₀ + 0x53b40#64)
    ⋆ (4 ?@ (r - 0xa8#64)
    ⋆ (Int.toBytes 4 ((BitVec.setWidth 32 (arg2 t₀)).toInt) =@ (r - 0xa4#64)
    ⋆ (c8 (r - 0xa0#64) (BitVec.ofNat 64 (0x15ac0 * ch))
    ⋆ (c8 (r - 0x98#64) (arg0 t₀)
    ⋆ (6 ?@ (r - 0x90#64)
    ⋆ (2 ?@ (r - 0x8a#64)
    ⋆ (8 ?@ (r - 0x88#64)
    ⋆ (8 ?@ (r - 0x80#64)
    ⋆ (c8 (r - 0x78#64) (sbrA t₀ + 0x4ec90#64)
    ⋆ (8 ?@ (r - 0x70#64)
    ⋆ (c8 (r - 0x68#64) (arg1 t₀ + BitVec.ofNat 64 (0xc0 * j))
    ⋆ (c8 (r - 0x60#64) (sbrA t₀ + 0x5dd40#64 + BitVec.ofNat 64 (0xc0 * j))
    ⋆ (8 ?@ (r - 0x58#64)
    ⋆ (c8 (r - 0x50#64) (dA t₀ ch)
    ⋆ (7 ?@ (r - 0x48#64)
    ⋆ (1 ?@ (r - 0x41#64)
    ⋆ (c8 (r - 0x40#64) (arg1 t₀)
    ⋆ (8 ?@ (r - 0x38#64)
    ⋆ (c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ Kt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

abbrev FrMB (x : Args) (t₀ : MachineData) (ch : Nat) (c0 : BitVec 32) (y : Args) (j : Nat) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x1c8#64)
    ⋆ (c8 (r - 0x1c0#64) (sbrA t₀ + 0x4c284#64)
    ⋆ (c8 (r - 0x1b8#64) (sbrA t₀ + 0x4c252#64)
    ⋆ (c8 (r - 0x1b0#64) (sbrA t₀ + 0x5e340#64)
    ⋆ (c8 (r - 0x1a8#64) (BitVec.ofNat 64 ch)
    ⋆ (c8 (r - 0x1a0#64) (sbrA t₀ + 0x4c288#64)
    ⋆ (c8 (r - 0x198#64) (sbrA t₀ + 0x4eb50#64)
    ⋆ (c8 (r - 0x190#64) (sbrA t₀ + 0x5dd40#64)
    ⋆ (c8 (r - 0x188#64) (sbrA t₀ + 0xb2#64)
    ⋆ (c8 (r - 0x180#64) (sbrA t₀ + 0x5e4c0#64)
    ⋆ (c8 (r - 0x178#64) (sbrA t₀ + 0x5f0c0#64)
    ⋆ (c8 (r - 0x170#64) (sbrA t₀ + 0x1c#64)
    ⋆ (c8 (r - 0x168#64) (sbrA t₀ + 0x150e0#64)
    ⋆ (c8 (r - 0x160#64) (sbrA t₀ + 0x5f6c4#64)
    ⋆ (c8 (r - 0x158#64) (BitVec.ofNat 64 (dsN x))
    ⋆ (c8 (r - 0x150#64) (sbrA t₀ + 0x5d340#64)
    ⋆ (c8 (r - 0x148#64) (sbrA t₀ + 0x5d540#64)
    ⋆ (c8 (r - 0x140#64) (sbrA t₀ + 0x80#64)
    ⋆ (c8 (r - 0x138#64) (arg3 t₀)
    ⋆ (c8 (r - 0x130#64) (arg4 t₀)
    ⋆ (c8 (r - 0x128#64) (sbrA t₀ + 0x601e0#64)
    ⋆ (c8 (r - 0x120#64) (sbrA t₀ + 0x5fcc0#64)
    ⋆ (8 ?@ (r - 0x118#64)
    ⋆ (c8 (r - 0x110#64) (sbrA t₀ + 0x5eac0#64)
    ⋆ (c8 (r - 0x108#64) (sbrA t₀ + 0x5f6c0#64)
    ⋆ (Int.toBytes 4 (c0.toInt) =@ (r - 0x100#64)
    ⋆ (4 ?@ (r - 0xfc#64)
    ⋆ (c8 (r - 0xf8#64) (lab "sbr_qmf_window_ds")
    ⋆ (c8 (r - 0xf0#64) (dA t₀ ch + 0x32#64)
    ⋆ (c8 (r - 0xe8#64) (dA t₀ ch + 0x15390#64)
    ⋆ (c8 (r - 0xe0#64) (dA t₀ ch + 0x15a60#64)
    ⋆ (c8 (r - 0xd8#64) (sbrA t₀ + 0x5d740#64)
    ⋆ (c8 (r - 0xd0#64) (sbrA t₀ + 0x5fdc0#64)
    ⋆ (c8 (r - 0xc8#64) (sbrA t₀ + 0x4c340#64)
    ⋆ (c8 (r - 0xc0#64) (sbrA t₀ + 0x4eb40#64)
    ⋆ (c8 (r - 0xb8#64) (sbrA t₀)
    ⋆ (c8 (r - 0xb0#64) (sbrA t₀ + 0x53b40#64)
    ⋆ (4 ?@ (r - 0xa8#64)
    ⋆ (Int.toBytes 4 ((BitVec.setWidth 32 (arg2 t₀)).toInt) =@ (r - 0xa4#64)
    ⋆ (c8 (r - 0xa0#64) (BitVec.ofNat 64 (0x15ac0 * ch))
    ⋆ (c8 (r - 0x98#64) (arg0 t₀)
    ⋆ (6 ?@ (r - 0x90#64)
    ⋆ (2 ?@ (r - 0x8a#64)
    ⋆ (c8 (r - 0x88#64) (dA t₀ ch + 0x15030#64)
    ⋆ (8 ?@ (r - 0x80#64)
    ⋆ (c8 (r - 0x78#64) (sbrA t₀ + 0x4ec90#64)
    ⋆ (8 ?@ (r - 0x70#64)
    ⋆ (c8 (r - 0x68#64) (arg1 t₀ + BitVec.ofNat 64 (0xc0 * j))
    ⋆ (c8 (r - 0x60#64) (sbrA t₀ + 0x5dd40#64 + BitVec.ofNat 64 (0xc0 * j))
    ⋆ (8 ?@ (r - 0x58#64)
    ⋆ (c8 (r - 0x50#64) (dA t₀ ch)
    ⋆ (7 ?@ (r - 0x48#64)
    ⋆ (1 ?@ (r - 0x41#64)
    ⋆ (c8 (r - 0x40#64) (arg1 t₀)
    ⋆ (Int.toBytes 4 (BitVec.ofNat 32 y.kx1).toInt =@ (r - 0x38#64) ⋆ 4 ?@ (r - 0x34#64)
    ⋆ (c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ Kt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

abbrev FrME (x : Args) (t₀ : MachineData) (ch : Nat) (c0 : BitVec 32) (y : Args) (j : Nat) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x1c8#64)
    ⋆ (c8 (r - 0x1c0#64) (sbrA t₀ + 0x4c284#64)
    ⋆ (c8 (r - 0x1b8#64) (sbrA t₀ + 0x4c252#64)
    ⋆ (c8 (r - 0x1b0#64) (sbrA t₀ + 0x5e340#64)
    ⋆ (c8 (r - 0x1a8#64) (BitVec.ofNat 64 ch)
    ⋆ (c8 (r - 0x1a0#64) (sbrA t₀ + 0x4c288#64)
    ⋆ (c8 (r - 0x198#64) (sbrA t₀ + 0x4eb50#64)
    ⋆ (c8 (r - 0x190#64) (sbrA t₀ + 0x5dd40#64)
    ⋆ (c8 (r - 0x188#64) (sbrA t₀ + 0xb2#64)
    ⋆ (c8 (r - 0x180#64) (sbrA t₀ + 0x5e4c0#64)
    ⋆ (c8 (r - 0x178#64) (sbrA t₀ + 0x5f0c0#64)
    ⋆ (c8 (r - 0x170#64) (sbrA t₀ + 0x1c#64)
    ⋆ (c8 (r - 0x168#64) (sbrA t₀ + 0x150e0#64)
    ⋆ (c8 (r - 0x160#64) (sbrA t₀ + 0x5f6c4#64)
    ⋆ (c8 (r - 0x158#64) (BitVec.ofNat 64 (dsN x))
    ⋆ (c8 (r - 0x150#64) (sbrA t₀ + 0x5d340#64)
    ⋆ (c8 (r - 0x148#64) (sbrA t₀ + 0x5d540#64)
    ⋆ (c8 (r - 0x140#64) (sbrA t₀ + 0x80#64)
    ⋆ (c8 (r - 0x138#64) (arg3 t₀)
    ⋆ (c8 (r - 0x130#64) (arg4 t₀)
    ⋆ (c8 (r - 0x128#64) (sbrA t₀ + 0x601e0#64)
    ⋆ (c8 (r - 0x120#64) (sbrA t₀ + 0x5fcc0#64)
    ⋆ (8 ?@ (r - 0x118#64)
    ⋆ (c8 (r - 0x110#64) (sbrA t₀ + 0x5eac0#64)
    ⋆ (c8 (r - 0x108#64) (sbrA t₀ + 0x5f6c0#64)
    ⋆ (Int.toBytes 4 (c0.toInt) =@ (r - 0x100#64)
    ⋆ (4 ?@ (r - 0xfc#64)
    ⋆ (c8 (r - 0xf8#64) (lab "sbr_qmf_window_ds")
    ⋆ (c8 (r - 0xf0#64) (dA t₀ ch + 0x32#64)
    ⋆ (c8 (r - 0xe8#64) (dA t₀ ch + 0x15390#64)
    ⋆ (c8 (r - 0xe0#64) (dA t₀ ch + 0x15a60#64)
    ⋆ (c8 (r - 0xd8#64) (sbrA t₀ + 0x5d740#64)
    ⋆ (c8 (r - 0xd0#64) (sbrA t₀ + 0x5fdc0#64)
    ⋆ (c8 (r - 0xc8#64) (sbrA t₀ + 0x4c340#64)
    ⋆ (c8 (r - 0xc0#64) (sbrA t₀ + 0x4eb40#64)
    ⋆ (c8 (r - 0xb8#64) (sbrA t₀)
    ⋆ (c8 (r - 0xb0#64) (sbrA t₀ + 0x53b40#64)
    ⋆ (4 ?@ (r - 0xa8#64)
    ⋆ (Int.toBytes 4 ((BitVec.setWidth 32 (arg2 t₀)).toInt) =@ (r - 0xa4#64)
    ⋆ (c8 (r - 0xa0#64) (BitVec.ofNat 64 (0x15ac0 * ch))
    ⋆ (c8 (r - 0x98#64) (arg0 t₀)
    ⋆ (6 ?@ (r - 0x90#64)
    ⋆ (2 ?@ (r - 0x8a#64)
    ⋆ (c8 (r - 0x88#64) (dA t₀ ch + 0x15030#64)
    ⋆ (8 ?@ (r - 0x80#64)
    ⋆ (c8 (r - 0x78#64) (sbrA t₀ + 0x4ec90#64)
    ⋆ (8 ?@ (r - 0x70#64)
    ⋆ (c8 (r - 0x68#64) (arg1 t₀ + BitVec.ofNat 64 (0xc0 * j))
    ⋆ (c8 (r - 0x60#64) (sbrA t₀ + 0x5dd40#64 + BitVec.ofNat 64 (0xc0 * j))
    ⋆ (c8 (r - 0x58#64) (BitVec.ofNat 64 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.n0 else y.n1))
    ⋆ (c8 (r - 0x50#64) (dA t₀ ch)
    ⋆ (7 ?@ (r - 0x48#64)
    ⋆ (1 ?@ (r - 0x41#64)
    ⋆ (c8 (r - 0x40#64) (arg1 t₀)
    ⋆ (Int.toBytes 4 (BitVec.ofNat 32 y.kx1).toInt =@ (r - 0x38#64) ⋆ 4 ?@ (r - 0x34#64)
    ⋆ (c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ Kt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

abbrev FrM0 (x : Args) (t₀ : MachineData) (ch : Nat) (c0 : BitVec 32) (y : Args) (j : Nat) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x1c8#64)
    ⋆ (c8 (r - 0x1c0#64) (sbrA t₀ + 0x4c284#64)
    ⋆ (c8 (r - 0x1b8#64) (sbrA t₀ + 0x4c252#64)
    ⋆ (c8 (r - 0x1b0#64) (sbrA t₀ + 0x5e340#64)
    ⋆ (c8 (r - 0x1a8#64) (BitVec.ofNat 64 ch)
    ⋆ (c8 (r - 0x1a0#64) (sbrA t₀ + 0x4c288#64)
    ⋆ (c8 (r - 0x198#64) (sbrA t₀ + 0x4eb50#64)
    ⋆ (c8 (r - 0x190#64) (sbrA t₀ + 0x5dd40#64)
    ⋆ (c8 (r - 0x188#64) (sbrA t₀ + 0xb2#64)
    ⋆ (c8 (r - 0x180#64) (sbrA t₀ + 0x5e4c0#64)
    ⋆ (c8 (r - 0x178#64) (sbrA t₀ + 0x5f0c0#64)
    ⋆ (c8 (r - 0x170#64) (sbrA t₀ + 0x1c#64)
    ⋆ (c8 (r - 0x168#64) (sbrA t₀ + 0x150e0#64)
    ⋆ (c8 (r - 0x160#64) (sbrA t₀ + 0x5f6c4#64)
    ⋆ (c8 (r - 0x158#64) (BitVec.ofNat 64 (dsN x))
    ⋆ (c8 (r - 0x150#64) (sbrA t₀ + 0x5d340#64)
    ⋆ (c8 (r - 0x148#64) (sbrA t₀ + 0x5d540#64)
    ⋆ (c8 (r - 0x140#64) (sbrA t₀ + 0x80#64)
    ⋆ (c8 (r - 0x138#64) (arg3 t₀)
    ⋆ (c8 (r - 0x130#64) (arg4 t₀)
    ⋆ (c8 (r - 0x128#64) (sbrA t₀ + 0x601e0#64)
    ⋆ (c8 (r - 0x120#64) (sbrA t₀ + 0x5fcc0#64)
    ⋆ (8 ?@ (r - 0x118#64)
    ⋆ (c8 (r - 0x110#64) (sbrA t₀ + 0x5eac0#64)
    ⋆ (c8 (r - 0x108#64) (sbrA t₀ + 0x5f6c0#64)
    ⋆ (Int.toBytes 4 (c0.toInt) =@ (r - 0x100#64)
    ⋆ (4 ?@ (r - 0xfc#64)
    ⋆ (c8 (r - 0xf8#64) (lab "sbr_qmf_window_ds")
    ⋆ (c8 (r - 0xf0#64) (dA t₀ ch + 0x32#64)
    ⋆ (c8 (r - 0xe8#64) (dA t₀ ch + 0x15390#64)
    ⋆ (c8 (r - 0xe0#64) (dA t₀ ch + 0x15a60#64)
    ⋆ (c8 (r - 0xd8#64) (sbrA t₀ + 0x5d740#64)
    ⋆ (c8 (r - 0xd0#64) (sbrA t₀ + 0x5fdc0#64)
    ⋆ (c8 (r - 0xc8#64) (sbrA t₀ + 0x4c340#64)
    ⋆ (c8 (r - 0xc0#64) (sbrA t₀ + 0x4eb40#64)
    ⋆ (c8 (r - 0xb8#64) (sbrA t₀)
    ⋆ (c8 (r - 0xb0#64) (sbrA t₀ + 0x53b40#64)
    ⋆ (4 ?@ (r - 0xa8#64)
    ⋆ (Int.toBytes 4 ((BitVec.setWidth 32 (arg2 t₀)).toInt) =@ (r - 0xa4#64)
    ⋆ (c8 (r - 0xa0#64) (BitVec.ofNat 64 (0x15ac0 * ch))
    ⋆ (c8 (r - 0x98#64) (arg0 t₀)
    ⋆ (6 ?@ (r - 0x90#64)
    ⋆ (2 ?@ (r - 0x8a#64)
    ⋆ (c8 (r - 0x88#64) (dA t₀ ch + 0x15030#64)
    ⋆ (8 ?@ (r - 0x80#64)
    ⋆ (c8 (r - 0x78#64) (sbrA t₀ + 0x4ec90#64)
    ⋆ (8 ?@ (r - 0x70#64)
    ⋆ (c8 (r - 0x68#64) (arg1 t₀ + BitVec.ofNat 64 (0xc0 * j))
    ⋆ (c8 (r - 0x60#64) (sbrA t₀ + 0x5dd40#64 + BitVec.ofNat 64 (0xc0 * j))
    ⋆ (8 ?@ (r - 0x58#64)
    ⋆ (c8 (r - 0x50#64) (dA t₀ ch)
    ⋆ (7 ?@ (r - 0x48#64)
    ⋆ (1 ?@ (r - 0x41#64)
    ⋆ (c8 (r - 0x40#64) (arg1 t₀)
    ⋆ (8 ?@ (r - 0x38#64)
    ⋆ (c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ Kt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

abbrev FrMb (x : Args) (t₀ : MachineData) (ch : Nat) (c0 : BitVec 32) (y : Args) (j : Nat) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x1c8#64)
    ⋆ (c8 (r - 0x1c0#64) (sbrA t₀ + 0x4c284#64)
    ⋆ (c8 (r - 0x1b8#64) (sbrA t₀ + 0x4c252#64)
    ⋆ (c8 (r - 0x1b0#64) (sbrA t₀ + 0x5e340#64)
    ⋆ (c8 (r - 0x1a8#64) (BitVec.ofNat 64 ch)
    ⋆ (c8 (r - 0x1a0#64) (sbrA t₀ + 0x4c288#64)
    ⋆ (c8 (r - 0x198#64) (sbrA t₀ + 0x4eb50#64)
    ⋆ (c8 (r - 0x190#64) (sbrA t₀ + 0x5dd40#64)
    ⋆ (c8 (r - 0x188#64) (sbrA t₀ + 0xb2#64)
    ⋆ (c8 (r - 0x180#64) (sbrA t₀ + 0x5e4c0#64)
    ⋆ (c8 (r - 0x178#64) (sbrA t₀ + 0x5f0c0#64)
    ⋆ (c8 (r - 0x170#64) (sbrA t₀ + 0x1c#64)
    ⋆ (c8 (r - 0x168#64) (sbrA t₀ + 0x150e0#64)
    ⋆ (c8 (r - 0x160#64) (sbrA t₀ + 0x5f6c4#64)
    ⋆ (c8 (r - 0x158#64) (BitVec.ofNat 64 (dsN x))
    ⋆ (c8 (r - 0x150#64) (sbrA t₀ + 0x5d340#64)
    ⋆ (c8 (r - 0x148#64) (sbrA t₀ + 0x5d540#64)
    ⋆ (c8 (r - 0x140#64) (sbrA t₀ + 0x80#64)
    ⋆ (c8 (r - 0x138#64) (arg3 t₀)
    ⋆ (c8 (r - 0x130#64) (arg4 t₀)
    ⋆ (c8 (r - 0x128#64) (sbrA t₀ + 0x601e0#64)
    ⋆ (c8 (r - 0x120#64) (sbrA t₀ + 0x5fcc0#64)
    ⋆ (8 ?@ (r - 0x118#64)
    ⋆ (c8 (r - 0x110#64) (sbrA t₀ + 0x5eac0#64)
    ⋆ (c8 (r - 0x108#64) (sbrA t₀ + 0x5f6c0#64)
    ⋆ (Int.toBytes 4 (c0.toInt) =@ (r - 0x100#64)
    ⋆ (4 ?@ (r - 0xfc#64)
    ⋆ (c8 (r - 0xf8#64) (lab "sbr_qmf_window_ds")
    ⋆ (c8 (r - 0xf0#64) (dA t₀ ch + 0x32#64)
    ⋆ (c8 (r - 0xe8#64) (dA t₀ ch + 0x15390#64)
    ⋆ (c8 (r - 0xe0#64) (dA t₀ ch + 0x15a60#64)
    ⋆ (c8 (r - 0xd8#64) (sbrA t₀ + 0x5d740#64)
    ⋆ (c8 (r - 0xd0#64) (sbrA t₀ + 0x5fdc0#64)
    ⋆ (c8 (r - 0xc8#64) (sbrA t₀ + 0x4c340#64)
    ⋆ (c8 (r - 0xc0#64) (sbrA t₀ + 0x4eb40#64)
    ⋆ (c8 (r - 0xb8#64) (sbrA t₀)
    ⋆ (c8 (r - 0xb0#64) (sbrA t₀ + 0x53b40#64)
    ⋆ (4 ?@ (r - 0xa8#64)
    ⋆ (Int.toBytes 4 ((BitVec.setWidth 32 (arg2 t₀)).toInt) =@ (r - 0xa4#64)
    ⋆ (c8 (r - 0xa0#64) (BitVec.ofNat 64 (0x15ac0 * ch))
    ⋆ (c8 (r - 0x98#64) (arg0 t₀)
    ⋆ (6 ?@ (r - 0x90#64)
    ⋆ (2 ?@ (r - 0x8a#64)
    ⋆ (c8 (r - 0x88#64) (dA t₀ ch + 0x15030#64)
    ⋆ (8 ?@ (r - 0x80#64)
    ⋆ (c8 (r - 0x78#64) (sbrA t₀ + 0x4ec90#64)
    ⋆ (c8 (r - 0x70#64) (BitVec.ofNat 64 (j + 1))
    ⋆ (c8 (r - 0x68#64) (arg1 t₀ + BitVec.ofNat 64 (0xc0 * j))
    ⋆ (c8 (r - 0x60#64) (sbrA t₀ + 0x5dd40#64 + BitVec.ofNat 64 (0xc0 * j))
    ⋆ (c8 (r - 0x58#64) (BitVec.ofNat 64 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.n0 else y.n1))
    ⋆ (c8 (r - 0x50#64) (dA t₀ ch)
    ⋆ (7 ?@ (r - 0x48#64)
    ⋆ (1 ?@ (r - 0x41#64)
    ⋆ (c8 (r - 0x40#64) (arg1 t₀)
    ⋆ (Int.toBytes 4 (BitVec.ofNat 32 y.kx1).toInt =@ (r - 0x38#64) ⋆ 4 ?@ (r - 0x34#64)
    ⋆ (c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ Kt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

abbrev FrMs (x : Args) (t₀ : MachineData) (ch : Nat) (c0 : BitVec 32) (y : Args) (j : Nat) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x1c8#64)
    ⋆ (c8 (r - 0x1c0#64) (sbrA t₀ + 0x4c284#64)
    ⋆ (c8 (r - 0x1b8#64) (sbrA t₀ + 0x4c252#64)
    ⋆ (c8 (r - 0x1b0#64) (sbrA t₀ + 0x5e340#64)
    ⋆ (c8 (r - 0x1a8#64) (BitVec.ofNat 64 ch)
    ⋆ (c8 (r - 0x1a0#64) (sbrA t₀ + 0x4c288#64)
    ⋆ (c8 (r - 0x198#64) (sbrA t₀ + 0x4eb50#64)
    ⋆ (c8 (r - 0x190#64) (sbrA t₀ + 0x5dd40#64)
    ⋆ (c8 (r - 0x188#64) (sbrA t₀ + 0xb2#64)
    ⋆ (c8 (r - 0x180#64) (sbrA t₀ + 0x5e4c0#64)
    ⋆ (c8 (r - 0x178#64) (sbrA t₀ + 0x5f0c0#64)
    ⋆ (c8 (r - 0x170#64) (sbrA t₀ + 0x1c#64)
    ⋆ (c8 (r - 0x168#64) (sbrA t₀ + 0x150e0#64)
    ⋆ (c8 (r - 0x160#64) (sbrA t₀ + 0x5f6c4#64)
    ⋆ (c8 (r - 0x158#64) (BitVec.ofNat 64 (dsN x))
    ⋆ (c8 (r - 0x150#64) (sbrA t₀ + 0x5d340#64)
    ⋆ (c8 (r - 0x148#64) (sbrA t₀ + 0x5d540#64)
    ⋆ (c8 (r - 0x140#64) (sbrA t₀ + 0x80#64)
    ⋆ (c8 (r - 0x138#64) (arg3 t₀)
    ⋆ (c8 (r - 0x130#64) (arg4 t₀)
    ⋆ (c8 (r - 0x128#64) (sbrA t₀ + 0x601e0#64)
    ⋆ (c8 (r - 0x120#64) (sbrA t₀ + 0x5fcc0#64)
    ⋆ (8 ?@ (r - 0x118#64)
    ⋆ (c8 (r - 0x110#64) (sbrA t₀ + 0x5eac0#64)
    ⋆ (c8 (r - 0x108#64) (sbrA t₀ + 0x5f6c0#64)
    ⋆ (Int.toBytes 4 (c0.toInt) =@ (r - 0x100#64)
    ⋆ (4 ?@ (r - 0xfc#64)
    ⋆ (c8 (r - 0xf8#64) (lab "sbr_qmf_window_ds")
    ⋆ (c8 (r - 0xf0#64) (dA t₀ ch + 0x32#64)
    ⋆ (c8 (r - 0xe8#64) (dA t₀ ch + 0x15390#64)
    ⋆ (c8 (r - 0xe0#64) (dA t₀ ch + 0x15a60#64)
    ⋆ (c8 (r - 0xd8#64) (sbrA t₀ + 0x5d740#64)
    ⋆ (c8 (r - 0xd0#64) (sbrA t₀ + 0x5fdc0#64)
    ⋆ (c8 (r - 0xc8#64) (sbrA t₀ + 0x4c340#64)
    ⋆ (c8 (r - 0xc0#64) (sbrA t₀ + 0x4eb40#64)
    ⋆ (c8 (r - 0xb8#64) (sbrA t₀)
    ⋆ (c8 (r - 0xb0#64) (sbrA t₀ + 0x53b40#64)
    ⋆ (4 ?@ (r - 0xa8#64)
    ⋆ (Int.toBytes 4 ((BitVec.setWidth 32 (arg2 t₀)).toInt) =@ (r - 0xa4#64)
    ⋆ (c8 (r - 0xa0#64) (BitVec.ofNat 64 (0x15ac0 * ch))
    ⋆ (c8 (r - 0x98#64) (arg0 t₀)
    ⋆ (6 ?@ (r - 0x90#64)
    ⋆ (2 ?@ (r - 0x8a#64)
    ⋆ (c8 (r - 0x88#64) (dA t₀ ch + 0x15030#64)
    ⋆ (c8 (r - 0x80#64) (BitVec.ofNat 64 ((2 ^ 32 - y.kx1) % 2 ^ 32))
    ⋆ (c8 (r - 0x78#64) (sbrA t₀ + 0x4ec90#64)
    ⋆ (c8 (r - 0x70#64) (BitVec.ofNat 64 (j + 1))
    ⋆ (c8 (r - 0x68#64) (arg1 t₀ + BitVec.ofNat 64 (0xc0 * j))
    ⋆ (c8 (r - 0x60#64) (sbrA t₀ + 0x5dd40#64 + BitVec.ofNat 64 (0xc0 * j))
    ⋆ (c8 (r - 0x58#64) (BitVec.ofNat 64 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.n0 else y.n1))
    ⋆ (c8 (r - 0x50#64) (dA t₀ ch)
    ⋆ (7 ?@ (r - 0x48#64)
    ⋆ (1 ?@ (r - 0x41#64)
    ⋆ (c8 (r - 0x40#64) (arg1 t₀)
    ⋆ (Int.toBytes 4 (BitVec.ofNat 32 y.kx1).toInt =@ (r - 0x38#64) ⋆ 4 ?@ (r - 0x34#64)
    ⋆ (c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ Kt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

abbrev FrMn (x : Args) (t₀ : MachineData) (ch : Nat) (c0 : BitVec 32) (y : Args) (j : Nat) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x1c8#64)
    ⋆ (c8 (r - 0x1c0#64) (sbrA t₀ + 0x4c284#64)
    ⋆ (c8 (r - 0x1b8#64) (sbrA t₀ + 0x4c252#64)
    ⋆ (c8 (r - 0x1b0#64) (sbrA t₀ + 0x5e340#64)
    ⋆ (c8 (r - 0x1a8#64) (BitVec.ofNat 64 ch)
    ⋆ (c8 (r - 0x1a0#64) (sbrA t₀ + 0x4c288#64)
    ⋆ (c8 (r - 0x198#64) (sbrA t₀ + 0x4eb50#64)
    ⋆ (c8 (r - 0x190#64) (sbrA t₀ + 0x5dd40#64)
    ⋆ (c8 (r - 0x188#64) (sbrA t₀ + 0xb2#64)
    ⋆ (c8 (r - 0x180#64) (sbrA t₀ + 0x5e4c0#64)
    ⋆ (c8 (r - 0x178#64) (sbrA t₀ + 0x5f0c0#64)
    ⋆ (c8 (r - 0x170#64) (sbrA t₀ + 0x1c#64)
    ⋆ (c8 (r - 0x168#64) (sbrA t₀ + 0x150e0#64)
    ⋆ (c8 (r - 0x160#64) (sbrA t₀ + 0x5f6c4#64)
    ⋆ (c8 (r - 0x158#64) (BitVec.ofNat 64 (dsN x))
    ⋆ (c8 (r - 0x150#64) (sbrA t₀ + 0x5d340#64)
    ⋆ (c8 (r - 0x148#64) (sbrA t₀ + 0x5d540#64)
    ⋆ (c8 (r - 0x140#64) (sbrA t₀ + 0x80#64)
    ⋆ (c8 (r - 0x138#64) (arg3 t₀)
    ⋆ (c8 (r - 0x130#64) (arg4 t₀)
    ⋆ (c8 (r - 0x128#64) (sbrA t₀ + 0x601e0#64)
    ⋆ (c8 (r - 0x120#64) (sbrA t₀ + 0x5fcc0#64)
    ⋆ (8 ?@ (r - 0x118#64)
    ⋆ (c8 (r - 0x110#64) (sbrA t₀ + 0x5eac0#64)
    ⋆ (c8 (r - 0x108#64) (sbrA t₀ + 0x5f6c0#64)
    ⋆ (Int.toBytes 4 (c0.toInt) =@ (r - 0x100#64)
    ⋆ (4 ?@ (r - 0xfc#64)
    ⋆ (c8 (r - 0xf8#64) (lab "sbr_qmf_window_ds")
    ⋆ (c8 (r - 0xf0#64) (dA t₀ ch + 0x32#64)
    ⋆ (c8 (r - 0xe8#64) (dA t₀ ch + 0x15390#64)
    ⋆ (c8 (r - 0xe0#64) (dA t₀ ch + 0x15a60#64)
    ⋆ (c8 (r - 0xd8#64) (sbrA t₀ + 0x5d740#64)
    ⋆ (c8 (r - 0xd0#64) (sbrA t₀ + 0x5fdc0#64)
    ⋆ (c8 (r - 0xc8#64) (sbrA t₀ + 0x4c340#64)
    ⋆ (c8 (r - 0xc0#64) (sbrA t₀ + 0x4eb40#64)
    ⋆ (c8 (r - 0xb8#64) (sbrA t₀)
    ⋆ (c8 (r - 0xb0#64) (sbrA t₀ + 0x53b40#64)
    ⋆ (4 ?@ (r - 0xa8#64)
    ⋆ (Int.toBytes 4 ((BitVec.setWidth 32 (arg2 t₀)).toInt) =@ (r - 0xa4#64)
    ⋆ (c8 (r - 0xa0#64) (BitVec.ofNat 64 (0x15ac0 * ch))
    ⋆ (c8 (r - 0x98#64) (arg0 t₀)
    ⋆ (6 ?@ (r - 0x90#64)
    ⋆ (2 ?@ (r - 0x8a#64)
    ⋆ (c8 (r - 0x88#64) (dA t₀ ch + 0x15030#64)
    ⋆ (8 ?@ (r - 0x80#64)
    ⋆ (c8 (r - 0x78#64) (sbrA t₀ + 0x4ec90#64)
    ⋆ (c8 (r - 0x70#64) (BitVec.ofNat 64 (j + 1))
    ⋆ (c8 (r - 0x68#64) (arg1 t₀ + BitVec.ofNat 64 (0xc0 * j))
    ⋆ (c8 (r - 0x60#64) (sbrA t₀ + 0x5dd40#64 + BitVec.ofNat 64 (0xc0 * (j + 1)))
    ⋆ (c8 (r - 0x58#64) (BitVec.ofNat 64 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.n0 else y.n1))
    ⋆ (c8 (r - 0x50#64) (dA t₀ ch)
    ⋆ (7 ?@ (r - 0x48#64)
    ⋆ (1 ?@ (r - 0x41#64)
    ⋆ (c8 (r - 0x40#64) (arg1 t₀)
    ⋆ (Int.toBytes 4 (BitVec.ofNat 32 y.kx1).toInt =@ (r - 0x38#64) ⋆ 4 ?@ (r - 0x34#64)
    ⋆ (c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ Kt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

abbrev FrZ (x : Args) (t₀ : MachineData) (ch : Nat) (c0 : BitVec 32) (y : Args) (j : Nat) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x1c8#64)
    ⋆ (c8 (r - 0x1c0#64) (sbrA t₀ + 0x4c284#64)
    ⋆ (c8 (r - 0x1b8#64) (sbrA t₀ + 0x4c252#64)
    ⋆ (c8 (r - 0x1b0#64) (sbrA t₀ + 0x5e340#64)
    ⋆ (c8 (r - 0x1a8#64) (BitVec.ofNat 64 ch)
    ⋆ (c8 (r - 0x1a0#64) (sbrA t₀ + 0x4c288#64)
    ⋆ (c8 (r - 0x198#64) (sbrA t₀ + 0x4eb50#64)
    ⋆ (c8 (r - 0x190#64) (sbrA t₀ + 0x5dd40#64)
    ⋆ (c8 (r - 0x188#64) (sbrA t₀ + 0xb2#64)
    ⋆ (c8 (r - 0x180#64) (sbrA t₀ + 0x5e4c0#64)
    ⋆ (c8 (r - 0x178#64) (sbrA t₀ + 0x5f0c0#64)
    ⋆ (c8 (r - 0x170#64) (sbrA t₀ + 0x1c#64)
    ⋆ (c8 (r - 0x168#64) (sbrA t₀ + 0x150e0#64)
    ⋆ (c8 (r - 0x160#64) (sbrA t₀ + 0x5f6c4#64)
    ⋆ (c8 (r - 0x158#64) (BitVec.ofNat 64 (dsN x))
    ⋆ (c8 (r - 0x150#64) (sbrA t₀ + 0x5d340#64)
    ⋆ (c8 (r - 0x148#64) (sbrA t₀ + 0x5d540#64)
    ⋆ (c8 (r - 0x140#64) (sbrA t₀ + 0x80#64)
    ⋆ (c8 (r - 0x138#64) (arg3 t₀)
    ⋆ (c8 (r - 0x130#64) (arg4 t₀)
    ⋆ (c8 (r - 0x128#64) (sbrA t₀ + 0x601e0#64)
    ⋆ (c8 (r - 0x120#64) (sbrA t₀ + 0x5fcc0#64)
    ⋆ (8 ?@ (r - 0x118#64)
    ⋆ (c8 (r - 0x110#64) (sbrA t₀ + 0x5eac0#64)
    ⋆ (c8 (r - 0x108#64) (sbrA t₀ + 0x5f6c0#64)
    ⋆ (Int.toBytes 4 (c0.toInt) =@ (r - 0x100#64)
    ⋆ (4 ?@ (r - 0xfc#64)
    ⋆ (c8 (r - 0xf8#64) (lab "sbr_qmf_window_ds")
    ⋆ (8 ?@ (r - 0xf0#64)
    ⋆ (8 ?@ (r - 0xe8#64)
    ⋆ (8 ?@ (r - 0xe0#64)
    ⋆ (c8 (r - 0xd8#64) (sbrA t₀ + 0x5d740#64)
    ⋆ (c8 (r - 0xd0#64) (sbrA t₀ + 0x5fdc0#64)
    ⋆ (c8 (r - 0xc8#64) (sbrA t₀ + 0x4c340#64)
    ⋆ (c8 (r - 0xc0#64) (sbrA t₀ + 0x4eb40#64)
    ⋆ (c8 (r - 0xb8#64) (sbrA t₀)
    ⋆ (c8 (r - 0xb0#64) (sbrA t₀ + 0x53b40#64)
    ⋆ (4 ?@ (r - 0xa8#64)
    ⋆ (Int.toBytes 4 ((BitVec.setWidth 32 (arg2 t₀)).toInt) =@ (r - 0xa4#64)
    ⋆ (c8 (r - 0xa0#64) (BitVec.ofNat 64 (0x15ac0 * ch))
    ⋆ (c8 (r - 0x98#64) (arg0 t₀)
    ⋆ (6 ?@ (r - 0x90#64)
    ⋆ (2 ?@ (r - 0x8a#64)
    ⋆ (8 ?@ (r - 0x88#64)
    ⋆ (8 ?@ (r - 0x80#64)
    ⋆ (c8 (r - 0x78#64) (sbrA t₀ + 0x4ec90#64)
    ⋆ (8 ?@ (r - 0x70#64)
    ⋆ (8 ?@ (r - 0x68#64)
    ⋆ (8 ?@ (r - 0x60#64)
    ⋆ (8 ?@ (r - 0x58#64)
    ⋆ (c8 (r - 0x50#64) (dA t₀ ch)
    ⋆ (7 ?@ (r - 0x48#64)
    ⋆ (1 ?@ (r - 0x41#64)
    ⋆ (c8 (r - 0x40#64) (arg1 t₀)
    ⋆ (8 ?@ (r - 0x38#64)
    ⋆ (c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ Kt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

abbrev FrE1 (x : Args) (t₀ : MachineData) (ch : Nat) (c0 : BitVec 32) (y : Args) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x1c8#64)
    ⋆ (c8 (r - 0x1c0#64) (sbrA t₀ + 0x4c284#64)
    ⋆ (c8 (r - 0x1b8#64) (sbrA t₀ + 0x4c252#64)
    ⋆ (c8 (r - 0x1b0#64) (sbrA t₀ + 0x5e340#64)
    ⋆ (c8 (r - 0x1a8#64) (BitVec.ofNat 64 ch)
    ⋆ (c8 (r - 0x1a0#64) (sbrA t₀ + 0x4c288#64)
    ⋆ (c8 (r - 0x198#64) (sbrA t₀ + 0x4eb50#64)
    ⋆ (c8 (r - 0x190#64) (sbrA t₀ + 0x5dd40#64)
    ⋆ (c8 (r - 0x188#64) (sbrA t₀ + 0xb2#64)
    ⋆ (c8 (r - 0x180#64) (sbrA t₀ + 0x5e4c0#64)
    ⋆ (c8 (r - 0x178#64) (sbrA t₀ + 0x5f0c0#64)
    ⋆ (c8 (r - 0x170#64) (sbrA t₀ + 0x1c#64)
    ⋆ (c8 (r - 0x168#64) (sbrA t₀ + 0x150e0#64)
    ⋆ (c8 (r - 0x160#64) (sbrA t₀ + 0x5f6c4#64)
    ⋆ (c8 (r - 0x158#64) (BitVec.ofNat 64 (dsN x))
    ⋆ (c8 (r - 0x150#64) (sbrA t₀ + 0x5d340#64)
    ⋆ (c8 (r - 0x148#64) (sbrA t₀ + 0x5d540#64)
    ⋆ (c8 (r - 0x140#64) (sbrA t₀ + 0x80#64)
    ⋆ (c8 (r - 0x138#64) (arg3 t₀)
    ⋆ (c8 (r - 0x130#64) (arg4 t₀)
    ⋆ (c8 (r - 0x128#64) (sbrA t₀ + 0x601e0#64)
    ⋆ (c8 (r - 0x120#64) (sbrA t₀ + 0x5fcc0#64)
    ⋆ (c8 (r - 0x118#64) (dA t₀ ch + 0x3904#64)
    ⋆ (c8 (r - 0x110#64) (sbrA t₀ + 0x5eac0#64)
    ⋆ (c8 (r - 0x108#64) (sbrA t₀ + 0x5f6c0#64)
    ⋆ (Int.toBytes 4 (c0.toInt) =@ (r - 0x100#64)
    ⋆ (4 ?@ (r - 0xfc#64)
    ⋆ (c8 (r - 0xf8#64) (lab "sbr_qmf_window_ds")
    ⋆ (8 ?@ (r - 0xf0#64)
    ⋆ (8 ?@ (r - 0xe8#64)
    ⋆ (8 ?@ (r - 0xe0#64)
    ⋆ (c8 (r - 0xd8#64) (sbrA t₀ + 0x5d740#64)
    ⋆ (c8 (r - 0xd0#64) (sbrA t₀ + 0x5fdc0#64)
    ⋆ (c8 (r - 0xc8#64) (sbrA t₀ + 0x4c340#64)
    ⋆ (c8 (r - 0xc0#64) (sbrA t₀ + 0x4eb40#64)
    ⋆ (c8 (r - 0xb8#64) (sbrA t₀)
    ⋆ (c8 (r - 0xb0#64) (sbrA t₀ + 0x53b40#64)
    ⋆ (4 ?@ (r - 0xa8#64)
    ⋆ (Int.toBytes 4 ((BitVec.setWidth 32 (arg2 t₀)).toInt) =@ (r - 0xa4#64)
    ⋆ (c8 (r - 0xa0#64) (BitVec.ofNat 64 (0x15ac0 * ch))
    ⋆ (c8 (r - 0x98#64) (arg0 t₀)
    ⋆ (6 ?@ (r - 0x90#64)
    ⋆ (2 ?@ (r - 0x8a#64)
    ⋆ (8 ?@ (r - 0x88#64)
    ⋆ (8 ?@ (r - 0x80#64)
    ⋆ (c8 (r - 0x78#64) (sbrA t₀ + 0x4ec90#64)
    ⋆ (8 ?@ (r - 0x70#64)
    ⋆ (8 ?@ (r - 0x68#64)
    ⋆ (8 ?@ (r - 0x60#64)
    ⋆ (8 ?@ (r - 0x58#64)
    ⋆ (c8 (r - 0x50#64) (dA t₀ ch)
    ⋆ (7 ?@ (r - 0x48#64)
    ⋆ (1 ?@ (r - 0x41#64)
    ⋆ (c8 (r - 0x40#64) (arg1 t₀)
    ⋆ (Int.toBytes 4 (BitVec.ofNat 32 y.kx1).toInt =@ (r - 0x38#64) ⋆ 4 ?@ (r - 0x34#64)
    ⋆ (c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ Kt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

abbrev FrI0 (x : Args) (t₀ : MachineData) (ch : Nat) (c0 : BitVec 32) (y : Args) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x1c8#64)
    ⋆ (c8 (r - 0x1c0#64) (sbrA t₀ + 0x4c284#64)
    ⋆ (c8 (r - 0x1b8#64) (sbrA t₀ + 0x4c252#64)
    ⋆ (c8 (r - 0x1b0#64) (sbrA t₀ + 0x5e340#64)
    ⋆ (c8 (r - 0x1a8#64) (BitVec.ofNat 64 ch)
    ⋆ (c8 (r - 0x1a0#64) (sbrA t₀ + 0x4c288#64)
    ⋆ (c8 (r - 0x198#64) (sbrA t₀ + 0x4eb50#64)
    ⋆ (c8 (r - 0x190#64) (sbrA t₀ + 0x5dd40#64)
    ⋆ (c8 (r - 0x188#64) (sbrA t₀ + 0xb2#64)
    ⋆ (c8 (r - 0x180#64) (sbrA t₀ + 0x5e4c0#64)
    ⋆ (c8 (r - 0x178#64) (sbrA t₀ + 0x5f0c0#64)
    ⋆ (c8 (r - 0x170#64) (sbrA t₀ + 0x1c#64)
    ⋆ (c8 (r - 0x168#64) (sbrA t₀ + 0x150e0#64)
    ⋆ (c8 (r - 0x160#64) (sbrA t₀ + 0x5f6c4#64)
    ⋆ (c8 (r - 0x158#64) (BitVec.ofNat 64 (dsN x))
    ⋆ (c8 (r - 0x150#64) (sbrA t₀ + 0x5d340#64)
    ⋆ (c8 (r - 0x148#64) (sbrA t₀ + 0x5d540#64)
    ⋆ (c8 (r - 0x140#64) (sbrA t₀ + 0x80#64)
    ⋆ (c8 (r - 0x138#64) (arg3 t₀)
    ⋆ (c8 (r - 0x130#64) (arg4 t₀)
    ⋆ (c8 (r - 0x128#64) (sbrA t₀ + 0x601e0#64)
    ⋆ (c8 (r - 0x120#64) (sbrA t₀ + 0x5fcc0#64)
    ⋆ (c8 (r - 0x118#64) (dA t₀ ch + 0x3904#64)
    ⋆ (c8 (r - 0x110#64) (sbrA t₀ + 0x5eac0#64)
    ⋆ (c8 (r - 0x108#64) (sbrA t₀ + 0x5f6c0#64)
    ⋆ (Int.toBytes 4 (c0.toInt) =@ (r - 0x100#64)
    ⋆ (4 ?@ (r - 0xfc#64)
    ⋆ (c8 (r - 0xf8#64) (lab "sbr_qmf_window_ds")
    ⋆ (8 ?@ (r - 0xf0#64)
    ⋆ (8 ?@ (r - 0xe8#64)
    ⋆ (8 ?@ (r - 0xe0#64)
    ⋆ (c8 (r - 0xd8#64) (sbrA t₀ + 0x5d740#64)
    ⋆ (c8 (r - 0xd0#64) (sbrA t₀ + 0x5fdc0#64)
    ⋆ (c8 (r - 0xc8#64) (sbrA t₀ + 0x4c340#64)
    ⋆ (c8 (r - 0xc0#64) (sbrA t₀ + 0x4eb40#64)
    ⋆ (c8 (r - 0xb8#64) (sbrA t₀)
    ⋆ (c8 (r - 0xb0#64) (sbrA t₀ + 0x53b40#64)
    ⋆ (4 ?@ (r - 0xa8#64)
    ⋆ (Int.toBytes 4 ((BitVec.setWidth 32 (arg2 t₀)).toInt) =@ (r - 0xa4#64)
    ⋆ (c8 (r - 0xa0#64) (BitVec.ofNat 64 (0x15ac0 * ch))
    ⋆ (c8 (r - 0x98#64) (arg0 t₀)
    ⋆ (6 ?@ (r - 0x90#64)
    ⋆ (2 ?@ (r - 0x8a#64)
    ⋆ (8 ?@ (r - 0x88#64)
    ⋆ (8 ?@ (r - 0x80#64)
    ⋆ (c8 (r - 0x78#64) (sbrA t₀ + 0x4ec90#64)
    ⋆ (8 ?@ (r - 0x70#64)
    ⋆ (8 ?@ (r - 0x68#64)
    ⋆ (8 ?@ (r - 0x60#64)
    ⋆ (c8 (r - 0x58#64) ((sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (320 * y.kx1))
    ⋆ (c8 (r - 0x50#64) (dA t₀ ch)
    ⋆ (7 ?@ (r - 0x48#64)
    ⋆ (1 ?@ (r - 0x41#64)
    ⋆ (c8 (r - 0x40#64) (arg1 t₀)
    ⋆ (4 ?@ (r - 0x38#64) ⋆ 4 ?@ (r - 0x34#64)
    ⋆ (c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ Kt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

abbrev FrI1 (x : Args) (t₀ : MachineData) (ch : Nat) (c0 : BitVec 32) (y : Args) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x1c8#64)
    ⋆ (c8 (r - 0x1c0#64) (sbrA t₀ + 0x4c284#64)
    ⋆ (c8 (r - 0x1b8#64) (sbrA t₀ + 0x4c252#64)
    ⋆ (c8 (r - 0x1b0#64) (sbrA t₀ + 0x5e340#64)
    ⋆ (c8 (r - 0x1a8#64) (BitVec.ofNat 64 ch)
    ⋆ (c8 (r - 0x1a0#64) (sbrA t₀ + 0x4c288#64)
    ⋆ (c8 (r - 0x198#64) (sbrA t₀ + 0x4eb50#64)
    ⋆ (c8 (r - 0x190#64) (sbrA t₀ + 0x5dd40#64)
    ⋆ (c8 (r - 0x188#64) (sbrA t₀ + 0xb2#64)
    ⋆ (c8 (r - 0x180#64) (sbrA t₀ + 0x5e4c0#64)
    ⋆ (c8 (r - 0x178#64) (sbrA t₀ + 0x5f0c0#64)
    ⋆ (c8 (r - 0x170#64) (sbrA t₀ + 0x1c#64)
    ⋆ (c8 (r - 0x168#64) (sbrA t₀ + 0x150e0#64)
    ⋆ (c8 (r - 0x160#64) (sbrA t₀ + 0x5f6c4#64)
    ⋆ (c8 (r - 0x158#64) (BitVec.ofNat 64 (dsN x))
    ⋆ (c8 (r - 0x150#64) (sbrA t₀ + 0x5d340#64)
    ⋆ (c8 (r - 0x148#64) (sbrA t₀ + 0x5d540#64)
    ⋆ (c8 (r - 0x140#64) (sbrA t₀ + 0x80#64)
    ⋆ (c8 (r - 0x138#64) (arg3 t₀)
    ⋆ (c8 (r - 0x130#64) (arg4 t₀)
    ⋆ (c8 (r - 0x128#64) (sbrA t₀ + 0x601e0#64)
    ⋆ (c8 (r - 0x120#64) (sbrA t₀ + 0x5fcc0#64)
    ⋆ (c8 (r - 0x118#64) (dA t₀ ch + 0x3904#64)
    ⋆ (c8 (r - 0x110#64) (sbrA t₀ + 0x5eac0#64)
    ⋆ (c8 (r - 0x108#64) (sbrA t₀ + 0x5f6c0#64)
    ⋆ (Int.toBytes 4 (c0.toInt) =@ (r - 0x100#64)
    ⋆ (4 ?@ (r - 0xfc#64)
    ⋆ (c8 (r - 0xf8#64) (lab "sbr_qmf_window_ds")
    ⋆ (8 ?@ (r - 0xf0#64)
    ⋆ (8 ?@ (r - 0xe8#64)
    ⋆ (8 ?@ (r - 0xe0#64)
    ⋆ (c8 (r - 0xd8#64) (sbrA t₀ + 0x5d740#64)
    ⋆ (c8 (r - 0xd0#64) (sbrA t₀ + 0x5fdc0#64)
    ⋆ (c8 (r - 0xc8#64) (sbrA t₀ + 0x4c340#64)
    ⋆ (c8 (r - 0xc0#64) (sbrA t₀ + 0x4eb40#64)
    ⋆ (c8 (r - 0xb8#64) (sbrA t₀)
    ⋆ (c8 (r - 0xb0#64) (sbrA t₀ + 0x53b40#64)
    ⋆ (4 ?@ (r - 0xa8#64)
    ⋆ (Int.toBytes 4 ((BitVec.setWidth 32 (arg2 t₀)).toInt) =@ (r - 0xa4#64)
    ⋆ (c8 (r - 0xa0#64) (BitVec.ofNat 64 (0x15ac0 * ch))
    ⋆ (c8 (r - 0x98#64) (arg0 t₀)
    ⋆ (6 ?@ (r - 0x90#64)
    ⋆ (2 ?@ (r - 0x8a#64)
    ⋆ (8 ?@ (r - 0x88#64)
    ⋆ (8 ?@ (r - 0x80#64)
    ⋆ (c8 (r - 0x78#64) (sbrA t₀ + 0x4ec90#64)
    ⋆ (8 ?@ (r - 0x70#64)
    ⋆ (8 ?@ (r - 0x68#64)
    ⋆ (8 ?@ (r - 0x60#64)
    ⋆ (c8 (r - 0x58#64) (BitVec.ofNat 64 (320 * y.kx1))
    ⋆ (c8 (r - 0x50#64) (dA t₀ ch)
    ⋆ (7 ?@ (r - 0x48#64)
    ⋆ (1 ?@ (r - 0x41#64)
    ⋆ (c8 (r - 0x40#64) (arg1 t₀)
    ⋆ (4 ?@ (r - 0x38#64) ⋆ 4 ?@ (r - 0x34#64)
    ⋆ (c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ Kt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

abbrev FrN0 (x : Args) (t₀ : MachineData) (ch : Nat) (c0 : BitVec 32) (y : Args) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x1c8#64)
    ⋆ (c8 (r - 0x1c0#64) (sbrA t₀ + 0x4c284#64)
    ⋆ (c8 (r - 0x1b8#64) (sbrA t₀ + 0x4c252#64)
    ⋆ (c8 (r - 0x1b0#64) (sbrA t₀ + 0x5e340#64)
    ⋆ (c8 (r - 0x1a8#64) (BitVec.ofNat 64 ch)
    ⋆ (c8 (r - 0x1a0#64) (sbrA t₀ + 0x4c288#64)
    ⋆ (c8 (r - 0x198#64) (sbrA t₀ + 0x4eb50#64)
    ⋆ (c8 (r - 0x190#64) (sbrA t₀ + 0x5dd40#64)
    ⋆ (c8 (r - 0x188#64) (sbrA t₀ + 0xb2#64)
    ⋆ (c8 (r - 0x180#64) (sbrA t₀ + 0x5e4c0#64)
    ⋆ (c8 (r - 0x178#64) (sbrA t₀ + 0x5f0c0#64)
    ⋆ (c8 (r - 0x170#64) (sbrA t₀ + 0x1c#64)
    ⋆ (c8 (r - 0x168#64) (sbrA t₀ + 0x150e0#64)
    ⋆ (c8 (r - 0x160#64) (sbrA t₀ + 0x5f6c4#64)
    ⋆ (c8 (r - 0x158#64) (BitVec.ofNat 64 (dsN x))
    ⋆ (c8 (r - 0x150#64) (sbrA t₀ + 0x5d340#64)
    ⋆ (c8 (r - 0x148#64) (sbrA t₀ + 0x5d540#64)
    ⋆ (c8 (r - 0x140#64) (sbrA t₀ + 0x80#64)
    ⋆ (c8 (r - 0x138#64) (arg3 t₀)
    ⋆ (c8 (r - 0x130#64) (arg4 t₀)
    ⋆ (c8 (r - 0x128#64) (sbrA t₀ + 0x601e0#64)
    ⋆ (c8 (r - 0x120#64) (sbrA t₀ + 0x5fcc0#64)
    ⋆ (c8 (r - 0x118#64) (dA t₀ ch + 0x3904#64)
    ⋆ (c8 (r - 0x110#64) (sbrA t₀ + 0x5eac0#64)
    ⋆ (c8 (r - 0x108#64) (sbrA t₀ + 0x5f6c0#64)
    ⋆ (Int.toBytes 4 (c0.toInt) =@ (r - 0x100#64)
    ⋆ (4 ?@ (r - 0xfc#64)
    ⋆ (c8 (r - 0xf8#64) (lab "sbr_qmf_window_ds")
    ⋆ (8 ?@ (r - 0xf0#64)
    ⋆ (8 ?@ (r - 0xe8#64)
    ⋆ (8 ?@ (r - 0xe0#64)
    ⋆ (c8 (r - 0xd8#64) (sbrA t₀ + 0x5d740#64)
    ⋆ (c8 (r - 0xd0#64) (sbrA t₀ + 0x5fdc0#64)
    ⋆ (c8 (r - 0xc8#64) (sbrA t₀ + 0x4c340#64)
    ⋆ (c8 (r - 0xc0#64) (sbrA t₀ + 0x4eb40#64)
    ⋆ (c8 (r - 0xb8#64) (sbrA t₀)
    ⋆ (c8 (r - 0xb0#64) (sbrA t₀ + 0x53b40#64)
    ⋆ (4 ?@ (r - 0xa8#64)
    ⋆ (Int.toBytes 4 ((BitVec.setWidth 32 (arg2 t₀)).toInt) =@ (r - 0xa4#64)
    ⋆ (c8 (r - 0xa0#64) (BitVec.ofNat 64 (0x15ac0 * ch))
    ⋆ (c8 (r - 0x98#64) (arg0 t₀)
    ⋆ (6 ?@ (r - 0x90#64)
    ⋆ (2 ?@ (r - 0x8a#64)
    ⋆ (8 ?@ (r - 0x88#64)
    ⋆ (8 ?@ (r - 0x80#64)
    ⋆ (c8 (r - 0x78#64) (sbrA t₀ + 0x4ec90#64)
    ⋆ (8 ?@ (r - 0x70#64)
    ⋆ (c8 (r - 0x68#64) (BitVec.ofNat 64 y.kx1)
    ⋆ (8 ?@ (r - 0x60#64)
    ⋆ (8 ?@ (r - 0x58#64)
    ⋆ (c8 (r - 0x50#64) (dA t₀ ch)
    ⋆ (7 ?@ (r - 0x48#64)
    ⋆ (1 ?@ (r - 0x41#64)
    ⋆ (c8 (r - 0x40#64) (arg1 t₀)
    ⋆ (4 ?@ (r - 0x38#64) ⋆ 4 ?@ (r - 0x34#64)
    ⋆ (c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ Kt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

abbrev FrN (x : Args) (t₀ : MachineData) (ch : Nat) (c0 : BitVec 32) (y : Args) (j : Nat) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x1c8#64)
    ⋆ (c8 (r - 0x1c0#64) (sbrA t₀ + 0x4c284#64)
    ⋆ (c8 (r - 0x1b8#64) (sbrA t₀ + 0x4c252#64)
    ⋆ (c8 (r - 0x1b0#64) (sbrA t₀ + 0x5e340#64)
    ⋆ (c8 (r - 0x1a8#64) (BitVec.ofNat 64 ch)
    ⋆ (c8 (r - 0x1a0#64) (sbrA t₀ + 0x4c288#64)
    ⋆ (c8 (r - 0x198#64) (sbrA t₀ + 0x4eb50#64)
    ⋆ (c8 (r - 0x190#64) (sbrA t₀ + 0x5dd40#64)
    ⋆ (c8 (r - 0x188#64) (sbrA t₀ + 0xb2#64)
    ⋆ (c8 (r - 0x180#64) (sbrA t₀ + 0x5e4c0#64)
    ⋆ (c8 (r - 0x178#64) (sbrA t₀ + 0x5f0c0#64)
    ⋆ (c8 (r - 0x170#64) (sbrA t₀ + 0x1c#64)
    ⋆ (c8 (r - 0x168#64) (sbrA t₀ + 0x150e0#64)
    ⋆ (c8 (r - 0x160#64) (sbrA t₀ + 0x5f6c4#64)
    ⋆ (c8 (r - 0x158#64) (BitVec.ofNat 64 (dsN x))
    ⋆ (c8 (r - 0x150#64) (sbrA t₀ + 0x5d340#64)
    ⋆ (c8 (r - 0x148#64) (sbrA t₀ + 0x5d540#64)
    ⋆ (c8 (r - 0x140#64) (sbrA t₀ + 0x80#64)
    ⋆ (c8 (r - 0x138#64) (arg3 t₀)
    ⋆ (c8 (r - 0x130#64) (arg4 t₀)
    ⋆ (c8 (r - 0x128#64) (sbrA t₀ + 0x601e0#64)
    ⋆ (c8 (r - 0x120#64) (sbrA t₀ + 0x5fcc0#64)
    ⋆ (c8 (r - 0x118#64) (dA t₀ ch + 0x3904#64)
    ⋆ (c8 (r - 0x110#64) (sbrA t₀ + 0x5eac0#64)
    ⋆ (c8 (r - 0x108#64) (sbrA t₀ + 0x5f6c0#64)
    ⋆ (Int.toBytes 4 (c0.toInt) =@ (r - 0x100#64)
    ⋆ (4 ?@ (r - 0xfc#64)
    ⋆ (c8 (r - 0xf8#64) (lab "sbr_qmf_window_ds")
    ⋆ (8 ?@ (r - 0xf0#64)
    ⋆ (8 ?@ (r - 0xe8#64)
    ⋆ (8 ?@ (r - 0xe0#64)
    ⋆ (c8 (r - 0xd8#64) (sbrA t₀ + 0x5d740#64)
    ⋆ (c8 (r - 0xd0#64) (sbrA t₀ + 0x5fdc0#64)
    ⋆ (c8 (r - 0xc8#64) (sbrA t₀ + 0x4c340#64)
    ⋆ (c8 (r - 0xc0#64) (sbrA t₀ + 0x4eb40#64)
    ⋆ (c8 (r - 0xb8#64) (sbrA t₀)
    ⋆ (c8 (r - 0xb0#64) (sbrA t₀ + 0x53b40#64)
    ⋆ (4 ?@ (r - 0xa8#64)
    ⋆ (Int.toBytes 4 ((BitVec.setWidth 32 (arg2 t₀)).toInt) =@ (r - 0xa4#64)
    ⋆ (c8 (r - 0xa0#64) (BitVec.ofNat 64 (0x15ac0 * ch))
    ⋆ (c8 (r - 0x98#64) (arg0 t₀)
    ⋆ (6 ?@ (r - 0x90#64)
    ⋆ (2 ?@ (r - 0x8a#64)
    ⋆ (c8 (r - 0x88#64) (sbrA t₀ + 0x4eb50#64 + BitVec.ofNat 64 (16 * u8 (y.d ch).te j))
    ⋆ (c8 (r - 0x80#64) (arg1 t₀ + BitVec.ofNat 64 (0xc0 * j))
    ⋆ (c8 (r - 0x78#64) (sbrA t₀ + 0x4ec90#64)
    ⋆ (c8 (r - 0x70#64) (BitVec.ofNat 64 (j + 1))
    ⋆ (c8 (r - 0x68#64) (BitVec.ofNat 64 y.kx1)
    ⋆ (8 ?@ (r - 0x60#64)
    ⋆ (8 ?@ (r - 0x58#64)
    ⋆ (c8 (r - 0x50#64) (dA t₀ ch)
    ⋆ (7 ?@ (r - 0x48#64)
    ⋆ (1 ?@ (r - 0x41#64)
    ⋆ (c8 (r - 0x40#64) (arg1 t₀)
    ⋆ (4 ?@ (r - 0x38#64) ⋆ 4 ?@ (r - 0x34#64)
    ⋆ (c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ Kt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

abbrev FrNP (x : Args) (t₀ : MachineData) (ch : Nat) (c0 : BitVec 32) (y : Args) (j p : Nat) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x1c8#64)
    ⋆ (c8 (r - 0x1c0#64) (sbrA t₀ + 0x4c284#64)
    ⋆ (c8 (r - 0x1b8#64) (sbrA t₀ + 0x4c252#64)
    ⋆ (c8 (r - 0x1b0#64) (sbrA t₀ + 0x5e340#64)
    ⋆ (c8 (r - 0x1a8#64) (BitVec.ofNat 64 ch)
    ⋆ (c8 (r - 0x1a0#64) (sbrA t₀ + 0x4c288#64)
    ⋆ (c8 (r - 0x198#64) (sbrA t₀ + 0x4eb50#64)
    ⋆ (c8 (r - 0x190#64) (sbrA t₀ + 0x5dd40#64)
    ⋆ (c8 (r - 0x188#64) (sbrA t₀ + 0xb2#64)
    ⋆ (c8 (r - 0x180#64) (sbrA t₀ + 0x5e4c0#64)
    ⋆ (c8 (r - 0x178#64) (sbrA t₀ + 0x5f0c0#64)
    ⋆ (c8 (r - 0x170#64) (sbrA t₀ + 0x1c#64)
    ⋆ (c8 (r - 0x168#64) (sbrA t₀ + 0x150e0#64)
    ⋆ (c8 (r - 0x160#64) (sbrA t₀ + 0x5f6c4#64)
    ⋆ (c8 (r - 0x158#64) (BitVec.ofNat 64 (dsN x))
    ⋆ (c8 (r - 0x150#64) (sbrA t₀ + 0x5d340#64)
    ⋆ (c8 (r - 0x148#64) (sbrA t₀ + 0x5d540#64)
    ⋆ (c8 (r - 0x140#64) (sbrA t₀ + 0x80#64)
    ⋆ (c8 (r - 0x138#64) (arg3 t₀)
    ⋆ (c8 (r - 0x130#64) (arg4 t₀)
    ⋆ (c8 (r - 0x128#64) (sbrA t₀ + 0x601e0#64)
    ⋆ (c8 (r - 0x120#64) (sbrA t₀ + 0x5fcc0#64)
    ⋆ (c8 (r - 0x118#64) (dA t₀ ch + 0x3904#64)
    ⋆ (c8 (r - 0x110#64) (sbrA t₀ + 0x5eac0#64)
    ⋆ (c8 (r - 0x108#64) (sbrA t₀ + 0x5f6c0#64)
    ⋆ (Int.toBytes 4 (c0.toInt) =@ (r - 0x100#64)
    ⋆ (4 ?@ (r - 0xfc#64)
    ⋆ (c8 (r - 0xf8#64) (lab "sbr_qmf_window_ds")
    ⋆ (8 ?@ (r - 0xf0#64)
    ⋆ (8 ?@ (r - 0xe8#64)
    ⋆ (8 ?@ (r - 0xe0#64)
    ⋆ (c8 (r - 0xd8#64) (sbrA t₀ + 0x5d740#64)
    ⋆ (c8 (r - 0xd0#64) (sbrA t₀ + 0x5fdc0#64)
    ⋆ (c8 (r - 0xc8#64) (sbrA t₀ + 0x4c340#64)
    ⋆ (c8 (r - 0xc0#64) (sbrA t₀ + 0x4eb40#64)
    ⋆ (c8 (r - 0xb8#64) (sbrA t₀)
    ⋆ (c8 (r - 0xb0#64) (sbrA t₀ + 0x53b40#64)
    ⋆ (4 ?@ (r - 0xa8#64)
    ⋆ (Int.toBytes 4 ((BitVec.setWidth 32 (arg2 t₀)).toInt) =@ (r - 0xa4#64)
    ⋆ (c8 (r - 0xa0#64) (BitVec.ofNat 64 (0x15ac0 * ch))
    ⋆ (c8 (r - 0x98#64) (arg0 t₀)
    ⋆ (6 ?@ (r - 0x90#64)
    ⋆ (2 ?@ (r - 0x8a#64)
    ⋆ (c8 (r - 0x88#64) (sbrA t₀ + 0x4eb50#64 + BitVec.ofNat 64 (16 * u8 (y.d ch).te j))
    ⋆ (c8 (r - 0x80#64) (arg1 t₀ + BitVec.ofNat 64 (0xc0 * j))
    ⋆ (c8 (r - 0x78#64) (sbrA t₀ + 0x4ec90#64)
    ⋆ (c8 (r - 0x70#64) (BitVec.ofNat 64 (j + 1))
    ⋆ (c8 (r - 0x68#64) (BitVec.ofNat 64 y.kx1)
    ⋆ (c8 (r - 0x60#64) (BitVec.ofNat 64 p)
    ⋆ (8 ?@ (r - 0x58#64)
    ⋆ (c8 (r - 0x50#64) (dA t₀ ch)
    ⋆ (7 ?@ (r - 0x48#64)
    ⋆ (1 ?@ (r - 0x41#64)
    ⋆ (c8 (r - 0x40#64) (arg1 t₀)
    ⋆ (4 ?@ (r - 0x38#64) ⋆ 4 ?@ (r - 0x34#64)
    ⋆ (c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ Kt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

abbrev FrGa1 (x : Args) (t₀ : MachineData) (ch : Nat) (c0 : BitVec 32) (y : Args) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x1c8#64)
    ⋆ (c8 (r - 0x1c0#64) (sbrA t₀ + 0x4c284#64)
    ⋆ (c8 (r - 0x1b8#64) (sbrA t₀ + 0x4c252#64)
    ⋆ (c8 (r - 0x1b0#64) (sbrA t₀ + 0x5e340#64)
    ⋆ (c8 (r - 0x1a8#64) (BitVec.ofNat 64 ch)
    ⋆ (c8 (r - 0x1a0#64) (sbrA t₀ + 0x4c288#64)
    ⋆ (c8 (r - 0x198#64) (sbrA t₀ + 0x4eb50#64)
    ⋆ (c8 (r - 0x190#64) (sbrA t₀ + 0x5dd40#64)
    ⋆ (c8 (r - 0x188#64) (sbrA t₀ + 0xb2#64)
    ⋆ (c8 (r - 0x180#64) (sbrA t₀ + 0x5e4c0#64)
    ⋆ (c8 (r - 0x178#64) (sbrA t₀ + 0x5f0c0#64)
    ⋆ (c8 (r - 0x170#64) (sbrA t₀ + 0x1c#64)
    ⋆ (c8 (r - 0x168#64) (sbrA t₀ + 0x150e0#64)
    ⋆ (c8 (r - 0x160#64) (sbrA t₀ + 0x5f6c4#64)
    ⋆ (c8 (r - 0x158#64) (BitVec.ofNat 64 (dsN x))
    ⋆ (c8 (r - 0x150#64) (sbrA t₀ + 0x5d340#64)
    ⋆ (c8 (r - 0x148#64) (sbrA t₀ + 0x5d540#64)
    ⋆ (c8 (r - 0x140#64) (sbrA t₀ + 0x80#64)
    ⋆ (c8 (r - 0x138#64) (arg3 t₀)
    ⋆ (c8 (r - 0x130#64) (arg4 t₀)
    ⋆ (c8 (r - 0x128#64) (sbrA t₀ + 0x601e0#64)
    ⋆ (c8 (r - 0x120#64) (sbrA t₀ + 0x5fcc0#64)
    ⋆ (c8 (r - 0x118#64) (dA t₀ ch + 0x3904#64)
    ⋆ (c8 (r - 0x110#64) (sbrA t₀ + 0x5eac0#64)
    ⋆ (c8 (r - 0x108#64) (sbrA t₀ + 0x5f6c0#64)
    ⋆ (Int.toBytes 4 (c0.toInt) =@ (r - 0x100#64)
    ⋆ (4 ?@ (r - 0xfc#64)
    ⋆ (c8 (r - 0xf8#64) (lab "sbr_qmf_window_ds")
    ⋆ (8 ?@ (r - 0xf0#64)
    ⋆ (8 ?@ (r - 0xe8#64)
    ⋆ (8 ?@ (r - 0xe0#64)
    ⋆ (c8 (r - 0xd8#64) (sbrA t₀ + 0x5d740#64)
    ⋆ (c8 (r - 0xd0#64) (sbrA t₀ + 0x5fdc0#64)
    ⋆ (c8 (r - 0xc8#64) (sbrA t₀ + 0x4c340#64)
    ⋆ (c8 (r - 0xc0#64) (sbrA t₀ + 0x4eb40#64)
    ⋆ (c8 (r - 0xb8#64) (sbrA t₀)
    ⋆ (c8 (r - 0xb0#64) (sbrA t₀ + 0x53b40#64)
    ⋆ (4 ?@ (r - 0xa8#64)
    ⋆ (Int.toBytes 4 ((BitVec.setWidth 32 (arg2 t₀)).toInt) =@ (r - 0xa4#64)
    ⋆ (c8 (r - 0xa0#64) (BitVec.ofNat 64 (0x15ac0 * ch))
    ⋆ (c8 (r - 0x98#64) (arg0 t₀)
    ⋆ (6 ?@ (r - 0x90#64)
    ⋆ (2 ?@ (r - 0x8a#64)
    ⋆ (8 ?@ (r - 0x88#64)
    ⋆ (c8 (r - 0x80#64) (BitVec.ofNat 64 (y.nlim))
    ⋆ (c8 (r - 0x78#64) (sbrA t₀ + 0x4ec90#64)
    ⋆ (8 ?@ (r - 0x70#64)
    ⋆ (8 ?@ (r - 0x68#64)
    ⋆ (8 ?@ (r - 0x60#64)
    ⋆ (8 ?@ (r - 0x58#64)
    ⋆ (c8 (r - 0x50#64) (dA t₀ ch)
    ⋆ (7 ?@ (r - 0x48#64)
    ⋆ (1 ?@ (r - 0x41#64)
    ⋆ (c8 (r - 0x40#64) (arg1 t₀)
    ⋆ (4 ?@ (r - 0x38#64) ⋆ 4 ?@ (r - 0x34#64)
    ⋆ (c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ Kt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

abbrev FrGa2 (x : Args) (t₀ : MachineData) (ch : Nat) (c0 : BitVec 32) (y : Args) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x1c8#64)
    ⋆ (c8 (r - 0x1c0#64) (sbrA t₀ + 0x4c284#64)
    ⋆ (c8 (r - 0x1b8#64) (sbrA t₀ + 0x4c252#64)
    ⋆ (c8 (r - 0x1b0#64) (sbrA t₀ + 0x5e340#64)
    ⋆ (c8 (r - 0x1a8#64) (BitVec.ofNat 64 ch)
    ⋆ (c8 (r - 0x1a0#64) (sbrA t₀ + 0x4c288#64)
    ⋆ (c8 (r - 0x198#64) (sbrA t₀ + 0x4eb50#64)
    ⋆ (c8 (r - 0x190#64) (sbrA t₀ + 0x5dd40#64)
    ⋆ (c8 (r - 0x188#64) (sbrA t₀ + 0xb2#64)
    ⋆ (c8 (r - 0x180#64) (sbrA t₀ + 0x5e4c0#64)
    ⋆ (c8 (r - 0x178#64) (sbrA t₀ + 0x5f0c0#64)
    ⋆ (c8 (r - 0x170#64) (sbrA t₀ + 0x1c#64)
    ⋆ (c8 (r - 0x168#64) (sbrA t₀ + 0x150e0#64)
    ⋆ (c8 (r - 0x160#64) (sbrA t₀ + 0x5f6c4#64)
    ⋆ (c8 (r - 0x158#64) (BitVec.ofNat 64 (dsN x))
    ⋆ (c8 (r - 0x150#64) (sbrA t₀ + 0x5d340#64)
    ⋆ (c8 (r - 0x148#64) (sbrA t₀ + 0x5d540#64)
    ⋆ (c8 (r - 0x140#64) (sbrA t₀ + 0x80#64)
    ⋆ (c8 (r - 0x138#64) (arg3 t₀)
    ⋆ (c8 (r - 0x130#64) (arg4 t₀)
    ⋆ (c8 (r - 0x128#64) (sbrA t₀ + 0x601e0#64)
    ⋆ (c8 (r - 0x120#64) (sbrA t₀ + 0x5fcc0#64)
    ⋆ (c8 (r - 0x118#64) (dA t₀ ch + 0x3904#64)
    ⋆ (c8 (r - 0x110#64) (sbrA t₀ + 0x5eac0#64)
    ⋆ (c8 (r - 0x108#64) (sbrA t₀ + 0x5f6c0#64)
    ⋆ (Int.toBytes 4 (c0.toInt) =@ (r - 0x100#64)
    ⋆ (4 ?@ (r - 0xfc#64)
    ⋆ (c8 (r - 0xf8#64) (lab "sbr_qmf_window_ds")
    ⋆ (8 ?@ (r - 0xf0#64)
    ⋆ (8 ?@ (r - 0xe8#64)
    ⋆ (8 ?@ (r - 0xe0#64)
    ⋆ (c8 (r - 0xd8#64) (sbrA t₀ + 0x5d740#64)
    ⋆ (c8 (r - 0xd0#64) (sbrA t₀ + 0x5fdc0#64)
    ⋆ (c8 (r - 0xc8#64) (sbrA t₀ + 0x4c340#64)
    ⋆ (c8 (r - 0xc0#64) (sbrA t₀ + 0x4eb40#64)
    ⋆ (c8 (r - 0xb8#64) (sbrA t₀)
    ⋆ (c8 (r - 0xb0#64) (sbrA t₀ + 0x53b40#64)
    ⋆ (4 ?@ (r - 0xa8#64)
    ⋆ (Int.toBytes 4 ((BitVec.setWidth 32 (arg2 t₀)).toInt) =@ (r - 0xa4#64)
    ⋆ (c8 (r - 0xa0#64) (BitVec.ofNat 64 (0x15ac0 * ch))
    ⋆ (c8 (r - 0x98#64) (arg0 t₀)
    ⋆ (6 ?@ (r - 0x90#64)
    ⋆ (Int.toBytes 2 (((u16 y.ftLim (0) : Nat) : Int)) =@ (r - 0x8a#64)
    ⋆ (8 ?@ (r - 0x88#64)
    ⋆ (c8 (r - 0x80#64) (BitVec.ofNat 64 (y.nlim))
    ⋆ (c8 (r - 0x78#64) (sbrA t₀ + 0x4ec90#64)
    ⋆ (8 ?@ (r - 0x70#64)
    ⋆ (8 ?@ (r - 0x68#64)
    ⋆ (8 ?@ (r - 0x60#64)
    ⋆ (8 ?@ (r - 0x58#64)
    ⋆ (c8 (r - 0x50#64) (dA t₀ ch)
    ⋆ (7 ?@ (r - 0x48#64)
    ⋆ (1 ?@ (r - 0x41#64)
    ⋆ (c8 (r - 0x40#64) (arg1 t₀)
    ⋆ (4 ?@ (r - 0x38#64) ⋆ 4 ?@ (r - 0x34#64)
    ⋆ (c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ Kt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

abbrev FrGA (x : Args) (t₀ : MachineData) (ch : Nat) (c0 : BitVec 32) (y : Args) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x1c8#64)
    ⋆ (c8 (r - 0x1c0#64) (sbrA t₀ + 0x4c284#64)
    ⋆ (c8 (r - 0x1b8#64) (sbrA t₀ + 0x4c252#64)
    ⋆ (c8 (r - 0x1b0#64) (sbrA t₀ + 0x5e340#64)
    ⋆ (c8 (r - 0x1a8#64) (BitVec.ofNat 64 ch)
    ⋆ (c8 (r - 0x1a0#64) (sbrA t₀ + 0x4c288#64)
    ⋆ (c8 (r - 0x198#64) (sbrA t₀ + 0x4eb50#64)
    ⋆ (c8 (r - 0x190#64) (sbrA t₀ + 0x5dd40#64)
    ⋆ (c8 (r - 0x188#64) (sbrA t₀ + 0xb2#64)
    ⋆ (c8 (r - 0x180#64) (sbrA t₀ + 0x5e4c0#64)
    ⋆ (c8 (r - 0x178#64) (sbrA t₀ + 0x5f0c0#64)
    ⋆ (c8 (r - 0x170#64) (sbrA t₀ + 0x1c#64)
    ⋆ (c8 (r - 0x168#64) (sbrA t₀ + 0x150e0#64)
    ⋆ (c8 (r - 0x160#64) (sbrA t₀ + 0x5f6c4#64)
    ⋆ (c8 (r - 0x158#64) (BitVec.ofNat 64 (dsN x))
    ⋆ (c8 (r - 0x150#64) (sbrA t₀ + 0x5d340#64)
    ⋆ (c8 (r - 0x148#64) (sbrA t₀ + 0x5d540#64)
    ⋆ (c8 (r - 0x140#64) (sbrA t₀ + 0x80#64)
    ⋆ (c8 (r - 0x138#64) (arg3 t₀)
    ⋆ (c8 (r - 0x130#64) (arg4 t₀)
    ⋆ (c8 (r - 0x128#64) (sbrA t₀ + 0x601e0#64)
    ⋆ (c8 (r - 0x120#64) (sbrA t₀ + 0x5fcc0#64)
    ⋆ (c8 (r - 0x118#64) (dA t₀ ch + 0x3904#64)
    ⋆ (c8 (r - 0x110#64) (sbrA t₀ + 0x5eac0#64)
    ⋆ (c8 (r - 0x108#64) (sbrA t₀ + 0x5f6c0#64)
    ⋆ (Int.toBytes 4 (c0.toInt) =@ (r - 0x100#64)
    ⋆ (4 ?@ (r - 0xfc#64)
    ⋆ (c8 (r - 0xf8#64) (lab "sbr_qmf_window_ds")
    ⋆ (8 ?@ (r - 0xf0#64)
    ⋆ (8 ?@ (r - 0xe8#64)
    ⋆ (8 ?@ (r - 0xe0#64)
    ⋆ (c8 (r - 0xd8#64) (sbrA t₀ + 0x5d740#64)
    ⋆ (c8 (r - 0xd0#64) (sbrA t₀ + 0x5fdc0#64)
    ⋆ (c8 (r - 0xc8#64) (sbrA t₀ + 0x4c340#64)
    ⋆ (c8 (r - 0xc0#64) (sbrA t₀ + 0x4eb40#64)
    ⋆ (c8 (r - 0xb8#64) (sbrA t₀)
    ⋆ (c8 (r - 0xb0#64) (sbrA t₀ + 0x53b40#64)
    ⋆ (4 ?@ (r - 0xa8#64)
    ⋆ (Int.toBytes 4 ((BitVec.setWidth 32 (arg2 t₀)).toInt) =@ (r - 0xa4#64)
    ⋆ (8 ?@ (r - 0xa0#64)
    ⋆ (c8 (r - 0x98#64) (arg0 t₀)
    ⋆ (6 ?@ (r - 0x90#64)
    ⋆ (2 ?@ (r - 0x8a#64)
    ⋆ (8 ?@ (r - 0x88#64)
    ⋆ (8 ?@ (r - 0x80#64)
    ⋆ (c8 (r - 0x78#64) (sbrA t₀ + 0x4ec90#64)
    ⋆ (8 ?@ (r - 0x70#64)
    ⋆ (8 ?@ (r - 0x68#64)
    ⋆ (8 ?@ (r - 0x60#64)
    ⋆ (8 ?@ (r - 0x58#64)
    ⋆ (c8 (r - 0x50#64) (dA t₀ ch)
    ⋆ (7 ?@ (r - 0x48#64)
    ⋆ (1 ?@ (r - 0x41#64)
    ⋆ (c8 (r - 0x40#64) (arg1 t₀)
    ⋆ (4 ?@ (r - 0x38#64) ⋆ 4 ?@ (r - 0x34#64)
    ⋆ (c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ Kt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

abbrev FrGe0 (x : Args) (t₀ : MachineData) (ch : Nat) (c0 : BitVec 32) (y : Args) (ee : Nat) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x1c8#64)
    ⋆ (c8 (r - 0x1c0#64) (sbrA t₀ + 0x4c284#64)
    ⋆ (c8 (r - 0x1b8#64) (sbrA t₀ + 0x4c252#64)
    ⋆ (c8 (r - 0x1b0#64) (sbrA t₀ + 0x5e340#64)
    ⋆ (c8 (r - 0x1a8#64) (BitVec.ofNat 64 ch)
    ⋆ (c8 (r - 0x1a0#64) (sbrA t₀ + 0x4c288#64)
    ⋆ (c8 (r - 0x198#64) (sbrA t₀ + 0x4eb50#64)
    ⋆ (c8 (r - 0x190#64) (sbrA t₀ + 0x5dd40#64)
    ⋆ (c8 (r - 0x188#64) (sbrA t₀ + 0xb2#64)
    ⋆ (c8 (r - 0x180#64) (sbrA t₀ + 0x5e4c0#64)
    ⋆ (c8 (r - 0x178#64) (sbrA t₀ + 0x5f0c0#64)
    ⋆ (c8 (r - 0x170#64) (sbrA t₀ + 0x1c#64)
    ⋆ (c8 (r - 0x168#64) (sbrA t₀ + 0x150e0#64)
    ⋆ (c8 (r - 0x160#64) (sbrA t₀ + 0x5f6c4#64)
    ⋆ (c8 (r - 0x158#64) (BitVec.ofNat 64 (dsN x))
    ⋆ (c8 (r - 0x150#64) (sbrA t₀ + 0x5d340#64)
    ⋆ (c8 (r - 0x148#64) (sbrA t₀ + 0x5d540#64)
    ⋆ (c8 (r - 0x140#64) (sbrA t₀ + 0x80#64)
    ⋆ (c8 (r - 0x138#64) (arg3 t₀)
    ⋆ (c8 (r - 0x130#64) (arg4 t₀)
    ⋆ (c8 (r - 0x128#64) (sbrA t₀ + 0x601e0#64)
    ⋆ (c8 (r - 0x120#64) (sbrA t₀ + 0x5fcc0#64)
    ⋆ (c8 (r - 0x118#64) (dA t₀ ch + 0x3904#64)
    ⋆ (c8 (r - 0x110#64) (sbrA t₀ + 0x5eac0#64)
    ⋆ (c8 (r - 0x108#64) (sbrA t₀ + 0x5f6c0#64)
    ⋆ (Int.toBytes 4 (c0.toInt) =@ (r - 0x100#64)
    ⋆ (Int.toBytes 4 ((-(BitVec.ofNat 32 y.kx1)).toInt) =@ (r - 0xfc#64)
    ⋆ (c8 (r - 0xf8#64) (lab "sbr_qmf_window_ds")
    ⋆ (8 ?@ (r - 0xf0#64)
    ⋆ (8 ?@ (r - 0xe8#64)
    ⋆ (8 ?@ (r - 0xe0#64)
    ⋆ (c8 (r - 0xd8#64) (sbrA t₀ + 0x5d740#64)
    ⋆ (c8 (r - 0xd0#64) (sbrA t₀ + 0x5fdc0#64)
    ⋆ (c8 (r - 0xc8#64) (sbrA t₀ + 0x4c340#64)
    ⋆ (c8 (r - 0xc0#64) (sbrA t₀ + 0x4eb40#64)
    ⋆ (c8 (r - 0xb8#64) (sbrA t₀)
    ⋆ (c8 (r - 0xb0#64) (sbrA t₀ + 0x53b40#64)
    ⋆ (4 ?@ (r - 0xa8#64)
    ⋆ (Int.toBytes 4 ((BitVec.setWidth 32 (arg2 t₀)).toInt) =@ (r - 0xa4#64)
    ⋆ (c8 (r - 0xa0#64) (dA t₀ ch + 0x15030#64 + BitVec.ofNat 64 (0x30 * (ee + 1)))
    ⋆ (c8 (r - 0x98#64) (arg0 t₀)
    ⋆ (6 ?@ (r - 0x90#64)
    ⋆ (Int.toBytes 2 (((u16 y.ftLim (0) : Nat) : Int)) =@ (r - 0x8a#64)
    ⋆ (8 ?@ (r - 0x88#64)
    ⋆ (c8 (r - 0x80#64) (BitVec.ofNat 64 (y.nlim))
    ⋆ (c8 (r - 0x78#64) (sbrA t₀ + 0x4ec90#64)
    ⋆ (8 ?@ (r - 0x70#64)
    ⋆ (8 ?@ (r - 0x68#64)
    ⋆ (8 ?@ (r - 0x60#64)
    ⋆ (8 ?@ (r - 0x58#64)
    ⋆ (c8 (r - 0x50#64) (dA t₀ ch)
    ⋆ (7 ?@ (r - 0x48#64)
    ⋆ (1 ?@ (r - 0x41#64)
    ⋆ (c8 (r - 0x40#64) (arg1 t₀)
    ⋆ (4 ?@ (r - 0x38#64) ⋆ 4 ?@ (r - 0x34#64)
    ⋆ (c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ Kt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

abbrev FrGe1 (x : Args) (t₀ : MachineData) (ch : Nat) (c0 : BitVec 32) (y : Args) (ee : Nat) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x1c8#64)
    ⋆ (c8 (r - 0x1c0#64) (sbrA t₀ + 0x4c284#64)
    ⋆ (c8 (r - 0x1b8#64) (sbrA t₀ + 0x4c252#64)
    ⋆ (c8 (r - 0x1b0#64) (sbrA t₀ + 0x5e340#64)
    ⋆ (c8 (r - 0x1a8#64) (BitVec.ofNat 64 ch)
    ⋆ (c8 (r - 0x1a0#64) (sbrA t₀ + 0x4c288#64)
    ⋆ (c8 (r - 0x198#64) (sbrA t₀ + 0x4eb50#64)
    ⋆ (c8 (r - 0x190#64) (sbrA t₀ + 0x5dd40#64)
    ⋆ (c8 (r - 0x188#64) (sbrA t₀ + 0xb2#64)
    ⋆ (c8 (r - 0x180#64) (sbrA t₀ + 0x5e4c0#64)
    ⋆ (c8 (r - 0x178#64) (sbrA t₀ + 0x5f0c0#64)
    ⋆ (c8 (r - 0x170#64) (sbrA t₀ + 0x1c#64)
    ⋆ (c8 (r - 0x168#64) (sbrA t₀ + 0x150e0#64)
    ⋆ (c8 (r - 0x160#64) (sbrA t₀ + 0x5f6c4#64)
    ⋆ (c8 (r - 0x158#64) (BitVec.ofNat 64 (dsN x))
    ⋆ (c8 (r - 0x150#64) (sbrA t₀ + 0x5d340#64)
    ⋆ (c8 (r - 0x148#64) (sbrA t₀ + 0x5d540#64)
    ⋆ (c8 (r - 0x140#64) (sbrA t₀ + 0x80#64)
    ⋆ (c8 (r - 0x138#64) (arg3 t₀)
    ⋆ (c8 (r - 0x130#64) (arg4 t₀)
    ⋆ (c8 (r - 0x128#64) (sbrA t₀ + 0x601e0#64)
    ⋆ (c8 (r - 0x120#64) (sbrA t₀ + 0x5fcc0#64)
    ⋆ (c8 (r - 0x118#64) (dA t₀ ch + 0x3904#64)
    ⋆ (c8 (r - 0x110#64) (sbrA t₀ + 0x5eac0#64)
    ⋆ (c8 (r - 0x108#64) (sbrA t₀ + 0x5f6c0#64)
    ⋆ (Int.toBytes 4 (c0.toInt) =@ (r - 0x100#64)
    ⋆ (Int.toBytes 4 ((-(BitVec.ofNat 32 y.kx1)).toInt) =@ (r - 0xfc#64)
    ⋆ (c8 (r - 0xf8#64) (lab "sbr_qmf_window_ds")
    ⋆ (8 ?@ (r - 0xf0#64)
    ⋆ (8 ?@ (r - 0xe8#64)
    ⋆ (8 ?@ (r - 0xe0#64)
    ⋆ (c8 (r - 0xd8#64) (sbrA t₀ + 0x5d740#64)
    ⋆ (c8 (r - 0xd0#64) (sbrA t₀ + 0x5fdc0#64)
    ⋆ (c8 (r - 0xc8#64) (sbrA t₀ + 0x4c340#64)
    ⋆ (c8 (r - 0xc0#64) (sbrA t₀ + 0x4eb40#64)
    ⋆ (c8 (r - 0xb8#64) (sbrA t₀)
    ⋆ (c8 (r - 0xb0#64) (sbrA t₀ + 0x53b40#64)
    ⋆ (4 ?@ (r - 0xa8#64)
    ⋆ (Int.toBytes 4 ((BitVec.setWidth 32 (arg2 t₀)).toInt) =@ (r - 0xa4#64)
    ⋆ (c8 (r - 0xa0#64) (dA t₀ ch + 0x15030#64 + BitVec.ofNat 64 (0x30 * (ee + 1)))
    ⋆ (c8 (r - 0x98#64) (arg0 t₀)
    ⋆ (6 ?@ (r - 0x90#64)
    ⋆ (Int.toBytes 2 (((u16 y.ftLim (0) : Nat) : Int)) =@ (r - 0x8a#64)
    ⋆ (8 ?@ (r - 0x88#64)
    ⋆ (c8 (r - 0x80#64) (BitVec.ofNat 64 (y.nlim))
    ⋆ (c8 (r - 0x78#64) (sbrA t₀ + 0x4ec90#64)
    ⋆ (8 ?@ (r - 0x70#64)
    ⋆ (c8 (r - 0x68#64) (sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee))
    ⋆ (8 ?@ (r - 0x60#64)
    ⋆ (8 ?@ (r - 0x58#64)
    ⋆ (c8 (r - 0x50#64) (dA t₀ ch)
    ⋆ (7 ?@ (r - 0x48#64)
    ⋆ (1 ?@ (r - 0x41#64)
    ⋆ (c8 (r - 0x40#64) (arg1 t₀)
    ⋆ (4 ?@ (r - 0x38#64) ⋆ 4 ?@ (r - 0x34#64)
    ⋆ (c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ Kt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

abbrev FrGe2 (x : Args) (t₀ : MachineData) (ch : Nat) (c0 : BitVec 32) (y : Args) (ee : Nat) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x1c8#64)
    ⋆ (c8 (r - 0x1c0#64) (sbrA t₀ + 0x4c284#64)
    ⋆ (c8 (r - 0x1b8#64) (sbrA t₀ + 0x4c252#64)
    ⋆ (c8 (r - 0x1b0#64) (sbrA t₀ + 0x5e340#64)
    ⋆ (c8 (r - 0x1a8#64) (BitVec.ofNat 64 ch)
    ⋆ (c8 (r - 0x1a0#64) (sbrA t₀ + 0x4c288#64)
    ⋆ (c8 (r - 0x198#64) (sbrA t₀ + 0x4eb50#64)
    ⋆ (c8 (r - 0x190#64) (sbrA t₀ + 0x5dd40#64)
    ⋆ (c8 (r - 0x188#64) (sbrA t₀ + 0xb2#64)
    ⋆ (c8 (r - 0x180#64) (sbrA t₀ + 0x5e4c0#64)
    ⋆ (c8 (r - 0x178#64) (sbrA t₀ + 0x5f0c0#64)
    ⋆ (c8 (r - 0x170#64) (sbrA t₀ + 0x1c#64)
    ⋆ (c8 (r - 0x168#64) (sbrA t₀ + 0x150e0#64)
    ⋆ (c8 (r - 0x160#64) (sbrA t₀ + 0x5f6c4#64)
    ⋆ (c8 (r - 0x158#64) (BitVec.ofNat 64 (dsN x))
    ⋆ (c8 (r - 0x150#64) (sbrA t₀ + 0x5d340#64)
    ⋆ (c8 (r - 0x148#64) (sbrA t₀ + 0x5d540#64)
    ⋆ (c8 (r - 0x140#64) (sbrA t₀ + 0x80#64)
    ⋆ (c8 (r - 0x138#64) (arg3 t₀)
    ⋆ (c8 (r - 0x130#64) (arg4 t₀)
    ⋆ (c8 (r - 0x128#64) (sbrA t₀ + 0x601e0#64)
    ⋆ (c8 (r - 0x120#64) (sbrA t₀ + 0x5fcc0#64)
    ⋆ (c8 (r - 0x118#64) (dA t₀ ch + 0x3904#64)
    ⋆ (c8 (r - 0x110#64) (sbrA t₀ + 0x5eac0#64)
    ⋆ (c8 (r - 0x108#64) (sbrA t₀ + 0x5f6c0#64)
    ⋆ (Int.toBytes 4 (c0.toInt) =@ (r - 0x100#64)
    ⋆ (Int.toBytes 4 ((-(BitVec.ofNat 32 y.kx1)).toInt) =@ (r - 0xfc#64)
    ⋆ (c8 (r - 0xf8#64) (lab "sbr_qmf_window_ds")
    ⋆ (c8 (r - 0xf0#64) (sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee))
    ⋆ (8 ?@ (r - 0xe8#64)
    ⋆ (8 ?@ (r - 0xe0#64)
    ⋆ (c8 (r - 0xd8#64) (sbrA t₀ + 0x5d740#64)
    ⋆ (c8 (r - 0xd0#64) (sbrA t₀ + 0x5fdc0#64)
    ⋆ (c8 (r - 0xc8#64) (sbrA t₀ + 0x4c340#64)
    ⋆ (c8 (r - 0xc0#64) (sbrA t₀ + 0x4eb40#64)
    ⋆ (c8 (r - 0xb8#64) (sbrA t₀)
    ⋆ (c8 (r - 0xb0#64) (sbrA t₀ + 0x53b40#64)
    ⋆ (4 ?@ (r - 0xa8#64)
    ⋆ (Int.toBytes 4 ((BitVec.setWidth 32 (arg2 t₀)).toInt) =@ (r - 0xa4#64)
    ⋆ (c8 (r - 0xa0#64) (dA t₀ ch + 0x15030#64 + BitVec.ofNat 64 (0x30 * (ee + 1)))
    ⋆ (c8 (r - 0x98#64) (arg0 t₀)
    ⋆ (6 ?@ (r - 0x90#64)
    ⋆ (Int.toBytes 2 (((u16 y.ftLim (0) : Nat) : Int)) =@ (r - 0x8a#64)
    ⋆ (8 ?@ (r - 0x88#64)
    ⋆ (c8 (r - 0x80#64) (BitVec.ofNat 64 (y.nlim))
    ⋆ (c8 (r - 0x78#64) (sbrA t₀ + 0x4ec90#64)
    ⋆ (8 ?@ (r - 0x70#64)
    ⋆ (c8 (r - 0x68#64) (sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee))
    ⋆ (8 ?@ (r - 0x60#64)
    ⋆ (8 ?@ (r - 0x58#64)
    ⋆ (c8 (r - 0x50#64) (dA t₀ ch)
    ⋆ (7 ?@ (r - 0x48#64)
    ⋆ (1 ?@ (r - 0x41#64)
    ⋆ (c8 (r - 0x40#64) (arg1 t₀)
    ⋆ (4 ?@ (r - 0x38#64) ⋆ 4 ?@ (r - 0x34#64)
    ⋆ (c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ Kt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

abbrev FrGe3 (x : Args) (t₀ : MachineData) (ch : Nat) (c0 : BitVec 32) (y : Args) (ee : Nat) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x1c8#64)
    ⋆ (c8 (r - 0x1c0#64) (sbrA t₀ + 0x4c284#64)
    ⋆ (c8 (r - 0x1b8#64) (sbrA t₀ + 0x4c252#64)
    ⋆ (c8 (r - 0x1b0#64) (sbrA t₀ + 0x5e340#64)
    ⋆ (c8 (r - 0x1a8#64) (BitVec.ofNat 64 ch)
    ⋆ (c8 (r - 0x1a0#64) (sbrA t₀ + 0x4c288#64)
    ⋆ (c8 (r - 0x198#64) (sbrA t₀ + 0x4eb50#64)
    ⋆ (c8 (r - 0x190#64) (sbrA t₀ + 0x5dd40#64)
    ⋆ (c8 (r - 0x188#64) (sbrA t₀ + 0xb2#64)
    ⋆ (c8 (r - 0x180#64) (sbrA t₀ + 0x5e4c0#64)
    ⋆ (c8 (r - 0x178#64) (sbrA t₀ + 0x5f0c0#64)
    ⋆ (c8 (r - 0x170#64) (sbrA t₀ + 0x1c#64)
    ⋆ (c8 (r - 0x168#64) (sbrA t₀ + 0x150e0#64)
    ⋆ (c8 (r - 0x160#64) (sbrA t₀ + 0x5f6c4#64)
    ⋆ (c8 (r - 0x158#64) (BitVec.ofNat 64 (dsN x))
    ⋆ (c8 (r - 0x150#64) (sbrA t₀ + 0x5d340#64)
    ⋆ (c8 (r - 0x148#64) (sbrA t₀ + 0x5d540#64)
    ⋆ (c8 (r - 0x140#64) (sbrA t₀ + 0x80#64)
    ⋆ (c8 (r - 0x138#64) (arg3 t₀)
    ⋆ (c8 (r - 0x130#64) (arg4 t₀)
    ⋆ (c8 (r - 0x128#64) (sbrA t₀ + 0x601e0#64)
    ⋆ (c8 (r - 0x120#64) (sbrA t₀ + 0x5fcc0#64)
    ⋆ (c8 (r - 0x118#64) (dA t₀ ch + 0x3904#64)
    ⋆ (c8 (r - 0x110#64) (sbrA t₀ + 0x5eac0#64)
    ⋆ (c8 (r - 0x108#64) (sbrA t₀ + 0x5f6c0#64)
    ⋆ (Int.toBytes 4 (c0.toInt) =@ (r - 0x100#64)
    ⋆ (Int.toBytes 4 ((-(BitVec.ofNat 32 y.kx1)).toInt) =@ (r - 0xfc#64)
    ⋆ (c8 (r - 0xf8#64) (lab "sbr_qmf_window_ds")
    ⋆ (c8 (r - 0xf0#64) (sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee))
    ⋆ (c8 (r - 0xe8#64) (sbrA t₀ + 0x5f0c0#64 + BitVec.ofNat 64 (0xc0 * ee))
    ⋆ (8 ?@ (r - 0xe0#64)
    ⋆ (c8 (r - 0xd8#64) (sbrA t₀ + 0x5d740#64)
    ⋆ (c8 (r - 0xd0#64) (sbrA t₀ + 0x5fdc0#64)
    ⋆ (c8 (r - 0xc8#64) (sbrA t₀ + 0x4c340#64)
    ⋆ (c8 (r - 0xc0#64) (sbrA t₀ + 0x4eb40#64)
    ⋆ (c8 (r - 0xb8#64) (sbrA t₀)
    ⋆ (c8 (r - 0xb0#64) (sbrA t₀ + 0x53b40#64)
    ⋆ (4 ?@ (r - 0xa8#64)
    ⋆ (Int.toBytes 4 ((BitVec.setWidth 32 (arg2 t₀)).toInt) =@ (r - 0xa4#64)
    ⋆ (c8 (r - 0xa0#64) (dA t₀ ch + 0x15030#64 + BitVec.ofNat 64 (0x30 * (ee + 1)))
    ⋆ (c8 (r - 0x98#64) (arg0 t₀)
    ⋆ (6 ?@ (r - 0x90#64)
    ⋆ (Int.toBytes 2 (((u16 y.ftLim (0) : Nat) : Int)) =@ (r - 0x8a#64)
    ⋆ (8 ?@ (r - 0x88#64)
    ⋆ (c8 (r - 0x80#64) (BitVec.ofNat 64 (y.nlim))
    ⋆ (c8 (r - 0x78#64) (sbrA t₀ + 0x4ec90#64)
    ⋆ (8 ?@ (r - 0x70#64)
    ⋆ (c8 (r - 0x68#64) (sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee))
    ⋆ (8 ?@ (r - 0x60#64)
    ⋆ (8 ?@ (r - 0x58#64)
    ⋆ (c8 (r - 0x50#64) (dA t₀ ch)
    ⋆ (7 ?@ (r - 0x48#64)
    ⋆ (1 ?@ (r - 0x41#64)
    ⋆ (c8 (r - 0x40#64) (arg1 t₀)
    ⋆ (4 ?@ (r - 0x38#64) ⋆ 4 ?@ (r - 0x34#64)
    ⋆ (c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ Kt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

abbrev FrGe4 (x : Args) (t₀ : MachineData) (ch : Nat) (c0 : BitVec 32) (y : Args) (ee : Nat) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x1c8#64)
    ⋆ (c8 (r - 0x1c0#64) (sbrA t₀ + 0x4c284#64)
    ⋆ (c8 (r - 0x1b8#64) (sbrA t₀ + 0x4c252#64)
    ⋆ (c8 (r - 0x1b0#64) (sbrA t₀ + 0x5e340#64)
    ⋆ (c8 (r - 0x1a8#64) (BitVec.ofNat 64 ch)
    ⋆ (c8 (r - 0x1a0#64) (sbrA t₀ + 0x4c288#64)
    ⋆ (c8 (r - 0x198#64) (sbrA t₀ + 0x4eb50#64)
    ⋆ (c8 (r - 0x190#64) (sbrA t₀ + 0x5dd40#64)
    ⋆ (c8 (r - 0x188#64) (sbrA t₀ + 0xb2#64)
    ⋆ (c8 (r - 0x180#64) (sbrA t₀ + 0x5e4c0#64)
    ⋆ (c8 (r - 0x178#64) (sbrA t₀ + 0x5f0c0#64)
    ⋆ (c8 (r - 0x170#64) (sbrA t₀ + 0x1c#64)
    ⋆ (c8 (r - 0x168#64) (sbrA t₀ + 0x150e0#64)
    ⋆ (c8 (r - 0x160#64) (sbrA t₀ + 0x5f6c4#64)
    ⋆ (c8 (r - 0x158#64) (BitVec.ofNat 64 (dsN x))
    ⋆ (c8 (r - 0x150#64) (sbrA t₀ + 0x5d340#64)
    ⋆ (c8 (r - 0x148#64) (sbrA t₀ + 0x5d540#64)
    ⋆ (c8 (r - 0x140#64) (sbrA t₀ + 0x80#64)
    ⋆ (c8 (r - 0x138#64) (arg3 t₀)
    ⋆ (c8 (r - 0x130#64) (arg4 t₀)
    ⋆ (c8 (r - 0x128#64) (sbrA t₀ + 0x601e0#64)
    ⋆ (c8 (r - 0x120#64) (sbrA t₀ + 0x5fcc0#64)
    ⋆ (c8 (r - 0x118#64) (dA t₀ ch + 0x3904#64)
    ⋆ (c8 (r - 0x110#64) (sbrA t₀ + 0x5eac0#64)
    ⋆ (c8 (r - 0x108#64) (sbrA t₀ + 0x5f6c0#64)
    ⋆ (Int.toBytes 4 (c0.toInt) =@ (r - 0x100#64)
    ⋆ (Int.toBytes 4 ((-(BitVec.ofNat 32 y.kx1)).toInt) =@ (r - 0xfc#64)
    ⋆ (c8 (r - 0xf8#64) (lab "sbr_qmf_window_ds")
    ⋆ (c8 (r - 0xf0#64) (sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee))
    ⋆ (c8 (r - 0xe8#64) (sbrA t₀ + 0x5f0c0#64 + BitVec.ofNat 64 (0xc0 * ee))
    ⋆ (c8 (r - 0xe0#64) (sbrA t₀ + 0x5e4c0#64 + BitVec.ofNat 64 (0xc0 * ee))
    ⋆ (c8 (r - 0xd8#64) (sbrA t₀ + 0x5d740#64)
    ⋆ (c8 (r - 0xd0#64) (sbrA t₀ + 0x5fdc0#64)
    ⋆ (c8 (r - 0xc8#64) (sbrA t₀ + 0x4c340#64)
    ⋆ (c8 (r - 0xc0#64) (sbrA t₀ + 0x4eb40#64)
    ⋆ (c8 (r - 0xb8#64) (sbrA t₀)
    ⋆ (c8 (r - 0xb0#64) (sbrA t₀ + 0x53b40#64)
    ⋆ (4 ?@ (r - 0xa8#64)
    ⋆ (Int.toBytes 4 ((BitVec.setWidth 32 (arg2 t₀)).toInt) =@ (r - 0xa4#64)
    ⋆ (c8 (r - 0xa0#64) (dA t₀ ch + 0x15030#64 + BitVec.ofNat 64 (0x30 * (ee + 1)))
    ⋆ (c8 (r - 0x98#64) (arg0 t₀)
    ⋆ (6 ?@ (r - 0x90#64)
    ⋆ (Int.toBytes 2 (((u16 y.ftLim (0) : Nat) : Int)) =@ (r - 0x8a#64)
    ⋆ (8 ?@ (r - 0x88#64)
    ⋆ (c8 (r - 0x80#64) (BitVec.ofNat 64 (y.nlim))
    ⋆ (c8 (r - 0x78#64) (sbrA t₀ + 0x4ec90#64)
    ⋆ (8 ?@ (r - 0x70#64)
    ⋆ (c8 (r - 0x68#64) (sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee))
    ⋆ (8 ?@ (r - 0x60#64)
    ⋆ (8 ?@ (r - 0x58#64)
    ⋆ (c8 (r - 0x50#64) (dA t₀ ch)
    ⋆ (7 ?@ (r - 0x48#64)
    ⋆ (1 ?@ (r - 0x41#64)
    ⋆ (c8 (r - 0x40#64) (arg1 t₀)
    ⋆ (4 ?@ (r - 0x38#64) ⋆ 4 ?@ (r - 0x34#64)
    ⋆ (c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ Kt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

abbrev FrGe5 (x : Args) (t₀ : MachineData) (ch : Nat) (c0 : BitVec 32) (y : Args) (ee : Nat) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x1c8#64)
    ⋆ (c8 (r - 0x1c0#64) (sbrA t₀ + 0x4c284#64)
    ⋆ (c8 (r - 0x1b8#64) (sbrA t₀ + 0x4c252#64)
    ⋆ (c8 (r - 0x1b0#64) (sbrA t₀ + 0x5e340#64)
    ⋆ (c8 (r - 0x1a8#64) (BitVec.ofNat 64 ch)
    ⋆ (c8 (r - 0x1a0#64) (sbrA t₀ + 0x4c288#64)
    ⋆ (c8 (r - 0x198#64) (sbrA t₀ + 0x4eb50#64)
    ⋆ (c8 (r - 0x190#64) (sbrA t₀ + 0x5dd40#64)
    ⋆ (c8 (r - 0x188#64) (sbrA t₀ + 0xb2#64)
    ⋆ (c8 (r - 0x180#64) (sbrA t₀ + 0x5e4c0#64)
    ⋆ (c8 (r - 0x178#64) (sbrA t₀ + 0x5f0c0#64)
    ⋆ (c8 (r - 0x170#64) (sbrA t₀ + 0x1c#64)
    ⋆ (c8 (r - 0x168#64) (sbrA t₀ + 0x150e0#64)
    ⋆ (c8 (r - 0x160#64) (sbrA t₀ + 0x5f6c4#64)
    ⋆ (c8 (r - 0x158#64) (BitVec.ofNat 64 (dsN x))
    ⋆ (c8 (r - 0x150#64) (sbrA t₀ + 0x5d340#64)
    ⋆ (c8 (r - 0x148#64) (sbrA t₀ + 0x5d540#64)
    ⋆ (c8 (r - 0x140#64) (sbrA t₀ + 0x80#64)
    ⋆ (c8 (r - 0x138#64) (arg3 t₀)
    ⋆ (c8 (r - 0x130#64) (arg4 t₀)
    ⋆ (c8 (r - 0x128#64) (sbrA t₀ + 0x601e0#64)
    ⋆ (c8 (r - 0x120#64) (sbrA t₀ + 0x5fcc0#64)
    ⋆ (c8 (r - 0x118#64) (dA t₀ ch + 0x3904#64)
    ⋆ (c8 (r - 0x110#64) (sbrA t₀ + 0x5eac0#64)
    ⋆ (c8 (r - 0x108#64) (sbrA t₀ + 0x5f6c0#64)
    ⋆ (Int.toBytes 4 (c0.toInt) =@ (r - 0x100#64)
    ⋆ (Int.toBytes 4 ((-(BitVec.ofNat 32 y.kx1)).toInt) =@ (r - 0xfc#64)
    ⋆ (c8 (r - 0xf8#64) (lab "sbr_qmf_window_ds")
    ⋆ (c8 (r - 0xf0#64) (sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee))
    ⋆ (c8 (r - 0xe8#64) (sbrA t₀ + 0x5f0c0#64 + BitVec.ofNat 64 (0xc0 * ee))
    ⋆ (c8 (r - 0xe0#64) (sbrA t₀ + 0x5e4c0#64 + BitVec.ofNat 64 (0xc0 * ee))
    ⋆ (c8 (r - 0xd8#64) (sbrA t₀ + 0x5d740#64)
    ⋆ (c8 (r - 0xd0#64) (sbrA t₀ + 0x5fdc0#64)
    ⋆ (c8 (r - 0xc8#64) (sbrA t₀ + 0x4c340#64)
    ⋆ (c8 (r - 0xc0#64) (sbrA t₀ + 0x4eb40#64)
    ⋆ (c8 (r - 0xb8#64) (sbrA t₀)
    ⋆ (c8 (r - 0xb0#64) (sbrA t₀ + 0x53b40#64)
    ⋆ (4 ?@ (r - 0xa8#64)
    ⋆ (Int.toBytes 4 ((BitVec.setWidth 32 (arg2 t₀)).toInt) =@ (r - 0xa4#64)
    ⋆ (c8 (r - 0xa0#64) (dA t₀ ch + 0x15030#64 + BitVec.ofNat 64 (0x30 * (ee + 1)))
    ⋆ (c8 (r - 0x98#64) (arg0 t₀)
    ⋆ (6 ?@ (r - 0x90#64)
    ⋆ (Int.toBytes 2 (((u16 y.ftLim (0) : Nat) : Int)) =@ (r - 0x8a#64)
    ⋆ (c8 (r - 0x88#64) (sbrA t₀ + 0x5f6c0#64 + BitVec.ofNat 64 (0xc0 * ee))
    ⋆ (c8 (r - 0x80#64) (BitVec.ofNat 64 (y.nlim))
    ⋆ (c8 (r - 0x78#64) (sbrA t₀ + 0x4ec90#64)
    ⋆ (8 ?@ (r - 0x70#64)
    ⋆ (c8 (r - 0x68#64) (sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee))
    ⋆ (8 ?@ (r - 0x60#64)
    ⋆ (8 ?@ (r - 0x58#64)
    ⋆ (c8 (r - 0x50#64) (dA t₀ ch)
    ⋆ (7 ?@ (r - 0x48#64)
    ⋆ (1 ?@ (r - 0x41#64)
    ⋆ (c8 (r - 0x40#64) (arg1 t₀)
    ⋆ (4 ?@ (r - 0x38#64) ⋆ 4 ?@ (r - 0x34#64)
    ⋆ (c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ Kt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

abbrev FrGk (x : Args) (t₀ : MachineData) (ch : Nat) (c0 : BitVec 32) (y : Args) (ee : Nat) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x1c8#64)
    ⋆ (c8 (r - 0x1c0#64) (sbrA t₀ + 0x4c284#64)
    ⋆ (c8 (r - 0x1b8#64) (sbrA t₀ + 0x4c252#64)
    ⋆ (c8 (r - 0x1b0#64) (sbrA t₀ + 0x5e340#64)
    ⋆ (c8 (r - 0x1a8#64) (BitVec.ofNat 64 ch)
    ⋆ (c8 (r - 0x1a0#64) (sbrA t₀ + 0x4c288#64)
    ⋆ (c8 (r - 0x198#64) (sbrA t₀ + 0x4eb50#64)
    ⋆ (c8 (r - 0x190#64) (sbrA t₀ + 0x5dd40#64)
    ⋆ (c8 (r - 0x188#64) (sbrA t₀ + 0xb2#64)
    ⋆ (c8 (r - 0x180#64) (sbrA t₀ + 0x5e4c0#64)
    ⋆ (c8 (r - 0x178#64) (sbrA t₀ + 0x5f0c0#64)
    ⋆ (c8 (r - 0x170#64) (sbrA t₀ + 0x1c#64)
    ⋆ (c8 (r - 0x168#64) (sbrA t₀ + 0x150e0#64)
    ⋆ (c8 (r - 0x160#64) (sbrA t₀ + 0x5f6c4#64)
    ⋆ (c8 (r - 0x158#64) (BitVec.ofNat 64 (dsN x))
    ⋆ (c8 (r - 0x150#64) (sbrA t₀ + 0x5d340#64)
    ⋆ (c8 (r - 0x148#64) (sbrA t₀ + 0x5d540#64)
    ⋆ (c8 (r - 0x140#64) (sbrA t₀ + 0x80#64)
    ⋆ (c8 (r - 0x138#64) (arg3 t₀)
    ⋆ (c8 (r - 0x130#64) (arg4 t₀)
    ⋆ (c8 (r - 0x128#64) (sbrA t₀ + 0x601e0#64)
    ⋆ (c8 (r - 0x120#64) (sbrA t₀ + 0x5fcc0#64)
    ⋆ (c8 (r - 0x118#64) (dA t₀ ch + 0x3904#64)
    ⋆ (c8 (r - 0x110#64) (sbrA t₀ + 0x5eac0#64)
    ⋆ (c8 (r - 0x108#64) (sbrA t₀ + 0x5f6c0#64)
    ⋆ (Int.toBytes 4 (c0.toInt) =@ (r - 0x100#64)
    ⋆ (Int.toBytes 4 ((-(BitVec.ofNat 32 y.kx1)).toInt) =@ (r - 0xfc#64)
    ⋆ (c8 (r - 0xf8#64) (lab "sbr_qmf_window_ds")
    ⋆ (c8 (r - 0xf0#64) (sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee))
    ⋆ (c8 (r - 0xe8#64) (sbrA t₀ + 0x5f0c0#64 + BitVec.ofNat 64 (0xc0 * ee))
    ⋆ (c8 (r - 0xe0#64) (sbrA t₀ + 0x5e4c0#64 + BitVec.ofNat 64 (0xc0 * ee))
    ⋆ (c8 (r - 0xd8#64) (sbrA t₀ + 0x5d740#64)
    ⋆ (c8 (r - 0xd0#64) (sbrA t₀ + 0x5fdc0#64)
    ⋆ (c8 (r - 0xc8#64) (sbrA t₀ + 0x4c340#64)
    ⋆ (c8 (r - 0xc0#64) (sbrA t₀ + 0x4eb40#64)
    ⋆ (c8 (r - 0xb8#64) (sbrA t₀)
    ⋆ (c8 (r - 0xb0#64) (sbrA t₀ + 0x53b40#64)
    ⋆ (4 ?@ (r - 0xa8#64)
    ⋆ (Int.toBytes 4 ((BitVec.setWidth 32 (arg2 t₀)).toInt) =@ (r - 0xa4#64)
    ⋆ (c8 (r - 0xa0#64) (dA t₀ ch + 0x15030#64 + BitVec.ofNat 64 (0x30 * (ee + 1)))
    ⋆ (c8 (r - 0x98#64) (arg0 t₀)
    ⋆ (6 ?@ (r - 0x90#64)
    ⋆ (Int.toBytes 2 (((u16 y.ftLim (0) : Nat) : Int)) =@ (r - 0x8a#64)
    ⋆ (c8 (r - 0x88#64) (sbrA t₀ + 0x5f6c0#64 + BitVec.ofNat 64 (0xc0 * ee))
    ⋆ (c8 (r - 0x80#64) (BitVec.ofNat 64 (y.nlim))
    ⋆ (c8 (r - 0x78#64) (sbrA t₀ + 0x4ec90#64)
    ⋆ (8 ?@ (r - 0x70#64)
    ⋆ (c8 (r - 0x68#64) (sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee))
    ⋆ (c8 (r - 0x60#64) (BitVec.ofNat 64 (ee))
    ⋆ (8 ?@ (r - 0x58#64)
    ⋆ (c8 (r - 0x50#64) (dA t₀ ch)
    ⋆ (7 ?@ (r - 0x48#64)
    ⋆ (1 ?@ (r - 0x41#64)
    ⋆ (c8 (r - 0x40#64) (arg1 t₀)
    ⋆ (4 ?@ (r - 0x38#64) ⋆ 4 ?@ (r - 0x34#64)
    ⋆ (c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ Kt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

abbrev FrGb (x : Args) (t₀ : MachineData) (ch : Nat) (c0 : BitVec 32) (y : Args) (ee kk : Nat) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x1c8#64)
    ⋆ (c8 (r - 0x1c0#64) (sbrA t₀ + 0x4c284#64)
    ⋆ (c8 (r - 0x1b8#64) (sbrA t₀ + 0x4c252#64)
    ⋆ (c8 (r - 0x1b0#64) (sbrA t₀ + 0x5e340#64)
    ⋆ (c8 (r - 0x1a8#64) (BitVec.ofNat 64 ch)
    ⋆ (c8 (r - 0x1a0#64) (sbrA t₀ + 0x4c288#64)
    ⋆ (c8 (r - 0x198#64) (sbrA t₀ + 0x4eb50#64)
    ⋆ (c8 (r - 0x190#64) (sbrA t₀ + 0x5dd40#64)
    ⋆ (c8 (r - 0x188#64) (sbrA t₀ + 0xb2#64)
    ⋆ (c8 (r - 0x180#64) (sbrA t₀ + 0x5e4c0#64)
    ⋆ (c8 (r - 0x178#64) (sbrA t₀ + 0x5f0c0#64)
    ⋆ (c8 (r - 0x170#64) (sbrA t₀ + 0x1c#64)
    ⋆ (c8 (r - 0x168#64) (sbrA t₀ + 0x150e0#64)
    ⋆ (c8 (r - 0x160#64) (sbrA t₀ + 0x5f6c4#64)
    ⋆ (c8 (r - 0x158#64) (BitVec.ofNat 64 (dsN x))
    ⋆ (c8 (r - 0x150#64) (sbrA t₀ + 0x5d340#64)
    ⋆ (c8 (r - 0x148#64) (sbrA t₀ + 0x5d540#64)
    ⋆ (c8 (r - 0x140#64) (sbrA t₀ + 0x80#64)
    ⋆ (c8 (r - 0x138#64) (arg3 t₀)
    ⋆ (c8 (r - 0x130#64) (arg4 t₀)
    ⋆ (c8 (r - 0x128#64) (sbrA t₀ + 0x601e0#64)
    ⋆ (c8 (r - 0x120#64) (sbrA t₀ + 0x5fcc0#64)
    ⋆ (c8 (r - 0x118#64) (dA t₀ ch + 0x3904#64)
    ⋆ (c8 (r - 0x110#64) (sbrA t₀ + 0x5eac0#64)
    ⋆ (c8 (r - 0x108#64) (sbrA t₀ + 0x5f6c0#64)
    ⋆ (Int.toBytes 4 (c0.toInt) =@ (r - 0x100#64)
    ⋆ (Int.toBytes 4 ((-(BitVec.ofNat 32 y.kx1)).toInt) =@ (r - 0xfc#64)
    ⋆ (c8 (r - 0xf8#64) (lab "sbr_qmf_window_ds")
    ⋆ (c8 (r - 0xf0#64) (sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee))
    ⋆ (c8 (r - 0xe8#64) (sbrA t₀ + 0x5f0c0#64 + BitVec.ofNat 64 (0xc0 * ee))
    ⋆ (c8 (r - 0xe0#64) (sbrA t₀ + 0x5e4c0#64 + BitVec.ofNat 64 (0xc0 * ee))
    ⋆ (c8 (r - 0xd8#64) (sbrA t₀ + 0x5d740#64)
    ⋆ (c8 (r - 0xd0#64) (sbrA t₀ + 0x5fdc0#64)
    ⋆ (c8 (r - 0xc8#64) (sbrA t₀ + 0x4c340#64)
    ⋆ (c8 (r - 0xc0#64) (sbrA t₀ + 0x4eb40#64)
    ⋆ (c8 (r - 0xb8#64) (sbrA t₀)
    ⋆ (c8 (r - 0xb0#64) (sbrA t₀ + 0x53b40#64)
    ⋆ (4 ?@ (r - 0xa8#64)
    ⋆ (Int.toBytes 4 ((BitVec.setWidth 32 (arg2 t₀)).toInt) =@ (r - 0xa4#64)
    ⋆ (c8 (r - 0xa0#64) (dA t₀ ch + 0x15030#64 + BitVec.ofNat 64 (0x30 * (ee + 1)))
    ⋆ (c8 (r - 0x98#64) (arg0 t₀)
    ⋆ (6 ?@ (r - 0x90#64)
    ⋆ (Int.toBytes 2 (((u16 y.ftLim (0) : Nat) : Int)) =@ (r - 0x8a#64)
    ⋆ (c8 (r - 0x88#64) (sbrA t₀ + 0x5f6c0#64 + BitVec.ofNat 64 (0xc0 * ee))
    ⋆ (c8 (r - 0x80#64) (BitVec.ofNat 64 (y.nlim))
    ⋆ (c8 (r - 0x78#64) (sbrA t₀ + 0x4ec90#64)
    ⋆ (8 ?@ (r - 0x70#64)
    ⋆ (c8 (r - 0x68#64) (sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee))
    ⋆ (c8 (r - 0x60#64) (BitVec.ofNat 64 (ee))
    ⋆ (c8 (r - 0x58#64) (BitVec.ofNat 64 (kk))
    ⋆ (c8 (r - 0x50#64) (dA t₀ ch)
    ⋆ (7 ?@ (r - 0x48#64)
    ⋆ (1 ?@ (r - 0x41#64)
    ⋆ (c8 (r - 0x40#64) (arg1 t₀)
    ⋆ (4 ?@ (r - 0x38#64) ⋆ 4 ?@ (r - 0x34#64)
    ⋆ (c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ Kt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

abbrev FrGb68 (x : Args) (t₀ : MachineData) (ch : Nat) (c0 : BitVec 32) (y : Args) (ee kk : Nat) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x1c8#64)
    ⋆ (c8 (r - 0x1c0#64) (sbrA t₀ + 0x4c284#64)
    ⋆ (c8 (r - 0x1b8#64) (sbrA t₀ + 0x4c252#64)
    ⋆ (c8 (r - 0x1b0#64) (sbrA t₀ + 0x5e340#64)
    ⋆ (c8 (r - 0x1a8#64) (BitVec.ofNat 64 ch)
    ⋆ (c8 (r - 0x1a0#64) (sbrA t₀ + 0x4c288#64)
    ⋆ (c8 (r - 0x198#64) (sbrA t₀ + 0x4eb50#64)
    ⋆ (c8 (r - 0x190#64) (sbrA t₀ + 0x5dd40#64)
    ⋆ (c8 (r - 0x188#64) (sbrA t₀ + 0xb2#64)
    ⋆ (c8 (r - 0x180#64) (sbrA t₀ + 0x5e4c0#64)
    ⋆ (c8 (r - 0x178#64) (sbrA t₀ + 0x5f0c0#64)
    ⋆ (c8 (r - 0x170#64) (sbrA t₀ + 0x1c#64)
    ⋆ (c8 (r - 0x168#64) (sbrA t₀ + 0x150e0#64)
    ⋆ (c8 (r - 0x160#64) (sbrA t₀ + 0x5f6c4#64)
    ⋆ (c8 (r - 0x158#64) (BitVec.ofNat 64 (dsN x))
    ⋆ (c8 (r - 0x150#64) (sbrA t₀ + 0x5d340#64)
    ⋆ (c8 (r - 0x148#64) (sbrA t₀ + 0x5d540#64)
    ⋆ (c8 (r - 0x140#64) (sbrA t₀ + 0x80#64)
    ⋆ (c8 (r - 0x138#64) (arg3 t₀)
    ⋆ (c8 (r - 0x130#64) (arg4 t₀)
    ⋆ (c8 (r - 0x128#64) (sbrA t₀ + 0x601e0#64)
    ⋆ (c8 (r - 0x120#64) (sbrA t₀ + 0x5fcc0#64)
    ⋆ (c8 (r - 0x118#64) (dA t₀ ch + 0x3904#64)
    ⋆ (c8 (r - 0x110#64) (sbrA t₀ + 0x5eac0#64)
    ⋆ (c8 (r - 0x108#64) (sbrA t₀ + 0x5f6c0#64)
    ⋆ (Int.toBytes 4 (c0.toInt) =@ (r - 0x100#64)
    ⋆ (Int.toBytes 4 ((-(BitVec.ofNat 32 y.kx1)).toInt) =@ (r - 0xfc#64)
    ⋆ (c8 (r - 0xf8#64) (lab "sbr_qmf_window_ds")
    ⋆ (c8 (r - 0xf0#64) (sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee))
    ⋆ (c8 (r - 0xe8#64) (sbrA t₀ + 0x5f0c0#64 + BitVec.ofNat 64 (0xc0 * ee))
    ⋆ (c8 (r - 0xe0#64) (sbrA t₀ + 0x5e4c0#64 + BitVec.ofNat 64 (0xc0 * ee))
    ⋆ (c8 (r - 0xd8#64) (sbrA t₀ + 0x5d740#64)
    ⋆ (c8 (r - 0xd0#64) (sbrA t₀ + 0x5fdc0#64)
    ⋆ (c8 (r - 0xc8#64) (sbrA t₀ + 0x4c340#64)
    ⋆ (c8 (r - 0xc0#64) (sbrA t₀ + 0x4eb40#64)
    ⋆ (c8 (r - 0xb8#64) (sbrA t₀)
    ⋆ (c8 (r - 0xb0#64) (sbrA t₀ + 0x53b40#64)
    ⋆ (4 ?@ (r - 0xa8#64)
    ⋆ (Int.toBytes 4 ((BitVec.setWidth 32 (arg2 t₀)).toInt) =@ (r - 0xa4#64)
    ⋆ (c8 (r - 0xa0#64) (dA t₀ ch + 0x15030#64 + BitVec.ofNat 64 (0x30 * (ee + 1)))
    ⋆ (c8 (r - 0x98#64) (arg0 t₀)
    ⋆ (6 ?@ (r - 0x90#64)
    ⋆ (Int.toBytes 2 (((u16 y.ftLim (0) : Nat) : Int)) =@ (r - 0x8a#64)
    ⋆ (c8 (r - 0x88#64) (sbrA t₀ + 0x5f6c0#64 + BitVec.ofNat 64 (0xc0 * ee))
    ⋆ (c8 (r - 0x80#64) (BitVec.ofNat 64 (y.nlim))
    ⋆ (c8 (r - 0x78#64) (sbrA t₀ + 0x4ec90#64)
    ⋆ (c8 (r - 0x70#64) (BitVec.ofNat 64 ((u16 y.ftLim (kk) - y.kx1)))
    ⋆ (c8 (r - 0x68#64) (sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee))
    ⋆ (c8 (r - 0x60#64) (BitVec.ofNat 64 (ee))
    ⋆ (c8 (r - 0x58#64) (BitVec.ofNat 64 (kk))
    ⋆ (c8 (r - 0x50#64) (dA t₀ ch)
    ⋆ (7 ?@ (r - 0x48#64)
    ⋆ (1 ?@ (r - 0x41#64)
    ⋆ (c8 (r - 0x40#64) (arg1 t₀)
    ⋆ (4 ?@ (r - 0x38#64) ⋆ 4 ?@ (r - 0x34#64)
    ⋆ (c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ Kt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


/-! ## The frame and the invariant -/


/-- The memory at every label: the callees' area below the frame (`0x298 + k` bytes:
a return-address slot, the stack arguments of `sbr_qmf_synthesis`, the callee's
need), the footprint groups, the frame `FR`, the return address and `R`. -/
abbrev Mm (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) (FR : (Mem 64 → Prop) → Mem 64 → Prop) :
    Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  Reserve (0x298 + k) (r - 0x1c8#64) ⋆ (ApplyF e x t₀ ⋆ FR (RetCell ra r ⋆ x.R))

/-- The four stack arguments of `sbr_qmf_synthesis` for channel `ch` as pushed (`mdct_buf =
sbr->qmf_filter_scratch`, `v0`, `v_off`, then `div` — the `ds` register, its low 4 bytes read). -/
abbrev SynArgs (x : Args) (t₀ : MachineData) (ch : Nat) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  c8 (r - 0x1e8#64) (sbrA t₀ + 0x5fcc0#64) ⋆ (c8 (r - 0x1e0#64) (dA t₀ ch + 0x80#64)
    ⋆ (c8 (r - 0x1d8#64) (dA t₀ ch + 0x3900#64) ⋆ c8 (r - 0x1d0#64) (BitVec.ofNat 64 (dsN x))))

/-- `Mm` with the top 0x20 bytes of the callees' area as `A` (the pushed stack arguments of
`sbr_qmf_synthesis`, or raw after the call). -/
abbrev MmS (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) (A : Mem 64 → Prop)
    (FR : (Mem 64 → Prop) → Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  Reserve (0x278 + k) (r - 0x1e8#64) ⋆ (A ⋆ (ApplyF e x t₀ ⋆ FR (RetCell ra r ⋆ x.R)))

/-- `rsp`/`rbp` inside the body. -/
abbrev Base (t₀ s : MachineData) : Prop :=
  s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x1c8#64 ∧ s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64

/-- `Base` and `r14 = 0`: from `start_1`'s `xor %r14d,%r14d` to `L74e9_1`'s `mov %cl,%r14b`
(the `ds` slot is `r14` with its low byte replaced, and `sbr_qmf_synthesis` reads its low
4 bytes as `div`); the dequantisation clobbers `r14` and zeroes it on every path to `L74de`.
The `rbp`/`r14` facts are one conjunct, so `⟨hrsp, hrbp⟩` patterns of `Base` still bind. -/
abbrev BaseZ (t₀ s : MachineData) : Prop :=
  s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x1c8#64
    ∧ (s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64 ∧ s.regs.get64 .r14 = 0#64)

theorem BaseZ.base {t₀ s : MachineData} (h : BaseZ t₀ s) : Base t₀ s := ⟨h.1, h.2.1⟩

/-- The argument registers as at entry. -/
abbrev ArgRegs (t₀ s : MachineData) : Prop :=
  s.regs.get64 .rdi = arg0 t₀ ∧ s.regs.get64 .rsi = arg1 t₀ ∧ s.regs.get64 .rdx = arg2 t₀
    ∧ s.regs.get64 .rcx = arg3 t₀ ∧ s.regs.get64 .r8 = arg4 t₀

/-- The default entry of a label inside the body: the conditions, `rsp`/`rbp`, the
callee-saved registers in the frame, the memory with a raw frame. Phase spec files
refine it (register facts, frame views with values). -/
abbrev Inv (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ s : MachineData) : Prop :=
  ApplyC x t₀ ∧ Base t₀ s ∧ (s.dmem =⋆ Mm k e x ra t₀ (FrRaw t₀))

/-! ## The table -/

namespace E

/-- ff_aac_sbr_apply -/
abbrev start (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => s = t₀ ∧ ApplyPre k e x ra t₀
/-- ff_aac_sbr_apply.start_1 -/
abbrev start_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ArgRegs t₀ s ∧ (s.dmem =⋆ Mm k e x ra t₀ (FrA x t₀))
/-- ff_aac_sbr_apply.start_2 -/
abbrev start_2 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ BaseZ t₀ s ∧ ArgRegs t₀ s ∧ (s.dmem =⋆ Mm k e x ra t₀ (FrA1 x t₀))
/-- ff_aac_sbr_apply.start_3 -/
abbrev start_3 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ BitVec.setWidth 8 (s.regs.get64 .rbx) = 0#8 ∧ x.start ≠ 0 ∧ s.status.zf = decide (x.pushed = 0) ∧ (s.dmem =⋆ Mm k e x ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L676e -/
abbrev L676e (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ ∃ x' : Args, (x' = x ∨ x' = x.turnoff.spSet) ∧ (BitVec.setWidth 8 (s.regs.get64 .rbx) = 1#8 ∨ (BitVec.setWidth 8 (s.regs.get64 .rbx) = 0#8 ∧ x' = x ∧ x.start ≠ 0)) ∧ x'.pushed = 0 ∧ IdLive t₀ x' ∧ (s.dmem =⋆ Mm k e x' ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L6797 -/
abbrev L6797 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ BaseZ t₀ s ∧ s.regs.get64 .rdi = arg0 t₀ ∧ s.regs.get64 .rdx = arg2 t₀ ∧ (s.dmem =⋆ Mm k e x ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L6797_1 -/
abbrev L6797_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ BaseZ t₀ s ∧ (s.dmem =⋆ Mm k e x ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L6817 -/
abbrev L6817 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ BitVec.setWidth 8 (s.regs.get64 .rbx) = 1#8 ∧ ∃ x' : Args, (x' = x ∨ x' = x.turnoff.spSet) ∧ IdLive t₀ x' ∧ (s.dmem =⋆ Mm k e x' ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L6825 -/
abbrev L6825 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ ∃ x' : Args, (x' = x ∨ x' = x.turnoff.spSet) ∧ (BitVec.setWidth 8 (s.regs.get64 .rbx) = 1#8 ∨ (BitVec.setWidth 8 (s.regs.get64 .rbx) = 0#8 ∧ x' = x ∧ x.start ≠ 0)) ∧ x'.pushed ≠ 0 ∧ IdLive t₀ x' ∧ (s.dmem =⋆ Mm k e x' ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L6838 -/
abbrev L6838 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ x.start ≠ 0 ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L6838_1 -/
abbrev L6838_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ x.start ≠ 0 ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrE x t₀))
/-- ff_aac_sbr_apply.L6838_2 -/
abbrev L6838_2 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ x.start ≠ 0 ∧ s.regs.get64 .rbx = 1#64 ∧ s.regs.get64 .r12 = arg1 t₀ + 0x53670#64 ∧ s.regs.get64 .r13 = arg1 t₀ + 0x538b0#64 ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L68b0 -/
abbrev L68b0 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ Base t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ (∃ ee : Nat, 1 ≤ ee ∧ ee ≤ x.d0.nenv ∧ s.regs.get64 .rbx = BitVec.ofNat 64 ee ∧ s.regs.get64 .r12 = arg1 t₀ + 0x53640#64 + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r13 = arg1 t₀ + 0x537f0#64 + BitVec.ofNat 64 (0xc0 * ee)) ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L68d0 -/
abbrev L68d0 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ Base t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ (∃ ee kk : Nat, 1 ≤ ee ∧ ee ≤ x.d0.nenv ∧ s.regs.get64 .rbx = BitVec.ofNat 64 ee ∧ s.regs.get64 .r12 = arg1 t₀ + 0x53640#64 + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r13 = arg1 t₀ + 0x537f0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ (s.regs.get64 .rax).toNat ≤ 1 ∧ kk < 48 ∧ s.regs.get64 .r14 = BitVec.ofNat 64 kk) ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L68d0_1 -/
abbrev L68d0_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ Base t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ (∃ ee kk : Nat, 1 ≤ ee ∧ ee ≤ x.d0.nenv ∧ s.regs.get64 .rbx = BitVec.ofNat 64 ee ∧ s.regs.get64 .r12 = arg1 t₀ + 0x53640#64 + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r13 = arg1 t₀ + 0x537f0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ (s.regs.get64 .rax).toNat ≤ 1 ∧ kk < 48 ∧ s.regs.get64 .r14 = BitVec.ofNat 64 kk) ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L68f8 -/
abbrev L68f8 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ Base t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ (∃ ee kk : Nat, 1 ≤ ee ∧ ee ≤ x.d0.nenv ∧ s.regs.get64 .rbx = BitVec.ofNat 64 ee ∧ s.regs.get64 .r12 = arg1 t₀ + 0x53640#64 + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r13 = arg1 t₀ + 0x537f0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ (s.regs.get64 .rax).toNat ≤ 1 ∧ kk ≤ 48 ∧ s.regs.get64 .r14 = BitVec.ofNat 64 kk) ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L6940 -/
abbrev L6940 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ Base t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ (∃ ee kk : Nat, 1 ≤ ee ∧ ee ≤ x.d0.nenv ∧ s.regs.get64 .rbx = BitVec.ofNat 64 ee ∧ s.regs.get64 .r12 = arg1 t₀ + 0x53640#64 + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r13 = arg1 t₀ + 0x537f0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ (s.regs.get64 .rax).toNat ≤ 1 ∧ kk < 48 ∧ s.regs.get64 .r14 = BitVec.ofNat 64 kk) ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L6940_1 -/
abbrev L6940_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ Base t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ (∃ ee kk : Nat, 1 ≤ ee ∧ ee ≤ x.d0.nenv ∧ s.regs.get64 .rbx = BitVec.ofNat 64 ee ∧ s.regs.get64 .r12 = arg1 t₀ + 0x53640#64 + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r13 = arg1 t₀ + 0x537f0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ (s.regs.get64 .rax).toNat ≤ 1 ∧ kk < 48 ∧ s.regs.get64 .r14 = BitVec.ofNat 64 kk) ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L69a4 -/
abbrev L69a4 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ Base t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ (∃ ee kk : Nat, 1 ≤ ee ∧ ee ≤ x.d0.nenv ∧ s.regs.get64 .rbx = BitVec.ofNat 64 ee ∧ s.regs.get64 .r12 = arg1 t₀ + 0x53640#64 + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r13 = arg1 t₀ + 0x537f0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ (s.regs.get64 .rax).toNat ≤ 1 ∧ kk < 48 ∧ s.regs.get64 .r14 = BitVec.ofNat 64 kk) ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L69d0 -/
abbrev L69d0 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ Base t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ (∃ ee kk : Nat, 1 ≤ ee ∧ ee ≤ x.d0.nenv ∧ s.regs.get64 .rbx = BitVec.ofNat 64 ee ∧ s.regs.get64 .r12 = arg1 t₀ + 0x53640#64 + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r13 = arg1 t₀ + 0x537f0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ (s.regs.get64 .rax).toNat ≤ 1 ∧ kk < 48 ∧ s.regs.get64 .r14 = BitVec.ofNat 64 kk) ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L69dd -/
abbrev L69dd (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ Base t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ (∃ ee kk : Nat, 1 ≤ ee ∧ ee ≤ x.d0.nenv ∧ s.regs.get64 .rbx = BitVec.ofNat 64 ee ∧ s.regs.get64 .r12 = arg1 t₀ + 0x53640#64 + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r13 = arg1 t₀ + 0x537f0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ (s.regs.get64 .rax).toNat ≤ 1 ∧ kk < 48 ∧ s.regs.get64 .r14 = BitVec.ofNat 64 kk) ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L6a10 -/
abbrev L6a10 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ Base t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ (∃ ee kk : Nat, 1 ≤ ee ∧ ee ≤ x.d0.nenv ∧ s.regs.get64 .rbx = BitVec.ofNat 64 ee ∧ s.regs.get64 .r12 = arg1 t₀ + 0x53640#64 + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r13 = arg1 t₀ + 0x537f0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ (s.regs.get64 .rax).toNat ≤ 1 ∧ kk < 48 ∧ s.regs.get64 .r14 = BitVec.ofNat 64 kk) ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L6a30 -/
abbrev L6a30 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ Base t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ (∃ ee kk : Nat, 1 ≤ ee ∧ ee ≤ x.d0.nenv ∧ s.regs.get64 .rbx = BitVec.ofNat 64 ee ∧ s.regs.get64 .r12 = arg1 t₀ + 0x53640#64 + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r13 = arg1 t₀ + 0x537f0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ (s.regs.get64 .rax).toNat ≤ 1 ∧ kk < 48 ∧ s.regs.get64 .r14 = BitVec.ofNat 64 kk) ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L6a30_1 -/
abbrev L6a30_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ Base t₀ s ∧ (∃ ee kk : Nat, 1 ≤ ee ∧ ee ≤ x.d0.nenv ∧ s.regs.get64 .rbx = BitVec.ofNat 64 ee ∧ s.regs.get64 .r12 = arg1 t₀ + 0x53640#64 + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r13 = arg1 t₀ + 0x537f0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ kk < 48 ∧ s.regs.get64 .r14 = BitVec.ofNat 64 kk) ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L6a30_2 -/
abbrev L6a30_2 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ Base t₀ s ∧ (∃ ee kk : Nat, 1 ≤ ee ∧ ee ≤ x.d0.nenv ∧ s.regs.get64 .rbx = BitVec.ofNat 64 ee ∧ s.regs.get64 .r12 = arg1 t₀ + 0x53640#64 + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r13 = arg1 t₀ + 0x537f0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ kk < 48 ∧ s.regs.get64 .r14 = BitVec.ofNat 64 kk) ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L6a90 -/
abbrev L6a90 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ Base t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ (∃ ee : Nat, 1 ≤ ee ∧ ee ≤ x.d0.nenv ∧ s.regs.get64 .rbx = BitVec.ofNat 64 ee ∧ s.regs.get64 .r12 = arg1 t₀ + 0x53640#64 + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r13 = arg1 t₀ + 0x537f0#64 + BitVec.ofNat 64 (0xc0 * ee)) ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L6abf -/
abbrev L6abf (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L6b00 -/
abbrev L6b00 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ (∃ jj : Nat, jj + 1 ≤ x.d0.nnoise ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (jj + 1) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (5 * jj) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (x.d0.nnoise + 1) ∧ BitVec.extractLsb' 0 64 (s.zmms.get (AvxReg.xmm RegMm.mm0)) = dbl1E20) ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L6b02 -/
abbrev L6b02 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ (∃ jj : Nat, jj + 1 ≤ x.d0.nnoise ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (jj + 1) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (5 * jj) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (x.d0.nnoise + 1) ∧ BitVec.extractLsb' 0 64 (s.zmms.get (AvxReg.xmm RegMm.mm0)) = dbl1E20) ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L6b12 -/
abbrev L6b12 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ (∃ jj : Nat, jj + 1 ≤ x.d0.nnoise ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (jj + 1) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (5 * jj) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (x.d0.nnoise + 1) ∧ BitVec.extractLsb' 0 64 (s.zmms.get (AvxReg.xmm RegMm.mm0)) = dbl1E20) ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L6b50 -/
abbrev L6b50 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ (∃ jj dd : Nat, jj + 1 ≤ x.d0.nnoise ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (jj + 1) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (5 * jj) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (x.d0.nnoise + 1) ∧ BitVec.extractLsb' 0 64 (s.zmms.get (AvxReg.xmm RegMm.mm0)) = dbl1E20 ∧ dd < 256 ∧ 134 ≤ dd ∧ s.regs.get64 .rdi = BitVec.ofNat 64 dd ∧ s.regs.get64 .rcx = BitVec.setWidth 64 (7#32 - BitVec.ofNat 32 dd)) ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L6b6c -/
abbrev L6b6c (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ (∃ jj : Nat, jj + 1 ≤ x.d0.nnoise ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (jj + 1) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (5 * jj) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (x.d0.nnoise + 1) ∧ BitVec.extractLsb' 0 64 (s.zmms.get (AvxReg.xmm RegMm.mm0)) = dbl1E20 ∧ (BitVec.setWidth 32 (s.zmms.get (AvxReg.xmm RegMm.mm2))).toNat ≤ 0x43000000) ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L6ba0 -/
abbrev L6ba0 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ (∃ jj : Nat, jj + 1 ≤ x.d0.nnoise ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (jj + 1) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (5 * jj) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (x.d0.nnoise + 1) ∧ BitVec.extractLsb' 0 64 (s.zmms.get (AvxReg.xmm RegMm.mm0)) = dbl1E20 ∧ (BitVec.setWidth 32 (s.zmms.get (AvxReg.xmm RegMm.mm2))).toNat ≤ 0x43000000) ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L6bbc -/
abbrev L6bbc (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ (∃ jj : Nat, jj + 1 ≤ x.d0.nnoise ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (jj + 1) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (5 * jj) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (x.d0.nnoise + 1) ∧ BitVec.extractLsb' 0 64 (s.zmms.get (AvxReg.xmm RegMm.mm0)) = dbl1E20 ∧ (BitVec.setWidth 32 (s.zmms.get (AvxReg.xmm RegMm.mm2))).toNat ≤ 0x43000000) ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L6bbc_1 -/
abbrev L6bbc_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ (∃ jj : Nat, jj + 1 ≤ x.d0.nnoise ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (jj + 1) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (5 * jj) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (x.d0.nnoise + 1) ∧ BitVec.extractLsb' 0 64 (s.zmms.get (AvxReg.xmm RegMm.mm0)) = dbl1E20) ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L6c1e -/
abbrev L6c1e (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ (∃ jj dd : Nat, jj + 1 ≤ x.d0.nnoise ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (jj + 1) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (5 * jj) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (x.d0.nnoise + 1) ∧ BitVec.extractLsb' 0 64 (s.zmms.get (AvxReg.xmm RegMm.mm0)) = dbl1E20 ∧ dd < 256 ∧ 134 ≤ dd ∧ s.regs.get64 .rdi = BitVec.ofNat 64 dd ∧ s.regs.get64 .rcx = BitVec.setWidth 64 (7#32 - BitVec.ofNat 32 dd)) ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L6c3a -/
abbrev L6c3a (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ (∃ jj : Nat, jj + 1 ≤ x.d0.nnoise ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (jj + 1) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (5 * jj) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (x.d0.nnoise + 1) ∧ BitVec.extractLsb' 0 64 (s.zmms.get (AvxReg.xmm RegMm.mm0)) = dbl1E20 ∧ (BitVec.setWidth 32 (s.zmms.get (AvxReg.xmm RegMm.mm2))).toNat ≤ 0x43000000) ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L6c61 -/
abbrev L6c61 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ (∃ jj : Nat, jj + 1 ≤ x.d0.nnoise ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (jj + 1) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (5 * jj) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (x.d0.nnoise + 1) ∧ BitVec.extractLsb' 0 64 (s.zmms.get (AvxReg.xmm RegMm.mm0)) = dbl1E20 ∧ (BitVec.setWidth 32 (s.zmms.get (AvxReg.xmm RegMm.mm2))).toNat ≤ 0x43000000) ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L6c7d -/
abbrev L6c7d (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ (∃ jj : Nat, jj + 1 ≤ x.d0.nnoise ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (jj + 1) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (5 * jj) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (x.d0.nnoise + 1) ∧ BitVec.extractLsb' 0 64 (s.zmms.get (AvxReg.xmm RegMm.mm0)) = dbl1E20 ∧ (BitVec.setWidth 32 (s.zmms.get (AvxReg.xmm RegMm.mm2))).toNat ≤ 0x43000000) ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L6c7d_1 -/
abbrev L6c7d_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ (∃ jj : Nat, jj + 1 ≤ x.d0.nnoise ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (jj + 1) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (5 * jj) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (x.d0.nnoise + 1) ∧ BitVec.extractLsb' 0 64 (s.zmms.get (AvxReg.xmm RegMm.mm0)) = dbl1E20) ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L6c7d_2 -/
abbrev L6c7d_2 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ (∃ jj : Nat, jj + 1 ≤ x.d0.nnoise ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (jj + 1) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (5 * jj) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (x.d0.nnoise + 1) ∧ BitVec.extractLsb' 0 64 (s.zmms.get (AvxReg.xmm RegMm.mm0)) = dbl1E20) ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L6ce0 -/
abbrev L6ce0 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ (∃ jj : Nat, jj + 1 ≤ x.d0.nnoise ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (jj + 1) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (5 * jj) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (x.d0.nnoise + 1) ∧ BitVec.extractLsb' 0 64 (s.zmms.get (AvxReg.xmm RegMm.mm0)) = dbl1E20) ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L6cea -/
abbrev L6cea (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ (∃ jj dd : Nat, jj + 1 ≤ x.d0.nnoise ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (jj + 1) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (5 * jj) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (x.d0.nnoise + 1) ∧ BitVec.extractLsb' 0 64 (s.zmms.get (AvxReg.xmm RegMm.mm0)) = dbl1E20 ∧ dd < 256 ∧ 134 ≤ dd ∧ s.regs.get64 .r8 = BitVec.ofNat 64 dd ∧ s.regs.get64 .rcx = BitVec.setWidth 64 (7#32 - BitVec.ofNat 32 dd)) ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L6d09 -/
abbrev L6d09 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ (∃ jj : Nat, jj + 1 ≤ x.d0.nnoise ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (jj + 1) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (5 * jj) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (x.d0.nnoise + 1) ∧ BitVec.extractLsb' 0 64 (s.zmms.get (AvxReg.xmm RegMm.mm0)) = dbl1E20 ∧ (BitVec.setWidth 32 (s.zmms.get (AvxReg.xmm RegMm.mm2))).toNat ≤ 0x43000000) ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L6d32 -/
abbrev L6d32 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ (∃ jj : Nat, jj + 1 ≤ x.d0.nnoise ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (jj + 1) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (5 * jj) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (x.d0.nnoise + 1) ∧ BitVec.extractLsb' 0 64 (s.zmms.get (AvxReg.xmm RegMm.mm0)) = dbl1E20 ∧ (BitVec.setWidth 32 (s.zmms.get (AvxReg.xmm RegMm.mm2))).toNat ≤ 0x43000000) ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L6d51 -/
abbrev L6d51 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ (∃ jj : Nat, jj + 1 ≤ x.d0.nnoise ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (jj + 1) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (5 * jj) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (x.d0.nnoise + 1) ∧ BitVec.extractLsb' 0 64 (s.zmms.get (AvxReg.xmm RegMm.mm0)) = dbl1E20 ∧ (BitVec.setWidth 32 (s.zmms.get (AvxReg.xmm RegMm.mm2))).toNat ≤ 0x43000000) ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L6d51_1 -/
abbrev L6d51_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ (∃ jj : Nat, jj + 1 ≤ x.d0.nnoise ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (jj + 1) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (5 * jj) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (x.d0.nnoise + 1) ∧ BitVec.extractLsb' 0 64 (s.zmms.get (AvxReg.xmm RegMm.mm0)) = dbl1E20) ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L6dbc -/
abbrev L6dbc (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ (∃ jj dd : Nat, jj + 1 ≤ x.d0.nnoise ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (jj + 1) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (5 * jj) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (x.d0.nnoise + 1) ∧ BitVec.extractLsb' 0 64 (s.zmms.get (AvxReg.xmm RegMm.mm0)) = dbl1E20 ∧ dd < 256 ∧ 134 ≤ dd ∧ s.regs.get64 .r8 = BitVec.ofNat 64 dd ∧ s.regs.get64 .rcx = BitVec.setWidth 64 (7#32 - BitVec.ofNat 32 dd)) ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L6ddb -/
abbrev L6ddb (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ (∃ jj : Nat, jj + 1 ≤ x.d0.nnoise ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (jj + 1) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (5 * jj) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (x.d0.nnoise + 1) ∧ BitVec.extractLsb' 0 64 (s.zmms.get (AvxReg.xmm RegMm.mm0)) = dbl1E20 ∧ (BitVec.setWidth 32 (s.zmms.get (AvxReg.xmm RegMm.mm2))).toNat ≤ 0x43000000) ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L6e04 -/
abbrev L6e04 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ (∃ jj : Nat, jj + 1 ≤ x.d0.nnoise ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (jj + 1) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (5 * jj) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (x.d0.nnoise + 1) ∧ BitVec.extractLsb' 0 64 (s.zmms.get (AvxReg.xmm RegMm.mm0)) = dbl1E20 ∧ (BitVec.setWidth 32 (s.zmms.get (AvxReg.xmm RegMm.mm2))).toNat ≤ 0x43000000) ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L6e23 -/
abbrev L6e23 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ (∃ jj : Nat, jj + 1 ≤ x.d0.nnoise ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (jj + 1) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (5 * jj) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (x.d0.nnoise + 1) ∧ BitVec.extractLsb' 0 64 (s.zmms.get (AvxReg.xmm RegMm.mm0)) = dbl1E20 ∧ (BitVec.setWidth 32 (s.zmms.get (AvxReg.xmm RegMm.mm2))).toNat ≤ 0x43000000) ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L6e23_1 -/
abbrev L6e23_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ (∃ jj : Nat, jj + 1 ≤ x.d0.nnoise ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (jj + 1) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (5 * jj) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (x.d0.nnoise + 1) ∧ BitVec.extractLsb' 0 64 (s.zmms.get (AvxReg.xmm RegMm.mm0)) = dbl1E20) ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L6e8c -/
abbrev L6e8c (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ (∃ jj dd : Nat, jj + 1 ≤ x.d0.nnoise ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (jj + 1) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (5 * jj) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (x.d0.nnoise + 1) ∧ BitVec.extractLsb' 0 64 (s.zmms.get (AvxReg.xmm RegMm.mm0)) = dbl1E20 ∧ dd < 256 ∧ 134 ≤ dd ∧ s.regs.get64 .rdi = BitVec.ofNat 64 dd ∧ s.regs.get64 .rcx = BitVec.setWidth 64 (7#32 - BitVec.ofNat 32 dd)) ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L6ea8 -/
abbrev L6ea8 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ (∃ jj : Nat, jj + 1 ≤ x.d0.nnoise ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (jj + 1) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (5 * jj) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (x.d0.nnoise + 1) ∧ BitVec.extractLsb' 0 64 (s.zmms.get (AvxReg.xmm RegMm.mm0)) = dbl1E20 ∧ (BitVec.setWidth 32 (s.zmms.get (AvxReg.xmm RegMm.mm2))).toNat ≤ 0x43000000) ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L6ecf -/
abbrev L6ecf (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ (∃ jj : Nat, jj + 1 ≤ x.d0.nnoise ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (jj + 1) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (5 * jj) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (x.d0.nnoise + 1) ∧ BitVec.extractLsb' 0 64 (s.zmms.get (AvxReg.xmm RegMm.mm0)) = dbl1E20 ∧ (BitVec.setWidth 32 (s.zmms.get (AvxReg.xmm RegMm.mm2))).toNat ≤ 0x43000000) ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L6eeb -/
abbrev L6eeb (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ (∃ jj : Nat, jj + 1 ≤ x.d0.nnoise ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (jj + 1) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (5 * jj) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (x.d0.nnoise + 1) ∧ BitVec.extractLsb' 0 64 (s.zmms.get (AvxReg.xmm RegMm.mm0)) = dbl1E20 ∧ (BitVec.setWidth 32 (s.zmms.get (AvxReg.xmm RegMm.mm2))).toNat ≤ 0x43000000) ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L6eeb_1 -/
abbrev L6eeb_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ (∃ jj : Nat, jj + 1 ≤ x.d0.nnoise ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (jj + 1) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (5 * jj) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (x.d0.nnoise + 1) ∧ BitVec.extractLsb' 0 64 (s.zmms.get (AvxReg.xmm RegMm.mm0)) = dbl1E20) ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L6eeb_2 -/
abbrev L6eeb_2 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ (∃ jj : Nat, jj + 1 ≤ x.d0.nnoise ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (jj + 1) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (5 * jj) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (x.d0.nnoise + 1) ∧ BitVec.extractLsb' 0 64 (s.zmms.get (AvxReg.xmm RegMm.mm0)) = dbl1E20) ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L6f32 -/
abbrev L6f32 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ BaseZ t₀ s ∧ BitVec.setWidth 8 (s.regs.get64 .rbx) = 1#8 ∧ (s.dmem =⋆ Mm k e x ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L6f32_1 -/
abbrev L6f32_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ BaseZ t₀ s ∧ BitVec.setWidth 8 (s.regs.get64 .rbx) = 1#8 ∧ (s.dmem =⋆ Mm k e x ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L6f32_2 -/
abbrev L6f32_2 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ BitVec.setWidth 8 (s.regs.get64 .rbx) = 1#8 ∧ (s.dmem =⋆ Mm k e x.turnoff.spSet ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L6fbe -/
abbrev L6fbe (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L6fca -/
abbrev L6fca (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ ∃ nch : Nat, (nch = 1 ∨ nch = 2) ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrS0 nch x t₀))
/-- ff_aac_sbr_apply.L6ff7 -/
abbrev L6ff7 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => False
/-- ff_aac_sbr_apply.L6ffc -/
abbrev L6ffc (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ ∃ ch nch : Nat, ch < nch ∧ nch ≤ 2 ∧ s.regs.get64 .r13 = dA t₀ ch ∧ s.regs.get64 .rax = 3#64 ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrDq ch nch x t₀))
/-- ff_aac_sbr_apply.L7007 -/
abbrev L7007 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ ∃ ch nch : Nat, ch < nch ∧ nch ≤ 2 ∧ s.regs.get64 .r13 = dA t₀ ch ∧ s.regs.get64 .rax = 3#64 ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrDq ch nch x t₀))
/-- ff_aac_sbr_apply.L700e -/
abbrev L700e (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ ∃ ch nch : Nat, ch < nch ∧ nch ≤ 2 ∧ s.regs.get64 .r13 = dA t₀ ch ∧ s.regs.get64 .rax = 3#64 ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrDq ch nch x t₀))
/-- ff_aac_sbr_apply.L7020 -/
abbrev L7020 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ ∃ ch nch : Nat, ch < nch ∧ nch ≤ 2 ∧ s.regs.get64 .r13 = dA t₀ ch ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrDq ch nch x t₀))
/-- ff_aac_sbr_apply.L7020_1 -/
abbrev L7020_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ ∃ ch nch : Nat, ch < nch ∧ nch ≤ 2 ∧ s.regs.get64 .rax = BitVec.ofNat 64 (ch + 1) ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrL1 ch nch x t₀))
/-- ff_aac_sbr_apply.L7020_2 -/
abbrev L7020_2 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ ∃ ch nch : Nat, ch < nch ∧ nch ≤ 2 ∧ s.regs.get64 .rax = BitVec.ofNat 64 (ch + 1) ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrL2 ch nch x t₀))
/-- ff_aac_sbr_apply.L7044 -/
abbrev L7044 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ ∃ ch nch : Nat, ch < nch ∧ nch ≤ 2 ∧ s.regs.get64 .rax = BitVec.ofNat 64 ch ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrM ch nch x t₀))
/-- ff_aac_sbr_apply.L7044_1 -/
abbrev L7044_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ ∃ ch nch : Nat, ch < nch ∧ nch ≤ 2 ∧ s.regs.get64 .rax = BitVec.ofNat 64 (0x15ac0 * ch) ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrDq ch nch x t₀))
/-- ff_aac_sbr_apply.L7070 -/
abbrev L7070 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ Base t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ ∃ ch nch : Nat, ch < nch ∧ nch ≤ 2 ∧ s.regs.get64 .r13 = dA t₀ ch ∧ ∃ j : BitVec 64, s.regs.get64 .r15 = j ∧ 1 ≤ j.toNat ∧ j.toNat ≤ (x.d ch).nenv ∧ s.regs.get64 .r14 = dA t₀ ch + 0x151e0#64 + 0x30#64 * j ∧ s.regs.get64 .r12 = dA t₀ ch + 0x15390#64 + 0xc0#64 * j ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrDq ch nch x t₀))
/-- ff_aac_sbr_apply.L7090 -/
abbrev L7090 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ Base t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ ∃ ch nch : Nat, ch < nch ∧ nch ≤ 2 ∧ s.regs.get64 .r13 = dA t₀ ch ∧ ∃ j : BitVec 64, s.regs.get64 .r15 = j ∧ 1 ≤ j.toNat ∧ j.toNat ≤ (x.d ch).nenv ∧ s.regs.get64 .r14 = dA t₀ ch + 0x151e0#64 + 0x30#64 * j ∧ s.regs.get64 .r12 = dA t₀ ch + 0x15390#64 + 0xc0#64 * j ∧ (s.regs.get64 .rbx).toNat < 48 ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrDq ch nch x t₀))
/-- ff_aac_sbr_apply.L7090_1 -/
abbrev L7090_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ Base t₀ s ∧ ∃ ch nch : Nat, ch < nch ∧ nch ≤ 2 ∧ s.regs.get64 .r13 = dA t₀ ch ∧ ∃ j : BitVec 64, s.regs.get64 .r15 = j ∧ 1 ≤ j.toNat ∧ j.toNat ≤ (x.d ch).nenv ∧ s.regs.get64 .r14 = dA t₀ ch + 0x151e0#64 + 0x30#64 * j ∧ s.regs.get64 .r12 = dA t₀ ch + 0x15390#64 + 0xc0#64 * j ∧ (s.regs.get64 .rbx).toNat < 48 ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrDq ch nch x t₀))
/-- ff_aac_sbr_apply.L7090_2 -/
abbrev L7090_2 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ Base t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ ∃ ch nch : Nat, ch < nch ∧ nch ≤ 2 ∧ s.regs.get64 .r13 = dA t₀ ch ∧ ∃ j : BitVec 64, s.regs.get64 .r15 = j ∧ 1 ≤ j.toNat ∧ j.toNat ≤ (x.d ch).nenv ∧ s.regs.get64 .r14 = dA t₀ ch + 0x151e0#64 + 0x30#64 * j ∧ s.regs.get64 .r12 = dA t₀ ch + 0x15390#64 + 0xc0#64 * j ∧ (s.regs.get64 .rbx).toNat < 48 ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrDq ch nch x t₀))
/-- ff_aac_sbr_apply.L70bf -/
abbrev L70bf (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ Base t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ ∃ ch nch : Nat, ch < nch ∧ nch ≤ 2 ∧ s.regs.get64 .r13 = dA t₀ ch ∧ ∃ j : BitVec 64, s.regs.get64 .r15 = j ∧ 1 ≤ j.toNat ∧ j.toNat ≤ (x.d ch).nenv ∧ s.regs.get64 .r14 = dA t₀ ch + 0x151e0#64 + 0x30#64 * j ∧ s.regs.get64 .r12 = dA t₀ ch + 0x15390#64 + 0xc0#64 * j ∧ s.regs.get64 .rax = BitVec.ofNat 64 (u8 (x.d ch).freqRes j.toNat) ∧ (s.regs.get64 .rbx).toNat < 48 ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrDq ch nch x t₀))
/-- ff_aac_sbr_apply.L70ca -/
abbrev L70ca (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ Base t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ ∃ ch nch : Nat, ch < nch ∧ nch ≤ 2 ∧ s.regs.get64 .r13 = dA t₀ ch ∧ ∃ j : BitVec 64, s.regs.get64 .r15 = j ∧ 1 ≤ j.toNat ∧ j.toNat ≤ (x.d ch).nenv ∧ s.regs.get64 .r14 = dA t₀ ch + 0x151e0#64 + 0x30#64 * j ∧ s.regs.get64 .r12 = dA t₀ ch + 0x15390#64 + 0xc0#64 * j ∧ s.regs.get64 .rax = BitVec.ofNat 64 (u8 (x.d ch).freqRes j.toNat) ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrDq ch nch x t₀))
/-- ff_aac_sbr_apply.L70ca_1 -/
abbrev L70ca_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ Base t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ ∃ ch nch : Nat, ch < nch ∧ nch ≤ 2 ∧ s.regs.get64 .r13 = dA t₀ ch ∧ ∃ j : BitVec 64, s.regs.get64 .r15 = j ∧ 1 ≤ j.toNat ∧ j.toNat ≤ (x.d ch).nenv ∧ s.regs.get64 .r14 = dA t₀ ch + 0x151e0#64 + 0x30#64 * j ∧ s.regs.get64 .r12 = dA t₀ ch + 0x15390#64 + 0xc0#64 * j ∧ s.regs.get64 .rax = BitVec.ofNat 64 (u8 (x.d ch).freqRes j.toNat) ∧ (s.regs.get64 .rbx).toNat < 48 ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrDq ch nch x t₀))
/-- ff_aac_sbr_apply.L7120 -/
abbrev L7120 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ Base t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ ∃ ch nch : Nat, ch < nch ∧ nch ≤ 2 ∧ s.regs.get64 .r13 = dA t₀ ch ∧ ∃ j : BitVec 64, s.regs.get64 .r15 = j ∧ 1 ≤ j.toNat ∧ j.toNat ≤ (x.d ch).nenv ∧ s.regs.get64 .r14 = dA t₀ ch + 0x151e0#64 + 0x30#64 * j ∧ s.regs.get64 .r12 = dA t₀ ch + 0x15390#64 + 0xc0#64 * j ∧ s.regs.get64 .rax = BitVec.ofNat 64 (u8 (x.d ch).freqRes j.toNat) ∧ (s.regs.get64 .rbx).toNat < 48 ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrDq ch nch x t₀))
/-- ff_aac_sbr_apply.L7140 -/
abbrev L7140 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ Base t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ ∃ ch nch : Nat, ch < nch ∧ nch ≤ 2 ∧ s.regs.get64 .r13 = dA t₀ ch ∧ ∃ j : BitVec 64, s.regs.get64 .r15 = j ∧ 1 ≤ j.toNat ∧ j.toNat ≤ (x.d ch).nenv ∧ s.regs.get64 .r14 = dA t₀ ch + 0x151e0#64 + 0x30#64 * j ∧ s.regs.get64 .r12 = dA t₀ ch + 0x15390#64 + 0xc0#64 * j ∧ s.regs.get64 .rax = BitVec.ofNat 64 (u8 (x.d ch).freqRes j.toNat) ∧ (s.regs.get64 .rbx).toNat < 48 ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrDq ch nch x t₀))
/-- ff_aac_sbr_apply.L7166 -/
abbrev L7166 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ Base t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ ∃ ch nch : Nat, ch < nch ∧ nch ≤ 2 ∧ s.regs.get64 .r13 = dA t₀ ch ∧ ∃ j : BitVec 64, s.regs.get64 .r15 = j ∧ 1 ≤ j.toNat ∧ j.toNat ≤ (x.d ch).nenv ∧ s.regs.get64 .r14 = dA t₀ ch + 0x151e0#64 + 0x30#64 * j ∧ s.regs.get64 .r12 = dA t₀ ch + 0x15390#64 + 0xc0#64 * j ∧ s.regs.get64 .rax = BitVec.ofNat 64 (u8 (x.d ch).freqRes j.toNat) ∧ (s.regs.get64 .rbx).toNat < 48 ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrDq ch nch x t₀))
/-- ff_aac_sbr_apply.L717f -/
abbrev L717f (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ Base t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ ∃ ch nch : Nat, ch < nch ∧ nch ≤ 2 ∧ s.regs.get64 .r13 = dA t₀ ch ∧ ∃ j : BitVec 64, s.regs.get64 .r15 = j ∧ 1 ≤ j.toNat ∧ j.toNat ≤ (x.d ch).nenv ∧ s.regs.get64 .r14 = dA t₀ ch + 0x151e0#64 + 0x30#64 * j ∧ s.regs.get64 .r12 = dA t₀ ch + 0x15390#64 + 0xc0#64 * j ∧ s.regs.get64 .rax = BitVec.ofNat 64 (u8 (x.d ch).freqRes j.toNat) ∧ (s.regs.get64 .rbx).toNat < 48 ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrDq ch nch x t₀))
/-- ff_aac_sbr_apply.L71b0 -/
abbrev L71b0 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ Base t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ ∃ ch nch : Nat, ch < nch ∧ nch ≤ 2 ∧ s.regs.get64 .r13 = dA t₀ ch ∧ ∃ j : BitVec 64, s.regs.get64 .r15 = j ∧ 1 ≤ j.toNat ∧ j.toNat ≤ (x.d ch).nenv ∧ s.regs.get64 .r14 = dA t₀ ch + 0x151e0#64 + 0x30#64 * j ∧ s.regs.get64 .r12 = dA t₀ ch + 0x15390#64 + 0xc0#64 * j ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrDq ch nch x t₀))
/-- ff_aac_sbr_apply.L71e0 -/
abbrev L71e0 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ Base t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ ∃ ch nch : Nat, ch < nch ∧ nch ≤ 2 ∧ s.regs.get64 .r13 = dA t₀ ch ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrDq ch nch x t₀))
/-- ff_aac_sbr_apply.L71e0_1 -/
abbrev L71e0_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ ∃ ch nch : Nat, ch < nch ∧ nch ≤ 2 ∧ s.regs.get64 .r13 = dA t₀ ch ∧ 1 ≤ (x.d ch).nnoise ∧ s.regs.get64 .rax = BitVec.ofNat 64 (x.d ch).nnoise ∧ s.regs.get64 .rdx = BitVec.ofNat 64 x.nq ∧ 1 ≤ x.nq ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrDq ch nch x t₀))
/-- ff_aac_sbr_apply.L7226 -/
abbrev L7226 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ ∃ ch nch : Nat, ch < nch ∧ nch ≤ 2 ∧ s.regs.get64 .r13 = dA t₀ ch ∧ 1 ≤ (x.d ch).nnoise ∧ s.regs.get64 .rax = BitVec.ofNat 64 (x.d ch).nnoise ∧ s.regs.get64 .rdx = BitVec.ofNat 64 x.nq ∧ 1 ≤ x.nq ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrDq ch nch x t₀))
/-- ff_aac_sbr_apply.L723c -/
abbrev L723c (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ ∃ ch nch : Nat, ch < nch ∧ nch ≤ 2 ∧ s.regs.get64 .r13 = dA t₀ ch ∧ 1 ≤ (x.d ch).nnoise ∧ s.regs.get64 .rax = BitVec.ofNat 64 (x.d ch).nnoise ∧ s.regs.get64 .rdx = BitVec.ofNat 64 x.nq ∧ 1 ≤ x.nq ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrDq ch nch x t₀))
/-- ff_aac_sbr_apply.L723c_1 -/
abbrev L723c_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ ∃ ch nch : Nat, ch < nch ∧ nch ≤ 2 ∧ s.regs.get64 .r13 = dA t₀ ch ∧ 1 ≤ (x.d ch).nnoise ∧ s.regs.get64 .rax = BitVec.ofNat 64 (x.d ch).nnoise ∧ s.regs.get64 .rdx = BitVec.ofNat 64 x.nq ∧ 2 ≤ x.nq ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrDq ch nch x t₀))
/-- ff_aac_sbr_apply.L7270 -/
abbrev L7270 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ ∃ ch nch : Nat, ch < nch ∧ nch ≤ 2 ∧ s.regs.get64 .r13 = dA t₀ ch ∧ 1 ≤ (x.d ch).nnoise ∧ s.regs.get64 .rax = BitVec.ofNat 64 (x.d ch).nnoise ∧ s.regs.get64 .rdx = BitVec.ofNat 64 x.nq ∧ 2 ≤ x.nq ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrDq ch nch x t₀))
/-- ff_aac_sbr_apply.L7286 -/
abbrev L7286 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ ∃ ch nch : Nat, ch < nch ∧ nch ≤ 2 ∧ s.regs.get64 .r13 = dA t₀ ch ∧ 1 ≤ (x.d ch).nnoise ∧ s.regs.get64 .rax = BitVec.ofNat 64 (x.d ch).nnoise ∧ s.regs.get64 .rdx = BitVec.ofNat 64 x.nq ∧ 2 ≤ x.nq ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrDq ch nch x t₀))
/-- ff_aac_sbr_apply.L7286_1 -/
abbrev L7286_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ ∃ ch nch : Nat, ch < nch ∧ nch ≤ 2 ∧ s.regs.get64 .r13 = dA t₀ ch ∧ 1 ≤ (x.d ch).nnoise ∧ s.regs.get64 .rax = BitVec.ofNat 64 (x.d ch).nnoise ∧ s.regs.get64 .rdx = BitVec.ofNat 64 x.nq ∧ 3 ≤ x.nq ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrDq ch nch x t₀))
/-- ff_aac_sbr_apply.L72ba -/
abbrev L72ba (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ ∃ ch nch : Nat, ch < nch ∧ nch ≤ 2 ∧ s.regs.get64 .r13 = dA t₀ ch ∧ 1 ≤ (x.d ch).nnoise ∧ s.regs.get64 .rax = BitVec.ofNat 64 (x.d ch).nnoise ∧ s.regs.get64 .rdx = BitVec.ofNat 64 x.nq ∧ 3 ≤ x.nq ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrDq ch nch x t₀))
/-- ff_aac_sbr_apply.L72d0 -/
abbrev L72d0 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ ∃ ch nch : Nat, ch < nch ∧ nch ≤ 2 ∧ s.regs.get64 .r13 = dA t₀ ch ∧ 1 ≤ (x.d ch).nnoise ∧ s.regs.get64 .rax = BitVec.ofNat 64 (x.d ch).nnoise ∧ s.regs.get64 .rdx = BitVec.ofNat 64 x.nq ∧ 3 ≤ x.nq ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrDq ch nch x t₀))
/-- ff_aac_sbr_apply.L72d0_1 -/
abbrev L72d0_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ ∃ ch nch : Nat, ch < nch ∧ nch ≤ 2 ∧ s.regs.get64 .r13 = dA t₀ ch ∧ 1 ≤ (x.d ch).nnoise ∧ s.regs.get64 .rax = BitVec.ofNat 64 (x.d ch).nnoise ∧ s.regs.get64 .rdx = BitVec.ofNat 64 x.nq ∧ 4 ≤ x.nq ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrDq ch nch x t₀))
/-- ff_aac_sbr_apply.L7304 -/
abbrev L7304 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ ∃ ch nch : Nat, ch < nch ∧ nch ≤ 2 ∧ s.regs.get64 .r13 = dA t₀ ch ∧ 1 ≤ (x.d ch).nnoise ∧ s.regs.get64 .rax = BitVec.ofNat 64 (x.d ch).nnoise ∧ s.regs.get64 .rdx = BitVec.ofNat 64 x.nq ∧ 4 ≤ x.nq ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrDq ch nch x t₀))
/-- ff_aac_sbr_apply.L731a -/
abbrev L731a (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ ∃ ch nch : Nat, ch < nch ∧ nch ≤ 2 ∧ s.regs.get64 .r13 = dA t₀ ch ∧ 1 ≤ (x.d ch).nnoise ∧ s.regs.get64 .rax = BitVec.ofNat 64 (x.d ch).nnoise ∧ s.regs.get64 .rdx = BitVec.ofNat 64 x.nq ∧ 4 ≤ x.nq ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrDq ch nch x t₀))
/-- ff_aac_sbr_apply.L731a_1 -/
abbrev L731a_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ ∃ ch nch : Nat, ch < nch ∧ nch ≤ 2 ∧ s.regs.get64 .r13 = dA t₀ ch ∧ 1 ≤ (x.d ch).nnoise ∧ s.regs.get64 .rax = BitVec.ofNat 64 (x.d ch).nnoise ∧ s.regs.get64 .rdx = BitVec.ofNat 64 x.nq ∧ 5 ≤ x.nq ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrDq ch nch x t₀))
/-- ff_aac_sbr_apply.L734a -/
abbrev L734a (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ ∃ ch nch : Nat, ch < nch ∧ nch ≤ 2 ∧ s.regs.get64 .r13 = dA t₀ ch ∧ 1 ≤ (x.d ch).nnoise ∧ s.regs.get64 .rax = BitVec.ofNat 64 (x.d ch).nnoise ∧ s.regs.get64 .rdx = BitVec.ofNat 64 x.nq ∧ 5 ≤ x.nq ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrDq ch nch x t₀))
/-- ff_aac_sbr_apply.L7360 -/
abbrev L7360 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ ∃ ch nch : Nat, ch < nch ∧ nch ≤ 2 ∧ s.regs.get64 .r13 = dA t₀ ch ∧ 1 ≤ (x.d ch).nnoise ∧ s.regs.get64 .rax = BitVec.ofNat 64 (x.d ch).nnoise ∧ s.regs.get64 .rdx = BitVec.ofNat 64 x.nq ∧ 5 ≤ x.nq ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrDq ch nch x t₀))
/-- ff_aac_sbr_apply.L7370 -/
abbrev L7370 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ ∃ ch nch : Nat, ch < nch ∧ nch ≤ 2 ∧ s.regs.get64 .r13 = dA t₀ ch ∧ 1 ≤ (x.d ch).nnoise ∧ s.regs.get64 .rax = BitVec.ofNat 64 (x.d ch).nnoise ∧ s.regs.get64 .rdx = BitVec.ofNat 64 x.nq ∧ 1 ≤ x.nq ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrDq ch nch x t₀))
/-- ff_aac_sbr_apply.L73a1 -/
abbrev L73a1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ ∃ ch nch : Nat, ch < nch ∧ nch ≤ 2 ∧ s.regs.get64 .r13 = dA t₀ ch ∧ (x.d ch).nnoise = 2 ∧ s.regs.get64 .rax = 3#64 ∧ s.regs.get64 .rdx = BitVec.ofNat 64 x.nq ∧ 1 ≤ x.nq ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrDq ch nch x t₀))
/-- ff_aac_sbr_apply.L73b7 -/
abbrev L73b7 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ ∃ ch nch : Nat, ch < nch ∧ nch ≤ 2 ∧ s.regs.get64 .r13 = dA t₀ ch ∧ (x.d ch).nnoise = 2 ∧ s.regs.get64 .rax = 3#64 ∧ s.regs.get64 .rdx = BitVec.ofNat 64 x.nq ∧ 1 ≤ x.nq ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrDq ch nch x t₀))
/-- ff_aac_sbr_apply.L73b7_1 -/
abbrev L73b7_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ ∃ ch nch : Nat, ch < nch ∧ nch ≤ 2 ∧ s.regs.get64 .r13 = dA t₀ ch ∧ (x.d ch).nnoise = 2 ∧ s.regs.get64 .rax = 3#64 ∧ s.regs.get64 .rdx = BitVec.ofNat 64 x.nq ∧ 2 ≤ x.nq ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrDq ch nch x t₀))
/-- ff_aac_sbr_apply.L73eb -/
abbrev L73eb (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ ∃ ch nch : Nat, ch < nch ∧ nch ≤ 2 ∧ s.regs.get64 .r13 = dA t₀ ch ∧ (x.d ch).nnoise = 2 ∧ s.regs.get64 .rax = 3#64 ∧ s.regs.get64 .rdx = BitVec.ofNat 64 x.nq ∧ 2 ≤ x.nq ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrDq ch nch x t₀))
/-- ff_aac_sbr_apply.L7401 -/
abbrev L7401 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ ∃ ch nch : Nat, ch < nch ∧ nch ≤ 2 ∧ s.regs.get64 .r13 = dA t₀ ch ∧ (x.d ch).nnoise = 2 ∧ s.regs.get64 .rax = 3#64 ∧ s.regs.get64 .rdx = BitVec.ofNat 64 x.nq ∧ 2 ≤ x.nq ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrDq ch nch x t₀))
/-- ff_aac_sbr_apply.L7401_1 -/
abbrev L7401_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ ∃ ch nch : Nat, ch < nch ∧ nch ≤ 2 ∧ s.regs.get64 .r13 = dA t₀ ch ∧ (x.d ch).nnoise = 2 ∧ s.regs.get64 .rax = 3#64 ∧ s.regs.get64 .rdx = BitVec.ofNat 64 x.nq ∧ 3 ≤ x.nq ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrDq ch nch x t₀))
/-- ff_aac_sbr_apply.L7435 -/
abbrev L7435 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ ∃ ch nch : Nat, ch < nch ∧ nch ≤ 2 ∧ s.regs.get64 .r13 = dA t₀ ch ∧ (x.d ch).nnoise = 2 ∧ s.regs.get64 .rax = 3#64 ∧ s.regs.get64 .rdx = BitVec.ofNat 64 x.nq ∧ 3 ≤ x.nq ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrDq ch nch x t₀))
/-- ff_aac_sbr_apply.L744b -/
abbrev L744b (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ ∃ ch nch : Nat, ch < nch ∧ nch ≤ 2 ∧ s.regs.get64 .r13 = dA t₀ ch ∧ (x.d ch).nnoise = 2 ∧ s.regs.get64 .rax = 3#64 ∧ s.regs.get64 .rdx = BitVec.ofNat 64 x.nq ∧ 3 ≤ x.nq ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrDq ch nch x t₀))
/-- ff_aac_sbr_apply.L744b_1 -/
abbrev L744b_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ ∃ ch nch : Nat, ch < nch ∧ nch ≤ 2 ∧ s.regs.get64 .r13 = dA t₀ ch ∧ (x.d ch).nnoise = 2 ∧ s.regs.get64 .rax = 3#64 ∧ s.regs.get64 .rdx = BitVec.ofNat 64 x.nq ∧ 4 ≤ x.nq ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrDq ch nch x t₀))
/-- ff_aac_sbr_apply.L747f -/
abbrev L747f (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ ∃ ch nch : Nat, ch < nch ∧ nch ≤ 2 ∧ s.regs.get64 .r13 = dA t₀ ch ∧ (x.d ch).nnoise = 2 ∧ s.regs.get64 .rax = 3#64 ∧ s.regs.get64 .rdx = BitVec.ofNat 64 x.nq ∧ 4 ≤ x.nq ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrDq ch nch x t₀))
/-- ff_aac_sbr_apply.L7495 -/
abbrev L7495 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ ∃ ch nch : Nat, ch < nch ∧ nch ≤ 2 ∧ s.regs.get64 .r13 = dA t₀ ch ∧ (x.d ch).nnoise = 2 ∧ s.regs.get64 .rax = 3#64 ∧ s.regs.get64 .rdx = BitVec.ofNat 64 x.nq ∧ 4 ≤ x.nq ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrDq ch nch x t₀))
/-- ff_aac_sbr_apply.L7495_1 -/
abbrev L7495_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ ∃ ch nch : Nat, ch < nch ∧ nch ≤ 2 ∧ s.regs.get64 .r13 = dA t₀ ch ∧ (x.d ch).nnoise = 2 ∧ s.regs.get64 .rax = 3#64 ∧ s.regs.get64 .rdx = BitVec.ofNat 64 x.nq ∧ 5 ≤ x.nq ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrDq ch nch x t₀))
/-- ff_aac_sbr_apply.L74de -/
abbrev L74de (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => (ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L74e9 -/
abbrev L74e9 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ ∃ y : Args, (x.Keep y ∧ IdLive t₀ y) ∧ ApplyC y t₀ ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrD x t₀))
/-- ff_aac_sbr_apply.L74e9_1 -/
abbrev L74e9_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ s.regs.get64 .rax = lab "_GLOBAL_OFFSET_TABLE_" ∧ ∃ y : Args, (x.Keep y ∧ IdLive t₀ y) ∧ ApplyC y t₀ ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrS1 x t₀))
/-- ff_aac_sbr_apply.L74e9_2 -/
abbrev L74e9_2 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ s.regs.get64 .rax = lab "_GLOBAL_OFFSET_TABLE_" ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5fcc0#64 ∧ s.regs.get64 .r13 = sbrA t₀ + 0x5fdc0#64 ∧ ∃ y : Args, (x.Keep y ∧ IdLive t₀ y) ∧ ApplyC y t₀ ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrS2 x t₀))
/-- ff_aac_sbr_apply.L74e9_3 -/
abbrev L74e9_3 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5fcc0#64 ∧ s.regs.get64 .r13 = sbrA t₀ + 0x5fdc0#64 ∧ s.regs.get64 .r15 = lab "sbr_qmf_window_ds" ∧ s.regs.get64 .rax = sbrA t₀ + 0x1c#64 ∧ ∃ y : Args, (x.Keep y ∧ IdLive t₀ y) ∧ ApplyC y t₀ ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrS3 x t₀))
/-- ff_aac_sbr_apply.L74e9_4 -/
abbrev L74e9_4 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5fcc0#64 ∧ s.regs.get64 .r13 = sbrA t₀ + 0x5fdc0#64 ∧ s.regs.get64 .r15 = lab "sbr_qmf_window_ds" ∧ ∃ y : Args, (x.Keep y ∧ IdLive t₀ y) ∧ ApplyC y t₀ ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrS4 x t₀))
/-- ff_aac_sbr_apply.L7682 -/
abbrev L7682 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch, ApplyC x t₀ ∧ Base t₀ s ∧ ch < 2 ∧ s.regs.get64 .r9 = arg1 t₀ ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5fcc0#64 ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (ch) ∧ (s.regs.get64 .rcx).getLsbD 0 = decide (ch = 0) ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrL x t₀))
/-- ff_aac_sbr_apply.L7682_1 -/
abbrev L7682_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch, ApplyC x t₀ ∧ Base t₀ s ∧ ch < 2 ∧ s.regs.get64 .r9 = arg1 t₀ ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5fcc0#64 ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (ch) ∧ (s.regs.get64 .rcx).getLsbD 0 = decide (ch = 0) ∧ s.regs.get64 .r14 = sbrA t₀ + 0x5fcc0#64 ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrAn1 x t₀))
/-- ff_aac_sbr_apply.L7682_2 -/
abbrev L7682_2 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch, ApplyC x t₀ ∧ Base t₀ s ∧ ch < 2 ∧ s.regs.get64 .r9 = arg1 t₀ ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5fcc0#64 ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (ch) ∧ (s.regs.get64 .rcx).getLsbD 0 = decide (ch = 0) ∧ s.regs.get64 .r14 = sbrA t₀ + 0x5fcc0#64 ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrA2 x t₀))
/-- ff_aac_sbr_apply.L7682_3 -/
abbrev L7682_3 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0, ApplyC x t₀ ∧ Base t₀ s ∧ ch < 2 ∧ c0.getLsbD 0 = decide (ch = 0) ∧ s.regs.get64 .r9 = arg1 t₀ ∧ s.regs.get64 .r14 = sbrA t₀ + 0x5fcc0#64 ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (ch) ∧ s.status.zf = decide (ch ≠ 0) ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrA3 x t₀ e ch c0))
/-- ff_aac_sbr_apply.L7682_4 -/
abbrev L7682_4 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0, ApplyC x t₀ ∧ Base t₀ s ∧ ch < 2 ∧ c0.getLsbD 0 = decide (ch = 0) ∧ s.regs.get64 .r9 = arg1 t₀ ∧ s.regs.get64 .r14 = sbrA t₀ + 0x5fcc0#64 ∧ s.regs.get64 .r13 = BitVec.ofNat 64 (0x15ac0 * ch) ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrA4 x t₀ e ch c0))
/-- ff_aac_sbr_apply.L7682_5 -/
abbrev L7682_5 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0, ApplyC x t₀ ∧ Base t₀ s ∧ ch < 2 ∧ c0.getLsbD 0 = decide (ch = 0) ∧ s.regs.get64 .r9 = arg1 t₀ ∧ s.regs.get64 .r14 = sbrA t₀ + 0x5fcc0#64 ∧ s.regs.get64 .r13 = BitVec.ofNat 64 (0x15ac0 * ch) ∧ s.regs.get64 .rcx = sbrA t₀ + 0x80#64 ∧ s.regs.get64 .rdi = dA t₀ ch + 0x2480#64 ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrA5 x t₀ e ch c0))
/-- ff_aac_sbr_apply.L7682_6 -/
abbrev L7682_6 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0, ApplyC x t₀ ∧ Base t₀ s ∧ ch < 2 ∧ c0.getLsbD 0 = decide (ch = 0) ∧ s.regs.get64 .r14 = sbrA t₀ + 0x5fcc0#64 ∧ s.regs.get64 .r12 = dA t₀ ch + 0x2480#64 ∧ s.regs.get64 .rbx = arg1 t₀ ∧ s.regs.get64 .r13 = BitVec.ofNat 64 (0x15ac0 * ch) ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ s.regs.get64 .r15 = BitVec.ofNat 64 ((y.d ch).ypos) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrA5 x t₀ e ch c0))
/-- ff_aac_sbr_apply.L7682_7 -/
abbrev L7682_7 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0, ApplyC x t₀ ∧ Base t₀ s ∧ ch < 2 ∧ c0.getLsbD 0 = decide (ch = 0) ∧ s.regs.get64 .r14 = sbrA t₀ + 0x5fcc0#64 ∧ s.regs.get64 .r12 = dA t₀ ch + 0x2480#64 ∧ s.regs.get64 .rbx = arg1 t₀ ∧ s.regs.get64 .r13 = BitVec.ofNat 64 (0x15ac0 * ch) ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ s.regs.get64 .r15 = BitVec.ofNat 64 ((y.d ch).ypos) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrA6 x t₀ e ch c0))
/-- ff_aac_sbr_apply.L7682_8 -/
abbrev L7682_8 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0, ApplyC x t₀ ∧ Base t₀ s ∧ ch < 2 ∧ c0.getLsbD 0 = decide (ch = 0) ∧ s.regs.get64 .r14 = sbrA t₀ + 0x5fcc0#64 ∧ s.regs.get64 .r12 = dA t₀ ch + 0x2480#64 ∧ s.regs.get64 .rbx = arg1 t₀ ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ s.regs.get64 .r15 = BitVec.ofNat 64 ((y.d ch).ypos) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrA6 x t₀ e ch c0))
/-- ff_aac_sbr_apply.L7750 -/
abbrev L7750 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0 i, ApplyC x t₀ ∧ Base t₀ s ∧ ch < 2 ∧ c0.getLsbD 0 = decide (ch = 0) ∧ i < 32 ∧ s.regs.get64 .r12 = dA t₀ ch + 0x2480#64 ∧ s.regs.get64 .r13 = BitVec.ofNat 64 (128 * i) ∧ s.regs.get64 .r14 = sbrA t₀ + 0x5fcc0#64 ∧ s.regs.get64 .rbx = arg1 t₀ ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ s.regs.get64 .r15 = dA t₀ ch + 0x3920#64 + BitVec.ofNat 64 (8192 * (y.d ch).ypos + 256 * i) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrA6 x t₀ e ch c0))
/-- ff_aac_sbr_apply.L7750_1 -/
abbrev L7750_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0 i, ApplyC x t₀ ∧ Base t₀ s ∧ ch < 2 ∧ c0.getLsbD 0 = decide (ch = 0) ∧ i < 32 ∧ s.regs.get64 .r12 = dA t₀ ch + 0x2480#64 ∧ s.regs.get64 .r13 = BitVec.ofNat 64 (128 * i) ∧ s.regs.get64 .r14 = sbrA t₀ + 0x5fcc0#64 ∧ s.regs.get64 .rbx = arg1 t₀ ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ s.regs.get64 .r15 = dA t₀ ch + 0x3920#64 + BitVec.ofNat 64 (8192 * (y.d ch).ypos + 256 * i) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrA6 x t₀ e ch c0))
/-- ff_aac_sbr_apply.L7750_2 -/
abbrev L7750_2 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0 i, ApplyC x t₀ ∧ Base t₀ s ∧ ch < 2 ∧ c0.getLsbD 0 = decide (ch = 0) ∧ i < 32 ∧ s.regs.get64 .r12 = dA t₀ ch + 0x2480#64 ∧ s.regs.get64 .r13 = BitVec.ofNat 64 (128 * i) ∧ s.regs.get64 .r14 = sbrA t₀ + 0x5fcc0#64 ∧ s.regs.get64 .rbx = arg1 t₀ ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ s.regs.get64 .r15 = dA t₀ ch + 0x3920#64 + BitVec.ofNat 64 (8192 * (y.d ch).ypos + 256 * i) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrA6 x t₀ e ch c0))
/-- ff_aac_sbr_apply.L7750_3 -/
abbrev L7750_3 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0 i, ApplyC x t₀ ∧ Base t₀ s ∧ ch < 2 ∧ c0.getLsbD 0 = decide (ch = 0) ∧ i < 32 ∧ s.regs.get64 .r12 = dA t₀ ch + 0x2480#64 ∧ s.regs.get64 .r13 = BitVec.ofNat 64 (128 * i) ∧ s.regs.get64 .r14 = sbrA t₀ + 0x5fcc0#64 ∧ s.regs.get64 .rbx = arg1 t₀ ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ s.regs.get64 .r15 = dA t₀ ch + 0x3920#64 + BitVec.ofNat 64 (8192 * (y.d ch).ypos + 256 * i) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrA6 x t₀ e ch c0))
/-- ff_aac_sbr_apply.L7750_4 -/
abbrev L7750_4 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0 i, ApplyC x t₀ ∧ Base t₀ s ∧ ch < 2 ∧ c0.getLsbD 0 = decide (ch = 0) ∧ i < 32 ∧ s.regs.get64 .r12 = dA t₀ ch + 0x2480#64 ∧ s.regs.get64 .r13 = BitVec.ofNat 64 (128 * i) ∧ s.regs.get64 .r14 = sbrA t₀ + 0x5fcc0#64 ∧ s.regs.get64 .rbx = arg1 t₀ ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ s.regs.get64 .r15 = dA t₀ ch + 0x3920#64 + BitVec.ofNat 64 (8192 * (y.d ch).ypos + 256 * i) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrA6 x t₀ e ch c0))
/-- ff_aac_sbr_apply.L7750_5 -/
abbrev L7750_5 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0 i, ApplyC x t₀ ∧ Base t₀ s ∧ ch < 2 ∧ c0.getLsbD 0 = decide (ch = 0) ∧ i < 32 ∧ s.regs.get64 .r12 = dA t₀ ch + 0x2480#64 ∧ s.regs.get64 .r13 = BitVec.ofNat 64 (128 * i) ∧ s.regs.get64 .r14 = sbrA t₀ + 0x5fcc0#64 ∧ s.regs.get64 .rbx = arg1 t₀ ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ s.regs.get64 .r15 = dA t₀ ch + 0x3920#64 + BitVec.ofNat 64 (8192 * (y.d ch).ypos + 256 * i) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrA6 x t₀ e ch c0))
/-- ff_aac_sbr_apply.L7750_6 -/
abbrev L7750_6 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0, ApplyC x t₀ ∧ Base t₀ s ∧ ch < 2 ∧ c0.getLsbD 0 = decide (ch = 0) ∧ s.regs.get64 .r14 = sbrA t₀ + 0x5fcc0#64 ∧ s.regs.get64 .r15 = dA t₀ ch ∧ s.regs.get64 .rbx = arg1 t₀ ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrA6 x t₀ e ch c0))
/-- ff_aac_sbr_apply.L7750_7 -/
abbrev L7750_7 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0, ApplyC x t₀ ∧ Base t₀ s ∧ ch < 2 ∧ c0.getLsbD 0 = decide (ch = 0) ∧ s.regs.get64 .r14 = sbrA t₀ + 0x5fcc0#64 ∧ s.regs.get64 .r15 = dA t₀ ch ∧ s.regs.get64 .rbx = arg1 t₀ ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ (s.regs.get64 .rax).toNat % 2^32 = (y.d ch).ypos ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrA6 x t₀ e ch c0))
/-- ff_aac_sbr_apply.L7750_8 -/
abbrev L7750_8 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0, ApplyC x t₀ ∧ Base t₀ s ∧ ch < 2 ∧ c0.getLsbD 0 = decide (ch = 0) ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ y.start ≠ 0 ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrA6 x t₀ e ch c0))
/-- ff_aac_sbr_apply.L7866 -/
abbrev L7866 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0, ApplyC x t₀ ∧ Base t₀ s ∧ ch < 2 ∧ c0.getLsbD 0 = decide (ch = 0) ∧ s.regs.get64 .r8 = arg1 t₀ ∧ s.regs.get64 .rbx = dA t₀ ch ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ y.start ≠ 0 ∧ s.regs.get64 .rax = BitVec.ofNat 64 (y.nq) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrA6 x t₀ e ch c0))
/-- ff_aac_sbr_apply.L7884 -/
abbrev L7884 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0, ApplyC x t₀ ∧ Base t₀ s ∧ ch < 2 ∧ c0.getLsbD 0 = decide (ch = 0) ∧ s.regs.get64 .r8 = arg1 t₀ ∧ s.regs.get64 .rbx = dA t₀ ch ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ y.start ≠ 0 ∧ s.regs.get64 .rax = BitVec.ofNat 64 (y.nq) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrA6 x t₀ e ch c0))
/-- ff_aac_sbr_apply.L7884_1 -/
abbrev L7884_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0, ApplyC x t₀ ∧ Base t₀ s ∧ ch < 2 ∧ c0.getLsbD 0 = decide (ch = 0) ∧ s.regs.get64 .r8 = arg1 t₀ ∧ s.regs.get64 .rbx = dA t₀ ch ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ y.start ≠ 0 ∧ s.regs.get64 .rax = BitVec.ofNat 64 (y.nq) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrA6 x t₀ e ch c0))
/-- ff_aac_sbr_apply.L78f2 -/
abbrev L78f2 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0, ApplyC x t₀ ∧ Base t₀ s ∧ ch < 2 ∧ c0.getLsbD 0 = decide (ch = 0) ∧ s.regs.get64 .r8 = arg1 t₀ ∧ s.regs.get64 .rbx = dA t₀ ch ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ y.start ≠ 0 ∧ s.regs.get64 .rax = BitVec.ofNat 64 (y.nq) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrA6 x t₀ e ch c0))
/-- ff_aac_sbr_apply.L7910 -/
abbrev L7910 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0, ApplyC x t₀ ∧ Base t₀ s ∧ ch < 2 ∧ c0.getLsbD 0 = decide (ch = 0) ∧ s.regs.get64 .r8 = arg1 t₀ ∧ s.regs.get64 .rbx = dA t₀ ch ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ y.start ≠ 0 ∧ s.regs.get64 .rax = BitVec.ofNat 64 (y.nq) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrA6 x t₀ e ch c0))
/-- ff_aac_sbr_apply.L7910_1 -/
abbrev L7910_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0, ApplyC x t₀ ∧ Base t₀ s ∧ ch < 2 ∧ c0.getLsbD 0 = decide (ch = 0) ∧ s.regs.get64 .r8 = arg1 t₀ ∧ s.regs.get64 .rbx = dA t₀ ch ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ y.start ≠ 0 ∧ s.regs.get64 .rax = BitVec.ofNat 64 (y.nq) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrA6 x t₀ e ch c0))
/-- ff_aac_sbr_apply.L797e -/
abbrev L797e (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0, ApplyC x t₀ ∧ Base t₀ s ∧ ch < 2 ∧ c0.getLsbD 0 = decide (ch = 0) ∧ s.regs.get64 .r8 = arg1 t₀ ∧ s.regs.get64 .rbx = dA t₀ ch ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ y.start ≠ 0 ∧ s.regs.get64 .rax = BitVec.ofNat 64 (y.nq) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrA6 x t₀ e ch c0))
/-- ff_aac_sbr_apply.L799c -/
abbrev L799c (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0, ApplyC x t₀ ∧ Base t₀ s ∧ ch < 2 ∧ c0.getLsbD 0 = decide (ch = 0) ∧ s.regs.get64 .r8 = arg1 t₀ ∧ s.regs.get64 .rbx = dA t₀ ch ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ y.start ≠ 0 ∧ s.regs.get64 .rax = BitVec.ofNat 64 (y.nq) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrA6 x t₀ e ch c0))
/-- ff_aac_sbr_apply.L799c_1 -/
abbrev L799c_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0, ApplyC x t₀ ∧ Base t₀ s ∧ ch < 2 ∧ c0.getLsbD 0 = decide (ch = 0) ∧ s.regs.get64 .r8 = arg1 t₀ ∧ s.regs.get64 .rbx = dA t₀ ch ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ y.start ≠ 0 ∧ s.regs.get64 .rax = BitVec.ofNat 64 (y.nq) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrA6 x t₀ e ch c0))
/-- ff_aac_sbr_apply.L7a0a -/
abbrev L7a0a (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0, ApplyC x t₀ ∧ Base t₀ s ∧ ch < 2 ∧ c0.getLsbD 0 = decide (ch = 0) ∧ s.regs.get64 .r8 = arg1 t₀ ∧ s.regs.get64 .rbx = dA t₀ ch ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ y.start ≠ 0 ∧ s.regs.get64 .rax = BitVec.ofNat 64 (y.nq) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrA6 x t₀ e ch c0))
/-- ff_aac_sbr_apply.L7a28 -/
abbrev L7a28 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0, ApplyC x t₀ ∧ Base t₀ s ∧ ch < 2 ∧ c0.getLsbD 0 = decide (ch = 0) ∧ s.regs.get64 .r8 = arg1 t₀ ∧ s.regs.get64 .rbx = dA t₀ ch ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ y.start ≠ 0 ∧ s.regs.get64 .rax = BitVec.ofNat 64 (y.nq) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrA6 x t₀ e ch c0))
/-- ff_aac_sbr_apply.L7a28_1 -/
abbrev L7a28_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0, ApplyC x t₀ ∧ Base t₀ s ∧ ch < 2 ∧ c0.getLsbD 0 = decide (ch = 0) ∧ s.regs.get64 .r8 = arg1 t₀ ∧ s.regs.get64 .rbx = dA t₀ ch ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ y.start ≠ 0 ∧ s.regs.get64 .rax = BitVec.ofNat 64 (y.nq) ∧ 5 ≤ y.nq ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrA6 x t₀ e ch c0))
/-- ff_aac_sbr_apply.L7a96 -/
abbrev L7a96 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0, ApplyC x t₀ ∧ Base t₀ s ∧ ch < 2 ∧ c0.getLsbD 0 = decide (ch = 0) ∧ s.regs.get64 .r8 = arg1 t₀ ∧ s.regs.get64 .rbx = dA t₀ ch ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ y.start ≠ 0 ∧ s.regs.get64 .rax = BitVec.ofNat 64 (y.nq) ∧ 5 ≤ y.nq ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrA6 x t₀ e ch c0))
/-- ff_aac_sbr_apply.L7ab4 -/
abbrev L7ab4 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0, ApplyC x t₀ ∧ Base t₀ s ∧ ch < 2 ∧ c0.getLsbD 0 = decide (ch = 0) ∧ s.regs.get64 .r8 = arg1 t₀ ∧ s.regs.get64 .rbx = dA t₀ ch ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ y.start ≠ 0 ∧ s.regs.get64 .rax = BitVec.ofNat 64 (y.nq) ∧ 5 ≤ y.nq ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrA6 x t₀ e ch c0))
/-- ff_aac_sbr_apply.L7b00 -/
abbrev L7b00 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0, ApplyC x t₀ ∧ Base t₀ s ∧ ch < 2 ∧ c0.getLsbD 0 = decide (ch = 0) ∧ s.regs.get64 .r8 = arg1 t₀ ∧ s.regs.get64 .rbx = dA t₀ ch ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ y.start ≠ 0 ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrA6 x t₀ e ch c0))
/-- ff_aac_sbr_apply.L7b00_1 -/
abbrev L7b00_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0 ne, ApplyC x t₀ ∧ Base t₀ s ∧ ch < 2 ∧ c0.getLsbD 0 = decide (ch = 0) ∧ s.regs.get64 .r8 = arg1 t₀ ∧ s.regs.get64 .rbx = dA t₀ ch ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ y.start ≠ 0 ∧ ne = (y.d ch).nenv ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrH x t₀ e ch c0 ne))
/-- ff_aac_sbr_apply.L7b2d -/
abbrev L7b2d (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0 ne j kk g, ApplyC x t₀ ∧ Base t₀ s ∧ ch < 2 ∧ c0.getLsbD 0 = decide (ch = 0) ∧ s.regs.get64 .r8 = arg1 t₀ ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .r15 = BitVec.ofNat 64 (j) ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (kk) ∧ s.regs.get64 .r13 = BitVec.ofNat 64 (g) ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ y.start ≠ 0 ∧ ne = (y.d ch).nenv ∧ j < y.npatch ∧ s.regs.get64 .rax = BitVec.ofNat 64 (y.npatch) ∧ g ≤ y.nq ∧ kk + ((List.range' (j) (y.npatch - (j))).map (fun i => u8 y.pnum i)).sum ≤ y.kx1 + y.m1 ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrH x t₀ e ch c0 ne))
/-- ff_aac_sbr_apply.L7b50 -/
abbrev L7b50 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0 ne j kk g xx, ApplyC x t₀ ∧ Base t₀ s ∧ ch < 2 ∧ c0.getLsbD 0 = decide (ch = 0) ∧ s.regs.get64 .r8 = arg1 t₀ ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .r15 = BitVec.ofNat 64 (j) ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (kk) ∧ s.regs.get64 .r14 = BitVec.ofNat 64 (xx) ∧ s.regs.get64 .r13 = BitVec.ofNat 64 (g) ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ y.start ≠ 0 ∧ ne = (y.d ch).nenv ∧ j < y.npatch ∧ xx < u8 y.pnum j ∧ kk + (u8 y.pnum j - xx) + ((List.range' (j + 1) (y.npatch - (j + 1))).map (fun i => u8 y.pnum i)).sum ≤ y.kx1 + y.m1 ∧ g ≤ y.nq ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrH x t₀ e ch c0 ne))
/-- ff_aac_sbr_apply.L7b80 -/
abbrev L7b80 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0 ne j kk xx gg, ApplyC x t₀ ∧ Base t₀ s ∧ ch < 2 ∧ c0.getLsbD 0 = decide (ch = 0) ∧ s.regs.get64 .r8 = arg1 t₀ ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .r15 = BitVec.ofNat 64 (j) ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (kk) ∧ s.regs.get64 .r14 = BitVec.ofNat 64 (xx) ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (gg) ∧ s.regs.get64 .rsi = 6#64 ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ y.start ≠ 0 ∧ ne = (y.d ch).nenv ∧ j < y.npatch ∧ xx < u8 y.pnum j ∧ kk + (u8 y.pnum j - xx) + ((List.range' (j + 1) (y.npatch - (j + 1))).map (fun i => u8 y.pnum i)).sum ≤ y.kx1 + y.m1 ∧ s.regs.get64 .rax = BitVec.ofNat 64 (u8 y.pstart j) ∧ gg < y.nq + 1 ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.nq + 1) ∧ s.regs.get64 .r13 = BitVec.ofNat 64 (y.nq + 1) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrH x t₀ e ch c0 ne))
/-- ff_aac_sbr_apply.L7bb0 -/
abbrev L7bb0 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0 ne j kk xx gg, ApplyC x t₀ ∧ Base t₀ s ∧ ch < 2 ∧ c0.getLsbD 0 = decide (ch = 0) ∧ s.regs.get64 .r8 = arg1 t₀ ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .r15 = BitVec.ofNat 64 (j) ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (kk) ∧ s.regs.get64 .r14 = BitVec.ofNat 64 (xx) ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (gg) ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ y.start ≠ 0 ∧ ne = (y.d ch).nenv ∧ j < y.npatch ∧ xx < u8 y.pnum j ∧ kk + (u8 y.pnum j - xx) + ((List.range' (j + 1) (y.npatch - (j + 1))).map (fun i => u8 y.pnum i)).sum ≤ y.kx1 + y.m1 ∧ s.regs.get64 .rax = BitVec.ofNat 64 (u8 y.pstart j) ∧ gg < y.nq + 1 ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrH x t₀ e ch c0 ne))
/-- ff_aac_sbr_apply.L7bb3 -/
abbrev L7bb3 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0 ne j kk g xx, ApplyC x t₀ ∧ Base t₀ s ∧ ch < 2 ∧ c0.getLsbD 0 = decide (ch = 0) ∧ s.regs.get64 .r8 = arg1 t₀ ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .r15 = BitVec.ofNat 64 (j) ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (kk) ∧ s.regs.get64 .r14 = BitVec.ofNat 64 (xx) ∧ s.regs.get64 .r13 = BitVec.ofNat 64 (g) ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ y.start ≠ 0 ∧ ne = (y.d ch).nenv ∧ j < y.npatch ∧ xx < u8 y.pnum j ∧ kk + (u8 y.pnum j - xx) + ((List.range' (j + 1) (y.npatch - (j + 1))).map (fun i => u8 y.pnum i)).sum ≤ y.kx1 + y.m1 ∧ s.regs.get64 .rax = BitVec.ofNat 64 (u8 y.pstart j) ∧ g ≤ y.nq ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrH x t₀ e ch c0 ne))
/-- ff_aac_sbr_apply.L7bb3_1 -/
abbrev L7bb3_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0 ne j kk g xx, ApplyC x t₀ ∧ Base t₀ s ∧ ch < 2 ∧ c0.getLsbD 0 = decide (ch = 0) ∧ s.regs.get64 .r8 = arg1 t₀ ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .r15 = BitVec.ofNat 64 (j) ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (kk) ∧ s.regs.get64 .r14 = BitVec.ofNat 64 (xx) ∧ s.regs.get64 .r13 = BitVec.ofNat 64 (g) ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ y.start ≠ 0 ∧ ne = (y.d ch).nenv ∧ j < y.npatch ∧ xx < u8 y.pnum j ∧ kk + (u8 y.pnum j - xx) + ((List.range' (j + 1) (y.npatch - (j + 1))).map (fun i => u8 y.pnum i)).sum ≤ y.kx1 + y.m1 ∧ g < y.nq ∧ s.regs.get64 .rax = BitVec.ofNat 64 ((u8 y.pstart j + xx)) ∧ s.regs.get64 .rdi = sbrA t₀ + 0x4eb40#64 + BitVec.ofNat 64 (320 * kk) + 16#64 ∧ s.regs.get64 .rsi = sbrA t₀ + 0x4c340#64 + BitVec.ofNat 64 (320 * (u8 y.pstart j + xx)) + 16#64 ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrH x t₀ e ch c0 ne))
/-- ff_aac_sbr_apply.L7bb3_2 -/
abbrev L7bb3_2 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0 ne j kk g xx, ApplyC x t₀ ∧ Base t₀ s ∧ ch < 2 ∧ c0.getLsbD 0 = decide (ch = 0) ∧ s.regs.get64 .rbx = arg1 t₀ ∧ s.regs.get64 .r15 = BitVec.ofNat 64 (j) ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (kk) ∧ s.regs.get64 .r14 = BitVec.ofNat 64 (xx) ∧ s.regs.get64 .r13 = BitVec.ofNat 64 (g) ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ y.start ≠ 0 ∧ ne = (y.d ch).nenv ∧ j < y.npatch ∧ xx < u8 y.pnum j ∧ kk + (u8 y.pnum j - xx) + ((List.range' (j + 1) (y.npatch - (j + 1))).map (fun i => u8 y.pnum i)).sum ≤ y.kx1 + y.m1 ∧ g < y.nq ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrH x t₀ e ch c0 ne))
/-- ff_aac_sbr_apply.L7c5d -/
abbrev L7c5d (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0 ne j kk g, ApplyC x t₀ ∧ Base t₀ s ∧ ch < 2 ∧ c0.getLsbD 0 = decide (ch = 0) ∧ s.regs.get64 .r8 = arg1 t₀ ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .r15 = BitVec.ofNat 64 (j) ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (kk) ∧ s.regs.get64 .r13 = BitVec.ofNat 64 (g) ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ y.start ≠ 0 ∧ ne = (y.d ch).nenv ∧ j < y.npatch ∧ s.regs.get64 .rax = BitVec.ofNat 64 (y.npatch) ∧ g ≤ y.nq ∧ kk + ((List.range' (j + 1) (y.npatch - (j + 1))).map (fun i => u8 y.pnum i)).sum ≤ y.kx1 + y.m1 ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrH x t₀ e ch c0 ne))
/-- ff_aac_sbr_apply.L7c80 -/
abbrev L7c80 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0 ne, ApplyC x t₀ ∧ Base t₀ s ∧ ch < 2 ∧ c0.getLsbD 0 = decide (ch = 0) ∧ s.regs.get64 .rbx = dA t₀ ch ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ y.start ≠ 0 ∧ ne = (y.d ch).nenv ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrH x t₀ e ch c0 ne))
/-- ff_aac_sbr_apply.L7c80_1 -/
abbrev L7c80_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0 ne, ApplyC x t₀ ∧ Base t₀ s ∧ ch < 2 ∧ c0.getLsbD 0 = decide (ch = 0) ∧ s.regs.get64 .rbx = dA t₀ ch ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ y.start ≠ 0 ∧ ne = (y.d ch).nenv ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrH x t₀ e ch c0 ne))
/-- ff_aac_sbr_apply.L7cb0 -/
abbrev L7cb0 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0 ne, ApplyC x t₀ ∧ Base t₀ s ∧ ch < 2 ∧ c0.getLsbD 0 = decide (ch = 0) ∧ s.regs.get64 .r8 = arg1 t₀ ∧ s.regs.get64 .rbx = dA t₀ ch ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ y.start ≠ 0 ∧ ne = (y.d ch).nenv ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (y.kx1) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrH x t₀ e ch c0 ne))
/-- ff_aac_sbr_apply.L7cbf -/
abbrev L7cbf (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0 ne kk cnt, ApplyC x t₀ ∧ Base t₀ s ∧ ch < 2 ∧ c0.getLsbD 0 = decide (ch = 0) ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (kk) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (cnt) ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ y.start ≠ 0 ∧ ne = (y.d ch).nenv ∧ kk + cnt ≤ 64 ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrH x t₀ e ch c0 ne))
/-- ff_aac_sbr_apply.L7ce0 -/
abbrev L7ce0 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0 ne, ApplyC x t₀ ∧ Base t₀ s ∧ ch < 2 ∧ c0.getLsbD 0 = decide (ch = 0) ∧ s.regs.get64 .rbx = dA t₀ ch ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ y.start ≠ 0 ∧ ne = (y.d ch).nenv ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrH x t₀ e ch c0 ne))
/-- ff_aac_sbr_apply.L7ce4 -/
abbrev L7ce4 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0, ApplyC x t₀ ∧ Base t₀ s ∧ ch < 2 ∧ c0.getLsbD 0 = decide (ch = 0) ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .r8 = arg1 t₀ ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ y.start ≠ 0 ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrC x t₀ ch c0))
/-- ff_aac_sbr_apply.L7ce4_1 -/
abbrev L7ce4_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j = 0 ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .r8 = arg1 t₀ ∧ s.regs.get64 .r10 = dA t₀ ch + 0x15030#64 ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrC x t₀ ch c0))
/-- ff_aac_sbr_apply.L7ce4_2 -/
abbrev L7ce4_2 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j = 0 ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .r8 = arg1 t₀ ∧ s.regs.get64 .r10 = dA t₀ ch + 0x15030#64 ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrC x t₀ ch c0))
/-- ff_aac_sbr_apply.L7ce4_3 -/
abbrev L7ce4_3 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j = 0 ∧ 0 < (y.d ch).nenv ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .r8 = arg1 t₀ ∧ s.regs.get64 .r10 = dA t₀ ch + 0x15030#64 ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrMA1 x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L7ce4_4 -/
abbrev L7ce4_4 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j = 0 ∧ 0 < (y.d ch).nenv ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .r8 = arg1 t₀ ∧ s.regs.get64 .r10 = dA t₀ ch + 0x15030#64 ∧ s.regs.get64 .r11 = dA t₀ ch + 0x32#64 ∧ s.regs.get64 .rcx = 1#64 ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrMA2 x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L7ce4_5 -/
abbrev L7ce4_5 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j = 0 ∧ 0 < (y.d ch).nenv ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .r8 = arg1 t₀ ∧ s.regs.get64 .r10 = dA t₀ ch + 0x15030#64 ∧ s.regs.get64 .r11 = dA t₀ ch + 0x32#64 ∧ s.regs.get64 .rcx = 1#64 ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrMA3 x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L7db0 -/
abbrev L7db0 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (j) ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (j + 1) ∧ s.regs.get64 .r8 = arg1 t₀ ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrM0 x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L7db0_1 -/
abbrev L7db0_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (j) ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .r14 = BitVec.ofNat 64 (j + 1) ∧ s.regs.get64 .r15 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ y.kx1 = u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (0) ∧ u8 (y.d ch).freqRes (j + 1) < 2 ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (u8 (y.d ch).freqRes (j + 1)) ∧ s.regs.get64 .r8 = arg1 t₀ ∧ s.regs.get64 .rdi = BitVec.ofNat 64 (u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (0)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrMB x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L7e20 -/
abbrev L7e20 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j i, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (j) ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .r14 = BitVec.ofNat 64 (j + 1) ∧ s.regs.get64 .r15 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ y.kx1 = u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (0) ∧ s.regs.get64 .rcx = dA t₀ ch + 0x15390#64 + BitVec.ofNat 64 (192 * (j + 1)) ∧ 1 ≤ i ∧ i ≤ (if u8 (y.d ch).freqRes (j + 1) = 0 then y.n0 else y.n1) ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (i) ∧ s.regs.get64 .r9 = BitVec.ofNat 64 (u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (i)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrME x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L7e29 -/
abbrev L7e29 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j i, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (j) ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .r14 = BitVec.ofNat 64 (j + 1) ∧ s.regs.get64 .r15 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ y.kx1 = u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (0) ∧ s.regs.get64 .rcx = dA t₀ ch + 0x15390#64 + BitVec.ofNat 64 (192 * (j + 1)) ∧ i < (if u8 (y.d ch).freqRes (j + 1) = 0 then y.n0 else y.n1) ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (i) ∧ s.regs.get64 .rdi = BitVec.ofNat 64 (u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (i)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrME x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L7e60 -/
abbrev L7e60 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j i v, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (j) ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .r14 = BitVec.ofNat 64 (j + 1) ∧ s.regs.get64 .r15 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ y.kx1 = u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (0) ∧ s.regs.get64 .rcx = dA t₀ ch + 0x15390#64 + BitVec.ofNat 64 (192 * (j + 1)) ∧ i < (if u8 (y.d ch).freqRes (j + 1) = 0 then y.n0 else y.n1) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (i) ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (i + 1) ∧ s.regs.get64 .r9 = BitVec.ofNat 64 (u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (i + 1)) ∧ u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (i) ≤ v ∧ v < u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (i + 1) ∧ y.kx1 ≤ v ∧ v < y.kx1 + 48 ∧ s.regs.get64 .r8 = BitVec.ofNat 64 (v - y.kx1) ∧ s.regs.get64 .rdi = BitVec.ofNat 64 (v + 1) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrME x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L7e60_1 -/
abbrev L7e60_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j i v, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (j) ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .r14 = BitVec.ofNat 64 (j + 1) ∧ s.regs.get64 .r15 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ y.kx1 = u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (0) ∧ s.regs.get64 .rcx = dA t₀ ch + 0x15390#64 + BitVec.ofNat 64 (192 * (j + 1)) ∧ i < (if u8 (y.d ch).freqRes (j + 1) = 0 then y.n0 else y.n1) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (i) ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (i + 1) ∧ s.regs.get64 .r9 = BitVec.ofNat 64 (u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (i + 1)) ∧ u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (i) ≤ v ∧ v < u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (i + 1) ∧ y.kx1 ≤ v ∧ v < y.kx1 + 48 ∧ s.regs.get64 .r8 = BitVec.ofNat 64 (v - y.kx1) ∧ s.regs.get64 .rdi = BitVec.ofNat 64 (v + 1) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrME x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L7e90 -/
abbrev L7e90 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (j) ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .r15 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ s.regs.get64 .r14 = BitVec.ofNat 64 (j + 1) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrME x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L7e90_1 -/
abbrev L7e90_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (j) ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .r15 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ s.regs.get64 .r14 = BitVec.ofNat 64 (j + 1) ∧ s.regs.get64 .rdx = 1#64 ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrMb x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L7eb6 -/
abbrev L7eb6 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j kk, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (j) ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .r15 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ s.regs.get64 .r14 = BitVec.ofNat 64 (j + 1) ∧ 1 ≤ kk ∧ kk ≤ 2 ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (kk) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrMb x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L7eb6_1 -/
abbrev L7eb6_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j kk, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (j) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.nq) ∧ kk ≤ 2 ∧ s.regs.get64 .rdx = dA t₀ ch + 0x15a60#64 + BitVec.ofNat 64 (20 * kk) ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .r15 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ 1 ≤ y.nq ∧ y.kx1 ≤ u16 y.ftNoise (0) ∧ u16 y.ftNoise (0) < u16 y.ftNoise (1) ∧ u16 y.ftNoise (1) ≤ y.kx1 + 48 ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (u16 y.ftNoise (1)) ∧ s.regs.get64 .rdi = BitVec.ofNat 64 (u16 y.ftNoise (0)) ∧ s.regs.get64 .r8 = BitVec.ofNat 64 ((u16 y.ftNoise (1) - u16 y.ftNoise (0))) ∧ s.regs.get64 .r9 = BitVec.ofNat 64 ((u16 y.ftNoise (1) - u16 y.ftNoise (0)) % 4) ∧ s.status.zf = decide ((u16 y.ftNoise (1) - u16 y.ftNoise (0)) % 4 = 0) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrMb x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L7f10 -/
abbrev L7f10 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j kk t, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (j) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.nq) ∧ kk ≤ 2 ∧ s.regs.get64 .rdx = dA t₀ ch + 0x15a60#64 + BitVec.ofNat 64 (20 * kk) ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .r15 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ 1 ≤ y.nq ∧ y.kx1 ≤ u16 y.ftNoise (0) ∧ u16 y.ftNoise (0) < u16 y.ftNoise (1) ∧ u16 y.ftNoise (1) ≤ y.kx1 + 48 ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (u16 y.ftNoise (1)) ∧ t < (u16 y.ftNoise (1) - u16 y.ftNoise (0)) % 4 ∧ s.regs.get64 .rdi = BitVec.ofNat 64 (u16 y.ftNoise (0)) ∧ s.regs.get64 .r8 = BitVec.ofNat 64 ((u16 y.ftNoise (1) - u16 y.ftNoise (0))) ∧ s.regs.get64 .r9 = 0#64 - BitVec.ofNat 64 ((u16 y.ftNoise (1) - u16 y.ftNoise (0)) % 4) ∧ s.regs.get64 .r11 = 0#64 - BitVec.ofNat 64 (t) ∧ s.regs.get64 .r10 = BitVec.ofNat 64 (u16 y.ftNoise (0) + t - y.kx1) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrMb x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L7f36 -/
abbrev L7f36 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j kk, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (j) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.nq) ∧ kk ≤ 2 ∧ s.regs.get64 .rdx = dA t₀ ch + 0x15a60#64 + BitVec.ofNat 64 (20 * kk) ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .r15 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ 1 ≤ y.nq ∧ y.kx1 ≤ u16 y.ftNoise (0) ∧ u16 y.ftNoise (0) < u16 y.ftNoise (1) ∧ u16 y.ftNoise (1) ≤ y.kx1 + 48 ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (u16 y.ftNoise (1)) ∧ s.regs.get64 .rdi = BitVec.ofNat 64 ((u16 y.ftNoise (0) + (u16 y.ftNoise (1) - u16 y.ftNoise (0)) % 4)) ∧ s.regs.get64 .r8 = BitVec.ofNat 64 ((u16 y.ftNoise (1) - u16 y.ftNoise (0))) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrMb x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L7f36_1 -/
abbrev L7f36_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j kk, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (j) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.nq) ∧ kk ≤ 2 ∧ s.regs.get64 .rdx = dA t₀ ch + 0x15a60#64 + BitVec.ofNat 64 (20 * kk) ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .r15 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ 1 ≤ y.nq ∧ y.kx1 ≤ u16 y.ftNoise (0) ∧ u16 y.ftNoise (0) < u16 y.ftNoise (1) ∧ u16 y.ftNoise (1) ≤ y.kx1 + 48 ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (u16 y.ftNoise (1)) ∧ (u16 y.ftNoise (0) + (u16 y.ftNoise (1) - u16 y.ftNoise (0)) % 4) + 4 ≤ u16 y.ftNoise (1) ∧ s.regs.get64 .r8 = BitVec.ofNat 64 (((u16 y.ftNoise (0) + (u16 y.ftNoise (1) - u16 y.ftNoise (0)) % 4) - y.kx1)) ∧ s.regs.get64 .rdi = BitVec.ofNat 64 ((u16 y.ftNoise (0) + (u16 y.ftNoise (1) - u16 y.ftNoise (0)) % 4)) - BitVec.ofNat 64 (u16 y.ftNoise (1)) ∧ s.regs.get64 .rbx = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * ((u16 y.ftNoise (0) + (u16 y.ftNoise (1) - u16 y.ftNoise (0)) % 4) - y.kx1)) ∧ s.regs.get64 .r11 = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * (((u16 y.ftNoise (0) + (u16 y.ftNoise (1) - u16 y.ftNoise (0)) % 4) - y.kx1) + 1)) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * (((u16 y.ftNoise (0) + (u16 y.ftNoise (1) - u16 y.ftNoise (0)) % 4) - y.kx1) + 2)) ∧ s.regs.get64 .r9 = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * (((u16 y.ftNoise (0) + (u16 y.ftNoise (1) - u16 y.ftNoise (0)) % 4) - y.kx1) + 3)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrMb x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L7f80 -/
abbrev L7f80 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j kk t, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (j) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.nq) ∧ kk ≤ 2 ∧ s.regs.get64 .rdx = dA t₀ ch + 0x15a60#64 + BitVec.ofNat 64 (20 * kk) ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .r15 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ 1 ≤ y.nq ∧ y.kx1 ≤ u16 y.ftNoise (0) ∧ u16 y.ftNoise (0) < u16 y.ftNoise (1) ∧ u16 y.ftNoise (1) ≤ y.kx1 + 48 ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (u16 y.ftNoise (1)) ∧ (u16 y.ftNoise (0) + (u16 y.ftNoise (1) - u16 y.ftNoise (0)) % 4) + 4 ≤ u16 y.ftNoise (1) ∧ s.regs.get64 .r8 = BitVec.ofNat 64 (((u16 y.ftNoise (0) + (u16 y.ftNoise (1) - u16 y.ftNoise (0)) % 4) - y.kx1)) ∧ s.regs.get64 .rdi = BitVec.ofNat 64 ((u16 y.ftNoise (0) + (u16 y.ftNoise (1) - u16 y.ftNoise (0)) % 4)) - BitVec.ofNat 64 (u16 y.ftNoise (1)) ∧ s.regs.get64 .rbx = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * ((u16 y.ftNoise (0) + (u16 y.ftNoise (1) - u16 y.ftNoise (0)) % 4) - y.kx1)) ∧ s.regs.get64 .r11 = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * (((u16 y.ftNoise (0) + (u16 y.ftNoise (1) - u16 y.ftNoise (0)) % 4) - y.kx1) + 1)) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * (((u16 y.ftNoise (0) + (u16 y.ftNoise (1) - u16 y.ftNoise (0)) % 4) - y.kx1) + 2)) ∧ s.regs.get64 .r9 = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * (((u16 y.ftNoise (0) + (u16 y.ftNoise (1) - u16 y.ftNoise (0)) % 4) - y.kx1) + 3)) ∧ (u16 y.ftNoise (0) + (u16 y.ftNoise (1) - u16 y.ftNoise (0)) % 4) + 4 * t + 4 ≤ u16 y.ftNoise (1) ∧ s.regs.get64 .r14 = 0x21998#64 + BitVec.ofNat 64 (4 * t) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrMb x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L7f80_1 -/
abbrev L7f80_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j kk t, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (j) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.nq) ∧ kk ≤ 2 ∧ s.regs.get64 .rdx = dA t₀ ch + 0x15a60#64 + BitVec.ofNat 64 (20 * kk) ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .r15 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ 1 ≤ y.nq ∧ y.kx1 ≤ u16 y.ftNoise (0) ∧ u16 y.ftNoise (0) < u16 y.ftNoise (1) ∧ u16 y.ftNoise (1) ≤ y.kx1 + 48 ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (u16 y.ftNoise (1)) ∧ (u16 y.ftNoise (0) + (u16 y.ftNoise (1) - u16 y.ftNoise (0)) % 4) + 4 ≤ u16 y.ftNoise (1) ∧ s.regs.get64 .r8 = BitVec.ofNat 64 (((u16 y.ftNoise (0) + (u16 y.ftNoise (1) - u16 y.ftNoise (0)) % 4) - y.kx1)) ∧ s.regs.get64 .rdi = BitVec.ofNat 64 ((u16 y.ftNoise (0) + (u16 y.ftNoise (1) - u16 y.ftNoise (0)) % 4)) - BitVec.ofNat 64 (u16 y.ftNoise (1)) ∧ s.regs.get64 .rbx = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * ((u16 y.ftNoise (0) + (u16 y.ftNoise (1) - u16 y.ftNoise (0)) % 4) - y.kx1)) ∧ s.regs.get64 .r11 = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * (((u16 y.ftNoise (0) + (u16 y.ftNoise (1) - u16 y.ftNoise (0)) % 4) - y.kx1) + 1)) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * (((u16 y.ftNoise (0) + (u16 y.ftNoise (1) - u16 y.ftNoise (0)) % 4) - y.kx1) + 2)) ∧ s.regs.get64 .r9 = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * (((u16 y.ftNoise (0) + (u16 y.ftNoise (1) - u16 y.ftNoise (0)) % 4) - y.kx1) + 3)) ∧ (u16 y.ftNoise (0) + (u16 y.ftNoise (1) - u16 y.ftNoise (0)) % 4) + 4 * t + 4 ≤ u16 y.ftNoise (1) ∧ s.regs.get64 .r14 = 0x21998#64 + BitVec.ofNat 64 (4 * t) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrMb x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L8009 -/
abbrev L8009 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j kk, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (j) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.nq) ∧ kk ≤ 2 ∧ s.regs.get64 .rdx = dA t₀ ch + 0x15a60#64 + BitVec.ofNat 64 (20 * kk) ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .r15 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ 1 ≤ y.nq ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (u16 y.ftNoise (1)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrMb x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L8050 -/
abbrev L8050 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j kk t, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (j) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.nq) ∧ kk ≤ 2 ∧ s.regs.get64 .rdx = dA t₀ ch + 0x15a60#64 + BitVec.ofNat 64 (20 * kk) ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .r15 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ 2 ≤ y.nq ∧ y.kx1 ≤ u16 y.ftNoise (1) ∧ u16 y.ftNoise (1) < u16 y.ftNoise (2) ∧ u16 y.ftNoise (2) ≤ y.kx1 + 48 ∧ t < (u16 y.ftNoise (2) - u16 y.ftNoise (1)) % 4 ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (u16 y.ftNoise (1)) ∧ s.regs.get64 .rdi = BitVec.ofNat 64 (u16 y.ftNoise (2)) ∧ s.regs.get64 .r8 = BitVec.ofNat 64 ((u16 y.ftNoise (2) - u16 y.ftNoise (1))) ∧ s.regs.get64 .r9 = 0#64 - BitVec.ofNat 64 ((u16 y.ftNoise (2) - u16 y.ftNoise (1)) % 4) ∧ s.regs.get64 .r11 = 0#64 - BitVec.ofNat 64 (t) ∧ s.regs.get64 .r10 = BitVec.ofNat 64 (u16 y.ftNoise (1) + t - y.kx1) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrMb x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L8077 -/
abbrev L8077 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j kk, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (j) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.nq) ∧ kk ≤ 2 ∧ s.regs.get64 .rdx = dA t₀ ch + 0x15a60#64 + BitVec.ofNat 64 (20 * kk) ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .r15 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ 2 ≤ y.nq ∧ y.kx1 ≤ u16 y.ftNoise (1) ∧ u16 y.ftNoise (1) < u16 y.ftNoise (2) ∧ u16 y.ftNoise (2) ≤ y.kx1 + 48 ∧ s.regs.get64 .rsi = BitVec.ofNat 64 ((u16 y.ftNoise (1) + (u16 y.ftNoise (2) - u16 y.ftNoise (1)) % 4)) ∧ s.regs.get64 .rdi = BitVec.ofNat 64 (u16 y.ftNoise (2)) ∧ s.regs.get64 .r8 = BitVec.ofNat 64 ((u16 y.ftNoise (2) - u16 y.ftNoise (1))) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrMb x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L8077_1 -/
abbrev L8077_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j kk, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (j) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.nq) ∧ kk ≤ 2 ∧ s.regs.get64 .rdx = dA t₀ ch + 0x15a60#64 + BitVec.ofNat 64 (20 * kk) ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .r15 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ 2 ≤ y.nq ∧ y.kx1 ≤ u16 y.ftNoise (1) ∧ u16 y.ftNoise (1) < u16 y.ftNoise (2) ∧ u16 y.ftNoise (2) ≤ y.kx1 + 48 ∧ (u16 y.ftNoise (1) + (u16 y.ftNoise (2) - u16 y.ftNoise (1)) % 4) + 4 ≤ u16 y.ftNoise (2) ∧ s.regs.get64 .r8 = BitVec.ofNat 64 (((u16 y.ftNoise (1) + (u16 y.ftNoise (2) - u16 y.ftNoise (1)) % 4) - y.kx1)) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 ((u16 y.ftNoise (1) + (u16 y.ftNoise (2) - u16 y.ftNoise (1)) % 4)) - BitVec.ofNat 64 (u16 y.ftNoise (2)) ∧ s.regs.get64 .rbx = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * ((u16 y.ftNoise (1) + (u16 y.ftNoise (2) - u16 y.ftNoise (1)) % 4) - y.kx1)) ∧ s.regs.get64 .r11 = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * (((u16 y.ftNoise (1) + (u16 y.ftNoise (2) - u16 y.ftNoise (1)) % 4) - y.kx1) + 1)) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * (((u16 y.ftNoise (1) + (u16 y.ftNoise (2) - u16 y.ftNoise (1)) % 4) - y.kx1) + 2)) ∧ s.regs.get64 .r9 = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * (((u16 y.ftNoise (1) + (u16 y.ftNoise (2) - u16 y.ftNoise (1)) % 4) - y.kx1) + 3)) ∧ s.regs.get64 .rdi = BitVec.ofNat 64 (u16 y.ftNoise (2)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrMb x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L80c0 -/
abbrev L80c0 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j kk t, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (j) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.nq) ∧ kk ≤ 2 ∧ s.regs.get64 .rdx = dA t₀ ch + 0x15a60#64 + BitVec.ofNat 64 (20 * kk) ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .r15 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ 2 ≤ y.nq ∧ y.kx1 ≤ u16 y.ftNoise (1) ∧ u16 y.ftNoise (1) < u16 y.ftNoise (2) ∧ u16 y.ftNoise (2) ≤ y.kx1 + 48 ∧ (u16 y.ftNoise (1) + (u16 y.ftNoise (2) - u16 y.ftNoise (1)) % 4) + 4 ≤ u16 y.ftNoise (2) ∧ s.regs.get64 .r8 = BitVec.ofNat 64 (((u16 y.ftNoise (1) + (u16 y.ftNoise (2) - u16 y.ftNoise (1)) % 4) - y.kx1)) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 ((u16 y.ftNoise (1) + (u16 y.ftNoise (2) - u16 y.ftNoise (1)) % 4)) - BitVec.ofNat 64 (u16 y.ftNoise (2)) ∧ s.regs.get64 .rbx = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * ((u16 y.ftNoise (1) + (u16 y.ftNoise (2) - u16 y.ftNoise (1)) % 4) - y.kx1)) ∧ s.regs.get64 .r11 = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * (((u16 y.ftNoise (1) + (u16 y.ftNoise (2) - u16 y.ftNoise (1)) % 4) - y.kx1) + 1)) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * (((u16 y.ftNoise (1) + (u16 y.ftNoise (2) - u16 y.ftNoise (1)) % 4) - y.kx1) + 2)) ∧ s.regs.get64 .r9 = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * (((u16 y.ftNoise (1) + (u16 y.ftNoise (2) - u16 y.ftNoise (1)) % 4) - y.kx1) + 3)) ∧ s.regs.get64 .rdi = BitVec.ofNat 64 (u16 y.ftNoise (2)) ∧ (u16 y.ftNoise (1) + (u16 y.ftNoise (2) - u16 y.ftNoise (1)) % 4) + 4 * t + 4 ≤ u16 y.ftNoise (2) ∧ s.regs.get64 .r14 = 0x21998#64 + BitVec.ofNat 64 (4 * t) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrMb x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L80c0_1 -/
abbrev L80c0_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j kk t, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (j) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.nq) ∧ kk ≤ 2 ∧ s.regs.get64 .rdx = dA t₀ ch + 0x15a60#64 + BitVec.ofNat 64 (20 * kk) ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .r15 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ 2 ≤ y.nq ∧ y.kx1 ≤ u16 y.ftNoise (1) ∧ u16 y.ftNoise (1) < u16 y.ftNoise (2) ∧ u16 y.ftNoise (2) ≤ y.kx1 + 48 ∧ (u16 y.ftNoise (1) + (u16 y.ftNoise (2) - u16 y.ftNoise (1)) % 4) + 4 ≤ u16 y.ftNoise (2) ∧ s.regs.get64 .r8 = BitVec.ofNat 64 (((u16 y.ftNoise (1) + (u16 y.ftNoise (2) - u16 y.ftNoise (1)) % 4) - y.kx1)) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 ((u16 y.ftNoise (1) + (u16 y.ftNoise (2) - u16 y.ftNoise (1)) % 4)) - BitVec.ofNat 64 (u16 y.ftNoise (2)) ∧ s.regs.get64 .rbx = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * ((u16 y.ftNoise (1) + (u16 y.ftNoise (2) - u16 y.ftNoise (1)) % 4) - y.kx1)) ∧ s.regs.get64 .r11 = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * (((u16 y.ftNoise (1) + (u16 y.ftNoise (2) - u16 y.ftNoise (1)) % 4) - y.kx1) + 1)) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * (((u16 y.ftNoise (1) + (u16 y.ftNoise (2) - u16 y.ftNoise (1)) % 4) - y.kx1) + 2)) ∧ s.regs.get64 .r9 = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * (((u16 y.ftNoise (1) + (u16 y.ftNoise (2) - u16 y.ftNoise (1)) % 4) - y.kx1) + 3)) ∧ s.regs.get64 .rdi = BitVec.ofNat 64 (u16 y.ftNoise (2)) ∧ (u16 y.ftNoise (1) + (u16 y.ftNoise (2) - u16 y.ftNoise (1)) % 4) + 4 * t + 4 ≤ u16 y.ftNoise (2) ∧ s.regs.get64 .r14 = 0x21998#64 + BitVec.ofNat 64 (4 * t) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrMb x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L814a -/
abbrev L814a (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j kk, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (j) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.nq) ∧ kk ≤ 2 ∧ s.regs.get64 .rdx = dA t₀ ch + 0x15a60#64 + BitVec.ofNat 64 (20 * kk) ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .r15 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ 2 ≤ y.nq ∧ s.regs.get64 .rdi = BitVec.ofNat 64 (u16 y.ftNoise (2)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrMb x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L8190 -/
abbrev L8190 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j kk t, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (j) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.nq) ∧ kk ≤ 2 ∧ s.regs.get64 .rdx = dA t₀ ch + 0x15a60#64 + BitVec.ofNat 64 (20 * kk) ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .r15 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ 3 ≤ y.nq ∧ y.kx1 ≤ u16 y.ftNoise (2) ∧ u16 y.ftNoise (2) < u16 y.ftNoise (3) ∧ u16 y.ftNoise (3) ≤ y.kx1 + 48 ∧ t < (u16 y.ftNoise (3) - u16 y.ftNoise (2)) % 4 ∧ s.regs.get64 .rdi = BitVec.ofNat 64 (u16 y.ftNoise (2)) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (u16 y.ftNoise (3)) ∧ s.regs.get64 .r8 = BitVec.ofNat 64 ((u16 y.ftNoise (3) - u16 y.ftNoise (2))) ∧ s.regs.get64 .r9 = 0#64 - BitVec.ofNat 64 ((u16 y.ftNoise (3) - u16 y.ftNoise (2)) % 4) ∧ s.regs.get64 .r11 = 0#64 - BitVec.ofNat 64 (t) ∧ s.regs.get64 .r10 = BitVec.ofNat 64 (u16 y.ftNoise (2) + t - y.kx1) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrMb x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L81b7 -/
abbrev L81b7 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j kk, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (j) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.nq) ∧ kk ≤ 2 ∧ s.regs.get64 .rdx = dA t₀ ch + 0x15a60#64 + BitVec.ofNat 64 (20 * kk) ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .r15 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ 3 ≤ y.nq ∧ y.kx1 ≤ u16 y.ftNoise (2) ∧ u16 y.ftNoise (2) < u16 y.ftNoise (3) ∧ u16 y.ftNoise (3) ≤ y.kx1 + 48 ∧ s.regs.get64 .rdi = BitVec.ofNat 64 ((u16 y.ftNoise (2) + (u16 y.ftNoise (3) - u16 y.ftNoise (2)) % 4)) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (u16 y.ftNoise (3)) ∧ s.regs.get64 .r8 = BitVec.ofNat 64 ((u16 y.ftNoise (3) - u16 y.ftNoise (2))) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrMb x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L81b7_1 -/
abbrev L81b7_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j kk, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (j) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.nq) ∧ kk ≤ 2 ∧ s.regs.get64 .rdx = dA t₀ ch + 0x15a60#64 + BitVec.ofNat 64 (20 * kk) ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .r15 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ 3 ≤ y.nq ∧ y.kx1 ≤ u16 y.ftNoise (2) ∧ u16 y.ftNoise (2) < u16 y.ftNoise (3) ∧ u16 y.ftNoise (3) ≤ y.kx1 + 48 ∧ (u16 y.ftNoise (2) + (u16 y.ftNoise (3) - u16 y.ftNoise (2)) % 4) + 4 ≤ u16 y.ftNoise (3) ∧ s.regs.get64 .r8 = BitVec.ofNat 64 (((u16 y.ftNoise (2) + (u16 y.ftNoise (3) - u16 y.ftNoise (2)) % 4) - y.kx1)) ∧ s.regs.get64 .rdi = BitVec.ofNat 64 ((u16 y.ftNoise (2) + (u16 y.ftNoise (3) - u16 y.ftNoise (2)) % 4)) - BitVec.ofNat 64 (u16 y.ftNoise (3)) ∧ s.regs.get64 .rbx = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * ((u16 y.ftNoise (2) + (u16 y.ftNoise (3) - u16 y.ftNoise (2)) % 4) - y.kx1)) ∧ s.regs.get64 .r11 = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * (((u16 y.ftNoise (2) + (u16 y.ftNoise (3) - u16 y.ftNoise (2)) % 4) - y.kx1) + 1)) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * (((u16 y.ftNoise (2) + (u16 y.ftNoise (3) - u16 y.ftNoise (2)) % 4) - y.kx1) + 2)) ∧ s.regs.get64 .r9 = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * (((u16 y.ftNoise (2) + (u16 y.ftNoise (3) - u16 y.ftNoise (2)) % 4) - y.kx1) + 3)) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (u16 y.ftNoise (3)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrMb x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L8200 -/
abbrev L8200 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j kk t, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (j) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.nq) ∧ kk ≤ 2 ∧ s.regs.get64 .rdx = dA t₀ ch + 0x15a60#64 + BitVec.ofNat 64 (20 * kk) ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .r15 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ 3 ≤ y.nq ∧ y.kx1 ≤ u16 y.ftNoise (2) ∧ u16 y.ftNoise (2) < u16 y.ftNoise (3) ∧ u16 y.ftNoise (3) ≤ y.kx1 + 48 ∧ (u16 y.ftNoise (2) + (u16 y.ftNoise (3) - u16 y.ftNoise (2)) % 4) + 4 ≤ u16 y.ftNoise (3) ∧ s.regs.get64 .r8 = BitVec.ofNat 64 (((u16 y.ftNoise (2) + (u16 y.ftNoise (3) - u16 y.ftNoise (2)) % 4) - y.kx1)) ∧ s.regs.get64 .rdi = BitVec.ofNat 64 ((u16 y.ftNoise (2) + (u16 y.ftNoise (3) - u16 y.ftNoise (2)) % 4)) - BitVec.ofNat 64 (u16 y.ftNoise (3)) ∧ s.regs.get64 .rbx = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * ((u16 y.ftNoise (2) + (u16 y.ftNoise (3) - u16 y.ftNoise (2)) % 4) - y.kx1)) ∧ s.regs.get64 .r11 = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * (((u16 y.ftNoise (2) + (u16 y.ftNoise (3) - u16 y.ftNoise (2)) % 4) - y.kx1) + 1)) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * (((u16 y.ftNoise (2) + (u16 y.ftNoise (3) - u16 y.ftNoise (2)) % 4) - y.kx1) + 2)) ∧ s.regs.get64 .r9 = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * (((u16 y.ftNoise (2) + (u16 y.ftNoise (3) - u16 y.ftNoise (2)) % 4) - y.kx1) + 3)) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (u16 y.ftNoise (3)) ∧ (u16 y.ftNoise (2) + (u16 y.ftNoise (3) - u16 y.ftNoise (2)) % 4) + 4 * t + 4 ≤ u16 y.ftNoise (3) ∧ s.regs.get64 .r14 = 0x21998#64 + BitVec.ofNat 64 (4 * t) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrMb x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L8200_1 -/
abbrev L8200_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j kk t, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (j) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.nq) ∧ kk ≤ 2 ∧ s.regs.get64 .rdx = dA t₀ ch + 0x15a60#64 + BitVec.ofNat 64 (20 * kk) ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .r15 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ 3 ≤ y.nq ∧ y.kx1 ≤ u16 y.ftNoise (2) ∧ u16 y.ftNoise (2) < u16 y.ftNoise (3) ∧ u16 y.ftNoise (3) ≤ y.kx1 + 48 ∧ (u16 y.ftNoise (2) + (u16 y.ftNoise (3) - u16 y.ftNoise (2)) % 4) + 4 ≤ u16 y.ftNoise (3) ∧ s.regs.get64 .r8 = BitVec.ofNat 64 (((u16 y.ftNoise (2) + (u16 y.ftNoise (3) - u16 y.ftNoise (2)) % 4) - y.kx1)) ∧ s.regs.get64 .rdi = BitVec.ofNat 64 ((u16 y.ftNoise (2) + (u16 y.ftNoise (3) - u16 y.ftNoise (2)) % 4)) - BitVec.ofNat 64 (u16 y.ftNoise (3)) ∧ s.regs.get64 .rbx = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * ((u16 y.ftNoise (2) + (u16 y.ftNoise (3) - u16 y.ftNoise (2)) % 4) - y.kx1)) ∧ s.regs.get64 .r11 = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * (((u16 y.ftNoise (2) + (u16 y.ftNoise (3) - u16 y.ftNoise (2)) % 4) - y.kx1) + 1)) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * (((u16 y.ftNoise (2) + (u16 y.ftNoise (3) - u16 y.ftNoise (2)) % 4) - y.kx1) + 2)) ∧ s.regs.get64 .r9 = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * (((u16 y.ftNoise (2) + (u16 y.ftNoise (3) - u16 y.ftNoise (2)) % 4) - y.kx1) + 3)) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (u16 y.ftNoise (3)) ∧ (u16 y.ftNoise (2) + (u16 y.ftNoise (3) - u16 y.ftNoise (2)) % 4) + 4 * t + 4 ≤ u16 y.ftNoise (3) ∧ s.regs.get64 .r14 = 0x21998#64 + BitVec.ofNat 64 (4 * t) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrMb x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L828a -/
abbrev L828a (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j kk, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (j) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.nq) ∧ kk ≤ 2 ∧ s.regs.get64 .rdx = dA t₀ ch + 0x15a60#64 + BitVec.ofNat 64 (20 * kk) ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .r15 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ 3 ≤ y.nq ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (u16 y.ftNoise (3)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrMb x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L82d0 -/
abbrev L82d0 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j kk t, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (j) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.nq) ∧ kk ≤ 2 ∧ s.regs.get64 .rdx = dA t₀ ch + 0x15a60#64 + BitVec.ofNat 64 (20 * kk) ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .r15 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ 4 ≤ y.nq ∧ y.kx1 ≤ u16 y.ftNoise (3) ∧ u16 y.ftNoise (3) < u16 y.ftNoise (4) ∧ u16 y.ftNoise (4) ≤ y.kx1 + 48 ∧ t < (u16 y.ftNoise (4) - u16 y.ftNoise (3)) % 4 ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (u16 y.ftNoise (3)) ∧ s.regs.get64 .rdi = BitVec.ofNat 64 (u16 y.ftNoise (4)) ∧ s.regs.get64 .r8 = BitVec.ofNat 64 ((u16 y.ftNoise (4) - u16 y.ftNoise (3))) ∧ s.regs.get64 .r9 = 0#64 - BitVec.ofNat 64 ((u16 y.ftNoise (4) - u16 y.ftNoise (3)) % 4) ∧ s.regs.get64 .r11 = 0#64 - BitVec.ofNat 64 (t) ∧ s.regs.get64 .r10 = BitVec.ofNat 64 (u16 y.ftNoise (3) + t - y.kx1) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrMb x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L82f7 -/
abbrev L82f7 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j kk, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (j) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.nq) ∧ kk ≤ 2 ∧ s.regs.get64 .rdx = dA t₀ ch + 0x15a60#64 + BitVec.ofNat 64 (20 * kk) ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .r15 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ 4 ≤ y.nq ∧ y.kx1 ≤ u16 y.ftNoise (3) ∧ u16 y.ftNoise (3) < u16 y.ftNoise (4) ∧ u16 y.ftNoise (4) ≤ y.kx1 + 48 ∧ s.regs.get64 .rsi = BitVec.ofNat 64 ((u16 y.ftNoise (3) + (u16 y.ftNoise (4) - u16 y.ftNoise (3)) % 4)) ∧ s.regs.get64 .rdi = BitVec.ofNat 64 (u16 y.ftNoise (4)) ∧ s.regs.get64 .r8 = BitVec.ofNat 64 ((u16 y.ftNoise (4) - u16 y.ftNoise (3))) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrMb x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L82f7_1 -/
abbrev L82f7_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j kk, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (j) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.nq) ∧ kk ≤ 2 ∧ s.regs.get64 .rdx = dA t₀ ch + 0x15a60#64 + BitVec.ofNat 64 (20 * kk) ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .r15 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ 4 ≤ y.nq ∧ y.kx1 ≤ u16 y.ftNoise (3) ∧ u16 y.ftNoise (3) < u16 y.ftNoise (4) ∧ u16 y.ftNoise (4) ≤ y.kx1 + 48 ∧ (u16 y.ftNoise (3) + (u16 y.ftNoise (4) - u16 y.ftNoise (3)) % 4) + 4 ≤ u16 y.ftNoise (4) ∧ s.regs.get64 .r8 = BitVec.ofNat 64 (((u16 y.ftNoise (3) + (u16 y.ftNoise (4) - u16 y.ftNoise (3)) % 4) - y.kx1)) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 ((u16 y.ftNoise (3) + (u16 y.ftNoise (4) - u16 y.ftNoise (3)) % 4)) - BitVec.ofNat 64 (u16 y.ftNoise (4)) ∧ s.regs.get64 .rbx = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * ((u16 y.ftNoise (3) + (u16 y.ftNoise (4) - u16 y.ftNoise (3)) % 4) - y.kx1)) ∧ s.regs.get64 .r11 = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * (((u16 y.ftNoise (3) + (u16 y.ftNoise (4) - u16 y.ftNoise (3)) % 4) - y.kx1) + 1)) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * (((u16 y.ftNoise (3) + (u16 y.ftNoise (4) - u16 y.ftNoise (3)) % 4) - y.kx1) + 2)) ∧ s.regs.get64 .r9 = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * (((u16 y.ftNoise (3) + (u16 y.ftNoise (4) - u16 y.ftNoise (3)) % 4) - y.kx1) + 3)) ∧ s.regs.get64 .rdi = BitVec.ofNat 64 (u16 y.ftNoise (4)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrMb x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L8340 -/
abbrev L8340 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j kk t, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (j) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.nq) ∧ kk ≤ 2 ∧ s.regs.get64 .rdx = dA t₀ ch + 0x15a60#64 + BitVec.ofNat 64 (20 * kk) ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .r15 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ 4 ≤ y.nq ∧ y.kx1 ≤ u16 y.ftNoise (3) ∧ u16 y.ftNoise (3) < u16 y.ftNoise (4) ∧ u16 y.ftNoise (4) ≤ y.kx1 + 48 ∧ (u16 y.ftNoise (3) + (u16 y.ftNoise (4) - u16 y.ftNoise (3)) % 4) + 4 ≤ u16 y.ftNoise (4) ∧ s.regs.get64 .r8 = BitVec.ofNat 64 (((u16 y.ftNoise (3) + (u16 y.ftNoise (4) - u16 y.ftNoise (3)) % 4) - y.kx1)) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 ((u16 y.ftNoise (3) + (u16 y.ftNoise (4) - u16 y.ftNoise (3)) % 4)) - BitVec.ofNat 64 (u16 y.ftNoise (4)) ∧ s.regs.get64 .rbx = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * ((u16 y.ftNoise (3) + (u16 y.ftNoise (4) - u16 y.ftNoise (3)) % 4) - y.kx1)) ∧ s.regs.get64 .r11 = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * (((u16 y.ftNoise (3) + (u16 y.ftNoise (4) - u16 y.ftNoise (3)) % 4) - y.kx1) + 1)) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * (((u16 y.ftNoise (3) + (u16 y.ftNoise (4) - u16 y.ftNoise (3)) % 4) - y.kx1) + 2)) ∧ s.regs.get64 .r9 = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * (((u16 y.ftNoise (3) + (u16 y.ftNoise (4) - u16 y.ftNoise (3)) % 4) - y.kx1) + 3)) ∧ s.regs.get64 .rdi = BitVec.ofNat 64 (u16 y.ftNoise (4)) ∧ (u16 y.ftNoise (3) + (u16 y.ftNoise (4) - u16 y.ftNoise (3)) % 4) + 4 * t + 4 ≤ u16 y.ftNoise (4) ∧ s.regs.get64 .r14 = 0x21998#64 + BitVec.ofNat 64 (4 * t) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrMb x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L8340_1 -/
abbrev L8340_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j kk t, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (j) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.nq) ∧ kk ≤ 2 ∧ s.regs.get64 .rdx = dA t₀ ch + 0x15a60#64 + BitVec.ofNat 64 (20 * kk) ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .r15 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ 4 ≤ y.nq ∧ y.kx1 ≤ u16 y.ftNoise (3) ∧ u16 y.ftNoise (3) < u16 y.ftNoise (4) ∧ u16 y.ftNoise (4) ≤ y.kx1 + 48 ∧ (u16 y.ftNoise (3) + (u16 y.ftNoise (4) - u16 y.ftNoise (3)) % 4) + 4 ≤ u16 y.ftNoise (4) ∧ s.regs.get64 .r8 = BitVec.ofNat 64 (((u16 y.ftNoise (3) + (u16 y.ftNoise (4) - u16 y.ftNoise (3)) % 4) - y.kx1)) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 ((u16 y.ftNoise (3) + (u16 y.ftNoise (4) - u16 y.ftNoise (3)) % 4)) - BitVec.ofNat 64 (u16 y.ftNoise (4)) ∧ s.regs.get64 .rbx = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * ((u16 y.ftNoise (3) + (u16 y.ftNoise (4) - u16 y.ftNoise (3)) % 4) - y.kx1)) ∧ s.regs.get64 .r11 = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * (((u16 y.ftNoise (3) + (u16 y.ftNoise (4) - u16 y.ftNoise (3)) % 4) - y.kx1) + 1)) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * (((u16 y.ftNoise (3) + (u16 y.ftNoise (4) - u16 y.ftNoise (3)) % 4) - y.kx1) + 2)) ∧ s.regs.get64 .r9 = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * (((u16 y.ftNoise (3) + (u16 y.ftNoise (4) - u16 y.ftNoise (3)) % 4) - y.kx1) + 3)) ∧ s.regs.get64 .rdi = BitVec.ofNat 64 (u16 y.ftNoise (4)) ∧ (u16 y.ftNoise (3) + (u16 y.ftNoise (4) - u16 y.ftNoise (3)) % 4) + 4 * t + 4 ≤ u16 y.ftNoise (4) ∧ s.regs.get64 .r14 = 0x21998#64 + BitVec.ofNat 64 (4 * t) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrMb x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L83ca -/
abbrev L83ca (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j kk, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (j) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.nq) ∧ kk ≤ 2 ∧ s.regs.get64 .rdx = dA t₀ ch + 0x15a60#64 + BitVec.ofNat 64 (20 * kk) ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .r15 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ 4 ≤ y.nq ∧ s.regs.get64 .rdi = BitVec.ofNat 64 (u16 y.ftNoise (4)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrMb x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L8410 -/
abbrev L8410 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j kk t, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (j) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.nq) ∧ kk ≤ 2 ∧ s.regs.get64 .rdx = dA t₀ ch + 0x15a60#64 + BitVec.ofNat 64 (20 * kk) ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .r15 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ 5 ≤ y.nq ∧ y.kx1 ≤ u16 y.ftNoise (4) ∧ u16 y.ftNoise (4) < u16 y.ftNoise (5) ∧ u16 y.ftNoise (5) ≤ y.kx1 + 48 ∧ t < (u16 y.ftNoise (5) - u16 y.ftNoise (4)) % 4 ∧ s.regs.get64 .rdi = BitVec.ofNat 64 (u16 y.ftNoise (4)) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (u16 y.ftNoise (5)) ∧ s.regs.get64 .r8 = BitVec.ofNat 64 ((u16 y.ftNoise (5) - u16 y.ftNoise (4))) ∧ s.regs.get64 .r9 = 0#64 - BitVec.ofNat 64 ((u16 y.ftNoise (5) - u16 y.ftNoise (4)) % 4) ∧ s.regs.get64 .r11 = 0#64 - BitVec.ofNat 64 (t) ∧ s.regs.get64 .r10 = BitVec.ofNat 64 (u16 y.ftNoise (4) + t - y.kx1) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrMb x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L8437 -/
abbrev L8437 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j kk, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (j) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.nq) ∧ kk ≤ 2 ∧ s.regs.get64 .rdx = dA t₀ ch + 0x15a60#64 + BitVec.ofNat 64 (20 * kk) ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .r15 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ 5 ≤ y.nq ∧ y.kx1 ≤ u16 y.ftNoise (4) ∧ u16 y.ftNoise (4) < u16 y.ftNoise (5) ∧ u16 y.ftNoise (5) ≤ y.kx1 + 48 ∧ s.regs.get64 .rdi = BitVec.ofNat 64 ((u16 y.ftNoise (4) + (u16 y.ftNoise (5) - u16 y.ftNoise (4)) % 4)) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (u16 y.ftNoise (5)) ∧ s.regs.get64 .r8 = BitVec.ofNat 64 ((u16 y.ftNoise (5) - u16 y.ftNoise (4))) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrMb x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L8437_1 -/
abbrev L8437_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j kk, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (j) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.nq) ∧ kk ≤ 2 ∧ s.regs.get64 .rdx = dA t₀ ch + 0x15a60#64 + BitVec.ofNat 64 (20 * kk) ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .r15 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ 5 ≤ y.nq ∧ y.kx1 ≤ u16 y.ftNoise (4) ∧ u16 y.ftNoise (4) < u16 y.ftNoise (5) ∧ u16 y.ftNoise (5) ≤ y.kx1 + 48 ∧ (u16 y.ftNoise (4) + (u16 y.ftNoise (5) - u16 y.ftNoise (4)) % 4) + 4 ≤ u16 y.ftNoise (5) ∧ s.regs.get64 .r8 = BitVec.ofNat 64 (((u16 y.ftNoise (4) + (u16 y.ftNoise (5) - u16 y.ftNoise (4)) % 4) - y.kx1)) ∧ s.regs.get64 .rdi = BitVec.ofNat 64 ((u16 y.ftNoise (4) + (u16 y.ftNoise (5) - u16 y.ftNoise (4)) % 4)) - BitVec.ofNat 64 (u16 y.ftNoise (5)) ∧ s.regs.get64 .rsi = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * ((u16 y.ftNoise (4) + (u16 y.ftNoise (5) - u16 y.ftNoise (4)) % 4) - y.kx1)) ∧ s.regs.get64 .r11 = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * (((u16 y.ftNoise (4) + (u16 y.ftNoise (5) - u16 y.ftNoise (4)) % 4) - y.kx1) + 1)) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * (((u16 y.ftNoise (4) + (u16 y.ftNoise (5) - u16 y.ftNoise (4)) % 4) - y.kx1) + 2)) ∧ s.regs.get64 .r9 = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * (((u16 y.ftNoise (4) + (u16 y.ftNoise (5) - u16 y.ftNoise (4)) % 4) - y.kx1) + 3)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrMb x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L8480 -/
abbrev L8480 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j kk t, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (j) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.nq) ∧ kk ≤ 2 ∧ s.regs.get64 .rdx = dA t₀ ch + 0x15a60#64 + BitVec.ofNat 64 (20 * kk) ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .r15 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ 5 ≤ y.nq ∧ y.kx1 ≤ u16 y.ftNoise (4) ∧ u16 y.ftNoise (4) < u16 y.ftNoise (5) ∧ u16 y.ftNoise (5) ≤ y.kx1 + 48 ∧ (u16 y.ftNoise (4) + (u16 y.ftNoise (5) - u16 y.ftNoise (4)) % 4) + 4 ≤ u16 y.ftNoise (5) ∧ s.regs.get64 .r8 = BitVec.ofNat 64 (((u16 y.ftNoise (4) + (u16 y.ftNoise (5) - u16 y.ftNoise (4)) % 4) - y.kx1)) ∧ s.regs.get64 .rdi = BitVec.ofNat 64 ((u16 y.ftNoise (4) + (u16 y.ftNoise (5) - u16 y.ftNoise (4)) % 4)) - BitVec.ofNat 64 (u16 y.ftNoise (5)) ∧ s.regs.get64 .rsi = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * ((u16 y.ftNoise (4) + (u16 y.ftNoise (5) - u16 y.ftNoise (4)) % 4) - y.kx1)) ∧ s.regs.get64 .r11 = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * (((u16 y.ftNoise (4) + (u16 y.ftNoise (5) - u16 y.ftNoise (4)) % 4) - y.kx1) + 1)) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * (((u16 y.ftNoise (4) + (u16 y.ftNoise (5) - u16 y.ftNoise (4)) % 4) - y.kx1) + 2)) ∧ s.regs.get64 .r9 = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * (((u16 y.ftNoise (4) + (u16 y.ftNoise (5) - u16 y.ftNoise (4)) % 4) - y.kx1) + 3)) ∧ (u16 y.ftNoise (4) + (u16 y.ftNoise (5) - u16 y.ftNoise (4)) % 4) + 4 * t + 4 ≤ u16 y.ftNoise (5) ∧ s.regs.get64 .rbx = 0x21998#64 + BitVec.ofNat 64 (4 * t) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrMb x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L8480_1 -/
abbrev L8480_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j kk t, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (j) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.nq) ∧ kk ≤ 2 ∧ s.regs.get64 .rdx = dA t₀ ch + 0x15a60#64 + BitVec.ofNat 64 (20 * kk) ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .r15 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ 5 ≤ y.nq ∧ y.kx1 ≤ u16 y.ftNoise (4) ∧ u16 y.ftNoise (4) < u16 y.ftNoise (5) ∧ u16 y.ftNoise (5) ≤ y.kx1 + 48 ∧ (u16 y.ftNoise (4) + (u16 y.ftNoise (5) - u16 y.ftNoise (4)) % 4) + 4 ≤ u16 y.ftNoise (5) ∧ s.regs.get64 .r8 = BitVec.ofNat 64 (((u16 y.ftNoise (4) + (u16 y.ftNoise (5) - u16 y.ftNoise (4)) % 4) - y.kx1)) ∧ s.regs.get64 .rdi = BitVec.ofNat 64 ((u16 y.ftNoise (4) + (u16 y.ftNoise (5) - u16 y.ftNoise (4)) % 4)) - BitVec.ofNat 64 (u16 y.ftNoise (5)) ∧ s.regs.get64 .rsi = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * ((u16 y.ftNoise (4) + (u16 y.ftNoise (5) - u16 y.ftNoise (4)) % 4) - y.kx1)) ∧ s.regs.get64 .r11 = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * (((u16 y.ftNoise (4) + (u16 y.ftNoise (5) - u16 y.ftNoise (4)) % 4) - y.kx1) + 1)) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * (((u16 y.ftNoise (4) + (u16 y.ftNoise (5) - u16 y.ftNoise (4)) % 4) - y.kx1) + 2)) ∧ s.regs.get64 .r9 = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) + BitVec.ofNat 64 (4 * (((u16 y.ftNoise (4) + (u16 y.ftNoise (5) - u16 y.ftNoise (4)) % 4) - y.kx1) + 3)) ∧ (u16 y.ftNoise (4) + (u16 y.ftNoise (5) - u16 y.ftNoise (4)) % 4) + 4 * t + 4 ≤ u16 y.ftNoise (5) ∧ s.regs.get64 .rbx = 0x21998#64 + BitVec.ofNat 64 (4 * t) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrMb x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L8509 -/
abbrev L8509 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j kk, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (j) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.nq) ∧ kk ≤ 2 ∧ s.regs.get64 .rdx = dA t₀ ch + 0x15a60#64 + BitVec.ofNat 64 (20 * kk) ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .r15 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ 5 ≤ y.nq ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrMb x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L8520 -/
abbrev L8520 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .r8 = arg1 t₀ ∧ s.regs.get64 .rax = BitVec.ofNat 64 (j) ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .r15 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrMb x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L8570 -/
abbrev L8570 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j i, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (j) ∧ s.regs.get64 .r11 = 0#64 ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .r14 = dA t₀ ch + 0x15030#64 ∧ s.regs.get64 .r13 = dA t₀ ch + 0x32#64 ∧ s.regs.get64 .rcx = dA t₀ ch + 0x15030#64 + BitVec.ofNat 64 (48 * (j + 1)) ∧ i % 2 = 0 ∧ i < y.n1 ∧ s.regs.get64 .rdi = BitVec.ofNat 64 (i) ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (i + 1) ∧ s.regs.get64 .rsi = sbrA t₀ + 0x4c288#64 + BitVec.ofNat 64 (2 * i) ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .r15 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrMb x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L8570_1 -/
abbrev L8570_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j i v, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (j) ∧ s.regs.get64 .r11 = 0#64 ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .r14 = dA t₀ ch + 0x15030#64 ∧ s.regs.get64 .r13 = dA t₀ ch + 0x32#64 ∧ s.regs.get64 .rcx = dA t₀ ch + 0x15030#64 + BitVec.ofNat 64 (48 * (j + 1)) ∧ i % 2 = 0 ∧ i < y.n1 ∧ s.regs.get64 .rdi = BitVec.ofNat 64 (i) ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (i + 1) ∧ s.regs.get64 .rsi = sbrA t₀ + 0x4c288#64 + BitVec.ofNat 64 (2 * i) ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .r15 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ v < 48 ∧ s.regs.get64 .r10 = BitVec.ofNat 64 (v) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrMb x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L85c0 -/
abbrev L85c0 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j i v, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (j) ∧ s.regs.get64 .r11 = 0#64 ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .r14 = dA t₀ ch + 0x15030#64 ∧ s.regs.get64 .r13 = dA t₀ ch + 0x32#64 ∧ s.regs.get64 .rcx = dA t₀ ch + 0x15030#64 + BitVec.ofNat 64 (48 * (j + 1)) ∧ i % 2 = 0 ∧ i < y.n1 ∧ s.regs.get64 .rdi = BitVec.ofNat 64 (i) ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (i + 1) ∧ s.regs.get64 .rsi = sbrA t₀ + 0x4c288#64 + BitVec.ofNat 64 (2 * i) ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .r15 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ v < 48 ∧ s.regs.get64 .r10 = BitVec.ofNat 64 (v) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrMb x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L85cd -/
abbrev L85cd (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j i v, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (j) ∧ s.regs.get64 .r11 = 0#64 ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .r14 = dA t₀ ch + 0x15030#64 ∧ s.regs.get64 .r13 = dA t₀ ch + 0x32#64 ∧ s.regs.get64 .rcx = dA t₀ ch + 0x15030#64 + BitVec.ofNat 64 (48 * (j + 1)) ∧ i % 2 = 0 ∧ i < y.n1 ∧ s.regs.get64 .rdi = BitVec.ofNat 64 (i) ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (i + 1) ∧ s.regs.get64 .rsi = sbrA t₀ + 0x4c288#64 + BitVec.ofNat 64 (2 * i) ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .r15 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ v < 48 ∧ s.regs.get64 .r10 = BitVec.ofNat 64 (v) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrMb x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L85cd_1 -/
abbrev L85cd_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j i, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (j) ∧ s.regs.get64 .r11 = 0#64 ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .r14 = dA t₀ ch + 0x15030#64 ∧ s.regs.get64 .r13 = dA t₀ ch + 0x32#64 ∧ s.regs.get64 .rcx = dA t₀ ch + 0x15030#64 + BitVec.ofNat 64 (48 * (j + 1)) ∧ i % 2 = 0 ∧ i < y.n1 ∧ s.regs.get64 .rdi = BitVec.ofNat 64 (i) ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (i + 1) ∧ s.regs.get64 .rsi = sbrA t₀ + 0x4c288#64 + BitVec.ofNat 64 (2 * i) ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .r15 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrMb x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L85cd_2 -/
abbrev L85cd_2 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j i v, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (j) ∧ s.regs.get64 .r11 = 0#64 ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .r14 = dA t₀ ch + 0x15030#64 ∧ s.regs.get64 .r13 = dA t₀ ch + 0x32#64 ∧ s.regs.get64 .rcx = dA t₀ ch + 0x15030#64 + BitVec.ofNat 64 (48 * (j + 1)) ∧ i % 2 = 0 ∧ i < y.n1 ∧ s.regs.get64 .rdi = BitVec.ofNat 64 (i) ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (i + 1) ∧ s.regs.get64 .rsi = sbrA t₀ + 0x4c288#64 + BitVec.ofNat 64 (2 * i) ∧ i + 1 < y.n1 ∧ v < 48 ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .r15 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ s.regs.get64 .r8 = BitVec.ofNat 64 (v) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrMb x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L8620 -/
abbrev L8620 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j i v, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (j) ∧ s.regs.get64 .r11 = 0#64 ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .r14 = dA t₀ ch + 0x15030#64 ∧ s.regs.get64 .r13 = dA t₀ ch + 0x32#64 ∧ s.regs.get64 .rcx = dA t₀ ch + 0x15030#64 + BitVec.ofNat 64 (48 * (j + 1)) ∧ i % 2 = 0 ∧ i < y.n1 ∧ s.regs.get64 .rdi = BitVec.ofNat 64 (i) ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (i + 1) ∧ s.regs.get64 .rsi = sbrA t₀ + 0x4c288#64 + BitVec.ofNat 64 (2 * i) ∧ i + 1 < y.n1 ∧ v < 48 ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .r15 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ s.regs.get64 .r10 = BitVec.ofNat 64 (v) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrMb x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L862d -/
abbrev L862d (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j i v, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (j) ∧ s.regs.get64 .r11 = 0#64 ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .r14 = dA t₀ ch + 0x15030#64 ∧ s.regs.get64 .r13 = dA t₀ ch + 0x32#64 ∧ s.regs.get64 .rcx = dA t₀ ch + 0x15030#64 + BitVec.ofNat 64 (48 * (j + 1)) ∧ i % 2 = 0 ∧ i < y.n1 ∧ s.regs.get64 .rdi = BitVec.ofNat 64 (i) ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (i + 1) ∧ s.regs.get64 .rsi = sbrA t₀ + 0x4c288#64 + BitVec.ofNat 64 (2 * i) ∧ i + 1 < y.n1 ∧ v < 48 ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .r15 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ s.regs.get64 .r8 = BitVec.ofNat 64 (v) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrMb x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L862d_1 -/
abbrev L862d_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j i, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (j) ∧ s.regs.get64 .r11 = 0#64 ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .r14 = dA t₀ ch + 0x15030#64 ∧ s.regs.get64 .r13 = dA t₀ ch + 0x32#64 ∧ s.regs.get64 .rcx = dA t₀ ch + 0x15030#64 + BitVec.ofNat 64 (48 * (j + 1)) ∧ i % 2 = 0 ∧ i + 2 ≤ y.n1 ∧ s.regs.get64 .rdi = BitVec.ofNat 64 (i + 2) ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (i + 1) ∧ s.regs.get64 .rsi = sbrA t₀ + 0x4c288#64 + BitVec.ofNat 64 (2 * i) ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .r15 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrMb x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L8660 -/
abbrev L8660 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (j) ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .r15 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrMb x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L86a0 -/
abbrev L86a0 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j i, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rbx = dA t₀ ch + 0x15030#64 + BitVec.ofNat 64 (48 * (j + 1)) ∧ s.regs.get64 .r14 = sbrA t₀ + 0x5e340#64 + BitVec.ofNat 64 (48 * j) ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .r15 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ i < (if u8 (y.d ch).freqRes (j + 1) = 0 then y.n0 else y.n1) ∧ s.regs.get64 .r13 = BitVec.ofNat 64 (i) ∧ y.kx1 ≤ u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (i) ∧ u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (i) ≤ u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (i + 1) ∧ u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (i + 1) ≤ y.kx1 + 48 ∧ s.regs.get64 .rax = BitVec.ofNat 64 (u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (i)) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (i + 1)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrMs x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L86b0 -/
abbrev L86b0 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j i, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rbx = dA t₀ ch + 0x15030#64 + BitVec.ofNat 64 (48 * (j + 1)) ∧ s.regs.get64 .r14 = sbrA t₀ + 0x5e340#64 + BitVec.ofNat 64 (48 * j) ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .r15 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ i < (if u8 (y.d ch).freqRes (j + 1) = 0 then y.n0 else y.n1) ∧ s.regs.get64 .r13 = BitVec.ofNat 64 (i) ∧ y.kx1 ≤ u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (i) ∧ u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (i) ≤ u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (i + 1) ∧ u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (i + 1) ≤ y.kx1 + 48 ∧ s.regs.get64 .rax = BitVec.ofNat 64 (u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (i)) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (i + 1)) ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (i) - y.kx1) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrMs x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L86b0_1 -/
abbrev L86b0_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j i, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rbx = dA t₀ ch + 0x15030#64 + BitVec.ofNat 64 (48 * (j + 1)) ∧ s.regs.get64 .r14 = sbrA t₀ + 0x5e340#64 + BitVec.ofNat 64 (48 * j) ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .r15 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ i ≤ (if u8 (y.d ch).freqRes (j + 1) = 0 then y.n0 else y.n1) ∧ s.regs.get64 .r13 = BitVec.ofNat 64 (i) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrMs x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L86d7 -/
abbrev L86d7 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j i, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rbx = dA t₀ ch + 0x15030#64 + BitVec.ofNat 64 (48 * (j + 1)) ∧ s.regs.get64 .r14 = sbrA t₀ + 0x5e340#64 + BitVec.ofNat 64 (48 * j) ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .r15 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ i < (if u8 (y.d ch).freqRes (j + 1) = 0 then y.n0 else y.n1) ∧ s.regs.get64 .r13 = BitVec.ofNat 64 (i) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrMs x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L8700 -/
abbrev L8700 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j i t, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rbx = dA t₀ ch + 0x15030#64 + BitVec.ofNat 64 (48 * (j + 1)) ∧ s.regs.get64 .r14 = sbrA t₀ + 0x5e340#64 + BitVec.ofNat 64 (48 * j) ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .r15 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ i < (if u8 (y.d ch).freqRes (j + 1) = 0 then y.n0 else y.n1) ∧ s.regs.get64 .r13 = BitVec.ofNat 64 (i) ∧ y.kx1 ≤ u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (i) ∧ u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (i) ≤ u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (i + 1) ∧ u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (i + 1) ≤ y.kx1 + 48 ∧ s.regs.get64 .rax = BitVec.ofNat 64 (u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (i)) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (i + 1)) ∧ u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (i) + t < u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (i + 1) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (i) + t - y.kx1) ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (i + 1) - u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (i) - t) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrMs x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L8720 -/
abbrev L8720 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j i, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rbx = dA t₀ ch + 0x15030#64 + BitVec.ofNat 64 (48 * (j + 1)) ∧ s.regs.get64 .r14 = sbrA t₀ + 0x5e340#64 + BitVec.ofNat 64 (48 * j) ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ s.regs.get64 .r15 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ i < (if u8 (y.d ch).freqRes (j + 1) = 0 then y.n0 else y.n1) ∧ s.regs.get64 .r13 = BitVec.ofNat 64 (i) ∧ y.kx1 ≤ u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (i) ∧ u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (i) ≤ u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (i + 1) ∧ u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (i + 1) ≤ y.kx1 + 48 ∧ s.regs.get64 .rax = BitVec.ofNat 64 (u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (i)) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (i + 1)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrMs x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L8740 -/
abbrev L8740 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * j) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrMb x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L8740_1 -/
abbrev L8740_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ j + 1 < (y.d ch).nenv ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (j + 1) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (j + 2) ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .r8 = arg1 t₀ ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * (j + 1)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrMn x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L8790 -/
abbrev L8790 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j = 0 ∧ (y.d ch).nenv = 0 ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .r8 = arg1 t₀ ∧ s.regs.get64 .r10 = dA t₀ ch + 0x15030#64 ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrZ x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L879e -/
abbrev L879e (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rbx = dA t₀ ch ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrM0 x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L879e_1 -/
abbrev L879e_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rbx = dA t₀ ch ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrM0 x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L879e_2 -/
abbrev L879e_2 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j, (x.Keep y.spSet ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ ch < 2 ∧ s.regs.get64 .rbx = dA t₀ ch ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrM0 x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L8818 -/
abbrev L8818 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .r8 = arg1 t₀ ∧ s.regs.get64 .rax = BitVec.ofNat 64 (y.d ch).nenv ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrO8 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L881c -/
abbrev L881c (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .r8 = arg1 t₀ ∧ s.regs.get64 .r10 = dA t₀ ch + 0x15030#64 ∧ s.regs.get64 .rax = BitVec.ofNat 64 (y.d ch).nenv ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrO x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L881c_1 -/
abbrev L881c_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .rax = BitVec.ofNat 64 ((y.d ch).nenv) ∧ s.regs.get64 .r8 = arg1 t₀ ∧ s.regs.get64 .rcx = BitVec.ofNat 64 ((y.d ch).nenv) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrE1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L881c_2 -/
abbrev L881c_2 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .rax = BitVec.ofNat 64 ((y.d ch).nenv) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 ((y.d ch).nenv) ∧ s.regs.get64 .r8 = arg1 t₀ ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (u8 (y.d ch).te (0)) ∧ s.regs.get64 .r14 = BitVec.ofNat 64 (320 * y.kx1) ∧ s.regs.get64 .rdi = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (320 * y.kx1) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrE1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L881c_3 -/
abbrev L881c_3 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 1 ≤ (y.d ch).nenv ∧ s.regs.get64 .rdi = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (320 * y.kx1) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (2 * u8 (y.d ch).te (0)) ∧ s.regs.get64 .r15 = BitVec.ofNat 64 (2 * (u8 (y.d ch).te (1) - u8 (y.d ch).te (0))) ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (u8 (y.d ch).te (0)) ∧ s.regs.get64 .r14 = BitVec.ofNat 64 (320 * y.kx1) ∧ s.regs.get64 .r8 = arg1 t₀ ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI0 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L881c_4 -/
abbrev L881c_4 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 1 ≤ (y.d ch).nenv ∧ s.regs.get64 .r13 = arg1 t₀ ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (u8 (y.d ch).te (0)) ∧ s.regs.get64 .r15 = BitVec.ofNat 64 (2 * (u8 (y.d ch).te (1) - u8 (y.d ch).te (0))) ∧ s.regs.get64 .r14 = BitVec.ofNat 64 (320 * y.kx1) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI0 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L8900 -/
abbrev L8900 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 m, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 1 ≤ (y.d ch).nenv ∧ s.regs.get64 .r13 = arg1 t₀ ∧ s.regs.get64 .r15 = BitVec.ofNat 64 (2 * (u8 (y.d ch).te (1) - u8 (y.d ch).te (0))) ∧ s.regs.get64 .r14 = BitVec.ofNat 64 (320 * y.kx1) ∧ m < y.m1 ∧ m < 48 ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (m) ∧ s.regs.get64 .r12 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (16 + 16 * u8 (y.d ch).te (0) + 320 * (y.kx1 + m + 1)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI0 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L8900_1 -/
abbrev L8900_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 m, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 1 ≤ (y.d ch).nenv ∧ s.regs.get64 .r13 = arg1 t₀ ∧ s.regs.get64 .r15 = BitVec.ofNat 64 (2 * (u8 (y.d ch).te (1) - u8 (y.d ch).te (0))) ∧ s.regs.get64 .r14 = BitVec.ofNat 64 (320 * y.kx1) ∧ 1 ≤ m ∧ m ≤ y.m1 ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (m) ∧ s.regs.get64 .r12 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (16 + 16 * u8 (y.d ch).te (0) + 320 * (y.kx1 + m)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI0 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L8900_2 -/
abbrev L8900_2 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 m, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 1 ≤ (y.d ch).nenv ∧ s.regs.get64 .r13 = arg1 t₀ ∧ s.regs.get64 .r15 = BitVec.ofNat 64 (2 * (u8 (y.d ch).te (1) - u8 (y.d ch).te (0))) ∧ s.regs.get64 .r14 = BitVec.ofNat 64 (320 * y.kx1) ∧ 1 ≤ m ∧ m < y.m1 ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (m) ∧ s.regs.get64 .r12 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (16 + 16 * u8 (y.d ch).te (0) + 320 * (y.kx1 + m)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI0 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L8947 -/
abbrev L8947 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .rax = BitVec.ofNat 64 ((y.d ch).nenv) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrE1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L8947_1 -/
abbrev L8947_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (1) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrN0 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L8970 -/
abbrev L8970 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .r8 = BitVec.ofNat 64 (j) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (j + 1) ∧ s.regs.get64 .rsi = arg1 t₀ ∧ s.regs.get64 .rdi = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrN0 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L8970_1 -/
abbrev L8970_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .r8 = BitVec.ofNat 64 (j + 1) ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (u8 (y.d ch).te (j)) ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (u8 (y.d ch).te (j + 1)) ∧ s.regs.get64 .r14 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (u8 (y.d ch).freqRes (j + 1)) ∧ s.regs.get64 .rsi = arg1 t₀ ∧ s.regs.get64 .rdi = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrN0 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L89e0 -/
abbrev L89e0 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j p, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rsi = arg1 t₀ ∧ s.regs.get64 .r14 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (2 * (u8 (y.d ch).te (j + 1) - u8 (y.d ch).te (j))) ∧ s.regs.get64 .r8 = BitVec.ofNat 64 (j + 1) ∧ s.regs.get64 .rdi = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) ∧ p ≤ (if u8 (y.d ch).freqRes (j + 1) = 0 then y.n0 else y.n1) ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (p) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrN x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L89f3 -/
abbrev L89f3 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j p, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rsi = arg1 t₀ ∧ s.regs.get64 .r14 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (2 * (u8 (y.d ch).te (j + 1) - u8 (y.d ch).te (j))) ∧ s.regs.get64 .r8 = BitVec.ofNat 64 (j + 1) ∧ s.regs.get64 .rdi = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) ∧ p ≤ (if u8 (y.d ch).freqRes (j + 1) = 0 then y.n0 else y.n1) ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (p) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (u8 (y.d ch).freqRes (j + 1)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrN x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L89f3_1 -/
abbrev L89f3_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j p, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .r14 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (2 * (u8 (y.d ch).te (j + 1) - u8 (y.d ch).te (j))) ∧ p < (if u8 (y.d ch).freqRes (j + 1) = 0 then y.n0 else y.n1) ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (p + 1) ∧ u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (p) < u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (p + 1) ∧ s.regs.get64 .r13 = BitVec.ofNat 64 (u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (p)) ∧ s.regs.get64 .r15 = BitVec.ofNat 64 (4 * u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (p)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrNP x t₀ ch c0 y j p))
/-- ff_aac_sbr_apply.L8a50 -/
abbrev L8a50 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j p q, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .r14 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (2 * (u8 (y.d ch).te (j + 1) - u8 (y.d ch).te (j))) ∧ p < (if u8 (y.d ch).freqRes (j + 1) = 0 then y.n0 else y.n1) ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (p + 1) ∧ u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (p) < u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (p + 1) ∧ u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (p) ≤ q ∧ q < u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (p + 1) ∧ s.regs.get64 .r13 = BitVec.ofNat 64 (q) ∧ s.regs.get64 .r15 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (16 + 16 * u8 (y.d ch).te (j) + 320 * q) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrNP x t₀ ch c0 y j p))
/-- ff_aac_sbr_apply.L8a50_1 -/
abbrev L8a50_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j p q, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .r14 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (2 * (u8 (y.d ch).te (j + 1) - u8 (y.d ch).te (j))) ∧ p < (if u8 (y.d ch).freqRes (j + 1) = 0 then y.n0 else y.n1) ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (p + 1) ∧ u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (p) < u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (p + 1) ∧ u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (p) ≤ q ∧ q < u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (p + 1) ∧ s.regs.get64 .r13 = BitVec.ofNat 64 (q) ∧ s.regs.get64 .r15 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (16 + 16 * u8 (y.d ch).te (j) + 320 * q) ∧ s.regs.get64 .rdi = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (16 + 16 * u8 (y.d ch).te (j) + 320 * q) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (2 * (u8 (y.d ch).te (j + 1) - u8 (y.d ch).te (j))) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrNP x t₀ ch c0 y j p))
/-- ff_aac_sbr_apply.L8a50_2 -/
abbrev L8a50_2 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j p q, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .r14 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (2 * (u8 (y.d ch).te (j + 1) - u8 (y.d ch).te (j))) ∧ p < (if u8 (y.d ch).freqRes (j + 1) = 0 then y.n0 else y.n1) ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (p + 1) ∧ u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (p) < u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (p + 1) ∧ u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (p) ≤ q ∧ q < u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (p + 1) ∧ s.regs.get64 .r13 = BitVec.ofNat 64 (q) ∧ s.regs.get64 .r15 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (16 + 16 * u8 (y.d ch).te (j) + 320 * q) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrNP x t₀ ch c0 y j p))
/-- ff_aac_sbr_apply.L8a50_3 -/
abbrev L8a50_3 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j p, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rsi = arg1 t₀ ∧ s.regs.get64 .r14 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (2 * (u8 (y.d ch).te (j + 1) - u8 (y.d ch).te (j))) ∧ s.regs.get64 .r8 = BitVec.ofNat 64 (j + 1) ∧ s.regs.get64 .rdi = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) ∧ p < (if u8 (y.d ch).freqRes (j + 1) = 0 then y.n0 else y.n1) ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (p + 1) ∧ u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (p) < u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (p + 1) ∧ s.status.cf = true ∧ s.regs.get64 .rax = BitVec.ofNat 64 (u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (p)) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (p + 1)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrNP x t₀ ch c0 y j p))
/-- ff_aac_sbr_apply.L8ad0 -/
abbrev L8ad0 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j p c, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rsi = arg1 t₀ ∧ s.regs.get64 .r14 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (2 * (u8 (y.d ch).te (j + 1) - u8 (y.d ch).te (j))) ∧ s.regs.get64 .r8 = BitVec.ofNat 64 (j + 1) ∧ s.regs.get64 .rdi = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) ∧ p < (if u8 (y.d ch).freqRes (j + 1) = 0 then y.n0 else y.n1) ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (p + 1) ∧ u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (p) < u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (p + 1) ∧ c < 48 ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (c) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (y.kx1 + c + 1) ∧ y.kx1 + c < u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (p + 1) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrNP x t₀ ch c0 y j p))
/-- ff_aac_sbr_apply.L8ad0_1 -/
abbrev L8ad0_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j p c, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .rsi = arg1 t₀ ∧ s.regs.get64 .r14 = (if u8 (y.d ch).freqRes (j + 1) = 0 then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64) ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (2 * (u8 (y.d ch).te (j + 1) - u8 (y.d ch).te (j))) ∧ s.regs.get64 .r8 = BitVec.ofNat 64 (j + 1) ∧ s.regs.get64 .rdi = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) ∧ p < (if u8 (y.d ch).freqRes (j + 1) = 0 then y.n0 else y.n1) ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (p + 1) ∧ u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (p) < u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (p + 1) ∧ c < 48 ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (c) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (y.kx1 + c + 1) ∧ y.kx1 + c < u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (p + 1) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrNP x t₀ ch c0 y j p))
/-- ff_aac_sbr_apply.L8b00 -/
abbrev L8b00 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ j < (y.d ch).nenv ∧ s.regs.get64 .r8 = BitVec.ofNat 64 (j + 1) ∧ s.regs.get64 .rsi = arg1 t₀ ∧ s.regs.get64 .rdi = arg1 t₀ + BitVec.ofNat 64 (0xc0 * j) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrN x t₀ ch c0 y j))
/-- ff_aac_sbr_apply.L8b2a -/
abbrev L8b2a (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 1 ≤ (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (y.m1) ∧ s.regs.get64 .r14 = BitVec.ofNat 64 (320 * y.kx1) ∧ s.regs.get64 .r8 = arg1 t₀ ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI0 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L8b4f -/
abbrev L8b4f (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0 ne kk, ApplyC x t₀ ∧ Base t₀ s ∧ ch < 2 ∧ c0.getLsbD 0 = decide (ch = 0) ∧ s.regs.get64 .r8 = arg1 t₀ ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (kk) ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ y.start ≠ 0 ∧ ne = (y.d ch).nenv ∧ kk ≤ 64 ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrH x t₀ e ch c0 ne))
/-- ff_aac_sbr_apply.L8b6b -/
abbrev L8b6b (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => False
/-- ff_aac_sbr_apply.L8b77 -/
abbrev L8b77 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 2 ≤ (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 ((y.d ch).nenv) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 ((y.d ch).nenv) ∧ (s.regs.get64 .rsi).toNat % 256 = 0 ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .rdi = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (320 * y.kx1) ∧ s.regs.get64 .r8 = arg1 t₀ ∧ s.regs.get64 .r14 = BitVec.ofNat 64 (320 * y.kx1) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI0 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L8b77_1 -/
abbrev L8b77_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 2 ≤ (y.d ch).nenv ∧ s.regs.get64 .rdi = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (320 * y.kx1) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (2 * u8 (y.d ch).te (1)) ∧ s.regs.get64 .r15 = BitVec.ofNat 64 (2 * (u8 (y.d ch).te (2) - u8 (y.d ch).te (1))) ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (u8 (y.d ch).te (1)) ∧ s.regs.get64 .r8 = arg1 t₀ ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L8b77_2 -/
abbrev L8b77_2 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 2 ≤ (y.d ch).nenv ∧ s.regs.get64 .r13 = arg1 t₀ ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (u8 (y.d ch).te (1)) ∧ s.regs.get64 .r15 = BitVec.ofNat 64 (2 * (u8 (y.d ch).te (2) - u8 (y.d ch).te (1))) ∧ s.regs.get64 .r14 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (320 * y.kx1) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L8bf0 -/
abbrev L8bf0 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 m, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 2 ≤ (y.d ch).nenv ∧ s.regs.get64 .r13 = arg1 t₀ ∧ s.regs.get64 .r15 = BitVec.ofNat 64 (2 * (u8 (y.d ch).te (2) - u8 (y.d ch).te (1))) ∧ s.regs.get64 .r14 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (320 * y.kx1) ∧ m < y.m1 ∧ m < 48 ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (m) ∧ s.regs.get64 .r12 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (16 + 16 * u8 (y.d ch).te (1) + 320 * (y.kx1 + m + 1)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L8bf0_1 -/
abbrev L8bf0_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 m, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 2 ≤ (y.d ch).nenv ∧ s.regs.get64 .r13 = arg1 t₀ ∧ s.regs.get64 .r15 = BitVec.ofNat 64 (2 * (u8 (y.d ch).te (2) - u8 (y.d ch).te (1))) ∧ s.regs.get64 .r14 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (320 * y.kx1) ∧ 1 ≤ m ∧ m ≤ y.m1 ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (m) ∧ s.regs.get64 .r12 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (16 + 16 * u8 (y.d ch).te (1) + 320 * (y.kx1 + m)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L8bf0_2 -/
abbrev L8bf0_2 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 m, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 2 ≤ (y.d ch).nenv ∧ s.regs.get64 .r13 = arg1 t₀ ∧ s.regs.get64 .r15 = BitVec.ofNat 64 (2 * (u8 (y.d ch).te (2) - u8 (y.d ch).te (1))) ∧ s.regs.get64 .r14 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (320 * y.kx1) ∧ 1 ≤ m ∧ m < y.m1 ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (m) ∧ s.regs.get64 .r12 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (16 + 16 * u8 (y.d ch).te (1) + 320 * (y.kx1 + m)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L8c33 -/
abbrev L8c33 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 2 ≤ (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (y.m1) ∧ s.regs.get64 .r14 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (320 * y.kx1) ∧ s.regs.get64 .r8 = arg1 t₀ ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L8c4c -/
abbrev L8c4c (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 2 ≤ (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 ((y.d ch).nenv) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 ((y.d ch).nenv) ∧ (s.regs.get64 .rdx).toNat % 256 = 0 ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .rdi = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (320 * y.kx1) ∧ s.regs.get64 .r8 = arg1 t₀ ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L8c4c_1 -/
abbrev L8c4c_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 3 ≤ (y.d ch).nenv ∧ s.regs.get64 .rdi = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (320 * y.kx1) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (2 * u8 (y.d ch).te (2)) ∧ s.regs.get64 .r15 = BitVec.ofNat 64 (u8 (y.d ch).te (3) - u8 (y.d ch).te (2)) ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (u8 (y.d ch).te (2)) ∧ s.regs.get64 .r8 = arg1 t₀ ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L8c4c_2 -/
abbrev L8c4c_2 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 3 ≤ (y.d ch).nenv ∧ s.regs.get64 .r13 = arg1 t₀ ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (u8 (y.d ch).te (2)) ∧ s.regs.get64 .r15 = BitVec.ofNat 64 (2 * (u8 (y.d ch).te (3) - u8 (y.d ch).te (2))) ∧ s.regs.get64 .r14 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (320 * y.kx1) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L8cc9 -/
abbrev L8cc9 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 m, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 3 ≤ (y.d ch).nenv ∧ s.regs.get64 .r13 = arg1 t₀ ∧ s.regs.get64 .r15 = BitVec.ofNat 64 (2 * (u8 (y.d ch).te (3) - u8 (y.d ch).te (2))) ∧ s.regs.get64 .r14 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (320 * y.kx1) ∧ m < y.m1 ∧ m < 48 ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (m) ∧ s.regs.get64 .r12 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (16 + 16 * u8 (y.d ch).te (2) + 320 * (y.kx1 + m + 1)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L8cc9_1 -/
abbrev L8cc9_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 m, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 3 ≤ (y.d ch).nenv ∧ s.regs.get64 .r13 = arg1 t₀ ∧ s.regs.get64 .r15 = BitVec.ofNat 64 (2 * (u8 (y.d ch).te (3) - u8 (y.d ch).te (2))) ∧ s.regs.get64 .r14 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (320 * y.kx1) ∧ 1 ≤ m ∧ m ≤ y.m1 ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (m) ∧ s.regs.get64 .r12 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (16 + 16 * u8 (y.d ch).te (2) + 320 * (y.kx1 + m)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L8cc9_2 -/
abbrev L8cc9_2 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 m, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 3 ≤ (y.d ch).nenv ∧ s.regs.get64 .r13 = arg1 t₀ ∧ s.regs.get64 .r15 = BitVec.ofNat 64 (2 * (u8 (y.d ch).te (3) - u8 (y.d ch).te (2))) ∧ s.regs.get64 .r14 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (320 * y.kx1) ∧ 1 ≤ m ∧ m < y.m1 ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (m) ∧ s.regs.get64 .r12 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (16 + 16 * u8 (y.d ch).te (2) + 320 * (y.kx1 + m)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L8d0c -/
abbrev L8d0c (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 3 ≤ (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (y.m1) ∧ s.regs.get64 .r14 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (320 * y.kx1) ∧ s.regs.get64 .r8 = arg1 t₀ ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L8d26 -/
abbrev L8d26 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 3 ≤ (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 ((y.d ch).nenv) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 ((y.d ch).nenv) ∧ (s.regs.get64 .rsi).toNat % 256 = 0 ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .rdi = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (320 * y.kx1) ∧ s.regs.get64 .r8 = arg1 t₀ ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L8d26_1 -/
abbrev L8d26_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 4 ≤ (y.d ch).nenv ∧ s.regs.get64 .rdi = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (320 * y.kx1) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (2 * u8 (y.d ch).te (3)) ∧ s.regs.get64 .r15 = BitVec.ofNat 64 (u8 (y.d ch).te (4) - u8 (y.d ch).te (3)) ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (u8 (y.d ch).te (3)) ∧ s.regs.get64 .r8 = arg1 t₀ ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L8d26_2 -/
abbrev L8d26_2 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 4 ≤ (y.d ch).nenv ∧ s.regs.get64 .r13 = arg1 t₀ ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (u8 (y.d ch).te (3)) ∧ s.regs.get64 .r15 = BitVec.ofNat 64 (2 * (u8 (y.d ch).te (4) - u8 (y.d ch).te (3))) ∧ s.regs.get64 .r14 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (320 * y.kx1) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L8da3 -/
abbrev L8da3 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 m, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 4 ≤ (y.d ch).nenv ∧ s.regs.get64 .r13 = arg1 t₀ ∧ s.regs.get64 .r15 = BitVec.ofNat 64 (2 * (u8 (y.d ch).te (4) - u8 (y.d ch).te (3))) ∧ s.regs.get64 .r14 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (320 * y.kx1) ∧ m < y.m1 ∧ m < 48 ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (m) ∧ s.regs.get64 .r12 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (16 + 16 * u8 (y.d ch).te (3) + 320 * (y.kx1 + m + 1)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L8da3_1 -/
abbrev L8da3_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 m, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 4 ≤ (y.d ch).nenv ∧ s.regs.get64 .r13 = arg1 t₀ ∧ s.regs.get64 .r15 = BitVec.ofNat 64 (2 * (u8 (y.d ch).te (4) - u8 (y.d ch).te (3))) ∧ s.regs.get64 .r14 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (320 * y.kx1) ∧ 1 ≤ m ∧ m ≤ y.m1 ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (m) ∧ s.regs.get64 .r12 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (16 + 16 * u8 (y.d ch).te (3) + 320 * (y.kx1 + m)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L8da3_2 -/
abbrev L8da3_2 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 m, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 4 ≤ (y.d ch).nenv ∧ s.regs.get64 .r13 = arg1 t₀ ∧ s.regs.get64 .r15 = BitVec.ofNat 64 (2 * (u8 (y.d ch).te (4) - u8 (y.d ch).te (3))) ∧ s.regs.get64 .r14 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (320 * y.kx1) ∧ 1 ≤ m ∧ m < y.m1 ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (m) ∧ s.regs.get64 .r12 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (16 + 16 * u8 (y.d ch).te (3) + 320 * (y.kx1 + m)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L8de6 -/
abbrev L8de6 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 4 ≤ (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (y.m1) ∧ s.regs.get64 .r14 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (320 * y.kx1) ∧ s.regs.get64 .r8 = arg1 t₀ ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L8dff -/
abbrev L8dff (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 4 ≤ (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 ((y.d ch).nenv) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 ((y.d ch).nenv) ∧ (s.regs.get64 .rdx).toNat % 256 = 0 ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .rdi = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (320 * y.kx1) ∧ s.regs.get64 .r8 = arg1 t₀ ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L8dff_1 -/
abbrev L8dff_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 5 ≤ (y.d ch).nenv ∧ s.regs.get64 .rdi = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (320 * y.kx1) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (2 * u8 (y.d ch).te (4)) ∧ s.regs.get64 .r15 = BitVec.ofNat 64 (u8 (y.d ch).te (5) - u8 (y.d ch).te (4)) ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (u8 (y.d ch).te (4)) ∧ s.regs.get64 .r8 = arg1 t₀ ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L8dff_2 -/
abbrev L8dff_2 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 5 ≤ (y.d ch).nenv ∧ s.regs.get64 .r13 = arg1 t₀ ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (u8 (y.d ch).te (4)) ∧ s.regs.get64 .r15 = BitVec.ofNat 64 (2 * (u8 (y.d ch).te (5) - u8 (y.d ch).te (4))) ∧ s.regs.get64 .r14 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (320 * y.kx1) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L8e7c -/
abbrev L8e7c (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 m, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 5 ≤ (y.d ch).nenv ∧ s.regs.get64 .r13 = arg1 t₀ ∧ s.regs.get64 .r15 = BitVec.ofNat 64 (2 * (u8 (y.d ch).te (5) - u8 (y.d ch).te (4))) ∧ s.regs.get64 .r14 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (320 * y.kx1) ∧ m < y.m1 ∧ m < 48 ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (m) ∧ s.regs.get64 .r12 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (16 + 16 * u8 (y.d ch).te (4) + 320 * (y.kx1 + m + 1)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L8e7c_1 -/
abbrev L8e7c_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 m, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 5 ≤ (y.d ch).nenv ∧ s.regs.get64 .r13 = arg1 t₀ ∧ s.regs.get64 .r15 = BitVec.ofNat 64 (2 * (u8 (y.d ch).te (5) - u8 (y.d ch).te (4))) ∧ s.regs.get64 .r14 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (320 * y.kx1) ∧ 1 ≤ m ∧ m ≤ y.m1 ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (m) ∧ s.regs.get64 .r12 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (16 + 16 * u8 (y.d ch).te (4) + 320 * (y.kx1 + m)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L8e7c_2 -/
abbrev L8e7c_2 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 m, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 5 ≤ (y.d ch).nenv ∧ s.regs.get64 .r13 = arg1 t₀ ∧ s.regs.get64 .r15 = BitVec.ofNat 64 (2 * (u8 (y.d ch).te (5) - u8 (y.d ch).te (4))) ∧ s.regs.get64 .r14 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (320 * y.kx1) ∧ 1 ≤ m ∧ m < y.m1 ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (m) ∧ s.regs.get64 .r12 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (16 + 16 * u8 (y.d ch).te (4) + 320 * (y.kx1 + m)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L8ebf -/
abbrev L8ebf (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 5 ≤ (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (y.m1) ∧ s.regs.get64 .r14 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (320 * y.kx1) ∧ s.regs.get64 .r8 = arg1 t₀ ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L8ed9 -/
abbrev L8ed9 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 5 ≤ (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 ((y.d ch).nenv) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 ((y.d ch).nenv) ∧ (s.regs.get64 .rsi).toNat % 256 = 0 ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .rdi = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (320 * y.kx1) ∧ s.regs.get64 .r8 = arg1 t₀ ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L8ed9_1 -/
abbrev L8ed9_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 6 ≤ (y.d ch).nenv ∧ s.regs.get64 .rdi = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (320 * y.kx1) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (2 * u8 (y.d ch).te (5)) ∧ s.regs.get64 .r15 = BitVec.ofNat 64 (u8 (y.d ch).te (6) - u8 (y.d ch).te (5)) ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (u8 (y.d ch).te (5)) ∧ s.regs.get64 .r8 = arg1 t₀ ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L8ed9_2 -/
abbrev L8ed9_2 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 6 ≤ (y.d ch).nenv ∧ s.regs.get64 .r13 = arg1 t₀ ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (u8 (y.d ch).te (5)) ∧ s.regs.get64 .r15 = BitVec.ofNat 64 (2 * (u8 (y.d ch).te (6) - u8 (y.d ch).te (5))) ∧ s.regs.get64 .r14 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (320 * y.kx1) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L8f56 -/
abbrev L8f56 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 m, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 6 ≤ (y.d ch).nenv ∧ s.regs.get64 .r13 = arg1 t₀ ∧ s.regs.get64 .r15 = BitVec.ofNat 64 (2 * (u8 (y.d ch).te (6) - u8 (y.d ch).te (5))) ∧ s.regs.get64 .r14 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (320 * y.kx1) ∧ m < y.m1 ∧ m < 48 ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (m) ∧ s.regs.get64 .r12 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (16 + 16 * u8 (y.d ch).te (5) + 320 * (y.kx1 + m + 1)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L8f56_1 -/
abbrev L8f56_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 m, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 6 ≤ (y.d ch).nenv ∧ s.regs.get64 .r13 = arg1 t₀ ∧ s.regs.get64 .r15 = BitVec.ofNat 64 (2 * (u8 (y.d ch).te (6) - u8 (y.d ch).te (5))) ∧ s.regs.get64 .r14 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (320 * y.kx1) ∧ 1 ≤ m ∧ m ≤ y.m1 ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (m) ∧ s.regs.get64 .r12 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (16 + 16 * u8 (y.d ch).te (5) + 320 * (y.kx1 + m)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L8f56_2 -/
abbrev L8f56_2 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 m, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 6 ≤ (y.d ch).nenv ∧ s.regs.get64 .r13 = arg1 t₀ ∧ s.regs.get64 .r15 = BitVec.ofNat 64 (2 * (u8 (y.d ch).te (6) - u8 (y.d ch).te (5))) ∧ s.regs.get64 .r14 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (320 * y.kx1) ∧ 1 ≤ m ∧ m < y.m1 ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (m) ∧ s.regs.get64 .r12 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (16 + 16 * u8 (y.d ch).te (5) + 320 * (y.kx1 + m)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L8f93 -/
abbrev L8f93 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 6 ≤ (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (y.m1) ∧ s.regs.get64 .r14 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (320 * y.kx1) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L8fa4 -/
abbrev L8fa4 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 6 ≤ (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 ((y.d ch).nenv) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 ((y.d ch).nenv) ∧ (s.regs.get64 .rdx).toNat % 256 = 0 ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .rdi = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (320 * y.kx1) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L8fa4_1 -/
abbrev L8fa4_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 7 ≤ (y.d ch).nenv ∧ s.regs.get64 .r14 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (320 * y.kx1) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (2 * u8 (y.d ch).te (6)) ∧ s.regs.get64 .r15 = BitVec.ofNat 64 (u8 (y.d ch).te (7) - u8 (y.d ch).te (6)) ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (u8 (y.d ch).te (6)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L8fa4_2 -/
abbrev L8fa4_2 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 7 ≤ (y.d ch).nenv ∧ s.regs.get64 .r14 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (320 * y.kx1) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (2 * u8 (y.d ch).te (6)) ∧ s.regs.get64 .r15 = BitVec.ofNat 64 (u8 (y.d ch).te (7) - u8 (y.d ch).te (6)) ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (u8 (y.d ch).te (6)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L8fa4_3 -/
abbrev L8fa4_3 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 7 ≤ (y.d ch).nenv ∧ s.regs.get64 .r13 = arg1 t₀ ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (u8 (y.d ch).te (6)) ∧ s.regs.get64 .r15 = BitVec.ofNat 64 (2 * (u8 (y.d ch).te (7) - u8 (y.d ch).te (6))) ∧ s.regs.get64 .r14 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (320 * y.kx1) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L9026 -/
abbrev L9026 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 m, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 7 ≤ (y.d ch).nenv ∧ s.regs.get64 .r13 = arg1 t₀ ∧ s.regs.get64 .r15 = BitVec.ofNat 64 (2 * (u8 (y.d ch).te (7) - u8 (y.d ch).te (6))) ∧ s.regs.get64 .r14 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (320 * y.kx1) ∧ m < y.m1 ∧ m < 48 ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (m) ∧ s.regs.get64 .r12 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (16 + 16 * u8 (y.d ch).te (6) + 320 * (y.kx1 + m + 1)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L9026_1 -/
abbrev L9026_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 m, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 7 ≤ (y.d ch).nenv ∧ s.regs.get64 .r13 = arg1 t₀ ∧ s.regs.get64 .r15 = BitVec.ofNat 64 (2 * (u8 (y.d ch).te (7) - u8 (y.d ch).te (6))) ∧ s.regs.get64 .r14 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (320 * y.kx1) ∧ 1 ≤ m ∧ m ≤ y.m1 ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (m) ∧ s.regs.get64 .r12 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (16 + 16 * u8 (y.d ch).te (6) + 320 * (y.kx1 + m)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L9026_2 -/
abbrev L9026_2 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 m, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 7 ≤ (y.d ch).nenv ∧ s.regs.get64 .r13 = arg1 t₀ ∧ s.regs.get64 .r15 = BitVec.ofNat 64 (2 * (u8 (y.d ch).te (7) - u8 (y.d ch).te (6))) ∧ s.regs.get64 .r14 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (320 * y.kx1) ∧ 1 ≤ m ∧ m < y.m1 ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (m) ∧ s.regs.get64 .r12 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (16 + 16 * u8 (y.d ch).te (6) + 320 * (y.kx1 + m)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L9063 -/
abbrev L9063 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ s.regs.get64 .rax = BitVec.ofNat 64 ((y.d ch).nenv) ∧ s.regs.get64 .rbx = dA t₀ ch ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L9070 -/
abbrev L9070 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 7 ≤ (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (y.m1) ∧ s.regs.get64 .r14 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (320 * y.kx1) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L907f -/
abbrev L907f (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 7 ≤ (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 ((y.d ch).nenv) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 ((y.d ch).nenv) ∧ (s.regs.get64 .rsi).toNat % 256 = 0 ∧ s.regs.get64 .r14 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (320 * y.kx1) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L907f_1 -/
abbrev L907f_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 8 ≤ (y.d ch).nenv ∧ s.regs.get64 .r14 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (320 * y.kx1) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (2 * u8 (y.d ch).te (7)) ∧ s.regs.get64 .r15 = BitVec.ofNat 64 (u8 (y.d ch).te (8) - u8 (y.d ch).te (7)) ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (u8 (y.d ch).te (7)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L907f_2 -/
abbrev L907f_2 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 8 ≤ (y.d ch).nenv ∧ s.regs.get64 .r14 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (320 * y.kx1) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (2 * u8 (y.d ch).te (7)) ∧ s.regs.get64 .r15 = BitVec.ofNat 64 (u8 (y.d ch).te (8) - u8 (y.d ch).te (7)) ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (u8 (y.d ch).te (7)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L907f_3 -/
abbrev L907f_3 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 8 ≤ (y.d ch).nenv ∧ s.regs.get64 .r14 = arg1 t₀ ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (u8 (y.d ch).te (7)) ∧ s.regs.get64 .r15 = BitVec.ofNat 64 (2 * (u8 (y.d ch).te (8) - u8 (y.d ch).te (7))) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L90f9 -/
abbrev L90f9 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 m, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 8 ≤ (y.d ch).nenv ∧ s.regs.get64 .r14 = arg1 t₀ ∧ s.regs.get64 .r15 = BitVec.ofNat 64 (2 * (u8 (y.d ch).te (8) - u8 (y.d ch).te (7))) ∧ m < y.m1 ∧ m < 48 ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (m) ∧ s.regs.get64 .r12 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (16 + 16 * u8 (y.d ch).te (7) + 320 * (y.kx1 + m + 1)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L90f9_1 -/
abbrev L90f9_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 m, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 8 ≤ (y.d ch).nenv ∧ s.regs.get64 .r14 = arg1 t₀ ∧ s.regs.get64 .r15 = BitVec.ofNat 64 (2 * (u8 (y.d ch).te (8) - u8 (y.d ch).te (7))) ∧ 1 ≤ m ∧ m ≤ y.m1 ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (m) ∧ s.regs.get64 .r12 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (16 + 16 * u8 (y.d ch).te (7) + 320 * (y.kx1 + m)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L90f9_2 -/
abbrev L90f9_2 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 m, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 8 ≤ (y.d ch).nenv ∧ s.regs.get64 .r14 = arg1 t₀ ∧ s.regs.get64 .r15 = BitVec.ofNat 64 (2 * (u8 (y.d ch).te (8) - u8 (y.d ch).te (7))) ∧ 1 ≤ m ∧ m < y.m1 ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (m) ∧ s.regs.get64 .r12 = (sbrA t₀ + 0x4eb40#64) + BitVec.ofNat 64 (16 + 16 * u8 (y.d ch).te (7) + 320 * (y.kx1 + m)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L913a -/
abbrev L913a (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ s.regs.get64 .rax = BitVec.ofNat 64 ((y.d ch).nenv) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L9146 -/
abbrev L9146 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ s.regs.get64 .rax = BitVec.ofNat 64 (y.d ch).nenv ∧ s.regs.get64 .rbx = dA t₀ ch ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrX x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L914e -/
abbrev L914e (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ s.regs.get64 .rbx = dA t₀ ch ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrX x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L914e_1 -/
abbrev L914e_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ s.regs.get64 .rbx = dA t₀ ch ∧ 1 ≤ y.nlim ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrGa1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L914e_2 -/
abbrev L914e_2 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ s.regs.get64 .rbx = dA t₀ ch ∧ 1 ≤ y.nlim ∧ s.regs.get64 .r10 = arg1 t₀ ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.kx1) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrGa2 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L914e_3 -/
abbrev L914e_3 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ s.regs.get64 .rbx = dA t₀ ch ∧ 1 ≤ y.nlim ∧ s.regs.get64 .r10 = arg1 t₀ ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.kx1) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrGe0 x t₀ ch c0 y 0))
/-- ff_aac_sbr_apply.L91c0 -/
abbrev L91c0 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 ee kk, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ ee < (y.d ch).nenv ∧ 1 ≤ y.nlim ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (ee) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.kx1) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r11 = sbrA t₀ + 0x5f6c0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r9 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r8 = sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .rdi = sbrA t₀ + 0x5f6c4#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrGb x t₀ ch c0 y ee kk))
/-- ff_aac_sbr_apply.L91f7 -/
abbrev L91f7 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 ee, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ ee < (y.d ch).nenv ∧ 1 ≤ y.nlim ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (ee) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.kx1) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r11 = sbrA t₀ + 0x5f6c0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r9 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r8 = sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .rdi = sbrA t₀ + 0x5f6c4#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrGe0 x t₀ ch c0 y ee))
/-- ff_aac_sbr_apply.L9206 -/
abbrev L9206 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 ee, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ ee < (y.d ch).nenv ∧ 1 ≤ y.nlim ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (ee) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.kx1) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r11 = sbrA t₀ + 0x5f6c0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r9 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r8 = sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .rdi = sbrA t₀ + 0x5f6c4#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrGe0 x t₀ ch c0 y ee))
/-- ff_aac_sbr_apply.L9215 -/
abbrev L9215 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 ee, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ ee < (y.d ch).nenv ∧ 1 ≤ y.nlim ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (ee) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.kx1) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r11 = sbrA t₀ + 0x5f6c0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r9 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r8 = sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .rdi = sbrA t₀ + 0x5f6c4#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrGe0 x t₀ ch c0 y ee))
/-- ff_aac_sbr_apply.L9215_1 -/
abbrev L9215_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 ee, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ ee < (y.d ch).nenv ∧ 1 ≤ y.nlim ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (ee) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.kx1) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r11 = sbrA t₀ + 0x5f6c0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r9 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r8 = sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .rdi = sbrA t₀ + 0x5f6c4#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrGe1 x t₀ ch c0 y ee))
/-- ff_aac_sbr_apply.L9215_2 -/
abbrev L9215_2 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 ee, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ ee < (y.d ch).nenv ∧ 1 ≤ y.nlim ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (ee) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.kx1) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r11 = sbrA t₀ + 0x5f6c0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r9 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r8 = sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .rdi = sbrA t₀ + 0x5f6c4#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrGe2 x t₀ ch c0 y ee))
/-- ff_aac_sbr_apply.L9215_3 -/
abbrev L9215_3 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 ee, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ ee < (y.d ch).nenv ∧ 1 ≤ y.nlim ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (ee) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.kx1) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r11 = sbrA t₀ + 0x5f6c0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r9 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r8 = sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .rdi = sbrA t₀ + 0x5f6c4#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrGe3 x t₀ ch c0 y ee))
/-- ff_aac_sbr_apply.L9215_4 -/
abbrev L9215_4 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 ee, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ ee < (y.d ch).nenv ∧ 1 ≤ y.nlim ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (ee) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.kx1) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r11 = sbrA t₀ + 0x5f6c0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r9 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r8 = sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .rdi = sbrA t₀ + 0x5f6c4#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrGe4 x t₀ ch c0 y ee))
/-- ff_aac_sbr_apply.L9215_5 -/
abbrev L9215_5 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 ee, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ ee < (y.d ch).nenv ∧ 1 ≤ y.nlim ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (ee) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.kx1) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r11 = sbrA t₀ + 0x5f6c0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r9 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r8 = sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .rdi = sbrA t₀ + 0x5f6c4#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrGe5 x t₀ ch c0 y ee))
/-- ff_aac_sbr_apply.L9290 -/
abbrev L9290 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 ee kk, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ ee < (y.d ch).nenv ∧ kk < y.nlim ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (kk + 1) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.kx1) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r11 = sbrA t₀ + 0x5f6c0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r9 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r8 = sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .rdi = sbrA t₀ + 0x5f6c4#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (ee) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (u16 y.ftLim (kk + 1)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrGb x t₀ ch c0 y ee kk))
/-- ff_aac_sbr_apply.L929e -/
abbrev L929e (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 ee kk, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ ee < (y.d ch).nenv ∧ kk < y.nlim ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (ee) ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (kk) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (u16 y.ftLim (kk)) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.kx1) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r11 = sbrA t₀ + 0x5f6c0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r9 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r8 = sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .rdi = sbrA t₀ + 0x5f6c4#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrGk x t₀ ch c0 y ee))
/-- ff_aac_sbr_apply.L929e_1 -/
abbrev L929e_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 ee kk, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ ee < (y.d ch).nenv ∧ kk < y.nlim ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (kk + 1) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.kx1) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r11 = sbrA t₀ + 0x5f6c0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r9 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r8 = sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .rdi = sbrA t₀ + 0x5f6c4#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (ee) ∧ s.regs.get64 .r13 = BitVec.ofNat 64 ((u16 y.ftLim (kk) - y.kx1)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrGb x t₀ ch c0 y ee kk))
/-- ff_aac_sbr_apply.L9300 -/
abbrev L9300 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 ee kk mm, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ ee < (y.d ch).nenv ∧ kk < y.nlim ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (kk + 1) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.kx1) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r11 = sbrA t₀ + 0x5f6c0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r9 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r8 = sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .rdi = sbrA t₀ + 0x5f6c4#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ (u16 y.ftLim (kk) - y.kx1) ≤ mm ∧ mm < (u16 y.ftLim (kk + 1) - y.kx1) ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (48) ∧ s.regs.get64 .r12 = dA t₀ ch + 0x15030#64 + BitVec.ofNat 64 (0x30 * (ee + 1)) ∧ s.regs.get64 .r13 = BitVec.ofNat 64 ((u16 y.ftLim (kk) - y.kx1)) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (mm) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (u16 y.ftLim (kk + 1)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrGb x t₀ ch c0 y ee kk))
/-- ff_aac_sbr_apply.L9300_1 -/
abbrev L9300_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 ee kk mm, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ ee < (y.d ch).nenv ∧ kk < y.nlim ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (kk + 1) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.kx1) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r11 = sbrA t₀ + 0x5f6c0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r9 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r8 = sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .rdi = sbrA t₀ + 0x5f6c4#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ (u16 y.ftLim (kk) - y.kx1) ≤ mm ∧ mm < (u16 y.ftLim (kk + 1) - y.kx1) ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (48) ∧ s.regs.get64 .r12 = dA t₀ ch + 0x15030#64 + BitVec.ofNat 64 (0x30 * (ee + 1)) ∧ s.regs.get64 .r13 = BitVec.ofNat 64 ((u16 y.ftLim (kk) - y.kx1)) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (mm) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (u16 y.ftLim (kk + 1)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrGb x t₀ ch c0 y ee kk))
/-- ff_aac_sbr_apply.L9300_2 -/
abbrev L9300_2 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 ee kk mm, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ ee < (y.d ch).nenv ∧ kk < y.nlim ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (kk + 1) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.kx1) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r11 = sbrA t₀ + 0x5f6c0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r9 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r8 = sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .rdi = sbrA t₀ + 0x5f6c4#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ (u16 y.ftLim (kk) - y.kx1) ≤ mm ∧ mm < (u16 y.ftLim (kk + 1) - y.kx1) ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (48) ∧ s.regs.get64 .r12 = dA t₀ ch + 0x15030#64 + BitVec.ofNat 64 (0x30 * (ee + 1)) ∧ s.regs.get64 .r13 = BitVec.ofNat 64 ((u16 y.ftLim (kk) - y.kx1)) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (mm) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrGb x t₀ ch c0 y ee kk))
/-- ff_aac_sbr_apply.L9370 -/
abbrev L9370 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 ee kk mm, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ ee < (y.d ch).nenv ∧ kk < y.nlim ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (kk + 1) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.kx1) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r11 = sbrA t₀ + 0x5f6c0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r9 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r8 = sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .rdi = sbrA t₀ + 0x5f6c4#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ (u16 y.ftLim (kk) - y.kx1) ≤ mm ∧ mm < (u16 y.ftLim (kk + 1) - y.kx1) ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (48) ∧ s.regs.get64 .r12 = dA t₀ ch + 0x15030#64 + BitVec.ofNat 64 (0x30 * (ee + 1)) ∧ s.regs.get64 .r13 = BitVec.ofNat 64 ((u16 y.ftLim (kk) - y.kx1)) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (mm) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrGb x t₀ ch c0 y ee kk))
/-- ff_aac_sbr_apply.L9386 -/
abbrev L9386 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 ee kk mm, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ ee < (y.d ch).nenv ∧ kk < y.nlim ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (kk + 1) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.kx1) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r11 = sbrA t₀ + 0x5f6c0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r9 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r8 = sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .rdi = sbrA t₀ + 0x5f6c4#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ (u16 y.ftLim (kk) - y.kx1) ≤ mm ∧ mm < (u16 y.ftLim (kk + 1) - y.kx1) ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (48) ∧ s.regs.get64 .r12 = dA t₀ ch + 0x15030#64 + BitVec.ofNat 64 (0x30 * (ee + 1)) ∧ s.regs.get64 .r13 = BitVec.ofNat 64 ((u16 y.ftLim (kk) - y.kx1)) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (mm) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrGb x t₀ ch c0 y ee kk))
/-- ff_aac_sbr_apply.L9386_1 -/
abbrev L9386_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 ee kk mm, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ ee < (y.d ch).nenv ∧ kk < y.nlim ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (kk + 1) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.kx1) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r11 = sbrA t₀ + 0x5f6c0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r9 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r8 = sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .rdi = sbrA t₀ + 0x5f6c4#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ (u16 y.ftLim (kk) - y.kx1) ≤ mm ∧ mm < (u16 y.ftLim (kk + 1) - y.kx1) ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (48) ∧ s.regs.get64 .r12 = dA t₀ ch + 0x15030#64 + BitVec.ofNat 64 (0x30 * (ee + 1)) ∧ s.regs.get64 .r13 = BitVec.ofNat 64 ((u16 y.ftLim (kk) - y.kx1)) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (mm + 1) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrGb x t₀ ch c0 y ee kk))
/-- ff_aac_sbr_apply.L93d0 -/
abbrev L93d0 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 ee kk, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ ee < (y.d ch).nenv ∧ kk < y.nlim ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (kk + 1) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.kx1) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r11 = sbrA t₀ + 0x5f6c0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r9 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r8 = sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .rdi = sbrA t₀ + 0x5f6c4#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ (u16 y.ftLim (kk + 1) - y.kx1) ≤ (u16 y.ftLim (kk) - y.kx1) ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (ee) ∧ s.regs.get64 .r13 = BitVec.ofNat 64 ((u16 y.ftLim (kk) - y.kx1)) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (u16 y.ftLim (kk + 1)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrGb x t₀ ch c0 y ee kk))
/-- ff_aac_sbr_apply.L93f0 -/
abbrev L93f0 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 ee kk, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ ee < (y.d ch).nenv ∧ kk < y.nlim ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (kk + 1) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.kx1) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r11 = sbrA t₀ + 0x5f6c0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r9 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r8 = sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .rdi = sbrA t₀ + 0x5f6c4#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ (u16 y.ftLim (kk) - y.kx1) < (u16 y.ftLim (kk + 1) - y.kx1) ∧ s.regs.get64 .r14 = BitVec.ofNat 64 ((u16 y.ftLim (kk + 1) - y.kx1)) ∧ s.regs.get64 .r15 = BitVec.ofNat 64 (u16 y.ftLim (kk + 1)) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (u16 y.ftLim (kk + 1)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrGb x t₀ ch c0 y ee kk))
/-- ff_aac_sbr_apply.L93f0_1 -/
abbrev L93f0_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 ee kk, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ ee < (y.d ch).nenv ∧ kk < y.nlim ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (kk + 1) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.kx1) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r11 = sbrA t₀ + 0x5f6c0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r9 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r8 = sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .rdi = sbrA t₀ + 0x5f6c4#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ (u16 y.ftLim (kk) - y.kx1) < (u16 y.ftLim (kk + 1) - y.kx1) ∧ s.regs.get64 .rbx = BitVec.ofNat 64 ((u16 y.ftLim (kk) - y.kx1)) ∧ s.regs.get64 .r12 = BitVec.ofNat 64 ((u16 y.ftLim (kk + 1) - y.kx1) - (u16 y.ftLim (kk) - y.kx1)) ∧ s.regs.get64 .r14 = BitVec.ofNat 64 ((u16 y.ftLim (kk + 1) - y.kx1)) ∧ s.regs.get64 .r15 = BitVec.ofNat 64 (u16 y.ftLim (kk + 1)) ∧ s.regs.get64 .r13 = BitVec.ofNat 64 ((u16 y.ftLim (kk) - y.kx1)) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (u16 y.ftLim (kk + 1)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrGb x t₀ ch c0 y ee kk))
/-- ff_aac_sbr_apply.L9440 -/
abbrev L9440 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 ee kk jj cc, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ ee < (y.d ch).nenv ∧ kk < y.nlim ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (kk + 1) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.kx1) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r11 = sbrA t₀ + 0x5f6c0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r9 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r8 = sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .rdi = sbrA t₀ + 0x5f6c4#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ (u16 y.ftLim (kk) - y.kx1) < (u16 y.ftLim (kk + 1) - y.kx1) ∧ 1 ≤ cc ∧ jj + cc = (u16 y.ftLim (kk) - y.kx1) + ((u16 y.ftLim (kk + 1) - y.kx1) - (u16 y.ftLim (kk) - y.kx1)) % 8 ∧ (u16 y.ftLim (kk) - y.kx1) ≤ jj ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (jj) ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (cc) ∧ s.regs.get64 .r14 = BitVec.ofNat 64 ((u16 y.ftLim (kk + 1) - y.kx1)) ∧ s.regs.get64 .r15 = BitVec.ofNat 64 (u16 y.ftLim (kk + 1)) ∧ s.regs.get64 .r13 = BitVec.ofNat 64 ((u16 y.ftLim (kk) - y.kx1)) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (u16 y.ftLim (kk + 1)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrGb68 x t₀ ch c0 y ee kk))
/-- ff_aac_sbr_apply.L9458 -/
abbrev L9458 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 ee kk, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ ee < (y.d ch).nenv ∧ kk < y.nlim ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (kk + 1) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.kx1) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r11 = sbrA t₀ + 0x5f6c0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r9 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r8 = sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .rdi = sbrA t₀ + 0x5f6c4#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ (u16 y.ftLim (kk) - y.kx1) < (u16 y.ftLim (kk + 1) - y.kx1) ∧ s.regs.get64 .rbx = BitVec.ofNat 64 ((u16 y.ftLim (kk) - y.kx1) + ((u16 y.ftLim (kk + 1) - y.kx1) - (u16 y.ftLim (kk) - y.kx1)) % 8) ∧ s.regs.get64 .r14 = BitVec.ofNat 64 ((u16 y.ftLim (kk + 1) - y.kx1)) ∧ s.regs.get64 .r15 = BitVec.ofNat 64 (u16 y.ftLim (kk + 1)) ∧ s.regs.get64 .r13 = BitVec.ofNat 64 ((u16 y.ftLim (kk) - y.kx1)) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (u16 y.ftLim (kk + 1)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrGb68 x t₀ ch c0 y ee kk))
/-- ff_aac_sbr_apply.L9470 -/
abbrev L9470 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 ee kk jj, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ ee < (y.d ch).nenv ∧ kk < y.nlim ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (kk + 1) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.kx1) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r11 = sbrA t₀ + 0x5f6c0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r9 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r8 = sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .rdi = sbrA t₀ + 0x5f6c4#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ (u16 y.ftLim (kk) - y.kx1) < (u16 y.ftLim (kk + 1) - y.kx1) ∧ (u16 y.ftLim (kk) - y.kx1) ≤ jj ∧ jj < (u16 y.ftLim (kk + 1) - y.kx1) ∧ ((u16 y.ftLim (kk + 1) - y.kx1) - jj) % 8 = 0 ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (jj) ∧ s.regs.get64 .r15 = BitVec.ofNat 64 ((u16 y.ftLim (kk + 1) - y.kx1)) ∧ s.regs.get64 .r13 = BitVec.ofNat 64 ((u16 y.ftLim (kk) - y.kx1)) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (u16 y.ftLim (kk + 1)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrGb68 x t₀ ch c0 y ee kk))
/-- ff_aac_sbr_apply.L9470_1 -/
abbrev L9470_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 ee kk jj, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ ee < (y.d ch).nenv ∧ kk < y.nlim ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (kk + 1) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.kx1) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r11 = sbrA t₀ + 0x5f6c0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r9 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r8 = sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .rdi = sbrA t₀ + 0x5f6c4#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ (u16 y.ftLim (kk) - y.kx1) < (u16 y.ftLim (kk + 1) - y.kx1) ∧ (u16 y.ftLim (kk) - y.kx1) ≤ jj ∧ jj < (u16 y.ftLim (kk + 1) - y.kx1) ∧ ((u16 y.ftLim (kk + 1) - y.kx1) - jj) % 8 = 0 ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (jj) ∧ s.regs.get64 .r15 = BitVec.ofNat 64 ((u16 y.ftLim (kk + 1) - y.kx1)) ∧ s.regs.get64 .r13 = BitVec.ofNat 64 ((u16 y.ftLim (kk) - y.kx1)) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (u16 y.ftLim (kk + 1)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrGb68 x t₀ ch c0 y ee kk))
/-- ff_aac_sbr_apply.L9504 -/
abbrev L9504 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 ee kk, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ ee < (y.d ch).nenv ∧ kk < y.nlim ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (kk + 1) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.kx1) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r11 = sbrA t₀ + 0x5f6c0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r9 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r8 = sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .rdi = sbrA t₀ + 0x5f6c4#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ (u16 y.ftLim (kk) - y.kx1) < (u16 y.ftLim (kk + 1) - y.kx1) ∧ s.regs.get64 .r13 = BitVec.ofNat 64 ((u16 y.ftLim (kk) - y.kx1)) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (u16 y.ftLim (kk + 1)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrGb68 x t₀ ch c0 y ee kk))
/-- ff_aac_sbr_apply.L9520 -/
abbrev L9520 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 ee kk, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ ee < (y.d ch).nenv ∧ kk < y.nlim ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (kk + 1) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.kx1) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r11 = sbrA t₀ + 0x5f6c0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r9 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r8 = sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .rdi = sbrA t₀ + 0x5f6c4#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r13 = BitVec.ofNat 64 ((u16 y.ftLim (kk) - y.kx1)) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (u16 y.ftLim (kk + 1)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrGb x t₀ ch c0 y ee kk))
/-- ff_aac_sbr_apply.L952c -/
abbrev L952c (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 ee kk, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ ee < (y.d ch).nenv ∧ kk < y.nlim ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (kk + 1) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.kx1) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r11 = sbrA t₀ + 0x5f6c0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r9 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r8 = sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .rdi = sbrA t₀ + 0x5f6c4#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r13 = BitVec.ofNat 64 ((u16 y.ftLim (kk) - y.kx1)) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (u16 y.ftLim (kk + 1)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrGb x t₀ ch c0 y ee kk))
/-- ff_aac_sbr_apply.L9530 -/
abbrev L9530 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 ee kk, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ ee < (y.d ch).nenv ∧ kk < y.nlim ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (kk + 1) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.kx1) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r11 = sbrA t₀ + 0x5f6c0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r9 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r8 = sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .rdi = sbrA t₀ + 0x5f6c4#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (ee) ∧ s.regs.get64 .r13 = BitVec.ofNat 64 ((u16 y.ftLim (kk) - y.kx1)) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (u16 y.ftLim (kk + 1)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrGb x t₀ ch c0 y ee kk))
/-- ff_aac_sbr_apply.L9530_1 -/
abbrev L9530_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 ee kk, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ ee < (y.d ch).nenv ∧ kk < y.nlim ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (kk + 1) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.kx1) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r11 = sbrA t₀ + 0x5f6c0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r9 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r8 = sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .rdi = sbrA t₀ + 0x5f6c4#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (ee) ∧ s.regs.get64 .r13 = BitVec.ofNat 64 ((u16 y.ftLim (kk) - y.kx1)) ∧ (u16 y.ftLim (kk) - y.kx1) < (u16 y.ftLim (kk + 1) - y.kx1) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (u16 y.ftLim (kk + 1)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrGb x t₀ ch c0 y ee kk))
/-- ff_aac_sbr_apply.L95a0 -/
abbrev L95a0 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 ee kk mm, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ ee < (y.d ch).nenv ∧ kk < y.nlim ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (kk + 1) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.kx1) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r11 = sbrA t₀ + 0x5f6c0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r9 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r8 = sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .rdi = sbrA t₀ + 0x5f6c4#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (ee) ∧ s.regs.get64 .r13 = BitVec.ofNat 64 ((u16 y.ftLim (kk) - y.kx1)) ∧ (u16 y.ftLim (kk) - y.kx1) < (u16 y.ftLim (kk + 1) - y.kx1) ∧ (u16 y.ftLim (kk) - y.kx1) ≤ mm ∧ mm < (u16 y.ftLim (kk + 1) - y.kx1) ∧ s.regs.get64 .r14 = BitVec.ofNat 64 (48) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (mm) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (u16 y.ftLim (kk + 1)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrGb x t₀ ch c0 y ee kk))
/-- ff_aac_sbr_apply.L95a0_1 -/
abbrev L95a0_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 ee kk mm, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ ee < (y.d ch).nenv ∧ kk < y.nlim ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (kk + 1) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.kx1) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r11 = sbrA t₀ + 0x5f6c0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r9 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r8 = sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .rdi = sbrA t₀ + 0x5f6c4#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (ee) ∧ s.regs.get64 .r13 = BitVec.ofNat 64 ((u16 y.ftLim (kk) - y.kx1)) ∧ (u16 y.ftLim (kk) - y.kx1) < (u16 y.ftLim (kk + 1) - y.kx1) ∧ (u16 y.ftLim (kk) - y.kx1) ≤ mm ∧ mm < (u16 y.ftLim (kk + 1) - y.kx1) ∧ s.regs.get64 .r14 = BitVec.ofNat 64 (48) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (mm) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (u16 y.ftLim (kk + 1)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrGb x t₀ ch c0 y ee kk))
/-- ff_aac_sbr_apply.L95a0_2 -/
abbrev L95a0_2 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 ee kk mm, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ ee < (y.d ch).nenv ∧ kk < y.nlim ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (kk + 1) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.kx1) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r11 = sbrA t₀ + 0x5f6c0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r9 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r8 = sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .rdi = sbrA t₀ + 0x5f6c4#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (ee) ∧ s.regs.get64 .r13 = BitVec.ofNat 64 ((u16 y.ftLim (kk) - y.kx1)) ∧ (u16 y.ftLim (kk) - y.kx1) < (u16 y.ftLim (kk + 1) - y.kx1) ∧ (u16 y.ftLim (kk) - y.kx1) ≤ mm ∧ mm < (u16 y.ftLim (kk + 1) - y.kx1) ∧ s.regs.get64 .r14 = BitVec.ofNat 64 (48) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (mm + 1) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrGb x t₀ ch c0 y ee kk))
/-- ff_aac_sbr_apply.L9600 -/
abbrev L9600 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 ee kk, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ ee < (y.d ch).nenv ∧ kk < y.nlim ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (kk + 1) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.kx1) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r11 = sbrA t₀ + 0x5f6c0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r9 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r8 = sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .rdi = sbrA t₀ + 0x5f6c4#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (ee) ∧ (u16 y.ftLim (kk) - y.kx1) < (u16 y.ftLim (kk + 1) - y.kx1) ∧ s.regs.get64 .rbx = BitVec.ofNat 64 ((u16 y.ftLim (kk + 1) - y.kx1)) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (u16 y.ftLim (kk + 1)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrGb x t₀ ch c0 y ee kk))
/-- ff_aac_sbr_apply.L9617 -/
abbrev L9617 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 ee kk, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ ee < (y.d ch).nenv ∧ kk < y.nlim ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (kk + 1) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.kx1) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r11 = sbrA t₀ + 0x5f6c0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r9 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r8 = sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .rdi = sbrA t₀ + 0x5f6c4#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (ee) ∧ s.regs.get64 .r13 = BitVec.ofNat 64 ((u16 y.ftLim (kk) - y.kx1)) ∧ s.regs.get64 .rbx = BitVec.ofNat 64 ((u16 y.ftLim (kk + 1) - y.kx1)) ∧ ((u16 y.ftLim (kk) - y.kx1) < (u16 y.ftLim (kk + 1) - y.kx1) → s.regs.get64 .rax = BitVec.ofNat 64 (u16 y.ftLim (kk))) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (u16 y.ftLim (kk + 1)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrGb x t₀ ch c0 y ee kk))
/-- ff_aac_sbr_apply.L9617_1 -/
abbrev L9617_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 ee kk, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ ee < (y.d ch).nenv ∧ kk < y.nlim ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (kk + 1) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.kx1) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r11 = sbrA t₀ + 0x5f6c0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r9 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r8 = sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .rdi = sbrA t₀ + 0x5f6c4#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ (u16 y.ftLim (kk) - y.kx1) < (u16 y.ftLim (kk + 1) - y.kx1) ∧ s.regs.get64 .r13 = BitVec.ofNat 64 ((u16 y.ftLim (kk) - y.kx1)) ∧ s.regs.get64 .r12 = BitVec.ofNat 64 ((u16 y.ftLim (kk + 1) - y.kx1)) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (u16 y.ftLim (kk + 1)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrGb x t₀ ch c0 y ee kk))
/-- ff_aac_sbr_apply.L968d -/
abbrev L968d (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 ee kk, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ ee < (y.d ch).nenv ∧ kk < y.nlim ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (kk + 1) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.kx1) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r11 = sbrA t₀ + 0x5f6c0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r9 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r8 = sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .rdi = sbrA t₀ + 0x5f6c4#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ (u16 y.ftLim (kk) - y.kx1) < (u16 y.ftLim (kk + 1) - y.kx1) ∧ ((u16 y.ftLim (kk + 1) - y.kx1) - (u16 y.ftLim (kk) - y.kx1)) % 2 = 1 ∧ s.regs.get64 .rax = BitVec.ofNat 64 ((u16 y.ftLim (kk) - y.kx1)) ∧ s.regs.get64 .r12 = BitVec.ofNat 64 ((u16 y.ftLim (kk + 1) - y.kx1)) ∧ s.regs.get64 .r13 = BitVec.ofNat 64 ((u16 y.ftLim (kk) - y.kx1)) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (u16 y.ftLim (kk + 1)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrGb x t₀ ch c0 y ee kk))
/-- ff_aac_sbr_apply.L96d3 -/
abbrev L96d3 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 ee kk, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ ee < (y.d ch).nenv ∧ kk < y.nlim ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (kk + 1) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.kx1) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r11 = sbrA t₀ + 0x5f6c0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r9 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r8 = sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .rdi = sbrA t₀ + 0x5f6c4#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ (u16 y.ftLim (kk) - y.kx1) < (u16 y.ftLim (kk + 1) - y.kx1) ∧ s.regs.get64 .rax = BitVec.ofNat 64 ((u16 y.ftLim (kk) - y.kx1)) ∧ s.regs.get64 .rbx = BitVec.ofNat 64 ((u16 y.ftLim (kk) - y.kx1) + ((u16 y.ftLim (kk + 1) - y.kx1) - (u16 y.ftLim (kk) - y.kx1)) % 2) ∧ s.regs.get64 .r12 = BitVec.ofNat 64 ((u16 y.ftLim (kk + 1) - y.kx1)) ∧ s.regs.get64 .r13 = BitVec.ofNat 64 ((u16 y.ftLim (kk) - y.kx1)) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (u16 y.ftLim (kk + 1)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrGb x t₀ ch c0 y ee kk))
/-- ff_aac_sbr_apply.L96e1 -/
abbrev L96e1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 ee kk, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ ee < (y.d ch).nenv ∧ kk < y.nlim ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (kk + 1) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.kx1) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r11 = sbrA t₀ + 0x5f6c0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r9 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r8 = sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .rdi = sbrA t₀ + 0x5f6c4#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ (u16 y.ftLim (kk) - y.kx1) < (u16 y.ftLim (kk + 1) - y.kx1) ∧ s.regs.get64 .rax = BitVec.ofNat 64 ((u16 y.ftLim (kk) - y.kx1)) ∧ s.regs.get64 .r13 = BitVec.ofNat 64 ((u16 y.ftLim (kk) - y.kx1)) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (u16 y.ftLim (kk + 1)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrGb x t₀ ch c0 y ee kk))
/-- ff_aac_sbr_apply.L9720 -/
abbrev L9720 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 ee kk jj, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ ee < (y.d ch).nenv ∧ kk < y.nlim ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (kk + 1) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.kx1) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r11 = sbrA t₀ + 0x5f6c0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r9 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r8 = sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .rdi = sbrA t₀ + 0x5f6c4#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ (u16 y.ftLim (kk) - y.kx1) < (u16 y.ftLim (kk + 1) - y.kx1) ∧ (u16 y.ftLim (kk) - y.kx1) ≤ jj ∧ jj + 2 ≤ (u16 y.ftLim (kk + 1) - y.kx1) ∧ ((u16 y.ftLim (kk + 1) - y.kx1) - jj) % 2 = 0 ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (jj) ∧ s.regs.get64 .r12 = BitVec.ofNat 64 ((u16 y.ftLim (kk + 1) - y.kx1)) ∧ s.regs.get64 .rax = BitVec.ofNat 64 ((u16 y.ftLim (kk) - y.kx1)) ∧ s.regs.get64 .r13 = BitVec.ofNat 64 ((u16 y.ftLim (kk) - y.kx1)) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (u16 y.ftLim (kk + 1)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrGb x t₀ ch c0 y ee kk))
/-- ff_aac_sbr_apply.L9731 -/
abbrev L9731 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 ee kk jj, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ ee < (y.d ch).nenv ∧ kk < y.nlim ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (kk + 1) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.kx1) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r11 = sbrA t₀ + 0x5f6c0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r9 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r8 = sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .rdi = sbrA t₀ + 0x5f6c4#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ (u16 y.ftLim (kk) - y.kx1) < (u16 y.ftLim (kk + 1) - y.kx1) ∧ (u16 y.ftLim (kk) - y.kx1) ≤ jj ∧ jj + 2 ≤ (u16 y.ftLim (kk + 1) - y.kx1) ∧ ((u16 y.ftLim (kk + 1) - y.kx1) - jj) % 2 = 0 ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (jj) ∧ s.regs.get64 .r12 = BitVec.ofNat 64 ((u16 y.ftLim (kk + 1) - y.kx1)) ∧ s.regs.get64 .rax = BitVec.ofNat 64 ((u16 y.ftLim (kk) - y.kx1)) ∧ s.regs.get64 .r13 = BitVec.ofNat 64 ((u16 y.ftLim (kk) - y.kx1)) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (u16 y.ftLim (kk + 1)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrGb x t₀ ch c0 y ee kk))
/-- ff_aac_sbr_apply.L9731_1 -/
abbrev L9731_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 ee kk jj, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ ee < (y.d ch).nenv ∧ kk < y.nlim ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (kk + 1) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.kx1) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r11 = sbrA t₀ + 0x5f6c0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r9 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r8 = sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .rdi = sbrA t₀ + 0x5f6c4#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ (u16 y.ftLim (kk) - y.kx1) < (u16 y.ftLim (kk + 1) - y.kx1) ∧ (u16 y.ftLim (kk) - y.kx1) ≤ jj ∧ jj + 2 ≤ (u16 y.ftLim (kk + 1) - y.kx1) ∧ ((u16 y.ftLim (kk + 1) - y.kx1) - jj) % 2 = 0 ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (jj) ∧ s.regs.get64 .r12 = BitVec.ofNat 64 ((u16 y.ftLim (kk + 1) - y.kx1)) ∧ s.regs.get64 .rax = BitVec.ofNat 64 ((u16 y.ftLim (kk) - y.kx1)) ∧ s.regs.get64 .r13 = BitVec.ofNat 64 ((u16 y.ftLim (kk) - y.kx1)) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (u16 y.ftLim (kk + 1)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrGb x t₀ ch c0 y ee kk))
/-- ff_aac_sbr_apply.L97b7 -/
abbrev L97b7 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 ee kk jj, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ ee < (y.d ch).nenv ∧ kk < y.nlim ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (kk + 1) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.kx1) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r11 = sbrA t₀ + 0x5f6c0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r9 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r8 = sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .rdi = sbrA t₀ + 0x5f6c4#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ (u16 y.ftLim (kk) - y.kx1) < (u16 y.ftLim (kk + 1) - y.kx1) ∧ (u16 y.ftLim (kk) - y.kx1) ≤ jj ∧ jj + 2 ≤ (u16 y.ftLim (kk + 1) - y.kx1) ∧ ((u16 y.ftLim (kk + 1) - y.kx1) - jj) % 2 = 0 ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (jj) ∧ s.regs.get64 .r12 = BitVec.ofNat 64 ((u16 y.ftLim (kk + 1) - y.kx1)) ∧ s.regs.get64 .rax = BitVec.ofNat 64 ((u16 y.ftLim (kk) - y.kx1)) ∧ s.regs.get64 .r13 = BitVec.ofNat 64 ((u16 y.ftLim (kk) - y.kx1)) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (u16 y.ftLim (kk + 1)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrGb x t₀ ch c0 y ee kk))
/-- ff_aac_sbr_apply.L97f0 -/
abbrev L97f0 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 ee kk jj, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ ee < (y.d ch).nenv ∧ kk < y.nlim ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (kk + 1) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.kx1) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r11 = sbrA t₀ + 0x5f6c0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r9 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r8 = sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .rdi = sbrA t₀ + 0x5f6c4#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ (u16 y.ftLim (kk) - y.kx1) < (u16 y.ftLim (kk + 1) - y.kx1) ∧ (u16 y.ftLim (kk) - y.kx1) ≤ jj ∧ jj + 2 ≤ (u16 y.ftLim (kk + 1) - y.kx1) ∧ ((u16 y.ftLim (kk + 1) - y.kx1) - jj) % 2 = 0 ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (jj) ∧ s.regs.get64 .r12 = BitVec.ofNat 64 ((u16 y.ftLim (kk + 1) - y.kx1)) ∧ s.regs.get64 .rax = BitVec.ofNat 64 ((u16 y.ftLim (kk) - y.kx1)) ∧ s.regs.get64 .r13 = BitVec.ofNat 64 ((u16 y.ftLim (kk) - y.kx1)) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (u16 y.ftLim (kk + 1)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrGb x t₀ ch c0 y ee kk))
/-- ff_aac_sbr_apply.L9820 -/
abbrev L9820 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 ee kk, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ ee < (y.d ch).nenv ∧ kk < y.nlim ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (kk + 1) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.kx1) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r11 = sbrA t₀ + 0x5f6c0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r9 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r8 = sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .rdi = sbrA t₀ + 0x5f6c4#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (ee) ∧ s.regs.get64 .r13 = BitVec.ofNat 64 ((u16 y.ftLim (kk) - y.kx1)) ∧ (u16 y.ftLim (kk + 1) - y.kx1) ≤ (u16 y.ftLim (kk) - y.kx1) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (u16 y.ftLim (kk + 1)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrGb x t₀ ch c0 y ee kk))
/-- ff_aac_sbr_apply.L983f -/
abbrev L983f (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 ee kk, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ ee < (y.d ch).nenv ∧ kk < y.nlim ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (kk + 1) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.kx1) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r11 = sbrA t₀ + 0x5f6c0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r9 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r8 = sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .rdi = sbrA t₀ + 0x5f6c4#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ (u16 y.ftLim (kk) - y.kx1) < (u16 y.ftLim (kk + 1) - y.kx1) ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (ee) ∧ s.regs.get64 .rax = BitVec.ofNat 64 ((u16 y.ftLim (kk) - y.kx1)) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (u16 y.ftLim (kk + 1)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrGb x t₀ ch c0 y ee kk))
/-- ff_aac_sbr_apply.L9860 -/
abbrev L9860 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 ee kk mm, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ ee < (y.d ch).nenv ∧ kk < y.nlim ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (kk + 1) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.kx1) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r11 = sbrA t₀ + 0x5f6c0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r9 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r8 = sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .rdi = sbrA t₀ + 0x5f6c4#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ (u16 y.ftLim (kk) - y.kx1) < (u16 y.ftLim (kk + 1) - y.kx1) ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (ee) ∧ (u16 y.ftLim (kk) - y.kx1) ≤ mm ∧ mm < (u16 y.ftLim (kk + 1) - y.kx1) ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (48) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (mm) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (u16 y.ftLim (kk + 1)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrGb x t₀ ch c0 y ee kk))
/-- ff_aac_sbr_apply.L9860_1 -/
abbrev L9860_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 ee kk mm, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ ee < (y.d ch).nenv ∧ kk < y.nlim ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (kk + 1) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.kx1) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r11 = sbrA t₀ + 0x5f6c0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r9 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r8 = sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .rdi = sbrA t₀ + 0x5f6c4#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ (u16 y.ftLim (kk) - y.kx1) < (u16 y.ftLim (kk + 1) - y.kx1) ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (ee) ∧ (u16 y.ftLim (kk) - y.kx1) ≤ mm ∧ mm < (u16 y.ftLim (kk + 1) - y.kx1) ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (48) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (mm) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (u16 y.ftLim (kk + 1)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrGb x t₀ ch c0 y ee kk))
/-- ff_aac_sbr_apply.L9860_2 -/
abbrev L9860_2 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 ee kk mm, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ ee < (y.d ch).nenv ∧ kk < y.nlim ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (kk + 1) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.kx1) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r11 = sbrA t₀ + 0x5f6c0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r9 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r8 = sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .rdi = sbrA t₀ + 0x5f6c4#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ (u16 y.ftLim (kk) - y.kx1) < (u16 y.ftLim (kk + 1) - y.kx1) ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (ee) ∧ (u16 y.ftLim (kk) - y.kx1) ≤ mm ∧ mm < (u16 y.ftLim (kk + 1) - y.kx1) ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (48) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (mm) ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (u16 y.ftLim (kk + 1)) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrGb x t₀ ch c0 y ee kk))
/-- ff_aac_sbr_apply.L9860_3 -/
abbrev L9860_3 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 ee kk mm, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ ee < (y.d ch).nenv ∧ kk < y.nlim ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (kk + 1) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (y.kx1) ∧ s.regs.get64 .r10 = arg1 t₀ + BitVec.ofNat 64 (0x30 * ee) ∧ s.regs.get64 .r11 = sbrA t₀ + 0x5f6c0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r9 = sbrA t₀ + 0x5d740#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .r8 = sbrA t₀ + 0x5eac0#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ s.regs.get64 .rdi = sbrA t₀ + 0x5f6c4#64 + BitVec.ofNat 64 (0xc0 * ee) ∧ (u16 y.ftLim (kk) - y.kx1) < (u16 y.ftLim (kk + 1) - y.kx1) ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (ee) ∧ (u16 y.ftLim (kk) - y.kx1) ≤ mm ∧ mm < (u16 y.ftLim (kk + 1) - y.kx1) ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (48) ∧ s.regs.get64 .rax = BitVec.ofNat 64 (mm + 1) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrGb x t₀ ch c0 y ee kk))
/-- ff_aac_sbr_apply.L98bc -/
abbrev L98bc (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => False
/-- ff_aac_sbr_apply.L98e0 -/
abbrev L98e0 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ s.regs.get64 .rbx = dA t₀ ch ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrGA x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L9927 -/
abbrev L9927 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ ch c0, ch < 2 ∧ c0.getLsbD 0 = decide (ch = 0) ∧ s.regs.get64 .rbx = dA t₀ ch ∧ ∃ y, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrCs x t₀ ch c0))
/-- ff_aac_sbr_apply.L9934 -/
abbrev L9934 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0, ApplyC x t₀ ∧ Base t₀ s ∧ ch < 2 ∧ c0.getLsbD 0 = decide (ch = 0) ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5fcc0#64 ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ (s.regs.get64 .rax).toNat % 2^32 = (y.d ch).ypos ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrCs x t₀ ch c0))
/-- ff_aac_sbr_apply.L9934_1 -/
abbrev L9934_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0, ApplyC x t₀ ∧ Base t₀ s ∧ ch < 2 ∧ c0.getLsbD 0 = decide (ch = 0) ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5fcc0#64 ∧ s.regs.get64 .r9 = BitVec.ofNat 64 (ch) ∧ s.regs.get64 .rsi = sbrA t₀ + 0x53b40#64 + BitVec.ofNat 64 (0x4c00 * ch) ∧ s.regs.get64 .rdi = dA t₀ ch + 0x7930#64 ∧ (s.regs.get64 .rbx).toNat % 256 = (if BitVec.setWidth 32 (arg2 t₀) = 1#32 then 1 else 0) ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ (s.regs.get64 .rax).toNat % 2^32 = (y.d ch).ypos ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (1 - (y.d ch).ypos) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrCs x t₀ ch c0))
/-- ff_aac_sbr_apply.L9934_2 -/
abbrev L9934_2 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0, ApplyC x t₀ ∧ Base t₀ s ∧ ch < 2 ∧ c0.getLsbD 0 = decide (ch = 0) ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5fcc0#64 ∧ s.regs.get64 .r14 = arg1 t₀ ∧ (s.regs.get64 .rbx).toNat % 256 = (if BitVec.setWidth 32 (arg2 t₀) = 1#32 then 1 else 0) ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrCs x t₀ ch c0))
/-- ff_aac_sbr_apply.L99c6 -/
abbrev L99c6 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 8 ≤ (y.d ch).nenv ∧ s.regs.get64 .rax = BitVec.ofNat 64 (y.m1) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L99cf -/
abbrev L99cf (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0) ∧ y.start ≠ 0 ∧ ch < 2 ∧ 8 ≤ (y.d ch).nenv ∧ s.regs.get64 .rcx = BitVec.ofNat 64 ((y.d ch).nenv) ∧ s.regs.get64 .rax = BitVec.ofNat 64 ((y.d ch).nenv) ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrI1 x t₀ ch c0 y))
/-- ff_aac_sbr_apply.L99e9 -/
abbrev L99e9 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => False
/-- ff_aac_sbr_apply.L99ee -/
abbrev L99ee (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => False
/-- ff_aac_sbr_apply.L99f3 -/
abbrev L99f3 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => False
/-- ff_aac_sbr_apply.L99f8 -/
abbrev L99f8 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => False
/-- ff_aac_sbr_apply.L99fd -/
abbrev L99fd (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => False
/-- ff_aac_sbr_apply.L9a02 -/
abbrev L9a02 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0, ApplyC x t₀ ∧ Base t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5fcc0#64 ∧ ∃ y : Args, x.Keep y ∧ ApplyC y t₀ ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrCs x t₀ ch c0))
/-- ff_aac_sbr_apply.L9a02_1 -/
abbrev L9a02_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0, ApplyC x t₀ ∧ Base t₀ s ∧ s.regs.get64 .rbx = arg0 t₀ ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5fcc0#64 ∧ s.regs.get64 .r14 = BitVec.ofNat 64 (dsN x) ∧ ∃ y : Args, x.Keep y ∧ ApplyC y t₀ ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrCs x t₀ ch c0))
/-- ff_aac_sbr_apply.L9a50 -/
abbrev L9a50 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => False
/-- ff_aac_sbr_apply.L9a55 -/
abbrev L9a55 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => False
/-- ff_aac_sbr_apply.L9a5a -/
abbrev L9a5a (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => False
/-- ff_aac_sbr_apply.L9a5f -/
abbrev L9a5f (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => False
/-- ff_aac_sbr_apply.L9a64 -/
abbrev L9a64 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => False
/-- ff_aac_sbr_apply.L9a69 -/
abbrev L9a69 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0, ApplyC x t₀ ∧ Base t₀ s ∧ s.regs.get64 .rbx = arg0 t₀ ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5fcc0#64 ∧ s.regs.get64 .r14 = BitVec.ofNat 64 (dsN x) ∧ s.regs.get64 .rax = arg1 t₀ + 0x81060#64 ∧ ∃ y : Args, x.Keep y ∧ ApplyC y t₀ ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrCs x t₀ ch c0))
/-- ff_aac_sbr_apply.L9a7d -/
abbrev L9a7d (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0, ApplyC x t₀ ∧ Base t₀ s ∧ s.regs.get64 .rbx = arg0 t₀ ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5fcc0#64 ∧ s.regs.get64 .r14 = BitVec.ofNat 64 (dsN x) ∧ ∃ y : Args, x.Keep y ∧ ApplyC y t₀ ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrCs x t₀ ch c0))
/-- ff_aac_sbr_apply.L9a85 -/
abbrev L9a85 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0, ApplyC x t₀ ∧ Base t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ s.regs.get64 .rbx = arg0 t₀ ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5fcc0#64 ∧ s.regs.get64 .r14 = BitVec.ofNat 64 (dsN x) ∧ ∃ y : Args, x.Keep y ∧ ApplyC y t₀ ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrCs x t₀ ch c0))
/-- ff_aac_sbr_apply.L9a85_1 -/
abbrev L9a85_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0, ApplyC x t₀ ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x1e8#64 ∧ s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64 ∧ s.regs.get64 .rbx = arg1 t₀ ∧ s.regs.get64 .r15 = arg0 t₀ ∧ s.regs.get64 .r13 = sbrA t₀ + 0x601e0#64 ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5fcc0#64 ∧ s.regs.get64 .r14 = BitVec.ofNat 64 (dsN x) ∧ ∃ y : Args, x.Keep y ∧ ApplyC y t₀ ∧ s.regs.get64 .rdi = y.synCtx ∧ s.regs.get64 .rsi = e.fs.qfs.tx.toBitVec ∧ s.regs.get64 .rcx = y.fdsp ∧ s.regs.get64 .rdx = sbrA t₀ + 0x601e0#64 ∧ s.regs.get64 .r8 = arg3 t₀ ∧ s.regs.get64 .r9 = sbrA t₀ + 0x53b40#64 ∧ (s.dmem =⋆ MmS k e y ra t₀ (SynArgs x t₀ 0) (FrCs x t₀ ch c0))
/-- ff_aac_sbr_apply.L9a85_2 -/
abbrev L9a85_2 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0, ApplyC x t₀ ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x1e8#64 ∧ s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64 ∧ s.regs.get64 .rbx = arg1 t₀ ∧ s.regs.get64 .r15 = arg0 t₀ ∧ s.regs.get64 .r13 = sbrA t₀ + 0x601e0#64 ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5fcc0#64 ∧ s.regs.get64 .r14 = BitVec.ofNat 64 (dsN x) ∧ ∃ y : Args, x.Keep y ∧ ApplyC y t₀ ∧ ∃ v : BitVec 32, v.toInt ≤ 1664 ∧ v.toNat % 8 = 0 ∧ (s.dmem =⋆ Mm k e (y.setV0 v) ra t₀ (FrCs x t₀ ch c0))
/-- ff_aac_sbr_apply.L9a85_3 -/
abbrev L9a85_3 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0, ApplyC x t₀ ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x1e8#64 ∧ s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64 ∧ s.regs.get64 .rbx = arg1 t₀ + 0x41d60#64 ∧ s.regs.get64 .r15 = arg0 t₀ ∧ s.regs.get64 .r13 = sbrA t₀ + 0x601e0#64 ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5fcc0#64 ∧ s.regs.get64 .r14 = BitVec.ofNat 64 (dsN x) ∧ ∃ y : Args, x.Keep y ∧ ApplyC y t₀ ∧ s.regs.get64 .rdi = y.synCtx ∧ s.regs.get64 .rsi = e.fs.qfs.tx.toBitVec ∧ s.regs.get64 .rcx = y.fdsp ∧ s.regs.get64 .rdx = sbrA t₀ + 0x601e0#64 ∧ s.regs.get64 .r8 = arg4 t₀ ∧ s.regs.get64 .r9 = sbrA t₀ + 0x58740#64 ∧ ∃ v : BitVec 32, v.toInt ≤ 1664 ∧ v.toNat % 8 = 0 ∧ (s.dmem =⋆ MmS k e (y.setV0 v) ra t₀ (SynArgs x t₀ 1) (FrCs x t₀ ch c0))
/-- ff_aac_sbr_apply.L9a85_4 -/
abbrev L9a85_4 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0, ApplyC x t₀ ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x1e8#64 ∧ s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64 ∧ ∃ y : Args, x.Keep y ∧ ApplyC y t₀ ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrCs x t₀ ch c0))
/-- ff_aac_sbr_apply.L9b24 -/
abbrev L9b24 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ∃ ch c0, ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y : Args, x.Keep y ∧ ApplyC y t₀ ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrCs x t₀ ch c0))
/-- ff_aac_sbr_apply.L9b2b -/
abbrev L9b2b (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => ApplyC x t₀ ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x30#64 ∧ s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64 ∧ (s.dmem =⋆ Reserve (0x298 + k) (t₀.regs.get64 .rsp - 0x1c8#64) ⋆ (ApplyFPost e x t₀ ⋆ FrRaw t₀ (RetCell ra (t₀.regs.get64 .rsp) ⋆ x.R)))
/-- ff_aac_sbr_apply.done -/
abbrev done (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp ∧ SavedRegs t₀ s ∧ (s.dmem =⋆ RetCell ra (t₀.regs.get64 .rsp) ⋆ (Reserve (applyNeed k) (t₀.regs.get64 .rsp) ⋆ (ApplyFPost e x t₀ ⋆ x.R)))
/-- ff_aac_sbr_apply.L9b36 -/
abbrev L9b36 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => False
/-- ff_aac_sbr_apply.L9b3b -/
abbrev L9b3b (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => False
/-- ff_aac_sbr_apply.L9b40 -/
abbrev L9b40 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => False
/-- ff_aac_sbr_apply.L9b45 -/
abbrev L9b45 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => False
/-- ff_aac_sbr_apply.L9b4a -/
abbrev L9b4a (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => False
/-- ff_aac_sbr_apply.L9b4f -/
abbrev L9b4f (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => False
/-- ff_aac_sbr_apply.L9b54 -/
abbrev L9b54 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => False
/-- ff_aac_sbr_apply.L9b59 -/
abbrev L9b59 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => False
/-- ff_aac_sbr_apply.L9b5e -/
abbrev L9b5e (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => False
/-- ff_aac_sbr_apply.L9b63 -/
abbrev L9b63 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => False
/-- ff_aac_sbr_apply.L9b68 -/
abbrev L9b68 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => False
/-- ff_aac_sbr_apply.L9b6d -/
abbrev L9b6d (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => False
/-- ff_aac_sbr_apply.L9b72 -/
abbrev L9b72 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => False
/-- ff_aac_sbr_apply.L9b77 -/
abbrev L9b77 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => False
/-- ff_aac_sbr_apply.L9b7c -/
abbrev L9b7c (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => False
/-- ff_aac_sbr_apply.L9b81 -/
abbrev L9b81 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => False
/-- ff_aac_sbr_apply.L9b86 -/
abbrev L9b86 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => False
/-- ff_aac_sbr_apply.L9b8b -/
abbrev L9b8b (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => False
/-- ff_aac_sbr_apply.L9b90 -/
abbrev L9b90 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => False
/-- ff_aac_sbr_apply.L9b95 -/
abbrev L9b95 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => False
/-- ff_aac_sbr_apply.L9b9a -/
abbrev L9b9a (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => False
/-- ff_aac_sbr_apply.L9b9a_1 -/
abbrev L9b9a_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => False
/-- ff_aac_sbr_apply.L9bc5 -/
abbrev L9bc5 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => False
/-- ff_aac_sbr_apply.L9bca -/
abbrev L9bca (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => False
/-- ff_aac_sbr_apply.L9bcf -/
abbrev L9bcf (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => False
/-- ff_aac_sbr_apply.L9bd4 -/
abbrev L9bd4 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => False
/-- ff_aac_sbr_apply.L9bd4_1 -/
abbrev L9bd4_1 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => False
/-- ff_aac_sbr_apply.L9bff -/
abbrev L9bff (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => False
/-- ff_aac_sbr_apply.L9c04 -/
abbrev L9c04 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => False
/-- ff_aac_sbr_apply.L9c09 -/
abbrev L9c09 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => False
/-- ff_aac_sbr_apply.L9c0e -/
abbrev L9c0e (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => False
/-- ff_aac_sbr_apply.L9c13 -/
abbrev L9c13 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => False
/-- ff_aac_sbr_apply.L9c18 -/
abbrev L9c18 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => False
/-- ff_aac_sbr_apply.L9c1d -/
abbrev L9c1d (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => False
/-- ff_aac_sbr_apply.L9c22 -/
abbrev L9c22 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => False
/-- ff_aac_sbr_apply.L9c27 -/
abbrev L9c27 (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop :=
  fun s => False
end E

def ENT (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) :
    List (MachineData → Prop) := [
  E.start k e x ra t₀,
  E.start_1 k e x ra t₀,
  E.start_2 k e x ra t₀,
  E.start_3 k e x ra t₀,
  E.L676e k e x ra t₀,
  E.L6797 k e x ra t₀,
  E.L6797_1 k e x ra t₀,
  E.L6817 k e x ra t₀,
  E.L6825 k e x ra t₀,
  E.L6838 k e x ra t₀,
  E.L6838_1 k e x ra t₀,
  E.L6838_2 k e x ra t₀,
  E.L68b0 k e x ra t₀,
  E.L68d0 k e x ra t₀,
  E.L68d0_1 k e x ra t₀,
  E.L68f8 k e x ra t₀,
  E.L6940 k e x ra t₀,
  E.L6940_1 k e x ra t₀,
  E.L69a4 k e x ra t₀,
  E.L69d0 k e x ra t₀,
  E.L69dd k e x ra t₀,
  E.L6a10 k e x ra t₀,
  E.L6a30 k e x ra t₀,
  E.L6a30_1 k e x ra t₀,
  E.L6a30_2 k e x ra t₀,
  E.L6a90 k e x ra t₀,
  E.L6abf k e x ra t₀,
  E.L6b00 k e x ra t₀,
  E.L6b02 k e x ra t₀,
  E.L6b12 k e x ra t₀,
  E.L6b50 k e x ra t₀,
  E.L6b6c k e x ra t₀,
  E.L6ba0 k e x ra t₀,
  E.L6bbc k e x ra t₀,
  E.L6bbc_1 k e x ra t₀,
  E.L6c1e k e x ra t₀,
  E.L6c3a k e x ra t₀,
  E.L6c61 k e x ra t₀,
  E.L6c7d k e x ra t₀,
  E.L6c7d_1 k e x ra t₀,
  E.L6c7d_2 k e x ra t₀,
  E.L6ce0 k e x ra t₀,
  E.L6cea k e x ra t₀,
  E.L6d09 k e x ra t₀,
  E.L6d32 k e x ra t₀,
  E.L6d51 k e x ra t₀,
  E.L6d51_1 k e x ra t₀,
  E.L6dbc k e x ra t₀,
  E.L6ddb k e x ra t₀,
  E.L6e04 k e x ra t₀,
  E.L6e23 k e x ra t₀,
  E.L6e23_1 k e x ra t₀,
  E.L6e8c k e x ra t₀,
  E.L6ea8 k e x ra t₀,
  E.L6ecf k e x ra t₀,
  E.L6eeb k e x ra t₀,
  E.L6eeb_1 k e x ra t₀,
  E.L6eeb_2 k e x ra t₀,
  E.L6f32 k e x ra t₀,
  E.L6f32_1 k e x ra t₀,
  E.L6f32_2 k e x ra t₀,
  E.L6fbe k e x ra t₀,
  E.L6fca k e x ra t₀,
  E.L6ff7 k e x ra t₀,
  E.L6ffc k e x ra t₀,
  E.L7007 k e x ra t₀,
  E.L700e k e x ra t₀,
  E.L7020 k e x ra t₀,
  E.L7020_1 k e x ra t₀,
  E.L7020_2 k e x ra t₀,
  E.L7044 k e x ra t₀,
  E.L7044_1 k e x ra t₀,
  E.L7070 k e x ra t₀,
  E.L7090 k e x ra t₀,
  E.L7090_1 k e x ra t₀,
  E.L7090_2 k e x ra t₀,
  E.L70bf k e x ra t₀,
  E.L70ca k e x ra t₀,
  E.L70ca_1 k e x ra t₀,
  E.L7120 k e x ra t₀,
  E.L7140 k e x ra t₀,
  E.L7166 k e x ra t₀,
  E.L717f k e x ra t₀,
  E.L71b0 k e x ra t₀,
  E.L71e0 k e x ra t₀,
  E.L71e0_1 k e x ra t₀,
  E.L7226 k e x ra t₀,
  E.L723c k e x ra t₀,
  E.L723c_1 k e x ra t₀,
  E.L7270 k e x ra t₀,
  E.L7286 k e x ra t₀,
  E.L7286_1 k e x ra t₀,
  E.L72ba k e x ra t₀,
  E.L72d0 k e x ra t₀,
  E.L72d0_1 k e x ra t₀,
  E.L7304 k e x ra t₀,
  E.L731a k e x ra t₀,
  E.L731a_1 k e x ra t₀,
  E.L734a k e x ra t₀,
  E.L7360 k e x ra t₀,
  E.L7370 k e x ra t₀,
  E.L73a1 k e x ra t₀,
  E.L73b7 k e x ra t₀,
  E.L73b7_1 k e x ra t₀,
  E.L73eb k e x ra t₀,
  E.L7401 k e x ra t₀,
  E.L7401_1 k e x ra t₀,
  E.L7435 k e x ra t₀,
  E.L744b k e x ra t₀,
  E.L744b_1 k e x ra t₀,
  E.L747f k e x ra t₀,
  E.L7495 k e x ra t₀,
  E.L7495_1 k e x ra t₀,
  E.L74de k e x ra t₀,
  E.L74e9 k e x ra t₀,
  E.L74e9_1 k e x ra t₀,
  E.L74e9_2 k e x ra t₀,
  E.L74e9_3 k e x ra t₀,
  E.L74e9_4 k e x ra t₀,
  E.L7682 k e x ra t₀,
  E.L7682_1 k e x ra t₀,
  E.L7682_2 k e x ra t₀,
  E.L7682_3 k e x ra t₀,
  E.L7682_4 k e x ra t₀,
  E.L7682_5 k e x ra t₀,
  E.L7682_6 k e x ra t₀,
  E.L7682_7 k e x ra t₀,
  E.L7682_8 k e x ra t₀,
  E.L7750 k e x ra t₀,
  E.L7750_1 k e x ra t₀,
  E.L7750_2 k e x ra t₀,
  E.L7750_3 k e x ra t₀,
  E.L7750_4 k e x ra t₀,
  E.L7750_5 k e x ra t₀,
  E.L7750_6 k e x ra t₀,
  E.L7750_7 k e x ra t₀,
  E.L7750_8 k e x ra t₀,
  E.L7866 k e x ra t₀,
  E.L7884 k e x ra t₀,
  E.L7884_1 k e x ra t₀,
  E.L78f2 k e x ra t₀,
  E.L7910 k e x ra t₀,
  E.L7910_1 k e x ra t₀,
  E.L797e k e x ra t₀,
  E.L799c k e x ra t₀,
  E.L799c_1 k e x ra t₀,
  E.L7a0a k e x ra t₀,
  E.L7a28 k e x ra t₀,
  E.L7a28_1 k e x ra t₀,
  E.L7a96 k e x ra t₀,
  E.L7ab4 k e x ra t₀,
  E.L7b00 k e x ra t₀,
  E.L7b00_1 k e x ra t₀,
  E.L7b2d k e x ra t₀,
  E.L7b50 k e x ra t₀,
  E.L7b80 k e x ra t₀,
  E.L7bb0 k e x ra t₀,
  E.L7bb3 k e x ra t₀,
  E.L7bb3_1 k e x ra t₀,
  E.L7bb3_2 k e x ra t₀,
  E.L7c5d k e x ra t₀,
  E.L7c80 k e x ra t₀,
  E.L7c80_1 k e x ra t₀,
  E.L7cb0 k e x ra t₀,
  E.L7cbf k e x ra t₀,
  E.L7ce0 k e x ra t₀,
  E.L7ce4 k e x ra t₀,
  E.L7ce4_1 k e x ra t₀,
  E.L7ce4_2 k e x ra t₀,
  E.L7ce4_3 k e x ra t₀,
  E.L7ce4_4 k e x ra t₀,
  E.L7ce4_5 k e x ra t₀,
  E.L7db0 k e x ra t₀,
  E.L7db0_1 k e x ra t₀,
  E.L7e20 k e x ra t₀,
  E.L7e29 k e x ra t₀,
  E.L7e60 k e x ra t₀,
  E.L7e60_1 k e x ra t₀,
  E.L7e90 k e x ra t₀,
  E.L7e90_1 k e x ra t₀,
  E.L7eb6 k e x ra t₀,
  E.L7eb6_1 k e x ra t₀,
  E.L7f10 k e x ra t₀,
  E.L7f36 k e x ra t₀,
  E.L7f36_1 k e x ra t₀,
  E.L7f80 k e x ra t₀,
  E.L7f80_1 k e x ra t₀,
  E.L8009 k e x ra t₀,
  E.L8050 k e x ra t₀,
  E.L8077 k e x ra t₀,
  E.L8077_1 k e x ra t₀,
  E.L80c0 k e x ra t₀,
  E.L80c0_1 k e x ra t₀,
  E.L814a k e x ra t₀,
  E.L8190 k e x ra t₀,
  E.L81b7 k e x ra t₀,
  E.L81b7_1 k e x ra t₀,
  E.L8200 k e x ra t₀,
  E.L8200_1 k e x ra t₀,
  E.L828a k e x ra t₀,
  E.L82d0 k e x ra t₀,
  E.L82f7 k e x ra t₀,
  E.L82f7_1 k e x ra t₀,
  E.L8340 k e x ra t₀,
  E.L8340_1 k e x ra t₀,
  E.L83ca k e x ra t₀,
  E.L8410 k e x ra t₀,
  E.L8437 k e x ra t₀,
  E.L8437_1 k e x ra t₀,
  E.L8480 k e x ra t₀,
  E.L8480_1 k e x ra t₀,
  E.L8509 k e x ra t₀,
  E.L8520 k e x ra t₀,
  E.L8570 k e x ra t₀,
  E.L8570_1 k e x ra t₀,
  E.L85c0 k e x ra t₀,
  E.L85cd k e x ra t₀,
  E.L85cd_1 k e x ra t₀,
  E.L85cd_2 k e x ra t₀,
  E.L8620 k e x ra t₀,
  E.L862d k e x ra t₀,
  E.L862d_1 k e x ra t₀,
  E.L8660 k e x ra t₀,
  E.L86a0 k e x ra t₀,
  E.L86b0 k e x ra t₀,
  E.L86b0_1 k e x ra t₀,
  E.L86d7 k e x ra t₀,
  E.L8700 k e x ra t₀,
  E.L8720 k e x ra t₀,
  E.L8740 k e x ra t₀,
  E.L8740_1 k e x ra t₀,
  E.L8790 k e x ra t₀,
  E.L879e k e x ra t₀,
  E.L879e_1 k e x ra t₀,
  E.L879e_2 k e x ra t₀,
  E.L8818 k e x ra t₀,
  E.L881c k e x ra t₀,
  E.L881c_1 k e x ra t₀,
  E.L881c_2 k e x ra t₀,
  E.L881c_3 k e x ra t₀,
  E.L881c_4 k e x ra t₀,
  E.L8900 k e x ra t₀,
  E.L8900_1 k e x ra t₀,
  E.L8900_2 k e x ra t₀,
  E.L8947 k e x ra t₀,
  E.L8947_1 k e x ra t₀,
  E.L8970 k e x ra t₀,
  E.L8970_1 k e x ra t₀,
  E.L89e0 k e x ra t₀,
  E.L89f3 k e x ra t₀,
  E.L89f3_1 k e x ra t₀,
  E.L8a50 k e x ra t₀,
  E.L8a50_1 k e x ra t₀,
  E.L8a50_2 k e x ra t₀,
  E.L8a50_3 k e x ra t₀,
  E.L8ad0 k e x ra t₀,
  E.L8ad0_1 k e x ra t₀,
  E.L8b00 k e x ra t₀,
  E.L8b2a k e x ra t₀,
  E.L8b4f k e x ra t₀,
  E.L8b6b k e x ra t₀,
  E.L8b77 k e x ra t₀,
  E.L8b77_1 k e x ra t₀,
  E.L8b77_2 k e x ra t₀,
  E.L8bf0 k e x ra t₀,
  E.L8bf0_1 k e x ra t₀,
  E.L8bf0_2 k e x ra t₀,
  E.L8c33 k e x ra t₀,
  E.L8c4c k e x ra t₀,
  E.L8c4c_1 k e x ra t₀,
  E.L8c4c_2 k e x ra t₀,
  E.L8cc9 k e x ra t₀,
  E.L8cc9_1 k e x ra t₀,
  E.L8cc9_2 k e x ra t₀,
  E.L8d0c k e x ra t₀,
  E.L8d26 k e x ra t₀,
  E.L8d26_1 k e x ra t₀,
  E.L8d26_2 k e x ra t₀,
  E.L8da3 k e x ra t₀,
  E.L8da3_1 k e x ra t₀,
  E.L8da3_2 k e x ra t₀,
  E.L8de6 k e x ra t₀,
  E.L8dff k e x ra t₀,
  E.L8dff_1 k e x ra t₀,
  E.L8dff_2 k e x ra t₀,
  E.L8e7c k e x ra t₀,
  E.L8e7c_1 k e x ra t₀,
  E.L8e7c_2 k e x ra t₀,
  E.L8ebf k e x ra t₀,
  E.L8ed9 k e x ra t₀,
  E.L8ed9_1 k e x ra t₀,
  E.L8ed9_2 k e x ra t₀,
  E.L8f56 k e x ra t₀,
  E.L8f56_1 k e x ra t₀,
  E.L8f56_2 k e x ra t₀,
  E.L8f93 k e x ra t₀,
  E.L8fa4 k e x ra t₀,
  E.L8fa4_1 k e x ra t₀,
  E.L8fa4_2 k e x ra t₀,
  E.L8fa4_3 k e x ra t₀,
  E.L9026 k e x ra t₀,
  E.L9026_1 k e x ra t₀,
  E.L9026_2 k e x ra t₀,
  E.L9063 k e x ra t₀,
  E.L9070 k e x ra t₀,
  E.L907f k e x ra t₀,
  E.L907f_1 k e x ra t₀,
  E.L907f_2 k e x ra t₀,
  E.L907f_3 k e x ra t₀,
  E.L90f9 k e x ra t₀,
  E.L90f9_1 k e x ra t₀,
  E.L90f9_2 k e x ra t₀,
  E.L913a k e x ra t₀,
  E.L9146 k e x ra t₀,
  E.L914e k e x ra t₀,
  E.L914e_1 k e x ra t₀,
  E.L914e_2 k e x ra t₀,
  E.L914e_3 k e x ra t₀,
  E.L91c0 k e x ra t₀,
  E.L91f7 k e x ra t₀,
  E.L9206 k e x ra t₀,
  E.L9215 k e x ra t₀,
  E.L9215_1 k e x ra t₀,
  E.L9215_2 k e x ra t₀,
  E.L9215_3 k e x ra t₀,
  E.L9215_4 k e x ra t₀,
  E.L9215_5 k e x ra t₀,
  E.L9290 k e x ra t₀,
  E.L929e k e x ra t₀,
  E.L929e_1 k e x ra t₀,
  E.L9300 k e x ra t₀,
  E.L9300_1 k e x ra t₀,
  E.L9300_2 k e x ra t₀,
  E.L9370 k e x ra t₀,
  E.L9386 k e x ra t₀,
  E.L9386_1 k e x ra t₀,
  E.L93d0 k e x ra t₀,
  E.L93f0 k e x ra t₀,
  E.L93f0_1 k e x ra t₀,
  E.L9440 k e x ra t₀,
  E.L9458 k e x ra t₀,
  E.L9470 k e x ra t₀,
  E.L9470_1 k e x ra t₀,
  E.L9504 k e x ra t₀,
  E.L9520 k e x ra t₀,
  E.L952c k e x ra t₀,
  E.L9530 k e x ra t₀,
  E.L9530_1 k e x ra t₀,
  E.L95a0 k e x ra t₀,
  E.L95a0_1 k e x ra t₀,
  E.L95a0_2 k e x ra t₀,
  E.L9600 k e x ra t₀,
  E.L9617 k e x ra t₀,
  E.L9617_1 k e x ra t₀,
  E.L968d k e x ra t₀,
  E.L96d3 k e x ra t₀,
  E.L96e1 k e x ra t₀,
  E.L9720 k e x ra t₀,
  E.L9731 k e x ra t₀,
  E.L9731_1 k e x ra t₀,
  E.L97b7 k e x ra t₀,
  E.L97f0 k e x ra t₀,
  E.L9820 k e x ra t₀,
  E.L983f k e x ra t₀,
  E.L9860 k e x ra t₀,
  E.L9860_1 k e x ra t₀,
  E.L9860_2 k e x ra t₀,
  E.L9860_3 k e x ra t₀,
  E.L98bc k e x ra t₀,
  E.L98e0 k e x ra t₀,
  E.L9927 k e x ra t₀,
  E.L9934 k e x ra t₀,
  E.L9934_1 k e x ra t₀,
  E.L9934_2 k e x ra t₀,
  E.L99c6 k e x ra t₀,
  E.L99cf k e x ra t₀,
  E.L99e9 k e x ra t₀,
  E.L99ee k e x ra t₀,
  E.L99f3 k e x ra t₀,
  E.L99f8 k e x ra t₀,
  E.L99fd k e x ra t₀,
  E.L9a02 k e x ra t₀,
  E.L9a02_1 k e x ra t₀,
  E.L9a50 k e x ra t₀,
  E.L9a55 k e x ra t₀,
  E.L9a5a k e x ra t₀,
  E.L9a5f k e x ra t₀,
  E.L9a64 k e x ra t₀,
  E.L9a69 k e x ra t₀,
  E.L9a7d k e x ra t₀,
  E.L9a85 k e x ra t₀,
  E.L9a85_1 k e x ra t₀,
  E.L9a85_2 k e x ra t₀,
  E.L9a85_3 k e x ra t₀,
  E.L9a85_4 k e x ra t₀,
  E.L9b24 k e x ra t₀,
  E.L9b2b k e x ra t₀,
  E.done k e x ra t₀,
  E.L9b36 k e x ra t₀,
  E.L9b3b k e x ra t₀,
  E.L9b40 k e x ra t₀,
  E.L9b45 k e x ra t₀,
  E.L9b4a k e x ra t₀,
  E.L9b4f k e x ra t₀,
  E.L9b54 k e x ra t₀,
  E.L9b59 k e x ra t₀,
  E.L9b5e k e x ra t₀,
  E.L9b63 k e x ra t₀,
  E.L9b68 k e x ra t₀,
  E.L9b6d k e x ra t₀,
  E.L9b72 k e x ra t₀,
  E.L9b77 k e x ra t₀,
  E.L9b7c k e x ra t₀,
  E.L9b81 k e x ra t₀,
  E.L9b86 k e x ra t₀,
  E.L9b8b k e x ra t₀,
  E.L9b90 k e x ra t₀,
  E.L9b95 k e x ra t₀,
  E.L9b9a k e x ra t₀,
  E.L9b9a_1 k e x ra t₀,
  E.L9bc5 k e x ra t₀,
  E.L9bca k e x ra t₀,
  E.L9bcf k e x ra t₀,
  E.L9bd4 k e x ra t₀,
  E.L9bd4_1 k e x ra t₀,
  E.L9bff k e x ra t₀,
  E.L9c04 k e x ra t₀,
  E.L9c09 k e x ra t₀,
  E.L9c0e k e x ra t₀,
  E.L9c13 k e x ra t₀,
  E.L9c18 k e x ra t₀,
  E.L9c1d k e x ra t₀,
  E.L9c22 k e x ra t₀,
  E.L9c27 k e x ra t₀]


set_option maxRecDepth 100000

/-- The table: the entry of the `i`-th label is `ENT[i]`. -/
def table (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) (l : Label)
    (s : MachineData) : Prop :=
  Program.LTable labelList (ENT k e x ra t₀) l s

namespace T

theorem start {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply" s ↔ E.start k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 0) rfl rfl
theorem start_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.start_1" s ↔ E.start_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 1) rfl rfl
theorem start_2 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.start_2" s ↔ E.start_2 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 2) rfl rfl
theorem start_3 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.start_3" s ↔ E.start_3 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 3) rfl rfl
theorem L676e {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L676e" s ↔ E.L676e k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 4) rfl rfl
theorem L6797 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L6797" s ↔ E.L6797 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 5) rfl rfl
theorem L6797_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L6797_1" s ↔ E.L6797_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 6) rfl rfl
theorem L6817 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L6817" s ↔ E.L6817 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 7) rfl rfl
theorem L6825 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L6825" s ↔ E.L6825 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 8) rfl rfl
theorem L6838 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L6838" s ↔ E.L6838 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 9) rfl rfl
theorem L6838_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L6838_1" s ↔ E.L6838_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 10) rfl rfl
theorem L6838_2 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L6838_2" s ↔ E.L6838_2 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 11) rfl rfl
theorem L68b0 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L68b0" s ↔ E.L68b0 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 12) rfl rfl
theorem L68d0 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L68d0" s ↔ E.L68d0 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 13) rfl rfl
theorem L68d0_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L68d0_1" s ↔ E.L68d0_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 14) rfl rfl
theorem L68f8 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L68f8" s ↔ E.L68f8 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 15) rfl rfl
theorem L6940 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L6940" s ↔ E.L6940 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 16) rfl rfl
theorem L6940_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L6940_1" s ↔ E.L6940_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 17) rfl rfl
theorem L69a4 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L69a4" s ↔ E.L69a4 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 18) rfl rfl
theorem L69d0 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L69d0" s ↔ E.L69d0 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 19) rfl rfl
theorem L69dd {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L69dd" s ↔ E.L69dd k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 20) rfl rfl
theorem L6a10 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L6a10" s ↔ E.L6a10 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 21) rfl rfl
theorem L6a30 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L6a30" s ↔ E.L6a30 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 22) rfl rfl
theorem L6a30_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L6a30_1" s ↔ E.L6a30_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 23) rfl rfl
theorem L6a30_2 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L6a30_2" s ↔ E.L6a30_2 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 24) rfl rfl
theorem L6a90 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L6a90" s ↔ E.L6a90 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 25) rfl rfl
theorem L6abf {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L6abf" s ↔ E.L6abf k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 26) rfl rfl
theorem L6b00 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L6b00" s ↔ E.L6b00 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 27) rfl rfl
theorem L6b02 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L6b02" s ↔ E.L6b02 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 28) rfl rfl
theorem L6b12 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L6b12" s ↔ E.L6b12 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 29) rfl rfl
theorem L6b50 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L6b50" s ↔ E.L6b50 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 30) rfl rfl
theorem L6b6c {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L6b6c" s ↔ E.L6b6c k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 31) rfl rfl
theorem L6ba0 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L6ba0" s ↔ E.L6ba0 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 32) rfl rfl
theorem L6bbc {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L6bbc" s ↔ E.L6bbc k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 33) rfl rfl
theorem L6bbc_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L6bbc_1" s ↔ E.L6bbc_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 34) rfl rfl
theorem L6c1e {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L6c1e" s ↔ E.L6c1e k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 35) rfl rfl
theorem L6c3a {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L6c3a" s ↔ E.L6c3a k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 36) rfl rfl
theorem L6c61 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L6c61" s ↔ E.L6c61 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 37) rfl rfl
theorem L6c7d {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L6c7d" s ↔ E.L6c7d k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 38) rfl rfl
theorem L6c7d_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L6c7d_1" s ↔ E.L6c7d_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 39) rfl rfl
theorem L6c7d_2 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L6c7d_2" s ↔ E.L6c7d_2 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 40) rfl rfl
theorem L6ce0 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L6ce0" s ↔ E.L6ce0 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 41) rfl rfl
theorem L6cea {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L6cea" s ↔ E.L6cea k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 42) rfl rfl
theorem L6d09 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L6d09" s ↔ E.L6d09 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 43) rfl rfl
theorem L6d32 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L6d32" s ↔ E.L6d32 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 44) rfl rfl
theorem L6d51 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L6d51" s ↔ E.L6d51 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 45) rfl rfl
theorem L6d51_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L6d51_1" s ↔ E.L6d51_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 46) rfl rfl
theorem L6dbc {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L6dbc" s ↔ E.L6dbc k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 47) rfl rfl
theorem L6ddb {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L6ddb" s ↔ E.L6ddb k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 48) rfl rfl
theorem L6e04 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L6e04" s ↔ E.L6e04 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 49) rfl rfl
theorem L6e23 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L6e23" s ↔ E.L6e23 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 50) rfl rfl
theorem L6e23_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L6e23_1" s ↔ E.L6e23_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 51) rfl rfl
theorem L6e8c {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L6e8c" s ↔ E.L6e8c k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 52) rfl rfl
theorem L6ea8 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L6ea8" s ↔ E.L6ea8 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 53) rfl rfl
theorem L6ecf {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L6ecf" s ↔ E.L6ecf k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 54) rfl rfl
theorem L6eeb {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L6eeb" s ↔ E.L6eeb k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 55) rfl rfl
theorem L6eeb_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L6eeb_1" s ↔ E.L6eeb_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 56) rfl rfl
theorem L6eeb_2 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L6eeb_2" s ↔ E.L6eeb_2 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 57) rfl rfl
theorem L6f32 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L6f32" s ↔ E.L6f32 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 58) rfl rfl
theorem L6f32_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L6f32_1" s ↔ E.L6f32_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 59) rfl rfl
theorem L6f32_2 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L6f32_2" s ↔ E.L6f32_2 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 60) rfl rfl
theorem L6fbe {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L6fbe" s ↔ E.L6fbe k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 61) rfl rfl
theorem L6fca {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L6fca" s ↔ E.L6fca k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 62) rfl rfl
theorem L6ff7 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L6ff7" s ↔ E.L6ff7 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 63) rfl rfl
theorem L6ffc {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L6ffc" s ↔ E.L6ffc k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 64) rfl rfl
theorem L7007 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7007" s ↔ E.L7007 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 65) rfl rfl
theorem L700e {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L700e" s ↔ E.L700e k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 66) rfl rfl
theorem L7020 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7020" s ↔ E.L7020 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 67) rfl rfl
theorem L7020_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7020_1" s ↔ E.L7020_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 68) rfl rfl
theorem L7020_2 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7020_2" s ↔ E.L7020_2 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 69) rfl rfl
theorem L7044 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7044" s ↔ E.L7044 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 70) rfl rfl
theorem L7044_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7044_1" s ↔ E.L7044_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 71) rfl rfl
theorem L7070 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7070" s ↔ E.L7070 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 72) rfl rfl
theorem L7090 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7090" s ↔ E.L7090 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 73) rfl rfl
theorem L7090_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7090_1" s ↔ E.L7090_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 74) rfl rfl
theorem L7090_2 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7090_2" s ↔ E.L7090_2 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 75) rfl rfl
theorem L70bf {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L70bf" s ↔ E.L70bf k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 76) rfl rfl
theorem L70ca {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L70ca" s ↔ E.L70ca k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 77) rfl rfl
theorem L70ca_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L70ca_1" s ↔ E.L70ca_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 78) rfl rfl
theorem L7120 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7120" s ↔ E.L7120 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 79) rfl rfl
theorem L7140 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7140" s ↔ E.L7140 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 80) rfl rfl
theorem L7166 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7166" s ↔ E.L7166 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 81) rfl rfl
theorem L717f {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L717f" s ↔ E.L717f k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 82) rfl rfl
theorem L71b0 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L71b0" s ↔ E.L71b0 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 83) rfl rfl
theorem L71e0 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L71e0" s ↔ E.L71e0 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 84) rfl rfl
theorem L71e0_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L71e0_1" s ↔ E.L71e0_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 85) rfl rfl
theorem L7226 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7226" s ↔ E.L7226 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 86) rfl rfl
theorem L723c {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L723c" s ↔ E.L723c k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 87) rfl rfl
theorem L723c_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L723c_1" s ↔ E.L723c_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 88) rfl rfl
theorem L7270 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7270" s ↔ E.L7270 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 89) rfl rfl
theorem L7286 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7286" s ↔ E.L7286 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 90) rfl rfl
theorem L7286_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7286_1" s ↔ E.L7286_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 91) rfl rfl
theorem L72ba {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L72ba" s ↔ E.L72ba k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 92) rfl rfl
theorem L72d0 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L72d0" s ↔ E.L72d0 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 93) rfl rfl
theorem L72d0_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L72d0_1" s ↔ E.L72d0_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 94) rfl rfl
theorem L7304 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7304" s ↔ E.L7304 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 95) rfl rfl
theorem L731a {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L731a" s ↔ E.L731a k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 96) rfl rfl
theorem L731a_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L731a_1" s ↔ E.L731a_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 97) rfl rfl
theorem L734a {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L734a" s ↔ E.L734a k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 98) rfl rfl
theorem L7360 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7360" s ↔ E.L7360 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 99) rfl rfl
theorem L7370 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7370" s ↔ E.L7370 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 100) rfl rfl
theorem L73a1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L73a1" s ↔ E.L73a1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 101) rfl rfl
theorem L73b7 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L73b7" s ↔ E.L73b7 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 102) rfl rfl
theorem L73b7_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L73b7_1" s ↔ E.L73b7_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 103) rfl rfl
theorem L73eb {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L73eb" s ↔ E.L73eb k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 104) rfl rfl
theorem L7401 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7401" s ↔ E.L7401 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 105) rfl rfl
theorem L7401_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7401_1" s ↔ E.L7401_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 106) rfl rfl
theorem L7435 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7435" s ↔ E.L7435 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 107) rfl rfl
theorem L744b {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L744b" s ↔ E.L744b k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 108) rfl rfl
theorem L744b_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L744b_1" s ↔ E.L744b_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 109) rfl rfl
theorem L747f {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L747f" s ↔ E.L747f k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 110) rfl rfl
theorem L7495 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7495" s ↔ E.L7495 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 111) rfl rfl
theorem L7495_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7495_1" s ↔ E.L7495_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 112) rfl rfl
theorem L74de {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L74de" s ↔ E.L74de k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 113) rfl rfl
theorem L74e9 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L74e9" s ↔ E.L74e9 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 114) rfl rfl
theorem L74e9_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L74e9_1" s ↔ E.L74e9_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 115) rfl rfl
theorem L74e9_2 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L74e9_2" s ↔ E.L74e9_2 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 116) rfl rfl
theorem L74e9_3 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L74e9_3" s ↔ E.L74e9_3 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 117) rfl rfl
theorem L74e9_4 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L74e9_4" s ↔ E.L74e9_4 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 118) rfl rfl
theorem L7682 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7682" s ↔ E.L7682 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 119) rfl rfl
theorem L7682_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7682_1" s ↔ E.L7682_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 120) rfl rfl
theorem L7682_2 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7682_2" s ↔ E.L7682_2 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 121) rfl rfl
theorem L7682_3 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7682_3" s ↔ E.L7682_3 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 122) rfl rfl
theorem L7682_4 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7682_4" s ↔ E.L7682_4 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 123) rfl rfl
theorem L7682_5 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7682_5" s ↔ E.L7682_5 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 124) rfl rfl
theorem L7682_6 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7682_6" s ↔ E.L7682_6 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 125) rfl rfl
theorem L7682_7 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7682_7" s ↔ E.L7682_7 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 126) rfl rfl
theorem L7682_8 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7682_8" s ↔ E.L7682_8 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 127) rfl rfl
theorem L7750 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7750" s ↔ E.L7750 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 128) rfl rfl
theorem L7750_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7750_1" s ↔ E.L7750_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 129) rfl rfl
theorem L7750_2 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7750_2" s ↔ E.L7750_2 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 130) rfl rfl
theorem L7750_3 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7750_3" s ↔ E.L7750_3 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 131) rfl rfl
theorem L7750_4 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7750_4" s ↔ E.L7750_4 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 132) rfl rfl
theorem L7750_5 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7750_5" s ↔ E.L7750_5 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 133) rfl rfl
theorem L7750_6 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7750_6" s ↔ E.L7750_6 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 134) rfl rfl
theorem L7750_7 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7750_7" s ↔ E.L7750_7 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 135) rfl rfl
theorem L7750_8 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7750_8" s ↔ E.L7750_8 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 136) rfl rfl
theorem L7866 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7866" s ↔ E.L7866 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 137) rfl rfl
theorem L7884 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7884" s ↔ E.L7884 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 138) rfl rfl
theorem L7884_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7884_1" s ↔ E.L7884_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 139) rfl rfl
theorem L78f2 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L78f2" s ↔ E.L78f2 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 140) rfl rfl
theorem L7910 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7910" s ↔ E.L7910 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 141) rfl rfl
theorem L7910_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7910_1" s ↔ E.L7910_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 142) rfl rfl
theorem L797e {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L797e" s ↔ E.L797e k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 143) rfl rfl
theorem L799c {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L799c" s ↔ E.L799c k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 144) rfl rfl
theorem L799c_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L799c_1" s ↔ E.L799c_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 145) rfl rfl
theorem L7a0a {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7a0a" s ↔ E.L7a0a k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 146) rfl rfl
theorem L7a28 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7a28" s ↔ E.L7a28 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 147) rfl rfl
theorem L7a28_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7a28_1" s ↔ E.L7a28_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 148) rfl rfl
theorem L7a96 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7a96" s ↔ E.L7a96 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 149) rfl rfl
theorem L7ab4 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7ab4" s ↔ E.L7ab4 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 150) rfl rfl
theorem L7b00 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7b00" s ↔ E.L7b00 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 151) rfl rfl
theorem L7b00_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7b00_1" s ↔ E.L7b00_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 152) rfl rfl
theorem L7b2d {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7b2d" s ↔ E.L7b2d k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 153) rfl rfl
theorem L7b50 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7b50" s ↔ E.L7b50 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 154) rfl rfl
theorem L7b80 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7b80" s ↔ E.L7b80 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 155) rfl rfl
theorem L7bb0 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7bb0" s ↔ E.L7bb0 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 156) rfl rfl
theorem L7bb3 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7bb3" s ↔ E.L7bb3 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 157) rfl rfl
theorem L7bb3_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7bb3_1" s ↔ E.L7bb3_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 158) rfl rfl
theorem L7bb3_2 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7bb3_2" s ↔ E.L7bb3_2 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 159) rfl rfl
theorem L7c5d {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7c5d" s ↔ E.L7c5d k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 160) rfl rfl
theorem L7c80 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7c80" s ↔ E.L7c80 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 161) rfl rfl
theorem L7c80_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7c80_1" s ↔ E.L7c80_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 162) rfl rfl
theorem L7cb0 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7cb0" s ↔ E.L7cb0 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 163) rfl rfl
theorem L7cbf {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7cbf" s ↔ E.L7cbf k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 164) rfl rfl
theorem L7ce0 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7ce0" s ↔ E.L7ce0 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 165) rfl rfl
theorem L7ce4 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7ce4" s ↔ E.L7ce4 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 166) rfl rfl
theorem L7ce4_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7ce4_1" s ↔ E.L7ce4_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 167) rfl rfl
theorem L7ce4_2 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7ce4_2" s ↔ E.L7ce4_2 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 168) rfl rfl
theorem L7ce4_3 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7ce4_3" s ↔ E.L7ce4_3 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 169) rfl rfl
theorem L7ce4_4 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7ce4_4" s ↔ E.L7ce4_4 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 170) rfl rfl
theorem L7ce4_5 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7ce4_5" s ↔ E.L7ce4_5 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 171) rfl rfl
theorem L7db0 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7db0" s ↔ E.L7db0 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 172) rfl rfl
theorem L7db0_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7db0_1" s ↔ E.L7db0_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 173) rfl rfl
theorem L7e20 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7e20" s ↔ E.L7e20 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 174) rfl rfl
theorem L7e29 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7e29" s ↔ E.L7e29 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 175) rfl rfl
theorem L7e60 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7e60" s ↔ E.L7e60 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 176) rfl rfl
theorem L7e60_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7e60_1" s ↔ E.L7e60_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 177) rfl rfl
theorem L7e90 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7e90" s ↔ E.L7e90 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 178) rfl rfl
theorem L7e90_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7e90_1" s ↔ E.L7e90_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 179) rfl rfl
theorem L7eb6 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7eb6" s ↔ E.L7eb6 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 180) rfl rfl
theorem L7eb6_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7eb6_1" s ↔ E.L7eb6_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 181) rfl rfl
theorem L7f10 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7f10" s ↔ E.L7f10 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 182) rfl rfl
theorem L7f36 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7f36" s ↔ E.L7f36 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 183) rfl rfl
theorem L7f36_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7f36_1" s ↔ E.L7f36_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 184) rfl rfl
theorem L7f80 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7f80" s ↔ E.L7f80 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 185) rfl rfl
theorem L7f80_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L7f80_1" s ↔ E.L7f80_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 186) rfl rfl
theorem L8009 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8009" s ↔ E.L8009 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 187) rfl rfl
theorem L8050 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8050" s ↔ E.L8050 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 188) rfl rfl
theorem L8077 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8077" s ↔ E.L8077 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 189) rfl rfl
theorem L8077_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8077_1" s ↔ E.L8077_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 190) rfl rfl
theorem L80c0 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L80c0" s ↔ E.L80c0 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 191) rfl rfl
theorem L80c0_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L80c0_1" s ↔ E.L80c0_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 192) rfl rfl
theorem L814a {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L814a" s ↔ E.L814a k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 193) rfl rfl
theorem L8190 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8190" s ↔ E.L8190 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 194) rfl rfl
theorem L81b7 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L81b7" s ↔ E.L81b7 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 195) rfl rfl
theorem L81b7_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L81b7_1" s ↔ E.L81b7_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 196) rfl rfl
theorem L8200 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8200" s ↔ E.L8200 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 197) rfl rfl
theorem L8200_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8200_1" s ↔ E.L8200_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 198) rfl rfl
theorem L828a {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L828a" s ↔ E.L828a k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 199) rfl rfl
theorem L82d0 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L82d0" s ↔ E.L82d0 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 200) rfl rfl
theorem L82f7 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L82f7" s ↔ E.L82f7 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 201) rfl rfl
theorem L82f7_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L82f7_1" s ↔ E.L82f7_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 202) rfl rfl
theorem L8340 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8340" s ↔ E.L8340 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 203) rfl rfl
theorem L8340_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8340_1" s ↔ E.L8340_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 204) rfl rfl
theorem L83ca {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L83ca" s ↔ E.L83ca k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 205) rfl rfl
theorem L8410 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8410" s ↔ E.L8410 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 206) rfl rfl
theorem L8437 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8437" s ↔ E.L8437 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 207) rfl rfl
theorem L8437_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8437_1" s ↔ E.L8437_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 208) rfl rfl
theorem L8480 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8480" s ↔ E.L8480 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 209) rfl rfl
theorem L8480_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8480_1" s ↔ E.L8480_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 210) rfl rfl
theorem L8509 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8509" s ↔ E.L8509 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 211) rfl rfl
theorem L8520 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8520" s ↔ E.L8520 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 212) rfl rfl
theorem L8570 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8570" s ↔ E.L8570 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 213) rfl rfl
theorem L8570_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8570_1" s ↔ E.L8570_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 214) rfl rfl
theorem L85c0 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L85c0" s ↔ E.L85c0 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 215) rfl rfl
theorem L85cd {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L85cd" s ↔ E.L85cd k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 216) rfl rfl
theorem L85cd_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L85cd_1" s ↔ E.L85cd_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 217) rfl rfl
theorem L85cd_2 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L85cd_2" s ↔ E.L85cd_2 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 218) rfl rfl
theorem L8620 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8620" s ↔ E.L8620 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 219) rfl rfl
theorem L862d {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L862d" s ↔ E.L862d k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 220) rfl rfl
theorem L862d_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L862d_1" s ↔ E.L862d_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 221) rfl rfl
theorem L8660 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8660" s ↔ E.L8660 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 222) rfl rfl
theorem L86a0 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L86a0" s ↔ E.L86a0 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 223) rfl rfl
theorem L86b0 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L86b0" s ↔ E.L86b0 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 224) rfl rfl
theorem L86b0_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L86b0_1" s ↔ E.L86b0_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 225) rfl rfl
theorem L86d7 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L86d7" s ↔ E.L86d7 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 226) rfl rfl
theorem L8700 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8700" s ↔ E.L8700 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 227) rfl rfl
theorem L8720 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8720" s ↔ E.L8720 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 228) rfl rfl
theorem L8740 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8740" s ↔ E.L8740 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 229) rfl rfl
theorem L8740_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8740_1" s ↔ E.L8740_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 230) rfl rfl
theorem L8790 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8790" s ↔ E.L8790 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 231) rfl rfl
theorem L879e {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L879e" s ↔ E.L879e k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 232) rfl rfl
theorem L879e_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L879e_1" s ↔ E.L879e_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 233) rfl rfl
theorem L879e_2 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L879e_2" s ↔ E.L879e_2 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 234) rfl rfl
theorem L8818 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8818" s ↔ E.L8818 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 235) rfl rfl
theorem L881c {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L881c" s ↔ E.L881c k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 236) rfl rfl
theorem L881c_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L881c_1" s ↔ E.L881c_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 237) rfl rfl
theorem L881c_2 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L881c_2" s ↔ E.L881c_2 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 238) rfl rfl
theorem L881c_3 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L881c_3" s ↔ E.L881c_3 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 239) rfl rfl
theorem L881c_4 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L881c_4" s ↔ E.L881c_4 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 240) rfl rfl
theorem L8900 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8900" s ↔ E.L8900 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 241) rfl rfl
theorem L8900_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8900_1" s ↔ E.L8900_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 242) rfl rfl
theorem L8900_2 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8900_2" s ↔ E.L8900_2 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 243) rfl rfl
theorem L8947 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8947" s ↔ E.L8947 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 244) rfl rfl
theorem L8947_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8947_1" s ↔ E.L8947_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 245) rfl rfl
theorem L8970 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8970" s ↔ E.L8970 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 246) rfl rfl
theorem L8970_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8970_1" s ↔ E.L8970_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 247) rfl rfl
theorem L89e0 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L89e0" s ↔ E.L89e0 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 248) rfl rfl
theorem L89f3 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L89f3" s ↔ E.L89f3 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 249) rfl rfl
theorem L89f3_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L89f3_1" s ↔ E.L89f3_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 250) rfl rfl
theorem L8a50 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8a50" s ↔ E.L8a50 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 251) rfl rfl
theorem L8a50_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8a50_1" s ↔ E.L8a50_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 252) rfl rfl
theorem L8a50_2 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8a50_2" s ↔ E.L8a50_2 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 253) rfl rfl
theorem L8a50_3 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8a50_3" s ↔ E.L8a50_3 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 254) rfl rfl
theorem L8ad0 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8ad0" s ↔ E.L8ad0 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 255) rfl rfl
theorem L8ad0_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8ad0_1" s ↔ E.L8ad0_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 256) rfl rfl
theorem L8b00 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8b00" s ↔ E.L8b00 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 257) rfl rfl
theorem L8b2a {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8b2a" s ↔ E.L8b2a k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 258) rfl rfl
theorem L8b4f {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8b4f" s ↔ E.L8b4f k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 259) rfl rfl
theorem L8b6b {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8b6b" s ↔ E.L8b6b k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 260) rfl rfl
theorem L8b77 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8b77" s ↔ E.L8b77 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 261) rfl rfl
theorem L8b77_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8b77_1" s ↔ E.L8b77_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 262) rfl rfl
theorem L8b77_2 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8b77_2" s ↔ E.L8b77_2 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 263) rfl rfl
theorem L8bf0 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8bf0" s ↔ E.L8bf0 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 264) rfl rfl
theorem L8bf0_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8bf0_1" s ↔ E.L8bf0_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 265) rfl rfl
theorem L8bf0_2 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8bf0_2" s ↔ E.L8bf0_2 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 266) rfl rfl
theorem L8c33 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8c33" s ↔ E.L8c33 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 267) rfl rfl
theorem L8c4c {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8c4c" s ↔ E.L8c4c k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 268) rfl rfl
theorem L8c4c_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8c4c_1" s ↔ E.L8c4c_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 269) rfl rfl
theorem L8c4c_2 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8c4c_2" s ↔ E.L8c4c_2 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 270) rfl rfl
theorem L8cc9 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8cc9" s ↔ E.L8cc9 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 271) rfl rfl
theorem L8cc9_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8cc9_1" s ↔ E.L8cc9_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 272) rfl rfl
theorem L8cc9_2 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8cc9_2" s ↔ E.L8cc9_2 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 273) rfl rfl
theorem L8d0c {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8d0c" s ↔ E.L8d0c k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 274) rfl rfl
theorem L8d26 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8d26" s ↔ E.L8d26 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 275) rfl rfl
theorem L8d26_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8d26_1" s ↔ E.L8d26_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 276) rfl rfl
theorem L8d26_2 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8d26_2" s ↔ E.L8d26_2 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 277) rfl rfl
theorem L8da3 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8da3" s ↔ E.L8da3 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 278) rfl rfl
theorem L8da3_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8da3_1" s ↔ E.L8da3_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 279) rfl rfl
theorem L8da3_2 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8da3_2" s ↔ E.L8da3_2 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 280) rfl rfl
theorem L8de6 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8de6" s ↔ E.L8de6 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 281) rfl rfl
theorem L8dff {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8dff" s ↔ E.L8dff k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 282) rfl rfl
theorem L8dff_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8dff_1" s ↔ E.L8dff_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 283) rfl rfl
theorem L8dff_2 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8dff_2" s ↔ E.L8dff_2 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 284) rfl rfl
theorem L8e7c {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8e7c" s ↔ E.L8e7c k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 285) rfl rfl
theorem L8e7c_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8e7c_1" s ↔ E.L8e7c_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 286) rfl rfl
theorem L8e7c_2 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8e7c_2" s ↔ E.L8e7c_2 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 287) rfl rfl
theorem L8ebf {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8ebf" s ↔ E.L8ebf k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 288) rfl rfl
theorem L8ed9 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8ed9" s ↔ E.L8ed9 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 289) rfl rfl
theorem L8ed9_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8ed9_1" s ↔ E.L8ed9_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 290) rfl rfl
theorem L8ed9_2 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8ed9_2" s ↔ E.L8ed9_2 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 291) rfl rfl
theorem L8f56 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8f56" s ↔ E.L8f56 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 292) rfl rfl
theorem L8f56_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8f56_1" s ↔ E.L8f56_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 293) rfl rfl
theorem L8f56_2 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8f56_2" s ↔ E.L8f56_2 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 294) rfl rfl
theorem L8f93 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8f93" s ↔ E.L8f93 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 295) rfl rfl
theorem L8fa4 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8fa4" s ↔ E.L8fa4 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 296) rfl rfl
theorem L8fa4_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8fa4_1" s ↔ E.L8fa4_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 297) rfl rfl
theorem L8fa4_2 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8fa4_2" s ↔ E.L8fa4_2 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 298) rfl rfl
theorem L8fa4_3 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L8fa4_3" s ↔ E.L8fa4_3 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 299) rfl rfl
theorem L9026 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9026" s ↔ E.L9026 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 300) rfl rfl
theorem L9026_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9026_1" s ↔ E.L9026_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 301) rfl rfl
theorem L9026_2 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9026_2" s ↔ E.L9026_2 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 302) rfl rfl
theorem L9063 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9063" s ↔ E.L9063 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 303) rfl rfl
theorem L9070 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9070" s ↔ E.L9070 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 304) rfl rfl
theorem L907f {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L907f" s ↔ E.L907f k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 305) rfl rfl
theorem L907f_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L907f_1" s ↔ E.L907f_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 306) rfl rfl
theorem L907f_2 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L907f_2" s ↔ E.L907f_2 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 307) rfl rfl
theorem L907f_3 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L907f_3" s ↔ E.L907f_3 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 308) rfl rfl
theorem L90f9 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L90f9" s ↔ E.L90f9 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 309) rfl rfl
theorem L90f9_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L90f9_1" s ↔ E.L90f9_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 310) rfl rfl
theorem L90f9_2 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L90f9_2" s ↔ E.L90f9_2 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 311) rfl rfl
theorem L913a {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L913a" s ↔ E.L913a k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 312) rfl rfl
theorem L9146 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9146" s ↔ E.L9146 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 313) rfl rfl
theorem L914e {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L914e" s ↔ E.L914e k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 314) rfl rfl
theorem L914e_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L914e_1" s ↔ E.L914e_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 315) rfl rfl
theorem L914e_2 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L914e_2" s ↔ E.L914e_2 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 316) rfl rfl
theorem L914e_3 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L914e_3" s ↔ E.L914e_3 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 317) rfl rfl
theorem L91c0 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L91c0" s ↔ E.L91c0 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 318) rfl rfl
theorem L91f7 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L91f7" s ↔ E.L91f7 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 319) rfl rfl
theorem L9206 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9206" s ↔ E.L9206 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 320) rfl rfl
theorem L9215 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9215" s ↔ E.L9215 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 321) rfl rfl
theorem L9215_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9215_1" s ↔ E.L9215_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 322) rfl rfl
theorem L9215_2 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9215_2" s ↔ E.L9215_2 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 323) rfl rfl
theorem L9215_3 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9215_3" s ↔ E.L9215_3 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 324) rfl rfl
theorem L9215_4 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9215_4" s ↔ E.L9215_4 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 325) rfl rfl
theorem L9215_5 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9215_5" s ↔ E.L9215_5 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 326) rfl rfl
theorem L9290 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9290" s ↔ E.L9290 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 327) rfl rfl
theorem L929e {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L929e" s ↔ E.L929e k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 328) rfl rfl
theorem L929e_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L929e_1" s ↔ E.L929e_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 329) rfl rfl
theorem L9300 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9300" s ↔ E.L9300 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 330) rfl rfl
theorem L9300_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9300_1" s ↔ E.L9300_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 331) rfl rfl
theorem L9300_2 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9300_2" s ↔ E.L9300_2 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 332) rfl rfl
theorem L9370 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9370" s ↔ E.L9370 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 333) rfl rfl
theorem L9386 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9386" s ↔ E.L9386 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 334) rfl rfl
theorem L9386_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9386_1" s ↔ E.L9386_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 335) rfl rfl
theorem L93d0 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L93d0" s ↔ E.L93d0 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 336) rfl rfl
theorem L93f0 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L93f0" s ↔ E.L93f0 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 337) rfl rfl
theorem L93f0_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L93f0_1" s ↔ E.L93f0_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 338) rfl rfl
theorem L9440 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9440" s ↔ E.L9440 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 339) rfl rfl
theorem L9458 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9458" s ↔ E.L9458 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 340) rfl rfl
theorem L9470 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9470" s ↔ E.L9470 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 341) rfl rfl
theorem L9470_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9470_1" s ↔ E.L9470_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 342) rfl rfl
theorem L9504 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9504" s ↔ E.L9504 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 343) rfl rfl
theorem L9520 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9520" s ↔ E.L9520 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 344) rfl rfl
theorem L952c {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L952c" s ↔ E.L952c k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 345) rfl rfl
theorem L9530 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9530" s ↔ E.L9530 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 346) rfl rfl
theorem L9530_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9530_1" s ↔ E.L9530_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 347) rfl rfl
theorem L95a0 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L95a0" s ↔ E.L95a0 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 348) rfl rfl
theorem L95a0_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L95a0_1" s ↔ E.L95a0_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 349) rfl rfl
theorem L95a0_2 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L95a0_2" s ↔ E.L95a0_2 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 350) rfl rfl
theorem L9600 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9600" s ↔ E.L9600 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 351) rfl rfl
theorem L9617 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9617" s ↔ E.L9617 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 352) rfl rfl
theorem L9617_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9617_1" s ↔ E.L9617_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 353) rfl rfl
theorem L968d {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L968d" s ↔ E.L968d k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 354) rfl rfl
theorem L96d3 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L96d3" s ↔ E.L96d3 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 355) rfl rfl
theorem L96e1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L96e1" s ↔ E.L96e1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 356) rfl rfl
theorem L9720 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9720" s ↔ E.L9720 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 357) rfl rfl
theorem L9731 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9731" s ↔ E.L9731 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 358) rfl rfl
theorem L9731_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9731_1" s ↔ E.L9731_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 359) rfl rfl
theorem L97b7 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L97b7" s ↔ E.L97b7 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 360) rfl rfl
theorem L97f0 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L97f0" s ↔ E.L97f0 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 361) rfl rfl
theorem L9820 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9820" s ↔ E.L9820 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 362) rfl rfl
theorem L983f {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L983f" s ↔ E.L983f k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 363) rfl rfl
theorem L9860 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9860" s ↔ E.L9860 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 364) rfl rfl
theorem L9860_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9860_1" s ↔ E.L9860_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 365) rfl rfl
theorem L9860_2 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9860_2" s ↔ E.L9860_2 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 366) rfl rfl
theorem L9860_3 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9860_3" s ↔ E.L9860_3 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 367) rfl rfl
theorem L98bc {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L98bc" s ↔ E.L98bc k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 368) rfl rfl
theorem L98e0 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L98e0" s ↔ E.L98e0 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 369) rfl rfl
theorem L9927 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9927" s ↔ E.L9927 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 370) rfl rfl
theorem L9934 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9934" s ↔ E.L9934 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 371) rfl rfl
theorem L9934_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9934_1" s ↔ E.L9934_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 372) rfl rfl
theorem L9934_2 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9934_2" s ↔ E.L9934_2 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 373) rfl rfl
theorem L99c6 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L99c6" s ↔ E.L99c6 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 374) rfl rfl
theorem L99cf {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L99cf" s ↔ E.L99cf k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 375) rfl rfl
theorem L99e9 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L99e9" s ↔ E.L99e9 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 376) rfl rfl
theorem L99ee {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L99ee" s ↔ E.L99ee k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 377) rfl rfl
theorem L99f3 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L99f3" s ↔ E.L99f3 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 378) rfl rfl
theorem L99f8 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L99f8" s ↔ E.L99f8 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 379) rfl rfl
theorem L99fd {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L99fd" s ↔ E.L99fd k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 380) rfl rfl
theorem L9a02 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9a02" s ↔ E.L9a02 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 381) rfl rfl
theorem L9a02_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9a02_1" s ↔ E.L9a02_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 382) rfl rfl
theorem L9a50 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9a50" s ↔ E.L9a50 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 383) rfl rfl
theorem L9a55 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9a55" s ↔ E.L9a55 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 384) rfl rfl
theorem L9a5a {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9a5a" s ↔ E.L9a5a k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 385) rfl rfl
theorem L9a5f {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9a5f" s ↔ E.L9a5f k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 386) rfl rfl
theorem L9a64 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9a64" s ↔ E.L9a64 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 387) rfl rfl
theorem L9a69 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9a69" s ↔ E.L9a69 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 388) rfl rfl
theorem L9a7d {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9a7d" s ↔ E.L9a7d k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 389) rfl rfl
theorem L9a85 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9a85" s ↔ E.L9a85 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 390) rfl rfl
theorem L9a85_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9a85_1" s ↔ E.L9a85_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 391) rfl rfl
theorem L9a85_2 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9a85_2" s ↔ E.L9a85_2 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 392) rfl rfl
theorem L9a85_3 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9a85_3" s ↔ E.L9a85_3 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 393) rfl rfl
theorem L9a85_4 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9a85_4" s ↔ E.L9a85_4 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 394) rfl rfl
theorem L9b24 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9b24" s ↔ E.L9b24 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 395) rfl rfl
theorem L9b2b {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9b2b" s ↔ E.L9b2b k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 396) rfl rfl
theorem done {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.done" s ↔ E.done k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 397) rfl rfl
theorem L9b36 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9b36" s ↔ E.L9b36 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 398) rfl rfl
theorem L9b3b {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9b3b" s ↔ E.L9b3b k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 399) rfl rfl
theorem L9b40 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9b40" s ↔ E.L9b40 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 400) rfl rfl
theorem L9b45 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9b45" s ↔ E.L9b45 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 401) rfl rfl
theorem L9b4a {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9b4a" s ↔ E.L9b4a k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 402) rfl rfl
theorem L9b4f {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9b4f" s ↔ E.L9b4f k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 403) rfl rfl
theorem L9b54 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9b54" s ↔ E.L9b54 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 404) rfl rfl
theorem L9b59 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9b59" s ↔ E.L9b59 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 405) rfl rfl
theorem L9b5e {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9b5e" s ↔ E.L9b5e k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 406) rfl rfl
theorem L9b63 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9b63" s ↔ E.L9b63 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 407) rfl rfl
theorem L9b68 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9b68" s ↔ E.L9b68 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 408) rfl rfl
theorem L9b6d {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9b6d" s ↔ E.L9b6d k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 409) rfl rfl
theorem L9b72 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9b72" s ↔ E.L9b72 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 410) rfl rfl
theorem L9b77 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9b77" s ↔ E.L9b77 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 411) rfl rfl
theorem L9b7c {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9b7c" s ↔ E.L9b7c k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 412) rfl rfl
theorem L9b81 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9b81" s ↔ E.L9b81 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 413) rfl rfl
theorem L9b86 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9b86" s ↔ E.L9b86 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 414) rfl rfl
theorem L9b8b {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9b8b" s ↔ E.L9b8b k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 415) rfl rfl
theorem L9b90 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9b90" s ↔ E.L9b90 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 416) rfl rfl
theorem L9b95 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9b95" s ↔ E.L9b95 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 417) rfl rfl
theorem L9b9a {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9b9a" s ↔ E.L9b9a k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 418) rfl rfl
theorem L9b9a_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9b9a_1" s ↔ E.L9b9a_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 419) rfl rfl
theorem L9bc5 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9bc5" s ↔ E.L9bc5 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 420) rfl rfl
theorem L9bca {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9bca" s ↔ E.L9bca k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 421) rfl rfl
theorem L9bcf {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9bcf" s ↔ E.L9bcf k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 422) rfl rfl
theorem L9bd4 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9bd4" s ↔ E.L9bd4 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 423) rfl rfl
theorem L9bd4_1 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9bd4_1" s ↔ E.L9bd4_1 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 424) rfl rfl
theorem L9bff {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9bff" s ↔ E.L9bff k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 425) rfl rfl
theorem L9c04 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9c04" s ↔ E.L9c04 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 426) rfl rfl
theorem L9c09 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9c09" s ↔ E.L9c09 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 427) rfl rfl
theorem L9c0e {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9c0e" s ↔ E.L9c0e k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 428) rfl rfl
theorem L9c13 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9c13" s ↔ E.L9c13 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 429) rfl rfl
theorem L9c18 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9c18" s ↔ E.L9c18 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 430) rfl rfl
theorem L9c1d {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9c1d" s ↔ E.L9c1d k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 431) rfl rfl
theorem L9c22 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9c22" s ↔ E.L9c22 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 432) rfl rfl
theorem L9c27 {k e x ra t₀ s} : table k e x ra t₀ "ff_aac_sbr_apply.L9c27" s ↔ E.L9c27 k e x ra t₀ s :=
  Program.LTable.iff labelList_nodup (i := 433) rfl rfl
end T

namespace L

theorem start : labelList[0]? = some "ff_aac_sbr_apply" := rfl
theorem start_1 : labelList[1]? = some "ff_aac_sbr_apply.start_1" := rfl
theorem start_2 : labelList[2]? = some "ff_aac_sbr_apply.start_2" := rfl
theorem start_3 : labelList[3]? = some "ff_aac_sbr_apply.start_3" := rfl
theorem L676e : labelList[4]? = some "ff_aac_sbr_apply.L676e" := rfl
theorem L6797 : labelList[5]? = some "ff_aac_sbr_apply.L6797" := rfl
theorem L6797_1 : labelList[6]? = some "ff_aac_sbr_apply.L6797_1" := rfl
theorem L6817 : labelList[7]? = some "ff_aac_sbr_apply.L6817" := rfl
theorem L6825 : labelList[8]? = some "ff_aac_sbr_apply.L6825" := rfl
theorem L6838 : labelList[9]? = some "ff_aac_sbr_apply.L6838" := rfl
theorem L6838_1 : labelList[10]? = some "ff_aac_sbr_apply.L6838_1" := rfl
theorem L6838_2 : labelList[11]? = some "ff_aac_sbr_apply.L6838_2" := rfl
theorem L68b0 : labelList[12]? = some "ff_aac_sbr_apply.L68b0" := rfl
theorem L68d0 : labelList[13]? = some "ff_aac_sbr_apply.L68d0" := rfl
theorem L68d0_1 : labelList[14]? = some "ff_aac_sbr_apply.L68d0_1" := rfl
theorem L68f8 : labelList[15]? = some "ff_aac_sbr_apply.L68f8" := rfl
theorem L6940 : labelList[16]? = some "ff_aac_sbr_apply.L6940" := rfl
theorem L6940_1 : labelList[17]? = some "ff_aac_sbr_apply.L6940_1" := rfl
theorem L69a4 : labelList[18]? = some "ff_aac_sbr_apply.L69a4" := rfl
theorem L69d0 : labelList[19]? = some "ff_aac_sbr_apply.L69d0" := rfl
theorem L69dd : labelList[20]? = some "ff_aac_sbr_apply.L69dd" := rfl
theorem L6a10 : labelList[21]? = some "ff_aac_sbr_apply.L6a10" := rfl
theorem L6a30 : labelList[22]? = some "ff_aac_sbr_apply.L6a30" := rfl
theorem L6a30_1 : labelList[23]? = some "ff_aac_sbr_apply.L6a30_1" := rfl
theorem L6a30_2 : labelList[24]? = some "ff_aac_sbr_apply.L6a30_2" := rfl
theorem L6a90 : labelList[25]? = some "ff_aac_sbr_apply.L6a90" := rfl
theorem L6abf : labelList[26]? = some "ff_aac_sbr_apply.L6abf" := rfl
theorem L6b00 : labelList[27]? = some "ff_aac_sbr_apply.L6b00" := rfl
theorem L6b02 : labelList[28]? = some "ff_aac_sbr_apply.L6b02" := rfl
theorem L6b12 : labelList[29]? = some "ff_aac_sbr_apply.L6b12" := rfl
theorem L6b50 : labelList[30]? = some "ff_aac_sbr_apply.L6b50" := rfl
theorem L6b6c : labelList[31]? = some "ff_aac_sbr_apply.L6b6c" := rfl
theorem L6ba0 : labelList[32]? = some "ff_aac_sbr_apply.L6ba0" := rfl
theorem L6bbc : labelList[33]? = some "ff_aac_sbr_apply.L6bbc" := rfl
theorem L6bbc_1 : labelList[34]? = some "ff_aac_sbr_apply.L6bbc_1" := rfl
theorem L6c1e : labelList[35]? = some "ff_aac_sbr_apply.L6c1e" := rfl
theorem L6c3a : labelList[36]? = some "ff_aac_sbr_apply.L6c3a" := rfl
theorem L6c61 : labelList[37]? = some "ff_aac_sbr_apply.L6c61" := rfl
theorem L6c7d : labelList[38]? = some "ff_aac_sbr_apply.L6c7d" := rfl
theorem L6c7d_1 : labelList[39]? = some "ff_aac_sbr_apply.L6c7d_1" := rfl
theorem L6c7d_2 : labelList[40]? = some "ff_aac_sbr_apply.L6c7d_2" := rfl
theorem L6ce0 : labelList[41]? = some "ff_aac_sbr_apply.L6ce0" := rfl
theorem L6cea : labelList[42]? = some "ff_aac_sbr_apply.L6cea" := rfl
theorem L6d09 : labelList[43]? = some "ff_aac_sbr_apply.L6d09" := rfl
theorem L6d32 : labelList[44]? = some "ff_aac_sbr_apply.L6d32" := rfl
theorem L6d51 : labelList[45]? = some "ff_aac_sbr_apply.L6d51" := rfl
theorem L6d51_1 : labelList[46]? = some "ff_aac_sbr_apply.L6d51_1" := rfl
theorem L6dbc : labelList[47]? = some "ff_aac_sbr_apply.L6dbc" := rfl
theorem L6ddb : labelList[48]? = some "ff_aac_sbr_apply.L6ddb" := rfl
theorem L6e04 : labelList[49]? = some "ff_aac_sbr_apply.L6e04" := rfl
theorem L6e23 : labelList[50]? = some "ff_aac_sbr_apply.L6e23" := rfl
theorem L6e23_1 : labelList[51]? = some "ff_aac_sbr_apply.L6e23_1" := rfl
theorem L6e8c : labelList[52]? = some "ff_aac_sbr_apply.L6e8c" := rfl
theorem L6ea8 : labelList[53]? = some "ff_aac_sbr_apply.L6ea8" := rfl
theorem L6ecf : labelList[54]? = some "ff_aac_sbr_apply.L6ecf" := rfl
theorem L6eeb : labelList[55]? = some "ff_aac_sbr_apply.L6eeb" := rfl
theorem L6eeb_1 : labelList[56]? = some "ff_aac_sbr_apply.L6eeb_1" := rfl
theorem L6eeb_2 : labelList[57]? = some "ff_aac_sbr_apply.L6eeb_2" := rfl
theorem L6f32 : labelList[58]? = some "ff_aac_sbr_apply.L6f32" := rfl
theorem L6f32_1 : labelList[59]? = some "ff_aac_sbr_apply.L6f32_1" := rfl
theorem L6f32_2 : labelList[60]? = some "ff_aac_sbr_apply.L6f32_2" := rfl
theorem L6fbe : labelList[61]? = some "ff_aac_sbr_apply.L6fbe" := rfl
theorem L6fca : labelList[62]? = some "ff_aac_sbr_apply.L6fca" := rfl
theorem L6ff7 : labelList[63]? = some "ff_aac_sbr_apply.L6ff7" := rfl
theorem L6ffc : labelList[64]? = some "ff_aac_sbr_apply.L6ffc" := rfl
theorem L7007 : labelList[65]? = some "ff_aac_sbr_apply.L7007" := rfl
theorem L700e : labelList[66]? = some "ff_aac_sbr_apply.L700e" := rfl
theorem L7020 : labelList[67]? = some "ff_aac_sbr_apply.L7020" := rfl
theorem L7020_1 : labelList[68]? = some "ff_aac_sbr_apply.L7020_1" := rfl
theorem L7020_2 : labelList[69]? = some "ff_aac_sbr_apply.L7020_2" := rfl
theorem L7044 : labelList[70]? = some "ff_aac_sbr_apply.L7044" := rfl
theorem L7044_1 : labelList[71]? = some "ff_aac_sbr_apply.L7044_1" := rfl
theorem L7070 : labelList[72]? = some "ff_aac_sbr_apply.L7070" := rfl
theorem L7090 : labelList[73]? = some "ff_aac_sbr_apply.L7090" := rfl
theorem L7090_1 : labelList[74]? = some "ff_aac_sbr_apply.L7090_1" := rfl
theorem L7090_2 : labelList[75]? = some "ff_aac_sbr_apply.L7090_2" := rfl
theorem L70bf : labelList[76]? = some "ff_aac_sbr_apply.L70bf" := rfl
theorem L70ca : labelList[77]? = some "ff_aac_sbr_apply.L70ca" := rfl
theorem L70ca_1 : labelList[78]? = some "ff_aac_sbr_apply.L70ca_1" := rfl
theorem L7120 : labelList[79]? = some "ff_aac_sbr_apply.L7120" := rfl
theorem L7140 : labelList[80]? = some "ff_aac_sbr_apply.L7140" := rfl
theorem L7166 : labelList[81]? = some "ff_aac_sbr_apply.L7166" := rfl
theorem L717f : labelList[82]? = some "ff_aac_sbr_apply.L717f" := rfl
theorem L71b0 : labelList[83]? = some "ff_aac_sbr_apply.L71b0" := rfl
theorem L71e0 : labelList[84]? = some "ff_aac_sbr_apply.L71e0" := rfl
theorem L71e0_1 : labelList[85]? = some "ff_aac_sbr_apply.L71e0_1" := rfl
theorem L7226 : labelList[86]? = some "ff_aac_sbr_apply.L7226" := rfl
theorem L723c : labelList[87]? = some "ff_aac_sbr_apply.L723c" := rfl
theorem L723c_1 : labelList[88]? = some "ff_aac_sbr_apply.L723c_1" := rfl
theorem L7270 : labelList[89]? = some "ff_aac_sbr_apply.L7270" := rfl
theorem L7286 : labelList[90]? = some "ff_aac_sbr_apply.L7286" := rfl
theorem L7286_1 : labelList[91]? = some "ff_aac_sbr_apply.L7286_1" := rfl
theorem L72ba : labelList[92]? = some "ff_aac_sbr_apply.L72ba" := rfl
theorem L72d0 : labelList[93]? = some "ff_aac_sbr_apply.L72d0" := rfl
theorem L72d0_1 : labelList[94]? = some "ff_aac_sbr_apply.L72d0_1" := rfl
theorem L7304 : labelList[95]? = some "ff_aac_sbr_apply.L7304" := rfl
theorem L731a : labelList[96]? = some "ff_aac_sbr_apply.L731a" := rfl
theorem L731a_1 : labelList[97]? = some "ff_aac_sbr_apply.L731a_1" := rfl
theorem L734a : labelList[98]? = some "ff_aac_sbr_apply.L734a" := rfl
theorem L7360 : labelList[99]? = some "ff_aac_sbr_apply.L7360" := rfl
theorem L7370 : labelList[100]? = some "ff_aac_sbr_apply.L7370" := rfl
theorem L73a1 : labelList[101]? = some "ff_aac_sbr_apply.L73a1" := rfl
theorem L73b7 : labelList[102]? = some "ff_aac_sbr_apply.L73b7" := rfl
theorem L73b7_1 : labelList[103]? = some "ff_aac_sbr_apply.L73b7_1" := rfl
theorem L73eb : labelList[104]? = some "ff_aac_sbr_apply.L73eb" := rfl
theorem L7401 : labelList[105]? = some "ff_aac_sbr_apply.L7401" := rfl
theorem L7401_1 : labelList[106]? = some "ff_aac_sbr_apply.L7401_1" := rfl
theorem L7435 : labelList[107]? = some "ff_aac_sbr_apply.L7435" := rfl
theorem L744b : labelList[108]? = some "ff_aac_sbr_apply.L744b" := rfl
theorem L744b_1 : labelList[109]? = some "ff_aac_sbr_apply.L744b_1" := rfl
theorem L747f : labelList[110]? = some "ff_aac_sbr_apply.L747f" := rfl
theorem L7495 : labelList[111]? = some "ff_aac_sbr_apply.L7495" := rfl
theorem L7495_1 : labelList[112]? = some "ff_aac_sbr_apply.L7495_1" := rfl
theorem L74de : labelList[113]? = some "ff_aac_sbr_apply.L74de" := rfl
theorem L74e9 : labelList[114]? = some "ff_aac_sbr_apply.L74e9" := rfl
theorem L74e9_1 : labelList[115]? = some "ff_aac_sbr_apply.L74e9_1" := rfl
theorem L74e9_2 : labelList[116]? = some "ff_aac_sbr_apply.L74e9_2" := rfl
theorem L74e9_3 : labelList[117]? = some "ff_aac_sbr_apply.L74e9_3" := rfl
theorem L74e9_4 : labelList[118]? = some "ff_aac_sbr_apply.L74e9_4" := rfl
theorem L7682 : labelList[119]? = some "ff_aac_sbr_apply.L7682" := rfl
theorem L7682_1 : labelList[120]? = some "ff_aac_sbr_apply.L7682_1" := rfl
theorem L7682_2 : labelList[121]? = some "ff_aac_sbr_apply.L7682_2" := rfl
theorem L7682_3 : labelList[122]? = some "ff_aac_sbr_apply.L7682_3" := rfl
theorem L7682_4 : labelList[123]? = some "ff_aac_sbr_apply.L7682_4" := rfl
theorem L7682_5 : labelList[124]? = some "ff_aac_sbr_apply.L7682_5" := rfl
theorem L7682_6 : labelList[125]? = some "ff_aac_sbr_apply.L7682_6" := rfl
theorem L7682_7 : labelList[126]? = some "ff_aac_sbr_apply.L7682_7" := rfl
theorem L7682_8 : labelList[127]? = some "ff_aac_sbr_apply.L7682_8" := rfl
theorem L7750 : labelList[128]? = some "ff_aac_sbr_apply.L7750" := rfl
theorem L7750_1 : labelList[129]? = some "ff_aac_sbr_apply.L7750_1" := rfl
theorem L7750_2 : labelList[130]? = some "ff_aac_sbr_apply.L7750_2" := rfl
theorem L7750_3 : labelList[131]? = some "ff_aac_sbr_apply.L7750_3" := rfl
theorem L7750_4 : labelList[132]? = some "ff_aac_sbr_apply.L7750_4" := rfl
theorem L7750_5 : labelList[133]? = some "ff_aac_sbr_apply.L7750_5" := rfl
theorem L7750_6 : labelList[134]? = some "ff_aac_sbr_apply.L7750_6" := rfl
theorem L7750_7 : labelList[135]? = some "ff_aac_sbr_apply.L7750_7" := rfl
theorem L7750_8 : labelList[136]? = some "ff_aac_sbr_apply.L7750_8" := rfl
theorem L7866 : labelList[137]? = some "ff_aac_sbr_apply.L7866" := rfl
theorem L7884 : labelList[138]? = some "ff_aac_sbr_apply.L7884" := rfl
theorem L7884_1 : labelList[139]? = some "ff_aac_sbr_apply.L7884_1" := rfl
theorem L78f2 : labelList[140]? = some "ff_aac_sbr_apply.L78f2" := rfl
theorem L7910 : labelList[141]? = some "ff_aac_sbr_apply.L7910" := rfl
theorem L7910_1 : labelList[142]? = some "ff_aac_sbr_apply.L7910_1" := rfl
theorem L797e : labelList[143]? = some "ff_aac_sbr_apply.L797e" := rfl
theorem L799c : labelList[144]? = some "ff_aac_sbr_apply.L799c" := rfl
theorem L799c_1 : labelList[145]? = some "ff_aac_sbr_apply.L799c_1" := rfl
theorem L7a0a : labelList[146]? = some "ff_aac_sbr_apply.L7a0a" := rfl
theorem L7a28 : labelList[147]? = some "ff_aac_sbr_apply.L7a28" := rfl
theorem L7a28_1 : labelList[148]? = some "ff_aac_sbr_apply.L7a28_1" := rfl
theorem L7a96 : labelList[149]? = some "ff_aac_sbr_apply.L7a96" := rfl
theorem L7ab4 : labelList[150]? = some "ff_aac_sbr_apply.L7ab4" := rfl
theorem L7b00 : labelList[151]? = some "ff_aac_sbr_apply.L7b00" := rfl
theorem L7b00_1 : labelList[152]? = some "ff_aac_sbr_apply.L7b00_1" := rfl
theorem L7b2d : labelList[153]? = some "ff_aac_sbr_apply.L7b2d" := rfl
theorem L7b50 : labelList[154]? = some "ff_aac_sbr_apply.L7b50" := rfl
theorem L7b80 : labelList[155]? = some "ff_aac_sbr_apply.L7b80" := rfl
theorem L7bb0 : labelList[156]? = some "ff_aac_sbr_apply.L7bb0" := rfl
theorem L7bb3 : labelList[157]? = some "ff_aac_sbr_apply.L7bb3" := rfl
theorem L7bb3_1 : labelList[158]? = some "ff_aac_sbr_apply.L7bb3_1" := rfl
theorem L7bb3_2 : labelList[159]? = some "ff_aac_sbr_apply.L7bb3_2" := rfl
theorem L7c5d : labelList[160]? = some "ff_aac_sbr_apply.L7c5d" := rfl
theorem L7c80 : labelList[161]? = some "ff_aac_sbr_apply.L7c80" := rfl
theorem L7c80_1 : labelList[162]? = some "ff_aac_sbr_apply.L7c80_1" := rfl
theorem L7cb0 : labelList[163]? = some "ff_aac_sbr_apply.L7cb0" := rfl
theorem L7cbf : labelList[164]? = some "ff_aac_sbr_apply.L7cbf" := rfl
theorem L7ce0 : labelList[165]? = some "ff_aac_sbr_apply.L7ce0" := rfl
theorem L7ce4 : labelList[166]? = some "ff_aac_sbr_apply.L7ce4" := rfl
theorem L7ce4_1 : labelList[167]? = some "ff_aac_sbr_apply.L7ce4_1" := rfl
theorem L7ce4_2 : labelList[168]? = some "ff_aac_sbr_apply.L7ce4_2" := rfl
theorem L7ce4_3 : labelList[169]? = some "ff_aac_sbr_apply.L7ce4_3" := rfl
theorem L7ce4_4 : labelList[170]? = some "ff_aac_sbr_apply.L7ce4_4" := rfl
theorem L7ce4_5 : labelList[171]? = some "ff_aac_sbr_apply.L7ce4_5" := rfl
theorem L7db0 : labelList[172]? = some "ff_aac_sbr_apply.L7db0" := rfl
theorem L7db0_1 : labelList[173]? = some "ff_aac_sbr_apply.L7db0_1" := rfl
theorem L7e20 : labelList[174]? = some "ff_aac_sbr_apply.L7e20" := rfl
theorem L7e29 : labelList[175]? = some "ff_aac_sbr_apply.L7e29" := rfl
theorem L7e60 : labelList[176]? = some "ff_aac_sbr_apply.L7e60" := rfl
theorem L7e60_1 : labelList[177]? = some "ff_aac_sbr_apply.L7e60_1" := rfl
theorem L7e90 : labelList[178]? = some "ff_aac_sbr_apply.L7e90" := rfl
theorem L7e90_1 : labelList[179]? = some "ff_aac_sbr_apply.L7e90_1" := rfl
theorem L7eb6 : labelList[180]? = some "ff_aac_sbr_apply.L7eb6" := rfl
theorem L7eb6_1 : labelList[181]? = some "ff_aac_sbr_apply.L7eb6_1" := rfl
theorem L7f10 : labelList[182]? = some "ff_aac_sbr_apply.L7f10" := rfl
theorem L7f36 : labelList[183]? = some "ff_aac_sbr_apply.L7f36" := rfl
theorem L7f36_1 : labelList[184]? = some "ff_aac_sbr_apply.L7f36_1" := rfl
theorem L7f80 : labelList[185]? = some "ff_aac_sbr_apply.L7f80" := rfl
theorem L7f80_1 : labelList[186]? = some "ff_aac_sbr_apply.L7f80_1" := rfl
theorem L8009 : labelList[187]? = some "ff_aac_sbr_apply.L8009" := rfl
theorem L8050 : labelList[188]? = some "ff_aac_sbr_apply.L8050" := rfl
theorem L8077 : labelList[189]? = some "ff_aac_sbr_apply.L8077" := rfl
theorem L8077_1 : labelList[190]? = some "ff_aac_sbr_apply.L8077_1" := rfl
theorem L80c0 : labelList[191]? = some "ff_aac_sbr_apply.L80c0" := rfl
theorem L80c0_1 : labelList[192]? = some "ff_aac_sbr_apply.L80c0_1" := rfl
theorem L814a : labelList[193]? = some "ff_aac_sbr_apply.L814a" := rfl
theorem L8190 : labelList[194]? = some "ff_aac_sbr_apply.L8190" := rfl
theorem L81b7 : labelList[195]? = some "ff_aac_sbr_apply.L81b7" := rfl
theorem L81b7_1 : labelList[196]? = some "ff_aac_sbr_apply.L81b7_1" := rfl
theorem L8200 : labelList[197]? = some "ff_aac_sbr_apply.L8200" := rfl
theorem L8200_1 : labelList[198]? = some "ff_aac_sbr_apply.L8200_1" := rfl
theorem L828a : labelList[199]? = some "ff_aac_sbr_apply.L828a" := rfl
theorem L82d0 : labelList[200]? = some "ff_aac_sbr_apply.L82d0" := rfl
theorem L82f7 : labelList[201]? = some "ff_aac_sbr_apply.L82f7" := rfl
theorem L82f7_1 : labelList[202]? = some "ff_aac_sbr_apply.L82f7_1" := rfl
theorem L8340 : labelList[203]? = some "ff_aac_sbr_apply.L8340" := rfl
theorem L8340_1 : labelList[204]? = some "ff_aac_sbr_apply.L8340_1" := rfl
theorem L83ca : labelList[205]? = some "ff_aac_sbr_apply.L83ca" := rfl
theorem L8410 : labelList[206]? = some "ff_aac_sbr_apply.L8410" := rfl
theorem L8437 : labelList[207]? = some "ff_aac_sbr_apply.L8437" := rfl
theorem L8437_1 : labelList[208]? = some "ff_aac_sbr_apply.L8437_1" := rfl
theorem L8480 : labelList[209]? = some "ff_aac_sbr_apply.L8480" := rfl
theorem L8480_1 : labelList[210]? = some "ff_aac_sbr_apply.L8480_1" := rfl
theorem L8509 : labelList[211]? = some "ff_aac_sbr_apply.L8509" := rfl
theorem L8520 : labelList[212]? = some "ff_aac_sbr_apply.L8520" := rfl
theorem L8570 : labelList[213]? = some "ff_aac_sbr_apply.L8570" := rfl
theorem L8570_1 : labelList[214]? = some "ff_aac_sbr_apply.L8570_1" := rfl
theorem L85c0 : labelList[215]? = some "ff_aac_sbr_apply.L85c0" := rfl
theorem L85cd : labelList[216]? = some "ff_aac_sbr_apply.L85cd" := rfl
theorem L85cd_1 : labelList[217]? = some "ff_aac_sbr_apply.L85cd_1" := rfl
theorem L85cd_2 : labelList[218]? = some "ff_aac_sbr_apply.L85cd_2" := rfl
theorem L8620 : labelList[219]? = some "ff_aac_sbr_apply.L8620" := rfl
theorem L862d : labelList[220]? = some "ff_aac_sbr_apply.L862d" := rfl
theorem L862d_1 : labelList[221]? = some "ff_aac_sbr_apply.L862d_1" := rfl
theorem L8660 : labelList[222]? = some "ff_aac_sbr_apply.L8660" := rfl
theorem L86a0 : labelList[223]? = some "ff_aac_sbr_apply.L86a0" := rfl
theorem L86b0 : labelList[224]? = some "ff_aac_sbr_apply.L86b0" := rfl
theorem L86b0_1 : labelList[225]? = some "ff_aac_sbr_apply.L86b0_1" := rfl
theorem L86d7 : labelList[226]? = some "ff_aac_sbr_apply.L86d7" := rfl
theorem L8700 : labelList[227]? = some "ff_aac_sbr_apply.L8700" := rfl
theorem L8720 : labelList[228]? = some "ff_aac_sbr_apply.L8720" := rfl
theorem L8740 : labelList[229]? = some "ff_aac_sbr_apply.L8740" := rfl
theorem L8740_1 : labelList[230]? = some "ff_aac_sbr_apply.L8740_1" := rfl
theorem L8790 : labelList[231]? = some "ff_aac_sbr_apply.L8790" := rfl
theorem L879e : labelList[232]? = some "ff_aac_sbr_apply.L879e" := rfl
theorem L879e_1 : labelList[233]? = some "ff_aac_sbr_apply.L879e_1" := rfl
theorem L879e_2 : labelList[234]? = some "ff_aac_sbr_apply.L879e_2" := rfl
theorem L8818 : labelList[235]? = some "ff_aac_sbr_apply.L8818" := rfl
theorem L881c : labelList[236]? = some "ff_aac_sbr_apply.L881c" := rfl
theorem L881c_1 : labelList[237]? = some "ff_aac_sbr_apply.L881c_1" := rfl
theorem L881c_2 : labelList[238]? = some "ff_aac_sbr_apply.L881c_2" := rfl
theorem L881c_3 : labelList[239]? = some "ff_aac_sbr_apply.L881c_3" := rfl
theorem L881c_4 : labelList[240]? = some "ff_aac_sbr_apply.L881c_4" := rfl
theorem L8900 : labelList[241]? = some "ff_aac_sbr_apply.L8900" := rfl
theorem L8900_1 : labelList[242]? = some "ff_aac_sbr_apply.L8900_1" := rfl
theorem L8900_2 : labelList[243]? = some "ff_aac_sbr_apply.L8900_2" := rfl
theorem L8947 : labelList[244]? = some "ff_aac_sbr_apply.L8947" := rfl
theorem L8947_1 : labelList[245]? = some "ff_aac_sbr_apply.L8947_1" := rfl
theorem L8970 : labelList[246]? = some "ff_aac_sbr_apply.L8970" := rfl
theorem L8970_1 : labelList[247]? = some "ff_aac_sbr_apply.L8970_1" := rfl
theorem L89e0 : labelList[248]? = some "ff_aac_sbr_apply.L89e0" := rfl
theorem L89f3 : labelList[249]? = some "ff_aac_sbr_apply.L89f3" := rfl
theorem L89f3_1 : labelList[250]? = some "ff_aac_sbr_apply.L89f3_1" := rfl
theorem L8a50 : labelList[251]? = some "ff_aac_sbr_apply.L8a50" := rfl
theorem L8a50_1 : labelList[252]? = some "ff_aac_sbr_apply.L8a50_1" := rfl
theorem L8a50_2 : labelList[253]? = some "ff_aac_sbr_apply.L8a50_2" := rfl
theorem L8a50_3 : labelList[254]? = some "ff_aac_sbr_apply.L8a50_3" := rfl
theorem L8ad0 : labelList[255]? = some "ff_aac_sbr_apply.L8ad0" := rfl
theorem L8ad0_1 : labelList[256]? = some "ff_aac_sbr_apply.L8ad0_1" := rfl
theorem L8b00 : labelList[257]? = some "ff_aac_sbr_apply.L8b00" := rfl
theorem L8b2a : labelList[258]? = some "ff_aac_sbr_apply.L8b2a" := rfl
theorem L8b4f : labelList[259]? = some "ff_aac_sbr_apply.L8b4f" := rfl
theorem L8b6b : labelList[260]? = some "ff_aac_sbr_apply.L8b6b" := rfl
theorem L8b77 : labelList[261]? = some "ff_aac_sbr_apply.L8b77" := rfl
theorem L8b77_1 : labelList[262]? = some "ff_aac_sbr_apply.L8b77_1" := rfl
theorem L8b77_2 : labelList[263]? = some "ff_aac_sbr_apply.L8b77_2" := rfl
theorem L8bf0 : labelList[264]? = some "ff_aac_sbr_apply.L8bf0" := rfl
theorem L8bf0_1 : labelList[265]? = some "ff_aac_sbr_apply.L8bf0_1" := rfl
theorem L8bf0_2 : labelList[266]? = some "ff_aac_sbr_apply.L8bf0_2" := rfl
theorem L8c33 : labelList[267]? = some "ff_aac_sbr_apply.L8c33" := rfl
theorem L8c4c : labelList[268]? = some "ff_aac_sbr_apply.L8c4c" := rfl
theorem L8c4c_1 : labelList[269]? = some "ff_aac_sbr_apply.L8c4c_1" := rfl
theorem L8c4c_2 : labelList[270]? = some "ff_aac_sbr_apply.L8c4c_2" := rfl
theorem L8cc9 : labelList[271]? = some "ff_aac_sbr_apply.L8cc9" := rfl
theorem L8cc9_1 : labelList[272]? = some "ff_aac_sbr_apply.L8cc9_1" := rfl
theorem L8cc9_2 : labelList[273]? = some "ff_aac_sbr_apply.L8cc9_2" := rfl
theorem L8d0c : labelList[274]? = some "ff_aac_sbr_apply.L8d0c" := rfl
theorem L8d26 : labelList[275]? = some "ff_aac_sbr_apply.L8d26" := rfl
theorem L8d26_1 : labelList[276]? = some "ff_aac_sbr_apply.L8d26_1" := rfl
theorem L8d26_2 : labelList[277]? = some "ff_aac_sbr_apply.L8d26_2" := rfl
theorem L8da3 : labelList[278]? = some "ff_aac_sbr_apply.L8da3" := rfl
theorem L8da3_1 : labelList[279]? = some "ff_aac_sbr_apply.L8da3_1" := rfl
theorem L8da3_2 : labelList[280]? = some "ff_aac_sbr_apply.L8da3_2" := rfl
theorem L8de6 : labelList[281]? = some "ff_aac_sbr_apply.L8de6" := rfl
theorem L8dff : labelList[282]? = some "ff_aac_sbr_apply.L8dff" := rfl
theorem L8dff_1 : labelList[283]? = some "ff_aac_sbr_apply.L8dff_1" := rfl
theorem L8dff_2 : labelList[284]? = some "ff_aac_sbr_apply.L8dff_2" := rfl
theorem L8e7c : labelList[285]? = some "ff_aac_sbr_apply.L8e7c" := rfl
theorem L8e7c_1 : labelList[286]? = some "ff_aac_sbr_apply.L8e7c_1" := rfl
theorem L8e7c_2 : labelList[287]? = some "ff_aac_sbr_apply.L8e7c_2" := rfl
theorem L8ebf : labelList[288]? = some "ff_aac_sbr_apply.L8ebf" := rfl
theorem L8ed9 : labelList[289]? = some "ff_aac_sbr_apply.L8ed9" := rfl
theorem L8ed9_1 : labelList[290]? = some "ff_aac_sbr_apply.L8ed9_1" := rfl
theorem L8ed9_2 : labelList[291]? = some "ff_aac_sbr_apply.L8ed9_2" := rfl
theorem L8f56 : labelList[292]? = some "ff_aac_sbr_apply.L8f56" := rfl
theorem L8f56_1 : labelList[293]? = some "ff_aac_sbr_apply.L8f56_1" := rfl
theorem L8f56_2 : labelList[294]? = some "ff_aac_sbr_apply.L8f56_2" := rfl
theorem L8f93 : labelList[295]? = some "ff_aac_sbr_apply.L8f93" := rfl
theorem L8fa4 : labelList[296]? = some "ff_aac_sbr_apply.L8fa4" := rfl
theorem L8fa4_1 : labelList[297]? = some "ff_aac_sbr_apply.L8fa4_1" := rfl
theorem L8fa4_2 : labelList[298]? = some "ff_aac_sbr_apply.L8fa4_2" := rfl
theorem L8fa4_3 : labelList[299]? = some "ff_aac_sbr_apply.L8fa4_3" := rfl
theorem L9026 : labelList[300]? = some "ff_aac_sbr_apply.L9026" := rfl
theorem L9026_1 : labelList[301]? = some "ff_aac_sbr_apply.L9026_1" := rfl
theorem L9026_2 : labelList[302]? = some "ff_aac_sbr_apply.L9026_2" := rfl
theorem L9063 : labelList[303]? = some "ff_aac_sbr_apply.L9063" := rfl
theorem L9070 : labelList[304]? = some "ff_aac_sbr_apply.L9070" := rfl
theorem L907f : labelList[305]? = some "ff_aac_sbr_apply.L907f" := rfl
theorem L907f_1 : labelList[306]? = some "ff_aac_sbr_apply.L907f_1" := rfl
theorem L907f_2 : labelList[307]? = some "ff_aac_sbr_apply.L907f_2" := rfl
theorem L907f_3 : labelList[308]? = some "ff_aac_sbr_apply.L907f_3" := rfl
theorem L90f9 : labelList[309]? = some "ff_aac_sbr_apply.L90f9" := rfl
theorem L90f9_1 : labelList[310]? = some "ff_aac_sbr_apply.L90f9_1" := rfl
theorem L90f9_2 : labelList[311]? = some "ff_aac_sbr_apply.L90f9_2" := rfl
theorem L913a : labelList[312]? = some "ff_aac_sbr_apply.L913a" := rfl
theorem L9146 : labelList[313]? = some "ff_aac_sbr_apply.L9146" := rfl
theorem L914e : labelList[314]? = some "ff_aac_sbr_apply.L914e" := rfl
theorem L914e_1 : labelList[315]? = some "ff_aac_sbr_apply.L914e_1" := rfl
theorem L914e_2 : labelList[316]? = some "ff_aac_sbr_apply.L914e_2" := rfl
theorem L914e_3 : labelList[317]? = some "ff_aac_sbr_apply.L914e_3" := rfl
theorem L91c0 : labelList[318]? = some "ff_aac_sbr_apply.L91c0" := rfl
theorem L91f7 : labelList[319]? = some "ff_aac_sbr_apply.L91f7" := rfl
theorem L9206 : labelList[320]? = some "ff_aac_sbr_apply.L9206" := rfl
theorem L9215 : labelList[321]? = some "ff_aac_sbr_apply.L9215" := rfl
theorem L9215_1 : labelList[322]? = some "ff_aac_sbr_apply.L9215_1" := rfl
theorem L9215_2 : labelList[323]? = some "ff_aac_sbr_apply.L9215_2" := rfl
theorem L9215_3 : labelList[324]? = some "ff_aac_sbr_apply.L9215_3" := rfl
theorem L9215_4 : labelList[325]? = some "ff_aac_sbr_apply.L9215_4" := rfl
theorem L9215_5 : labelList[326]? = some "ff_aac_sbr_apply.L9215_5" := rfl
theorem L9290 : labelList[327]? = some "ff_aac_sbr_apply.L9290" := rfl
theorem L929e : labelList[328]? = some "ff_aac_sbr_apply.L929e" := rfl
theorem L929e_1 : labelList[329]? = some "ff_aac_sbr_apply.L929e_1" := rfl
theorem L9300 : labelList[330]? = some "ff_aac_sbr_apply.L9300" := rfl
theorem L9300_1 : labelList[331]? = some "ff_aac_sbr_apply.L9300_1" := rfl
theorem L9300_2 : labelList[332]? = some "ff_aac_sbr_apply.L9300_2" := rfl
theorem L9370 : labelList[333]? = some "ff_aac_sbr_apply.L9370" := rfl
theorem L9386 : labelList[334]? = some "ff_aac_sbr_apply.L9386" := rfl
theorem L9386_1 : labelList[335]? = some "ff_aac_sbr_apply.L9386_1" := rfl
theorem L93d0 : labelList[336]? = some "ff_aac_sbr_apply.L93d0" := rfl
theorem L93f0 : labelList[337]? = some "ff_aac_sbr_apply.L93f0" := rfl
theorem L93f0_1 : labelList[338]? = some "ff_aac_sbr_apply.L93f0_1" := rfl
theorem L9440 : labelList[339]? = some "ff_aac_sbr_apply.L9440" := rfl
theorem L9458 : labelList[340]? = some "ff_aac_sbr_apply.L9458" := rfl
theorem L9470 : labelList[341]? = some "ff_aac_sbr_apply.L9470" := rfl
theorem L9470_1 : labelList[342]? = some "ff_aac_sbr_apply.L9470_1" := rfl
theorem L9504 : labelList[343]? = some "ff_aac_sbr_apply.L9504" := rfl
theorem L9520 : labelList[344]? = some "ff_aac_sbr_apply.L9520" := rfl
theorem L952c : labelList[345]? = some "ff_aac_sbr_apply.L952c" := rfl
theorem L9530 : labelList[346]? = some "ff_aac_sbr_apply.L9530" := rfl
theorem L9530_1 : labelList[347]? = some "ff_aac_sbr_apply.L9530_1" := rfl
theorem L95a0 : labelList[348]? = some "ff_aac_sbr_apply.L95a0" := rfl
theorem L95a0_1 : labelList[349]? = some "ff_aac_sbr_apply.L95a0_1" := rfl
theorem L95a0_2 : labelList[350]? = some "ff_aac_sbr_apply.L95a0_2" := rfl
theorem L9600 : labelList[351]? = some "ff_aac_sbr_apply.L9600" := rfl
theorem L9617 : labelList[352]? = some "ff_aac_sbr_apply.L9617" := rfl
theorem L9617_1 : labelList[353]? = some "ff_aac_sbr_apply.L9617_1" := rfl
theorem L968d : labelList[354]? = some "ff_aac_sbr_apply.L968d" := rfl
theorem L96d3 : labelList[355]? = some "ff_aac_sbr_apply.L96d3" := rfl
theorem L96e1 : labelList[356]? = some "ff_aac_sbr_apply.L96e1" := rfl
theorem L9720 : labelList[357]? = some "ff_aac_sbr_apply.L9720" := rfl
theorem L9731 : labelList[358]? = some "ff_aac_sbr_apply.L9731" := rfl
theorem L9731_1 : labelList[359]? = some "ff_aac_sbr_apply.L9731_1" := rfl
theorem L97b7 : labelList[360]? = some "ff_aac_sbr_apply.L97b7" := rfl
theorem L97f0 : labelList[361]? = some "ff_aac_sbr_apply.L97f0" := rfl
theorem L9820 : labelList[362]? = some "ff_aac_sbr_apply.L9820" := rfl
theorem L983f : labelList[363]? = some "ff_aac_sbr_apply.L983f" := rfl
theorem L9860 : labelList[364]? = some "ff_aac_sbr_apply.L9860" := rfl
theorem L9860_1 : labelList[365]? = some "ff_aac_sbr_apply.L9860_1" := rfl
theorem L9860_2 : labelList[366]? = some "ff_aac_sbr_apply.L9860_2" := rfl
theorem L9860_3 : labelList[367]? = some "ff_aac_sbr_apply.L9860_3" := rfl
theorem L98bc : labelList[368]? = some "ff_aac_sbr_apply.L98bc" := rfl
theorem L98e0 : labelList[369]? = some "ff_aac_sbr_apply.L98e0" := rfl
theorem L9927 : labelList[370]? = some "ff_aac_sbr_apply.L9927" := rfl
theorem L9934 : labelList[371]? = some "ff_aac_sbr_apply.L9934" := rfl
theorem L9934_1 : labelList[372]? = some "ff_aac_sbr_apply.L9934_1" := rfl
theorem L9934_2 : labelList[373]? = some "ff_aac_sbr_apply.L9934_2" := rfl
theorem L99c6 : labelList[374]? = some "ff_aac_sbr_apply.L99c6" := rfl
theorem L99cf : labelList[375]? = some "ff_aac_sbr_apply.L99cf" := rfl
theorem L99e9 : labelList[376]? = some "ff_aac_sbr_apply.L99e9" := rfl
theorem L99ee : labelList[377]? = some "ff_aac_sbr_apply.L99ee" := rfl
theorem L99f3 : labelList[378]? = some "ff_aac_sbr_apply.L99f3" := rfl
theorem L99f8 : labelList[379]? = some "ff_aac_sbr_apply.L99f8" := rfl
theorem L99fd : labelList[380]? = some "ff_aac_sbr_apply.L99fd" := rfl
theorem L9a02 : labelList[381]? = some "ff_aac_sbr_apply.L9a02" := rfl
theorem L9a02_1 : labelList[382]? = some "ff_aac_sbr_apply.L9a02_1" := rfl
theorem L9a50 : labelList[383]? = some "ff_aac_sbr_apply.L9a50" := rfl
theorem L9a55 : labelList[384]? = some "ff_aac_sbr_apply.L9a55" := rfl
theorem L9a5a : labelList[385]? = some "ff_aac_sbr_apply.L9a5a" := rfl
theorem L9a5f : labelList[386]? = some "ff_aac_sbr_apply.L9a5f" := rfl
theorem L9a64 : labelList[387]? = some "ff_aac_sbr_apply.L9a64" := rfl
theorem L9a69 : labelList[388]? = some "ff_aac_sbr_apply.L9a69" := rfl
theorem L9a7d : labelList[389]? = some "ff_aac_sbr_apply.L9a7d" := rfl
theorem L9a85 : labelList[390]? = some "ff_aac_sbr_apply.L9a85" := rfl
theorem L9a85_1 : labelList[391]? = some "ff_aac_sbr_apply.L9a85_1" := rfl
theorem L9a85_2 : labelList[392]? = some "ff_aac_sbr_apply.L9a85_2" := rfl
theorem L9a85_3 : labelList[393]? = some "ff_aac_sbr_apply.L9a85_3" := rfl
theorem L9a85_4 : labelList[394]? = some "ff_aac_sbr_apply.L9a85_4" := rfl
theorem L9b24 : labelList[395]? = some "ff_aac_sbr_apply.L9b24" := rfl
theorem L9b2b : labelList[396]? = some "ff_aac_sbr_apply.L9b2b" := rfl
theorem done : labelList[397]? = some "ff_aac_sbr_apply.done" := rfl
theorem L9b36 : labelList[398]? = some "ff_aac_sbr_apply.L9b36" := rfl
theorem L9b3b : labelList[399]? = some "ff_aac_sbr_apply.L9b3b" := rfl
theorem L9b40 : labelList[400]? = some "ff_aac_sbr_apply.L9b40" := rfl
theorem L9b45 : labelList[401]? = some "ff_aac_sbr_apply.L9b45" := rfl
theorem L9b4a : labelList[402]? = some "ff_aac_sbr_apply.L9b4a" := rfl
theorem L9b4f : labelList[403]? = some "ff_aac_sbr_apply.L9b4f" := rfl
theorem L9b54 : labelList[404]? = some "ff_aac_sbr_apply.L9b54" := rfl
theorem L9b59 : labelList[405]? = some "ff_aac_sbr_apply.L9b59" := rfl
theorem L9b5e : labelList[406]? = some "ff_aac_sbr_apply.L9b5e" := rfl
theorem L9b63 : labelList[407]? = some "ff_aac_sbr_apply.L9b63" := rfl
theorem L9b68 : labelList[408]? = some "ff_aac_sbr_apply.L9b68" := rfl
theorem L9b6d : labelList[409]? = some "ff_aac_sbr_apply.L9b6d" := rfl
theorem L9b72 : labelList[410]? = some "ff_aac_sbr_apply.L9b72" := rfl
theorem L9b77 : labelList[411]? = some "ff_aac_sbr_apply.L9b77" := rfl
theorem L9b7c : labelList[412]? = some "ff_aac_sbr_apply.L9b7c" := rfl
theorem L9b81 : labelList[413]? = some "ff_aac_sbr_apply.L9b81" := rfl
theorem L9b86 : labelList[414]? = some "ff_aac_sbr_apply.L9b86" := rfl
theorem L9b8b : labelList[415]? = some "ff_aac_sbr_apply.L9b8b" := rfl
theorem L9b90 : labelList[416]? = some "ff_aac_sbr_apply.L9b90" := rfl
theorem L9b95 : labelList[417]? = some "ff_aac_sbr_apply.L9b95" := rfl
theorem L9b9a : labelList[418]? = some "ff_aac_sbr_apply.L9b9a" := rfl
theorem L9b9a_1 : labelList[419]? = some "ff_aac_sbr_apply.L9b9a_1" := rfl
theorem L9bc5 : labelList[420]? = some "ff_aac_sbr_apply.L9bc5" := rfl
theorem L9bca : labelList[421]? = some "ff_aac_sbr_apply.L9bca" := rfl
theorem L9bcf : labelList[422]? = some "ff_aac_sbr_apply.L9bcf" := rfl
theorem L9bd4 : labelList[423]? = some "ff_aac_sbr_apply.L9bd4" := rfl
theorem L9bd4_1 : labelList[424]? = some "ff_aac_sbr_apply.L9bd4_1" := rfl
theorem L9bff : labelList[425]? = some "ff_aac_sbr_apply.L9bff" := rfl
theorem L9c04 : labelList[426]? = some "ff_aac_sbr_apply.L9c04" := rfl
theorem L9c09 : labelList[427]? = some "ff_aac_sbr_apply.L9c09" := rfl
theorem L9c0e : labelList[428]? = some "ff_aac_sbr_apply.L9c0e" := rfl
theorem L9c13 : labelList[429]? = some "ff_aac_sbr_apply.L9c13" := rfl
theorem L9c18 : labelList[430]? = some "ff_aac_sbr_apply.L9c18" := rfl
theorem L9c1d : labelList[431]? = some "ff_aac_sbr_apply.L9c1d" := rfl
theorem L9c22 : labelList[432]? = some "ff_aac_sbr_apply.L9c22" := rfl
theorem L9c27 : labelList[433]? = some "ff_aac_sbr_apply.L9c27" := rfl
end L


/-! ## Frame lemmas -/

omit [CodeEnv] in
/-- The reservation at entry: the callees' area below the frame, the own slot area,
the six saved-register slots (`hW`: the entry's headroom, `CallPre.le`). -/
theorem reserve_frame (k : Nat) {r : BitVec 64} (hW : 0x460 + k ≤ r.toNat) (K : Mem 64 → Prop) :
    Reserve (0x460 + k) r ⋆ K
      = Reserve (0x298 + k) (r - 0x1c8#64) ⋆ (0x198 ?@ (r - 0x1c8#64) ⋆ (8 ?@ (r - 0x30#64)
        ⋆ (8 ?@ (r - 0x28#64) ⋆ (8 ?@ (r - 0x20#64) ⋆ (8 ?@ (r - 0x18#64)
        ⋆ (8 ?@ (r - 0x10#64) ⋆ (8 ?@ (r - 0x8#64) ⋆ K))))))) := by
  rw [show 0x460 + k = 0x1c8 + (0x298 + k) by omega, Reserve_split 0x1c8 (0x298 + k) r (by omega)]
  rw [show (0x1c8 ?@ (r - BitVec.ofNat 64 0x1c8) : Mem 64 → Prop) = (0x198 + 0x30) ?@ (r - 0x1c8#64) from rfl,
    Block.split (r - 0x1c8#64) 0x198 0x30 (by decide), show r - 0x1c8#64 + BitVec.ofNat 64 0x198 = r - 0x30#64 by bv_omega]
  rw [show (0x30 ?@ (r - 0x30#64) : Mem 64 → Prop) = (8 + 0x28) ?@ (r - 0x30#64) from rfl,
    Block.split (r - 0x30#64) 8 0x28 (by decide), show r - 0x30#64 + BitVec.ofNat 64 8 = r - 0x28#64 by bv_omega]
  rw [show (0x28 ?@ (r - 0x28#64) : Mem 64 → Prop) = (8 + 0x20) ?@ (r - 0x28#64) from rfl,
    Block.split (r - 0x28#64) 8 0x20 (by decide), show r - 0x28#64 + BitVec.ofNat 64 8 = r - 0x20#64 by bv_omega]
  rw [show (0x20 ?@ (r - 0x20#64) : Mem 64 → Prop) = (8 + 0x18) ?@ (r - 0x20#64) from rfl,
    Block.split (r - 0x20#64) 8 0x18 (by decide), show r - 0x20#64 + BitVec.ofNat 64 8 = r - 0x18#64 by bv_omega]
  rw [show (0x18 ?@ (r - 0x18#64) : Mem 64 → Prop) = (8 + 0x10) ?@ (r - 0x18#64) from rfl,
    Block.split (r - 0x18#64) 8 0x10 (by decide), show r - 0x18#64 + BitVec.ofNat 64 8 = r - 0x10#64 by bv_omega]
  rw [show (0x10 ?@ (r - 0x10#64) : Mem 64 → Prop) = (8 + 8) ?@ (r - 0x10#64) from rfl,
    Block.split (r - 0x10#64) 8 8 (by decide), show r - 0x10#64 + BitVec.ofNat 64 8 = r - 0x8#64 by bv_omega]
  simp only [Std.ExtHashMap.sep_assoc]
  rw [Std.ExtHashMap.sep_comm_l (8 ?@ (r - 0x8#64)) (Reserve (0x298 + k) (r - 0x1c8#64)),
    Std.ExtHashMap.sep_comm_l (8 ?@ (r - 0x10#64)) (Reserve (0x298 + k) (r - 0x1c8#64)),
    Std.ExtHashMap.sep_comm_l (8 ?@ (r - 0x18#64)) (Reserve (0x298 + k) (r - 0x1c8#64)),
    Std.ExtHashMap.sep_comm_l (8 ?@ (r - 0x20#64)) (Reserve (0x298 + k) (r - 0x1c8#64)),
    Std.ExtHashMap.sep_comm_l (8 ?@ (r - 0x28#64)) (Reserve (0x298 + k) (r - 0x1c8#64)),
    Std.ExtHashMap.sep_comm_l (8 ?@ (r - 0x30#64)) (Reserve (0x298 + k) (r - 0x1c8#64)),
    Std.ExtHashMap.sep_comm_l (0x198 ?@ (r - 0x1c8#64)) (Reserve (0x298 + k) (r - 0x1c8#64))]

omit [CodeEnv] in
/-- A call's share of the callees' area: the push slot, the callee's `k`, the rest
(`sbr_qmf_synthesis`'s stack arguments and slack) below. -/
theorem call_res (k : Nat) {r₀ : BitVec 64} (hW : 0x460 + k ≤ r₀.toNat) (K : Mem 64 → Prop) :
    Reserve (0x298 + k) (r₀ - 0x1c8#64) ⋆ K
      = 8 ?@ (r₀ - 0x1c8#64 - 8#64) ⋆ (Reserve k (r₀ - 0x1c8#64 - 8#64)
        ⋆ (0x290 ?@ (r₀ - 0x1c8#64 - BitVec.ofNat 64 (0x298 + k)) ⋆ K)) := by
  have hr : 0x298 + k ≤ (r₀ - 0x1c8#64).toNat := by bv_omega
  generalize r₀ - 0x1c8#64 = r at hr ⊢
  rw [show 0x298 + k = 8 + (k + 0x290) by omega, Reserve_split 8 (k + 0x290) r (by omega),
    Reserve.excess k (k + 0x290) (r - BitVec.ofNat 64 8) (by omega) (by bv_omega),
    Nat.add_sub_cancel_left, BitVec.sub_sub_ofNat]
  simp only [Std.ExtHashMap.sep_assoc]

omit [CodeEnv] in
/-- A callee's reservation of `k` below the push slot as none and the `k` bytes. -/
theorem res_k0 {k : Nat} {r₀ : BitVec 64} (hW : 0x460 + k ≤ r₀.toNat) :
    Reserve k (r₀ - 464#64)
      = Reserve 0 (r₀ - 464#64) ⋆ (k - 0) ?@ (r₀ - 464#64 - BitVec.ofNat 64 k) :=
  Reserve.excess 0 k _ (Nat.zero_le _) (by bv_omega)


section OmegaSafeSec
/-! `omega_safe`: `omega`, except that it first refuses, immediately and with a message, any goal
whose target or hypotheses contain `t % m` where `m ≥ 2^32` is a literal (`2^64`,
`18446744073709551616`, …) and `t` is not a literal. That shape (wrap-around facts of 64-bit sums)
is what made omega exhaust memory. Prove such facts as closed lemmas instead, using
`BitVec.toNat_add`/`toNat_ofNat` with explicit `< 2^64` hypotheses. -/

open Lean Meta Elab Tactic

namespace OmegaSafe

/-- A natural/integer literal: `OfNat.ofNat n`, a raw literal, or `a ^ b` of literals. -/
partial def lit? (e : Expr) : Option Nat :=
  match e.nat? with
  | some n => some n
  | none =>
    match e.int? with
    | some i => if 0 ≤ i then some i.toNat else none
    | none =>
      if let some n := e.rawNatLit? then some n
      else if e.isAppOfArity ``HPow.hPow 6 then
        match lit? (e.getArg! 4), lit? (e.getArg! 5) with
        | some a, some b => if b ≤ 128 then some (a ^ b) else none
        | _, _ => none
      else none

/-- The first subterm `t % m`, `m ≥ 2^32` literal, `t` non-literal. -/
def badMod? (e : Expr) : Option Expr :=
  e.find? fun s =>
    s.isAppOfArity ``HMod.hMod 6 &&
      (match lit? (s.getArg! 5) with
       | some m => decide (2 ^ 32 ≤ m) && (lit? (s.getArg! 4)).isNone
       | none => false)

/-- Throws if the main goal (target or a local hypothesis) contains a bad `%`. -/
def check : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let mut es : Array (Option Name × Expr) := #[(none, ← instantiateMVars (← g.getType))]
  for d in ← getLCtx do
    if !d.isImplementationDetail then
      es := es.push (some d.userName, ← instantiateMVars d.type)
  for (n, e) in es do
    if let some s := badMod? e then
      let w := match n with | some n => m!"hypothesis {n}" | none => m!"the goal"
      throwError "omega_safe: refusing, {w} contains the symbolic big modulus{indentExpr s}\n\
        (risk of omega memory blow-up; prove a closed lemma via BitVec.toNat_add/toNat_ofNat \
        with explicit `< 2^64` facts, or `clear` the hypothesis)"

end OmegaSafe

/-- `omega`, but fails fast on `t % 2^k` (k ≥ 32) with a symbolic `t` in the goal or context. -/
elab "omega_safe" : tactic => do
  OmegaSafe.check
  evalTactic (← `(tactic| omega))

end OmegaSafeSec

/-- The channel pair of `ApplyF` with channel `ch` first, so block proofs can keep `ch` symbolic
(no `ch = 0 ∨ ch = 1` split). Unifies the former `gn_dpair` (GainAsm), `an_dpair` (AnaHf/MapA clean)
and `applyF_dpair` (Env clean). -/
theorem applyF_dpair (y : Args) (t : MachineData) (ch : Nat) (h : ch < 2) (K : Mem 64 → Prop) :
    DScW y.d0 t 0 ⋆ (DScW y.d1 t 1 ⋆ (DArrW t 0 ⋆ (DArrW t 1 ⋆ K)))
      = DScW (y.d ch) t ch ⋆ (DArrW t ch ⋆ (DScW (y.d (1 - ch)) t (1 - ch) ⋆ (DArrW t (1 - ch) ⋆ K))) := by
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  · simp only [Args.d, ↓reduceIte, Nat.sub_zero, Nat.one_ne_zero]; ac_rfl
  · simp only [Args.d, ↓reduceIte, Nat.sub_self, Nat.one_ne_zero]; ac_rfl

/-! ## M4b per-object views (D1 layout, synthesis window) -/

omit [CodeEnv] in
/-- D1: the `DArrW` blocks `Y ++ g_temp[0][0..6)` (38936 bytes) and the rest of `g_temp`
(8040) as the objects `Y[0]`, `Y[1]` (19456 bytes each) and `g_temp` (8064). -/
theorem gtemp_rejoin (d : BitVec 64) (K : Mem 64 → Prop) :
    38936 ?@ (d + 0x7930#64) ⋆ (8040 ?@ (d + 0x11148#64) ⋆ K)
      = 19456 ?@ (d + 0x7930#64) ⋆ (19456 ?@ (d + 0xc530#64) ⋆ (8064 ?@ (d + 0x11130#64) ⋆ K)) := by
  have e1 := Block.split (d + 0x7930#64) 19456 19480 (by decide)
  have e2 := Block.split (d + 0xc530#64) 19456 24 (by decide)
  have e3 := Block.split (d + 0x11130#64) 24 8040 (by decide)
  simp only [BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceAdd] at e1 e2 e3
  rw [e1, e2, e3]
  simp only [Std.ExtHashMap.sep_assoc]

omit [CodeEnv] in
/-- `g_temp` and `q_temp` (8064 bytes each, contiguous) as one 16128-byte block. -/
theorem gq_rejoin (d : BitVec 64) (K : Mem 64 → Prop) :
    8064 ?@ (d + 0x11130#64) ⋆ (8064 ?@ (d + 0x130b0#64) ⋆ K) = 16128 ?@ (d + 0x11130#64) ⋆ K := by
  have e1 := Block.split (d + 0x11130#64) 8064 8064 (by decide)
  simp only [BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceAdd] at e1
  rw [e1]
  simp only [Std.ExtHashMap.sep_assoc]

omit [CodeEnv] in
/-- `synthesis_filterbank_samples` (9216 bytes at `d + 0x80`) and
`analysis_filterbank_samples` (5248 at `d + 0x2480`) as the larger `v0` window of
`sbr_qmf_synthesis` (11264 bytes at `d + 0x80`, see `qmfVSize`) and the rest of the analysis
buffer. -/
theorem a3_overread_carve (d : BitVec 64) (K : Mem 64 → Prop) :
    9216 ?@ (d + 0x80#64) ⋆ (5248 ?@ (d + 0x2480#64) ⋆ K)
      = 11264 ?@ (d + 0x80#64) ⋆ (3200 ?@ (d + 0x2c80#64) ⋆ K) := by
  have e1 := Block.split (d + 0x80#64) 9216 2048 (by decide)
  have e2 := Block.split (d + 0x2480#64) 2048 3200 (by decide)
  simp only [BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceAdd] at e1 e2
  rw [e1, e2]
  simp only [Std.ExtHashMap.sep_assoc]


/-! ## The variant (lexicographic: per loop level a phase and the loop's measure) -/

-- loops (text-index intervals): [(4, 60), (8, 60), (12, 25), (13, 24), (27, 57), (64, 112), (65, 112), (66, 111), (67, 100), (72, 83), (73, 82), (76, 82), (119, 375), (128, 133), (153, 160), (154, 159), (155, 155), (164, 259), (166, 259), (172, 230), (174, 177), (176, 177), (182, 182), (185, 186), (188, 188), (191, 192), (194, 194), (197, 198), (200, 200), (203, 204), (206, 206), (209, 210), (213, 221), (223, 228), (227, 227), (241, 243), (246, 257), (248, 256), (251, 253), (255, 256), (264, 266), (271, 273), (278, 280), (285, 287), (292, 294), (300, 302), (309, 311), (318, 368), (330, 335), (339, 339), (341, 342), (348, 350), (356, 361), (358, 361), (364, 367)]
namespace VD
/-- ff_aac_sbr_apply -/
abbrev start (s : MachineData) : List Nat := [3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.start_1 -/
abbrev start_1 (s : MachineData) : List Nat := [3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.start_2 -/
abbrev start_2 (s : MachineData) : List Nat := [3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.start_3 -/
abbrev start_3 (s : MachineData) : List Nat := [3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L676e -/
abbrev L676e (s : MachineData) : List Nat := [2, (0), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L6797 -/
abbrev L6797 (s : MachineData) : List Nat := [2, (1), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L6797_1 -/
abbrev L6797_1 (s : MachineData) : List Nat := [2, (1), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L6817 -/
abbrev L6817 (s : MachineData) : List Nat := [2, (1), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L6825 -/
abbrev L6825 (s : MachineData) : List Nat := [2, (0), 0, (0), 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L6838 -/
abbrev L6838 (s : MachineData) : List Nat := [2, (0), 0, (0), 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L6838_1 -/
abbrev L6838_1 (s : MachineData) : List Nat := [2, (0), 0, (0), 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L6838_2 -/
abbrev L6838_2 (s : MachineData) : List Nat := [2, (0), 0, (0), 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L68b0 -/
abbrev L68b0 (s : MachineData) : List Nat := [2, (0), 0, (0), 1, (9 - (s.regs.get64 .rbx).toNat), 1, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L68d0 -/
abbrev L68d0 (s : MachineData) : List Nat := [2, (0), 0, (0), 1, (9 - (s.regs.get64 .rbx).toNat), 0, (2 * (48 - (s.regs.get64 .r14).toNat)), 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L68d0_1 -/
abbrev L68d0_1 (s : MachineData) : List Nat := [2, (0), 0, (0), 1, (9 - (s.regs.get64 .rbx).toNat), 0, (2 * (48 - (s.regs.get64 .r14).toNat)), 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L68f8 -/
abbrev L68f8 (s : MachineData) : List Nat := [2, (0), 0, (0), 1, (9 - (s.regs.get64 .rbx).toNat), 0, (2 * (48 - (s.regs.get64 .r14).toNat) + 1), 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L6940 -/
abbrev L6940 (s : MachineData) : List Nat := [2, (0), 0, (0), 1, (9 - (s.regs.get64 .rbx).toNat), 0, (2 * (48 - (s.regs.get64 .r14).toNat) + 1), 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L6940_1 -/
abbrev L6940_1 (s : MachineData) : List Nat := [2, (0), 0, (0), 1, (9 - (s.regs.get64 .rbx).toNat), 0, (2 * (48 - (s.regs.get64 .r14).toNat) + 1), 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L69a4 -/
abbrev L69a4 (s : MachineData) : List Nat := [2, (0), 0, (0), 1, (9 - (s.regs.get64 .rbx).toNat), 0, (2 * (48 - (s.regs.get64 .r14).toNat) + 1), 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L69d0 -/
abbrev L69d0 (s : MachineData) : List Nat := [2, (0), 0, (0), 1, (9 - (s.regs.get64 .rbx).toNat), 0, (2 * (48 - (s.regs.get64 .r14).toNat) + 1), 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L69dd -/
abbrev L69dd (s : MachineData) : List Nat := [2, (0), 0, (0), 1, (9 - (s.regs.get64 .rbx).toNat), 0, (2 * (48 - (s.regs.get64 .r14).toNat) + 1), 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L6a10 -/
abbrev L6a10 (s : MachineData) : List Nat := [2, (0), 0, (0), 1, (9 - (s.regs.get64 .rbx).toNat), 0, (2 * (48 - (s.regs.get64 .r14).toNat) + 1), 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L6a30 -/
abbrev L6a30 (s : MachineData) : List Nat := [2, (0), 0, (0), 1, (9 - (s.regs.get64 .rbx).toNat), 0, (2 * (48 - (s.regs.get64 .r14).toNat) + 1), 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L6a30_1 -/
abbrev L6a30_1 (s : MachineData) : List Nat := [2, (0), 0, (0), 1, (9 - (s.regs.get64 .rbx).toNat), 0, (2 * (48 - (s.regs.get64 .r14).toNat) + 1), 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L6a30_2 -/
abbrev L6a30_2 (s : MachineData) : List Nat := [2, (0), 0, (0), 1, (9 - (s.regs.get64 .rbx).toNat), 0, (2 * (48 - (s.regs.get64 .r14).toNat) + 1), 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L6a90 -/
abbrev L6a90 (s : MachineData) : List Nat := [2, (0), 0, (0), 1, (9 - (s.regs.get64 .rbx).toNat), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L6abf -/
abbrev L6abf (s : MachineData) : List Nat := [2, (0), 0, (0), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L6b00 -/
abbrev L6b00 (s : MachineData) : List Nat := [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat)), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L6b02 -/
abbrev L6b02 (s : MachineData) : List Nat := [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat)), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L6b12 -/
abbrev L6b12 (s : MachineData) : List Nat := [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L6b50 -/
abbrev L6b50 (s : MachineData) : List Nat := [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L6b6c -/
abbrev L6b6c (s : MachineData) : List Nat := [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L6ba0 -/
abbrev L6ba0 (s : MachineData) : List Nat := [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L6bbc -/
abbrev L6bbc (s : MachineData) : List Nat := [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L6bbc_1 -/
abbrev L6bbc_1 (s : MachineData) : List Nat := [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L6c1e -/
abbrev L6c1e (s : MachineData) : List Nat := [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L6c3a -/
abbrev L6c3a (s : MachineData) : List Nat := [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L6c61 -/
abbrev L6c61 (s : MachineData) : List Nat := [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L6c7d -/
abbrev L6c7d (s : MachineData) : List Nat := [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L6c7d_1 -/
abbrev L6c7d_1 (s : MachineData) : List Nat := [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L6c7d_2 -/
abbrev L6c7d_2 (s : MachineData) : List Nat := [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L6ce0 -/
abbrev L6ce0 (s : MachineData) : List Nat := [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L6cea -/
abbrev L6cea (s : MachineData) : List Nat := [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L6d09 -/
abbrev L6d09 (s : MachineData) : List Nat := [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L6d32 -/
abbrev L6d32 (s : MachineData) : List Nat := [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L6d51 -/
abbrev L6d51 (s : MachineData) : List Nat := [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L6d51_1 -/
abbrev L6d51_1 (s : MachineData) : List Nat := [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L6dbc -/
abbrev L6dbc (s : MachineData) : List Nat := [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L6ddb -/
abbrev L6ddb (s : MachineData) : List Nat := [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L6e04 -/
abbrev L6e04 (s : MachineData) : List Nat := [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L6e23 -/
abbrev L6e23 (s : MachineData) : List Nat := [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L6e23_1 -/
abbrev L6e23_1 (s : MachineData) : List Nat := [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L6e8c -/
abbrev L6e8c (s : MachineData) : List Nat := [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L6ea8 -/
abbrev L6ea8 (s : MachineData) : List Nat := [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L6ecf -/
abbrev L6ecf (s : MachineData) : List Nat := [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L6eeb -/
abbrev L6eeb (s : MachineData) : List Nat := [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L6eeb_1 -/
abbrev L6eeb_1 (s : MachineData) : List Nat := [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L6eeb_2 -/
abbrev L6eeb_2 (s : MachineData) : List Nat := [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L6f32 -/
abbrev L6f32 (s : MachineData) : List Nat := [2, (1), 0, (0), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L6f32_1 -/
abbrev L6f32_1 (s : MachineData) : List Nat := [2, (1), 0, (0), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L6f32_2 -/
abbrev L6f32_2 (s : MachineData) : List Nat := [2, (1), 0, (0), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L6fbe -/
abbrev L6fbe (s : MachineData) : List Nat := [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L6fca -/
abbrev L6fca (s : MachineData) : List Nat := [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L6ff7 -/
abbrev L6ff7 (s : MachineData) : List Nat := [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L6ffc -/
abbrev L6ffc (s : MachineData) : List Nat := [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 0), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7007 -/
abbrev L7007 (s : MachineData) : List Nat := [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 0), 0, (0), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L700e -/
abbrev L700e (s : MachineData) : List Nat := [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 0), 0, (0), 0, (0), 1, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7020 -/
abbrev L7020 (s : MachineData) : List Nat := [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 0), 0, (0), 0, (0), 0, (0), 1, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7020_1 -/
abbrev L7020_1 (s : MachineData) : List Nat := [1, ((if s.regs.get64 .rax = 1#64 then 4 else 0) + 3), 0, (0), 0, (0), 0, (0), 1, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7020_2 -/
abbrev L7020_2 (s : MachineData) : List Nat := [1, ((if s.regs.get64 .rax = 1#64 then 4 else 0) + 3), 0, (0), 0, (0), 0, (0), 1, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7044 -/
abbrev L7044 (s : MachineData) : List Nat := [1, ((if s.regs.get64 .rax = 0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 1, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7044_1 -/
abbrev L7044_1 (s : MachineData) : List Nat := [1, ((if s.regs.get64 .rax = 0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 1, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7070 -/
abbrev L7070 (s : MachineData) : List Nat := [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, (9 - (s.regs.get64 .r15).toNat), 1, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7090 -/
abbrev L7090 (s : MachineData) : List Nat := [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, (9 - (s.regs.get64 .r15).toNat), 0, (3 * (48 - (s.regs.get64 .rbx).toNat) + 1), 1, 0, 0]
/-- ff_aac_sbr_apply.L7090_1 -/
abbrev L7090_1 (s : MachineData) : List Nat := [1, ((if s.regs.get64 .r13 - slot64 s 0x38 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, (9 - (s.regs.get64 .r15).toNat), 0, (3 * (48 - (s.regs.get64 .rbx).toNat) + 1), 1, 0, 0]
/-- ff_aac_sbr_apply.L7090_2 -/
abbrev L7090_2 (s : MachineData) : List Nat := [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, (9 - (s.regs.get64 .r15).toNat), 0, (3 * (48 - (s.regs.get64 .rbx).toNat) + 1), 1, 0, 0]
/-- ff_aac_sbr_apply.L70bf -/
abbrev L70bf (s : MachineData) : List Nat := [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, (9 - (s.regs.get64 .r15).toNat), 0, (3 * (48 - (s.regs.get64 .rbx).toNat) + 0), 0, (0), 0]
/-- ff_aac_sbr_apply.L70ca -/
abbrev L70ca (s : MachineData) : List Nat := [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, (9 - (s.regs.get64 .r15).toNat), 0, (3 * (48 - (s.regs.get64 .rbx).toNat) + 2), 0, (0), 0]
/-- ff_aac_sbr_apply.L70ca_1 -/
abbrev L70ca_1 (s : MachineData) : List Nat := [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, (9 - (s.regs.get64 .r15).toNat), 0, (3 * (48 - (s.regs.get64 .rbx).toNat) + 2), 0, (0), 0]
/-- ff_aac_sbr_apply.L7120 -/
abbrev L7120 (s : MachineData) : List Nat := [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, (9 - (s.regs.get64 .r15).toNat), 0, (3 * (48 - (s.regs.get64 .rbx).toNat) + 2), 0, (0), 0]
/-- ff_aac_sbr_apply.L7140 -/
abbrev L7140 (s : MachineData) : List Nat := [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, (9 - (s.regs.get64 .r15).toNat), 0, (3 * (48 - (s.regs.get64 .rbx).toNat) + 2), 0, (0), 0]
/-- ff_aac_sbr_apply.L7166 -/
abbrev L7166 (s : MachineData) : List Nat := [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, (9 - (s.regs.get64 .r15).toNat), 0, (3 * (48 - (s.regs.get64 .rbx).toNat) + 2), 0, (0), 0]
/-- ff_aac_sbr_apply.L717f -/
abbrev L717f (s : MachineData) : List Nat := [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, (9 - (s.regs.get64 .r15).toNat), 0, (3 * (48 - (s.regs.get64 .rbx).toNat) + 2), 0, (0), 0]
/-- ff_aac_sbr_apply.L71b0 -/
abbrev L71b0 (s : MachineData) : List Nat := [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, (9 - (s.regs.get64 .r15).toNat), 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L71e0 -/
abbrev L71e0 (s : MachineData) : List Nat := [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L71e0_1 -/
abbrev L71e0_1 (s : MachineData) : List Nat := [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7226 -/
abbrev L7226 (s : MachineData) : List Nat := [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L723c -/
abbrev L723c (s : MachineData) : List Nat := [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L723c_1 -/
abbrev L723c_1 (s : MachineData) : List Nat := [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7270 -/
abbrev L7270 (s : MachineData) : List Nat := [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7286 -/
abbrev L7286 (s : MachineData) : List Nat := [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7286_1 -/
abbrev L7286_1 (s : MachineData) : List Nat := [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L72ba -/
abbrev L72ba (s : MachineData) : List Nat := [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L72d0 -/
abbrev L72d0 (s : MachineData) : List Nat := [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L72d0_1 -/
abbrev L72d0_1 (s : MachineData) : List Nat := [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7304 -/
abbrev L7304 (s : MachineData) : List Nat := [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L731a -/
abbrev L731a (s : MachineData) : List Nat := [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L731a_1 -/
abbrev L731a_1 (s : MachineData) : List Nat := [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L734a -/
abbrev L734a (s : MachineData) : List Nat := [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7360 -/
abbrev L7360 (s : MachineData) : List Nat := [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7370 -/
abbrev L7370 (s : MachineData) : List Nat := [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L73a1 -/
abbrev L73a1 (s : MachineData) : List Nat := [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 2), 0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L73b7 -/
abbrev L73b7 (s : MachineData) : List Nat := [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 2), 0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L73b7_1 -/
abbrev L73b7_1 (s : MachineData) : List Nat := [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 2), 0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L73eb -/
abbrev L73eb (s : MachineData) : List Nat := [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 2), 0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7401 -/
abbrev L7401 (s : MachineData) : List Nat := [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 2), 0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7401_1 -/
abbrev L7401_1 (s : MachineData) : List Nat := [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 2), 0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7435 -/
abbrev L7435 (s : MachineData) : List Nat := [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 2), 0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L744b -/
abbrev L744b (s : MachineData) : List Nat := [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 2), 0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L744b_1 -/
abbrev L744b_1 (s : MachineData) : List Nat := [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 2), 0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L747f -/
abbrev L747f (s : MachineData) : List Nat := [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 2), 0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7495 -/
abbrev L7495 (s : MachineData) : List Nat := [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 2), 0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7495_1 -/
abbrev L7495_1 (s : MachineData) : List Nat := [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 2), 0, (0), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L74de -/
abbrev L74de (s : MachineData) : List Nat := [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L74e9 -/
abbrev L74e9 (s : MachineData) : List Nat := [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L74e9_1 -/
abbrev L74e9_1 (s : MachineData) : List Nat := [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L74e9_2 -/
abbrev L74e9_2 (s : MachineData) : List Nat := [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L74e9_3 -/
abbrev L74e9_3 (s : MachineData) : List Nat := [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L74e9_4 -/
abbrev L74e9_4 (s : MachineData) : List Nat := [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7682 -/
abbrev L7682 (s : MachineData) : List Nat := [0, (2 - (s.regs.get64 .rdx).toNat), 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7682_1 -/
abbrev L7682_1 (s : MachineData) : List Nat := [0, (2 - (s.regs.get64 .rdx).toNat), 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7682_2 -/
abbrev L7682_2 (s : MachineData) : List Nat := [0, (2 - (s.regs.get64 .rdx).toNat), 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7682_3 -/
abbrev L7682_3 (s : MachineData) : List Nat := [0, (2 - (s.regs.get64 .rdx).toNat), 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7682_4 -/
abbrev L7682_4 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7682_5 -/
abbrev L7682_5 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7682_6 -/
abbrev L7682_6 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7682_7 -/
abbrev L7682_7 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7682_8 -/
abbrev L7682_8 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7750 -/
abbrev L7750 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 10, (4096 - (s.regs.get64 .r13).toNat), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7750_1 -/
abbrev L7750_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 10, (4096 - (s.regs.get64 .r13).toNat), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7750_2 -/
abbrev L7750_2 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 10, (4096 - (s.regs.get64 .r13).toNat), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7750_3 -/
abbrev L7750_3 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 10, (4096 - (s.regs.get64 .r13).toNat), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7750_4 -/
abbrev L7750_4 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 10, (4096 - (s.regs.get64 .r13).toNat), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7750_5 -/
abbrev L7750_5 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 10, (4096 - (s.regs.get64 .r13).toNat), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7750_6 -/
abbrev L7750_6 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7750_7 -/
abbrev L7750_7 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7750_8 -/
abbrev L7750_8 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7866 -/
abbrev L7866 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7884 -/
abbrev L7884 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7884_1 -/
abbrev L7884_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L78f2 -/
abbrev L78f2 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7910 -/
abbrev L7910 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7910_1 -/
abbrev L7910_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L797e -/
abbrev L797e (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L799c -/
abbrev L799c (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L799c_1 -/
abbrev L799c_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7a0a -/
abbrev L7a0a (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7a28 -/
abbrev L7a28 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7a28_1 -/
abbrev L7a28_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7a96 -/
abbrev L7a96 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7ab4 -/
abbrev L7ab4 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7b00 -/
abbrev L7b00 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7b00_1 -/
abbrev L7b00_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7b2d -/
abbrev L7b2d (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 9, (6 - (s.regs.get64 .r15).toNat), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7b50 -/
abbrev L7b50 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 9, (6 - (s.regs.get64 .r15).toNat), 0, (256 - (s.regs.get64 .r14).toNat), 1, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7b80 -/
abbrev L7b80 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 9, (6 - (s.regs.get64 .r15).toNat), 0, (256 - (s.regs.get64 .r14).toNat), 0, ((s.regs.get64 .rcx).toNat - (s.regs.get64 .rdx).toNat), 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7bb0 -/
abbrev L7bb0 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 9, (6 - (s.regs.get64 .r15).toNat), 0, (256 - (s.regs.get64 .r14).toNat), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7bb3 -/
abbrev L7bb3 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 9, (6 - (s.regs.get64 .r15).toNat), 0, (256 - (s.regs.get64 .r14).toNat), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7bb3_1 -/
abbrev L7bb3_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 9, (6 - (s.regs.get64 .r15).toNat), 0, (256 - (s.regs.get64 .r14).toNat), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7bb3_2 -/
abbrev L7bb3_2 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 9, (6 - (s.regs.get64 .r15).toNat), 0, (256 - (s.regs.get64 .r14).toNat), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7c5d -/
abbrev L7c5d (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 9, (6 - (s.regs.get64 .r15).toNat), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7c80 -/
abbrev L7c80 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7c80_1 -/
abbrev L7c80_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7cb0 -/
abbrev L7cb0 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7cbf -/
abbrev L7cbf (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7ce0 -/
abbrev L7ce0 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7ce4 -/
abbrev L7ce4 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 3, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7ce4_1 -/
abbrev L7ce4_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 3, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7ce4_2 -/
abbrev L7ce4_2 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 3, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7ce4_3 -/
abbrev L7ce4_3 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 3, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7ce4_4 -/
abbrev L7ce4_4 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 3, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7ce4_5 -/
abbrev L7ce4_5 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 3, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7db0 -/
abbrev L7db0 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (s.regs.get64 .rcx).toNat), 13, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7db0_1 -/
abbrev L7db0_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (s.regs.get64 .r14).toNat), 13, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7e20 -/
abbrev L7e20 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (s.regs.get64 .r14).toNat), 12, (50 - (s.regs.get64 .rdx).toNat), 1, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7e29 -/
abbrev L7e29 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (s.regs.get64 .r14).toNat), 12, (50 - (s.regs.get64 .rdx).toNat), 1, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7e60 -/
abbrev L7e60 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (s.regs.get64 .r14).toNat), 12, (51 - (s.regs.get64 .rdx).toNat), 0, (2 ^ 16 + 64 - (s.regs.get64 .rdi).toNat), 0, 0, 0]
/-- ff_aac_sbr_apply.L7e60_1 -/
abbrev L7e60_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (s.regs.get64 .r14).toNat), 12, (51 - (s.regs.get64 .rdx).toNat), 0, (2 ^ 16 + 64 - (s.regs.get64 .rdi).toNat), 0, 0, 0]
/-- ff_aac_sbr_apply.L7e90 -/
abbrev L7e90 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (s.regs.get64 .r14).toNat), 12, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7e90_1 -/
abbrev L7e90_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 12, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7eb6 -/
abbrev L7eb6 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 12, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7eb6_1 -/
abbrev L7eb6_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 12, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7f10 -/
abbrev L7f10 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 11, (((s.regs.get64 .r11) - (s.regs.get64 .r9)).toNat), 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7f36 -/
abbrev L7f36 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 11, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7f36_1 -/
abbrev L7f36_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 11, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7f80 -/
abbrev L7f80 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 10, ((0x21998#64 - ((s.regs.get64 .rdi) + (s.regs.get64 .r14))).toNat), 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L7f80_1 -/
abbrev L7f80_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 10, ((0x21998#64 - ((s.regs.get64 .rdi) + (s.regs.get64 .r14))).toNat), 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8009 -/
abbrev L8009 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 10, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8050 -/
abbrev L8050 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 9, (((s.regs.get64 .r11) - (s.regs.get64 .r9)).toNat), 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8077 -/
abbrev L8077 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 9, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8077_1 -/
abbrev L8077_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 9, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L80c0 -/
abbrev L80c0 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 8, ((0x21998#64 - ((s.regs.get64 .rsi) + (s.regs.get64 .r14))).toNat), 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L80c0_1 -/
abbrev L80c0_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 8, ((0x21998#64 - ((s.regs.get64 .rsi) + (s.regs.get64 .r14))).toNat), 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L814a -/
abbrev L814a (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 8, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8190 -/
abbrev L8190 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 7, (((s.regs.get64 .r11) - (s.regs.get64 .r9)).toNat), 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L81b7 -/
abbrev L81b7 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 7, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L81b7_1 -/
abbrev L81b7_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 7, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8200 -/
abbrev L8200 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 6, ((0x21998#64 - ((s.regs.get64 .rdi) + (s.regs.get64 .r14))).toNat), 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8200_1 -/
abbrev L8200_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 6, ((0x21998#64 - ((s.regs.get64 .rdi) + (s.regs.get64 .r14))).toNat), 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L828a -/
abbrev L828a (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 6, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L82d0 -/
abbrev L82d0 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 5, (((s.regs.get64 .r11) - (s.regs.get64 .r9)).toNat), 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L82f7 -/
abbrev L82f7 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 5, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L82f7_1 -/
abbrev L82f7_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 5, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8340 -/
abbrev L8340 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 4, ((0x21998#64 - ((s.regs.get64 .rsi) + (s.regs.get64 .r14))).toNat), 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8340_1 -/
abbrev L8340_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 4, ((0x21998#64 - ((s.regs.get64 .rsi) + (s.regs.get64 .r14))).toNat), 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L83ca -/
abbrev L83ca (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 4, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8410 -/
abbrev L8410 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 3, (((s.regs.get64 .r11) - (s.regs.get64 .r9)).toNat), 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8437 -/
abbrev L8437 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 3, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8437_1 -/
abbrev L8437_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 3, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8480 -/
abbrev L8480 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 2, ((0x21998#64 - ((s.regs.get64 .rdi) + (s.regs.get64 .rbx))).toNat), 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8480_1 -/
abbrev L8480_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 2, ((0x21998#64 - ((s.regs.get64 .rdi) + (s.regs.get64 .rbx))).toNat), 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8509 -/
abbrev L8509 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 2, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8520 -/
abbrev L8520 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 2, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8570 -/
abbrev L8570 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 1, (50 - (s.regs.get64 .rdi).toNat), 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8570_1 -/
abbrev L8570_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 1, (50 - (s.regs.get64 .rdi).toNat), 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L85c0 -/
abbrev L85c0 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 1, (50 - (s.regs.get64 .rdi).toNat), 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L85cd -/
abbrev L85cd (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 1, (50 - (s.regs.get64 .rdi).toNat), 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L85cd_1 -/
abbrev L85cd_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 1, (50 - (s.regs.get64 .rdi).toNat), 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L85cd_2 -/
abbrev L85cd_2 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 1, (50 - (s.regs.get64 .rdi).toNat), 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8620 -/
abbrev L8620 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 1, (50 - (s.regs.get64 .rdi).toNat), 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L862d -/
abbrev L862d (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 1, (50 - (s.regs.get64 .rdi).toNat), 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L862d_1 -/
abbrev L862d_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 1, (51 - (s.regs.get64 .rdi).toNat), 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8660 -/
abbrev L8660 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 1, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L86a0 -/
abbrev L86a0 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 0, (4 * (48 - (s.regs.get64 .r13).toNat) + 1), 1, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L86b0 -/
abbrev L86b0 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 0, (4 * (48 - (s.regs.get64 .r13).toNat) + 1), 1, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L86b0_1 -/
abbrev L86b0_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 0, (4 * (48 - (s.regs.get64 .r13).toNat) + 3), 1, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L86d7 -/
abbrev L86d7 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 0, (4 * (48 - (s.regs.get64 .r13).toNat) + 3), 1, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8700 -/
abbrev L8700 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 0, (4 * (48 - (s.regs.get64 .r13).toNat) + 2), 0, ((s.regs.get64 .rdx).toNat), 0, 0, 0]
/-- ff_aac_sbr_apply.L8720 -/
abbrev L8720 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 0, (4 * (48 - (s.regs.get64 .r13).toNat) + 2), 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8740 -/
abbrev L8740 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8740_1 -/
abbrev L8740_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8790 -/
abbrev L8790 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L879e -/
abbrev L879e (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L879e_1 -/
abbrev L879e_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L879e_2 -/
abbrev L879e_2 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8818 -/
abbrev L8818 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L881c -/
abbrev L881c (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L881c_1 -/
abbrev L881c_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L881c_2 -/
abbrev L881c_2 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L881c_3 -/
abbrev L881c_3 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L881c_4 -/
abbrev L881c_4 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8900 -/
abbrev L8900 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 1, (2 * (48 - (s.regs.get64 .rbx).toNat)), 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8900_1 -/
abbrev L8900_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 1, (2 * (48 - (s.regs.get64 .rbx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8900_2 -/
abbrev L8900_2 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 1, (2 * (48 - (s.regs.get64 .rbx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8947 -/
abbrev L8947 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 1, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8947_1 -/
abbrev L8947_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 1, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8970 -/
abbrev L8970 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 0, (2 * (9 - (s.regs.get64 .r8).toNat)), 1, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8970_1 -/
abbrev L8970_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 0, (2 * (9 - (s.regs.get64 .r8).toNat) + 2), 1, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L89e0 -/
abbrev L89e0 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 0, (2 * (9 - (slot64 s 0x68).toNat) + 1), 0, (2 * (50 - (s.regs.get64 .rbx).toNat)), 2, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L89f3 -/
abbrev L89f3 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 0, (2 * (9 - (slot64 s 0x68).toNat) + 1), 0, (2 * (50 - (s.regs.get64 .rbx).toNat)), 2, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L89f3_1 -/
abbrev L89f3_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 0, (2 * (9 - (slot64 s 0x68).toNat) + 1), 0, (2 * (50 - (s.regs.get64 .rbx).toNat) + 1), 2, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8a50 -/
abbrev L8a50 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 0, (2 * (9 - (slot64 s 0x68).toNat) + 1), 0, (2 * (50 - (s.regs.get64 .rbx).toNat) + 1), 1, (64 - (s.regs.get64 .r13).toNat), 0, 0, 0]
/-- ff_aac_sbr_apply.L8a50_1 -/
abbrev L8a50_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 0, (2 * (9 - (slot64 s 0x68).toNat) + 1), 0, (2 * (50 - (s.regs.get64 .rbx).toNat) + 1), 1, (64 - (s.regs.get64 .r13).toNat), 0, 0, 0]
/-- ff_aac_sbr_apply.L8a50_2 -/
abbrev L8a50_2 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 0, (2 * (9 - (slot64 s 0x68).toNat) + 1), 0, (2 * (50 - (s.regs.get64 .rbx).toNat) + 1), 1, (64 - (s.regs.get64 .r13).toNat), 0, 0, 0]
/-- ff_aac_sbr_apply.L8a50_3 -/
abbrev L8a50_3 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 0, (2 * (9 - (slot64 s 0x68).toNat) + 1), 0, (2 * (50 - (s.regs.get64 .rbx).toNat) + 1), 1, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8ad0 -/
abbrev L8ad0 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 0, (2 * (9 - (slot64 s 0x68).toNat) + 1), 0, (2 * (50 - (s.regs.get64 .rbx).toNat) + 1), 0, (48 - (s.regs.get64 .rcx).toNat), 0, 0, 0]
/-- ff_aac_sbr_apply.L8ad0_1 -/
abbrev L8ad0_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 0, (2 * (9 - (slot64 s 0x68).toNat) + 1), 0, (2 * (50 - (s.regs.get64 .rbx).toNat) + 1), 0, (48 - (s.regs.get64 .rcx).toNat), 0, 0, 0]
/-- ff_aac_sbr_apply.L8b00 -/
abbrev L8b00 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 0, (2 * (9 - (slot64 s 0x68).toNat) + 1), 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8b2a -/
abbrev L8b2a (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8b4f -/
abbrev L8b4f (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, (1), 0, (0), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8b6b -/
abbrev L8b6b (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8b77 -/
abbrev L8b77 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8b77_1 -/
abbrev L8b77_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8b77_2 -/
abbrev L8b77_2 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8bf0 -/
abbrev L8bf0 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 7, (2 * (48 - (s.regs.get64 .rbx).toNat)), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8bf0_1 -/
abbrev L8bf0_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 7, (2 * (48 - (s.regs.get64 .rbx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8bf0_2 -/
abbrev L8bf0_2 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 7, (2 * (48 - (s.regs.get64 .rbx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8c33 -/
abbrev L8c33 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8c4c -/
abbrev L8c4c (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8c4c_1 -/
abbrev L8c4c_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8c4c_2 -/
abbrev L8c4c_2 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8cc9 -/
abbrev L8cc9 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 6, (2 * (48 - (s.regs.get64 .rbx).toNat)), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8cc9_1 -/
abbrev L8cc9_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 6, (2 * (48 - (s.regs.get64 .rbx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8cc9_2 -/
abbrev L8cc9_2 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 6, (2 * (48 - (s.regs.get64 .rbx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8d0c -/
abbrev L8d0c (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8d26 -/
abbrev L8d26 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8d26_1 -/
abbrev L8d26_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8d26_2 -/
abbrev L8d26_2 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8da3 -/
abbrev L8da3 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 5, (2 * (48 - (s.regs.get64 .rbx).toNat)), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8da3_1 -/
abbrev L8da3_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 5, (2 * (48 - (s.regs.get64 .rbx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8da3_2 -/
abbrev L8da3_2 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 5, (2 * (48 - (s.regs.get64 .rbx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8de6 -/
abbrev L8de6 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8dff -/
abbrev L8dff (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8dff_1 -/
abbrev L8dff_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8dff_2 -/
abbrev L8dff_2 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8e7c -/
abbrev L8e7c (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 4, (2 * (48 - (s.regs.get64 .rbx).toNat)), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8e7c_1 -/
abbrev L8e7c_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 4, (2 * (48 - (s.regs.get64 .rbx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8e7c_2 -/
abbrev L8e7c_2 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 4, (2 * (48 - (s.regs.get64 .rbx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8ebf -/
abbrev L8ebf (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8ed9 -/
abbrev L8ed9 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8ed9_1 -/
abbrev L8ed9_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8ed9_2 -/
abbrev L8ed9_2 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8f56 -/
abbrev L8f56 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 3, (2 * (48 - (s.regs.get64 .rbx).toNat)), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8f56_1 -/
abbrev L8f56_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 3, (2 * (48 - (s.regs.get64 .rbx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8f56_2 -/
abbrev L8f56_2 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 3, (2 * (48 - (s.regs.get64 .rbx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8f93 -/
abbrev L8f93 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8fa4 -/
abbrev L8fa4 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8fa4_1 -/
abbrev L8fa4_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8fa4_2 -/
abbrev L8fa4_2 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L8fa4_3 -/
abbrev L8fa4_3 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9026 -/
abbrev L9026 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 2, (2 * (48 - (s.regs.get64 .rbx).toNat)), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9026_1 -/
abbrev L9026_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 2, (2 * (48 - (s.regs.get64 .rbx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9026_2 -/
abbrev L9026_2 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 2, (2 * (48 - (s.regs.get64 .rbx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9063 -/
abbrev L9063 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9070 -/
abbrev L9070 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L907f -/
abbrev L907f (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L907f_1 -/
abbrev L907f_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L907f_2 -/
abbrev L907f_2 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L907f_3 -/
abbrev L907f_3 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L90f9 -/
abbrev L90f9 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 1, (2 * (48 - (s.regs.get64 .rbx).toNat)), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L90f9_1 -/
abbrev L90f9_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 1, (2 * (48 - (s.regs.get64 .rbx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L90f9_2 -/
abbrev L90f9_2 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 1, (2 * (48 - (s.regs.get64 .rbx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L913a -/
abbrev L913a (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9146 -/
abbrev L9146 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L914e -/
abbrev L914e (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L914e_1 -/
abbrev L914e_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L914e_2 -/
abbrev L914e_2 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L914e_3 -/
abbrev L914e_3 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L91c0 -/
abbrev L91c0 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (s.regs.get64 .r12).toNat) + 1), 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L91f7 -/
abbrev L91f7 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (s.regs.get64 .r12).toNat) + 127), 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9206 -/
abbrev L9206 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (s.regs.get64 .r12).toNat) + 127), 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9215 -/
abbrev L9215 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (s.regs.get64 .r12).toNat) + 127), 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9215_1 -/
abbrev L9215_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (s.regs.get64 .r12).toNat) + 127), 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9215_2 -/
abbrev L9215_2 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (s.regs.get64 .r12).toNat) + 127), 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9215_3 -/
abbrev L9215_3 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (s.regs.get64 .r12).toNat) + 127), 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9215_4 -/
abbrev L9215_4 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (s.regs.get64 .r12).toNat) + 127), 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9215_5 -/
abbrev L9215_5 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (s.regs.get64 .r12).toNat) + 127), 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9290 -/
abbrev L9290 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 1), 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L929e -/
abbrev L929e (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (s.regs.get64 .rdx).toNat) + 3), 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L929e_1 -/
abbrev L929e_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9300 -/
abbrev L9300 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 5, (2 * (64 - (s.regs.get64 .rax).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9300_1 -/
abbrev L9300_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 5, (2 * (64 - (s.regs.get64 .rax).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9300_2 -/
abbrev L9300_2 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 5, (2 * (64 - (s.regs.get64 .rax).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9370 -/
abbrev L9370 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 5, (2 * (64 - (s.regs.get64 .rax).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9386 -/
abbrev L9386 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 5, (2 * (64 - (s.regs.get64 .rax).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9386_1 -/
abbrev L9386_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 5, (2 * (64 - (s.regs.get64 .rax).toNat) + 3), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L93d0 -/
abbrev L93d0 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L93f0 -/
abbrev L93f0 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L93f0_1 -/
abbrev L93f0_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9440 -/
abbrev L9440 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 4, ((s.regs.get64 .r12).toNat), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9458 -/
abbrev L9458 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9470 -/
abbrev L9470 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 3, (64 - (s.regs.get64 .rbx).toNat), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9470_1 -/
abbrev L9470_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 3, (64 - (s.regs.get64 .rbx).toNat), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9504 -/
abbrev L9504 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9520 -/
abbrev L9520 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L952c -/
abbrev L952c (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9530 -/
abbrev L9530 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9530_1 -/
abbrev L9530_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L95a0 -/
abbrev L95a0 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 2, (2 * (64 - (s.regs.get64 .rax).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L95a0_1 -/
abbrev L95a0_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 2, (2 * (64 - (s.regs.get64 .rax).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L95a0_2 -/
abbrev L95a0_2 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 2, (2 * (64 - (s.regs.get64 .rax).toNat) + 3), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9600 -/
abbrev L9600 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9617 -/
abbrev L9617 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9617_1 -/
abbrev L9617_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L968d -/
abbrev L968d (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L96d3 -/
abbrev L96d3 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L96e1 -/
abbrev L96e1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 1, (0), 1, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9720 -/
abbrev L9720 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 1, (3 * (64 - (s.regs.get64 .rbx).toNat) + 1), 1, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9731 -/
abbrev L9731 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 1, (3 * (64 - (s.regs.get64 .rbx).toNat)), 0, (0), 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9731_1 -/
abbrev L9731_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 1, (3 * (64 - (s.regs.get64 .rbx).toNat)), 0, (0), 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L97b7 -/
abbrev L97b7 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 1, (3 * (64 - (s.regs.get64 .rbx).toNat) + 2), 0, (0), 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L97f0 -/
abbrev L97f0 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 1, (3 * (64 - (s.regs.get64 .rbx).toNat) + 2), 0, (0), 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9820 -/
abbrev L9820 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L983f -/
abbrev L983f (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9860 -/
abbrev L9860 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 0, (2 * (64 - (s.regs.get64 .rax).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9860_1 -/
abbrev L9860_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 0, (2 * (64 - (s.regs.get64 .rax).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9860_2 -/
abbrev L9860_2 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 0, (2 * (64 - (s.regs.get64 .rax).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9860_3 -/
abbrev L9860_3 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 0, (2 * (64 - (s.regs.get64 .rax).toNat) + 3), 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L98bc -/
abbrev L98bc (s : MachineData) : List Nat := [0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L98e0 -/
abbrev L98e0 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9927 -/
abbrev L9927 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9934 -/
abbrev L9934 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9934_1 -/
abbrev L9934_1 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9934_2 -/
abbrev L9934_2 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L99c6 -/
abbrev L99c6 (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L99cf -/
abbrev L99cf (s : MachineData) : List Nat := [0, (2 - (slot64 s 0x1a0).toNat), 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L99e9 -/
abbrev L99e9 (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L99ee -/
abbrev L99ee (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L99f3 -/
abbrev L99f3 (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L99f8 -/
abbrev L99f8 (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L99fd -/
abbrev L99fd (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9a02 -/
abbrev L9a02 (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9a02_1 -/
abbrev L9a02_1 (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9a50 -/
abbrev L9a50 (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9a55 -/
abbrev L9a55 (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9a5a -/
abbrev L9a5a (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9a5f -/
abbrev L9a5f (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9a64 -/
abbrev L9a64 (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9a69 -/
abbrev L9a69 (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9a7d -/
abbrev L9a7d (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9a85 -/
abbrev L9a85 (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9a85_1 -/
abbrev L9a85_1 (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9a85_2 -/
abbrev L9a85_2 (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9a85_3 -/
abbrev L9a85_3 (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9a85_4 -/
abbrev L9a85_4 (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9b24 -/
abbrev L9b24 (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9b2b -/
abbrev L9b2b (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.done -/
abbrev done (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9b36 -/
abbrev L9b36 (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9b3b -/
abbrev L9b3b (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9b40 -/
abbrev L9b40 (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9b45 -/
abbrev L9b45 (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9b4a -/
abbrev L9b4a (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9b4f -/
abbrev L9b4f (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9b54 -/
abbrev L9b54 (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9b59 -/
abbrev L9b59 (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9b5e -/
abbrev L9b5e (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9b63 -/
abbrev L9b63 (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9b68 -/
abbrev L9b68 (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9b6d -/
abbrev L9b6d (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9b72 -/
abbrev L9b72 (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9b77 -/
abbrev L9b77 (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9b7c -/
abbrev L9b7c (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9b81 -/
abbrev L9b81 (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9b86 -/
abbrev L9b86 (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9b8b -/
abbrev L9b8b (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9b90 -/
abbrev L9b90 (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9b95 -/
abbrev L9b95 (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9b9a -/
abbrev L9b9a (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9b9a_1 -/
abbrev L9b9a_1 (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9bc5 -/
abbrev L9bc5 (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9bca -/
abbrev L9bca (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9bcf -/
abbrev L9bcf (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9bd4 -/
abbrev L9bd4 (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9bd4_1 -/
abbrev L9bd4_1 (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9bff -/
abbrev L9bff (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9c04 -/
abbrev L9c04 (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9c09 -/
abbrev L9c09 (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9c0e -/
abbrev L9c0e (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9c13 -/
abbrev L9c13 (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9c18 -/
abbrev L9c18 (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9c1d -/
abbrev L9c1d (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9c22 -/
abbrev L9c22 (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- ff_aac_sbr_apply.L9c27 -/
abbrev L9c27 (s : MachineData) : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
end VD

def VAR : List (MachineData → List Nat) := [
  VD.start,
  VD.start_1,
  VD.start_2,
  VD.start_3,
  VD.L676e,
  VD.L6797,
  VD.L6797_1,
  VD.L6817,
  VD.L6825,
  VD.L6838,
  VD.L6838_1,
  VD.L6838_2,
  VD.L68b0,
  VD.L68d0,
  VD.L68d0_1,
  VD.L68f8,
  VD.L6940,
  VD.L6940_1,
  VD.L69a4,
  VD.L69d0,
  VD.L69dd,
  VD.L6a10,
  VD.L6a30,
  VD.L6a30_1,
  VD.L6a30_2,
  VD.L6a90,
  VD.L6abf,
  VD.L6b00,
  VD.L6b02,
  VD.L6b12,
  VD.L6b50,
  VD.L6b6c,
  VD.L6ba0,
  VD.L6bbc,
  VD.L6bbc_1,
  VD.L6c1e,
  VD.L6c3a,
  VD.L6c61,
  VD.L6c7d,
  VD.L6c7d_1,
  VD.L6c7d_2,
  VD.L6ce0,
  VD.L6cea,
  VD.L6d09,
  VD.L6d32,
  VD.L6d51,
  VD.L6d51_1,
  VD.L6dbc,
  VD.L6ddb,
  VD.L6e04,
  VD.L6e23,
  VD.L6e23_1,
  VD.L6e8c,
  VD.L6ea8,
  VD.L6ecf,
  VD.L6eeb,
  VD.L6eeb_1,
  VD.L6eeb_2,
  VD.L6f32,
  VD.L6f32_1,
  VD.L6f32_2,
  VD.L6fbe,
  VD.L6fca,
  VD.L6ff7,
  VD.L6ffc,
  VD.L7007,
  VD.L700e,
  VD.L7020,
  VD.L7020_1,
  VD.L7020_2,
  VD.L7044,
  VD.L7044_1,
  VD.L7070,
  VD.L7090,
  VD.L7090_1,
  VD.L7090_2,
  VD.L70bf,
  VD.L70ca,
  VD.L70ca_1,
  VD.L7120,
  VD.L7140,
  VD.L7166,
  VD.L717f,
  VD.L71b0,
  VD.L71e0,
  VD.L71e0_1,
  VD.L7226,
  VD.L723c,
  VD.L723c_1,
  VD.L7270,
  VD.L7286,
  VD.L7286_1,
  VD.L72ba,
  VD.L72d0,
  VD.L72d0_1,
  VD.L7304,
  VD.L731a,
  VD.L731a_1,
  VD.L734a,
  VD.L7360,
  VD.L7370,
  VD.L73a1,
  VD.L73b7,
  VD.L73b7_1,
  VD.L73eb,
  VD.L7401,
  VD.L7401_1,
  VD.L7435,
  VD.L744b,
  VD.L744b_1,
  VD.L747f,
  VD.L7495,
  VD.L7495_1,
  VD.L74de,
  VD.L74e9,
  VD.L74e9_1,
  VD.L74e9_2,
  VD.L74e9_3,
  VD.L74e9_4,
  VD.L7682,
  VD.L7682_1,
  VD.L7682_2,
  VD.L7682_3,
  VD.L7682_4,
  VD.L7682_5,
  VD.L7682_6,
  VD.L7682_7,
  VD.L7682_8,
  VD.L7750,
  VD.L7750_1,
  VD.L7750_2,
  VD.L7750_3,
  VD.L7750_4,
  VD.L7750_5,
  VD.L7750_6,
  VD.L7750_7,
  VD.L7750_8,
  VD.L7866,
  VD.L7884,
  VD.L7884_1,
  VD.L78f2,
  VD.L7910,
  VD.L7910_1,
  VD.L797e,
  VD.L799c,
  VD.L799c_1,
  VD.L7a0a,
  VD.L7a28,
  VD.L7a28_1,
  VD.L7a96,
  VD.L7ab4,
  VD.L7b00,
  VD.L7b00_1,
  VD.L7b2d,
  VD.L7b50,
  VD.L7b80,
  VD.L7bb0,
  VD.L7bb3,
  VD.L7bb3_1,
  VD.L7bb3_2,
  VD.L7c5d,
  VD.L7c80,
  VD.L7c80_1,
  VD.L7cb0,
  VD.L7cbf,
  VD.L7ce0,
  VD.L7ce4,
  VD.L7ce4_1,
  VD.L7ce4_2,
  VD.L7ce4_3,
  VD.L7ce4_4,
  VD.L7ce4_5,
  VD.L7db0,
  VD.L7db0_1,
  VD.L7e20,
  VD.L7e29,
  VD.L7e60,
  VD.L7e60_1,
  VD.L7e90,
  VD.L7e90_1,
  VD.L7eb6,
  VD.L7eb6_1,
  VD.L7f10,
  VD.L7f36,
  VD.L7f36_1,
  VD.L7f80,
  VD.L7f80_1,
  VD.L8009,
  VD.L8050,
  VD.L8077,
  VD.L8077_1,
  VD.L80c0,
  VD.L80c0_1,
  VD.L814a,
  VD.L8190,
  VD.L81b7,
  VD.L81b7_1,
  VD.L8200,
  VD.L8200_1,
  VD.L828a,
  VD.L82d0,
  VD.L82f7,
  VD.L82f7_1,
  VD.L8340,
  VD.L8340_1,
  VD.L83ca,
  VD.L8410,
  VD.L8437,
  VD.L8437_1,
  VD.L8480,
  VD.L8480_1,
  VD.L8509,
  VD.L8520,
  VD.L8570,
  VD.L8570_1,
  VD.L85c0,
  VD.L85cd,
  VD.L85cd_1,
  VD.L85cd_2,
  VD.L8620,
  VD.L862d,
  VD.L862d_1,
  VD.L8660,
  VD.L86a0,
  VD.L86b0,
  VD.L86b0_1,
  VD.L86d7,
  VD.L8700,
  VD.L8720,
  VD.L8740,
  VD.L8740_1,
  VD.L8790,
  VD.L879e,
  VD.L879e_1,
  VD.L879e_2,
  VD.L8818,
  VD.L881c,
  VD.L881c_1,
  VD.L881c_2,
  VD.L881c_3,
  VD.L881c_4,
  VD.L8900,
  VD.L8900_1,
  VD.L8900_2,
  VD.L8947,
  VD.L8947_1,
  VD.L8970,
  VD.L8970_1,
  VD.L89e0,
  VD.L89f3,
  VD.L89f3_1,
  VD.L8a50,
  VD.L8a50_1,
  VD.L8a50_2,
  VD.L8a50_3,
  VD.L8ad0,
  VD.L8ad0_1,
  VD.L8b00,
  VD.L8b2a,
  VD.L8b4f,
  VD.L8b6b,
  VD.L8b77,
  VD.L8b77_1,
  VD.L8b77_2,
  VD.L8bf0,
  VD.L8bf0_1,
  VD.L8bf0_2,
  VD.L8c33,
  VD.L8c4c,
  VD.L8c4c_1,
  VD.L8c4c_2,
  VD.L8cc9,
  VD.L8cc9_1,
  VD.L8cc9_2,
  VD.L8d0c,
  VD.L8d26,
  VD.L8d26_1,
  VD.L8d26_2,
  VD.L8da3,
  VD.L8da3_1,
  VD.L8da3_2,
  VD.L8de6,
  VD.L8dff,
  VD.L8dff_1,
  VD.L8dff_2,
  VD.L8e7c,
  VD.L8e7c_1,
  VD.L8e7c_2,
  VD.L8ebf,
  VD.L8ed9,
  VD.L8ed9_1,
  VD.L8ed9_2,
  VD.L8f56,
  VD.L8f56_1,
  VD.L8f56_2,
  VD.L8f93,
  VD.L8fa4,
  VD.L8fa4_1,
  VD.L8fa4_2,
  VD.L8fa4_3,
  VD.L9026,
  VD.L9026_1,
  VD.L9026_2,
  VD.L9063,
  VD.L9070,
  VD.L907f,
  VD.L907f_1,
  VD.L907f_2,
  VD.L907f_3,
  VD.L90f9,
  VD.L90f9_1,
  VD.L90f9_2,
  VD.L913a,
  VD.L9146,
  VD.L914e,
  VD.L914e_1,
  VD.L914e_2,
  VD.L914e_3,
  VD.L91c0,
  VD.L91f7,
  VD.L9206,
  VD.L9215,
  VD.L9215_1,
  VD.L9215_2,
  VD.L9215_3,
  VD.L9215_4,
  VD.L9215_5,
  VD.L9290,
  VD.L929e,
  VD.L929e_1,
  VD.L9300,
  VD.L9300_1,
  VD.L9300_2,
  VD.L9370,
  VD.L9386,
  VD.L9386_1,
  VD.L93d0,
  VD.L93f0,
  VD.L93f0_1,
  VD.L9440,
  VD.L9458,
  VD.L9470,
  VD.L9470_1,
  VD.L9504,
  VD.L9520,
  VD.L952c,
  VD.L9530,
  VD.L9530_1,
  VD.L95a0,
  VD.L95a0_1,
  VD.L95a0_2,
  VD.L9600,
  VD.L9617,
  VD.L9617_1,
  VD.L968d,
  VD.L96d3,
  VD.L96e1,
  VD.L9720,
  VD.L9731,
  VD.L9731_1,
  VD.L97b7,
  VD.L97f0,
  VD.L9820,
  VD.L983f,
  VD.L9860,
  VD.L9860_1,
  VD.L9860_2,
  VD.L9860_3,
  VD.L98bc,
  VD.L98e0,
  VD.L9927,
  VD.L9934,
  VD.L9934_1,
  VD.L9934_2,
  VD.L99c6,
  VD.L99cf,
  VD.L99e9,
  VD.L99ee,
  VD.L99f3,
  VD.L99f8,
  VD.L99fd,
  VD.L9a02,
  VD.L9a02_1,
  VD.L9a50,
  VD.L9a55,
  VD.L9a5a,
  VD.L9a5f,
  VD.L9a64,
  VD.L9a69,
  VD.L9a7d,
  VD.L9a85,
  VD.L9a85_1,
  VD.L9a85_2,
  VD.L9a85_3,
  VD.L9a85_4,
  VD.L9b24,
  VD.L9b2b,
  VD.done,
  VD.L9b36,
  VD.L9b3b,
  VD.L9b40,
  VD.L9b45,
  VD.L9b4a,
  VD.L9b4f,
  VD.L9b54,
  VD.L9b59,
  VD.L9b5e,
  VD.L9b63,
  VD.L9b68,
  VD.L9b6d,
  VD.L9b72,
  VD.L9b77,
  VD.L9b7c,
  VD.L9b81,
  VD.L9b86,
  VD.L9b8b,
  VD.L9b90,
  VD.L9b95,
  VD.L9b9a,
  VD.L9b9a_1,
  VD.L9bc5,
  VD.L9bca,
  VD.L9bcf,
  VD.L9bd4,
  VD.L9bd4_1,
  VD.L9bff,
  VD.L9c04,
  VD.L9c09,
  VD.L9c0e,
  VD.L9c13,
  VD.L9c18,
  VD.L9c1d,
  VD.L9c22,
  VD.L9c27]

/-- The variant: `lex` of the label's digits. -/
def var (l : Label) (s : MachineData) : Nat :=
  lex ((VAR[labelList.idxOf l]?.getD (fun _ => [])) s)

namespace V
@[lex_var] theorem start {s : MachineData} : var "ff_aac_sbr_apply" s = lex [3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 0) rfl]; rfl
@[lex_var] theorem start_1 {s : MachineData} : var "ff_aac_sbr_apply.start_1" s = lex [3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 1) rfl]; rfl
@[lex_var] theorem start_2 {s : MachineData} : var "ff_aac_sbr_apply.start_2" s = lex [3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 2) rfl]; rfl
@[lex_var] theorem start_3 {s : MachineData} : var "ff_aac_sbr_apply.start_3" s = lex [3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 3) rfl]; rfl
@[lex_var] theorem L676e {s : MachineData} : var "ff_aac_sbr_apply.L676e" s = lex [2, (0), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 4) rfl]; rfl
@[lex_var] theorem L6797 {s : MachineData} : var "ff_aac_sbr_apply.L6797" s = lex [2, (1), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 5) rfl]; rfl
@[lex_var] theorem L6797_1 {s : MachineData} : var "ff_aac_sbr_apply.L6797_1" s = lex [2, (1), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 6) rfl]; rfl
@[lex_var] theorem L6817 {s : MachineData} : var "ff_aac_sbr_apply.L6817" s = lex [2, (1), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 7) rfl]; rfl
@[lex_var] theorem L6825 {s : MachineData} : var "ff_aac_sbr_apply.L6825" s = lex [2, (0), 0, (0), 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 8) rfl]; rfl
@[lex_var] theorem L6838 {s : MachineData} : var "ff_aac_sbr_apply.L6838" s = lex [2, (0), 0, (0), 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 9) rfl]; rfl
@[lex_var] theorem L6838_1 {s : MachineData} : var "ff_aac_sbr_apply.L6838_1" s = lex [2, (0), 0, (0), 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 10) rfl]; rfl
@[lex_var] theorem L6838_2 {s : MachineData} : var "ff_aac_sbr_apply.L6838_2" s = lex [2, (0), 0, (0), 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 11) rfl]; rfl
@[lex_var] theorem L68b0 {s : MachineData} : var "ff_aac_sbr_apply.L68b0" s = lex [2, (0), 0, (0), 1, (9 - (s.regs.get64 .rbx).toNat), 1, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 12) rfl]; rfl
@[lex_var] theorem L68d0 {s : MachineData} : var "ff_aac_sbr_apply.L68d0" s = lex [2, (0), 0, (0), 1, (9 - (s.regs.get64 .rbx).toNat), 0, (2 * (48 - (s.regs.get64 .r14).toNat)), 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 13) rfl]; rfl
@[lex_var] theorem L68d0_1 {s : MachineData} : var "ff_aac_sbr_apply.L68d0_1" s = lex [2, (0), 0, (0), 1, (9 - (s.regs.get64 .rbx).toNat), 0, (2 * (48 - (s.regs.get64 .r14).toNat)), 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 14) rfl]; rfl
@[lex_var] theorem L68f8 {s : MachineData} : var "ff_aac_sbr_apply.L68f8" s = lex [2, (0), 0, (0), 1, (9 - (s.regs.get64 .rbx).toNat), 0, (2 * (48 - (s.regs.get64 .r14).toNat) + 1), 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 15) rfl]; rfl
@[lex_var] theorem L6940 {s : MachineData} : var "ff_aac_sbr_apply.L6940" s = lex [2, (0), 0, (0), 1, (9 - (s.regs.get64 .rbx).toNat), 0, (2 * (48 - (s.regs.get64 .r14).toNat) + 1), 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 16) rfl]; rfl
@[lex_var] theorem L6940_1 {s : MachineData} : var "ff_aac_sbr_apply.L6940_1" s = lex [2, (0), 0, (0), 1, (9 - (s.regs.get64 .rbx).toNat), 0, (2 * (48 - (s.regs.get64 .r14).toNat) + 1), 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 17) rfl]; rfl
@[lex_var] theorem L69a4 {s : MachineData} : var "ff_aac_sbr_apply.L69a4" s = lex [2, (0), 0, (0), 1, (9 - (s.regs.get64 .rbx).toNat), 0, (2 * (48 - (s.regs.get64 .r14).toNat) + 1), 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 18) rfl]; rfl
@[lex_var] theorem L69d0 {s : MachineData} : var "ff_aac_sbr_apply.L69d0" s = lex [2, (0), 0, (0), 1, (9 - (s.regs.get64 .rbx).toNat), 0, (2 * (48 - (s.regs.get64 .r14).toNat) + 1), 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 19) rfl]; rfl
@[lex_var] theorem L69dd {s : MachineData} : var "ff_aac_sbr_apply.L69dd" s = lex [2, (0), 0, (0), 1, (9 - (s.regs.get64 .rbx).toNat), 0, (2 * (48 - (s.regs.get64 .r14).toNat) + 1), 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 20) rfl]; rfl
@[lex_var] theorem L6a10 {s : MachineData} : var "ff_aac_sbr_apply.L6a10" s = lex [2, (0), 0, (0), 1, (9 - (s.regs.get64 .rbx).toNat), 0, (2 * (48 - (s.regs.get64 .r14).toNat) + 1), 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 21) rfl]; rfl
@[lex_var] theorem L6a30 {s : MachineData} : var "ff_aac_sbr_apply.L6a30" s = lex [2, (0), 0, (0), 1, (9 - (s.regs.get64 .rbx).toNat), 0, (2 * (48 - (s.regs.get64 .r14).toNat) + 1), 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 22) rfl]; rfl
@[lex_var] theorem L6a30_1 {s : MachineData} : var "ff_aac_sbr_apply.L6a30_1" s = lex [2, (0), 0, (0), 1, (9 - (s.regs.get64 .rbx).toNat), 0, (2 * (48 - (s.regs.get64 .r14).toNat) + 1), 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 23) rfl]; rfl
@[lex_var] theorem L6a30_2 {s : MachineData} : var "ff_aac_sbr_apply.L6a30_2" s = lex [2, (0), 0, (0), 1, (9 - (s.regs.get64 .rbx).toNat), 0, (2 * (48 - (s.regs.get64 .r14).toNat) + 1), 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 24) rfl]; rfl
@[lex_var] theorem L6a90 {s : MachineData} : var "ff_aac_sbr_apply.L6a90" s = lex [2, (0), 0, (0), 1, (9 - (s.regs.get64 .rbx).toNat), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 25) rfl]; rfl
@[lex_var] theorem L6abf {s : MachineData} : var "ff_aac_sbr_apply.L6abf" s = lex [2, (0), 0, (0), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 26) rfl]; rfl
@[lex_var] theorem L6b00 {s : MachineData} : var "ff_aac_sbr_apply.L6b00" s = lex [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat)), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 27) rfl]; rfl
@[lex_var] theorem L6b02 {s : MachineData} : var "ff_aac_sbr_apply.L6b02" s = lex [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat)), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 28) rfl]; rfl
@[lex_var] theorem L6b12 {s : MachineData} : var "ff_aac_sbr_apply.L6b12" s = lex [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 29) rfl]; rfl
@[lex_var] theorem L6b50 {s : MachineData} : var "ff_aac_sbr_apply.L6b50" s = lex [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 30) rfl]; rfl
@[lex_var] theorem L6b6c {s : MachineData} : var "ff_aac_sbr_apply.L6b6c" s = lex [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 31) rfl]; rfl
@[lex_var] theorem L6ba0 {s : MachineData} : var "ff_aac_sbr_apply.L6ba0" s = lex [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 32) rfl]; rfl
@[lex_var] theorem L6bbc {s : MachineData} : var "ff_aac_sbr_apply.L6bbc" s = lex [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 33) rfl]; rfl
@[lex_var] theorem L6bbc_1 {s : MachineData} : var "ff_aac_sbr_apply.L6bbc_1" s = lex [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 34) rfl]; rfl
@[lex_var] theorem L6c1e {s : MachineData} : var "ff_aac_sbr_apply.L6c1e" s = lex [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 35) rfl]; rfl
@[lex_var] theorem L6c3a {s : MachineData} : var "ff_aac_sbr_apply.L6c3a" s = lex [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 36) rfl]; rfl
@[lex_var] theorem L6c61 {s : MachineData} : var "ff_aac_sbr_apply.L6c61" s = lex [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 37) rfl]; rfl
@[lex_var] theorem L6c7d {s : MachineData} : var "ff_aac_sbr_apply.L6c7d" s = lex [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 38) rfl]; rfl
@[lex_var] theorem L6c7d_1 {s : MachineData} : var "ff_aac_sbr_apply.L6c7d_1" s = lex [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 39) rfl]; rfl
@[lex_var] theorem L6c7d_2 {s : MachineData} : var "ff_aac_sbr_apply.L6c7d_2" s = lex [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 40) rfl]; rfl
@[lex_var] theorem L6ce0 {s : MachineData} : var "ff_aac_sbr_apply.L6ce0" s = lex [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 41) rfl]; rfl
@[lex_var] theorem L6cea {s : MachineData} : var "ff_aac_sbr_apply.L6cea" s = lex [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 42) rfl]; rfl
@[lex_var] theorem L6d09 {s : MachineData} : var "ff_aac_sbr_apply.L6d09" s = lex [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 43) rfl]; rfl
@[lex_var] theorem L6d32 {s : MachineData} : var "ff_aac_sbr_apply.L6d32" s = lex [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 44) rfl]; rfl
@[lex_var] theorem L6d51 {s : MachineData} : var "ff_aac_sbr_apply.L6d51" s = lex [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 45) rfl]; rfl
@[lex_var] theorem L6d51_1 {s : MachineData} : var "ff_aac_sbr_apply.L6d51_1" s = lex [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 46) rfl]; rfl
@[lex_var] theorem L6dbc {s : MachineData} : var "ff_aac_sbr_apply.L6dbc" s = lex [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 47) rfl]; rfl
@[lex_var] theorem L6ddb {s : MachineData} : var "ff_aac_sbr_apply.L6ddb" s = lex [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 48) rfl]; rfl
@[lex_var] theorem L6e04 {s : MachineData} : var "ff_aac_sbr_apply.L6e04" s = lex [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 49) rfl]; rfl
@[lex_var] theorem L6e23 {s : MachineData} : var "ff_aac_sbr_apply.L6e23" s = lex [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 50) rfl]; rfl
@[lex_var] theorem L6e23_1 {s : MachineData} : var "ff_aac_sbr_apply.L6e23_1" s = lex [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 51) rfl]; rfl
@[lex_var] theorem L6e8c {s : MachineData} : var "ff_aac_sbr_apply.L6e8c" s = lex [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 52) rfl]; rfl
@[lex_var] theorem L6ea8 {s : MachineData} : var "ff_aac_sbr_apply.L6ea8" s = lex [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 53) rfl]; rfl
@[lex_var] theorem L6ecf {s : MachineData} : var "ff_aac_sbr_apply.L6ecf" s = lex [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 54) rfl]; rfl
@[lex_var] theorem L6eeb {s : MachineData} : var "ff_aac_sbr_apply.L6eeb" s = lex [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 55) rfl]; rfl
@[lex_var] theorem L6eeb_1 {s : MachineData} : var "ff_aac_sbr_apply.L6eeb_1" s = lex [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 56) rfl]; rfl
@[lex_var] theorem L6eeb_2 {s : MachineData} : var "ff_aac_sbr_apply.L6eeb_2" s = lex [2, (0), 0, (0), 0, (2 * (3 - (s.regs.get64 .rdx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 57) rfl]; rfl
@[lex_var] theorem L6f32 {s : MachineData} : var "ff_aac_sbr_apply.L6f32" s = lex [2, (1), 0, (0), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 58) rfl]; rfl
@[lex_var] theorem L6f32_1 {s : MachineData} : var "ff_aac_sbr_apply.L6f32_1" s = lex [2, (1), 0, (0), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 59) rfl]; rfl
@[lex_var] theorem L6f32_2 {s : MachineData} : var "ff_aac_sbr_apply.L6f32_2" s = lex [2, (1), 0, (0), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 60) rfl]; rfl
@[lex_var] theorem L6fbe {s : MachineData} : var "ff_aac_sbr_apply.L6fbe" s = lex [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 61) rfl]; rfl
@[lex_var] theorem L6fca {s : MachineData} : var "ff_aac_sbr_apply.L6fca" s = lex [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 62) rfl]; rfl
@[lex_var] theorem L6ff7 {s : MachineData} : var "ff_aac_sbr_apply.L6ff7" s = lex [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 63) rfl]; rfl
@[lex_var] theorem L6ffc {s : MachineData} : var "ff_aac_sbr_apply.L6ffc" s = lex [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 0), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 64) rfl]; rfl
@[lex_var] theorem L7007 {s : MachineData} : var "ff_aac_sbr_apply.L7007" s = lex [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 0), 0, (0), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 65) rfl]; rfl
@[lex_var] theorem L700e {s : MachineData} : var "ff_aac_sbr_apply.L700e" s = lex [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 0), 0, (0), 0, (0), 1, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 66) rfl]; rfl
@[lex_var] theorem L7020 {s : MachineData} : var "ff_aac_sbr_apply.L7020" s = lex [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 0), 0, (0), 0, (0), 0, (0), 1, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 67) rfl]; rfl
@[lex_var] theorem L7020_1 {s : MachineData} : var "ff_aac_sbr_apply.L7020_1" s = lex [1, ((if s.regs.get64 .rax = 1#64 then 4 else 0) + 3), 0, (0), 0, (0), 0, (0), 1, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 68) rfl]; rfl
@[lex_var] theorem L7020_2 {s : MachineData} : var "ff_aac_sbr_apply.L7020_2" s = lex [1, ((if s.regs.get64 .rax = 1#64 then 4 else 0) + 3), 0, (0), 0, (0), 0, (0), 1, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 69) rfl]; rfl
@[lex_var] theorem L7044 {s : MachineData} : var "ff_aac_sbr_apply.L7044" s = lex [1, ((if s.regs.get64 .rax = 0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 1, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 70) rfl]; rfl
@[lex_var] theorem L7044_1 {s : MachineData} : var "ff_aac_sbr_apply.L7044_1" s = lex [1, ((if s.regs.get64 .rax = 0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 1, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 71) rfl]; rfl
@[lex_var] theorem L7070 {s : MachineData} : var "ff_aac_sbr_apply.L7070" s = lex [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, (9 - (s.regs.get64 .r15).toNat), 1, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 72) rfl]; rfl
@[lex_var] theorem L7090 {s : MachineData} : var "ff_aac_sbr_apply.L7090" s = lex [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, (9 - (s.regs.get64 .r15).toNat), 0, (3 * (48 - (s.regs.get64 .rbx).toNat) + 1), 1, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 73) rfl]; rfl
@[lex_var] theorem L7090_1 {s : MachineData} : var "ff_aac_sbr_apply.L7090_1" s = lex [1, ((if s.regs.get64 .r13 - slot64 s 0x38 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, (9 - (s.regs.get64 .r15).toNat), 0, (3 * (48 - (s.regs.get64 .rbx).toNat) + 1), 1, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 74) rfl]; rfl
@[lex_var] theorem L7090_2 {s : MachineData} : var "ff_aac_sbr_apply.L7090_2" s = lex [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, (9 - (s.regs.get64 .r15).toNat), 0, (3 * (48 - (s.regs.get64 .rbx).toNat) + 1), 1, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 75) rfl]; rfl
@[lex_var] theorem L70bf {s : MachineData} : var "ff_aac_sbr_apply.L70bf" s = lex [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, (9 - (s.regs.get64 .r15).toNat), 0, (3 * (48 - (s.regs.get64 .rbx).toNat) + 0), 0, (0), 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 76) rfl]; rfl
@[lex_var] theorem L70ca {s : MachineData} : var "ff_aac_sbr_apply.L70ca" s = lex [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, (9 - (s.regs.get64 .r15).toNat), 0, (3 * (48 - (s.regs.get64 .rbx).toNat) + 2), 0, (0), 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 77) rfl]; rfl
@[lex_var] theorem L70ca_1 {s : MachineData} : var "ff_aac_sbr_apply.L70ca_1" s = lex [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, (9 - (s.regs.get64 .r15).toNat), 0, (3 * (48 - (s.regs.get64 .rbx).toNat) + 2), 0, (0), 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 78) rfl]; rfl
@[lex_var] theorem L7120 {s : MachineData} : var "ff_aac_sbr_apply.L7120" s = lex [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, (9 - (s.regs.get64 .r15).toNat), 0, (3 * (48 - (s.regs.get64 .rbx).toNat) + 2), 0, (0), 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 79) rfl]; rfl
@[lex_var] theorem L7140 {s : MachineData} : var "ff_aac_sbr_apply.L7140" s = lex [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, (9 - (s.regs.get64 .r15).toNat), 0, (3 * (48 - (s.regs.get64 .rbx).toNat) + 2), 0, (0), 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 80) rfl]; rfl
@[lex_var] theorem L7166 {s : MachineData} : var "ff_aac_sbr_apply.L7166" s = lex [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, (9 - (s.regs.get64 .r15).toNat), 0, (3 * (48 - (s.regs.get64 .rbx).toNat) + 2), 0, (0), 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 81) rfl]; rfl
@[lex_var] theorem L717f {s : MachineData} : var "ff_aac_sbr_apply.L717f" s = lex [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, (9 - (s.regs.get64 .r15).toNat), 0, (3 * (48 - (s.regs.get64 .rbx).toNat) + 2), 0, (0), 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 82) rfl]; rfl
@[lex_var] theorem L71b0 {s : MachineData} : var "ff_aac_sbr_apply.L71b0" s = lex [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, (9 - (s.regs.get64 .r15).toNat), 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 83) rfl]; rfl
@[lex_var] theorem L71e0 {s : MachineData} : var "ff_aac_sbr_apply.L71e0" s = lex [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 84) rfl]; rfl
@[lex_var] theorem L71e0_1 {s : MachineData} : var "ff_aac_sbr_apply.L71e0_1" s = lex [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 85) rfl]; rfl
@[lex_var] theorem L7226 {s : MachineData} : var "ff_aac_sbr_apply.L7226" s = lex [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 86) rfl]; rfl
@[lex_var] theorem L723c {s : MachineData} : var "ff_aac_sbr_apply.L723c" s = lex [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 87) rfl]; rfl
@[lex_var] theorem L723c_1 {s : MachineData} : var "ff_aac_sbr_apply.L723c_1" s = lex [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 88) rfl]; rfl
@[lex_var] theorem L7270 {s : MachineData} : var "ff_aac_sbr_apply.L7270" s = lex [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 89) rfl]; rfl
@[lex_var] theorem L7286 {s : MachineData} : var "ff_aac_sbr_apply.L7286" s = lex [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 90) rfl]; rfl
@[lex_var] theorem L7286_1 {s : MachineData} : var "ff_aac_sbr_apply.L7286_1" s = lex [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 91) rfl]; rfl
@[lex_var] theorem L72ba {s : MachineData} : var "ff_aac_sbr_apply.L72ba" s = lex [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 92) rfl]; rfl
@[lex_var] theorem L72d0 {s : MachineData} : var "ff_aac_sbr_apply.L72d0" s = lex [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 93) rfl]; rfl
@[lex_var] theorem L72d0_1 {s : MachineData} : var "ff_aac_sbr_apply.L72d0_1" s = lex [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 94) rfl]; rfl
@[lex_var] theorem L7304 {s : MachineData} : var "ff_aac_sbr_apply.L7304" s = lex [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 95) rfl]; rfl
@[lex_var] theorem L731a {s : MachineData} : var "ff_aac_sbr_apply.L731a" s = lex [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 96) rfl]; rfl
@[lex_var] theorem L731a_1 {s : MachineData} : var "ff_aac_sbr_apply.L731a_1" s = lex [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 97) rfl]; rfl
@[lex_var] theorem L734a {s : MachineData} : var "ff_aac_sbr_apply.L734a" s = lex [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 98) rfl]; rfl
@[lex_var] theorem L7360 {s : MachineData} : var "ff_aac_sbr_apply.L7360" s = lex [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 99) rfl]; rfl
@[lex_var] theorem L7370 {s : MachineData} : var "ff_aac_sbr_apply.L7370" s = lex [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 3), 0, (0), 0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 100) rfl]; rfl
@[lex_var] theorem L73a1 {s : MachineData} : var "ff_aac_sbr_apply.L73a1" s = lex [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 2), 0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 101) rfl]; rfl
@[lex_var] theorem L73b7 {s : MachineData} : var "ff_aac_sbr_apply.L73b7" s = lex [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 2), 0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 102) rfl]; rfl
@[lex_var] theorem L73b7_1 {s : MachineData} : var "ff_aac_sbr_apply.L73b7_1" s = lex [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 2), 0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 103) rfl]; rfl
@[lex_var] theorem L73eb {s : MachineData} : var "ff_aac_sbr_apply.L73eb" s = lex [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 2), 0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 104) rfl]; rfl
@[lex_var] theorem L7401 {s : MachineData} : var "ff_aac_sbr_apply.L7401" s = lex [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 2), 0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 105) rfl]; rfl
@[lex_var] theorem L7401_1 {s : MachineData} : var "ff_aac_sbr_apply.L7401_1" s = lex [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 2), 0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 106) rfl]; rfl
@[lex_var] theorem L7435 {s : MachineData} : var "ff_aac_sbr_apply.L7435" s = lex [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 2), 0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 107) rfl]; rfl
@[lex_var] theorem L744b {s : MachineData} : var "ff_aac_sbr_apply.L744b" s = lex [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 2), 0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 108) rfl]; rfl
@[lex_var] theorem L744b_1 {s : MachineData} : var "ff_aac_sbr_apply.L744b_1" s = lex [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 2), 0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 109) rfl]; rfl
@[lex_var] theorem L747f {s : MachineData} : var "ff_aac_sbr_apply.L747f" s = lex [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 2), 0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 110) rfl]; rfl
@[lex_var] theorem L7495 {s : MachineData} : var "ff_aac_sbr_apply.L7495" s = lex [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 2), 0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 111) rfl]; rfl
@[lex_var] theorem L7495_1 {s : MachineData} : var "ff_aac_sbr_apply.L7495_1" s = lex [1, ((if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4) + 2), 0, (0), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 112) rfl]; rfl
@[lex_var] theorem L74de {s : MachineData} : var "ff_aac_sbr_apply.L74de" s = lex [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 113) rfl]; rfl
@[lex_var] theorem L74e9 {s : MachineData} : var "ff_aac_sbr_apply.L74e9" s = lex [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 114) rfl]; rfl
@[lex_var] theorem L74e9_1 {s : MachineData} : var "ff_aac_sbr_apply.L74e9_1" s = lex [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 115) rfl]; rfl
@[lex_var] theorem L74e9_2 {s : MachineData} : var "ff_aac_sbr_apply.L74e9_2" s = lex [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 116) rfl]; rfl
@[lex_var] theorem L74e9_3 {s : MachineData} : var "ff_aac_sbr_apply.L74e9_3" s = lex [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 117) rfl]; rfl
@[lex_var] theorem L74e9_4 {s : MachineData} : var "ff_aac_sbr_apply.L74e9_4" s = lex [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 118) rfl]; rfl
@[lex_var] theorem L7682 {s : MachineData} : var "ff_aac_sbr_apply.L7682" s = lex [0, (2 - (s.regs.get64 .rdx).toNat), 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 119) rfl]; rfl
@[lex_var] theorem L7682_1 {s : MachineData} : var "ff_aac_sbr_apply.L7682_1" s = lex [0, (2 - (s.regs.get64 .rdx).toNat), 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 120) rfl]; rfl
@[lex_var] theorem L7682_2 {s : MachineData} : var "ff_aac_sbr_apply.L7682_2" s = lex [0, (2 - (s.regs.get64 .rdx).toNat), 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 121) rfl]; rfl
@[lex_var] theorem L7682_3 {s : MachineData} : var "ff_aac_sbr_apply.L7682_3" s = lex [0, (2 - (s.regs.get64 .rdx).toNat), 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 122) rfl]; rfl
@[lex_var] theorem L7682_4 {s : MachineData} : var "ff_aac_sbr_apply.L7682_4" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 123) rfl]; rfl
@[lex_var] theorem L7682_5 {s : MachineData} : var "ff_aac_sbr_apply.L7682_5" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 124) rfl]; rfl
@[lex_var] theorem L7682_6 {s : MachineData} : var "ff_aac_sbr_apply.L7682_6" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 125) rfl]; rfl
@[lex_var] theorem L7682_7 {s : MachineData} : var "ff_aac_sbr_apply.L7682_7" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 126) rfl]; rfl
@[lex_var] theorem L7682_8 {s : MachineData} : var "ff_aac_sbr_apply.L7682_8" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 127) rfl]; rfl
@[lex_var] theorem L7750 {s : MachineData} : var "ff_aac_sbr_apply.L7750" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 10, (4096 - (s.regs.get64 .r13).toNat), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 128) rfl]; rfl
@[lex_var] theorem L7750_1 {s : MachineData} : var "ff_aac_sbr_apply.L7750_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 10, (4096 - (s.regs.get64 .r13).toNat), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 129) rfl]; rfl
@[lex_var] theorem L7750_2 {s : MachineData} : var "ff_aac_sbr_apply.L7750_2" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 10, (4096 - (s.regs.get64 .r13).toNat), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 130) rfl]; rfl
@[lex_var] theorem L7750_3 {s : MachineData} : var "ff_aac_sbr_apply.L7750_3" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 10, (4096 - (s.regs.get64 .r13).toNat), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 131) rfl]; rfl
@[lex_var] theorem L7750_4 {s : MachineData} : var "ff_aac_sbr_apply.L7750_4" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 10, (4096 - (s.regs.get64 .r13).toNat), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 132) rfl]; rfl
@[lex_var] theorem L7750_5 {s : MachineData} : var "ff_aac_sbr_apply.L7750_5" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 10, (4096 - (s.regs.get64 .r13).toNat), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 133) rfl]; rfl
@[lex_var] theorem L7750_6 {s : MachineData} : var "ff_aac_sbr_apply.L7750_6" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 134) rfl]; rfl
@[lex_var] theorem L7750_7 {s : MachineData} : var "ff_aac_sbr_apply.L7750_7" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 135) rfl]; rfl
@[lex_var] theorem L7750_8 {s : MachineData} : var "ff_aac_sbr_apply.L7750_8" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 136) rfl]; rfl
@[lex_var] theorem L7866 {s : MachineData} : var "ff_aac_sbr_apply.L7866" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 137) rfl]; rfl
@[lex_var] theorem L7884 {s : MachineData} : var "ff_aac_sbr_apply.L7884" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 138) rfl]; rfl
@[lex_var] theorem L7884_1 {s : MachineData} : var "ff_aac_sbr_apply.L7884_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 139) rfl]; rfl
@[lex_var] theorem L78f2 {s : MachineData} : var "ff_aac_sbr_apply.L78f2" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 140) rfl]; rfl
@[lex_var] theorem L7910 {s : MachineData} : var "ff_aac_sbr_apply.L7910" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 141) rfl]; rfl
@[lex_var] theorem L7910_1 {s : MachineData} : var "ff_aac_sbr_apply.L7910_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 142) rfl]; rfl
@[lex_var] theorem L797e {s : MachineData} : var "ff_aac_sbr_apply.L797e" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 143) rfl]; rfl
@[lex_var] theorem L799c {s : MachineData} : var "ff_aac_sbr_apply.L799c" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 144) rfl]; rfl
@[lex_var] theorem L799c_1 {s : MachineData} : var "ff_aac_sbr_apply.L799c_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 145) rfl]; rfl
@[lex_var] theorem L7a0a {s : MachineData} : var "ff_aac_sbr_apply.L7a0a" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 146) rfl]; rfl
@[lex_var] theorem L7a28 {s : MachineData} : var "ff_aac_sbr_apply.L7a28" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 147) rfl]; rfl
@[lex_var] theorem L7a28_1 {s : MachineData} : var "ff_aac_sbr_apply.L7a28_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 148) rfl]; rfl
@[lex_var] theorem L7a96 {s : MachineData} : var "ff_aac_sbr_apply.L7a96" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 149) rfl]; rfl
@[lex_var] theorem L7ab4 {s : MachineData} : var "ff_aac_sbr_apply.L7ab4" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 150) rfl]; rfl
@[lex_var] theorem L7b00 {s : MachineData} : var "ff_aac_sbr_apply.L7b00" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 151) rfl]; rfl
@[lex_var] theorem L7b00_1 {s : MachineData} : var "ff_aac_sbr_apply.L7b00_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 152) rfl]; rfl
@[lex_var] theorem L7b2d {s : MachineData} : var "ff_aac_sbr_apply.L7b2d" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 9, (6 - (s.regs.get64 .r15).toNat), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 153) rfl]; rfl
@[lex_var] theorem L7b50 {s : MachineData} : var "ff_aac_sbr_apply.L7b50" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 9, (6 - (s.regs.get64 .r15).toNat), 0, (256 - (s.regs.get64 .r14).toNat), 1, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 154) rfl]; rfl
@[lex_var] theorem L7b80 {s : MachineData} : var "ff_aac_sbr_apply.L7b80" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 9, (6 - (s.regs.get64 .r15).toNat), 0, (256 - (s.regs.get64 .r14).toNat), 0, ((s.regs.get64 .rcx).toNat - (s.regs.get64 .rdx).toNat), 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 155) rfl]; rfl
@[lex_var] theorem L7bb0 {s : MachineData} : var "ff_aac_sbr_apply.L7bb0" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 9, (6 - (s.regs.get64 .r15).toNat), 0, (256 - (s.regs.get64 .r14).toNat), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 156) rfl]; rfl
@[lex_var] theorem L7bb3 {s : MachineData} : var "ff_aac_sbr_apply.L7bb3" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 9, (6 - (s.regs.get64 .r15).toNat), 0, (256 - (s.regs.get64 .r14).toNat), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 157) rfl]; rfl
@[lex_var] theorem L7bb3_1 {s : MachineData} : var "ff_aac_sbr_apply.L7bb3_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 9, (6 - (s.regs.get64 .r15).toNat), 0, (256 - (s.regs.get64 .r14).toNat), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 158) rfl]; rfl
@[lex_var] theorem L7bb3_2 {s : MachineData} : var "ff_aac_sbr_apply.L7bb3_2" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 9, (6 - (s.regs.get64 .r15).toNat), 0, (256 - (s.regs.get64 .r14).toNat), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 159) rfl]; rfl
@[lex_var] theorem L7c5d {s : MachineData} : var "ff_aac_sbr_apply.L7c5d" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 9, (6 - (s.regs.get64 .r15).toNat), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 160) rfl]; rfl
@[lex_var] theorem L7c80 {s : MachineData} : var "ff_aac_sbr_apply.L7c80" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 161) rfl]; rfl
@[lex_var] theorem L7c80_1 {s : MachineData} : var "ff_aac_sbr_apply.L7c80_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 162) rfl]; rfl
@[lex_var] theorem L7cb0 {s : MachineData} : var "ff_aac_sbr_apply.L7cb0" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 163) rfl]; rfl
@[lex_var] theorem L7cbf {s : MachineData} : var "ff_aac_sbr_apply.L7cbf" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 164) rfl]; rfl
@[lex_var] theorem L7ce0 {s : MachineData} : var "ff_aac_sbr_apply.L7ce0" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 165) rfl]; rfl
@[lex_var] theorem L7ce4 {s : MachineData} : var "ff_aac_sbr_apply.L7ce4" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 3, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 166) rfl]; rfl
@[lex_var] theorem L7ce4_1 {s : MachineData} : var "ff_aac_sbr_apply.L7ce4_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 3, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 167) rfl]; rfl
@[lex_var] theorem L7ce4_2 {s : MachineData} : var "ff_aac_sbr_apply.L7ce4_2" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 3, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 168) rfl]; rfl
@[lex_var] theorem L7ce4_3 {s : MachineData} : var "ff_aac_sbr_apply.L7ce4_3" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 3, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 169) rfl]; rfl
@[lex_var] theorem L7ce4_4 {s : MachineData} : var "ff_aac_sbr_apply.L7ce4_4" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 3, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 170) rfl]; rfl
@[lex_var] theorem L7ce4_5 {s : MachineData} : var "ff_aac_sbr_apply.L7ce4_5" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 3, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 171) rfl]; rfl
@[lex_var] theorem L7db0 {s : MachineData} : var "ff_aac_sbr_apply.L7db0" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (s.regs.get64 .rcx).toNat), 13, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 172) rfl]; rfl
@[lex_var] theorem L7db0_1 {s : MachineData} : var "ff_aac_sbr_apply.L7db0_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (s.regs.get64 .r14).toNat), 13, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 173) rfl]; rfl
@[lex_var] theorem L7e20 {s : MachineData} : var "ff_aac_sbr_apply.L7e20" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (s.regs.get64 .r14).toNat), 12, (50 - (s.regs.get64 .rdx).toNat), 1, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 174) rfl]; rfl
@[lex_var] theorem L7e29 {s : MachineData} : var "ff_aac_sbr_apply.L7e29" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (s.regs.get64 .r14).toNat), 12, (50 - (s.regs.get64 .rdx).toNat), 1, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 175) rfl]; rfl
@[lex_var] theorem L7e60 {s : MachineData} : var "ff_aac_sbr_apply.L7e60" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (s.regs.get64 .r14).toNat), 12, (51 - (s.regs.get64 .rdx).toNat), 0, (2 ^ 16 + 64 - (s.regs.get64 .rdi).toNat), 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 176) rfl]; rfl
@[lex_var] theorem L7e60_1 {s : MachineData} : var "ff_aac_sbr_apply.L7e60_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (s.regs.get64 .r14).toNat), 12, (51 - (s.regs.get64 .rdx).toNat), 0, (2 ^ 16 + 64 - (s.regs.get64 .rdi).toNat), 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 177) rfl]; rfl
@[lex_var] theorem L7e90 {s : MachineData} : var "ff_aac_sbr_apply.L7e90" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (s.regs.get64 .r14).toNat), 12, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 178) rfl]; rfl
@[lex_var] theorem L7e90_1 {s : MachineData} : var "ff_aac_sbr_apply.L7e90_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 12, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 179) rfl]; rfl
@[lex_var] theorem L7eb6 {s : MachineData} : var "ff_aac_sbr_apply.L7eb6" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 12, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 180) rfl]; rfl
@[lex_var] theorem L7eb6_1 {s : MachineData} : var "ff_aac_sbr_apply.L7eb6_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 12, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 181) rfl]; rfl
@[lex_var] theorem L7f10 {s : MachineData} : var "ff_aac_sbr_apply.L7f10" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 11, (((s.regs.get64 .r11) - (s.regs.get64 .r9)).toNat), 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 182) rfl]; rfl
@[lex_var] theorem L7f36 {s : MachineData} : var "ff_aac_sbr_apply.L7f36" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 11, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 183) rfl]; rfl
@[lex_var] theorem L7f36_1 {s : MachineData} : var "ff_aac_sbr_apply.L7f36_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 11, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 184) rfl]; rfl
@[lex_var] theorem L7f80 {s : MachineData} : var "ff_aac_sbr_apply.L7f80" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 10, ((0x21998#64 - ((s.regs.get64 .rdi) + (s.regs.get64 .r14))).toNat), 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 185) rfl]; rfl
@[lex_var] theorem L7f80_1 {s : MachineData} : var "ff_aac_sbr_apply.L7f80_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 10, ((0x21998#64 - ((s.regs.get64 .rdi) + (s.regs.get64 .r14))).toNat), 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 186) rfl]; rfl
@[lex_var] theorem L8009 {s : MachineData} : var "ff_aac_sbr_apply.L8009" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 10, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 187) rfl]; rfl
@[lex_var] theorem L8050 {s : MachineData} : var "ff_aac_sbr_apply.L8050" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 9, (((s.regs.get64 .r11) - (s.regs.get64 .r9)).toNat), 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 188) rfl]; rfl
@[lex_var] theorem L8077 {s : MachineData} : var "ff_aac_sbr_apply.L8077" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 9, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 189) rfl]; rfl
@[lex_var] theorem L8077_1 {s : MachineData} : var "ff_aac_sbr_apply.L8077_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 9, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 190) rfl]; rfl
@[lex_var] theorem L80c0 {s : MachineData} : var "ff_aac_sbr_apply.L80c0" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 8, ((0x21998#64 - ((s.regs.get64 .rsi) + (s.regs.get64 .r14))).toNat), 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 191) rfl]; rfl
@[lex_var] theorem L80c0_1 {s : MachineData} : var "ff_aac_sbr_apply.L80c0_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 8, ((0x21998#64 - ((s.regs.get64 .rsi) + (s.regs.get64 .r14))).toNat), 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 192) rfl]; rfl
@[lex_var] theorem L814a {s : MachineData} : var "ff_aac_sbr_apply.L814a" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 8, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 193) rfl]; rfl
@[lex_var] theorem L8190 {s : MachineData} : var "ff_aac_sbr_apply.L8190" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 7, (((s.regs.get64 .r11) - (s.regs.get64 .r9)).toNat), 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 194) rfl]; rfl
@[lex_var] theorem L81b7 {s : MachineData} : var "ff_aac_sbr_apply.L81b7" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 7, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 195) rfl]; rfl
@[lex_var] theorem L81b7_1 {s : MachineData} : var "ff_aac_sbr_apply.L81b7_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 7, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 196) rfl]; rfl
@[lex_var] theorem L8200 {s : MachineData} : var "ff_aac_sbr_apply.L8200" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 6, ((0x21998#64 - ((s.regs.get64 .rdi) + (s.regs.get64 .r14))).toNat), 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 197) rfl]; rfl
@[lex_var] theorem L8200_1 {s : MachineData} : var "ff_aac_sbr_apply.L8200_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 6, ((0x21998#64 - ((s.regs.get64 .rdi) + (s.regs.get64 .r14))).toNat), 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 198) rfl]; rfl
@[lex_var] theorem L828a {s : MachineData} : var "ff_aac_sbr_apply.L828a" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 6, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 199) rfl]; rfl
@[lex_var] theorem L82d0 {s : MachineData} : var "ff_aac_sbr_apply.L82d0" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 5, (((s.regs.get64 .r11) - (s.regs.get64 .r9)).toNat), 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 200) rfl]; rfl
@[lex_var] theorem L82f7 {s : MachineData} : var "ff_aac_sbr_apply.L82f7" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 5, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 201) rfl]; rfl
@[lex_var] theorem L82f7_1 {s : MachineData} : var "ff_aac_sbr_apply.L82f7_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 5, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 202) rfl]; rfl
@[lex_var] theorem L8340 {s : MachineData} : var "ff_aac_sbr_apply.L8340" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 4, ((0x21998#64 - ((s.regs.get64 .rsi) + (s.regs.get64 .r14))).toNat), 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 203) rfl]; rfl
@[lex_var] theorem L8340_1 {s : MachineData} : var "ff_aac_sbr_apply.L8340_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 4, ((0x21998#64 - ((s.regs.get64 .rsi) + (s.regs.get64 .r14))).toNat), 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 204) rfl]; rfl
@[lex_var] theorem L83ca {s : MachineData} : var "ff_aac_sbr_apply.L83ca" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 4, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 205) rfl]; rfl
@[lex_var] theorem L8410 {s : MachineData} : var "ff_aac_sbr_apply.L8410" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 3, (((s.regs.get64 .r11) - (s.regs.get64 .r9)).toNat), 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 206) rfl]; rfl
@[lex_var] theorem L8437 {s : MachineData} : var "ff_aac_sbr_apply.L8437" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 3, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 207) rfl]; rfl
@[lex_var] theorem L8437_1 {s : MachineData} : var "ff_aac_sbr_apply.L8437_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 3, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 208) rfl]; rfl
@[lex_var] theorem L8480 {s : MachineData} : var "ff_aac_sbr_apply.L8480" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 2, ((0x21998#64 - ((s.regs.get64 .rdi) + (s.regs.get64 .rbx))).toNat), 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 209) rfl]; rfl
@[lex_var] theorem L8480_1 {s : MachineData} : var "ff_aac_sbr_apply.L8480_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 2, ((0x21998#64 - ((s.regs.get64 .rdi) + (s.regs.get64 .rbx))).toNat), 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 210) rfl]; rfl
@[lex_var] theorem L8509 {s : MachineData} : var "ff_aac_sbr_apply.L8509" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 2, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 211) rfl]; rfl
@[lex_var] theorem L8520 {s : MachineData} : var "ff_aac_sbr_apply.L8520" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 2, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 212) rfl]; rfl
@[lex_var] theorem L8570 {s : MachineData} : var "ff_aac_sbr_apply.L8570" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 1, (50 - (s.regs.get64 .rdi).toNat), 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 213) rfl]; rfl
@[lex_var] theorem L8570_1 {s : MachineData} : var "ff_aac_sbr_apply.L8570_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 1, (50 - (s.regs.get64 .rdi).toNat), 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 214) rfl]; rfl
@[lex_var] theorem L85c0 {s : MachineData} : var "ff_aac_sbr_apply.L85c0" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 1, (50 - (s.regs.get64 .rdi).toNat), 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 215) rfl]; rfl
@[lex_var] theorem L85cd {s : MachineData} : var "ff_aac_sbr_apply.L85cd" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 1, (50 - (s.regs.get64 .rdi).toNat), 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 216) rfl]; rfl
@[lex_var] theorem L85cd_1 {s : MachineData} : var "ff_aac_sbr_apply.L85cd_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 1, (50 - (s.regs.get64 .rdi).toNat), 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 217) rfl]; rfl
@[lex_var] theorem L85cd_2 {s : MachineData} : var "ff_aac_sbr_apply.L85cd_2" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 1, (50 - (s.regs.get64 .rdi).toNat), 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 218) rfl]; rfl
@[lex_var] theorem L8620 {s : MachineData} : var "ff_aac_sbr_apply.L8620" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 1, (50 - (s.regs.get64 .rdi).toNat), 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 219) rfl]; rfl
@[lex_var] theorem L862d {s : MachineData} : var "ff_aac_sbr_apply.L862d" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 1, (50 - (s.regs.get64 .rdi).toNat), 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 220) rfl]; rfl
@[lex_var] theorem L862d_1 {s : MachineData} : var "ff_aac_sbr_apply.L862d_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 1, (51 - (s.regs.get64 .rdi).toNat), 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 221) rfl]; rfl
@[lex_var] theorem L8660 {s : MachineData} : var "ff_aac_sbr_apply.L8660" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 1, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 222) rfl]; rfl
@[lex_var] theorem L86a0 {s : MachineData} : var "ff_aac_sbr_apply.L86a0" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 0, (4 * (48 - (s.regs.get64 .r13).toNat) + 1), 1, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 223) rfl]; rfl
@[lex_var] theorem L86b0 {s : MachineData} : var "ff_aac_sbr_apply.L86b0" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 0, (4 * (48 - (s.regs.get64 .r13).toNat) + 1), 1, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 224) rfl]; rfl
@[lex_var] theorem L86b0_1 {s : MachineData} : var "ff_aac_sbr_apply.L86b0_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 0, (4 * (48 - (s.regs.get64 .r13).toNat) + 3), 1, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 225) rfl]; rfl
@[lex_var] theorem L86d7 {s : MachineData} : var "ff_aac_sbr_apply.L86d7" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 0, (4 * (48 - (s.regs.get64 .r13).toNat) + 3), 1, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 226) rfl]; rfl
@[lex_var] theorem L8700 {s : MachineData} : var "ff_aac_sbr_apply.L8700" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 0, (4 * (48 - (s.regs.get64 .r13).toNat) + 2), 0, ((s.regs.get64 .rdx).toNat), 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 227) rfl]; rfl
@[lex_var] theorem L8720 {s : MachineData} : var "ff_aac_sbr_apply.L8720" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 0, (4 * (48 - (s.regs.get64 .r13).toNat) + 2), 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 228) rfl]; rfl
@[lex_var] theorem L8740 {s : MachineData} : var "ff_aac_sbr_apply.L8740" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 229) rfl]; rfl
@[lex_var] theorem L8740_1 {s : MachineData} : var "ff_aac_sbr_apply.L8740_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, (9 - (slot64 s 0x68).toNat), 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 230) rfl]; rfl
@[lex_var] theorem L8790 {s : MachineData} : var "ff_aac_sbr_apply.L8790" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 231) rfl]; rfl
@[lex_var] theorem L879e {s : MachineData} : var "ff_aac_sbr_apply.L879e" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 232) rfl]; rfl
@[lex_var] theorem L879e_1 {s : MachineData} : var "ff_aac_sbr_apply.L879e_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 233) rfl]; rfl
@[lex_var] theorem L879e_2 {s : MachineData} : var "ff_aac_sbr_apply.L879e_2" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 234) rfl]; rfl
@[lex_var] theorem L8818 {s : MachineData} : var "ff_aac_sbr_apply.L8818" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 235) rfl]; rfl
@[lex_var] theorem L881c {s : MachineData} : var "ff_aac_sbr_apply.L881c" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 236) rfl]; rfl
@[lex_var] theorem L881c_1 {s : MachineData} : var "ff_aac_sbr_apply.L881c_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 237) rfl]; rfl
@[lex_var] theorem L881c_2 {s : MachineData} : var "ff_aac_sbr_apply.L881c_2" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 238) rfl]; rfl
@[lex_var] theorem L881c_3 {s : MachineData} : var "ff_aac_sbr_apply.L881c_3" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 239) rfl]; rfl
@[lex_var] theorem L881c_4 {s : MachineData} : var "ff_aac_sbr_apply.L881c_4" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 2, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 240) rfl]; rfl
@[lex_var] theorem L8900 {s : MachineData} : var "ff_aac_sbr_apply.L8900" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 1, (2 * (48 - (s.regs.get64 .rbx).toNat)), 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 241) rfl]; rfl
@[lex_var] theorem L8900_1 {s : MachineData} : var "ff_aac_sbr_apply.L8900_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 1, (2 * (48 - (s.regs.get64 .rbx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 242) rfl]; rfl
@[lex_var] theorem L8900_2 {s : MachineData} : var "ff_aac_sbr_apply.L8900_2" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 1, (2 * (48 - (s.regs.get64 .rbx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 243) rfl]; rfl
@[lex_var] theorem L8947 {s : MachineData} : var "ff_aac_sbr_apply.L8947" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 1, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 244) rfl]; rfl
@[lex_var] theorem L8947_1 {s : MachineData} : var "ff_aac_sbr_apply.L8947_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 1, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 245) rfl]; rfl
@[lex_var] theorem L8970 {s : MachineData} : var "ff_aac_sbr_apply.L8970" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 0, (2 * (9 - (s.regs.get64 .r8).toNat)), 1, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 246) rfl]; rfl
@[lex_var] theorem L8970_1 {s : MachineData} : var "ff_aac_sbr_apply.L8970_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 0, (2 * (9 - (s.regs.get64 .r8).toNat) + 2), 1, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 247) rfl]; rfl
@[lex_var] theorem L89e0 {s : MachineData} : var "ff_aac_sbr_apply.L89e0" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 0, (2 * (9 - (slot64 s 0x68).toNat) + 1), 0, (2 * (50 - (s.regs.get64 .rbx).toNat)), 2, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 248) rfl]; rfl
@[lex_var] theorem L89f3 {s : MachineData} : var "ff_aac_sbr_apply.L89f3" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 0, (2 * (9 - (slot64 s 0x68).toNat) + 1), 0, (2 * (50 - (s.regs.get64 .rbx).toNat)), 2, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 249) rfl]; rfl
@[lex_var] theorem L89f3_1 {s : MachineData} : var "ff_aac_sbr_apply.L89f3_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 0, (2 * (9 - (slot64 s 0x68).toNat) + 1), 0, (2 * (50 - (s.regs.get64 .rbx).toNat) + 1), 2, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 250) rfl]; rfl
@[lex_var] theorem L8a50 {s : MachineData} : var "ff_aac_sbr_apply.L8a50" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 0, (2 * (9 - (slot64 s 0x68).toNat) + 1), 0, (2 * (50 - (s.regs.get64 .rbx).toNat) + 1), 1, (64 - (s.regs.get64 .r13).toNat), 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 251) rfl]; rfl
@[lex_var] theorem L8a50_1 {s : MachineData} : var "ff_aac_sbr_apply.L8a50_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 0, (2 * (9 - (slot64 s 0x68).toNat) + 1), 0, (2 * (50 - (s.regs.get64 .rbx).toNat) + 1), 1, (64 - (s.regs.get64 .r13).toNat), 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 252) rfl]; rfl
@[lex_var] theorem L8a50_2 {s : MachineData} : var "ff_aac_sbr_apply.L8a50_2" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 0, (2 * (9 - (slot64 s 0x68).toNat) + 1), 0, (2 * (50 - (s.regs.get64 .rbx).toNat) + 1), 1, (64 - (s.regs.get64 .r13).toNat), 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 253) rfl]; rfl
@[lex_var] theorem L8a50_3 {s : MachineData} : var "ff_aac_sbr_apply.L8a50_3" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 0, (2 * (9 - (slot64 s 0x68).toNat) + 1), 0, (2 * (50 - (s.regs.get64 .rbx).toNat) + 1), 1, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 254) rfl]; rfl
@[lex_var] theorem L8ad0 {s : MachineData} : var "ff_aac_sbr_apply.L8ad0" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 0, (2 * (9 - (slot64 s 0x68).toNat) + 1), 0, (2 * (50 - (s.regs.get64 .rbx).toNat) + 1), 0, (48 - (s.regs.get64 .rcx).toNat), 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 255) rfl]; rfl
@[lex_var] theorem L8ad0_1 {s : MachineData} : var "ff_aac_sbr_apply.L8ad0_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 0, (2 * (9 - (slot64 s 0x68).toNat) + 1), 0, (2 * (50 - (s.regs.get64 .rbx).toNat) + 1), 0, (48 - (s.regs.get64 .rcx).toNat), 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 256) rfl]; rfl
@[lex_var] theorem L8b00 {s : MachineData} : var "ff_aac_sbr_apply.L8b00" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 0, (2 * (9 - (slot64 s 0x68).toNat) + 1), 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 257) rfl]; rfl
@[lex_var] theorem L8b2a {s : MachineData} : var "ff_aac_sbr_apply.L8b2a" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 258) rfl]; rfl
@[lex_var] theorem L8b4f {s : MachineData} : var "ff_aac_sbr_apply.L8b4f" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, (1), 0, (0), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 259) rfl]; rfl
@[lex_var] theorem L8b6b {s : MachineData} : var "ff_aac_sbr_apply.L8b6b" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 260) rfl]; rfl
@[lex_var] theorem L8b77 {s : MachineData} : var "ff_aac_sbr_apply.L8b77" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 261) rfl]; rfl
@[lex_var] theorem L8b77_1 {s : MachineData} : var "ff_aac_sbr_apply.L8b77_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 262) rfl]; rfl
@[lex_var] theorem L8b77_2 {s : MachineData} : var "ff_aac_sbr_apply.L8b77_2" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 263) rfl]; rfl
@[lex_var] theorem L8bf0 {s : MachineData} : var "ff_aac_sbr_apply.L8bf0" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 7, (2 * (48 - (s.regs.get64 .rbx).toNat)), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 264) rfl]; rfl
@[lex_var] theorem L8bf0_1 {s : MachineData} : var "ff_aac_sbr_apply.L8bf0_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 7, (2 * (48 - (s.regs.get64 .rbx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 265) rfl]; rfl
@[lex_var] theorem L8bf0_2 {s : MachineData} : var "ff_aac_sbr_apply.L8bf0_2" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 7, (2 * (48 - (s.regs.get64 .rbx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 266) rfl]; rfl
@[lex_var] theorem L8c33 {s : MachineData} : var "ff_aac_sbr_apply.L8c33" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 267) rfl]; rfl
@[lex_var] theorem L8c4c {s : MachineData} : var "ff_aac_sbr_apply.L8c4c" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 268) rfl]; rfl
@[lex_var] theorem L8c4c_1 {s : MachineData} : var "ff_aac_sbr_apply.L8c4c_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 269) rfl]; rfl
@[lex_var] theorem L8c4c_2 {s : MachineData} : var "ff_aac_sbr_apply.L8c4c_2" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 270) rfl]; rfl
@[lex_var] theorem L8cc9 {s : MachineData} : var "ff_aac_sbr_apply.L8cc9" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 6, (2 * (48 - (s.regs.get64 .rbx).toNat)), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 271) rfl]; rfl
@[lex_var] theorem L8cc9_1 {s : MachineData} : var "ff_aac_sbr_apply.L8cc9_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 6, (2 * (48 - (s.regs.get64 .rbx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 272) rfl]; rfl
@[lex_var] theorem L8cc9_2 {s : MachineData} : var "ff_aac_sbr_apply.L8cc9_2" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 6, (2 * (48 - (s.regs.get64 .rbx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 273) rfl]; rfl
@[lex_var] theorem L8d0c {s : MachineData} : var "ff_aac_sbr_apply.L8d0c" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 274) rfl]; rfl
@[lex_var] theorem L8d26 {s : MachineData} : var "ff_aac_sbr_apply.L8d26" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 275) rfl]; rfl
@[lex_var] theorem L8d26_1 {s : MachineData} : var "ff_aac_sbr_apply.L8d26_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 276) rfl]; rfl
@[lex_var] theorem L8d26_2 {s : MachineData} : var "ff_aac_sbr_apply.L8d26_2" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 277) rfl]; rfl
@[lex_var] theorem L8da3 {s : MachineData} : var "ff_aac_sbr_apply.L8da3" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 5, (2 * (48 - (s.regs.get64 .rbx).toNat)), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 278) rfl]; rfl
@[lex_var] theorem L8da3_1 {s : MachineData} : var "ff_aac_sbr_apply.L8da3_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 5, (2 * (48 - (s.regs.get64 .rbx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 279) rfl]; rfl
@[lex_var] theorem L8da3_2 {s : MachineData} : var "ff_aac_sbr_apply.L8da3_2" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 5, (2 * (48 - (s.regs.get64 .rbx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 280) rfl]; rfl
@[lex_var] theorem L8de6 {s : MachineData} : var "ff_aac_sbr_apply.L8de6" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 281) rfl]; rfl
@[lex_var] theorem L8dff {s : MachineData} : var "ff_aac_sbr_apply.L8dff" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 282) rfl]; rfl
@[lex_var] theorem L8dff_1 {s : MachineData} : var "ff_aac_sbr_apply.L8dff_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 283) rfl]; rfl
@[lex_var] theorem L8dff_2 {s : MachineData} : var "ff_aac_sbr_apply.L8dff_2" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 284) rfl]; rfl
@[lex_var] theorem L8e7c {s : MachineData} : var "ff_aac_sbr_apply.L8e7c" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 4, (2 * (48 - (s.regs.get64 .rbx).toNat)), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 285) rfl]; rfl
@[lex_var] theorem L8e7c_1 {s : MachineData} : var "ff_aac_sbr_apply.L8e7c_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 4, (2 * (48 - (s.regs.get64 .rbx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 286) rfl]; rfl
@[lex_var] theorem L8e7c_2 {s : MachineData} : var "ff_aac_sbr_apply.L8e7c_2" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 4, (2 * (48 - (s.regs.get64 .rbx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 287) rfl]; rfl
@[lex_var] theorem L8ebf {s : MachineData} : var "ff_aac_sbr_apply.L8ebf" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 288) rfl]; rfl
@[lex_var] theorem L8ed9 {s : MachineData} : var "ff_aac_sbr_apply.L8ed9" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 289) rfl]; rfl
@[lex_var] theorem L8ed9_1 {s : MachineData} : var "ff_aac_sbr_apply.L8ed9_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 290) rfl]; rfl
@[lex_var] theorem L8ed9_2 {s : MachineData} : var "ff_aac_sbr_apply.L8ed9_2" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 291) rfl]; rfl
@[lex_var] theorem L8f56 {s : MachineData} : var "ff_aac_sbr_apply.L8f56" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 3, (2 * (48 - (s.regs.get64 .rbx).toNat)), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 292) rfl]; rfl
@[lex_var] theorem L8f56_1 {s : MachineData} : var "ff_aac_sbr_apply.L8f56_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 3, (2 * (48 - (s.regs.get64 .rbx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 293) rfl]; rfl
@[lex_var] theorem L8f56_2 {s : MachineData} : var "ff_aac_sbr_apply.L8f56_2" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 3, (2 * (48 - (s.regs.get64 .rbx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 294) rfl]; rfl
@[lex_var] theorem L8f93 {s : MachineData} : var "ff_aac_sbr_apply.L8f93" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 295) rfl]; rfl
@[lex_var] theorem L8fa4 {s : MachineData} : var "ff_aac_sbr_apply.L8fa4" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 296) rfl]; rfl
@[lex_var] theorem L8fa4_1 {s : MachineData} : var "ff_aac_sbr_apply.L8fa4_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 297) rfl]; rfl
@[lex_var] theorem L8fa4_2 {s : MachineData} : var "ff_aac_sbr_apply.L8fa4_2" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 298) rfl]; rfl
@[lex_var] theorem L8fa4_3 {s : MachineData} : var "ff_aac_sbr_apply.L8fa4_3" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 299) rfl]; rfl
@[lex_var] theorem L9026 {s : MachineData} : var "ff_aac_sbr_apply.L9026" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 2, (2 * (48 - (s.regs.get64 .rbx).toNat)), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 300) rfl]; rfl
@[lex_var] theorem L9026_1 {s : MachineData} : var "ff_aac_sbr_apply.L9026_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 2, (2 * (48 - (s.regs.get64 .rbx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 301) rfl]; rfl
@[lex_var] theorem L9026_2 {s : MachineData} : var "ff_aac_sbr_apply.L9026_2" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 2, (2 * (48 - (s.regs.get64 .rbx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 302) rfl]; rfl
@[lex_var] theorem L9063 {s : MachineData} : var "ff_aac_sbr_apply.L9063" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 303) rfl]; rfl
@[lex_var] theorem L9070 {s : MachineData} : var "ff_aac_sbr_apply.L9070" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 304) rfl]; rfl
@[lex_var] theorem L907f {s : MachineData} : var "ff_aac_sbr_apply.L907f" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 305) rfl]; rfl
@[lex_var] theorem L907f_1 {s : MachineData} : var "ff_aac_sbr_apply.L907f_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 306) rfl]; rfl
@[lex_var] theorem L907f_2 {s : MachineData} : var "ff_aac_sbr_apply.L907f_2" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 307) rfl]; rfl
@[lex_var] theorem L907f_3 {s : MachineData} : var "ff_aac_sbr_apply.L907f_3" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 308) rfl]; rfl
@[lex_var] theorem L90f9 {s : MachineData} : var "ff_aac_sbr_apply.L90f9" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 1, (2 * (48 - (s.regs.get64 .rbx).toNat)), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 309) rfl]; rfl
@[lex_var] theorem L90f9_1 {s : MachineData} : var "ff_aac_sbr_apply.L90f9_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 1, (2 * (48 - (s.regs.get64 .rbx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 310) rfl]; rfl
@[lex_var] theorem L90f9_2 {s : MachineData} : var "ff_aac_sbr_apply.L90f9_2" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 1, (2 * (48 - (s.regs.get64 .rbx).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 311) rfl]; rfl
@[lex_var] theorem L913a {s : MachineData} : var "ff_aac_sbr_apply.L913a" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 312) rfl]; rfl
@[lex_var] theorem L9146 {s : MachineData} : var "ff_aac_sbr_apply.L9146" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 313) rfl]; rfl
@[lex_var] theorem L914e {s : MachineData} : var "ff_aac_sbr_apply.L914e" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 314) rfl]; rfl
@[lex_var] theorem L914e_1 {s : MachineData} : var "ff_aac_sbr_apply.L914e_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 315) rfl]; rfl
@[lex_var] theorem L914e_2 {s : MachineData} : var "ff_aac_sbr_apply.L914e_2" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 316) rfl]; rfl
@[lex_var] theorem L914e_3 {s : MachineData} : var "ff_aac_sbr_apply.L914e_3" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 317) rfl]; rfl
@[lex_var] theorem L91c0 {s : MachineData} : var "ff_aac_sbr_apply.L91c0" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (s.regs.get64 .r12).toNat) + 1), 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 318) rfl]; rfl
@[lex_var] theorem L91f7 {s : MachineData} : var "ff_aac_sbr_apply.L91f7" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (s.regs.get64 .r12).toNat) + 127), 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 319) rfl]; rfl
@[lex_var] theorem L9206 {s : MachineData} : var "ff_aac_sbr_apply.L9206" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (s.regs.get64 .r12).toNat) + 127), 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 320) rfl]; rfl
@[lex_var] theorem L9215 {s : MachineData} : var "ff_aac_sbr_apply.L9215" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (s.regs.get64 .r12).toNat) + 127), 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 321) rfl]; rfl
@[lex_var] theorem L9215_1 {s : MachineData} : var "ff_aac_sbr_apply.L9215_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (s.regs.get64 .r12).toNat) + 127), 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 322) rfl]; rfl
@[lex_var] theorem L9215_2 {s : MachineData} : var "ff_aac_sbr_apply.L9215_2" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (s.regs.get64 .r12).toNat) + 127), 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 323) rfl]; rfl
@[lex_var] theorem L9215_3 {s : MachineData} : var "ff_aac_sbr_apply.L9215_3" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (s.regs.get64 .r12).toNat) + 127), 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 324) rfl]; rfl
@[lex_var] theorem L9215_4 {s : MachineData} : var "ff_aac_sbr_apply.L9215_4" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (s.regs.get64 .r12).toNat) + 127), 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 325) rfl]; rfl
@[lex_var] theorem L9215_5 {s : MachineData} : var "ff_aac_sbr_apply.L9215_5" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (s.regs.get64 .r12).toNat) + 127), 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 326) rfl]; rfl
@[lex_var] theorem L9290 {s : MachineData} : var "ff_aac_sbr_apply.L9290" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 1), 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 327) rfl]; rfl
@[lex_var] theorem L929e {s : MachineData} : var "ff_aac_sbr_apply.L929e" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (s.regs.get64 .rdx).toNat) + 3), 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 328) rfl]; rfl
@[lex_var] theorem L929e_1 {s : MachineData} : var "ff_aac_sbr_apply.L929e_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 329) rfl]; rfl
@[lex_var] theorem L9300 {s : MachineData} : var "ff_aac_sbr_apply.L9300" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 5, (2 * (64 - (s.regs.get64 .rax).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 330) rfl]; rfl
@[lex_var] theorem L9300_1 {s : MachineData} : var "ff_aac_sbr_apply.L9300_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 5, (2 * (64 - (s.regs.get64 .rax).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 331) rfl]; rfl
@[lex_var] theorem L9300_2 {s : MachineData} : var "ff_aac_sbr_apply.L9300_2" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 5, (2 * (64 - (s.regs.get64 .rax).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 332) rfl]; rfl
@[lex_var] theorem L9370 {s : MachineData} : var "ff_aac_sbr_apply.L9370" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 5, (2 * (64 - (s.regs.get64 .rax).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 333) rfl]; rfl
@[lex_var] theorem L9386 {s : MachineData} : var "ff_aac_sbr_apply.L9386" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 5, (2 * (64 - (s.regs.get64 .rax).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 334) rfl]; rfl
@[lex_var] theorem L9386_1 {s : MachineData} : var "ff_aac_sbr_apply.L9386_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 5, (2 * (64 - (s.regs.get64 .rax).toNat) + 3), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 335) rfl]; rfl
@[lex_var] theorem L93d0 {s : MachineData} : var "ff_aac_sbr_apply.L93d0" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 336) rfl]; rfl
@[lex_var] theorem L93f0 {s : MachineData} : var "ff_aac_sbr_apply.L93f0" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 337) rfl]; rfl
@[lex_var] theorem L93f0_1 {s : MachineData} : var "ff_aac_sbr_apply.L93f0_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 338) rfl]; rfl
@[lex_var] theorem L9440 {s : MachineData} : var "ff_aac_sbr_apply.L9440" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 4, ((s.regs.get64 .r12).toNat), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 339) rfl]; rfl
@[lex_var] theorem L9458 {s : MachineData} : var "ff_aac_sbr_apply.L9458" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 340) rfl]; rfl
@[lex_var] theorem L9470 {s : MachineData} : var "ff_aac_sbr_apply.L9470" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 3, (64 - (s.regs.get64 .rbx).toNat), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 341) rfl]; rfl
@[lex_var] theorem L9470_1 {s : MachineData} : var "ff_aac_sbr_apply.L9470_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 3, (64 - (s.regs.get64 .rbx).toNat), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 342) rfl]; rfl
@[lex_var] theorem L9504 {s : MachineData} : var "ff_aac_sbr_apply.L9504" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 343) rfl]; rfl
@[lex_var] theorem L9520 {s : MachineData} : var "ff_aac_sbr_apply.L9520" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 344) rfl]; rfl
@[lex_var] theorem L952c {s : MachineData} : var "ff_aac_sbr_apply.L952c" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 345) rfl]; rfl
@[lex_var] theorem L9530 {s : MachineData} : var "ff_aac_sbr_apply.L9530" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 346) rfl]; rfl
@[lex_var] theorem L9530_1 {s : MachineData} : var "ff_aac_sbr_apply.L9530_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 347) rfl]; rfl
@[lex_var] theorem L95a0 {s : MachineData} : var "ff_aac_sbr_apply.L95a0" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 2, (2 * (64 - (s.regs.get64 .rax).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 348) rfl]; rfl
@[lex_var] theorem L95a0_1 {s : MachineData} : var "ff_aac_sbr_apply.L95a0_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 2, (2 * (64 - (s.regs.get64 .rax).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 349) rfl]; rfl
@[lex_var] theorem L95a0_2 {s : MachineData} : var "ff_aac_sbr_apply.L95a0_2" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 2, (2 * (64 - (s.regs.get64 .rax).toNat) + 3), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 350) rfl]; rfl
@[lex_var] theorem L9600 {s : MachineData} : var "ff_aac_sbr_apply.L9600" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 351) rfl]; rfl
@[lex_var] theorem L9617 {s : MachineData} : var "ff_aac_sbr_apply.L9617" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 352) rfl]; rfl
@[lex_var] theorem L9617_1 {s : MachineData} : var "ff_aac_sbr_apply.L9617_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 353) rfl]; rfl
@[lex_var] theorem L968d {s : MachineData} : var "ff_aac_sbr_apply.L968d" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 354) rfl]; rfl
@[lex_var] theorem L96d3 {s : MachineData} : var "ff_aac_sbr_apply.L96d3" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 355) rfl]; rfl
@[lex_var] theorem L96e1 {s : MachineData} : var "ff_aac_sbr_apply.L96e1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 1, (0), 1, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 356) rfl]; rfl
@[lex_var] theorem L9720 {s : MachineData} : var "ff_aac_sbr_apply.L9720" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 1, (3 * (64 - (s.regs.get64 .rbx).toNat) + 1), 1, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 357) rfl]; rfl
@[lex_var] theorem L9731 {s : MachineData} : var "ff_aac_sbr_apply.L9731" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 1, (3 * (64 - (s.regs.get64 .rbx).toNat)), 0, (0), 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 358) rfl]; rfl
@[lex_var] theorem L9731_1 {s : MachineData} : var "ff_aac_sbr_apply.L9731_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 1, (3 * (64 - (s.regs.get64 .rbx).toNat)), 0, (0), 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 359) rfl]; rfl
@[lex_var] theorem L97b7 {s : MachineData} : var "ff_aac_sbr_apply.L97b7" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 1, (3 * (64 - (s.regs.get64 .rbx).toNat) + 2), 0, (0), 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 360) rfl]; rfl
@[lex_var] theorem L97f0 {s : MachineData} : var "ff_aac_sbr_apply.L97f0" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 1, (3 * (64 - (s.regs.get64 .rbx).toNat) + 2), 0, (0), 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 361) rfl]; rfl
@[lex_var] theorem L9820 {s : MachineData} : var "ff_aac_sbr_apply.L9820" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 362) rfl]; rfl
@[lex_var] theorem L983f {s : MachineData} : var "ff_aac_sbr_apply.L983f" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 363) rfl]; rfl
@[lex_var] theorem L9860 {s : MachineData} : var "ff_aac_sbr_apply.L9860" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 0, (2 * (64 - (s.regs.get64 .rax).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 364) rfl]; rfl
@[lex_var] theorem L9860_1 {s : MachineData} : var "ff_aac_sbr_apply.L9860_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 0, (2 * (64 - (s.regs.get64 .rax).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 365) rfl]; rfl
@[lex_var] theorem L9860_2 {s : MachineData} : var "ff_aac_sbr_apply.L9860_2" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 0, (2 * (64 - (s.regs.get64 .rax).toNat) + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 366) rfl]; rfl
@[lex_var] theorem L9860_3 {s : MachineData} : var "ff_aac_sbr_apply.L9860_3" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 0, (128 * (8 - (slot64 s 0x58).toNat) + 4 * (30 - (slot64 s 0x50).toNat) + 2), 0, (2 * (64 - (s.regs.get64 .rax).toNat) + 3), 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 367) rfl]; rfl
@[lex_var] theorem L98bc {s : MachineData} : var "ff_aac_sbr_apply.L98bc" s = lex [0, (0), 0, (0), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 368) rfl]; rfl
@[lex_var] theorem L98e0 {s : MachineData} : var "ff_aac_sbr_apply.L98e0" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 369) rfl]; rfl
@[lex_var] theorem L9927 {s : MachineData} : var "ff_aac_sbr_apply.L9927" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 370) rfl]; rfl
@[lex_var] theorem L9934 {s : MachineData} : var "ff_aac_sbr_apply.L9934" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 371) rfl]; rfl
@[lex_var] theorem L9934_1 {s : MachineData} : var "ff_aac_sbr_apply.L9934_1" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 372) rfl]; rfl
@[lex_var] theorem L9934_2 {s : MachineData} : var "ff_aac_sbr_apply.L9934_2" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 373) rfl]; rfl
@[lex_var] theorem L99c6 {s : MachineData} : var "ff_aac_sbr_apply.L99c6" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 374) rfl]; rfl
@[lex_var] theorem L99cf {s : MachineData} : var "ff_aac_sbr_apply.L99cf" s = lex [0, (2 - (slot64 s 0x1a0).toNat), 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 375) rfl]; rfl
@[lex_var] theorem L99e9 {s : MachineData} : var "ff_aac_sbr_apply.L99e9" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 376) rfl]; rfl
@[lex_var] theorem L99ee {s : MachineData} : var "ff_aac_sbr_apply.L99ee" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 377) rfl]; rfl
@[lex_var] theorem L99f3 {s : MachineData} : var "ff_aac_sbr_apply.L99f3" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 378) rfl]; rfl
@[lex_var] theorem L99f8 {s : MachineData} : var "ff_aac_sbr_apply.L99f8" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 379) rfl]; rfl
@[lex_var] theorem L99fd {s : MachineData} : var "ff_aac_sbr_apply.L99fd" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 380) rfl]; rfl
@[lex_var] theorem L9a02 {s : MachineData} : var "ff_aac_sbr_apply.L9a02" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 381) rfl]; rfl
@[lex_var] theorem L9a02_1 {s : MachineData} : var "ff_aac_sbr_apply.L9a02_1" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 382) rfl]; rfl
@[lex_var] theorem L9a50 {s : MachineData} : var "ff_aac_sbr_apply.L9a50" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 383) rfl]; rfl
@[lex_var] theorem L9a55 {s : MachineData} : var "ff_aac_sbr_apply.L9a55" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 384) rfl]; rfl
@[lex_var] theorem L9a5a {s : MachineData} : var "ff_aac_sbr_apply.L9a5a" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 385) rfl]; rfl
@[lex_var] theorem L9a5f {s : MachineData} : var "ff_aac_sbr_apply.L9a5f" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 386) rfl]; rfl
@[lex_var] theorem L9a64 {s : MachineData} : var "ff_aac_sbr_apply.L9a64" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 387) rfl]; rfl
@[lex_var] theorem L9a69 {s : MachineData} : var "ff_aac_sbr_apply.L9a69" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 388) rfl]; rfl
@[lex_var] theorem L9a7d {s : MachineData} : var "ff_aac_sbr_apply.L9a7d" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 389) rfl]; rfl
@[lex_var] theorem L9a85 {s : MachineData} : var "ff_aac_sbr_apply.L9a85" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 390) rfl]; rfl
@[lex_var] theorem L9a85_1 {s : MachineData} : var "ff_aac_sbr_apply.L9a85_1" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 391) rfl]; rfl
@[lex_var] theorem L9a85_2 {s : MachineData} : var "ff_aac_sbr_apply.L9a85_2" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 392) rfl]; rfl
@[lex_var] theorem L9a85_3 {s : MachineData} : var "ff_aac_sbr_apply.L9a85_3" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 393) rfl]; rfl
@[lex_var] theorem L9a85_4 {s : MachineData} : var "ff_aac_sbr_apply.L9a85_4" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 394) rfl]; rfl
@[lex_var] theorem L9b24 {s : MachineData} : var "ff_aac_sbr_apply.L9b24" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 395) rfl]; rfl
@[lex_var] theorem L9b2b {s : MachineData} : var "ff_aac_sbr_apply.L9b2b" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 396) rfl]; rfl
@[lex_var] theorem done {s : MachineData} : var "ff_aac_sbr_apply.done" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 397) rfl]; rfl
@[lex_var] theorem L9b36 {s : MachineData} : var "ff_aac_sbr_apply.L9b36" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 398) rfl]; rfl
@[lex_var] theorem L9b3b {s : MachineData} : var "ff_aac_sbr_apply.L9b3b" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 399) rfl]; rfl
@[lex_var] theorem L9b40 {s : MachineData} : var "ff_aac_sbr_apply.L9b40" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 400) rfl]; rfl
@[lex_var] theorem L9b45 {s : MachineData} : var "ff_aac_sbr_apply.L9b45" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 401) rfl]; rfl
@[lex_var] theorem L9b4a {s : MachineData} : var "ff_aac_sbr_apply.L9b4a" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 402) rfl]; rfl
@[lex_var] theorem L9b4f {s : MachineData} : var "ff_aac_sbr_apply.L9b4f" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 403) rfl]; rfl
@[lex_var] theorem L9b54 {s : MachineData} : var "ff_aac_sbr_apply.L9b54" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 404) rfl]; rfl
@[lex_var] theorem L9b59 {s : MachineData} : var "ff_aac_sbr_apply.L9b59" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 405) rfl]; rfl
@[lex_var] theorem L9b5e {s : MachineData} : var "ff_aac_sbr_apply.L9b5e" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 406) rfl]; rfl
@[lex_var] theorem L9b63 {s : MachineData} : var "ff_aac_sbr_apply.L9b63" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 407) rfl]; rfl
@[lex_var] theorem L9b68 {s : MachineData} : var "ff_aac_sbr_apply.L9b68" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 408) rfl]; rfl
@[lex_var] theorem L9b6d {s : MachineData} : var "ff_aac_sbr_apply.L9b6d" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 409) rfl]; rfl
@[lex_var] theorem L9b72 {s : MachineData} : var "ff_aac_sbr_apply.L9b72" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 410) rfl]; rfl
@[lex_var] theorem L9b77 {s : MachineData} : var "ff_aac_sbr_apply.L9b77" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 411) rfl]; rfl
@[lex_var] theorem L9b7c {s : MachineData} : var "ff_aac_sbr_apply.L9b7c" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 412) rfl]; rfl
@[lex_var] theorem L9b81 {s : MachineData} : var "ff_aac_sbr_apply.L9b81" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 413) rfl]; rfl
@[lex_var] theorem L9b86 {s : MachineData} : var "ff_aac_sbr_apply.L9b86" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 414) rfl]; rfl
@[lex_var] theorem L9b8b {s : MachineData} : var "ff_aac_sbr_apply.L9b8b" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 415) rfl]; rfl
@[lex_var] theorem L9b90 {s : MachineData} : var "ff_aac_sbr_apply.L9b90" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 416) rfl]; rfl
@[lex_var] theorem L9b95 {s : MachineData} : var "ff_aac_sbr_apply.L9b95" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 417) rfl]; rfl
@[lex_var] theorem L9b9a {s : MachineData} : var "ff_aac_sbr_apply.L9b9a" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 418) rfl]; rfl
@[lex_var] theorem L9b9a_1 {s : MachineData} : var "ff_aac_sbr_apply.L9b9a_1" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 419) rfl]; rfl
@[lex_var] theorem L9bc5 {s : MachineData} : var "ff_aac_sbr_apply.L9bc5" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 420) rfl]; rfl
@[lex_var] theorem L9bca {s : MachineData} : var "ff_aac_sbr_apply.L9bca" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 421) rfl]; rfl
@[lex_var] theorem L9bcf {s : MachineData} : var "ff_aac_sbr_apply.L9bcf" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 422) rfl]; rfl
@[lex_var] theorem L9bd4 {s : MachineData} : var "ff_aac_sbr_apply.L9bd4" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 423) rfl]; rfl
@[lex_var] theorem L9bd4_1 {s : MachineData} : var "ff_aac_sbr_apply.L9bd4_1" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 424) rfl]; rfl
@[lex_var] theorem L9bff {s : MachineData} : var "ff_aac_sbr_apply.L9bff" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 425) rfl]; rfl
@[lex_var] theorem L9c04 {s : MachineData} : var "ff_aac_sbr_apply.L9c04" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 426) rfl]; rfl
@[lex_var] theorem L9c09 {s : MachineData} : var "ff_aac_sbr_apply.L9c09" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 427) rfl]; rfl
@[lex_var] theorem L9c0e {s : MachineData} : var "ff_aac_sbr_apply.L9c0e" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 428) rfl]; rfl
@[lex_var] theorem L9c13 {s : MachineData} : var "ff_aac_sbr_apply.L9c13" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 429) rfl]; rfl
@[lex_var] theorem L9c18 {s : MachineData} : var "ff_aac_sbr_apply.L9c18" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 430) rfl]; rfl
@[lex_var] theorem L9c1d {s : MachineData} : var "ff_aac_sbr_apply.L9c1d" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 431) rfl]; rfl
@[lex_var] theorem L9c22 {s : MachineData} : var "ff_aac_sbr_apply.L9c22" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 432) rfl]; rfl
@[lex_var] theorem L9c27 {s : MachineData} : var "ff_aac_sbr_apply.L9c27" s = lex [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := 433) rfl]; rfl
end V

namespace I
@[lex_var] theorem start : Program.blockIdx body "ff_aac_sbr_apply" = 0 := blockIdx_at L.start
@[lex_var] theorem start_1 : Program.blockIdx body "ff_aac_sbr_apply.start_1" = 1 := blockIdx_at L.start_1
@[lex_var] theorem start_2 : Program.blockIdx body "ff_aac_sbr_apply.start_2" = 2 := blockIdx_at L.start_2
@[lex_var] theorem start_3 : Program.blockIdx body "ff_aac_sbr_apply.start_3" = 3 := blockIdx_at L.start_3
@[lex_var] theorem L676e : Program.blockIdx body "ff_aac_sbr_apply.L676e" = 4 := blockIdx_at L.L676e
@[lex_var] theorem L6797 : Program.blockIdx body "ff_aac_sbr_apply.L6797" = 5 := blockIdx_at L.L6797
@[lex_var] theorem L6797_1 : Program.blockIdx body "ff_aac_sbr_apply.L6797_1" = 6 := blockIdx_at L.L6797_1
@[lex_var] theorem L6817 : Program.blockIdx body "ff_aac_sbr_apply.L6817" = 7 := blockIdx_at L.L6817
@[lex_var] theorem L6825 : Program.blockIdx body "ff_aac_sbr_apply.L6825" = 8 := blockIdx_at L.L6825
@[lex_var] theorem L6838 : Program.blockIdx body "ff_aac_sbr_apply.L6838" = 9 := blockIdx_at L.L6838
@[lex_var] theorem L6838_1 : Program.blockIdx body "ff_aac_sbr_apply.L6838_1" = 10 := blockIdx_at L.L6838_1
@[lex_var] theorem L6838_2 : Program.blockIdx body "ff_aac_sbr_apply.L6838_2" = 11 := blockIdx_at L.L6838_2
@[lex_var] theorem L68b0 : Program.blockIdx body "ff_aac_sbr_apply.L68b0" = 12 := blockIdx_at L.L68b0
@[lex_var] theorem L68d0 : Program.blockIdx body "ff_aac_sbr_apply.L68d0" = 13 := blockIdx_at L.L68d0
@[lex_var] theorem L68d0_1 : Program.blockIdx body "ff_aac_sbr_apply.L68d0_1" = 14 := blockIdx_at L.L68d0_1
@[lex_var] theorem L68f8 : Program.blockIdx body "ff_aac_sbr_apply.L68f8" = 15 := blockIdx_at L.L68f8
@[lex_var] theorem L6940 : Program.blockIdx body "ff_aac_sbr_apply.L6940" = 16 := blockIdx_at L.L6940
@[lex_var] theorem L6940_1 : Program.blockIdx body "ff_aac_sbr_apply.L6940_1" = 17 := blockIdx_at L.L6940_1
@[lex_var] theorem L69a4 : Program.blockIdx body "ff_aac_sbr_apply.L69a4" = 18 := blockIdx_at L.L69a4
@[lex_var] theorem L69d0 : Program.blockIdx body "ff_aac_sbr_apply.L69d0" = 19 := blockIdx_at L.L69d0
@[lex_var] theorem L69dd : Program.blockIdx body "ff_aac_sbr_apply.L69dd" = 20 := blockIdx_at L.L69dd
@[lex_var] theorem L6a10 : Program.blockIdx body "ff_aac_sbr_apply.L6a10" = 21 := blockIdx_at L.L6a10
@[lex_var] theorem L6a30 : Program.blockIdx body "ff_aac_sbr_apply.L6a30" = 22 := blockIdx_at L.L6a30
@[lex_var] theorem L6a30_1 : Program.blockIdx body "ff_aac_sbr_apply.L6a30_1" = 23 := blockIdx_at L.L6a30_1
@[lex_var] theorem L6a30_2 : Program.blockIdx body "ff_aac_sbr_apply.L6a30_2" = 24 := blockIdx_at L.L6a30_2
@[lex_var] theorem L6a90 : Program.blockIdx body "ff_aac_sbr_apply.L6a90" = 25 := blockIdx_at L.L6a90
@[lex_var] theorem L6abf : Program.blockIdx body "ff_aac_sbr_apply.L6abf" = 26 := blockIdx_at L.L6abf
@[lex_var] theorem L6b00 : Program.blockIdx body "ff_aac_sbr_apply.L6b00" = 27 := blockIdx_at L.L6b00
@[lex_var] theorem L6b02 : Program.blockIdx body "ff_aac_sbr_apply.L6b02" = 28 := blockIdx_at L.L6b02
@[lex_var] theorem L6b12 : Program.blockIdx body "ff_aac_sbr_apply.L6b12" = 29 := blockIdx_at L.L6b12
@[lex_var] theorem L6b50 : Program.blockIdx body "ff_aac_sbr_apply.L6b50" = 30 := blockIdx_at L.L6b50
@[lex_var] theorem L6b6c : Program.blockIdx body "ff_aac_sbr_apply.L6b6c" = 31 := blockIdx_at L.L6b6c
@[lex_var] theorem L6ba0 : Program.blockIdx body "ff_aac_sbr_apply.L6ba0" = 32 := blockIdx_at L.L6ba0
@[lex_var] theorem L6bbc : Program.blockIdx body "ff_aac_sbr_apply.L6bbc" = 33 := blockIdx_at L.L6bbc
@[lex_var] theorem L6bbc_1 : Program.blockIdx body "ff_aac_sbr_apply.L6bbc_1" = 34 := blockIdx_at L.L6bbc_1
@[lex_var] theorem L6c1e : Program.blockIdx body "ff_aac_sbr_apply.L6c1e" = 35 := blockIdx_at L.L6c1e
@[lex_var] theorem L6c3a : Program.blockIdx body "ff_aac_sbr_apply.L6c3a" = 36 := blockIdx_at L.L6c3a
@[lex_var] theorem L6c61 : Program.blockIdx body "ff_aac_sbr_apply.L6c61" = 37 := blockIdx_at L.L6c61
@[lex_var] theorem L6c7d : Program.blockIdx body "ff_aac_sbr_apply.L6c7d" = 38 := blockIdx_at L.L6c7d
@[lex_var] theorem L6c7d_1 : Program.blockIdx body "ff_aac_sbr_apply.L6c7d_1" = 39 := blockIdx_at L.L6c7d_1
@[lex_var] theorem L6c7d_2 : Program.blockIdx body "ff_aac_sbr_apply.L6c7d_2" = 40 := blockIdx_at L.L6c7d_2
@[lex_var] theorem L6ce0 : Program.blockIdx body "ff_aac_sbr_apply.L6ce0" = 41 := blockIdx_at L.L6ce0
@[lex_var] theorem L6cea : Program.blockIdx body "ff_aac_sbr_apply.L6cea" = 42 := blockIdx_at L.L6cea
@[lex_var] theorem L6d09 : Program.blockIdx body "ff_aac_sbr_apply.L6d09" = 43 := blockIdx_at L.L6d09
@[lex_var] theorem L6d32 : Program.blockIdx body "ff_aac_sbr_apply.L6d32" = 44 := blockIdx_at L.L6d32
@[lex_var] theorem L6d51 : Program.blockIdx body "ff_aac_sbr_apply.L6d51" = 45 := blockIdx_at L.L6d51
@[lex_var] theorem L6d51_1 : Program.blockIdx body "ff_aac_sbr_apply.L6d51_1" = 46 := blockIdx_at L.L6d51_1
@[lex_var] theorem L6dbc : Program.blockIdx body "ff_aac_sbr_apply.L6dbc" = 47 := blockIdx_at L.L6dbc
@[lex_var] theorem L6ddb : Program.blockIdx body "ff_aac_sbr_apply.L6ddb" = 48 := blockIdx_at L.L6ddb
@[lex_var] theorem L6e04 : Program.blockIdx body "ff_aac_sbr_apply.L6e04" = 49 := blockIdx_at L.L6e04
@[lex_var] theorem L6e23 : Program.blockIdx body "ff_aac_sbr_apply.L6e23" = 50 := blockIdx_at L.L6e23
@[lex_var] theorem L6e23_1 : Program.blockIdx body "ff_aac_sbr_apply.L6e23_1" = 51 := blockIdx_at L.L6e23_1
@[lex_var] theorem L6e8c : Program.blockIdx body "ff_aac_sbr_apply.L6e8c" = 52 := blockIdx_at L.L6e8c
@[lex_var] theorem L6ea8 : Program.blockIdx body "ff_aac_sbr_apply.L6ea8" = 53 := blockIdx_at L.L6ea8
@[lex_var] theorem L6ecf : Program.blockIdx body "ff_aac_sbr_apply.L6ecf" = 54 := blockIdx_at L.L6ecf
@[lex_var] theorem L6eeb : Program.blockIdx body "ff_aac_sbr_apply.L6eeb" = 55 := blockIdx_at L.L6eeb
@[lex_var] theorem L6eeb_1 : Program.blockIdx body "ff_aac_sbr_apply.L6eeb_1" = 56 := blockIdx_at L.L6eeb_1
@[lex_var] theorem L6eeb_2 : Program.blockIdx body "ff_aac_sbr_apply.L6eeb_2" = 57 := blockIdx_at L.L6eeb_2
@[lex_var] theorem L6f32 : Program.blockIdx body "ff_aac_sbr_apply.L6f32" = 58 := blockIdx_at L.L6f32
@[lex_var] theorem L6f32_1 : Program.blockIdx body "ff_aac_sbr_apply.L6f32_1" = 59 := blockIdx_at L.L6f32_1
@[lex_var] theorem L6f32_2 : Program.blockIdx body "ff_aac_sbr_apply.L6f32_2" = 60 := blockIdx_at L.L6f32_2
@[lex_var] theorem L6fbe : Program.blockIdx body "ff_aac_sbr_apply.L6fbe" = 61 := blockIdx_at L.L6fbe
@[lex_var] theorem L6fca : Program.blockIdx body "ff_aac_sbr_apply.L6fca" = 62 := blockIdx_at L.L6fca
@[lex_var] theorem L6ff7 : Program.blockIdx body "ff_aac_sbr_apply.L6ff7" = 63 := blockIdx_at L.L6ff7
@[lex_var] theorem L6ffc : Program.blockIdx body "ff_aac_sbr_apply.L6ffc" = 64 := blockIdx_at L.L6ffc
@[lex_var] theorem L7007 : Program.blockIdx body "ff_aac_sbr_apply.L7007" = 65 := blockIdx_at L.L7007
@[lex_var] theorem L700e : Program.blockIdx body "ff_aac_sbr_apply.L700e" = 66 := blockIdx_at L.L700e
@[lex_var] theorem L7020 : Program.blockIdx body "ff_aac_sbr_apply.L7020" = 67 := blockIdx_at L.L7020
@[lex_var] theorem L7020_1 : Program.blockIdx body "ff_aac_sbr_apply.L7020_1" = 68 := blockIdx_at L.L7020_1
@[lex_var] theorem L7020_2 : Program.blockIdx body "ff_aac_sbr_apply.L7020_2" = 69 := blockIdx_at L.L7020_2
@[lex_var] theorem L7044 : Program.blockIdx body "ff_aac_sbr_apply.L7044" = 70 := blockIdx_at L.L7044
@[lex_var] theorem L7044_1 : Program.blockIdx body "ff_aac_sbr_apply.L7044_1" = 71 := blockIdx_at L.L7044_1
@[lex_var] theorem L7070 : Program.blockIdx body "ff_aac_sbr_apply.L7070" = 72 := blockIdx_at L.L7070
@[lex_var] theorem L7090 : Program.blockIdx body "ff_aac_sbr_apply.L7090" = 73 := blockIdx_at L.L7090
@[lex_var] theorem L7090_1 : Program.blockIdx body "ff_aac_sbr_apply.L7090_1" = 74 := blockIdx_at L.L7090_1
@[lex_var] theorem L7090_2 : Program.blockIdx body "ff_aac_sbr_apply.L7090_2" = 75 := blockIdx_at L.L7090_2
@[lex_var] theorem L70bf : Program.blockIdx body "ff_aac_sbr_apply.L70bf" = 76 := blockIdx_at L.L70bf
@[lex_var] theorem L70ca : Program.blockIdx body "ff_aac_sbr_apply.L70ca" = 77 := blockIdx_at L.L70ca
@[lex_var] theorem L70ca_1 : Program.blockIdx body "ff_aac_sbr_apply.L70ca_1" = 78 := blockIdx_at L.L70ca_1
@[lex_var] theorem L7120 : Program.blockIdx body "ff_aac_sbr_apply.L7120" = 79 := blockIdx_at L.L7120
@[lex_var] theorem L7140 : Program.blockIdx body "ff_aac_sbr_apply.L7140" = 80 := blockIdx_at L.L7140
@[lex_var] theorem L7166 : Program.blockIdx body "ff_aac_sbr_apply.L7166" = 81 := blockIdx_at L.L7166
@[lex_var] theorem L717f : Program.blockIdx body "ff_aac_sbr_apply.L717f" = 82 := blockIdx_at L.L717f
@[lex_var] theorem L71b0 : Program.blockIdx body "ff_aac_sbr_apply.L71b0" = 83 := blockIdx_at L.L71b0
@[lex_var] theorem L71e0 : Program.blockIdx body "ff_aac_sbr_apply.L71e0" = 84 := blockIdx_at L.L71e0
@[lex_var] theorem L71e0_1 : Program.blockIdx body "ff_aac_sbr_apply.L71e0_1" = 85 := blockIdx_at L.L71e0_1
@[lex_var] theorem L7226 : Program.blockIdx body "ff_aac_sbr_apply.L7226" = 86 := blockIdx_at L.L7226
@[lex_var] theorem L723c : Program.blockIdx body "ff_aac_sbr_apply.L723c" = 87 := blockIdx_at L.L723c
@[lex_var] theorem L723c_1 : Program.blockIdx body "ff_aac_sbr_apply.L723c_1" = 88 := blockIdx_at L.L723c_1
@[lex_var] theorem L7270 : Program.blockIdx body "ff_aac_sbr_apply.L7270" = 89 := blockIdx_at L.L7270
@[lex_var] theorem L7286 : Program.blockIdx body "ff_aac_sbr_apply.L7286" = 90 := blockIdx_at L.L7286
@[lex_var] theorem L7286_1 : Program.blockIdx body "ff_aac_sbr_apply.L7286_1" = 91 := blockIdx_at L.L7286_1
@[lex_var] theorem L72ba : Program.blockIdx body "ff_aac_sbr_apply.L72ba" = 92 := blockIdx_at L.L72ba
@[lex_var] theorem L72d0 : Program.blockIdx body "ff_aac_sbr_apply.L72d0" = 93 := blockIdx_at L.L72d0
@[lex_var] theorem L72d0_1 : Program.blockIdx body "ff_aac_sbr_apply.L72d0_1" = 94 := blockIdx_at L.L72d0_1
@[lex_var] theorem L7304 : Program.blockIdx body "ff_aac_sbr_apply.L7304" = 95 := blockIdx_at L.L7304
@[lex_var] theorem L731a : Program.blockIdx body "ff_aac_sbr_apply.L731a" = 96 := blockIdx_at L.L731a
@[lex_var] theorem L731a_1 : Program.blockIdx body "ff_aac_sbr_apply.L731a_1" = 97 := blockIdx_at L.L731a_1
@[lex_var] theorem L734a : Program.blockIdx body "ff_aac_sbr_apply.L734a" = 98 := blockIdx_at L.L734a
@[lex_var] theorem L7360 : Program.blockIdx body "ff_aac_sbr_apply.L7360" = 99 := blockIdx_at L.L7360
@[lex_var] theorem L7370 : Program.blockIdx body "ff_aac_sbr_apply.L7370" = 100 := blockIdx_at L.L7370
@[lex_var] theorem L73a1 : Program.blockIdx body "ff_aac_sbr_apply.L73a1" = 101 := blockIdx_at L.L73a1
@[lex_var] theorem L73b7 : Program.blockIdx body "ff_aac_sbr_apply.L73b7" = 102 := blockIdx_at L.L73b7
@[lex_var] theorem L73b7_1 : Program.blockIdx body "ff_aac_sbr_apply.L73b7_1" = 103 := blockIdx_at L.L73b7_1
@[lex_var] theorem L73eb : Program.blockIdx body "ff_aac_sbr_apply.L73eb" = 104 := blockIdx_at L.L73eb
@[lex_var] theorem L7401 : Program.blockIdx body "ff_aac_sbr_apply.L7401" = 105 := blockIdx_at L.L7401
@[lex_var] theorem L7401_1 : Program.blockIdx body "ff_aac_sbr_apply.L7401_1" = 106 := blockIdx_at L.L7401_1
@[lex_var] theorem L7435 : Program.blockIdx body "ff_aac_sbr_apply.L7435" = 107 := blockIdx_at L.L7435
@[lex_var] theorem L744b : Program.blockIdx body "ff_aac_sbr_apply.L744b" = 108 := blockIdx_at L.L744b
@[lex_var] theorem L744b_1 : Program.blockIdx body "ff_aac_sbr_apply.L744b_1" = 109 := blockIdx_at L.L744b_1
@[lex_var] theorem L747f : Program.blockIdx body "ff_aac_sbr_apply.L747f" = 110 := blockIdx_at L.L747f
@[lex_var] theorem L7495 : Program.blockIdx body "ff_aac_sbr_apply.L7495" = 111 := blockIdx_at L.L7495
@[lex_var] theorem L7495_1 : Program.blockIdx body "ff_aac_sbr_apply.L7495_1" = 112 := blockIdx_at L.L7495_1
@[lex_var] theorem L74de : Program.blockIdx body "ff_aac_sbr_apply.L74de" = 113 := blockIdx_at L.L74de
@[lex_var] theorem L74e9 : Program.blockIdx body "ff_aac_sbr_apply.L74e9" = 114 := blockIdx_at L.L74e9
@[lex_var] theorem L74e9_1 : Program.blockIdx body "ff_aac_sbr_apply.L74e9_1" = 115 := blockIdx_at L.L74e9_1
@[lex_var] theorem L74e9_2 : Program.blockIdx body "ff_aac_sbr_apply.L74e9_2" = 116 := blockIdx_at L.L74e9_2
@[lex_var] theorem L74e9_3 : Program.blockIdx body "ff_aac_sbr_apply.L74e9_3" = 117 := blockIdx_at L.L74e9_3
@[lex_var] theorem L74e9_4 : Program.blockIdx body "ff_aac_sbr_apply.L74e9_4" = 118 := blockIdx_at L.L74e9_4
@[lex_var] theorem L7682 : Program.blockIdx body "ff_aac_sbr_apply.L7682" = 119 := blockIdx_at L.L7682
@[lex_var] theorem L7682_1 : Program.blockIdx body "ff_aac_sbr_apply.L7682_1" = 120 := blockIdx_at L.L7682_1
@[lex_var] theorem L7682_2 : Program.blockIdx body "ff_aac_sbr_apply.L7682_2" = 121 := blockIdx_at L.L7682_2
@[lex_var] theorem L7682_3 : Program.blockIdx body "ff_aac_sbr_apply.L7682_3" = 122 := blockIdx_at L.L7682_3
@[lex_var] theorem L7682_4 : Program.blockIdx body "ff_aac_sbr_apply.L7682_4" = 123 := blockIdx_at L.L7682_4
@[lex_var] theorem L7682_5 : Program.blockIdx body "ff_aac_sbr_apply.L7682_5" = 124 := blockIdx_at L.L7682_5
@[lex_var] theorem L7682_6 : Program.blockIdx body "ff_aac_sbr_apply.L7682_6" = 125 := blockIdx_at L.L7682_6
@[lex_var] theorem L7682_7 : Program.blockIdx body "ff_aac_sbr_apply.L7682_7" = 126 := blockIdx_at L.L7682_7
@[lex_var] theorem L7682_8 : Program.blockIdx body "ff_aac_sbr_apply.L7682_8" = 127 := blockIdx_at L.L7682_8
@[lex_var] theorem L7750 : Program.blockIdx body "ff_aac_sbr_apply.L7750" = 128 := blockIdx_at L.L7750
@[lex_var] theorem L7750_1 : Program.blockIdx body "ff_aac_sbr_apply.L7750_1" = 129 := blockIdx_at L.L7750_1
@[lex_var] theorem L7750_2 : Program.blockIdx body "ff_aac_sbr_apply.L7750_2" = 130 := blockIdx_at L.L7750_2
@[lex_var] theorem L7750_3 : Program.blockIdx body "ff_aac_sbr_apply.L7750_3" = 131 := blockIdx_at L.L7750_3
@[lex_var] theorem L7750_4 : Program.blockIdx body "ff_aac_sbr_apply.L7750_4" = 132 := blockIdx_at L.L7750_4
@[lex_var] theorem L7750_5 : Program.blockIdx body "ff_aac_sbr_apply.L7750_5" = 133 := blockIdx_at L.L7750_5
@[lex_var] theorem L7750_6 : Program.blockIdx body "ff_aac_sbr_apply.L7750_6" = 134 := blockIdx_at L.L7750_6
@[lex_var] theorem L7750_7 : Program.blockIdx body "ff_aac_sbr_apply.L7750_7" = 135 := blockIdx_at L.L7750_7
@[lex_var] theorem L7750_8 : Program.blockIdx body "ff_aac_sbr_apply.L7750_8" = 136 := blockIdx_at L.L7750_8
@[lex_var] theorem L7866 : Program.blockIdx body "ff_aac_sbr_apply.L7866" = 137 := blockIdx_at L.L7866
@[lex_var] theorem L7884 : Program.blockIdx body "ff_aac_sbr_apply.L7884" = 138 := blockIdx_at L.L7884
@[lex_var] theorem L7884_1 : Program.blockIdx body "ff_aac_sbr_apply.L7884_1" = 139 := blockIdx_at L.L7884_1
@[lex_var] theorem L78f2 : Program.blockIdx body "ff_aac_sbr_apply.L78f2" = 140 := blockIdx_at L.L78f2
@[lex_var] theorem L7910 : Program.blockIdx body "ff_aac_sbr_apply.L7910" = 141 := blockIdx_at L.L7910
@[lex_var] theorem L7910_1 : Program.blockIdx body "ff_aac_sbr_apply.L7910_1" = 142 := blockIdx_at L.L7910_1
@[lex_var] theorem L797e : Program.blockIdx body "ff_aac_sbr_apply.L797e" = 143 := blockIdx_at L.L797e
@[lex_var] theorem L799c : Program.blockIdx body "ff_aac_sbr_apply.L799c" = 144 := blockIdx_at L.L799c
@[lex_var] theorem L799c_1 : Program.blockIdx body "ff_aac_sbr_apply.L799c_1" = 145 := blockIdx_at L.L799c_1
@[lex_var] theorem L7a0a : Program.blockIdx body "ff_aac_sbr_apply.L7a0a" = 146 := blockIdx_at L.L7a0a
@[lex_var] theorem L7a28 : Program.blockIdx body "ff_aac_sbr_apply.L7a28" = 147 := blockIdx_at L.L7a28
@[lex_var] theorem L7a28_1 : Program.blockIdx body "ff_aac_sbr_apply.L7a28_1" = 148 := blockIdx_at L.L7a28_1
@[lex_var] theorem L7a96 : Program.blockIdx body "ff_aac_sbr_apply.L7a96" = 149 := blockIdx_at L.L7a96
@[lex_var] theorem L7ab4 : Program.blockIdx body "ff_aac_sbr_apply.L7ab4" = 150 := blockIdx_at L.L7ab4
@[lex_var] theorem L7b00 : Program.blockIdx body "ff_aac_sbr_apply.L7b00" = 151 := blockIdx_at L.L7b00
@[lex_var] theorem L7b00_1 : Program.blockIdx body "ff_aac_sbr_apply.L7b00_1" = 152 := blockIdx_at L.L7b00_1
@[lex_var] theorem L7b2d : Program.blockIdx body "ff_aac_sbr_apply.L7b2d" = 153 := blockIdx_at L.L7b2d
@[lex_var] theorem L7b50 : Program.blockIdx body "ff_aac_sbr_apply.L7b50" = 154 := blockIdx_at L.L7b50
@[lex_var] theorem L7b80 : Program.blockIdx body "ff_aac_sbr_apply.L7b80" = 155 := blockIdx_at L.L7b80
@[lex_var] theorem L7bb0 : Program.blockIdx body "ff_aac_sbr_apply.L7bb0" = 156 := blockIdx_at L.L7bb0
@[lex_var] theorem L7bb3 : Program.blockIdx body "ff_aac_sbr_apply.L7bb3" = 157 := blockIdx_at L.L7bb3
@[lex_var] theorem L7bb3_1 : Program.blockIdx body "ff_aac_sbr_apply.L7bb3_1" = 158 := blockIdx_at L.L7bb3_1
@[lex_var] theorem L7bb3_2 : Program.blockIdx body "ff_aac_sbr_apply.L7bb3_2" = 159 := blockIdx_at L.L7bb3_2
@[lex_var] theorem L7c5d : Program.blockIdx body "ff_aac_sbr_apply.L7c5d" = 160 := blockIdx_at L.L7c5d
@[lex_var] theorem L7c80 : Program.blockIdx body "ff_aac_sbr_apply.L7c80" = 161 := blockIdx_at L.L7c80
@[lex_var] theorem L7c80_1 : Program.blockIdx body "ff_aac_sbr_apply.L7c80_1" = 162 := blockIdx_at L.L7c80_1
@[lex_var] theorem L7cb0 : Program.blockIdx body "ff_aac_sbr_apply.L7cb0" = 163 := blockIdx_at L.L7cb0
@[lex_var] theorem L7cbf : Program.blockIdx body "ff_aac_sbr_apply.L7cbf" = 164 := blockIdx_at L.L7cbf
@[lex_var] theorem L7ce0 : Program.blockIdx body "ff_aac_sbr_apply.L7ce0" = 165 := blockIdx_at L.L7ce0
@[lex_var] theorem L7ce4 : Program.blockIdx body "ff_aac_sbr_apply.L7ce4" = 166 := blockIdx_at L.L7ce4
@[lex_var] theorem L7ce4_1 : Program.blockIdx body "ff_aac_sbr_apply.L7ce4_1" = 167 := blockIdx_at L.L7ce4_1
@[lex_var] theorem L7ce4_2 : Program.blockIdx body "ff_aac_sbr_apply.L7ce4_2" = 168 := blockIdx_at L.L7ce4_2
@[lex_var] theorem L7ce4_3 : Program.blockIdx body "ff_aac_sbr_apply.L7ce4_3" = 169 := blockIdx_at L.L7ce4_3
@[lex_var] theorem L7ce4_4 : Program.blockIdx body "ff_aac_sbr_apply.L7ce4_4" = 170 := blockIdx_at L.L7ce4_4
@[lex_var] theorem L7ce4_5 : Program.blockIdx body "ff_aac_sbr_apply.L7ce4_5" = 171 := blockIdx_at L.L7ce4_5
@[lex_var] theorem L7db0 : Program.blockIdx body "ff_aac_sbr_apply.L7db0" = 172 := blockIdx_at L.L7db0
@[lex_var] theorem L7db0_1 : Program.blockIdx body "ff_aac_sbr_apply.L7db0_1" = 173 := blockIdx_at L.L7db0_1
@[lex_var] theorem L7e20 : Program.blockIdx body "ff_aac_sbr_apply.L7e20" = 174 := blockIdx_at L.L7e20
@[lex_var] theorem L7e29 : Program.blockIdx body "ff_aac_sbr_apply.L7e29" = 175 := blockIdx_at L.L7e29
@[lex_var] theorem L7e60 : Program.blockIdx body "ff_aac_sbr_apply.L7e60" = 176 := blockIdx_at L.L7e60
@[lex_var] theorem L7e60_1 : Program.blockIdx body "ff_aac_sbr_apply.L7e60_1" = 177 := blockIdx_at L.L7e60_1
@[lex_var] theorem L7e90 : Program.blockIdx body "ff_aac_sbr_apply.L7e90" = 178 := blockIdx_at L.L7e90
@[lex_var] theorem L7e90_1 : Program.blockIdx body "ff_aac_sbr_apply.L7e90_1" = 179 := blockIdx_at L.L7e90_1
@[lex_var] theorem L7eb6 : Program.blockIdx body "ff_aac_sbr_apply.L7eb6" = 180 := blockIdx_at L.L7eb6
@[lex_var] theorem L7eb6_1 : Program.blockIdx body "ff_aac_sbr_apply.L7eb6_1" = 181 := blockIdx_at L.L7eb6_1
@[lex_var] theorem L7f10 : Program.blockIdx body "ff_aac_sbr_apply.L7f10" = 182 := blockIdx_at L.L7f10
@[lex_var] theorem L7f36 : Program.blockIdx body "ff_aac_sbr_apply.L7f36" = 183 := blockIdx_at L.L7f36
@[lex_var] theorem L7f36_1 : Program.blockIdx body "ff_aac_sbr_apply.L7f36_1" = 184 := blockIdx_at L.L7f36_1
@[lex_var] theorem L7f80 : Program.blockIdx body "ff_aac_sbr_apply.L7f80" = 185 := blockIdx_at L.L7f80
@[lex_var] theorem L7f80_1 : Program.blockIdx body "ff_aac_sbr_apply.L7f80_1" = 186 := blockIdx_at L.L7f80_1
@[lex_var] theorem L8009 : Program.blockIdx body "ff_aac_sbr_apply.L8009" = 187 := blockIdx_at L.L8009
@[lex_var] theorem L8050 : Program.blockIdx body "ff_aac_sbr_apply.L8050" = 188 := blockIdx_at L.L8050
@[lex_var] theorem L8077 : Program.blockIdx body "ff_aac_sbr_apply.L8077" = 189 := blockIdx_at L.L8077
@[lex_var] theorem L8077_1 : Program.blockIdx body "ff_aac_sbr_apply.L8077_1" = 190 := blockIdx_at L.L8077_1
@[lex_var] theorem L80c0 : Program.blockIdx body "ff_aac_sbr_apply.L80c0" = 191 := blockIdx_at L.L80c0
@[lex_var] theorem L80c0_1 : Program.blockIdx body "ff_aac_sbr_apply.L80c0_1" = 192 := blockIdx_at L.L80c0_1
@[lex_var] theorem L814a : Program.blockIdx body "ff_aac_sbr_apply.L814a" = 193 := blockIdx_at L.L814a
@[lex_var] theorem L8190 : Program.blockIdx body "ff_aac_sbr_apply.L8190" = 194 := blockIdx_at L.L8190
@[lex_var] theorem L81b7 : Program.blockIdx body "ff_aac_sbr_apply.L81b7" = 195 := blockIdx_at L.L81b7
@[lex_var] theorem L81b7_1 : Program.blockIdx body "ff_aac_sbr_apply.L81b7_1" = 196 := blockIdx_at L.L81b7_1
@[lex_var] theorem L8200 : Program.blockIdx body "ff_aac_sbr_apply.L8200" = 197 := blockIdx_at L.L8200
@[lex_var] theorem L8200_1 : Program.blockIdx body "ff_aac_sbr_apply.L8200_1" = 198 := blockIdx_at L.L8200_1
@[lex_var] theorem L828a : Program.blockIdx body "ff_aac_sbr_apply.L828a" = 199 := blockIdx_at L.L828a
@[lex_var] theorem L82d0 : Program.blockIdx body "ff_aac_sbr_apply.L82d0" = 200 := blockIdx_at L.L82d0
@[lex_var] theorem L82f7 : Program.blockIdx body "ff_aac_sbr_apply.L82f7" = 201 := blockIdx_at L.L82f7
@[lex_var] theorem L82f7_1 : Program.blockIdx body "ff_aac_sbr_apply.L82f7_1" = 202 := blockIdx_at L.L82f7_1
@[lex_var] theorem L8340 : Program.blockIdx body "ff_aac_sbr_apply.L8340" = 203 := blockIdx_at L.L8340
@[lex_var] theorem L8340_1 : Program.blockIdx body "ff_aac_sbr_apply.L8340_1" = 204 := blockIdx_at L.L8340_1
@[lex_var] theorem L83ca : Program.blockIdx body "ff_aac_sbr_apply.L83ca" = 205 := blockIdx_at L.L83ca
@[lex_var] theorem L8410 : Program.blockIdx body "ff_aac_sbr_apply.L8410" = 206 := blockIdx_at L.L8410
@[lex_var] theorem L8437 : Program.blockIdx body "ff_aac_sbr_apply.L8437" = 207 := blockIdx_at L.L8437
@[lex_var] theorem L8437_1 : Program.blockIdx body "ff_aac_sbr_apply.L8437_1" = 208 := blockIdx_at L.L8437_1
@[lex_var] theorem L8480 : Program.blockIdx body "ff_aac_sbr_apply.L8480" = 209 := blockIdx_at L.L8480
@[lex_var] theorem L8480_1 : Program.blockIdx body "ff_aac_sbr_apply.L8480_1" = 210 := blockIdx_at L.L8480_1
@[lex_var] theorem L8509 : Program.blockIdx body "ff_aac_sbr_apply.L8509" = 211 := blockIdx_at L.L8509
@[lex_var] theorem L8520 : Program.blockIdx body "ff_aac_sbr_apply.L8520" = 212 := blockIdx_at L.L8520
@[lex_var] theorem L8570 : Program.blockIdx body "ff_aac_sbr_apply.L8570" = 213 := blockIdx_at L.L8570
@[lex_var] theorem L8570_1 : Program.blockIdx body "ff_aac_sbr_apply.L8570_1" = 214 := blockIdx_at L.L8570_1
@[lex_var] theorem L85c0 : Program.blockIdx body "ff_aac_sbr_apply.L85c0" = 215 := blockIdx_at L.L85c0
@[lex_var] theorem L85cd : Program.blockIdx body "ff_aac_sbr_apply.L85cd" = 216 := blockIdx_at L.L85cd
@[lex_var] theorem L85cd_1 : Program.blockIdx body "ff_aac_sbr_apply.L85cd_1" = 217 := blockIdx_at L.L85cd_1
@[lex_var] theorem L85cd_2 : Program.blockIdx body "ff_aac_sbr_apply.L85cd_2" = 218 := blockIdx_at L.L85cd_2
@[lex_var] theorem L8620 : Program.blockIdx body "ff_aac_sbr_apply.L8620" = 219 := blockIdx_at L.L8620
@[lex_var] theorem L862d : Program.blockIdx body "ff_aac_sbr_apply.L862d" = 220 := blockIdx_at L.L862d
@[lex_var] theorem L862d_1 : Program.blockIdx body "ff_aac_sbr_apply.L862d_1" = 221 := blockIdx_at L.L862d_1
@[lex_var] theorem L8660 : Program.blockIdx body "ff_aac_sbr_apply.L8660" = 222 := blockIdx_at L.L8660
@[lex_var] theorem L86a0 : Program.blockIdx body "ff_aac_sbr_apply.L86a0" = 223 := blockIdx_at L.L86a0
@[lex_var] theorem L86b0 : Program.blockIdx body "ff_aac_sbr_apply.L86b0" = 224 := blockIdx_at L.L86b0
@[lex_var] theorem L86b0_1 : Program.blockIdx body "ff_aac_sbr_apply.L86b0_1" = 225 := blockIdx_at L.L86b0_1
@[lex_var] theorem L86d7 : Program.blockIdx body "ff_aac_sbr_apply.L86d7" = 226 := blockIdx_at L.L86d7
@[lex_var] theorem L8700 : Program.blockIdx body "ff_aac_sbr_apply.L8700" = 227 := blockIdx_at L.L8700
@[lex_var] theorem L8720 : Program.blockIdx body "ff_aac_sbr_apply.L8720" = 228 := blockIdx_at L.L8720
@[lex_var] theorem L8740 : Program.blockIdx body "ff_aac_sbr_apply.L8740" = 229 := blockIdx_at L.L8740
@[lex_var] theorem L8740_1 : Program.blockIdx body "ff_aac_sbr_apply.L8740_1" = 230 := blockIdx_at L.L8740_1
@[lex_var] theorem L8790 : Program.blockIdx body "ff_aac_sbr_apply.L8790" = 231 := blockIdx_at L.L8790
@[lex_var] theorem L879e : Program.blockIdx body "ff_aac_sbr_apply.L879e" = 232 := blockIdx_at L.L879e
@[lex_var] theorem L879e_1 : Program.blockIdx body "ff_aac_sbr_apply.L879e_1" = 233 := blockIdx_at L.L879e_1
@[lex_var] theorem L879e_2 : Program.blockIdx body "ff_aac_sbr_apply.L879e_2" = 234 := blockIdx_at L.L879e_2
@[lex_var] theorem L8818 : Program.blockIdx body "ff_aac_sbr_apply.L8818" = 235 := blockIdx_at L.L8818
@[lex_var] theorem L881c : Program.blockIdx body "ff_aac_sbr_apply.L881c" = 236 := blockIdx_at L.L881c
@[lex_var] theorem L881c_1 : Program.blockIdx body "ff_aac_sbr_apply.L881c_1" = 237 := blockIdx_at L.L881c_1
@[lex_var] theorem L881c_2 : Program.blockIdx body "ff_aac_sbr_apply.L881c_2" = 238 := blockIdx_at L.L881c_2
@[lex_var] theorem L881c_3 : Program.blockIdx body "ff_aac_sbr_apply.L881c_3" = 239 := blockIdx_at L.L881c_3
@[lex_var] theorem L881c_4 : Program.blockIdx body "ff_aac_sbr_apply.L881c_4" = 240 := blockIdx_at L.L881c_4
@[lex_var] theorem L8900 : Program.blockIdx body "ff_aac_sbr_apply.L8900" = 241 := blockIdx_at L.L8900
@[lex_var] theorem L8900_1 : Program.blockIdx body "ff_aac_sbr_apply.L8900_1" = 242 := blockIdx_at L.L8900_1
@[lex_var] theorem L8900_2 : Program.blockIdx body "ff_aac_sbr_apply.L8900_2" = 243 := blockIdx_at L.L8900_2
@[lex_var] theorem L8947 : Program.blockIdx body "ff_aac_sbr_apply.L8947" = 244 := blockIdx_at L.L8947
@[lex_var] theorem L8947_1 : Program.blockIdx body "ff_aac_sbr_apply.L8947_1" = 245 := blockIdx_at L.L8947_1
@[lex_var] theorem L8970 : Program.blockIdx body "ff_aac_sbr_apply.L8970" = 246 := blockIdx_at L.L8970
@[lex_var] theorem L8970_1 : Program.blockIdx body "ff_aac_sbr_apply.L8970_1" = 247 := blockIdx_at L.L8970_1
@[lex_var] theorem L89e0 : Program.blockIdx body "ff_aac_sbr_apply.L89e0" = 248 := blockIdx_at L.L89e0
@[lex_var] theorem L89f3 : Program.blockIdx body "ff_aac_sbr_apply.L89f3" = 249 := blockIdx_at L.L89f3
@[lex_var] theorem L89f3_1 : Program.blockIdx body "ff_aac_sbr_apply.L89f3_1" = 250 := blockIdx_at L.L89f3_1
@[lex_var] theorem L8a50 : Program.blockIdx body "ff_aac_sbr_apply.L8a50" = 251 := blockIdx_at L.L8a50
@[lex_var] theorem L8a50_1 : Program.blockIdx body "ff_aac_sbr_apply.L8a50_1" = 252 := blockIdx_at L.L8a50_1
@[lex_var] theorem L8a50_2 : Program.blockIdx body "ff_aac_sbr_apply.L8a50_2" = 253 := blockIdx_at L.L8a50_2
@[lex_var] theorem L8a50_3 : Program.blockIdx body "ff_aac_sbr_apply.L8a50_3" = 254 := blockIdx_at L.L8a50_3
@[lex_var] theorem L8ad0 : Program.blockIdx body "ff_aac_sbr_apply.L8ad0" = 255 := blockIdx_at L.L8ad0
@[lex_var] theorem L8ad0_1 : Program.blockIdx body "ff_aac_sbr_apply.L8ad0_1" = 256 := blockIdx_at L.L8ad0_1
@[lex_var] theorem L8b00 : Program.blockIdx body "ff_aac_sbr_apply.L8b00" = 257 := blockIdx_at L.L8b00
@[lex_var] theorem L8b2a : Program.blockIdx body "ff_aac_sbr_apply.L8b2a" = 258 := blockIdx_at L.L8b2a
@[lex_var] theorem L8b4f : Program.blockIdx body "ff_aac_sbr_apply.L8b4f" = 259 := blockIdx_at L.L8b4f
@[lex_var] theorem L8b6b : Program.blockIdx body "ff_aac_sbr_apply.L8b6b" = 260 := blockIdx_at L.L8b6b
@[lex_var] theorem L8b77 : Program.blockIdx body "ff_aac_sbr_apply.L8b77" = 261 := blockIdx_at L.L8b77
@[lex_var] theorem L8b77_1 : Program.blockIdx body "ff_aac_sbr_apply.L8b77_1" = 262 := blockIdx_at L.L8b77_1
@[lex_var] theorem L8b77_2 : Program.blockIdx body "ff_aac_sbr_apply.L8b77_2" = 263 := blockIdx_at L.L8b77_2
@[lex_var] theorem L8bf0 : Program.blockIdx body "ff_aac_sbr_apply.L8bf0" = 264 := blockIdx_at L.L8bf0
@[lex_var] theorem L8bf0_1 : Program.blockIdx body "ff_aac_sbr_apply.L8bf0_1" = 265 := blockIdx_at L.L8bf0_1
@[lex_var] theorem L8bf0_2 : Program.blockIdx body "ff_aac_sbr_apply.L8bf0_2" = 266 := blockIdx_at L.L8bf0_2
@[lex_var] theorem L8c33 : Program.blockIdx body "ff_aac_sbr_apply.L8c33" = 267 := blockIdx_at L.L8c33
@[lex_var] theorem L8c4c : Program.blockIdx body "ff_aac_sbr_apply.L8c4c" = 268 := blockIdx_at L.L8c4c
@[lex_var] theorem L8c4c_1 : Program.blockIdx body "ff_aac_sbr_apply.L8c4c_1" = 269 := blockIdx_at L.L8c4c_1
@[lex_var] theorem L8c4c_2 : Program.blockIdx body "ff_aac_sbr_apply.L8c4c_2" = 270 := blockIdx_at L.L8c4c_2
@[lex_var] theorem L8cc9 : Program.blockIdx body "ff_aac_sbr_apply.L8cc9" = 271 := blockIdx_at L.L8cc9
@[lex_var] theorem L8cc9_1 : Program.blockIdx body "ff_aac_sbr_apply.L8cc9_1" = 272 := blockIdx_at L.L8cc9_1
@[lex_var] theorem L8cc9_2 : Program.blockIdx body "ff_aac_sbr_apply.L8cc9_2" = 273 := blockIdx_at L.L8cc9_2
@[lex_var] theorem L8d0c : Program.blockIdx body "ff_aac_sbr_apply.L8d0c" = 274 := blockIdx_at L.L8d0c
@[lex_var] theorem L8d26 : Program.blockIdx body "ff_aac_sbr_apply.L8d26" = 275 := blockIdx_at L.L8d26
@[lex_var] theorem L8d26_1 : Program.blockIdx body "ff_aac_sbr_apply.L8d26_1" = 276 := blockIdx_at L.L8d26_1
@[lex_var] theorem L8d26_2 : Program.blockIdx body "ff_aac_sbr_apply.L8d26_2" = 277 := blockIdx_at L.L8d26_2
@[lex_var] theorem L8da3 : Program.blockIdx body "ff_aac_sbr_apply.L8da3" = 278 := blockIdx_at L.L8da3
@[lex_var] theorem L8da3_1 : Program.blockIdx body "ff_aac_sbr_apply.L8da3_1" = 279 := blockIdx_at L.L8da3_1
@[lex_var] theorem L8da3_2 : Program.blockIdx body "ff_aac_sbr_apply.L8da3_2" = 280 := blockIdx_at L.L8da3_2
@[lex_var] theorem L8de6 : Program.blockIdx body "ff_aac_sbr_apply.L8de6" = 281 := blockIdx_at L.L8de6
@[lex_var] theorem L8dff : Program.blockIdx body "ff_aac_sbr_apply.L8dff" = 282 := blockIdx_at L.L8dff
@[lex_var] theorem L8dff_1 : Program.blockIdx body "ff_aac_sbr_apply.L8dff_1" = 283 := blockIdx_at L.L8dff_1
@[lex_var] theorem L8dff_2 : Program.blockIdx body "ff_aac_sbr_apply.L8dff_2" = 284 := blockIdx_at L.L8dff_2
@[lex_var] theorem L8e7c : Program.blockIdx body "ff_aac_sbr_apply.L8e7c" = 285 := blockIdx_at L.L8e7c
@[lex_var] theorem L8e7c_1 : Program.blockIdx body "ff_aac_sbr_apply.L8e7c_1" = 286 := blockIdx_at L.L8e7c_1
@[lex_var] theorem L8e7c_2 : Program.blockIdx body "ff_aac_sbr_apply.L8e7c_2" = 287 := blockIdx_at L.L8e7c_2
@[lex_var] theorem L8ebf : Program.blockIdx body "ff_aac_sbr_apply.L8ebf" = 288 := blockIdx_at L.L8ebf
@[lex_var] theorem L8ed9 : Program.blockIdx body "ff_aac_sbr_apply.L8ed9" = 289 := blockIdx_at L.L8ed9
@[lex_var] theorem L8ed9_1 : Program.blockIdx body "ff_aac_sbr_apply.L8ed9_1" = 290 := blockIdx_at L.L8ed9_1
@[lex_var] theorem L8ed9_2 : Program.blockIdx body "ff_aac_sbr_apply.L8ed9_2" = 291 := blockIdx_at L.L8ed9_2
@[lex_var] theorem L8f56 : Program.blockIdx body "ff_aac_sbr_apply.L8f56" = 292 := blockIdx_at L.L8f56
@[lex_var] theorem L8f56_1 : Program.blockIdx body "ff_aac_sbr_apply.L8f56_1" = 293 := blockIdx_at L.L8f56_1
@[lex_var] theorem L8f56_2 : Program.blockIdx body "ff_aac_sbr_apply.L8f56_2" = 294 := blockIdx_at L.L8f56_2
@[lex_var] theorem L8f93 : Program.blockIdx body "ff_aac_sbr_apply.L8f93" = 295 := blockIdx_at L.L8f93
@[lex_var] theorem L8fa4 : Program.blockIdx body "ff_aac_sbr_apply.L8fa4" = 296 := blockIdx_at L.L8fa4
@[lex_var] theorem L8fa4_1 : Program.blockIdx body "ff_aac_sbr_apply.L8fa4_1" = 297 := blockIdx_at L.L8fa4_1
@[lex_var] theorem L8fa4_2 : Program.blockIdx body "ff_aac_sbr_apply.L8fa4_2" = 298 := blockIdx_at L.L8fa4_2
@[lex_var] theorem L8fa4_3 : Program.blockIdx body "ff_aac_sbr_apply.L8fa4_3" = 299 := blockIdx_at L.L8fa4_3
@[lex_var] theorem L9026 : Program.blockIdx body "ff_aac_sbr_apply.L9026" = 300 := blockIdx_at L.L9026
@[lex_var] theorem L9026_1 : Program.blockIdx body "ff_aac_sbr_apply.L9026_1" = 301 := blockIdx_at L.L9026_1
@[lex_var] theorem L9026_2 : Program.blockIdx body "ff_aac_sbr_apply.L9026_2" = 302 := blockIdx_at L.L9026_2
@[lex_var] theorem L9063 : Program.blockIdx body "ff_aac_sbr_apply.L9063" = 303 := blockIdx_at L.L9063
@[lex_var] theorem L9070 : Program.blockIdx body "ff_aac_sbr_apply.L9070" = 304 := blockIdx_at L.L9070
@[lex_var] theorem L907f : Program.blockIdx body "ff_aac_sbr_apply.L907f" = 305 := blockIdx_at L.L907f
@[lex_var] theorem L907f_1 : Program.blockIdx body "ff_aac_sbr_apply.L907f_1" = 306 := blockIdx_at L.L907f_1
@[lex_var] theorem L907f_2 : Program.blockIdx body "ff_aac_sbr_apply.L907f_2" = 307 := blockIdx_at L.L907f_2
@[lex_var] theorem L907f_3 : Program.blockIdx body "ff_aac_sbr_apply.L907f_3" = 308 := blockIdx_at L.L907f_3
@[lex_var] theorem L90f9 : Program.blockIdx body "ff_aac_sbr_apply.L90f9" = 309 := blockIdx_at L.L90f9
@[lex_var] theorem L90f9_1 : Program.blockIdx body "ff_aac_sbr_apply.L90f9_1" = 310 := blockIdx_at L.L90f9_1
@[lex_var] theorem L90f9_2 : Program.blockIdx body "ff_aac_sbr_apply.L90f9_2" = 311 := blockIdx_at L.L90f9_2
@[lex_var] theorem L913a : Program.blockIdx body "ff_aac_sbr_apply.L913a" = 312 := blockIdx_at L.L913a
@[lex_var] theorem L9146 : Program.blockIdx body "ff_aac_sbr_apply.L9146" = 313 := blockIdx_at L.L9146
@[lex_var] theorem L914e : Program.blockIdx body "ff_aac_sbr_apply.L914e" = 314 := blockIdx_at L.L914e
@[lex_var] theorem L914e_1 : Program.blockIdx body "ff_aac_sbr_apply.L914e_1" = 315 := blockIdx_at L.L914e_1
@[lex_var] theorem L914e_2 : Program.blockIdx body "ff_aac_sbr_apply.L914e_2" = 316 := blockIdx_at L.L914e_2
@[lex_var] theorem L914e_3 : Program.blockIdx body "ff_aac_sbr_apply.L914e_3" = 317 := blockIdx_at L.L914e_3
@[lex_var] theorem L91c0 : Program.blockIdx body "ff_aac_sbr_apply.L91c0" = 318 := blockIdx_at L.L91c0
@[lex_var] theorem L91f7 : Program.blockIdx body "ff_aac_sbr_apply.L91f7" = 319 := blockIdx_at L.L91f7
@[lex_var] theorem L9206 : Program.blockIdx body "ff_aac_sbr_apply.L9206" = 320 := blockIdx_at L.L9206
@[lex_var] theorem L9215 : Program.blockIdx body "ff_aac_sbr_apply.L9215" = 321 := blockIdx_at L.L9215
@[lex_var] theorem L9215_1 : Program.blockIdx body "ff_aac_sbr_apply.L9215_1" = 322 := blockIdx_at L.L9215_1
@[lex_var] theorem L9215_2 : Program.blockIdx body "ff_aac_sbr_apply.L9215_2" = 323 := blockIdx_at L.L9215_2
@[lex_var] theorem L9215_3 : Program.blockIdx body "ff_aac_sbr_apply.L9215_3" = 324 := blockIdx_at L.L9215_3
@[lex_var] theorem L9215_4 : Program.blockIdx body "ff_aac_sbr_apply.L9215_4" = 325 := blockIdx_at L.L9215_4
@[lex_var] theorem L9215_5 : Program.blockIdx body "ff_aac_sbr_apply.L9215_5" = 326 := blockIdx_at L.L9215_5
@[lex_var] theorem L9290 : Program.blockIdx body "ff_aac_sbr_apply.L9290" = 327 := blockIdx_at L.L9290
@[lex_var] theorem L929e : Program.blockIdx body "ff_aac_sbr_apply.L929e" = 328 := blockIdx_at L.L929e
@[lex_var] theorem L929e_1 : Program.blockIdx body "ff_aac_sbr_apply.L929e_1" = 329 := blockIdx_at L.L929e_1
@[lex_var] theorem L9300 : Program.blockIdx body "ff_aac_sbr_apply.L9300" = 330 := blockIdx_at L.L9300
@[lex_var] theorem L9300_1 : Program.blockIdx body "ff_aac_sbr_apply.L9300_1" = 331 := blockIdx_at L.L9300_1
@[lex_var] theorem L9300_2 : Program.blockIdx body "ff_aac_sbr_apply.L9300_2" = 332 := blockIdx_at L.L9300_2
@[lex_var] theorem L9370 : Program.blockIdx body "ff_aac_sbr_apply.L9370" = 333 := blockIdx_at L.L9370
@[lex_var] theorem L9386 : Program.blockIdx body "ff_aac_sbr_apply.L9386" = 334 := blockIdx_at L.L9386
@[lex_var] theorem L9386_1 : Program.blockIdx body "ff_aac_sbr_apply.L9386_1" = 335 := blockIdx_at L.L9386_1
@[lex_var] theorem L93d0 : Program.blockIdx body "ff_aac_sbr_apply.L93d0" = 336 := blockIdx_at L.L93d0
@[lex_var] theorem L93f0 : Program.blockIdx body "ff_aac_sbr_apply.L93f0" = 337 := blockIdx_at L.L93f0
@[lex_var] theorem L93f0_1 : Program.blockIdx body "ff_aac_sbr_apply.L93f0_1" = 338 := blockIdx_at L.L93f0_1
@[lex_var] theorem L9440 : Program.blockIdx body "ff_aac_sbr_apply.L9440" = 339 := blockIdx_at L.L9440
@[lex_var] theorem L9458 : Program.blockIdx body "ff_aac_sbr_apply.L9458" = 340 := blockIdx_at L.L9458
@[lex_var] theorem L9470 : Program.blockIdx body "ff_aac_sbr_apply.L9470" = 341 := blockIdx_at L.L9470
@[lex_var] theorem L9470_1 : Program.blockIdx body "ff_aac_sbr_apply.L9470_1" = 342 := blockIdx_at L.L9470_1
@[lex_var] theorem L9504 : Program.blockIdx body "ff_aac_sbr_apply.L9504" = 343 := blockIdx_at L.L9504
@[lex_var] theorem L9520 : Program.blockIdx body "ff_aac_sbr_apply.L9520" = 344 := blockIdx_at L.L9520
@[lex_var] theorem L952c : Program.blockIdx body "ff_aac_sbr_apply.L952c" = 345 := blockIdx_at L.L952c
@[lex_var] theorem L9530 : Program.blockIdx body "ff_aac_sbr_apply.L9530" = 346 := blockIdx_at L.L9530
@[lex_var] theorem L9530_1 : Program.blockIdx body "ff_aac_sbr_apply.L9530_1" = 347 := blockIdx_at L.L9530_1
@[lex_var] theorem L95a0 : Program.blockIdx body "ff_aac_sbr_apply.L95a0" = 348 := blockIdx_at L.L95a0
@[lex_var] theorem L95a0_1 : Program.blockIdx body "ff_aac_sbr_apply.L95a0_1" = 349 := blockIdx_at L.L95a0_1
@[lex_var] theorem L95a0_2 : Program.blockIdx body "ff_aac_sbr_apply.L95a0_2" = 350 := blockIdx_at L.L95a0_2
@[lex_var] theorem L9600 : Program.blockIdx body "ff_aac_sbr_apply.L9600" = 351 := blockIdx_at L.L9600
@[lex_var] theorem L9617 : Program.blockIdx body "ff_aac_sbr_apply.L9617" = 352 := blockIdx_at L.L9617
@[lex_var] theorem L9617_1 : Program.blockIdx body "ff_aac_sbr_apply.L9617_1" = 353 := blockIdx_at L.L9617_1
@[lex_var] theorem L968d : Program.blockIdx body "ff_aac_sbr_apply.L968d" = 354 := blockIdx_at L.L968d
@[lex_var] theorem L96d3 : Program.blockIdx body "ff_aac_sbr_apply.L96d3" = 355 := blockIdx_at L.L96d3
@[lex_var] theorem L96e1 : Program.blockIdx body "ff_aac_sbr_apply.L96e1" = 356 := blockIdx_at L.L96e1
@[lex_var] theorem L9720 : Program.blockIdx body "ff_aac_sbr_apply.L9720" = 357 := blockIdx_at L.L9720
@[lex_var] theorem L9731 : Program.blockIdx body "ff_aac_sbr_apply.L9731" = 358 := blockIdx_at L.L9731
@[lex_var] theorem L9731_1 : Program.blockIdx body "ff_aac_sbr_apply.L9731_1" = 359 := blockIdx_at L.L9731_1
@[lex_var] theorem L97b7 : Program.blockIdx body "ff_aac_sbr_apply.L97b7" = 360 := blockIdx_at L.L97b7
@[lex_var] theorem L97f0 : Program.blockIdx body "ff_aac_sbr_apply.L97f0" = 361 := blockIdx_at L.L97f0
@[lex_var] theorem L9820 : Program.blockIdx body "ff_aac_sbr_apply.L9820" = 362 := blockIdx_at L.L9820
@[lex_var] theorem L983f : Program.blockIdx body "ff_aac_sbr_apply.L983f" = 363 := blockIdx_at L.L983f
@[lex_var] theorem L9860 : Program.blockIdx body "ff_aac_sbr_apply.L9860" = 364 := blockIdx_at L.L9860
@[lex_var] theorem L9860_1 : Program.blockIdx body "ff_aac_sbr_apply.L9860_1" = 365 := blockIdx_at L.L9860_1
@[lex_var] theorem L9860_2 : Program.blockIdx body "ff_aac_sbr_apply.L9860_2" = 366 := blockIdx_at L.L9860_2
@[lex_var] theorem L9860_3 : Program.blockIdx body "ff_aac_sbr_apply.L9860_3" = 367 := blockIdx_at L.L9860_3
@[lex_var] theorem L98bc : Program.blockIdx body "ff_aac_sbr_apply.L98bc" = 368 := blockIdx_at L.L98bc
@[lex_var] theorem L98e0 : Program.blockIdx body "ff_aac_sbr_apply.L98e0" = 369 := blockIdx_at L.L98e0
@[lex_var] theorem L9927 : Program.blockIdx body "ff_aac_sbr_apply.L9927" = 370 := blockIdx_at L.L9927
@[lex_var] theorem L9934 : Program.blockIdx body "ff_aac_sbr_apply.L9934" = 371 := blockIdx_at L.L9934
@[lex_var] theorem L9934_1 : Program.blockIdx body "ff_aac_sbr_apply.L9934_1" = 372 := blockIdx_at L.L9934_1
@[lex_var] theorem L9934_2 : Program.blockIdx body "ff_aac_sbr_apply.L9934_2" = 373 := blockIdx_at L.L9934_2
@[lex_var] theorem L99c6 : Program.blockIdx body "ff_aac_sbr_apply.L99c6" = 374 := blockIdx_at L.L99c6
@[lex_var] theorem L99cf : Program.blockIdx body "ff_aac_sbr_apply.L99cf" = 375 := blockIdx_at L.L99cf
@[lex_var] theorem L99e9 : Program.blockIdx body "ff_aac_sbr_apply.L99e9" = 376 := blockIdx_at L.L99e9
@[lex_var] theorem L99ee : Program.blockIdx body "ff_aac_sbr_apply.L99ee" = 377 := blockIdx_at L.L99ee
@[lex_var] theorem L99f3 : Program.blockIdx body "ff_aac_sbr_apply.L99f3" = 378 := blockIdx_at L.L99f3
@[lex_var] theorem L99f8 : Program.blockIdx body "ff_aac_sbr_apply.L99f8" = 379 := blockIdx_at L.L99f8
@[lex_var] theorem L99fd : Program.blockIdx body "ff_aac_sbr_apply.L99fd" = 380 := blockIdx_at L.L99fd
@[lex_var] theorem L9a02 : Program.blockIdx body "ff_aac_sbr_apply.L9a02" = 381 := blockIdx_at L.L9a02
@[lex_var] theorem L9a02_1 : Program.blockIdx body "ff_aac_sbr_apply.L9a02_1" = 382 := blockIdx_at L.L9a02_1
@[lex_var] theorem L9a50 : Program.blockIdx body "ff_aac_sbr_apply.L9a50" = 383 := blockIdx_at L.L9a50
@[lex_var] theorem L9a55 : Program.blockIdx body "ff_aac_sbr_apply.L9a55" = 384 := blockIdx_at L.L9a55
@[lex_var] theorem L9a5a : Program.blockIdx body "ff_aac_sbr_apply.L9a5a" = 385 := blockIdx_at L.L9a5a
@[lex_var] theorem L9a5f : Program.blockIdx body "ff_aac_sbr_apply.L9a5f" = 386 := blockIdx_at L.L9a5f
@[lex_var] theorem L9a64 : Program.blockIdx body "ff_aac_sbr_apply.L9a64" = 387 := blockIdx_at L.L9a64
@[lex_var] theorem L9a69 : Program.blockIdx body "ff_aac_sbr_apply.L9a69" = 388 := blockIdx_at L.L9a69
@[lex_var] theorem L9a7d : Program.blockIdx body "ff_aac_sbr_apply.L9a7d" = 389 := blockIdx_at L.L9a7d
@[lex_var] theorem L9a85 : Program.blockIdx body "ff_aac_sbr_apply.L9a85" = 390 := blockIdx_at L.L9a85
@[lex_var] theorem L9a85_1 : Program.blockIdx body "ff_aac_sbr_apply.L9a85_1" = 391 := blockIdx_at L.L9a85_1
@[lex_var] theorem L9a85_2 : Program.blockIdx body "ff_aac_sbr_apply.L9a85_2" = 392 := blockIdx_at L.L9a85_2
@[lex_var] theorem L9a85_3 : Program.blockIdx body "ff_aac_sbr_apply.L9a85_3" = 393 := blockIdx_at L.L9a85_3
@[lex_var] theorem L9a85_4 : Program.blockIdx body "ff_aac_sbr_apply.L9a85_4" = 394 := blockIdx_at L.L9a85_4
@[lex_var] theorem L9b24 : Program.blockIdx body "ff_aac_sbr_apply.L9b24" = 395 := blockIdx_at L.L9b24
@[lex_var] theorem L9b2b : Program.blockIdx body "ff_aac_sbr_apply.L9b2b" = 396 := blockIdx_at L.L9b2b
@[lex_var] theorem done : Program.blockIdx body "ff_aac_sbr_apply.done" = 397 := blockIdx_at L.done
@[lex_var] theorem L9b36 : Program.blockIdx body "ff_aac_sbr_apply.L9b36" = 398 := blockIdx_at L.L9b36
@[lex_var] theorem L9b3b : Program.blockIdx body "ff_aac_sbr_apply.L9b3b" = 399 := blockIdx_at L.L9b3b
@[lex_var] theorem L9b40 : Program.blockIdx body "ff_aac_sbr_apply.L9b40" = 400 := blockIdx_at L.L9b40
@[lex_var] theorem L9b45 : Program.blockIdx body "ff_aac_sbr_apply.L9b45" = 401 := blockIdx_at L.L9b45
@[lex_var] theorem L9b4a : Program.blockIdx body "ff_aac_sbr_apply.L9b4a" = 402 := blockIdx_at L.L9b4a
@[lex_var] theorem L9b4f : Program.blockIdx body "ff_aac_sbr_apply.L9b4f" = 403 := blockIdx_at L.L9b4f
@[lex_var] theorem L9b54 : Program.blockIdx body "ff_aac_sbr_apply.L9b54" = 404 := blockIdx_at L.L9b54
@[lex_var] theorem L9b59 : Program.blockIdx body "ff_aac_sbr_apply.L9b59" = 405 := blockIdx_at L.L9b59
@[lex_var] theorem L9b5e : Program.blockIdx body "ff_aac_sbr_apply.L9b5e" = 406 := blockIdx_at L.L9b5e
@[lex_var] theorem L9b63 : Program.blockIdx body "ff_aac_sbr_apply.L9b63" = 407 := blockIdx_at L.L9b63
@[lex_var] theorem L9b68 : Program.blockIdx body "ff_aac_sbr_apply.L9b68" = 408 := blockIdx_at L.L9b68
@[lex_var] theorem L9b6d : Program.blockIdx body "ff_aac_sbr_apply.L9b6d" = 409 := blockIdx_at L.L9b6d
@[lex_var] theorem L9b72 : Program.blockIdx body "ff_aac_sbr_apply.L9b72" = 410 := blockIdx_at L.L9b72
@[lex_var] theorem L9b77 : Program.blockIdx body "ff_aac_sbr_apply.L9b77" = 411 := blockIdx_at L.L9b77
@[lex_var] theorem L9b7c : Program.blockIdx body "ff_aac_sbr_apply.L9b7c" = 412 := blockIdx_at L.L9b7c
@[lex_var] theorem L9b81 : Program.blockIdx body "ff_aac_sbr_apply.L9b81" = 413 := blockIdx_at L.L9b81
@[lex_var] theorem L9b86 : Program.blockIdx body "ff_aac_sbr_apply.L9b86" = 414 := blockIdx_at L.L9b86
@[lex_var] theorem L9b8b : Program.blockIdx body "ff_aac_sbr_apply.L9b8b" = 415 := blockIdx_at L.L9b8b
@[lex_var] theorem L9b90 : Program.blockIdx body "ff_aac_sbr_apply.L9b90" = 416 := blockIdx_at L.L9b90
@[lex_var] theorem L9b95 : Program.blockIdx body "ff_aac_sbr_apply.L9b95" = 417 := blockIdx_at L.L9b95
@[lex_var] theorem L9b9a : Program.blockIdx body "ff_aac_sbr_apply.L9b9a" = 418 := blockIdx_at L.L9b9a
@[lex_var] theorem L9b9a_1 : Program.blockIdx body "ff_aac_sbr_apply.L9b9a_1" = 419 := blockIdx_at L.L9b9a_1
@[lex_var] theorem L9bc5 : Program.blockIdx body "ff_aac_sbr_apply.L9bc5" = 420 := blockIdx_at L.L9bc5
@[lex_var] theorem L9bca : Program.blockIdx body "ff_aac_sbr_apply.L9bca" = 421 := blockIdx_at L.L9bca
@[lex_var] theorem L9bcf : Program.blockIdx body "ff_aac_sbr_apply.L9bcf" = 422 := blockIdx_at L.L9bcf
@[lex_var] theorem L9bd4 : Program.blockIdx body "ff_aac_sbr_apply.L9bd4" = 423 := blockIdx_at L.L9bd4
@[lex_var] theorem L9bd4_1 : Program.blockIdx body "ff_aac_sbr_apply.L9bd4_1" = 424 := blockIdx_at L.L9bd4_1
@[lex_var] theorem L9bff : Program.blockIdx body "ff_aac_sbr_apply.L9bff" = 425 := blockIdx_at L.L9bff
@[lex_var] theorem L9c04 : Program.blockIdx body "ff_aac_sbr_apply.L9c04" = 426 := blockIdx_at L.L9c04
@[lex_var] theorem L9c09 : Program.blockIdx body "ff_aac_sbr_apply.L9c09" = 427 := blockIdx_at L.L9c09
@[lex_var] theorem L9c0e : Program.blockIdx body "ff_aac_sbr_apply.L9c0e" = 428 := blockIdx_at L.L9c0e
@[lex_var] theorem L9c13 : Program.blockIdx body "ff_aac_sbr_apply.L9c13" = 429 := blockIdx_at L.L9c13
@[lex_var] theorem L9c18 : Program.blockIdx body "ff_aac_sbr_apply.L9c18" = 430 := blockIdx_at L.L9c18
@[lex_var] theorem L9c1d : Program.blockIdx body "ff_aac_sbr_apply.L9c1d" = 431 := blockIdx_at L.L9c1d
@[lex_var] theorem L9c22 : Program.blockIdx body "ff_aac_sbr_apply.L9c22" = 432 := blockIdx_at L.L9c22
@[lex_var] theorem L9c27 : Program.blockIdx body "ff_aac_sbr_apply.L9c27" = 433 := blockIdx_at L.L9c27
end I


abbrev Post' (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ s : MachineData) : Prop := ApplyPost k e x ra t₀ s

/-- The obligation of the block `blk` at the literal label `l`. -/
abbrev BlockOb (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) (l : Label)
    (blk : Program.Block) : Prop :=
  ∀ n : Nat,
    ⦃ fun s => table k e x ra t₀ l s ∧ var l s = n ⦄ blk.body
    ⦃ (match blk.next with
       | some l' => fun _ s => table k e x ra t₀ l' s ∧ var l' s ≤ n
       | none => fun _ _ => False);
      fun a s => Table.ofLabels (fun l' s => (Program.blockAt body l').isSome
          ∧ table k e x ra t₀ l' s ∧ Program.EdgeLt body var l n l' s) a s
        ∨ (a = ra ∧ Post' k e x ra t₀ s) ⦄

end Kraken.Examples.Sbr.Apply
