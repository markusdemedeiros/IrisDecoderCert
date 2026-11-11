import Kraken.X64.Examples.Sbr.Parse.UsacGrd
open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse
set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true
/-! # `ff_aac_sbr_decode_usac_data`: the calls of `read_sbr_grid`

The frame `UM` at the call is the grid's `CallPre` with `GF` (`uf_grid0/1`) and the caller's
part `GR ⋆ Rst`; the return state goes back into `UF` (`uf_post0/1`). -/
namespace Kraken.Examples.Sbr.Usac
variable [CodeEnv]

/-- The cell `bs_coupling` (`sbr + 0x3c`) in the frame. -/
theorem um_split_cpl (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) (Lc Sg : Mem 64 → Prop)
    (st : USt) (v : BitVec 32) :
    ∃ R, Split (cell4 (sA A.1.c + 0x3c#64) st.x.coupling) R (UM k A ra t₀ Lc Sg st)
      ∧ Split (cell4 (sA A.1.c + 0x3c#64) v) R
          (UM k A ra t₀ Lc Sg { st with x := { st.x with coupling := v } }) := by
  simp only [UM, UF, SHW]
  exact ⟨_, Split.right (Split.right (Split.left (Split.left (Split.right (Split.right
      (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right
      (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right
      (Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _,
    Split.right (Split.right (Split.left (Split.left (Split.right (Split.right
      (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right
      (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right
      (Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _⟩

/-- Storing `bs_coupling`. -/
theorem um_storeCpl {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} (h : m =⋆ UM k A ra t₀ Lc Sg st) (a : BitVec 64)
    (ha : a = sA A.1.c + 0x3c#64) (v : BitVec 32) :
    m.storeInt a 4 v.toInt =⋆ UM k A ra t₀ Lc Sg { st with x := { st.x with coupling := v } } := by
  obtain ⟨R, hs, hs'⟩ := um_split_cpl k A ra t₀ Lc Sg st v
  rw [hs', ha]
  exact Val.storeInt h hs (Int.toBytes_length 4 _) v.toInt

/-- Loading `bs_coupling` succeeds. -/
theorem um_loadCpl {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} (h : m =⋆ UM k A ra t₀ Lc Sg st) (a : BitVec 64)
    (ha : a = sA A.1.c + 0x3c#64) :
    (m.loadInt a 4).isSome = true := by
  obtain ⟨R, hs, -⟩ := um_split_cpl k A ra t₀ Lc Sg st 0#32
  rw [ha, Val.loadInt h hs (Int.toBytes_length 4 _) (by decide)]
  rfl

set_option maxRecDepth 8000 in
/-- `read_sbr_grid(ac, sbr, gb, &sbr->data[0])` of the single channel element. -/
theorem blk_L3609 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData)
    (hc : GridSpecA k A.1.Ext) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L3609" := by
  cfg_block
  measure_hb "L3609"
    intro n
    simp only [tbl_L3609, var_L3609, tbl_L3621, var_L3621]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, hP, hm⟩, hch⟩, rfl⟩ := hs₀
    simp only [UM] at hm
    obtain ⟨hmi, hid, hu⟩ := hP
    have e50 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 80#64 := by
      rw [hsp]; show _ - 72#64 - 8#64 = _; bv_omega
    have e72 : s₀.regs.get64 .rsp - Width.W64.bytesv + 8 = t₀.regs.get64 .rsp - 72#64 := by
      rw [hsp]; show _ - 72#64 - 8#64 + 8#64 = _; bv_omega
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rsp - Width.W64.bytesv) 8).isSome = true := by
      rw [e50]
      exact Block.loadInt_isSome hm (by simp)
    have hd0 : s₀.regs.get64 .rbx + Int64.toBitVec 166304 = dAc A.1.c 0 := by
      rw [hbx, show Int64.toBitVec 166304 = 166304#64 from rfl]; simp only [dAc, sA]; bv_omega
    have hpush := fun v => Block.storeInt_val hm (Split.here _ _) v
    generalize table k A ra t₀ = T
    generalize var = V
    vcgen [call_procA_spec_at (gx A.1 st st.x.d0
        (GR0 A.1 st ⋆ Rst A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀))))
      "read_sbr_grid" hc]
    all_goals try call_simp
    have hs1 := ‹_ = s₀›
    subst hs1
    refine ⟨fun ra' => ⟨⟨?mem, ?gc⟩, fun s' hpost => ?post⟩,
      fun _ => Or.inr (Or.inr (Or.inl trivial)), hld⟩
    case mem =>
      rw [e50]
      have h := hpush (ra'.toBitVec.toInt)
      rw [uf_grid0 A.1 st _ _ _ _ ?h0 ?h1 ?hg ?hd, Std.ExtHashMap.sep_assoc] at h
      exact h
      case h0 =>
          simp only [arg0, MachineData.get64_pushRa, Reg64s.get64_set64, reduceCtorEq,
            ite_false, ite_true]
          exact h12
      case h1 =>
          simp only [arg1, MachineData.get64_pushRa, Reg64s.get64_set64, reduceCtorEq,
            ite_false, ite_true]
          exact h13
      case hg => exact h14
      case hd => exact hd0
    case gc =>
      exact ⟨hmi.1.2.2.1, hmi.1.2.2.2.2.2.1, hI.2.2, hF.1.2.2.2.1.1, hF.1.2.2.2.1.2.1,
        hF.1.2.2.2.1.2.2, hF.1.2.2.2.2.2.1⟩
    case post =>
      obtain ⟨g, hout, hsp', hbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩ := hpost
      rw [e50] at hm'
      have hm2 : s'.dmem =⋆ UM k A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) (Sv t₀)
          (gs0 A.1 st (GR0 A.1 st ⋆ Rst A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀))) g) := by
        simp only [UM]
        rw [← uf_post0 A.1 st _ _ g _ _ ?p0 ?p1 ?pg ?pd, Std.ExtHashMap.sep_assoc]
        exact hm'
        case p0 =>
          simp only [arg0, MachineData.get64_pushRa, Reg64s.get64_set64, reduceCtorEq,
            ite_false, ite_true]
          exact h12
        case p1 =>
          simp only [arg1, MachineData.get64_pushRa, Reg64s.get64_set64, reduceCtorEq,
            ite_false, ite_true]
          exact h13
        case pg => exact h14
        case pd => exact hd0
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨⟨⟨⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, gs0 A.1 st _ g, ⟨hI.1, hI.2.1, hout.2.2.2.2⟩,
        ⟨⟨mi_d0 hmi hout.1 hout.2.1, hid, hu⟩, fun h0 => hout.2.2.2.1 h0⟩, hm2⟩, ?_⟩, hch⟩,
        Nat.le_refl _⟩
      · exact hsp'.trans e72
      · exact hbp'.trans hbp
      · exact h12'.trans h12
      · exact hbx'.trans hbx
      · exact h14'.trans h14
      · exact h13'.trans h13
      · first
        | exact h15'.trans hd0
        | (rw [h15']; dsimp only
           simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]; exact hd0)

set_option maxRecDepth 8000 in
/-- `read_sbr_grid(ac, sbr, gb, &sbr->data[1])` of the independent coupled pair. -/
theorem blk_L395d (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData)
    (hc : GridSpecA k A.1.Ext) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L395d" := by
  cfg_block
  measure_hb "L395d"
    intro n
    simp only [tbl_L395d, var_L395d, tbl_L3972, var_L3972]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, hP, hm⟩, h15⟩, rfl⟩ := hs₀
    simp only [UM] at hm
    obtain ⟨⟨hmi, hid, hu⟩, hlive⟩ := hP
    have e50 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 80#64 := by
      rw [hsp]; show _ - 72#64 - 8#64 = _; bv_omega
    have e72 : s₀.regs.get64 .rsp - Width.W64.bytesv + 8 = t₀.regs.get64 .rsp - 72#64 := by
      rw [hsp]; show _ - 72#64 - 8#64 + 8#64 = _; bv_omega
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rsp - Width.W64.bytesv) 8).isSome = true := by
      rw [e50]
      exact Block.loadInt_isSome hm (by simp)
    have hd0 : s₀.regs.get64 .rbx + Int64.toBitVec 255072 = dAc A.1.c 1 := by
      rw [hbx, show Int64.toBitVec 255072 = 255072#64 from rfl]; simp only [dAc, sA]; bv_omega
    have hpush := fun v => Block.storeInt_val hm (Split.here _ _) v
    generalize table k A ra t₀ = T
    generalize var = V
    vcgen [call_procA_spec_at (gx A.1 st st.x.d1
        (GR1 A.1 st ⋆ Rst A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀))))
      "read_sbr_grid" hc]
    all_goals try call_simp
    have hs1 := ‹_ = s₀›
    subst hs1
    refine ⟨fun ra' => ⟨⟨?mem, ?gc⟩, fun s' hpost => ?post⟩,
      fun _ => Or.inr (Or.inr (Or.inl trivial)), hld⟩
    case mem =>
      rw [e50]
      have h := hpush (ra'.toBitVec.toInt)
      rw [uf_grid1 A.1 st _ _ _ _ ?h0 ?h1 ?hg ?hd, Std.ExtHashMap.sep_assoc] at h
      exact h
      case h0 =>
          simp only [arg0, MachineData.get64_pushRa, Reg64s.get64_set64, reduceCtorEq,
            ite_false, ite_true]
          exact h12
      case h1 =>
          simp only [arg1, MachineData.get64_pushRa, Reg64s.get64_set64, reduceCtorEq,
            ite_false, ite_true]
          exact h13
      case hg => exact h14
      case hd => exact hd0
    case gc =>
      exact ⟨hmi.1.2.2.2.1, hmi.1.2.2.2.2.2.2, hI.2.2, hF.1.2.2.2.1.1, hF.1.2.2.2.1.2.1,
        hF.1.2.2.2.1.2.2, hF.1.2.2.2.2.2.1⟩
    case post =>
      obtain ⟨g, hout, hsp', hbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩ := hpost
      rw [e50] at hm'
      have hm2 : s'.dmem =⋆ UM k A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) (Sv t₀)
          (gs1 A.1 st (GR1 A.1 st ⋆ Rst A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀))) g) := by
        simp only [UM]
        rw [← uf_post1 A.1 st _ _ g _ _ ?p0 ?p1 ?pg ?pd, Std.ExtHashMap.sep_assoc]
        exact hm'
        case p0 =>
          simp only [arg0, MachineData.get64_pushRa, Reg64s.get64_set64, reduceCtorEq,
            ite_false, ite_true]
          exact h12
        case p1 =>
          simp only [arg1, MachineData.get64_pushRa, Reg64s.get64_set64, reduceCtorEq,
            ite_false, ite_true]
          exact h13
        case pg => exact h14
        case pd => exact hd0
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨⟨⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, gs1 A.1 st _ g, ⟨hI.1, hI.2.1, hout.2.2.2.2⟩,
        ⟨⟨⟨mi_d1 hmi hout.1 hout.2.1, hid, hu⟩, hlive⟩, fun h0 => hout.2.2.2.1 h0⟩, hm2⟩,
        ?_⟩, Nat.le_refl _⟩
      · exact hsp'.trans e72
      · exact hbp'.trans hbp
      · exact h12'.trans h12
      · exact hbx'.trans hbx
      · exact h14'.trans h14
      · exact h13'.trans h13
      · first
        | exact h15'.trans h15
        | (rw [h15']; simp only [MachineData.get64_pushRa, Reg64s.get64_set64, reduceCtorEq,
             ite_false, ite_true]; exact h15)

set_option maxRecDepth 8000 in
/-- `bs_coupling = 1`, `read_sbr_grid(ac, sbr, gb, &sbr->data[0])` of the coupled pair. -/
theorem blk_L36fa (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData)
    (hc : GridSpecA k A.1.Ext) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L36fa" := by
  cfg_block
  measure_hb "L36fa"
    intro n
    simp only [tbl_L36fa, var_L36fa, tbl_L3715, var_L3715]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, hP, hm⟩, h15⟩, rfl⟩ := hs₀
    obtain ⟨hmi, hid, hu⟩ := hP
    have e50 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 80#64 := by
      rw [hsp]; show _ - 72#64 - 8#64 = _; bv_omega
    have e72 : s₀.regs.get64 .rsp - Width.W64.bytesv + 8 = t₀.regs.get64 .rsp - 72#64 := by
      rw [hsp]; show _ - 72#64 - 8#64 + 8#64 = _; bv_omega
    have hca : s₀.regs.get64 .rbx + Int64.toBitVec 166236 = sA A.1.c + 0x3c#64 := by
      rw [hbx, show Int64.toBitVec 166236 = 166236#64 from rfl]; simp only [sA]; bv_omega
    have hlc := um_loadCpl hm _ hca
    have hm1 := um_storeCpl hm _ hca (BitVec.setWidth 32 (Int64.toBitVec 1))
    simp only [UM] at hm1
    have hld : ((s₀.dmem.storeInt (s₀.regs.get64 .rbx + Int64.toBitVec 166236) 4
        (BitVec.setWidth 32 (Int64.toBitVec 1)).toInt).loadInt
        (s₀.regs.get64 .rsp - Width.W64.bytesv) 8).isSome = true := by
      rw [e50]
      exact Block.loadInt_isSome hm1 (by simp)
    have hpush := fun v => Block.storeInt_val hm1 (Split.here _ _) v
    generalize table k A ra t₀ = T
    generalize var = V
    vcgen [call_procA_spec_at (gx A.1 { st with x := { st.x with coupling := 1#32 } }
        st.x.d0 (GR0 A.1 { st with x := { st.x with coupling := 1#32 } }
          ⋆ Rst A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)))) "read_sbr_grid" hc]
    all_goals try call_simp
    all_goals try simp only [AddrIndex.offset64_none, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at *
    all_goals subst s₀
    case vc1 => exact hlc
    refine ⟨fun ra' => ⟨⟨?mem, ?gc⟩, fun s' hpost => ?post⟩,
      fun _ => Or.inr (Or.inr (Or.inl trivial)), hld⟩
    case mem =>
      rw [e50]
      have h := hpush (ra'.toBitVec.toInt)
      rw [uf_grid0 A.1 _ _ _ _ _ ?h0 ?h1 ?hg ?hd, Std.ExtHashMap.sep_assoc] at h
      exact h
      case h0 =>
          simp only [arg0, MachineData.get64_pushRa, Reg64s.get64_set64, reduceCtorEq,
            ite_false, ite_true]
          exact h12
      case h1 =>
          simp only [arg1, MachineData.get64_pushRa, Reg64s.get64_set64, reduceCtorEq,
            ite_false, ite_true]
          exact h13
      case hg => exact h14
      case hd => exact h15
    case gc =>
      exact ⟨hmi.1.2.2.1, hmi.1.2.2.2.2.2.1, hI.2.2, hF.1.2.2.2.1.1, hF.1.2.2.2.1.2.1,
        hF.1.2.2.2.1.2.2, hF.1.2.2.2.2.2.1⟩
    case post =>
      obtain ⟨g, hout, hsp', hbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩ := hpost
      rw [e50] at hm'
      have hm2 : s'.dmem =⋆ UM k A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) (Sv t₀)
          (gs0 A.1 { st with x := { st.x with coupling := 1#32 } }
            (GR0 A.1 { st with x := { st.x with coupling := 1#32 } }
              ⋆ Rst A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀))) g) := by
        simp only [UM]
        rw [← uf_post0 A.1 _ _ _ g _ _ ?p0 ?p1 ?pg ?pd, Std.ExtHashMap.sep_assoc]
        exact hm'
        case p0 =>
          simp only [arg0, MachineData.get64_pushRa, Reg64s.get64_set64, reduceCtorEq,
            ite_false, ite_true]
          exact h12
        case p1 =>
          simp only [arg1, MachineData.get64_pushRa, Reg64s.get64_set64, reduceCtorEq,
            ite_false, ite_true]
          exact h13
        case pg => exact h14
        case pd => exact h15
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨⟨⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_,
        gs0 A.1 { st with x := { st.x with coupling := 1#32 } } _ g,
        ⟨hI.1, hI.2.1, hout.2.2.2.2⟩,
        ⟨⟨mi_d0 (mi_coupling _ hmi) hout.1 hout.2.1, hid, hu⟩, rfl, fun h0 => hout.2.2.2.1 h0⟩,
        hm2⟩, ?_⟩, Nat.le_refl _⟩
      · exact hsp'.trans e72
      · exact hbp'.trans hbp
      · exact h12'.trans h12
      · exact hbx'.trans hbx
      · exact h14'.trans h14
      · exact h13'.trans h13
      · first
        | exact h15'.trans h15
        | (rw [h15']; simp only [MachineData.get64_pushRa, Reg64s.get64_set64, reduceCtorEq,
             ite_false, ite_true]; exact h15)

set_option maxRecDepth 8000 in
/-- `bs_coupling = 0`, `read_sbr_grid(ac, sbr, gb, &sbr->data[0])` of the independent pair. -/
theorem blk_L3933 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData)
    (hc : GridSpecA k A.1.Ext) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L3933" := by
  cfg_block
  measure_hb "L3933"
    intro n
    simp only [tbl_L3933, var_L3933, tbl_L394e, var_L394e]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, hP, hm⟩, h15⟩, rfl⟩ := hs₀
    obtain ⟨hmi, hid, hu⟩ := hP
    have e50 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 80#64 := by
      rw [hsp]; show _ - 72#64 - 8#64 = _; bv_omega
    have e72 : s₀.regs.get64 .rsp - Width.W64.bytesv + 8 = t₀.regs.get64 .rsp - 72#64 := by
      rw [hsp]; show _ - 72#64 - 8#64 + 8#64 = _; bv_omega
    have hca : s₀.regs.get64 .rbx + Int64.toBitVec 166236 = sA A.1.c + 0x3c#64 := by
      rw [hbx, show Int64.toBitVec 166236 = 166236#64 from rfl]; simp only [sA]; bv_omega
    have hlc := um_loadCpl hm _ hca
    have hm1 := um_storeCpl hm _ hca (BitVec.setWidth 32 (Int64.toBitVec 0))
    simp only [UM] at hm1
    have hld : ((s₀.dmem.storeInt (s₀.regs.get64 .rbx + Int64.toBitVec 166236) 4
        (BitVec.setWidth 32 (Int64.toBitVec 0)).toInt).loadInt
        (s₀.regs.get64 .rsp - Width.W64.bytesv) 8).isSome = true := by
      rw [e50]
      exact Block.loadInt_isSome hm1 (by simp)
    have hpush := fun v => Block.storeInt_val hm1 (Split.here _ _) v
    generalize table k A ra t₀ = T
    generalize var = V
    vcgen [call_procA_spec_at (gx A.1 { st with x := { st.x with coupling := 0#32 } }
        st.x.d0 (GR0 A.1 { st with x := { st.x with coupling := 0#32 } }
          ⋆ Rst A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)))) "read_sbr_grid" hc]
    all_goals try call_simp
    all_goals try simp only [AddrIndex.offset64_none, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at *
    all_goals subst s₀
    case vc1 => exact hlc
    refine ⟨fun ra' => ⟨⟨?mem, ?gc⟩, fun s' hpost => ?post⟩,
      fun _ => Or.inr (Or.inr (Or.inl trivial)), hld⟩
    case mem =>
      rw [e50]
      have h := hpush (ra'.toBitVec.toInt)
      rw [uf_grid0 A.1 _ _ _ _ _ ?h0 ?h1 ?hg ?hd, Std.ExtHashMap.sep_assoc] at h
      exact h
      case h0 =>
          simp only [arg0, MachineData.get64_pushRa, Reg64s.get64_set64, reduceCtorEq,
            ite_false, ite_true]
          exact h12
      case h1 =>
          simp only [arg1, MachineData.get64_pushRa, Reg64s.get64_set64, reduceCtorEq,
            ite_false, ite_true]
          exact h13
      case hg => exact h14
      case hd => exact h15
    case gc =>
      exact ⟨hmi.1.2.2.1, hmi.1.2.2.2.2.2.1, hI.2.2, hF.1.2.2.2.1.1, hF.1.2.2.2.1.2.1,
        hF.1.2.2.2.1.2.2, hF.1.2.2.2.2.2.1⟩
    case post =>
      obtain ⟨g, hout, hsp', hbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩ := hpost
      rw [e50] at hm'
      have hm2 : s'.dmem =⋆ UM k A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) (Sv t₀)
          (gs0 A.1 { st with x := { st.x with coupling := 0#32 } }
            (GR0 A.1 { st with x := { st.x with coupling := 0#32 } }
              ⋆ Rst A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀))) g) := by
        simp only [UM]
        rw [← uf_post0 A.1 _ _ _ g _ _ ?p0 ?p1 ?pg ?pd, Std.ExtHashMap.sep_assoc]
        exact hm'
        case p0 =>
          simp only [arg0, MachineData.get64_pushRa, Reg64s.get64_set64, reduceCtorEq,
            ite_false, ite_true]
          exact h12
        case p1 =>
          simp only [arg1, MachineData.get64_pushRa, Reg64s.get64_set64, reduceCtorEq,
            ite_false, ite_true]
          exact h13
        case pg => exact h14
        case pd => exact h15
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨⟨⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_,
        gs0 A.1 { st with x := { st.x with coupling := 0#32 } } _ g,
        ⟨hI.1, hI.2.1, hout.2.2.2.2⟩,
        ⟨⟨mi_d0 (mi_coupling _ hmi) hout.1 hout.2.1, hid, hu⟩, fun h0 => hout.2.2.2.1 h0⟩,
        hm2⟩, ?_⟩, Nat.le_refl _⟩
      · exact hsp'.trans e72
      · exact hbp'.trans hbp
      · exact h12'.trans h12
      · exact hbx'.trans hbx
      · exact h14'.trans h14
      · exact h13'.trans h13
      · first
        | exact h15'.trans h15
        | (rw [h15']; simp only [MachineData.get64_pushRa, Reg64s.get64_set64, reduceCtorEq,
             ite_false, ite_true]; exact h15)

end Kraken.Examples.Sbr.Usac
