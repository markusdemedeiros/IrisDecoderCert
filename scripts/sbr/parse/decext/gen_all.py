#!/usr/bin/env python3
"""The assembly `DecExtAll.lean` of `ff_aac_sbr_decode_extension`.

Reads the labels of `body` (in order) from `DecExtText.lean` and writes (stdout) the case split of
`ProcSpecS.of_cfg_post`:

  * a label of PROVED: its block theorem `blk_<suffix>`;
  * a label of the table (`DecExtBase.table`) not in PROVED: a field of `DecMissing`;
  * any other label: its table entry is `False` (`blk_false`).

Usage: gen_all.py Kraken/X64/Examples/Sbr/Parse/DecExtText.lean > DecExtAll.lean
"""
import re
import sys

P = "ff_aac_sbr_decode_extension"
TABLE = ["entry", "L21", "L36", "L63", "L301", "L31c", "L8b", "Lad", "Ld4", "Lff", "L333",
         "L10d", "L11d", "L128", "L349", "L164", "L384", "L39d", "L3bd", "L3cb", "L3e4", "L401",
         "L409", "L43d", "Lb1a", "L48b", "L4a1", "L4b7", "L4cd", "L4e2",
         "L4ee", "L50b", "L527", "L53d", "L553", "L569", "L57e", "done",
         "L7de", "L7e8", "L80e", "L835", "L85b", "L898", "L8b0"]
# The labels of `tableE` (the main table's last case).
TABLE_E = ["Lb40", "Lb64", "Lb86", "Lb9d", "Lbd4", "Lbe6", "Lbf5", "Lc1c", "Lc1f", "Lc41", "Lc4b",
           "Lc67", "Lc7d", "Lc83", "Lca0", "Lcbb", "Lcc0", "Lcd3"]
# The labels of `tableC` (`tableE`'s last case: the channel pair element).
TABLE_C = ["L466", "L481", "L16e", "L1a7", "L1d4", "L1ea", "L483", "L591", "L215", "L239", "L251",
           "L26a", "L27c", "L29e", "L2c2", "L2e3", "L76e", "L779", "L781", "L7b5", "L8e2", "L8ec",
           "L913", "L939", "L960", "L998", "L9a7", "L9d4", "La04", "La29", "La33", "La59", "La80",
           "Laa6", "Ladf", "Laed", "L5a2", "L5cc", "L5e1", "L5fd", "L614", "L62b", "L647", "L663",
           "L686", "L69a", "L6b3", "L6d0", "L6ed", "L708", "L729", "L751"]
PROVED = ["entry", "L21", "L36", "L63", "L301", "L31c", "L8b", "Lad", "Ld4", "Lff", "L333", "L10d", "L11d", "L4ee",
          "L527", "L53d", "L553", "L569", "L50b",
          "L128", "L48b", "L4a1", "L4b7", "L4cd", "L4e2",
          "L349", "L384", "L39d", "L3bd", "L3cb", "L3e4", "L401", "L409",
          "L43d", "L7de", "L7e8", "L80e", "L835", "L85b", "L898", "L8b0", "Lb1a",
          "Lb40", "Lb64", "Lb86", "Lc1c", "Lc1f", "Lcbb", "Lc7d", "Lc83", "Lcd3",
          "Lc41", "Lc4b", "Lca0", "Lc67", "Lcc0", "Lb9d", "Lbd4", "Lbe6", "Lbf5",
          "L57e", "done",
          "L164", "L481", "L779", "L2c2", "L2e3", "L76e", "L27c", "L29e", "L251", "L26a",
          "L215", "L239", "L483", "L1d4", "L1ea", "L466", "L16e", "L1a7", "L781",
          "L7b5", "L8e2", "L8ec", "L913", "L939", "L960", "L998", "L9a7",
          "L9d4", "La04", "La29", "La33", "La59", "La80", "Laa6", "Ladf", "Laed",
          "L591", "L5a2", "L5cc", "L5e1", "L5fd", "L614", "L62b", "L647", "L663", "L686", "L69a", "L6b3", "L6d0", "L6ed", "L708", "L729", "L751"]
# The blocks with a call: the hypothesis of the callee's contract.
SPECIAL = {"L50b": "hAv", "Lff": "hH", "L11d": "hR", "L384": "hG", "L39d": "hD", "L3bd": "hI",
           "L3cb": "hV", "L3e4": "hN", "Lca0": "hAv", "Lcc0": "hAv",
           "Lc67": "hReq", "Lbe6": "hPs",
           "L2c2": "hN", "L76e": "hN", "L27c": "hV", "L29e": "hV", "L251": "hI", "L26a": "hI",
           "L215": "hD", "L239": "hD", "L1d4": "hG", "L1ea": "hG", "L466": "hAv",
           "L663": "hD", "L686": "hD", "L69a": "hI", "L6ed": "hV", "L708": "hN", "L729": "hV"}


def suffix(lab):
  return "entry" if lab == P else lab[len(P) + 1:]


def table_false():
  """`table_false`: the last case of the table's match, of `tableE`'s and of `tableC`'s (`False`)."""
  hs = []
  for i, t in enumerate(TABLE + TABLE_E + TABLE_C):
    lab = P if t == "entry" else f"{P}.{t}"
    hs.append(f"    (h{i + 1} : l = \"{lab}\" → False := by intro e; simp only [String.reduceEq] at e)")
  n = len(TABLE) + len(TABLE_E) + len(TABLE_C)
  return (f"""/-- The table's last case (`False`): a label other than the {n} of the table. -/
theorem table_false {{PI : List UInt8 → Prop}} {{kc : Nat}} {{Ext : Mem 64 → Prop}} {{X : XA}}
    {{ra : Int64}} {{t₀ s : MachineData}} {{l : Label}} (h : table PI kc Ext X ra t₀ l s)
""" + "\n".join(hs) + f""" :
    False := by
  unfold table at h
  rw [table.match_1.eq_{len(TABLE) + 1}] at h
  · unfold tableE at h
    rw [tableE.match_1.eq_{len(TABLE_E) + 1}] at h
    · unfold tableC at h
      rw [tableC.match_1.eq_{len(TABLE_C) + 1}] at h
      · exact h
      all_goals assumption
    all_goals assumption
  all_goals assumption

""")


def main():
  labs = []
  for l in open(sys.argv[1]):
    m = re.match(r"^(" + re.escape(P) + r"(\.[A-Za-z0-9_]+)?):\s*$", l)
    if m:
      labs.append(m.group(1))
  missing = [t for t in TABLE + TABLE_E + TABLE_C if t not in PROVED]
  out = []
  w = out.append
  w(HEAD.replace("@@TABLEFALSE@@\n", table_false()))
  w("/-- The block obligations of the table's labels not proved here, one field per label. -/")
  w("structure DecMissing (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) : Prop where")
  for t in missing:
    w(f"  b_{t} : ∀ (X : XA) (ra : Int64) (t₀ : MachineData),")
    w(f"    BlockOb PI kc Ext X ra t₀ \"{P}.{t}\"")
  w("")
  w(MID)
  w("  obtain " + " | ".join(["rfl"] * len(labs)) + " := hmem")
  nf = 0
  for lab in labs:
    s = suffix(lab)
    if s in SPECIAL:
      w(f"  · exact blk_{s} PI kc Ext {SPECIAL[s]} X ra t₀ blk hblk")
    elif s in PROVED:
      w(f"  · exact blk_{s} PI kc Ext X ra t₀ blk hblk")
    elif s in TABLE + TABLE_E + TABLE_C:
      w(f"  · exact hmiss.b_{s} X ra t₀ blk hblk")
    else:
      nf += 1
      w("  · exact blk_false _ (fun _ h => table_false h) blk hblk")
  w("")
  w(f"-- {len(labs)} blocks: {len(PROVED)} proved, {len(missing)} hypotheses, {nf} with table False.")
  w("")
  w("end Kraken.Examples.Sbr.DecExt")
  print("\n".join(out))


HEAD = '''import Kraken.X64.Examples.Sbr.Parse.DecExtEntry
import Kraken.X64.Examples.Sbr.Parse.DecExtPro
import Kraken.X64.Examples.Sbr.Parse.DecExtPro2
import Kraken.X64.Examples.Sbr.Parse.DecExtExit
import Kraken.X64.Examples.Sbr.Parse.DecExtOff
import Kraken.X64.Examples.Sbr.Parse.DecExtCall
import Kraken.X64.Examples.Sbr.Parse.DecExtDat
import Kraken.X64.Examples.Sbr.Parse.DecExtOffD
import Kraken.X64.Examples.Sbr.Parse.DecExtSce2
import Kraken.X64.Examples.Sbr.Parse.DecExtHarm
import Kraken.X64.Examples.Sbr.Parse.DecExtCpB
import Kraken.X64.Examples.Sbr.Parse.DecExtCpD
import Kraken.X64.Examples.Sbr.Parse.DecExtCpTail
import Kraken.X64.Examples.Sbr.Parse.DecExtCpF
import Kraken.X64.Examples.Sbr.Parse.DecExtCpInvf

/-!
# `ff_aac_sbr_decode_extension`: the assembly

`ProcSpecS.of_cfg_post` over the blocks of `body` with the table of `DecExtBase.lean`
(generated by `scripts/sbr/parse/decext/gen_all.py`). The labels outside the table (the inlined
`read_sbr_data` and the rest of the data path) have the entry `False`: their obligations hold
(`blk_false`), and an edge into one of them is an obligation of the block it leaves. The table
labels whose blocks are not proved are the hypothesis `DecMissing`.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

namespace Kraken.Examples.Sbr.DecExt

variable [CodeEnv]

/-- A label whose table entry is `False`. -/
theorem blk_false {PI : List UInt8 → Prop} {kc : Nat} {Ext : Mem 64 → Prop} {X : XA}
    {ra : Int64} {t₀ : MachineData} (l : Label)
    (hF : ∀ s, table PI kc Ext X ra t₀ l s → False) : BlockOb PI kc Ext X ra t₀ l :=
  fun _ _ _ => Triple.pin fun s hs => (hF s hs.1).elim

@@TABLEFALSE@@
omit [CodeEnv] in
/-- `Entails` in both parts of a separating conjunction. -/
theorem sep_mono {X Y K K' : Mem 64 → Prop} (e₁ : Mem.Entails X Y)
    (e₂ : Mem.Entails K K') : Mem.Entails (X ⋆ K) (Y ⋆ K') := by
  intro m ⟨m₁, m₂, hd, hm, h₁, h₂⟩
  exact ⟨m₁, m₂, hd, hm, e₁ m₁ h₁, e₂ m₂ h₂⟩

omit [CodeEnv] in
theorem rsub (r : BitVec 64) (a b : Nat) :
    r - BitVec.ofNat 64 a - BitVec.ofNat 64 b = r - BitVec.ofNat 64 (a + b) := by
  rw [BitVec.sub_sub, BitVec.ofNat_add]

omit [CodeEnv] in
/-- The caller's reservation as the frame at entry: the callees' slot and reservation, the
locals `Loc0`, the six register slots. -/
theorem reserve_frame0 (kc : Nat) (r : BitVec 64) (K : Mem 64 → Prop)
    (hr : 0x70 ≤ r.toNat) :
    Reserve (0x70 + kc) r ⋆ K
      = 8 ?@ (r - 0x70#64) ⋆ (Reserve kc (r - 0x70#64) ⋆ (Loc0 r ⋆ BlankS r K)) := by
  rw [Reserve_split 0x70 kc r hr]
  have e : (0x70 : Nat) = 8 + (8 + (8 + (8 + (8 + (8 + (8 + (16 + (8 + (8 + (8 + (8
      + 8))))))))))) := by omega
  rw [e]
  repeat rw [block_split_top _ _ _ (by omega)]
  simp only [rsub, Loc0, BlankS]
  try simp only [Nat.reduceAdd]
  ac_rfl

/-- `LocE` with `cnt` forgotten. -/
abbrev LocER (r : BitVec 64) : Mem 64 → Prop :=
  8 ?@ (r - 0x68#64) ⋆ (8 ?@ (r - 0x60#64) ⋆ (8 ?@ (r - 0x58#64)
    ⋆ (8 ?@ (r - 0x50#64) ⋆ (8 ?@ (r - 0x48#64) ⋆ (4 ?@ (r - 0x40#64) ⋆ (4 ?@ (r - 0x3c#64)
    ⋆ (4 ?@ (r - 0x38#64) ⋆ 4 ?@ (r - 0x34#64))))))))

omit [CodeEnv] in
/-- The reservation as the frame at the exit. -/
theorem reserve_frameE (kc : Nat) (r : BitVec 64) (K : Mem 64 → Prop)
    (hr : 0x70 ≤ r.toNat) :
    Reserve (0x70 + kc) r ⋆ K
      = 8 ?@ (r - 0x70#64) ⋆ (Reserve kc (r - 0x70#64) ⋆ (LocER r ⋆ BlankS r K)) := by
  rw [Reserve_split 0x70 kc r hr]
  have e : (0x70 : Nat) = 8 + (8 + (8 + (8 + (8 + (8 + (4 + (4 + (4 + (4 + (8 + (8 + (8 + (8
      + (8 + 8)))))))))))))) := by omega
  rw [e]
  repeat rw [block_split_top _ _ _ (by omega)]
  simp only [rsub, LocER, BlankS]
  try simp only [Nat.reduceAdd]
  ac_rfl

theorem dec_hpre (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop)
    (X : XA) (ra : Int64) (t : MachineData) (h : DecPre PI kc Ext X ra t) :
    table PI kc Ext X ra t "ff_aac_sbr_decode_extension" t := by
  obtain ⟨hm, hC⟩ := h
  have hr : 0x70 ≤ (t.regs.get64 .rsp).toNat := by
    have := CallPre.le hm; unfold decNeed at this; omega
  refine ⟨rfl, DecCI.of hC hr, ?_⟩
  unfold CallPre at hm
  rw [reserve_frame0 kc _ _ hr] at hm
  simp only [BlankS] at hm
  simp only [T, Rest, BlankS]
  exact Mem.ac hm

theorem dec_hpost (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop)
    (X : XA) (ra : Int64) (t₀ s : MachineData) (h : Post' PI kc Ext X ra t₀ s) :
    DecPost PI kc Ext X ra t₀ s := by
  obtain ⟨hr, d, i, hI, hi, hax, hsp, hbp, hsv, hm⟩ := h
  refine ⟨d, i, hI, hi, hax, hsp, hbp, hsv, ?_⟩
  have e : Mem.Entails (8 ?@ t₀.regs.get64 .rsp ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x70#64)
      ⋆ (Reserve kc (t₀.regs.get64 .rsp - 0x70#64) ⋆ (LocE t₀
      ⋆ (DecF Ext X t₀ d i ⋆ Saved t₀ X.R)))))
      (8 ?@ t₀.regs.get64 .rsp ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x70#64)
      ⋆ (Reserve kc (t₀.regs.get64 .rsp - 0x70#64) ⋆ (LocER (t₀.regs.get64 .rsp)
      ⋆ (DecF Ext X t₀ d i ⋆ BlankS (t₀.regs.get64 .rsp) X.R))))) := by
    refine Mem.Entails.sep_left (Mem.Entails.sep_left (Mem.Entails.sep_left ?_))
    refine sep_mono ?_ (Mem.Entails.sep_left ?_)
    · repeat (first | exact Mem.Entails.refl _ | refine Mem.Entails.forget8 _ _ ?_ | refine Mem.Entails.sep_left ?_)
    · exact Mem.Entails.forget8 _ _ (Mem.Entails.forget8 _ _ (Mem.Entails.forget8 _ _
        (Mem.Entails.forget8 _ _ (Mem.Entails.forget8 _ _ (Mem.Entails.forget8 _ _
        (Mem.Entails.refl _))))))
  have hm' := e _ hm
  rw [reserve_frameE kc _ _ hr]
  simp only [BlankS] at hm' ⊢
  exact Mem.ac hm'
'''

MID = '''/-- **`ff_aac_sbr_decode_extension`** from the contracts of `av_log`, `read_sbr_header`,
`sbr_reset`, `read_sbr_grid`, `read_sbr_dtdf`, `read_sbr_invf`, `read_sbr_envelope`,
`read_sbr_noise`, `ff_ps_read_data` and `avpriv_request_sample` (with `kc` bytes), the blocks of
`DecMissing`, `kc ≤ 2^32`, and the placement of the text. -/
theorem decExtSpec_holds (PI : List UInt8 → Prop) (kc : Nat) (_hk : kc ≤ 2 ^ 32)
    (Ext : Mem 64 → Prop) (hAv : AvLogSpec Ext kc) (hH : HdrSpec kc Ext) (hR : ResetSpec kc Ext)
    (hG : GridSpec kc Ext) (hD : DtdfSpec kc Ext) (hI : InvfSpec kc Ext) (hV : EnvSpec kc Ext)
    (hN : NoiseSpec kc Ext) (hPs : PsSpec PI kc Ext) (hReq : AvReqSpec Ext kc)
    (hmiss : DecMissing PI kc Ext)
    (hpl : Program.PlacedIn body) :
    DecExtSpec PI kc Ext := by
  refine ProcSpecS.of_cfg_post (p := body) (table PI kc Ext) (Post' PI kc Ext) var
    (hblocks := ?_) (hpre := dec_hpre PI kc Ext) (hpost := dec_hpost PI kc Ext)
    (hwf := by decide +kernel)
  intro X ra t₀ l blk hblk
  have hmem := Program.isSome_blockAt body l
  cfg_view hblk as hview
  rw [hblk, hview] at hmem
  replace hmem := hmem.symm
  clear hview
  simp only [Option.isSome_some, List.map_cons, List.map_nil, List.contains_cons,
    List.contains_nil, Bool.or_false, Bool.or_eq_true, beq_iff_eq] at hmem'''

if __name__ == "__main__":
  main()
