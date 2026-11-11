#!/usr/bin/env python3
"""Generate DecExtGlueN.lean (the read_sbr_noise / read_sbr_envelope adapters).

Usage: python3 gen_glue_n.py > Kraken/X64/Examples/Sbr/Parse/DecExtGlueN.lean
"""
import sys

def nest(atoms):
    if len(atoms) == 1:
        return atoms[0]
    return atoms[0] + " ⋆ (" + nest(atoms[1:]) + ")" if len(atoms) > 2 else atoms[0] + " ⋆ " + atoms[1]

def nest_p(atoms):
    s = nest(atoms)
    return s

def wrap(s, ind="  "):
    # break long lines at ' ⋆ ' boundaries
    out, line = [], ind
    toks = s.split(" ⋆ ")
    for k, t in enumerate(toks):
        piece = t if k == 0 else " ⋆ " + t
        if len(line) + len(piece) > 98 and line.strip():
            out.append(line.rstrip())
            line = ind + piece.lstrip()
        else:
            line += piece
    out.append(line)
    return "\n".join(out)

D = {  # DataF atoms with the fine split, keyed by name
 'A1': '4 ?@ d', 'A2': '4 ?@ (d + 0x4#64)', 'NE': 'c4 (d + 0x8#64) v.nenv',
 'FR': 'v.freqRes =@ (d + 0xc#64)', 'A5': '3 ?@ (d + 0x15#64)', 'NN': 'c4 (d + 0x18#64) v.nnoise',
 'B9': '9 ?@ (d + 0x1c#64)', 'B2': '2 ?@ (d + 0x25#64)', 'IV': 'v.invf =@ (d + 0x27#64)',
 'A10': '48 ?@ (d + 0x31#64)', 'A11': '3 ?@ (d + 0x61#64)', 'AM': '4 ?@ (d + 0x64#64)',
 'A13': '0x3898 ?@ (d + 0x68#64)', 'VO': 'cell4 (d + 0x3900#64) v.vOff',
 'A15': '4 ?@ (d + 0x3904#64)', 'A16': '4 ?@ (d + 0x3908#64)', 'A17': '0x4014 ?@ (d + 0x390c#64)',
 'YP': 'c4 (d + 0x7920#64) v.ypos', 'E1': '0xd8bc ?@ (d + 0x7924#64)',
 'EQ': '432 ?@ (d + 0x151e0#64)', 'E3': '0x6c0 ?@ (d + 0x15390#64)',
 'NQ': '15 ?@ (d + 0x15a50#64)', 'E5': '0x3d ?@ (d + 0x15a5f#64)',
 'TE': 'v.te =@ (d + 0x15a9c#64)', 'TQ': 'v.tq =@ (d + 0x15aa6#64)',
 'A26': '3 ?@ (d + 0x15aa9#64)', 'IX': 'Apply.c8 (d + 0x15aac#64) v.idx',
 'TS': '12 ?@ (d + 0x15ab4#64)'}
ORDER = ['A1','A2','NE','FR','A5','NN','B9','B2','IV','A10','A11','AM','A13','VO','A15','A16',
         'A17','YP','E1','EQ','E3','NQ','E5','TE','TQ','A26','IX','TS']

S = [  # SbrS atoms
 ('SR', 'cell4 s d.a.sampleRate'), ('ST', 'cell4 (s + 0x4#64) d.a.start'),
 ('RD', 'cell4 (s + 0x8#64) d.a.ready'), ('ID', 'cell4 (s + 0xc#64) d.a.idAac'),
 ('US', 'cell4 (s + 0x10#64) d.usac'), ('IT', 'cell4 (s + 0x14#64) d.it'),
 ('RS', 'cell4 (s + 0x18#64) d.a.reset'), ('SP', 'd.sp =@ (s + 0x1c#64)'),
 ('S2', '2 ?@ (s + 0x22#64)'), ('AP', 'cell4 (s + 0x24#64) d.amp'), ('S4', '4 ?@ (s + 0x28#64)'),
 ('LB', 'c4 (s + 0x2c#64) d.h.lb'), ('LG', 'c4 (s + 0x30#64) d.a.limGains'),
 ('IP', 'cell4 (s + 0x34#64) d.a.interpol'), ('SM', 'cell4 (s + 0x38#64) d.a.smooth'),
 ('CP', 'cell4 (s + 0x3c#64) d.a.coupling'), ('K0', 'c4 (s + 0x40#64) d.a.k0'),
 ('S16', '16 ?@ (s + 0x44#64)'), ('KX0', 'c4 (s + 0x54#64) d.a.kx0'),
 ('KX1', 'c4 (s + 0x58#64) d.a.kx1'), ('M0', 'c4 (s + 0x5c#64) d.a.m0'),
 ('M1', 'c4 (s + 0x60#64) d.a.m1'), ('PU', 'cell4 (s + 0x64#64) d.a.pushed'),
 ('S18', '0x18 ?@ (s + 0x68#64)')]
T = [  # TabF atoms
 ('N0', 'c4 (s + 0x4c1e0#64) x.n0'), ('N1', 'c4 (s + 0x4c1e4#64) x.n1'),
 ('NQ', 'c4 (s + 0x4c1e8#64) x.nq'), ('NL', 'c4 (s + 0x4c1ec#64) x.nlim'),
 ('T98', '98 ?@ (s + 0x4c1f0#64)'), ('FL', 'x.ftLow =@ (s + 0x4c252#64)'),
 ('FH', 'x.ftHigh =@ (s + 0x4c284#64)'), ('FN', 'x.ftNoise =@ (s + 0x4c2e6#64)'),
 ('FM', 'x.ftLim =@ (s + 0x4c2f2#64)'), ('T2', '2 ?@ (s + 0x4c32e#64)'),
 ('NP', 'c4 (s + 0x4c330#64) x.npatch'), ('PN', 'x.pnum =@ (s + 0x4c334#64)'),
 ('PS', 'x.pstart =@ (s + 0x4c33a#64)')]

def data_minus(names):
    return nest([D[k] for k in ORDER if k not in names])
def sbr_minus(names):
    return nest([v for k, v in S if k not in names])
def tab_minus(names):
    return nest([v for k, v in T if k not in names])

out = []
P = out.append
P('''import Kraken.X64.Examples.Sbr.Parse.DecExtGlueC
import Kraken.X64.Examples.Sbr.Parse.DecExtGlueR
import Kraken.X64.Examples.Sbr.Parse.NoiseSpec
import Kraken.X64.Examples.Sbr.Parse.EnvSpec

/-!
# `ff_aac_sbr_decode_extension`: the `read_sbr_noise` and `read_sbr_envelope` adapters

Both routines read the Huffman tables `ff_aac_sbr_vlc` (`VlcW v`, with `VlcC v`) and log with
`av_log` (state `E`): the caller's `Ext` is `A ⋆ (B ⋆ (VlcW v ⋆ E))` (for the decoder: `A`, `B` the
read-only data of `sbr_reset`, `ExtR`).

* `dataF_n`, `dataF_e`: `DataF` with the raw arrays cut at the parts the routines own
  (`bs_df_noise`, `noise_facs_q`; `bs_df_env`, `bs_amp_res`, `env_facs_q`, `temp_shape`).
* `noise_glue`: `Noise.NoiseSpec k E` gives the local `NoiseSpec (noiseNeed k)`.
* `env_glue`: `read_sbr_envelope`'s statement (a `ProcSpecS` with the bounds trap as a stop) gives
  the local `EnvSpec (envNeed k)`. The routine reads `bs_amp_res` (`+0x64`) at a value, which the
  caller holds as raw bytes (`blk4_cell`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Session
open Kraken.Examples.Sbr.ParseModel Kraken.Examples.Sbr.Vlc

namespace Kraken.Examples.Sbr.DecExt

variable [CodeEnv]

/-! ## Raw bytes -/

omit [CodeEnv] in
theorem blk_cut (a b : BitVec 64) (i j : Nat) (hb : b = a + BitVec.ofNat 64 i)
    (hw : i + j ≤ 2 ^ 64) : (i + j) ?@ a = i ?@ a ⋆ j ?@ b := by
  subst hb; exact Block.split a i j hw

omit [CodeEnv] in
theorem blk_11 (d : BitVec 64) : 11 ?@ (d + 0x1c#64) = 9 ?@ (d + 0x1c#64) ⋆ 2 ?@ (d + 0x25#64) :=
  blk_cut _ _ 9 2 (by rw [BitVec.add_assoc]; rfl) (by omega)

omit [CodeEnv] in
theorem blk_e178 (d : BitVec 64) :
    0xe178 ?@ (d + 0x7924#64) = 0xd8bc ?@ (d + 0x7924#64) ⋆ (432 ?@ (d + 0x151e0#64)
      ⋆ (0x6c0 ?@ (d + 0x15390#64) ⋆ (15 ?@ (d + 0x15a50#64) ⋆ 0x3d ?@ (d + 0x15a5f#64)))) := by
  rw [show (0xe178 : Nat) = 0xd8bc + (432 + (0x6c0 + (15 + 0x3d))) from rfl,
    blk_cut _ (d + 0x151e0#64) _ _ (by rw [BitVec.add_assoc]; rfl) (by omega),
    blk_cut _ (d + 0x15390#64) 432 _ (by rw [BitVec.add_assoc]; rfl) (by omega),
    blk_cut _ (d + 0x15a50#64) 0x6c0 _ (by rw [BitVec.add_assoc]; rfl) (by omega),
    blk_cut _ (d + 0x15a5f#64) 15 _ (by rw [BitVec.add_assoc]; rfl) (by omega)]

omit [CodeEnv] in
/-- Four raw bytes hold some 32-bit value. -/
theorem blk4_cell {a : BitVec 64} {m : Mem 64} (h : (4 ?@ a) m) :
    ∃ v : BitVec 32, cell4 a v m := by
  obtain ⟨-, bs, hlen, rfl⟩ := h
  refine ⟨BitVec.ofInt 32 (Int.ofBytes bs), ?_⟩
  show (Int.toBytes 4 (BitVec.ofInt 32 (Int.ofBytes bs)).toInt =@ a) (bs.At a)
  rw [BitVec.toInt_ofInt, show (2 ^ 32 : Nat) = 256 ^ 4 by decide,
    Int.toBytes_bmod_ofBytes 4 bs hlen]
  rfl

omit [CodeEnv] in
theorem cell4_blk {a : BitVec 64} {v : BitVec 32} {m : Mem 64} (h : cell4 a v m) : (4 ?@ a) m :=
  ⟨by omega, _, Int.toBytes_length 4 _, h⟩

omit [CodeEnv] in
theorem ex4 {X Y G : Mem 64 → Prop} {a : BitVec 64} {m : Mem 64}
    (h : m =⋆ X ⋆ (Y ⋆ (4 ?@ a ⋆ G))) : ∃ v : BitVec 32, m =⋆ X ⋆ (Y ⋆ (cell4 a v ⋆ G)) := by
  obtain ⟨m1, m2, hd, hu, hX, m3, m4, hd2, hu2, hY, m5, m6, hd3, hu3, h4, hG⟩ := h
  obtain ⟨v, hv⟩ := blk4_cell h4
  exact ⟨v, m1, m2, hd, hu, hX, m3, m4, hd2, hu2, hY, m5, m6, hd3, hu3, hv, hG⟩

omit [CodeEnv] in
theorem forget4 {X Y G : Mem 64 → Prop} {a : BitVec 64} {v : BitVec 32} {m : Mem 64}
    (h : m =⋆ X ⋆ (Y ⋆ (cell4 a v ⋆ G))) : m =⋆ X ⋆ (Y ⋆ (4 ?@ a ⋆ G)) :=
  sepM (fun _ h => h) (sepM (fun _ h => h) (sepM (fun _ h => cell4_blk h) (fun _ h => h))) _ h

omit [CodeEnv] in
theorem chA_al (s : BitVec 64) (b : Bool) (h : s.toNat % 32 = 0) : (chA s b).toNat % 32 = 0 := by
  cases b <;> simp only [chA, Bool.false_eq_true, ↓reduceIte, BitVec.toNat_add,
    BitVec.toNat_ofNat] <;> omega
''')

# ---------------- noise
P('/-! ## `read_sbr_noise` -/\n')
P('/-- `DataF` but `bs_num_noise`, `bs_df_noise`, `noise_facs_q`. -/')
P('abbrev DataN (v : DV) (d : BitVec 64) : Mem 64 → Prop :=\n' + wrap(data_minus({'NN','B2','NQ'})) + '\n')
P('''omit [CodeEnv] in
theorem dataF_n (v : DV) (d : BitVec 64) :
    DataF v d = (c4 (d + 0x18#64) v.nnoise ⋆ (2 ?@ (d + 0x25#64) ⋆ 15 ?@ (d + 0x15a50#64)))
      ⋆ DataN v d := by
  simp only [DataF, DataN]; rw [blk_11, blk_e178]; ac_rfl
''')
P('/-- `SbrS` but `bs_coupling`. -/')
P('abbrev ScC (d : DS) (s : BitVec 64) : Mem 64 → Prop :=\n' + wrap(sbr_minus({'CP'})) + '\n')
P('''omit [CodeEnv] in
theorem sbrS_c (d : DS) (s : BitVec 64) : SbrS d s = cell4 (s + 0x3c#64) d.a.coupling ⋆ ScC d s := by
  simp only [SbrS, ScC]; ac_rfl

/-- The caller's part at the `read_sbr_noise` call. -/
abbrev FrN (A B : Mem 64 → Prop) (c : CA) (d : DS) (b : Bool) : Mem 64 → Prop :=
  DataN (chV d b) (chA c.s b) ⋆ (ScC d c.s ⋆ (DataF (chV d !b) (chA c.s !b)
    ⋆ (d.a.psc =@ (c.s + 0x2b600#64) ⋆ (TabQ d.a c.s ⋆ (Block (lab "ceil_log2") 6
    ⋆ (Grid.JtW ⋆ (A ⋆ (B ⋆ c.R))))))))

omit [CodeEnv] in
theorem perm_n (NN D2 DQ DN Cp ScC Do Ps Nq TQ Gb Bb Bc Av Jt A B V E R : Mem 64 → Prop) :
    (((NN ⋆ (D2 ⋆ DQ)) ⋆ DN) ⋆ ((Cp ⋆ ScC) ⋆ (Do ⋆ (Ps ⋆ (Nq ⋆ TQ)))))
      ⋆ (Gb ⋆ ((Bb ⋆ Bc) ⋆ (Av ⋆ (Jt ⋆ (A ⋆ (B ⋆ (V ⋆ E))))))) ⋆ R
    = (Cp ⋆ (Nq ⋆ (NN ⋆ (D2 ⋆ (DQ ⋆ (Av ⋆ (Gb ⋆ (Bb ⋆ (V ⋆ E))))))))) ⋆ (DN ⋆ (ScC ⋆ (Do ⋆ (Ps
      ⋆ (TQ ⋆ (Bc ⋆ (Jt ⋆ (A ⋆ (B ⋆ R))))))))) := by
  ac_rfl

theorem cfn_eq (A B E : Mem 64 → Prop) (v : Nat → VlcTab) (c : CA) (d : DS) (i : BitVec 32)
    (b : Bool) :
    CF (A ⋆ (B ⋆ (VlcW v ⋆ E))) c d i ⋆ c.R = (cell4 (c.s + 0x3c#64) d.a.coupling
      ⋆ (c4 (c.s + 0x4c1e8#64) d.a.nq ⋆ (c4 (chA c.s b + 0x18#64) (chV d b).nnoise
      ⋆ (2 ?@ (chA c.s b + 0x25#64) ⋆ (15 ?@ (chA c.s b + 0x15a50#64) ⋆ (AvW c.ac d.a
      ⋆ (GbR c.g c.r i ⋆ (Blocks [(c.r.buf, c.r.L)] ⋆ (VlcW v ⋆ E))))))))) ⋆ FrN A B c d b := by
  simp only [CF, BufW, Blocks, FrN]
  rw [sbrF_ch d c.s b, dataF_n, SbrO, sbrS_c, tabF_q]
  exact perm_n _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- `read_sbr_noise`'s logical variable at the call. -/
abbrev nxOf (A B : Mem 64 → Prop) (v : Nat → VlcTab) (c : CA) (b : Bool) : Noise.NArgs :=
  ⟨FrN A B c c.d b, c.d.a.coupling, c.d.a.nq, (chV c.d b).nnoise, c.d.a.avctx, c.r.buf, c.i,
    c.r.p8, c.r.L, v⟩

/-- **`read_sbr_noise`'s adapter.** -/
theorem noise_glue (k : Nat) (A B E : Mem 64 → Prop) (v : Nat → VlcTab) (hv : VlcC v)
    (hN : Noise.NoiseSpec k E) : NoiseSpec (Noise.noiseNeed k) (A ⋆ (B ⋆ (VlcW v ⋆ E))) := by
  intro c ra t ⟨⟨hcall, hrok, hdok⟩, h0, h1, h2, h3, hnq, n0, n1⟩
  obtain ⟨b, hb⟩ := ch_of h3
  have hpre : Noise.NoisePre k E (nxOf A B v c b) ra t := by
    refine ⟨?_, ?_, hnq, hv, hrok.1, hrok.2.1, hrok.2.2.1, hrok.2.2.2⟩
    · have hm : t.dmem =⋆ _ ⋆ (_ ⋆ (CF (A ⋆ (B ⋆ (VlcW v ⋆ E))) c c.d c.i ⋆ c.R)) := hcall
      rw [cfn_eq A B E v c c.d c.i b] at hm
      show t.dmem =⋆ _ ⋆ (_ ⋆ (Noise.NoiseF E (nxOf A B v c b) t c.i ⋆ FrN A B c c.d b))
      simp only [Noise.NoiseF, hb, h0, h1, h2]
      exact hm
    · cases b <;> assumption
  refine eventually_weaken _ _ _ _ (fun st hst => ⟨hst.1, ?_⟩) (hN _ ra t hpre)
  obtain ⟨i', hi, -, hsr, hbp, hsv, hm⟩ := hst.2
  refine ⟨c.d, i', rfl, hdok, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, hi, hsr, hbp, hsv, ?_⟩
  show st.1.dmem =⋆ _ ⋆ (_ ⋆ (CF (A ⋆ (B ⋆ (VlcW v ⋆ E))) c c.d i' ⋆ c.R))
  rw [cfn_eq A B E v c c.d i' b]
  simp only [Noise.NoiseF, hb, h0, h1, h2] at hm
  exact hm
''')

# ---------------- env
P('/-! ## `read_sbr_envelope` -/\n')
P('/-- `DataF` but `bs_num_env`, `bs_freq_res`, `bs_df_env`, `bs_amp_res`, `env_facs_q`,\n`temp_shape`. -/')
P('abbrev DataE (v : DV) (d : BitVec 64) : Mem 64 → Prop :=\n' + wrap(data_minus({'NE','FR','B9','AM','EQ','TS'})) + '\n')
P('''omit [CodeEnv] in
theorem dataF_e (v : DV) (d : BitVec 64) :
    DataF v d = 4 ?@ (d + 0x64#64) ⋆ ((c4 (d + 0x8#64) v.nenv ⋆ (v.freqRes =@ (d + 0xc#64)
      ⋆ (9 ?@ (d + 0x1c#64) ⋆ (432 ?@ (d + 0x151e0#64) ⋆ 12 ?@ (d + 0x15ab4#64))))) ⋆ DataE v d) := by
  simp only [DataF, DataE]; rw [blk_11, blk_e178]; ac_rfl
''')
P('/-- `SbrS` but `usac`, `inter_tes`, `bs_coupling`. -/')
P('abbrev ScE (d : DS) (s : BitVec 64) : Mem 64 → Prop :=\n' + wrap(sbr_minus({'US','IT','CP'})) + '\n')
P('/-- `TabF` but `n[0..1]`. -/')
P('abbrev TabE (x : Args) (s : BitVec 64) : Mem 64 → Prop :=\n' + wrap(tab_minus({'N0','N1'})) + '\n')
P('''omit [CodeEnv] in
theorem sbrS_e (d : DS) (s : BitVec 64) : SbrS d s = (cell4 (s + 0x10#64) d.usac
    ⋆ (cell4 (s + 0x14#64) d.it ⋆ cell4 (s + 0x3c#64) d.a.coupling)) ⋆ ScE d s := by
  simp only [SbrS, ScE]; ac_rfl

omit [CodeEnv] in
theorem tabF_e (x : Args) (s : BitVec 64) :
    TabF x s = (c4 (s + 0x4c1e0#64) x.n0 ⋆ c4 (s + 0x4c1e4#64) x.n1) ⋆ TabE x s := by
  simp only [TabF, TabE]; ac_rfl

/-- The caller's part at the `read_sbr_envelope` call. -/
abbrev FrE (A B : Mem 64 → Prop) (c : CA) (d : DS) (b : Bool) : Mem 64 → Prop :=
  DataE (chV d b) (chA c.s b) ⋆ (ScE d c.s ⋆ (DataF (chV d !b) (chA c.s !b)
    ⋆ (d.a.psc =@ (c.s + 0x2b600#64) ⋆ (TabE d.a c.s ⋆ (Block (lab "ceil_log2") 6
    ⋆ (Grid.JtW ⋆ (A ⋆ (B ⋆ c.R))))))))

/-- What `read_sbr_envelope` owns but `bs_amp_res`. -/
abbrev EnvG (E : Mem 64 → Prop) (v : Nat → VlcTab) (c : CA) (d : DS) (i : BitVec 32) (b : Bool) :
    Mem 64 → Prop :=
  (c4 (chA c.s b + 0x8#64) (chV d b).nenv ⋆ ((chV d b).freqRes =@ (chA c.s b + 0xc#64)
    ⋆ (9 ?@ (chA c.s b + 0x1c#64) ⋆ (432 ?@ (chA c.s b + 0x151e0#64)
    ⋆ 12 ?@ (chA c.s b + 0x15ab4#64)))))
  ⋆ ((cell4 (c.s + 0x10#64) d.usac ⋆ (cell4 (c.s + 0x14#64) d.it
    ⋆ (cell4 (c.s + 0x3c#64) d.a.coupling ⋆ (c4 (c.s + 0x4c1e0#64) d.a.n0
    ⋆ c4 (c.s + 0x4c1e4#64) d.a.n1))))
  ⋆ (GbR c.g c.r i ⋆ (AvW c.ac d.a ⋆ (Blocks [(c.r.buf, c.r.L)] ⋆ (VlcW v ⋆ E)))))

omit [CodeEnv] in
theorem perm_e (Am NFD DE Us It Cp ScE Do Ps N0 N1 TE Gb Bb Bc Av Jt A B V E R : Mem 64 → Prop) :
    ((Am ⋆ (NFD ⋆ DE)) ⋆ (((Us ⋆ (It ⋆ Cp)) ⋆ ScE) ⋆ (Do ⋆ (Ps ⋆ ((N0 ⋆ N1) ⋆ TE)))))
      ⋆ (Gb ⋆ ((Bb ⋆ Bc) ⋆ (Av ⋆ (Jt ⋆ (A ⋆ (B ⋆ (V ⋆ E))))))) ⋆ R
    = Am ⋆ ((NFD ⋆ ((Us ⋆ (It ⋆ (Cp ⋆ (N0 ⋆ N1)))) ⋆ (Gb ⋆ (Av ⋆ (Bb ⋆ (V ⋆ E))))))
      ⋆ (DE ⋆ (ScE ⋆ (Do ⋆ (Ps ⋆ (TE ⋆ (Bc ⋆ (Jt ⋆ (A ⋆ (B ⋆ R)))))))))) := by
  ac_rfl

theorem cfe_eq (A B E : Mem 64 → Prop) (v : Nat → VlcTab) (c : CA) (d : DS) (i : BitVec 32)
    (b : Bool) :
    CF (A ⋆ (B ⋆ (VlcW v ⋆ E))) c d i ⋆ c.R
      = 4 ?@ (chA c.s b + 0x64#64) ⋆ (EnvG E v c d i b ⋆ FrE A B c d b) := by
  simp only [CF, BufW, Blocks, FrE, EnvG]
  rw [sbrF_ch d c.s b, dataF_e, SbrO, sbrS_e, tabF_e]
  exact perm_e _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

omit [CodeEnv] in
theorem perm_ea (NE FR B9 Am EQ TS G Fr : Mem 64 → Prop) :
    ((NE ⋆ (FR ⋆ (B9 ⋆ (Am ⋆ (EQ ⋆ TS))))) ⋆ G) ⋆ Fr
      = Am ⋆ (((NE ⋆ (FR ⋆ (B9 ⋆ (EQ ⋆ TS)))) ⋆ G) ⋆ Fr) := by
  ac_rfl

/-- `read_sbr_envelope`'s logical variable at the call, with `bs_amp_res = am`. -/
abbrev exOf (A B : Mem 64 → Prop) (v : Nat → VlcTab) (c : CA) (b : Bool) (am : BitVec 32) :
    Env.EArgs :=
  ⟨FrE A B c c.d b, chV c.d b, c.d.a.n0, c.d.a.n1, c.d.a.coupling, am, c.d.usac, c.d.it,
    c.d.a.avctx, c.r.buf, c.i, c.r.p8, c.r.L, v⟩

theorem efe_eq (A B E : Mem 64 → Prop) (v : Nat → VlcTab) (c : CA) (b : Bool) (am : BitVec 32)
    (t : MachineData) (i : BitVec 32) (h0 : arg0 t = c.ac) (h1 : arg1 t = c.s) (h2 : arg2 t = c.g)
    (h3 : arg3 t = chA c.s b) :
    Env.EF E (exOf A B v c b am) t i ⋆ FrE A B c c.d b
      = cell4 (chA c.s b + 0x64#64) am ⋆ (EnvG E v c c.d i b ⋆ FrE A B c c.d b) := by
  simp only [Env.EF, Env.ChE, Env.SbrE, Env.GbE, Env.InE, EnvG, h0, h1, h2, h3]
  exact perm_ea _ _ _ _ _ _ _ _

/-- **`read_sbr_envelope`'s adapter.** -/
theorem env_glue (k : Nat) (A B E : Mem 64 → Prop) (v : Nat → VlcTab) (hv : VlcC v)
    (hE : Kraken.Examples.Sbr.Parse.ProcSpecS Env.envStops (entry "read_sbr_envelope")
      (Env.EnvPre k E) (Env.EnvPost k E)) :
    EnvSpec (Env.envNeed k) (A ⋆ (B ⋆ (VlcW v ⋆ E))) := by
  intro c ra t ⟨⟨hcall, hrok, hdok⟩, h0, h1, h2, h3, w0, w1, hn0, hn1, hal⟩
  obtain ⟨b, hb⟩ := ch_of h3
  have hm : t.dmem =⋆ _ ⋆ (_ ⋆ (CF (A ⋆ (B ⋆ (VlcW v ⋆ E))) c c.d c.i ⋆ c.R)) := hcall
  rw [cfe_eq A B E v c c.d c.i b] at hm
  obtain ⟨am, hm⟩ := ex4 hm
  have hpre : Env.EnvPre k E (exOf A B v c b am) ra t := by
    refine ⟨?_, ?_, hn0, hn1, hrok.1, hrok.2.1, hrok.2.2.1, hrok.2.2.2, hv, ?_⟩
    · show t.dmem =⋆ _ ⋆ (_ ⋆ (Env.EF E (exOf A B v c b am) t c.i ⋆ FrE A B c c.d b))
      rw [efe_eq A B E v c b am t c.i h0 h1 h2 hb]
      exact hm
    · cases b <;> assumption
    · rw [hb]; exact chA_al c.s b hal
  have hpost : ∀ s, Env.EnvPost k E (exOf A B v c b am) ra t s →
      CPost (Env.envNeed k) (A ⋆ (B ⋆ (VlcW v ⋆ E))) c ra t s fun d' => d' = c.d := by
    intro s hs
    obtain ⟨i', ⟨hi, -⟩, hsr, hbp, hsv, hm'⟩ := hs
    refine ⟨c.d, i', rfl, hdok, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, hi, hsr, hbp, hsv, ?_⟩
    show s.dmem =⋆ _ ⋆ (_ ⋆ (CF (A ⋆ (B ⋆ (VlcW v ⋆ E))) c c.d i' ⋆ c.R))
    rw [cfe_eq A B E v c c.d i' b]
    have hm'' : s.dmem =⋆ _ ⋆ (_ ⋆ (Env.EF E (exOf A B v c b am) t i' ⋆ FrE A B c c.d b)) := hm'
    rw [efe_eq A B E v c b am t i' h0 h1 h2 hb] at hm''
    exact forget4 hm''
  exact eventually_weaken _ _ _ _ (fun st hst => hst.imp (fun h => ⟨h.1, hpost _ h.2⟩) id)
    (hE _ ra t hpre)

end Kraken.Examples.Sbr.DecExt
''')
if __name__ == "__main__":
    sys.stdout.write("\n".join(out))
