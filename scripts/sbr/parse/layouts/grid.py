# Layout of read_sbr_grid's footprint, for focus.py (output: Parse/GridFoot.lean).
P = "(k : Nat) (Ext : Mem 64 → Prop) (x : GArgs) (ra : Int64) (t₀ : MachineData) " \
    "(FR : (Mem 64 → Prop) → Mem 64 → Prop) (st : GSt)"
A = "k Ext x ra t₀ FR st"
D = "arg3 t₀"
G = "arg2 t₀"
R = "t₀.regs.get64 .rsp"

LAYOUT = {
    "source": "scripts/sbr/parse/layouts/grid.py",
    "namespace": "Kraken.Examples.Sbr.Grid",
    "header": "import Kraken.X64.Examples.Sbr.Parse.GridSpec",
    "doc": """# `read_sbr_grid`: the footprint and its focus lemmas

Inside the proof the byte arrays of `*ch_data` (`bs_freq_res`, `t_env` with `t_env_num_env_old`,
`t_q`) are one 1-byte cell per element (`FrB`, `TeB`, `TqB`), so that every access at a
constant offset matches a cell; an access at a variable index uses the array lemmas, proved
once by a case split on the index. `ChB` and `ChW` describe the same bytes.""",
    "opens": """open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false""",
    "prelude": """variable [CodeEnv]

def Rest (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) : Mem 64 → Prop :=
  RetCell ra (t₀.regs.get64 .rsp) ⋆ R

abbrev Saved (t₀ : MachineData) (K : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  c8 (r - 0x28#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ K))))

abbrev BlankS (r : BitVec 64) (K : Mem 64 → Prop) : Mem 64 → Prop :=
  8 ?@ (r - 0x28#64) ⋆ (8 ?@ (r - 0x20#64) ⋆ (8 ?@ (r - 0x18#64) ⋆ (8 ?@ (r - 0x10#64)
    ⋆ (8 ?@ (r - 0x8#64) ⋆ K))))""",
    "params": P,
    "args": A,
    "arrays": [
        {"name": "FrB", "off": 0xc, "len": 9, "doc": "bs_freq_res[9]"},
        {"name": "TeB", "off": 0x15a9c, "len": 10, "doc": "t_env[9], t_env_num_env_old"},
        {"name": "TqB", "off": 0x15aa6, "len": 3, "doc": "t_q[3]"},
    ],
    "groups": [
        {"name": "ChB", "params": ["d", "st"], "binders": "(d : BitVec 64) (st : GSt)",
         "doc": "`*ch_data` with the arrays byte by byte (`e_a[2]` as two 4-byte cells).",
         "body": [{"name": "cls", "e": "4 ?@ d"},
                  {"name": "n", "e": "cell4 (d + 8#64) st.n"},
                  {"g": "FrB", "a": ["d", "st.fr"]},
                  {"name": "nn", "e": "cell4 (d + 0x18#64) st.nn"},
                  {"name": "x64", "e": "4 ?@ (d + 0x64#64)"},
                  {"name": "ea0", "e": "4 ?@ (d + 0x3904#64)"},
                  {"name": "ea1", "e": "4 ?@ (d + 0x3908#64)"},
                  {"g": "TeB", "a": ["d", "st.te"]},
                  {"g": "TqB", "a": ["d", "st.tq"]}]},
        {"name": "GbW", "params": ["g", "x", "i"], "emit": False,
         "body": [{"name": "buf", "e": "Int.toBytes 8 x.buf.toInt =@ g"},
                  {"name": "idx", "e": "cell4 (g + 8#64) i"},
                  {"name": "sib", "e": "4 ?@ (g + 0xc#64)"},
                  {"name": "p8", "e": "cell4 (g + 0x10#64) x.p8"}]},
        {"name": "InW", "params": ["Ext", "x", "t"], "emit": False,
         "body": [{"name": "usac", "e": "cell4 (arg1 t + 0x10#64) x.usac"},
                  {"name": "amp", "e": "cell4 (arg1 t + 0x24#64) x.ampHdr"},
                  {"name": "avctx", "e": "Int.toBytes 8 x.avctx.toInt =@ (arg0 t + 8#64)"},
                  {"name": "blocks", "e": "Blocks [(x.buf, x.L), (lab \"ceil_log2\", 6)]"},
                  {"name": "jt", "e": "JtW"},
                  {"name": "ext", "e": "Ext"}]},
        {"name": "GFB", "params": ["Ext", "x", "t", "st"],
         "binders": "(Ext : Mem 64 → Prop) (x : GArgs) (t : MachineData) (st : GSt)",
         "body": [{"g": "ChB", "a": ["arg3 t", "st"]},
                  {"g": "GbW", "a": ["arg2 t", "x", "st.i"]},
                  {"g": "InW", "a": ["Ext", "x", "t"]}]},
    ],
    "Tdoc": "The memory at every label: the slot of a callee's return address, the callee's "
            "reservation, the footprint, and the frame (`FR`: the saved registers or their "
            "blank slots) around the caller's memory.",
    "T": [{"name": "slot30", "e": f"8 ?@ ({R} - 0x30#64)"},
          {"name": "reserve", "e": f"Reserve k ({R} - 0x30#64)"},
          {"g": "GFB", "a": ["Ext", "x", "t₀", "st"]},
          {"name": "frame", "e": "FR (Rest x.R ra t₀)"}],
    "focus": [
        {"lemma": "T_fr", "target": ["FrB"], "tx": "TxFr"},
        {"lemma": "T_te", "target": ["TeB"], "tx": "TxTe"},
        {"lemma": "T_tq", "target": ["TqB"], "tx": "TxTq"},
        {"lemma": "T_i", "target": ["idx"], "tx": "TxI"},
        {"lemma": "T_n", "target": ["n"], "tx": "TxN"},
        {"lemma": "T_nn", "target": ["nn"], "tx": "TxNn"},
        {"lemma": "T_cls", "target": ["cls"], "tx": "TxCls"},
        {"lemma": "T_x64", "target": ["x64"], "mode": "exists", "tx": "TxX64"},
        {"lemma": "T_ea0", "target": ["ea0"], "tx": "TxEa0"},
        {"lemma": "T_ea1", "target": ["ea1"], "tx": "TxEa1"},
        {"lemma": "T_amp", "target": ["amp"], "mode": "exists", "tx": "TxAmp"},
        {"lemma": "T_usac", "target": ["usac"], "mode": "exists", "tx": "TxUsac"},
        {"lemma": "T_avctx", "target": ["avctx"], "mode": "exists", "tx": "TxAvctx"},
        {"lemma": "T_jt", "target": ["jt"], "mode": "exists", "tx": "TxJt"},
        {"lemma": "T_ext", "target": ["slot30", "reserve", "ext"], "mode": "exists",
         "tx": "TxExt"},
        {"lemma": "T_gb", "target": ["GbW"], "mode": "hyp", "tx": "TxGb"},
        {"lemma": "T_blocks", "target": ["blocks"], "mode": "hyp", "tx": "TxBlocks"},
    ],
    "custom": [
        {"lemma": "T_saved", "doc": "`T` with the saved registers at the head.",
         "binders": "(k : Nat) (Ext : Mem 64 → Prop) (x : GArgs) (ra : Int64) "
                    "(t₀ : MachineData) (st : GSt)",
         "lhs": "T k Ext x ra t₀ (Saved t₀) st",
         "rhs": f"Saved t₀ (8 ?@ ({R} - 0x30#64) ⋆ (Reserve k ({R} - 0x30#64) "
                "⋆ (GFB Ext x t₀ st ⋆ Rest x.R ra t₀)))",
         "unfold": ["T", "Saved"]},
        {"lemma": "T_ret", "doc": "`T` with the return address at the head.",
         "binders": "(k : Nat) (Ext : Mem 64 → Prop) (x : GArgs) (ra : Int64) "
                    "(t₀ : MachineData) (st : GSt)",
         "lhs": "T k Ext x ra t₀ (Saved t₀) st",
         "rhs": f"RetCell ra ({R}) ⋆ (8 ?@ ({R} - 0x30#64) ⋆ (Reserve k ({R} - 0x30#64) "
                "⋆ (GFB Ext x t₀ st ⋆ Saved t₀ x.R)))",
         "unfold": ["T", "Saved", "Rest"]},
    ],
    "access": [
        {"kind": "array_list", "array": "FrB"},
        {"kind": "array_list", "array": "TeB"},
        {"kind": "array_list", "array": "TqB"},
        {"kind": "array", "atom": "FrB", "suffix": "Fr", "base": D, "list": "st.fr",
         "stvar": "st", "upd": "st.setFr {j} {v}"},
        {"kind": "array", "atom": "TeB", "suffix": "Te", "base": D, "list": "st.te",
         "stvar": "st", "upd": "st.setTe {j} {v}"},
        {"kind": "array", "atom": "TqB", "suffix": "Tq", "base": D, "list": "st.tq",
         "stvar": "st", "upd": "st.setTq {j} {v}"},
        {"kind": "cell4", "atom": "idx", "addr": f"{G} + 8#64", "val": "st.i",
         "load": "T_loadI", "store": "T_storeI", "stvar": "st", "upd": "st.withI {v}",
         "doc": "The reader's index."},
        {"kind": "cell4", "atom": "n", "addr": f"{D} + 8#64", "val": "st.n",
         "load": "T_loadN", "store": "T_storeN", "stvar": "st", "upd": "st.withN {v}",
         "doc": "`bs_num_env`."},
        {"kind": "cell4", "atom": "nn", "addr": f"{D} + 0x18#64", "val": "st.nn",
         "load": "T_loadNn", "store": "T_storeNn", "stvar": "st", "upd": "st.withNn {v}",
         "doc": "`bs_num_noise`."},
        {"kind": "cell4", "atom": "amp", "addr": "arg1 t₀ + 0x24#64", "val": "x.ampHdr",
         "load": "T_load_amp", "doc": "`sbr->bs_amp_res_header`."},
        {"kind": "cell4", "atom": "usac", "addr": "arg1 t₀ + 0x10#64", "val": "x.usac",
         "load": "T_load_usac", "doc": "`sbr->usac`."},
        {"kind": "cell8", "atom": "avctx", "addr": "arg0 t₀ + 8#64", "val": "x.avctx",
         "load": "T_load_avctx", "doc": "`ac->avctx`."},
        {"kind": "slot", "atom": "x64", "addr": f"{D} + 0x64#64", "size": 4,
         "load": "T_load_x64", "store": "T_store_x64", "doc": "`bs_amp_res` (raw)."},
        {"kind": "slot", "atom": "cls", "addr": D, "size": 4,
         "load": "T_load_cls", "store": "T_store_cls", "doc": "`bs_frame_class` (raw)."},
        {"kind": "slot", "atom": "ea0", "addr": f"{D} + 0x3904#64", "size": 4,
         "load": "T_load_ea0", "store": "T_store_ea0", "doc": "`e_a[0]` (raw)."},
        {"kind": "slot", "atom": "ea1", "addr": f"{D} + 0x3908#64", "size": 4,
         "load": "T_load_ea1", "store": "T_store_ea1", "doc": "`e_a[1]` (raw)."},
    ],
}
