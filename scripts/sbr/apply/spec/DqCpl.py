# entries of shard DqCpl (coupled-stereo sbr_dequant: envelope loop L68b0.., noise loop L6abf..)
# owner of this file: apply-dqcpl (helper); IN boundaries L68b0 (from L6838_2), L6abf (from L6838_1).

BASE = "(ApplyC x t₀ ∧ IdLive t₀ x) ∧ Base t₀ s ∧ s.regs.get64 .r9 = arg1 t₀"
MEM = "(s.dmem =⋆ Mm k e x ra t₀ (FrD x t₀))"

# envelope loop, e = rbx ∈ [1, nenv]; r12/r13 = rows e of data[1].env_facs_q / env_facs
ENV = ("1 ≤ ee ∧ ee ≤ x.d0.nenv ∧ s.regs.get64 .rbx = BitVec.ofNat 64 ee"
       " ∧ s.regs.get64 .r12 = arg1 t₀ + 0x53640#64 + BitVec.ofNat 64 (0x30 * ee)"
       " ∧ s.regs.get64 .r13 = arg1 t₀ + 0x537f0#64 + BitVec.ofNat 64 (0xc0 * ee)")
K_LT = "kk < 48 ∧ s.regs.get64 .r14 = BitVec.ofNat 64 kk"
K_LE = "kk ≤ 48 ∧ s.regs.get64 .r14 = BitVec.ofNat 64 kk"
RAX = "(s.regs.get64 .rax).toNat ≤ 1"

# noise loop, e = rdx = j + 1 ∈ [1, nnoise], rsi = 5 j, rax = nnoise + 1, xmm0 = 1E20
NZ = ("jj + 1 ≤ x.d0.nnoise ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (jj + 1)"
      " ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (5 * jj)"
      " ∧ s.regs.get64 .rax = BitVec.ofNat 64 (x.d0.nnoise + 1)"
      " ∧ BitVec.extractLsb' 0 64 (s.zmms.get (AvxReg.xmm RegMm.mm0)) = dbl1E20")
X2 = "(BitVec.setWidth 32 (s.zmms.get (AvxReg.xmm RegMm.mm2))).toNat ≤ 0x43000000"


def D(r):  # the byte q in r (rdi or r8), ecx = 7 - q (32 bit)
    return ("dd < 256 ∧ 134 ≤ dd ∧ s.regs.get64 .%s = BitVec.ofNat 64 dd"
            " ∧ s.regs.get64 .rcx = BitVec.setWidth 64 (7#32 - BitVec.ofNat 32 dd)" % r)


def env(i, *extra, k=None):
    parts = [ENV] + list(extra)
    body = " ∧ ".join(parts)
    if k:
        return f"{BASE} ∧ (∃ ee kk : Nat, {body} ∧ {k}) ∧ {MEM}"
    return f"{BASE} ∧ (∃ ee : Nat, {body}) ∧ {MEM}"


def nz(*extra, d=None):
    body = " ∧ ".join([NZ] + list(extra))
    if d:
        return f"{BASE} ∧ (∃ jj dd : Nat, {body} ∧ {D(d)}) ∧ {MEM}"
    return f"{BASE} ∧ (∃ jj : Nat, {body}) ∧ {MEM}"


def define(g):
    E = g.entry
    # envelope loop
    E("L68b0", env("L68b0"))
    E("L68f8", env("L68f8", RAX, k=K_LE))
    for i in ["L6940", "L6940_1", "L69a4", "L69d0", "L69dd", "L6a10", "L6a30", "L68d0", "L68d0_1"]:
        E(i, env(i, RAX, k=K_LT))
    # after the av_log call r9 is reloaded from the frame (slot che)
    E("L6a30_1", f"(ApplyC x t₀ ∧ IdLive t₀ x) ∧ Base t₀ s ∧ (∃ ee kk : Nat, {ENV} ∧ {K_LT}) ∧ {MEM}")
    E("L6a30_2", f"(ApplyC x t₀ ∧ IdLive t₀ x) ∧ Base t₀ s ∧ (∃ ee kk : Nat, {ENV} ∧ {K_LT}) ∧ {MEM}")
    E("L6a90", env("L6a90"))
    # noise loop (L6abf: boundary entry, the shared L74de form)
    E("L6abf", f"{BASE} ∧ {MEM}")
    for i in ["L6b12", "L6b00", "L6b02", "L6bbc_1", "L6c7d_1", "L6c7d_2", "L6ce0",
              "L6d51_1", "L6e23_1", "L6eeb_1", "L6eeb_2"]:
        E(i, nz())
    for i in ["L6b6c", "L6ba0", "L6bbc", "L6c3a", "L6c61", "L6c7d", "L6d09", "L6d32", "L6d51",
              "L6ddb", "L6e04", "L6e23", "L6ea8", "L6ecf", "L6eeb"]:
        E(i, nz(X2))
    for i in ["L6b50", "L6c1e", "L6e8c"]:
        E(i, nz(d="rdi"))
    for i in ["L6cea", "L6dbc"]:
        E(i, nz(d="r8"))


_define_entries = define


def define(g):
    _define_entries(g)
    # variant: the two enclosing Entry-region loops (4,60),(8,60) are never re-entered from here: 0
    O = ["0", "0"]
    ENVM = "9 - (s.regs.get64 .rbx).toNat"
    for i in ["L68b0", "L6a90"]:
        g.measure(i, O + [ENVM])
    for i in ["L68d0", "L68d0_1"]:
        g.measure(i, O + [ENVM, "2 * (48 - (s.regs.get64 .r14).toNat)"])
    for i in ["L68f8", "L6940", "L6940_1", "L69a4", "L69d0", "L69dd", "L6a10", "L6a30", "L6a30_1", "L6a30_2"]:
        g.measure(i, O + [ENVM, "2 * (48 - (s.regs.get64 .r14).toNat) + 1"])
    g.measure("L6abf", O)
    for i in ["L6b00", "L6b02"]:
        g.measure(i, O + ["2 * (3 - (s.regs.get64 .rdx).toNat)"])
    for i in ["L6b12", "L6b50", "L6b6c", "L6ba0", "L6bbc", "L6bbc_1", "L6c1e", "L6c3a", "L6c61", "L6c7d",
              "L6c7d_1", "L6c7d_2", "L6ce0", "L6cea", "L6d09", "L6d32", "L6d51", "L6d51_1", "L6dbc",
              "L6ddb", "L6e04", "L6e23", "L6e23_1", "L6e8c", "L6ea8", "L6ecf", "L6eeb", "L6eeb_1", "L6eeb_2"]:
        g.measure(i, O + ["2 * (3 - (s.regs.get64 .rdx).toNat) + 1"])

# envelope loop (r14 = kk): plain Base; L6abf (from L6838_1 or L6a90 `mov $0,%r14d`) + noise loop: BaseZ
ENV_IDS = {"L68b0", "L68f8", "L6940", "L6940_1", "L69a4", "L69d0", "L69dd", "L6a10", "L6a30", "L68d0",
           "L68d0_1", "L6a30_1", "L6a30_2", "L6a90"}

# ---- apply (push/BaseZ rebuild): the dequant runs on x.push; r14 = 0 (BaseZ) where noted ----
_define_dq = define


def define(g):
    orig = g.entry

    def ent(i, text):
        text = text.replace("Mm k e x ra", "Mm k e x.push ra")
        if i not in ENV_IDS:
            text = text.replace("Base t₀ s", "BaseZ t₀ s", 1)
        orig(i, text)
    g.entry = ent
    try:
        _define_dq(g)
    finally:
        del g.entry
