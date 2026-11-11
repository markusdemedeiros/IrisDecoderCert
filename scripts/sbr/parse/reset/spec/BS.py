# Entries of shard B, part goal_sb search of `sbr_hf_calc_npatches` (owner: noise, helper of
# reset): L2cc2, L2d03, ..., L3093, L30c9 (the unrolled search over f_master for the first
# entry >= goal_sb).
#
# The entries carry `PFix` (with `1 <= n_q`) and the frame slots 0x48/0x50/0x80 of gB's `AtPat`.
# They are established only by `L2c89` (and through it the f_tablenoise loop / `L2bb5`), which
# is left an explicit OPEN obligation of `ResetOpen`: `1 <= n_q` needs a log2f hypothesis
# (`NqOK`) and the slots 0x50/0x80 need facts carried from `L2b30`; nothing here assumes them
# silently.
LEMMAS = r"""
/-! ## Shard B: the `goal_sb` search (owner noise) -/

/-- The unrolled `goal_sb` search at index `j` (blocks `L2cc2` … `L30c9`): `goal_sb <
kx[1] + m[1]`, every `f_master[i]`, `i < j`, below `goal_sb`, `eax = goal_sb`, the values of
`L30df` (`num_patches = 0`), `esi = k[0]`, `r12 = sbr`. -/
def AtSrch (j : Nat) (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtPat k e a ra t₀ s (fun st c => goalSb a.x.sampleRate.toInt < ptop a c (fOf st)
    ∧ (∀ i, i < j → ((fOf st) i : Int) < goalSb a.x.sampleRate.toInt)
    ∧ st.x = { px0 a c (fOf st) with npatch := 0 }
    ∧ s.regs.get64 .rsi = BitVec.ofNat 64 (pk0 c) ∧ s.regs.get64 .r12 = arg1 t₀
    ∧ s.regs.get64 .rax = BitVec.ofNat 64 (goalSb a.x.sampleRate.toInt).toNat)
"""

_J = {"L2cc2": 0, "L2d03": 3, "L2d45": 6, "L2d87": 9, "L2dc9": 12, "L2e0b": 15, "L2e4d": 18,
      "L2e8f": 21, "L2ed1": 24, "L2f13": 27, "L2f55": 30, "L2f97": 33, "L2fd9": 36, "L301b": 39,
      "L305d": 42, "L3093": 45, "L30c9": 48}

ENTRIES = {lab: f"AtSrch {j} k e a ra t₀ s" for lab, j in _J.items()}
