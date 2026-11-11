# Interface entries of sbr_reset (owner: reset). The shards A1, A2, B add their own files
# (spec/A1.py, spec/A2.py, spec/B.py) with the entries of their blocks; an id may be defined in
# one file only. Each entry is the Lean text of a Prop in `k e a ra t₀ s`.
ENTRIES = {
    # the entry: the precondition, unchanged state
    "start": "s = t₀ ∧ ResetPre k e a ra t₀",
    # sbr_make_f_master succeeded (A1 / A2 -> B)
    "L2012": "AtDerived k e a ra t₀ s",
    # every failure: the last av_log, then sbr_turnoff (A1 / A2 / B -> B)
    "L1d31": "AtFail k e a ra t₀ s",
    # the epilogue
    "L1d95": "AtExit k e a ra t₀ s",
    # after the pops, before `ret`
    "done": "ResetCI a t₀ ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp "
            "∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp ∧ SavedRegs t₀ s "
            "∧ ∃ (x' : Args) (sp' : List UInt8) (us' : BitVec 32), ResetOut a x' sp' us' "
            "∧ (s.dmem =⋆ RetCell ra (t₀.regs.get64 .rsp) ⋆ (Reserve (resetNeed k) "
            "(t₀.regs.get64 .rsp) ⋆ (RF e { a with x := x', sp := sp', us := us' } t₀ ⋆ a.x.R)))",
}
