import Kraken.X64.Examples.Sbr.Parse.ResetQs2Lib2

/-!
# `sbr_reset`, `AV_QSORT` copy 2: more helper lemmas (the scan loop, the pushes)
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Parse Kraken.Examples.Sbr.Parse.Qsort

namespace Kraken.Examples.Sbr.Reset

/-- A variant step with an equal measure and phase, and a smaller last digit. -/
theorem lex_last_lt {x a b p d d' : Nat} (h : a = b) (hd : d % 2 ^ 64 < d' % 2 ^ 64) :
    lex [x, a, p, d] < lex [x, b, p, d'] := by
  subst h
  exact lex_cons_lt_cons rfl (lex_cons_lt_cons rfl (lex_cons_lt_cons rfl
    (lex_cons_lt_of_lt rfl hd)))

end Kraken.Examples.Sbr.Reset
