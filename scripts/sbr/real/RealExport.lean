import Kraken.X64.PrintIntel
import KrakenSbrReal.Real

/-! The real image, step 1: print every cell of the elaborated image `Real.rImg` as laid out
by `Real.rLayout 0` (the link-time layout `Real.rCE 0`): its address, its size and the cell
(a label, an instruction in Intel syntax via `Kraken/X64/PrintIntel.lean`, or a byte cell).
The addresses are computed here from the layout, the same way `Executable.addrOf` does
(the start plus the sizes of the cells before). Also prints, per text of `Real.rTexts`, its
entry label. Output: `$SBR_REAL_OUT/cells.txt` (set by `check.sh`). -/

open Kraken.Examples.Sbr.Real

def cellLine (a z : Nat) (d : Directive) : String :=
  let hex := String.mk (Nat.toDigits 16 a)
  match d with
  | .label l => s!"{hex} {z} L {l}"
  | .instr _ => s!"{hex} {z} I {toString d}"
  | .byteArray _ => s!"{hex} {z} B"

def main : IO Unit := do
  let some dir ← IO.getEnv "SBR_REAL_OUT"
    | throw (IO.userError "RealExport.lean: SBR_REAL_OUT is not set (run it through check.sh)")
  IO.FS.createDirAll dir
  let cells := ((rLayout 0) rImg).2
  let start := ((rLayout 0) rImg).1
  let mut a := start.toBitVec.toNat
  let mut out : Array String := #[]
  for (d, z) in cells do
    out := out.push (cellLine a z d)
    a := a + z
  IO.FS.writeFile s!"{dir}/cells.txt" ("\n".intercalate out.toList ++ "\n")
  let ents := rTexts.map fun t => match t with
    | .label l :: _ => l
    | _ => "?"
  IO.FS.writeFile s!"{dir}/texts.txt" ("\n".intercalate ents ++ "\n")
  IO.println s!"cells: {cells.length}, end {String.mk (Nat.toDigits 16 a)}"

#eval main
