import Geo.NGon.EncodingNew
import LeanSAT.Solver.Dimacs

open LeanSAT

-- instance : Solver IO := Solver.Impl.DimacsCommand "cadical"

def main (args : List String) : IO Unit := do
  match args with
  | [] => IO.println "expected one argument (number of points)"
  | n::rest =>
  let some n := String.toNat? n
    | throw (.userError "hi")
  let (vars, enc) := Geo.hexagonEncoding n |>.toICnf compare
  if let out::_ := rest then
    let h ← IO.FS.Handle.mk out IO.FS.Mode.write
    for v in vars do
      h.putStrLn v.toCode
  Solver.Dimacs.printFormula (IO.print) enc
