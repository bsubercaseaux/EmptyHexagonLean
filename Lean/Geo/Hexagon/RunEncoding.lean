import Geo.Hexagon.Encoding

open LeanSAT

instance : Solver IO := Solver.Impl.DimacsCommand "cadical"

def main (args : List String) : IO Unit := do
  match args with
  | [] => IO.println "expected one argument (number of points)"
  | n::_ =>
  let some n := String.toNat? n
    | throw (.userError "hi")
  let enc := Geo.theEncoding n |>.val.toICnf
  Solver.Dimacs.printFormula (IO.print) enc
