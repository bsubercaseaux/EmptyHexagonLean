import Geo.Encoding

open LeanSAT

instance : Solver IO := Solver.Impl.DimacsCommand "cadical"

def main : IO Unit :=
  let enc := Geo.theEncoding (by decide : 4 ≥ 3) |>.val.toICnf
  Solver.Dimacs.printFormula (IO.print) enc

open Model PropFun
axiom cnfUnsat : ¬∃ τ : PropAssignment IVar,
  τ ⊨ (Geo.theEncoding (by decide : 10 ≥ 3) |>.val.toICnf.toPropFun)
