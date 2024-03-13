import Geo.Naive.Encoding
import Geo.Hexagon.Encoding
import LeanSAT.Solver.Dimacs

open LeanSAT

-- instance : Solver IO := Solver.Impl.DimacsCommand "cadical"

def main (args : List String) : IO Unit := do
  let help {α} : IO α := do
    IO.println "\
      usage: lake exe encode (gon|hole) <k> <n> [vars.out]\n\
      where 3 <= k <= 6"
    IO.Process.exit 1
  let kind::k::n::rest := args | help
  match kind with
  | "gon" => IO.println "TODO: k-gon encoding unsupported"
  | "hole" =>
    let some k := String.toNat? k | help
    let some n := String.toNat? n | help
    let rlen + 1 := n | throw (.userError "n must be positive")
    let (vars, enc) ← if k = 6 then
      pure <| (Geo.hexagonEncoding rlen).toICnf compare
    else
      pure <| (Geo.naiveEncoding k rlen).toICnf compare
    if let out::_ := rest then
      let h ← IO.FS.Handle.mk out IO.FS.Mode.write
      for v in vars do
        h.putStrLn v.toCode
    Solver.Dimacs.printFormula (IO.print) enc
  | _ => help
