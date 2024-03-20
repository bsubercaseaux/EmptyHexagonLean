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
  let some k := String.toNat? k | help
  let some n := String.toNat? n | help
  let rlen + 1 := n | throw (.userError "n must be positive")
  let holes ← match kind with
  | "gon" => pure false
  | "hole" => pure true
  | _ => help
  let (vars, enc) ← if k == 6 then
    pure <| (Geo.hexagonEncoding rlen holes).toICnf compare
  else if holes then
    pure <| (Geo.naiveEncoding k rlen).toICnf compare
  else
    IO.println "TODO: k-gon encoding only supported for k=6"
    IO.Process.exit 1
  if let out::_ := rest then
    let h ← IO.FS.Handle.mk out IO.FS.Mode.write
    for v in vars do
      h.putStrLn v.toCode
    Solver.Dimacs.printFormula IO.print enc
  else
    -- FOR TESTING PURPOSES ONLY, the variable renaming is unverified
    let r4 (a b c d : Nat) : Nat :=
      a + (b-2)*(b-1)/2 + (c-3)*(c-2)*(c-1)/6 + (d-4)*(d-3)*(d-2)*(d-1)/24
    let r3 a b c := r4 a b c 0
    let inside (x a b c : Nat) :=
      let (l, r) := if x > b then (b, x) else (x, b)
      r3 0 0 (n+1) + 2 * r4 a l r c - (if x < b then 1 else 0)
    let hole a b c :=
      r4 0 0 (n+1) (n+1) + r4 a b c (n+1)
    let nVars :=
      r3 0 0 (n+1) -- base variables
      + 2 * r4 0 0 0 (n+1) -- inside variables
      + r3 0 0 (n+1)  -- hole variables
      + 3 * r3 0 0 (n+1)
    let aux := 1 + 2 * r4 0 0 (n+1) (n+1)
    let def_ a b c d := aux + 3 * r3 a b c + d
    let toNat
    | .sigma a b c => r3 (a+2) (b+2) (c+2)
    | .inside x a b c => inside (x+2) (a+2) (b+2) (c+2)
    | .hole₀ a b c => hole (a+1) (b+2) (c+2)
    | .cap a b c => def_ (a+2) (b+2) (c+2) 0
    | .cup a b c => def_ (a+2) (b+2) (c+2) 1
    | .capF a b c => def_ (a+2) (b+2) (c+2) 2
    | .arc .. => 0
    let m (v : Nat) : Nat :=
      match vars[v]? with
      | none => v - vars.size + nVars
      | some var => toNat var
    let enc : ICnf := enc.map <| Array.map fun l =>
      LitVar.mkLit ILit (m (LitVar.toVar l).natPred - 1).succPNat (LitVar.polarity l)
    -- for v in vars do
    --   IO.eprintln s!"{repr v}: {toNat v}"
    Solver.Dimacs.printFormula IO.print enc
