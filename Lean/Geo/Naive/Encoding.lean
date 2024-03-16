import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Range
import Geo.SAT.ToLeanSAT.EncodeProof
import Geo.KGon.Var
import Geo.KGon.Encoding

namespace Geo

open LeanSAT Var

def noKHoleClausesCore (n k : Nat) (i : Nat)
    (G1 : Fin n → Fin n → PropForm (Var n)) (G2 : Fin n → PropForm (Var n)) : PropForm (Var n) :=
  if 0 < k then
    .guard (i < n) fun hi =>
    .and (.imp (G2 ⟨i, hi⟩) <|
      noKHoleClausesCore n (k-1) (i+1)
        (fun b c => .and (Var.hole ⟨i, hi⟩ b c) (G1 b c))
        (fun c => .and (G1 ⟨i, hi⟩ c) (G2 c))) <|
    noKHoleClausesCore n k (i+1) G1 G2
  else
    .false
termination_by n - i
decreasing_by all_goals decreasing_with omega

def noKHoleClauses (k n : Nat) : PropForm (Var n) :=
  .guard (0 < k) fun _ =>
    .and (noKHoleClausesCore n (k-1) 0 (fun b c => Var.hole₀ 0 b c) (fun _ => .true)) <|
    noKHoleClausesCore n k 0 (fun _ _ => .true) (fun _ => .true)

def naiveEncoding (k n : Nat) : PropForm (Var n) :=
  .flatCNF <| .all #[baseEncoding n, signotopeClauses2 n, holeDefClauses0 n, noKHoleClauses k n]

def naiveCNF (k rlen : Nat) : ICnf := (Geo.naiveEncoding k rlen |>.toICnf compare).2

-- set_option profiler true in
-- #eval let cnf := Geo.naiveCNF 10; (cnf.size, cnf.maxVar)
