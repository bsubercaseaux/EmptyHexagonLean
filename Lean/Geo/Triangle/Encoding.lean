import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Range
import Geo.SAT.ToLeanSAT.EncodeProof
import Geo.KGon.Var
import Geo.KGon.Encoding

namespace Geo

open LeanSAT Var

def noHoleClauses (n : Nat) : PropForm (Var n) :=
  .forAll (Fin n) fun a =>
  .forAll (Fin n) fun b =>
  .guard (a < b) fun _ =>
  .forAll (Fin n) fun c =>
  .guard (b < c) fun _ =>
    .not (hole a b c)

def triangleEncoding (n : Nat) : PropForm (Var n) :=
  .and (baseEncoding n) (noHoleClauses n)

def triangleCNF (rlen : Nat) : ICnf := (Geo.triangleEncoding rlen |>.toICnf compare).2

-- set_option profiler true in
-- #eval let cnf := Geo.triangleCNF 10; (cnf.size, cnf.maxVar)
