import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Range
import Geo.SAT.ToLeanSAT.EncodeProof
import Geo.KGon.Var
import Geo.KGon.Encoding

namespace Geo

open LeanSAT Var

def arc2 (o : Orientation) (sz : Nat) (a c : Fin n) : PropForm (Var n) :=
  match sz with
  | 0 => .true
  | sz+1 =>
    .atomic <| .flatCNF <|
    .exists (Fin n) fun b =>
    .andP (a.1+sz < b.1 ∧ b < c) fun _ =>
    arc o sz a b c

def noKGon2Arc (n sz1 sz2 : Nat) : PropForm (Var n) :=
  .forAll (Fin n) fun a =>
  .forAll (Fin n) fun b =>
  .impP (a.1+sz1+sz2 < b.1) fun _ =>
  .not <| .and (arc2 .ccw sz1 a b) (arc2 .cw sz2 a b)

-- for k = 6:
--
-- 1            ..       ...       ....
--  a     b   a    b   a     b   a      b
--    ...       ..       .
def noGonClauses (k n : Nat) : PropForm (Var n) :=
  .impP (3 ≤ k) fun _ =>
  .and (noKGon2Arc n (k-3) 0) <|
  .forAll (Fin (k-3)) fun ⟨sz1, _⟩ =>
  noKGon2Arc n sz1 (k-2-sz1)

def gonEncoding (k n : Nat) : PropForm (Var n) :=
  .all #[
    baseEncoding n false, signotopeClauses2 n,
    arcDefClausesUpTo n .ccw (k-4),
    arcDefClausesUpTo n .cw (k-3),
    noGonClauses k n]

def gonCNF (k rlen : Nat) : ICnf := (Geo.gonEncoding k rlen |>.toICnf compare).2

-- set_option profiler true in
-- #eval let cnf := Geo.naiveCNF 10; (cnf.size, cnf.maxVar)
