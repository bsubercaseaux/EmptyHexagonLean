import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Range
import Geo.SAT.ToLeanSAT.EncodeProof
import Geo.KGon.Var
import Geo.KGon.Encoding

namespace Geo

open LeanSAT Var

-- a ----------- e
--   ·         d
--        c
def no6Hole3Below (holes : Bool) (a c d e : Fin n) : PropForm (Var n) :=
  .not <| .all #[Var.cup a c d, Var.sigma c d e, holeIf holes a c e]

--       .  d
--   ·         e
-- a ----------- f
def no6Hole4Above (a d e f : Fin n) : PropForm (Var n) :=
  .not <| .all #[Var.capF a d e, .not (Var.sigma d e f)]

def no6HoleClauses1 (n : Nat) (holes : Bool) : PropForm (Var n) :=
  .forAll (Fin n) fun a =>
  .forAll (Fin n) fun b =>
  .impP (a.1+1 < b.1) fun _ =>
  .forAll (Fin n) fun c =>
  .impP (b < c) fun _ =>
  .forAll (Fin n) fun d =>
  .impP (c < d) fun _ =>
  .flatCNF <| .all #[
    no6Hole3Below holes a b c d,
    .impP (a.1+2 < b.1) fun _ => no6Hole4Above a b c d
  ]

--     ·   c'
-- a --------- d
--     ·   c
def no6Hole2Below (holes : Bool) (a c d c' : Fin n) : PropForm (Var n) :=
  .not <| .all #[Var.cup a c d, Var.cap a c' d,
    .impP holes fun _ => if c < c' then Var.hole a c c' else Var.hole a c' c]

--        ·
--   ·         d
-- a ----------- e
--         p
def no6Hole1Below (a d e p : Fin n) : PropForm (Var n) :=
  .not <| .all #[Var.capF a d e, Var.sigma a p e]

def no6HoleClauses2 (n : Nat) (holes : Bool) : PropForm (Var n) :=
  .forAll (Fin n) fun a =>
  .forAll (Fin n) fun b =>
  .impP (a.1 + 1 < b.1) fun _ =>
  .forAll (Fin n) fun c =>
  .impP (b < c) fun _ =>
  .forAll (Fin n) fun p =>
  .impP (a < p ∧ p < c ∧ b ≠ p) fun _ =>
  .all #[
    .impP (a.1 + 1 < p.1) fun _ => no6Hole2Below holes a b c p,
    .impP (a.1 + 2 < b.1) fun _ => no6Hole1Below a b c p
  ]

def hexagonEncoding (n : Nat) (holes : Bool) : PropForm (Var n) :=
  .all #[baseEncoding n holes,
    arcDefClauses1 n .ccw 0, arcDefClauses2 n .ccw 0,
    arcDefClauses1 n .cw 0, arcDefClauses2 n .cw 0,
    capFDefClauses n holes,
    no6HoleClauses1 n holes, no6HoleClauses2 n holes]

def hexagonCNF (rlen : Nat) (holes : Bool) : ICnf :=
  (Geo.hexagonEncoding rlen holes |>.toICnf compare).2

-- set_option profiler true in
-- #eval let cnf := Geo.hexagonCNF 30; (cnf.size, cnf.maxVar)
