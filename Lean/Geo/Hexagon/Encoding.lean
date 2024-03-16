import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Range
import Geo.SAT.ToLeanSAT.EncodeProof
import Geo.KGon.Var
import Geo.KGon.Encoding

namespace Geo

open LeanSAT Var

-- a ----------- d
--   ·         c
--        b
def no6Hole3Below (a b c d : Fin n) : PropForm (Var n) :=
  .not <| .all #[Var.hole a b d, Var.cup a b c, Var.sigma b c d]

--       .  b
--   ·         c
-- a ----------- d
def no6Hole4Above (a b c d : Fin n) : PropForm (Var n) :=
  .imp (Var.capF a b c) (Var.sigma b c d)

def no6HoleClauses1 (n : Nat) : PropForm (Var n) :=
  .forAll (Fin n) fun a =>
  .forAll (Fin n) fun b =>
  .guard (a.1+1 < b.1) fun _ =>
  .forAll (Fin n) fun c =>
  .guard (b < c) fun _ =>
  .forAll (Fin n) fun d =>
  .guard (c < d) fun _ =>
  .flatCNF <| .all #[
    no6Hole3Below a b c d,
    .guard (a.1+2 < b.1) fun _ => no6Hole4Above a b c d
  ]

--     ·   p
-- a --------- c
--     ·   b
def no6Hole2Below (a b c p : Fin n) : PropForm (Var n) :=
  .not <| .all #[Var.cup a b c, Var.cap a p c,
    if b < p then Var.hole a b p else Var.hole a p b]

--        ·
--   ·         b
-- a ----------- c
--         p
def no6Hole1Below (a b c p : Fin n) : PropForm (Var n) :=
  .not <| .all #[Var.capF a b c, Var.sigma a p c]

def no6HoleClauses2 (n : Nat) : PropForm (Var n) :=
  .forAll (Fin n) fun a =>
  .forAll (Fin n) fun b =>
  .guard (a.1 + 1 < b.1) fun _ =>
  .forAll (Fin n) fun c =>
  .guard (b < c) fun _ =>
  .forAll (Fin n) fun p =>
  .guard (a < p ∧ p < c ∧ b ≠ p) fun _ =>
  .all #[
    .guard (a.1 + 1 < p.1) fun _ => no6Hole2Below a b c p,
    .guard (a.1 + 2 < b.1) fun _ => no6Hole1Below a b c p
  ]

def hexagonEncoding (n : Nat) : PropForm (Var n) :=
  .all #[baseKGonEncoding n, no6HoleClauses1 n, no6HoleClauses2 n]

def hexagonCNF (rlen : Nat) : ICnf := (Geo.hexagonEncoding rlen |>.toICnf compare).2

-- set_option profiler true in
-- #eval let cnf := Geo.hexagonCNF 30; (cnf.size, cnf.maxVar)
