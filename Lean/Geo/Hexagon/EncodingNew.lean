import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Range
import Geo.SAT.ToLeanSAT.EncodeProof
import Geo.NGon.Var
import Geo.NGon.EncodingNew
import LeanSAT

namespace LeanSAT
instance : Coe (ν : Type u) (Literal ν) := ⟨Literal.pos⟩
end LeanSAT

namespace Geo

open LeanSAT Var Encode VEncCNF

-- Corresponds to constraint (10) in the paper
-- Logically equivalent to: (!σ(a, b, c) ∧ !σ(b, c, d)) → cap(a, c, d)
-- cap a c d:    b  c
--            a ------ d
def capDef (a b c d : Fin n) :=
  show VEncCNF (Var n) _ _ from
  andImply #[ -↑(sigma a b c), -↑(sigma b c d) ] (cap a c d)


-- Corresponds to constraint (??) in the paper
def capDef2 (a c d : Fin n) :=
  show VEncCNF (Var n) _ _ from
  imply (cap a c d) (-↑(sigma a c d))

-- Corresponds to constraint (12) in the paper
-- Logically equivalent to (σ(a, b, c) ∧ σ(b, c, d)) → cup(a, c, d)
--            a ------ d
-- cup a c d:    b  c
def cupDef (a b c d : Fin n) :=
  show VEncCNF (Var n) _ _ from
  andImply #[ -↑(sigma a b c), -↑(sigma b c d) ] (cup a c d)

-- Corresponds to constraint (??) in the paper
def cupDef2 (a c d : Fin n) :=
  show VEncCNF (Var n) _ _ from
  imply (cup a c d) (sigma a c d)

-- Corresponds to constraint (11) in the paper (but omits the hole variable)
-- Logically equivalent to (cap(a, c, d) ∧ !σ(c, d, e)) → capF(a, d, e)
--                .   b
-- capF a c d:            c      (where a-b-d is a hole)
--             a ---------- d
def capFDef (a b c d : Fin n) :=
  --/- Var.hole a b d -> -/ .imp (.and (.not (Var.sigma b c d)) (Var.cap a b c)) (Var.capF a c d)
  show VEncCNF (Var n) _ _ from
  andImply #[ ↑(cap a b c), -↑(sigma b c d) ] (capF a c d)

-- We range across `b`, even though it doesn't appear as an argument here
--def capFDef' (a b c d e : Fin n) :=
--  show VEncCNF (Var n) _ _ from
--  andImply #[ ↑(cap a c d), -↑(sigma c d e), ↑(hole a c e) ] (capF a d e)

-- Corresponds to constraint (17) in the paper (but omits the hole variable)
-- Logically equivalent to cup(a, c, d) → σ(b, c, d)
-- a ----------- d
--   ·         c
--        b
def no6Hole3Below (a b c d : Fin n) :=
  show VEncCNF (Var n) _ _ from
  imply (cup a b c) (sigma b c d)

-- We range across `b`, even though it doesn't appear as an argument here
--def no6Hole3Below' (a b c d e : Fin n) :=
--  show VEncCNF (Var n) _ _ from
--  andImply #[ hole a c e, cup a c d ] (sigma c d e)

-- Corresponds to constraint (14) in the paper
--       .  b
--   ·         c
-- a ----------- d
def no6Hole4Above (a d e f : Fin n) :=
  show VEncCNF (Var n) _ _ from
  imply (capF a d e) (sigma d e f)

/-- This expression builds constraints (10), (11), (12), (14), and (17).
  Note how the use of the guard (a.1 + 1 < b.1) is used to introduce an
  implicit variable b' in between a and b, essentially mapping the variable
  name b to c, and ranging over those (a < b < c), but where b is not actually
  an argument to the constraint.
-/
def no6HoleClauses1 (n : Nat) :=
  show VEncCNF (Var n) _ _ from
  let U := Array.finRange n
  (
    for_all U fun a =>
    VEncCNF.guard (⟨0, Fin.size_positive a⟩ < a) fun _ =>
    for_all U fun b =>
    VEncCNF.guard (a < b) fun _ =>
    for_all U fun c =>
    VEncCNF.guard (b < c) fun _ =>
    for_all U fun d =>
    VEncCNF.guard (c < d) fun _ =>
    seq[
      capDef a b c d,
      cupDef a b c d,
      (VEncCNF.guard (a.1+1 < b.1) fun _ =>
        seq[
          capFDef a b c d,
          no6Hole3Below a b c d
        ]),
      (VEncCNF.guard (a.1+2 < b.1) fun _ =>
        no6Hole4Above a b c d)
    ]
  )

-- Corresponds to constraints (??) in the paper.
def no6HoleClauses2 (n : Nat) :=
  show VEncCNF (Var n) _ _ from
  let U := Array.finRange n
  (
    for_all U fun a =>
    VEncCNF.guard (⟨0, Fin.size_positive a⟩ < a) fun _ =>
    for_all U fun c =>
    VEncCNF.guard (a.1 + 1 < c) fun _ =>
    for_all U fun d =>
    VEncCNF.guard (c < d) fun _ =>
    seq[
      capDef2 a c d,
      cupDef2 a c d
    ]
  )

-- Corresponds to constraints (15) and (16) in the paper, depending on whether b or p is smaller
--     ·   p
-- a --------- c
--     ·   b
def no6Hole2Below (a b p c : Fin n) :=
  show VEncCNF (Var n) _ _ from
  VEncCNF.ite (b < p)
    (fun _ => addClause #[ -↑(cup a b c), -↑(cap a p c), -↑(hole a b p) ])
    (fun _ => addClause #[ -↑(cup a b c), -↑(cap a p c), -↑(hole a p b) ])

-- Corresponds to constraint (13) in the paper
--        ·
--   ·         b
-- a ----------- c
--         p
def no6Hole1Below (a b p c : Fin n) :=
  show VEncCNF (Var n) _ _ from
  imply (capF a b c) (-↑(sigma a p c))


-- This expression builds constraints (13), (15), and (16).
def no6HoleClauses3 (n : Nat) :=
  show VEncCNF (Var n) _ _ from
  let U := Array.finRange n
  (
    for_all U fun a =>
    VEncCNF.guard (⟨0, Fin.size_positive a⟩ < a) fun _ =>
    for_all U fun b =>
    VEncCNF.guard (a < b) fun _ =>
    for_all U fun c =>
    VEncCNF.guard (b < c) fun _ =>
    for_all U fun p =>
    VEncCNF.guard (a < p ∧ p < c ∧ b ≠ p) fun _ =>
    seq[
      (VEncCNF.guard (a.1+1 < b.1 ∧ a.1+1 < p.1) fun _ =>
        no6Hole2Below a b p c),
      (VEncCNF.guard (a.1+2 < b.1) fun _ =>
        no6Hole1Below a b p c)
    ]
  )

def hexagonEncoding (n : Nat) :=
  show VEncCNF (Var n) _ _ from
  seq[
    baseEncoding n,
    no6HoleClauses1 n,
    no6HoleClauses2 n,
    no6HoleClauses3 n
  ]

def hexagonCNF (n : Nat) : ICnf := (Geo.hexagonEncoding n |>.toICnf compare).2

-- set_option profiler true in
-- #eval let cnf := Geo.hexagonCNF 30; (cnf.size, cnf.maxVar)
