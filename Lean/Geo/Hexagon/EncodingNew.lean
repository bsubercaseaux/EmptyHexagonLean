import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Range
import Geo.SAT.ToLeanSAT.EncodeProof
import Geo.NGon.Var
import Geo.NGon.EncodingNew

namespace Geo

open LeanSAT Var

-- cap a c d:    b  c
--            a ------ d
def capDef (a b c d : Fin n) : PropForm (Var n) :=
  .imp (.and (.not (Var.sigma a b c)) (.not (Var.sigma b c d))) (Var.cap a c d)

def capDef2 (a c d : Fin n) : PropForm (Var n) :=
  .imp (Var.cap a c d) (.not (Var.sigma a c d))

--            a ------ d
-- cup a c d:    b  c
def cupDef (a b c d : Fin n) : PropForm (Var n) :=
  .imp (.and (Var.sigma a b c) (Var.sigma b c d)) (Var.cup a c d)

def cupDef2 (a c d : Fin n) : PropForm (Var n) :=
  .imp (Var.cup a c d) (Var.sigma a c d)

--                .   b
-- capF a c d:            c      (where a-b-d is a hole)
--             a ---------- d
def capFDef (a b c d : Fin n) : PropForm (Var n) :=
  /- Var.hole a b d -> -/ .imp (.and (.not (Var.sigma b c d)) (Var.cap a b c)) (Var.capF a c d)

-- a ----------- d
--   ·         c
--        b
def no6Hole3Below (a b c d : Fin n) : PropForm (Var n) :=
  /- Var.hole a b d -> -/ .imp (Var.cup a b c) (.not (Var.sigma b c d))

--       .  b
--   ·         c
-- a ----------- d
def no6Hole4Above (a b c d : Fin n) : PropForm (Var n) :=
  .imp (Var.capF a b c) (Var.sigma b c d)

def no6HoleClauses1 (n : Nat) : PropForm (Var n) :=
  .forAll (Fin n) fun a =>
  .guard (⟨0, Fin.size_positive a⟩ < a) fun _ =>
  .forAll (Fin n) fun b =>
  .guard (a < b) fun _ =>
  .forAll (Fin n) fun c =>
  .guard (b < c) fun _ =>
  .forAll (Fin n) fun d =>
  .guard (c < d) fun _ =>
  .flatCNF <| .all #[
    capDef a b c d, cupDef a b c d,
    .guard (a.1+1 < b.1) fun _ => .all #[
      .imp (Var.hole a b d) <| .all #[capFDef a b c d, no6Hole3Below a b c d],
      .guard (a.1+2 < b.1) fun _ => no6Hole4Above a b c d
    ]
  ]

def no6HoleClauses2 (n : Nat) : PropForm (Var n) :=
  .forAll (Fin n) fun a =>
  .guard (⟨0, Fin.size_positive a⟩ < a) fun _ =>
  .forAll (Fin n) fun c =>
  .guard (a.1+1 < c.1) fun _ =>
  .forAll (Fin n) fun d =>
  .guard (c < d) fun _ =>
  .all #[capDef2 a c d, cupDef2 a c d]

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
  .imp (Var.capF a b c) <| .not (Var.sigma a p c)

def no6HoleClauses3 (n : Nat) : PropForm (Var n) :=
  .forAll (Fin n) fun a =>
  .guard (⟨0, Fin.size_positive a⟩ < a) fun _ =>
  .forAll (Fin n) fun b =>
  .guard (a < b) fun _ =>
  .forAll (Fin n) fun c =>
  .guard (b < c) fun _ =>
  .forAll (Fin n) fun p =>
  .guard (a < p ∧ p < c ∧ b ≠ p) fun _ =>
  .all #[
    .guard (a.1 + 1 < b.1 ∧ a.1 + 1 < p.1) fun _ => no6Hole2Below a b c p,
    .guard (a.1 + 2 < b.1) fun _ => no6Hole1Below a b c p
  ]


def hexagonEncoding (n : Nat) : PropForm (Var n) :=
  .all #[baseEncoding n, no6HoleClauses1 n, no6HoleClauses2 n, no6HoleClauses3 n]

open Model PropFun
axiom hexagonCnfUnsat : ¬∃ τ : IVar → Prop, (Geo.hexagonEncoding 30 |>.toICnf compare).2.eval τ

-- set_option profiler true in
-- #eval let cnf := (Geo.triangleEncoding 10 |>.toICnf compare).2; (cnf.size, cnf.maxVar)
