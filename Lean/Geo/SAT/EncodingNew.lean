import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Range
import Geo.SAT.ToLeanSAT.Encode
import Geo.SAT.Formula

namespace Geo

open LeanSAT Var

/-

Overall, we have three sets of variables:

∀ 1 ≤ a < b < c ≤ n:

  s{a, b, c}       === signotope of points a b c
  I{x, a, b, c}    === x is "Inside" triangle a b c
  H{a, b, c}       === triangle a b c is a hole (i.e. no other points strictly inside)

  Notably, while the I variables can be defined for any four distinct {x, a, b, c},
  they only really matter when

      a < b < c (which we may assume generally throughout)
      a < x < c

  because otherwise, x cannot be inside the triangle anyway, and so its variable
  would automatically be set to false (via logic, not by the SAT solver).

The contraints are:

  ∀ 1 ≤ a < b < c ≤ n:

  Orientation constraints:
    ∀ {d}, c < d:
      !s{a, b, c} ∨ !s{a, c, d} ∨  s{a, b, d} ≃  (s{a, b, c} ∧ s{a, c, d}) → s{a, b, d}
      !s{a, b, c} ∨ !s{b, c d}  ∨  s{a, c, d} ≃  (s{a, b, c} ∧ s{b, c, d}) → s{a, c, d}

      (We take the top grouping and do them again, except negating the actual variables)

       s{a, b, c} ∨  s{a, c, d} ∨ !s{a, b, d} ≃  (!s{a, b, c} ∧ !s{a, c, d}) → !s{a, b, d}
       s{a, b, c} ∨  s{b, c, d} ∨ !s{a, c, d} ≃  (!s{a, b, c} ∧ !s{b, c, d}) → !s{a, c, d}


  The "inside triangles" constraints:

    (We split on whether the candidate point "x" to be inside is before or after "b")
    (Note(WN): the new pt_in_triangle doesn't need a split, can we backport that to encoding?)

    ∀ {x}, a < x < b:
      I{x, a, b, c} ↔ ((s{a, b, c} ↔ s{a, x, c}) ∧ (!s{a, x, b} ↔ s{a, b, c}))

    ∀ {x}, b < x < c:
      I{x, a, b, c} ↔ ((s{a, b, c} ↔ s{a, x, c}) ∧ (!s{b, x, c} ↔ s{a, b, c}))

    (Notably, the only difference is the third "s" variable, noting which two triangle points "x" lies between.)

    The way the constraints work is as follows:
      - The first pair places "x" and "b" on the same side of the line segment "ac"
      - The second pair places "x" below the line segment coming from "a" to "b", or going from "b" to "c"

    In addition to "x" being between "a" and "c", this places "x" to be inside the triangle.

  The "hole" constraints:

    ∀ {x}, a < x < c, with x ≠ b:
      I{x, a, b, c} → !H{a, b, c}           (If "x" is inside triangle abc, then triangle abc isn't a hole)

  Finally, the UNSAT constraints to look for non-holes:
    !H{a, b, c}                             (To satisfy the formula, every triangle cannot be a hole, i.e. it contains a point.)



  The proof skeleton looks like:
    ∃ {pts : Finset Point}, NoHoles pts → ∃ {τ : Assignment}, F(τ) = SAT

  The contrapositive then gives us
    ∀ {τ : Assignment}, F(τ) = UNSAT → ∀ {pts : Finset Point}, ∃ a hole.
-/


def signotopeClause (a b c d : Fin n) : PropForm (Var n) :=
  .all #[
    -- (s{a, b, c} ∧ s{a, c, d}) → s{a, b, d}
    .imp (.and (sigma a b c) (sigma a c d)) (sigma a b d)
  , -- (s{a, b, c} ∧ s{b, c, d}) → s{a, c, d}
    .imp (.and (sigma a b c) (sigma b c d)) (sigma a c d)
  , -- (!s{a, b, c} ∧ !s{a, c, d}) → !s{a, b, d}
    .imp (.and (.not (sigma a b c)) (.not (sigma a c d))) (.not (sigma a b d))
  , -- (!s{a, b, c} ∧ !s{b, c, d}) → !s{a, c, d}
    .imp (.and (.not (sigma a b c)) (.not (sigma b c d))) (.not (sigma a c d))
  ]

def signotopeClauses (n : Nat) : PropForm (Var n) :=
  -- for all `a`, `b`, `c` with `a < b < c`
  .forAll (Fin n) fun a =>
  .forAll (Fin n) fun b =>
  .guard (a < b) fun _ =>
  .forAll (Fin n) fun c =>
  .guard (b < c) fun _ =>
  .forAll (Fin n) fun d =>
  .guard (c < d) fun _ =>
  signotopeClause a b c d

def xIsInsideClause (a b c x : Fin n) : PropForm (Var n) :=
  .all #[
    -- a < x < b
    .guard (a < x ∧ x < b) fun _ =>
      -- NOTE(Bernardo): Each of those should be expressible as 8 clauses or so
      -- I{x, a, b, c} ↔ ((s{a, b, c} ↔ s{a, x, c}) ∧ (!s{a, x, b} ↔ s{a, b, c}))
      .iff (inside x a b c) (
        .and (.iff (sigma a b c) (sigma a x c)) (.iff (.not (sigma a x b)) (sigma a b c)))
  , -- b < x < c
    .guard (b < x ∧ x < c) fun _ =>
      -- I{x, a, b, c} ↔ ((s{a, b, c} ↔ s{a, x, c}) ∧ (!s{b, x, c} ↔ s{a, b, c}))
      .iff (inside x a b c) (
        .and (.iff (sigma a b c) (sigma a x c)) (.iff (.not (sigma b x c)) (sigma a b c)))
  ]

def insideClauses (n : Nat) : PropForm (Var n) :=
  -- for all `a`, `b`, `c` with `a < b < c`
  .forAll (Fin n) fun a =>
  .forAll (Fin n) fun b =>
  .guard (a < b) fun _ =>
  .forAll (Fin n) fun c =>
  .guard (b < c) fun _ =>
  .forAll (Fin n) fun x =>
  xIsInsideClause a b c x

def holeDefClauses (n : Nat) : PropForm (Var n) :=
  .forAll (Fin n) fun a =>
  .forAll (Fin n) fun b =>
  .guard (a < b) fun _ =>
  .forAll (Fin n) fun c =>
  .guard (b < c) fun _ =>
  .iff (Var.hole a b c) <|
    .forAll (Fin n) fun x =>
    .guard (a < x ∧ x < c ∧ x ≠ b) fun _ =>
    .not (Var.inside x a b c)

def noHoleClauses (n : Nat) : PropForm (Var n) :=
  .forAll (Fin n) fun a =>
  .forAll (Fin n) fun b =>
  .guard (a < b) fun _ =>
  .forAll (Fin n) fun c =>
  .guard (b < c) fun _ =>
    .not (hole a b c)

def leftmostCCWClauses (n : Nat) : PropForm (Var n) :=
  .forAll (Fin n) fun a =>
  .guard (⟨0, Fin.size_positive a⟩ < a) fun _ =>
  .forAll (Fin n) fun b =>
  .guard (a < b) fun _ =>
    Var.sigma ⟨0, Fin.size_positive a⟩ a b

def theEncoding (n : Nat) : PropForm (Var n) :=
  .all #[
    signotopeClauses n, insideClauses n, holeDefClauses n, noHoleClauses n, leftmostCCWClauses n
  ]

open Model PropFun
axiom cnfUnsat : ¬∃ τ : PropAssignment IVar,
  τ ⊨ (Geo.theEncoding 10 |>.toICnf compare).toPropFun

-- set_option profiler true in
-- #eval let cnf := Geo.theEncoding 10 |>.toICnf compare; (cnf.size, cnf.maxVar)
