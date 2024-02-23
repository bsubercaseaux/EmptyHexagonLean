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


instance : Monad Multiset where
  pure := ({·})
  bind := Multiset.bind

instance : Alternative Multiset where
  failure := {}
  orElse x f := if Multiset.card x = 0 then f () else x

-- instance : FinEnum (Var n) := FinEnum.ofEquiv {
--     toFun := fun
--       | Var.sigma a b c => Sum.inl (a,b,c)
--       | Var.inside x a b c => Sum.inr (Sum.inl (x,a,b,c))
--       | Var.hole a b c => Sum.inr (Sum.inr (a,b,c))
--     invFun := fun
--       | Sum.inl (a,b,c) => Var.sigma a b c
--       | Sum.inr (Sum.inl (x,a,b,c)) => Var.inside x a b c
--       | Sum.inr (Sum.inr (a,b,c)) => Var.hole a b c
--     left_inv := by intro x; cases x <;> simp
--     right_inv := by intro x; rcases x with (_|_|_) <;> simp
--   }

def Array.finRange (n : Nat) : Array (Fin n) :=
  ⟨List.finRange n⟩

@[simp] theorem Array.mem_finRange {n} (x : Fin n)
  : x ∈ Array.finRange n := by simp [Array.finRange, Array.mem_def]

@[simp] theorem Array.finRange_data (n)
  : (Array.finRange n).data = List.finRange n := rfl

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
  -- let U := (Array.finRange n)
  ( -- for all `a`, `b`, `c` with `a < b < c`
    .forAll (Fin n) fun a =>
    .forAll (Fin n) fun b =>
    .guard (a < b) fun _ =>
    .forAll (Fin n) fun c =>
    .guard (b < c) fun _ =>
    .forAll (Fin n) fun d =>
    .guard (c < d) fun _ =>
    signotopeClause a b c d
  )

theorem Fin.lt_asymm {a b : Fin n} : a < b → ¬b < a := @Nat.lt_asymm a b

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
  ( -- for all `a`, `b`, `c` with `a < b < c`
    .forAll (Fin n) fun a =>
    .forAll (Fin n) fun b =>
    .guard (a < b) fun _ =>
    .forAll (Fin n) fun c =>
    .guard (b < c) fun _ =>
    .forAll (Fin n) fun x =>
    xIsInsideClause a b c x
  )

def notHoleOfPointInsideClauses (a b c : Fin n) : PropForm (Var n) :=
  ( .forAll (Fin n) fun x =>
    .guard (a < x ∧ x < c ∧ x ≠ b) fun _ =>
      -- Q(WN): this is just a clause, why do we need Tseitin? Also in `signotopeClause` above
      -- A?(CC): Seems like Tseitin is doing the conversion from implication to CNF
      --         I supplied the direct formula object instead here and in `signotopeClause`, and
      --         the proofs remained the same (either simp or aesop)
      .imp (Var.inside x a b c) (.not (Var.hole a b c))
  )

def pointInsideOfNotHoleClauses (a b c : Fin n) : PropForm (Var n) :=
  let insideVars :=
    Array.finRange n |>.filter (fun x => a < x ∧ x < c ∧ x ≠ b) |>.map fun x => .var (inside x a b c)
  ( .imp (.not <| Var.hole a b c) <| .any insideVars
  )

def holeDefClauses (n : Nat) : PropForm (Var n) :=
  ( .forAll (Fin n) fun a =>
    .forAll (Fin n) fun b =>
    .guard (a < b) fun _ =>
    .forAll (Fin n) fun c =>
    .guard (b < c) fun _ =>
      .and
        (notHoleOfPointInsideClauses a b c)
        (pointInsideOfNotHoleClauses a b c)
  )

def noHoleClauses (n : Nat) : PropForm (Var n) :=
  ( .forAll (Fin n) fun a =>
    .forAll (Fin n) fun b =>
    .guard (a < b) fun _ =>
    .forAll (Fin n) fun c =>
    .guard (b < c) fun _ =>
      .not (hole a b c)
  )

def leftmostCCWClauses (n : Nat) : PropForm (Var n) :=
  ( .forAll (Fin n) fun a =>
    .guard (⟨0, Fin.size_positive a⟩ < a) fun _ =>
    .forAll (Fin n) fun b =>
    .guard (a < b) fun _ =>
      Var.sigma ⟨0, Fin.size_positive a⟩ a b
  )

def theEncoding (n : Nat) : PropForm (Var n) :=
  .all #[
    signotopeClauses n, insideClauses n, holeDefClauses n, noHoleClauses n, leftmostCCWClauses n
  ]

open Model PropFun
axiom cnfUnsat : ¬∃ τ : PropAssignment IVar,
  τ ⊨ (Geo.theEncoding 10 |>.toICnf compare).toPropFun

-- set_option profiler true in
-- #eval let cnf := Geo.theEncoding 10 |>.toICnf compare; (cnf.size, cnf.maxVar)
