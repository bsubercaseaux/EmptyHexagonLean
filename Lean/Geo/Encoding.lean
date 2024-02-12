import LeanSAT
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Range
import Geo.Formula

namespace Geo

open LeanSAT Encode VEncCNF Model Var PropForm

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

instance : FinEnum (Var n) := FinEnum.ofEquiv _ {
    toFun := fun
      | Var.sigma a b c => Sum.inl (a,b,c)
      | Var.inside x a b c => Sum.inr (Sum.inl (x,a,b,c))
      | Var.hole a b c => Sum.inr (Sum.inr (a,b,c))
    invFun := fun
      | Sum.inl (a,b,c) => Var.sigma a b c
      | Sum.inr (Sum.inl (x,a,b,c)) => Var.inside x a b c
      | Sum.inr (Sum.inr (a,b,c)) => Var.hole a b c
    left_inv := by intro x; cases x <;> simp
    right_inv := by intro x; rcases x with (_|_|_) <;> simp
  }

def Array.finRange (n : Nat) : Array (Fin n) :=
  ⟨List.finRange n⟩

@[simp] theorem Array.mem_finRange {n} (x : Fin n)
  : x ∈ Array.finRange n := by simp [Array.finRange, Array.mem_def]

@[simp] theorem Array.finRange_data (n)
  : (Array.finRange n).data = List.finRange n := rfl

def signotopeClause (a b c d : Fin n) : VEncCNF (Literal (Var n)) Unit (signotopeAxiom a b c d) :=
  seq[
    -- (s{a, b, c} ∧ s{a, c, d}) → s{a, b, d}
    tseitin[ ({sigma a b c} ∧ {sigma a c d}) → {sigma a b d} ]
  , -- (s{a, b, c} ∧ s{b, c, d}) → s{a, c, d}
    tseitin[ ({sigma a b c} ∧ {sigma b c d}) → {sigma a c d} ]
  , -- (!s{a, b, c} ∧ !s{a, c, d}) → !s{a, b, d}
    tseitin[ (¬{sigma a b c} ∧ ¬{sigma a c d}) → ¬{sigma a b d} ]
  , -- (!s{a, b, c} ∧ !s{b, c, d}) → !s{a, c, d}
    tseitin[ (¬{sigma a b c} ∧ ¬{sigma b c d}) → ¬{sigma a c d} ]
  ].mapProp (by
    simp [signotopeAxiom]
  )

def signotopeClauses (n : Nat) : VEncCNF (Literal (Var n)) Unit (signotopeAxioms n) :=
  ( -- for all `a`, `b`, `c` with `a < b < c`
    for_all (Array.finRange n) fun a =>
    for_all (Array.finRange n) fun b =>
    VEncCNF.guard (a < b) fun _ =>
    for_all (Array.finRange n) fun c =>
    VEncCNF.guard (b < c) fun _ =>
    for_all (Array.finRange n) fun d =>
    VEncCNF.guard (c < d) fun _ =>
      signotopeClause a b c d
  ).mapProp (by
    ext τ
    simp [signotopeAxioms]
    constructor
    · intro h a b c d
      split
      next habcd =>
        rcases habcd with ⟨hab,hbc,hcd⟩
        specialize h a b; simp [hab] at h
        specialize h c; simp [hbc] at h
        specialize h d; simp [hcd] at h
        exact h
      · trivial
    · intro h a b
      split
      next hab =>
        simp; intro c
        split
        next hbc =>
          simp; intro d
          split
          next hcd =>
            specialize h a b c d
            simp [*] at h
            exact h
          · trivial
        · trivial
      · trivial
    )

theorem Fin.lt_asymm {a b : Fin n} : a < b → ¬b < a := @Nat.lt_asymm a b

def xIsInsideClause (a b c x : Fin n) : VEncCNF (Literal (Var n)) Unit (xIsInsideDef a b c x) :=
  seq[
    -- a < x < b
    VEncCNF.guard (a < x ∧ x < b) fun _ =>
      -- I{x, a, b, c} ↔ ((s{a, b, c} ↔ s{a, x, c}) ∧ (!s{a, x, b} ↔ s{a, b, c}))
      tseitin[{inside x a b c} ↔ (
        ({sigma a b c} ↔ {sigma a x c}) ∧ (¬{sigma a x b} ↔ {sigma a b c})
      )]
  , -- b < x < c
    VEncCNF.guard (b < x ∧ x < c) fun _ =>
      -- I{x, a, b, c} ↔ ((s{a, b, c} ↔ s{a, x, c}) ∧ (!s{b, x, c} ↔ s{a, b, c}))
      tseitin[{inside x a b c} ↔ (
        ({sigma a b c} ↔ {sigma a x c}) ∧ (¬{sigma b x c} ↔ {sigma a b c})
      )]
  ].mapProp (by
    ext τ
    simp [xIsInsideDef]
    split
    next h =>
      rcases h with ⟨-,h2⟩
      have := Fin.lt_asymm h2
      simp [this]
    · simp
    )

def insideClauses (n : Nat) : VEncCNF (Literal (Var n)) Unit (insideDefs n) :=
  ( -- for all `a`, `b`, `c` with `a < b < c`
    for_all (Array.finRange n) fun a =>
    for_all (Array.finRange n) fun b =>
    VEncCNF.guard (a < b) fun _ =>
    for_all (Array.finRange n) fun c =>
    VEncCNF.guard (b < c) fun _ =>
    for_all (Array.finRange n) fun x =>
    xIsInsideClause a b c x
  ).mapProp (by
    ext τ
    simp [insideDefs]
    constructor
    · intro h a b c d
      split
      · specialize h a b; simp [*] at h
        specialize h c; simp [*] at h
        specialize h d; exact h
      · trivial
    · intro h a b
      split
      · simp; intro c
        split
        · simp; intro d
          specialize h a b c d
          simp [*] at h
          exact h
        · trivial
      · trivial)

def notHoleOfPointInsideClauses (a b c : Fin n) : VEncCNF (Literal (Var n)) Unit (notHoleOfPointInside a b c) :=
  ( for_all (Array.finRange n) fun x =>
    VEncCNF.guard (a < x ∧ x < c ∧ x ≠ b) fun _ =>
      -- Q(WN): this is just a clause, why do we need Tseitin? Also in `signotopeClause` above
      tseitin[ {Var.inside x a b c} → ¬{Var.hole a b c} ]
  ).mapProp (by
    ext τ
    simp [notHoleOfPointInside])

def pointInsideOfNotHoleClauses (a b c : Fin n) :
    VEncCNF (Literal (Var n)) Unit [propfun| ¬{Var.hole a b c} → {hasPointInside a b c} ]:=
  ( tseitin[ ¬{Var.hole a b c} →
    {(((Array.finRange n).filter (fun x => a < x ∧ x < c ∧ x ≠ b)).map fun x => PropForm.var $ Var.inside x a b c).foldl (init := .tr) .disj} ]
  ).mapProp (by
    sorry
    )

def holeDefClauses (n : Nat) : VEncCNF (Literal (Var n)) Unit (holeDefs n) :=
  ( for_all (Array.finRange n) fun a =>
    for_all (Array.finRange n) fun b =>
    VEncCNF.guard (a < b) fun _ =>
    for_all (Array.finRange n) fun c =>
    VEncCNF.guard (b < c) fun _ =>
      seq[
        notHoleOfPointInsideClauses a b c,
        pointInsideOfNotHoleClauses a b c
      ]
  ).mapProp (by
    ext τ
    simp [holeDefs]
    constructor
    · intro h a b c
      split
      · specialize h a b; simp [*] at h
        specialize h c; simp [*] at h
        simp_all [h]
      · trivial
    · intro h a b
      split
      · simp; intro c
        split
        · specialize h a b c
          simpa [*] using h
        · trivial
      · trivial)

def noHoleClauses (n : Nat) : VEncCNF (Literal (Var n)) Unit (noHoles n) :=
  ( for_all (Array.finRange n) fun a =>
    for_all (Array.finRange n) fun b =>
    VEncCNF.guard (a < b) fun _ =>
    for_all (Array.finRange n) fun c =>
    VEncCNF.guard (b < c) fun _ =>
      tseitin[ ¬ {Var.hole a b c} ]
  ).mapProp (by
    ext τ
    simp [noHoles]
    constructor
    · intro h a b c
      split
      · specialize h a b; simp [*] at h
        specialize h c; simp [*] at h
        simp [h]
      · trivial
    · intro h a b
      split
      · simp; intro c
        split
        · specialize h a b c
          simpa [*] using h
        · trivial
      · trivial
  )

def theEncoding (n : Nat) : VEncCNF (Literal (Var n)) Unit (theFormula n) :=
  (seq[
    signotopeClauses n, insideClauses n, holeDefClauses n, noHoleClauses n
  ]).mapProp (by
    simp [theFormula]; aesop)
