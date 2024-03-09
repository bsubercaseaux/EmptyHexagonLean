import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Range
import Geo.SAT.ToLeanSAT.EncodeProof
import Geo.NGon.Var
import LeanSAT

namespace Geo

open LeanSAT Var Encode VEncCNF
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

-- This builds constraints (1) - (4) in the paper.
def signotopeClauses (n : Nat) :=
  show VEncCNF (Var n) _ _ from
  let U := (Array.finRange n)
  (
    for_all U fun a =>
    -- CC: Do we need a positivity constraint here?
    -- VEncCNF.guard (⟨0, Fin.size_positive a⟩ < a) fun _ =>
    for_all U fun b =>
    VEncCNF.guard (a < b) fun _ =>
    for_all U fun c =>
    VEncCNF.guard (b < c) fun _ =>
    for_all U fun d =>
    VEncCNF.guard (c < d) fun _ =>
    seq[
      andImply #[ sigma a b c, sigma a c d] (sigma a b d),
      andImply #[ sigma a b c, sigma b c d] (sigma a c d),
      andImply #[ -↑(sigma a b c), -↑(sigma a c d)] (-↑(sigma a b d)),
      andImply #[ -↑(sigma a b c), -↑(sigma b c d)] (-↑(sigma a c d))
    ]
  )

-- This builds constraints (5) and (6) in the paper.
def insideClauses (n : Nat) :=
  show VEncCNF (Var n) _ _ from
  let U := (Array.finRange n)
  (
    for_all U fun a =>
    for_all U fun b =>
    VEncCNF.guard (a < b) fun _ =>
    for_all U fun c =>
    VEncCNF.guard (b < c) fun _ =>
    for_all U fun x =>
    seq[
      (VEncCNF.guard (a < x ∧ x < b) fun _ =>
        seq[
          defDisj (inside x a b c) #[ -↑(sigma a b c),    sigma a x c  ],
          defDisj (inside x a b c) #[   (sigma a b c), -↑(sigma a x c) ],
          defDisj (inside x a b c) #[ -↑(sigma a b c), -↑(sigma a x b) ],
          defDisj (inside x a b c) #[   (sigma a b c),    sigma a x b  ]
        ]),
      (VEncCNF.guard (b < x ∧ x < c) fun _ =>
        seq[
          defDisj (inside x a b c) #[ -↑(sigma a b c),    sigma a x c ],
          defDisj (inside x a b c) #[   (sigma a b c), -↑(sigma a x c) ],
          defDisj (inside x a b c) #[ -↑(sigma a b c), -↑(sigma b x c) ],
          defDisj (inside x a b c) #[   (sigma a b c),    sigma b x c  ]
        ])
    ]
  )

-- This builds constraint (7) in the paper.
def holeDefClauses (n : Nat) :=
  show VEncCNF (Var n) _ _ from
  let U := (Array.finRange n)
  (
    for_all U fun a =>
    for_all U fun b =>
    VEncCNF.guard (a < b) fun _ =>
    for_all U fun c =>
    VEncCNF.guard (b < c) fun _ =>
      defConj (hole a b c) (
        Array.finRange n |>.filter (fun x => a < x ∧ x < c ∧ x ≠ b) |>.map fun x => -((inside x a b c) : Literal (Var n))
      )
  )

-- This builds constraint (8) in the paper.
def leftmostCCWClauses (n : Nat) :=
  show VEncCNF (Var n) _ _ from
  let U := Array.finRange n
  (
    for_all U fun a =>
    VEncCNF.guard (⟨0, Fin.size_positive a⟩ < a) fun _ =>
    for_all U fun b =>
    VEncCNF.guard (a < b) fun _ =>
      addClause #[ sigma ⟨0, Fin.size_positive a⟩ a b ]
  )

-- This builds constraint (9) in the paper (in part)
def revLexClausesCore (F : Fin n → PropForm α) (a b : Fin n) (acc : PropForm α) : PropForm α :=
  if h : a < b then
    revLexClausesCore F
        ⟨a + 1, Nat.lt_of_le_of_lt h b.2⟩
        ⟨b - 1, Nat.lt_of_le_of_lt (Nat.sub_le ..) b.2⟩ <|
      .or (.imp (F b) (F a)) <|
      .and (.imp (F a) (F b)) acc
  else
    acc

def revLexClauses (n : Nat) : PropForm (Var n) :=
  .guard (5 ≤ n) fun _ =>
  revLexClausesCore (n := n-2) ⟨1, by omega⟩ ⟨n - 3, by omega⟩ .true
    (F := fun ⟨a, _⟩ => Var.sigma ⟨a, by omega⟩ ⟨a+1, by omega⟩ ⟨a+2, by omega⟩)

--#eval ((revLexClauses 16) |>.toICnf compare).2

def baseEncoding (n : Nat) :=
  show VEncCNF (Var n) _ _ from
  seq[
    signotopeClauses n,
    insideClauses n,
    holeDefClauses n,
    leftmostCCWClauses n
    --revLexClauses n
  ]
