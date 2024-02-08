import LeanSAT
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Range

open LeanSAT Encode VEncCNF

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

-- Q(WN): why do we need the constraints on indices in the variable type?
inductive Var (n : Nat)
  | sigma  (a b c : Fin n)
  | inside (x a b c : Fin n)
  | hole   (a b c : Fin n)
  deriving DecidableEq

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

open Var in
set_option maxHeartbeats 300000 in
def trianglessss {n : Nat} (hn : n ≥ 3) : VEncCNF (Literal (Var n)) Unit ⊤ :=
  (-- for all `a`, `b`, `c` with `a < b < c`
  for_all (Array.finRange n) fun a =>
  for_all (Array.finRange n) fun b =>
  VEncCNF.guard (a < b) fun hab =>
  for_all (Array.finRange n) fun c =>
  VEncCNF.guard (b < c) fun hbc =>
    -- Cayden notes: For whatever reason, "let" notation isn't allowed in these funs
    --let sabc := LitVar.mkPos <| sigma a b c
    --let habc := LitVar.mkPos <| hole  a b c
    seq[

    -- Signotope axioms
    -- for all `d` with `c < d`
    for_all (Array.finRange n) (fun d =>
      VEncCNF.guard (c < d) (fun hcd =>
        seq[
          -- (s{a, b, c} ∧ s{a, c, d}) → s{a, b, d}
          (tseitin (Model.PropForm.impl (Model.PropForm.conj (sigma a b c) (sigma a c d))
                          (sigma a b d) ))
        , -- (s{a, b, c} ∧ s{b, c, d}) → s{a, c, d}
          (tseitin (Model.PropForm.impl (Model.PropForm.conj (sigma a b c) (sigma b c d))
                          (sigma a c d) ))
        , -- (!s{a, b, c} ∧ !s{a, c, d}) → !s{a, b, d}
          (tseitin (Model.PropForm.impl  (Model.PropForm.conj (Model.PropForm.neg <| sigma a b c) (Model.PropForm.neg <| sigma b c d))
                          (Model.PropForm.neg <| sigma a b d) ))
        , -- (!s{a, b, c} ∧ !s{b, c, d}) → !s{a, c, d}
          (tseitin (Model.PropForm.impl  (Model.PropForm.conj (Model.PropForm.neg <| sigma a b c) (Model.PropForm.neg <| sigma b c d))
                          (Model.PropForm.neg <| sigma a c d) ))
        ]
      )
    ),

    for_all (Array.finRange n) (fun x =>
      seq[
        -- a < x < b
        VEncCNF.guard (a < x ∧ x < b) (fun haxb =>
          -- I{x, a, b, c} ↔ ((s{a, b, c} ↔ s{a, x, c}) ∧ (!s{a, x, b} ↔ s{a, b, c}))
          tseitin (
            Model.PropForm.biImpl (inside x a b c)
              (Model.PropForm.conj  (Model.PropForm.biImpl (sigma a b c) (sigma a x c))
                      (Model.PropForm.biImpl (Model.PropForm.neg <| sigma a x b) (sigma a b c)))
          )
        )
      , -- b < x < c
        VEncCNF.guard (b < x ∧ x < c) (fun hbxc =>
          -- I{x, a, b, c} ↔ ((s{a, b, c} ↔ s{a, x, c}) ∧ (!s{b, x, c} ↔ s{a, b, c}))
          tseitin (
            Model.PropForm.biImpl (inside x a b c)
              (Model.PropForm.conj  (Model.PropForm.biImpl (sigma a b c) (sigma a x c))
                      (Model.PropForm.biImpl (Model.PropForm.neg <| sigma b x c) (sigma a b c)))
          )
        )
      ]
    ),

    -- No holes
    (tseitin (Model.PropForm.neg <| hole a b c))
    ]
  ).mapProp (by
    ext τ
    simp
    sorry)
