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

  Signotope axioms:

    !s{a, b, c} ∨ !s{a, c, d} ∨ s{a, b, d}  ≃  (s{a, b, c} ∧ s{a, c, d}) → s{a, b, d}
    !s{a, b, c} ∨ !s{b, c d}  ∨ s{a, c, d}  ≃  (s{a, b, c} ∧ s{b, c, d}) → s{a, c, d}

    (We take the top grouping and do them again, except negating the actual variables)

     s{a, b, c} ∨  s{a, c, d} ∨ !s{a, b, d}  ≃  (!s{a, b, c} ∧ !s{a, c, d}) → !s{a, b, d}
     s{a, b, c} ∨  s{b, c d}  ∨ !s{a, c, d}  ≃  (!s{a, b, c} ∧ !s{b, c, d}) → !s{a, c, d}


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
  | sigma  (a b c : Fin n) (hab : a < b) (hbc : b < c)
  | inside (x a b c : Fin n) (hab : a < b) (hbc : b < c) (hax : a < x) (hxc : x < c)
  | hole   (a b c : Fin n) (hab : a < b) (hbc : b < c)
  deriving DecidableEq

instance : Fintype (Var n) := by sorry

def Array.finRange (n : Nat) : Array (Fin n) :=
  List.finRange n |> List.toArray

-- Cayden says TODO: The ↔ axioms for inside are missing, too much work without biImpl VEnc op
def trianglessss {n : Nat} (hn : n ≥ 3) : VEncCNF (Literal (Var n)) Unit ⊤ :=
  for_all (Array.finRange n) (fun a =>
    for_all (Array.finRange n) (fun b =>
      VEncCNF.guard (a < b) (fun hab =>
        for_all (Array.finRange n) (fun c =>
          VEncCNF.guard (b < c) (fun hbc =>
            -- Cayden notes: For whatever reason, "let" notation isn't allowed in these funs
            --let sabc := LitVar.mkPos <| Var.sigma a b c hab hbc
            --let habc := LitVar.mkPos <| Var.hole  a b c hab hbc
            seq

            -- Signotope axioms
            ( for_all (Array.finRange n) (fun d =>
                VEncCNF.guard (c < d) (fun hcd =>
                  tseitin
                    (.conj
                      (.impl (.conj (Var.sigma a b c hab hbc)
                                    (Var.sigma a c d (lt_trans hab hbc) hcd))
                             (Var.sigma a b d hab (lt_trans hbc hcd)) )
                    (.conj
                      (.impl (.conj (Var.sigma a b c hab hbc) (Var.sigma b c d hbc hcd))
                             (.var <| Var.sigma a c d (lt_trans hab hbc) hcd) )
                    (.conj
                      (.impl (.conj (.neg <| Var.sigma a b c hab hbc)
                                    (.neg <| Var.sigma b c d hbc hcd))
                             (.neg <| Var.sigma a b d hab (lt_trans hbc hcd)) )
                      (.impl (.conj (.neg <| Var.sigma a b c hab hbc)
                                    (.neg <| Var.sigma b c d hbc hcd))
                             (.neg <| Var.sigma a c d (lt_trans hab hbc) hcd) )
                    ) ) )
                )
              )
            )

            ( seq

            ( seq
              -- a < x < b
              ( for_all (Array.finRange n) (fun x =>
                  guard (a < x ∧ x < b) (fun haxb =>
                    -- Ix → ¬ Habc
                    -- Cayden asks: Have a simple .impl operation?
                    imply (LitVar.mkNeg <| Var.inside x a b c hab hbc haxb.1 (lt_trans haxb.2 hbc))
                          (LitVar.mkNeg <| Var.hole a b c hab hbc)
                  )
                )
              )

              -- b < x < c
              ( for_all (Array.finRange n) (fun x =>
                  VEncCNF.guard (b < x ∧ x < c) (fun hbxc =>
                    -- Ix → ¬ Habc
                    -- Cayden asks: Have a simple .impl operation?
                    imply (LitVar.mkPos <| Var.inside x a b c hab hbc (lt_trans hab hbxc.1) hbxc.2)
                          (LitVar.mkNeg <| Var.hole a b c hab hbc)
                  )
                )
              )
            )

            -- No holes
            (addClause #[LitVar.mkNeg <| Var.hole a b c hab hbc]) )
          )
        )
      )
    )
  )
  |> mapProp (by
    sorry)
