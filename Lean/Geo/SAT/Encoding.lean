import LeanSAT
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Range
import Geo.SAT.Formula

-- CC: This is in my commit of LeanSAT, but not in the main branch/the branch this project pulls from
-- Ah, it's because the underlying definition of .toPropFun changed to .any and not .foldr
namespace LeanSAT

variable {L : Type u} {ν : Type v} [LitVar L ν]

@[simp]
theorem Clause.toPropFun_empty : Clause.toPropFun (#[] : Clause L) = ⊥ := by
  simp [toPropFun, Model.PropFun.any]

@[simp]
theorem Clause.toPropFun_singleton (l : L) : Clause.toPropFun #[l] = LitVar.toPropFun l := by
  ext; simp [satisfies_iff]

end LeanSAT

namespace Geo

open LeanSAT Encode VEncCNF Model Var PropFun LitVar

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

instance : FinEnum (Var n) := FinEnum.ofEquiv {
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

def signotopeClause (a b c d : Fin n) : VEncCNF (Literal (Var n)) (ν := Var n) Unit (· ⊨ orientationConstraint a b c d) :=
  seq[
    -- (s{a, b, c} ∧ s{a, c, d}) → s{a, b, d}
    andImply (#[ mkPos <| sigma a b c, mkPos <| sigma a c d ]) (mkPos <| sigma a b d)
  , -- (s{a, b, c} ∧ s{b, c, d}) → s{a, c, d}
    andImply (#[ mkPos <| sigma a b c, mkPos <| sigma b c d ]) (mkPos <| sigma a c d)
  , -- (!s{a, b, c} ∧ !s{a, c, d}) → !s{a, b, d}
    andImply (#[ mkNeg <| sigma a b c, mkNeg <| sigma a c d ]) (mkNeg <| sigma a b d)
  , -- (!s{a, b, c} ∧ !s{b, c, d}) → !s{a, c, d}
    andImply (#[ mkNeg <| sigma a b c, mkNeg <| sigma b c d ]) (mkNeg <| sigma a c d)
  ].mapProp (by
    simp [orientationConstraint]
  )

def signotopeClauses (n : Nat) : VEncCNF (Literal (Var n)) Unit (orientationConstraints n) :=
  let U := (Array.finRange n)
  ( -- for all `a`, `b`, `c` with `a < b < c`
    for_all U fun a =>
    for_all U fun b =>
    VEncCNF.guard (a < b) fun _ =>
    for_all U fun c =>
    VEncCNF.guard (b < c) fun _ =>
    for_all U fun d =>
    VEncCNF.guard (c < d) fun _ =>
      signotopeClause a b c d
  ).mapProp (by
    ext τ
    simp [orientationConstraints, ite_apply]
    apply forall_congr'; intro a; apply forall_congr'; intro b
    split <;> simp [*]
    apply forall_congr'; intro c
    split <;> simp [*]
    apply forall_congr'; intro d
    split <;> simp [*]
  )

theorem Fin.lt_asymm {a b : Fin n} : a < b → ¬b < a := @Nat.lt_asymm a b

def xIsInsideClause (a b c x : Fin n) : VEncCNF (Literal (Var n)) Unit (xIsInsideDef a b c x) :=
  seq[
    -- a < x < b
    VEncCNF.guard (a < x ∧ x < b) fun _ =>
      -- NOTE(Bernardo): Each of those should be expressible as 8 clauses or so
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
    simp [xIsInsideDef, ite_apply]
    aesop
  )

def insideClauses (n : Nat) : VEncCNF (Literal (Var n)) Unit (insideDefs n) :=
  ( let U := (Array.finRange n)
    -- for all `a`, `b`, `c` with `a < b < c`
    for_all U fun a =>
    for_all U fun b =>
    VEncCNF.guard (a < b) fun _ =>
    for_all U fun c =>
    VEncCNF.guard (b < c) fun _ =>
    for_all U fun x =>
    xIsInsideClause a b c x
  ).mapProp (by
    ext τ
    simp [insideDefs, ite_apply]
    apply forall_congr'; intro a; apply forall_congr'; intro b
    split <;> simp [*]
    apply forall_congr'; intro c
    split <;> simp [*]
  )

def notHoleOfPointInsideClauses (a b c : Fin n) : VEncCNF (Literal (Var n)) Unit (fun τ =>
      ∀ x, a < x → x < c → x ≠ b → τ (Var.inside x a b c) → !τ (Var.hole a b c)) :=
  ( for_all (Array.finRange n) fun x =>
    VEncCNF.guard (a < x ∧ x < c ∧ x ≠ b) fun _ =>
      -- Q(WN): this is just a clause, why do we need Tseitin? Also in `signotopeClause` above
      -- A?(CC): Seems like Tseitin is doing the conversion from implication to CNF
      --         I supplied the direct formula object instead here and in `signotopeClause`, and
      --         the proofs remained the same (either simp or aesop)
      imply (mkPos <| (Var.inside x a b c )) (mkNeg <| Var.hole a b c)
  ).mapProp (by
    ext τ
    simp
    apply forall_congr'
    aesop
  )

def pointInsideOfNotHoleClauses (a b c : Fin n) : VEncCNF (Literal (Var n)) Unit (fun τ =>
    !τ (Var.hole a b c) → ∃ x, a < x ∧ x < c ∧ x ≠ b ∧ τ (Var.inside x a b c)) :=
  let insideVars :=
    Array.finRange n |>.filter (fun x => a < x ∧ x < c ∧ x ≠ b) |>.map fun x => LitVar.mkPos $ Var.inside x a b c
  ( implyOr (LitVar.mkNeg <| Var.hole a b c) insideVars
  ).mapProp (by
    ext τ
    simp
    aesop)

def holeDefClauses (n : Nat) : VEncCNF (Literal (Var n)) Unit (holeDefs n) :=
  ( let U := (Array.finRange n)
    for_all U fun a =>
    for_all U fun b =>
    VEncCNF.guard (a < b) fun _ =>
    for_all U fun c =>
    VEncCNF.guard (b < c) fun _ =>
      seq[
        notHoleOfPointInsideClauses a b c,
        pointInsideOfNotHoleClauses a b c
      ]
  ).mapProp (by
    ext τ
    simp [holeDefs, ite_apply]
    apply forall_congr'; intro a
    apply forall_congr'; intro b
    split <;> simp [*]
    apply forall_congr'; intro c
    split <;> simp [*]
    conv => rhs; rw [iff_def]
    apply and_congr
    · rw [imp_forall_iff]; apply forall_congr'; aesop
    · rw [← not_imp_not]; simp
  )

def noHoleClauses (n : Nat) : VEncCNF (Literal (Var n)) Unit (noHoles n) :=
  ( let U := (Array.finRange n)
    for_all U fun a =>
    for_all U fun b =>
    VEncCNF.guard (a < b) fun _ =>
    for_all U fun c =>
    VEncCNF.guard (b < c) fun _ =>
      addClause #[(mkNeg <| Var.hole a b c)]
  ).mapProp (by
    ext τ
    simp [noHoles, ite_apply]
    apply forall_congr'; intro a
    apply forall_congr'; intro b
    split <;> simp [*]
    apply forall_congr'; intro c
    split <;> simp [*]
  )

def leftmostCCWClauses (n : Nat) : VEncCNF (Literal (Var n)) Unit (pointsCCW n) :=
  ( let U := (Array.finRange n)
    for_all U fun a =>
    VEncCNF.guard (⟨0, Fin.size_positive a⟩ < a) fun _ =>
    for_all U fun b =>
    VEncCNF.guard (a < b) fun _ =>
      addClause #[(mkPos <| Var.sigma ⟨0, Fin.size_positive a⟩ a b)]
  ).mapProp (by
    ext τ
    simp [pointsCCW, ite_apply]
    apply forall_congr'; intro a
    split
    · apply forall_congr'; intro b
      split <;> simp [*]
      aesop
    · simp only [Fin.lt_def] at *; aesop
  )

def theEncoding (n : Nat) : VEncCNF (Literal (Var n)) Unit (theFormula n) :=
  (seq[
    signotopeClauses n, insideClauses n, holeDefClauses n, noHoleClauses n, leftmostCCWClauses n
  ]).mapProp (by
    simp [theFormula]; aesop)

open Model PropFun
axiom cnfUnsat : ¬∃ τ : PropAssignment IVar,
  τ ⊨ (Geo.theEncoding 10).val.toICnf.toPropFun
