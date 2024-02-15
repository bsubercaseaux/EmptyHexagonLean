import Geo.PointsToWB.SymmetryBreaking


structure ConvexQuadrilateral (a b c d : Point) : Prop :=
  -- mathy definition of convex quadrilateral


theorem convex_quadrilateral_iff_signotope_conditions (a b c d : Point) :
  ConvexQuadrilateral a b c d ↔
    σ a b c = Orientation.CCW ∧ True  := by sorry


structure CNFFormula := -- dummy definition
  (vars : List String)
  (clauses : List (List Int))
  satisfies : List Bool → Prop


def EncodeNoConvexQuadrilaterals (n : Nat) : CNFFormula :=
  sorry

structure UNSAT (formula: CNFFormula): Prop :=
  (unsatisfiable: ∀ (assignment: List Bool), ¬ formula.satisfies assignment)

structure SAT (formula: CNFFormula): Prop :=
  (satisfiable: ∃ (assignment: List Bool), formula.satisfies assignment)


----
----

---
-- A property P : (List Point) -> Bool, is gonna be called an orientation property
-- If for any pairs of list of points L, and L',
  -- it holds that omega_equivalence (L L') → P L = P L'

structure MathyNonEmptyHexagon (pts: List Point) : Prop :=
  -- mathy definition of a list of points that does not have empty exagons


structure OrientationNonEmptyHexagon (pts: List Point) : Prop :=
  condition: ∀ (a b c d e f : Point), (h: List.Sublist [a, b, c, d, e, f] pts) →
    σ a b c = Orientation.CCW ∧
    σ b c d = Orientation.CCW ∧
    σ c d e = Orientation.CCW ∧
    σ d e f = Orientation.CCW ∧
    σ e f a = Orientation.CCW ∧
    σ f a b = Orientation.CCW


def dummyOrientationProperty (pts: List Point) : Prop :=
   ∀ (a b c  : Point), List.Sublist [a, b, c] pts ∧
    σ a b c = Orientation.CCW ∧
    ¬ σ a b c = Orientation.CCW

theorem dummyNeverHolds (pts: List Point) : ¬ dummyOrientationProperty pts :=
  sorry

theorem mathy_iff_orientation_non_empty_hexagon (pts: List Point) :
  MathyNonEmptyHexagon pts ↔ OrientationNonEmptyHexagon pts :=
  sorry

-- Lemma: Let F be a boolean combination of atoms of the form
    -- (i) omegaFunction a b c = Orientation.Counterclockwise
    -- (ii) ¬ omegaFunction a b c = Orientation.Counterclockwise
  -- Then F describes an orientation property OP(F).

-- Theorem: let s_(a, b, c) be propositional variables.
      ---  and let F' be the propositional formula resulting from replacing the atoms of F by
        -- s_(a, b, c) (and ¬ s(a, b, c) respectively)
      --- Then (UNSAT F') → ∀ L : List Point (of the appropriate length)
          -- ¬ OP(F) L

      -- Proof sketch: by contradiction, assume (UNSAT F'), and
      -- that there exists a list L such that OP(F) L.
      ---- The fact that OP(F) L, implies that L ⊧ F
        ---  Now define the assignment σ : s_(a, b, c) ← omegaFunction a b c
        --- Then σ ⊧ F', and thus F' is satisfiable, which is a contradiction.



-- theorem orientation_property_abstracted (ι : Type u) (pts : ι → Point) (P : ι → ι → ι → orientation)
--   (oProp: OrientationProperty P pts) :=



-------------------------
theorem empty_quadrilateral (a b c d e : Point) :
  ∃ p q r s : Point, List.Sublist [p, q, r, s] [a, b, c, d, e] ∧
  ConvexQuadrilateral p q r s := by

  let F : CNFFormula := EncodeNoConvexQuadrilaterals 5
  have encoding_correctness : SAT F ↔
    ∃ a b c d e: Point,
      ∀ p q r s : Point,
        List.Sublist [p, q, r, s] [a, b, c, d, e] -> ¬ ConvexQuadrilateral p q r s :=
    sorry

  have unsatisfiable : ¬ SAT F := sorry

  have converse : ∀ a b c d e: Point,
    ∃ p q r s : Point, List.Sublist [p, q, r, s] [a, b, c, d, e] ∧
    ConvexQuadrilateral p q r s := by

    rw [encoding_correctness] at unsatisfiable
    push_neg at unsatisfiable
    exact unsatisfiable
      --

  exact converse a b c d e
  done
