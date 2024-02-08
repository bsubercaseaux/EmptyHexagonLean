

structure EmptyCovexHexagon (S: Finset Point) (pts: Finset Point) : Prop :=
  --
  hexagon: S.card = 6
  sorry

-- Convex Hexagon at Thirty General Position Theorem
theorem EmptyHexagonTheorem (pts: Finset Point)
    (h: pts.card ≥ 30) :
  ∃ (S : Finset Point),
    (S ⊆ pts) ∧ EmptyCovexHexagon S pts := by sorry
