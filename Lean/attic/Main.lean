-- import Geo.PlaneGeometry
import Geo.PointsToWB.SymmetryBreaking
import Geo.Slope
import Geo.Point
import Mathlib.Data.Finset.Basic

noncomputable section

structure EmptyCovexHexagon (S: Finset Point) (pts: Finset Point) : Prop :=
  --
  hexagon: S.card = 6
  sorry


theorem EmptyHexagonTheorem (pts: Finset Point)
    (h: pts.card ≥ 30) :
  ∃ (S : Finset Point),
    (S ⊆ pts) ∧ EmptyCovexHexagon S pts := by sorry


structure Triangle (S: Finset Point) : Prop :=
  --
  triangle: S.card = 3
  triangle_list : S.toList.length = 3
  no_three_collinear: σ (S.toList.get ⟨0, by linarith⟩) (S.toList.get ⟨1, by linarith⟩) (S.toList.get ⟨2, by linarith⟩) ≠ Orientation.Collinear

def pt_in_triangle (p: Point) (T: Triangle S): Prop :=
  let L_S := S.toList
  have h: L_S.length = 3 := T.triangle_list
  -- let sorted_L_S := L_S.sort (λ p1 p2 => p1.x < p2.x)
  let a := L_S.get ⟨0, by linarith⟩
  let b := L_S.get ⟨1, by linarith⟩
  let c := L_S.get ⟨2, by linarith⟩
  sorry



def finset_sort (S : Finset Point) : List Point :=
  let L_S := S.toList
  let A_S := L_S.toArray
  (A_S.insertionSort (λ p1 p2 => p1.x <= p2.x)).toList

theorem finset_sort_sorts (S : Finset Point) : (IsSortedPts (finset_sort S)) := by
  sorry

structure ListEmptyTriangle (L : List Point) (pts : List Point) : Prop :=
  --
  let sorted_L :=


structure EmptyTriangle (S: Finset Point) (pts: Finset Point) : Prop :=
  --
  h : ListEmptyTriangle S.toList pts.toList
  -- triangle: Triangle S
  -- empty: ∀ p, p ∈ pts ∧ p ∉ S → ¬ (pt_in_triangle p triangle)





open Classical
structure GeneralPosition (pts: Finset Point) : Prop :=
  no_three_collinear: ∀ p1 p2 p3: Point, {p1, p2, p3} ⊆ pts
                        → σ p1 p2 p3 ≠ Orientation.Collinear


theorem EmptyTriangle10Theorem (pts: Finset Point)
    (gp : GeneralPosition pts)
    (h: pts.card = 10) :
  ∃ (S : Finset Point),
    S ⊆ pts ∧ EmptyTriangle S pts := by sorry


structure Has_K_Hole (S: Finset Point) (k: Nat) : Prop :=
  sorry

theorem HolesAreOrientationProperties
  (S₁ S₂ : Finset Point) (k : Nat) :
    σ_equivalence S₁ S₂ →
    (Has_K_Hole S₁ k ↔ Has_K_Hole S₂ k) := by sorry

theorem NoSameX_WLOG (n k : Nat) :
  ∃ (S : Finset Point),
    S.card = n ∧ ¬ Has_K_Hole S k
   →
  ∃ (S' : Finset Point),
    S'.card = n ∧ ¬ Has_K_Hole S' k ∧
      (NoSameX S') := by sorry
