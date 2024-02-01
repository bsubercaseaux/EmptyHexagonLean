import Mathlib.Data.List.Sort
import Geo.PlaneGeometry
import Geo.SymmetryBreaking
import Geo.Slope
import Geo.Point

namespace Geo
noncomputable section
open Classical Point

-- structure Triangle (S: Finset Point) : Prop :=
--   --
--   triangle: S.card = 3
--   triangle_list : S.toList.length = 3
--   no_three_collinear: σ (S.toList.get ⟨0, by linarith⟩) (S.toList.get ⟨1, by linarith⟩) (S.toList.get ⟨2, by linarith⟩) ≠ Orientation.Collinear

-- NB: should probably prove that this is equiv. to the defn in terms of convex combinations
-- NB: This is for points *strictly* in the triangle
def pt_in_triangle (a : Point) (p q r : Point) : Prop :=
  ∃ p' q' r', ({p', q', r'} : Set Point) = {p, q, r} ∧
    Sorted₃ p' q' r' ∧
    Sorted₃ p' a r' ∧
    a ≠ q' ∧ -- this isn't needed if p,q,r are in GP
    σ p' q' r' = σ p' a r' ∧
    σ p' a q' = σ p' r' q' ∧
    σ q' a r' = σ q' p' r'

/-- S is an empty triangle relative to pts -/
structure EmptyTriangleIn (p q r : Point) (pts : Finset Point) : Prop :=
  gp : InGeneralPosition₃ p q r
  empty: ∀ a ∈ pts, ¬(pt_in_triangle a p q r)

theorem EmptyTriangle10Theorem (pts : Finset Point)
    (gp : PointFinsetInGeneralPosition pts)
    (h : pts.card = 10) :
    ∃ (p q r : Point), {p, q, r} ⊆ pts ∧ EmptyTriangleIn p q r pts := by
  sorry
