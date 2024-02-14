import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Algebra.Basic
import Geo.Orientations
import Geo.ToMathlib
import Geo.PointsToWB.TMatrix

namespace Geo

noncomputable def projectiveMap : Point → Point := fun pt =>
  ![pt.y / pt.x, 1 / pt.x]

noncomputable def orientWithInfty (p1 p2 : Point) :=
  Orientation.ofReal (p2.x - p1.x)

theorem orientWithInfty_preserved (p1 p2 : Point) (h1 : p1.x > 0) (h2 : p2.x > 0)
  : σ ![0,0] p1 p2 = orientWithInfty (projectiveMap p1) (projectiveMap p2)
  := by sorry

theorem orientations_preserved (p1 p2 p3 : Point) (h1 : p1.x > 0) (h2 : p2.x > 0) (h3 : p3.x > 0)
  : σ p1 p2 p3 = σ (projectiveMap p1) (projectiveMap p2) (projectiveMap p3)
  := by sorry

-- use this
#check Finset.sort

theorem exists_pt_st_orientations_preserved (pts : List Point) (h : pts.Sorted (·.x < ·.x))
  : ∃ z : Point, ∀ p1 ∈ pts, ∀ p2 ∈ pts, orientWithInfty p1 p2 = σ z p1 p2
  := by
  sorry
