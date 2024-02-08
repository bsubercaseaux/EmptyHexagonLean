import Std.Data.List.Lemmas
import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Algebra.Basic
import Geo.Orientations

-- not used atm
#exit

namespace Geo

-- Polygons are defined by a list of points
-- no three of them on a same line
-- Note: this allows for self-intersecting polygons
structure Polygon where
  points : List Point
  at_least_three : points.length ≥ 3
  no_three_collinear : ∀ (a b c : Point), List.Sublist [a, b, c] points
                        → σ a b c ≠ Orientation.Collinear
  --- define cyclic nature:
  -- points.get (points.length) = points.get 0
  get (i : Nat ) : Point :=
    if h : i < points.length then
      points.get ⟨i, h⟩
    else
      points.get ⟨i % points.length, by apply Nat.mod_lt; linarith⟩


structure LineSegment where
  p1 : Point
  p2 : Point

structure LineEq where
  m : Real -- slope
  b : Real -- y-intercept

noncomputable def line_segment_to_lineq (l : LineSegment) : LineEq :=
  let m := (l.p2.y - l.p1.y) / (l.p2.x - l.p1.x)
  let b := l.p1.y - m * l.p1.x
  ⟨m, b⟩

noncomputable def intersection (l1 l2 : LineSegment) : Option Point :=
  let l1_eq := line_segment_to_lineq l1
  let l2_eq := line_segment_to_lineq l2
  -- m_2 * x + b_2 = m_1 * x + b_1
  -- (b_2 - b_1) = (m_1 - m_2) * x
  let x_int : Real := (l2_eq.b - l1_eq.b) / (l1_eq.m - l2_eq.m)
  let y_int : Real := l1_eq.m * x_int + l1_eq.b
  if x_int < l1.p1.x || x_int > l1.p2.x then
    none
  else if x_int < l2.p1.x || x_int > l2.p2.x then
    none
  else
    some ![x_int, y_int]


def is_simple_polygon (p : Polygon) : Prop :=
  ∀ (i j : (Fin p.points.length)),
    i ≠ j →
        match intersection ⟨p.get i, p.get (i+1)⟩
                        ⟨p.get j, p.get (j + 1)⟩ with
      | some point => point ∈ p.points
      | none       => false

-- temporary definition
def pt_inside_pgon (p : Polygon) (pt : Point) : Prop :=
  sorry

noncomputable def is_convex_polygon (P : Polygon) : Prop :=
  ∀ α : Real, α ∈ [0, 1] →
    ∀ a b : Point, pt_inside_pgon P a ∧ pt_inside_pgon P b
      → pt_inside_pgon P ![α * a.x + (1 - α) * b.x, α * a.y + (1 - α) * b.y]

def is_convex_orientation_based (P : Polygon) : Prop :=
  ∀ i : (Fin (P.points.length)),
    σ (P.get i) (P.get (i+1)) (P.get (i+2)) =
    σ (P.get (i+1)) (P.get (i+2)) (P.get (i+3))

theorem convex_iff_convex_or : ∀ (P : Polygon),
  is_convex_polygon P ↔ is_convex_orientation_based P :=
by
  intro P
  sorry
