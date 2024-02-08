import Geo.Point
import Geo.WBPoints

namespace Geo
open List
open Classical

def σIsEmptyTriangle (p q r : Point) (pts : List Point) : Prop :=
  sorry

def HasEmptyTriangle (pts : List Point) : Prop :=
  ∃ p q r, Sublist [p, q, r] pts ∧ ∀ a ∈ pts, a ∉ ({p, q, r} : Set Point) → ¬PtInTriangle a p q r

def σHasEmptyTriangle (pts : List Point) : Prop :=
  ∃ p q r, Sublist [p, q, r] pts ∧ ∀ a ∈ pts, a ∉ ({p, q, r} : Set Point) → ¬σPtInTriangle a p q r

theorem σHasEmptyTriangle_iff {pts : List Point} (gp : Point.PointListInGeneralPosition pts) :
    σHasEmptyTriangle pts ↔ HasEmptyTriangle pts := by
  unfold σHasEmptyTriangle HasEmptyTriangle
  constructor
  sorry
  -- . intro ⟨p, q, r, hSub, h⟩
  --   use p, q, r, hSub
  --   intro a ha ha'
  --   rw [← σPtInTriangle_iff]
  --   sorry
  sorry -- obvious, TODO WN

/-
/-- The convex hull of `S` contains none of the points in `T`,
except those that are already in `S`. -/
def IsEmptyWrt (S T : Finset Point) :=
  ∀ p ∈ T, p ∉ S → p ∉ convexHull ℝ S
--def σMathyHasEmptyTriangle (pts : List Point) : Prop :=
  -- ∃ p q r, Sublist [p, q, r] pts ∧ MathyIsEmptyWrt {p, q, r} pts.toFinset
-- theorem HasEmptyTriangle_iff_Mathy (pts : List Point) (gp : Point.PointListInGeneralPosition pts) :
 --   HasEmptyTriangle pts ↔ MathyHasEmptyTriangle pts := by
 --  sorry
 -/

def OrientationProperty (P : List Point → Prop) :=
  ∀ l₁ l₂, σ_equivalence l₁ l₂ → (P l₁ ↔ P l₂)

theorem OrientationProperty.not : OrientationProperty P → OrientationProperty (¬P ·) := by
  unfold OrientationProperty
  intro h l₁ l₂ hσ
  simp [h l₁ l₂ hσ]

theorem OrientationProperty_σHasEmptyTriangle : OrientationProperty σHasEmptyTriangle :=
  sorry -- TODO(Bernardo)

theorem fundamentalTheoremOfSymmetryBreaking {P : List Point → Prop} {L : List Point} (gp : Point.PointListInGeneralPosition L) :
    OrientationProperty P → P L →
    ∃ (w : WBPoints), w.length = L.length ∧ P w.points := by
  sorry -- TODO(Bernardo)

theorem fromLeanSAT :
    ¬∃ (w : WBPoints), w.length = 10 ∧ ¬σHasEmptyTriangle w.points := by
  sorry -- TODO(Wojciech/Cayden)

theorem EmptyTriangle10TheoremLists (pts : List Point) (gp : Point.PointListInGeneralPosition pts) (h : pts.length = 10) :
    HasEmptyTriangle pts := by
  by_contra h'
  rw [← σHasEmptyTriangle_iff gp] at h'
  have ⟨w, hw, hw'⟩ := fundamentalTheoremOfSymmetryBreaking gp OrientationProperty_σHasEmptyTriangle.not h'
  apply fromLeanSAT
  use w, hw.trans h
