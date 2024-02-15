import Std.Data.List.Lemmas
import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Algebra.Basic
import Geo.Orientations
import Geo.ToMathlib
import Geo.PointsToWB.TMatrix
import Geo.WBPoints
import Geo.PointsToWB.Affine
import Geo.PointsToWB.Projective

open Classical

noncomputable section

namespace Geo

variable (l : Finset Point) (gp : Point.PointFinsetInGeneralPosition l)

/-! ## STEP 1: ROTATE -/

def step1 : ∃ step1 : Finset Point,
    σ_equivalence l.toList step1.toList ∧
    (∀ᵉ (x ∈ step1) (y ∈ step1), x.x = y.x → x = y) ∧
    Point.PointFinsetInGeneralPosition step1
  := by
  let _ := l
  let _ := gp
  have ⟨θ,h⟩ := distinct_rotate_finset l l.countable_toSet
  use l.image (rotationMap θ)
  refine ⟨?seqv, ?xInj, ?gp⟩
  case seqv =>
    sorry
  case xInj =>
    sorry
  case gp =>
    sorry

/-! ## STEP 2: TRANSLATE -/

def step2 : ∃ step2 : Finset Point,
    σ_equivalence l.toList (insert ![0,0] step2).toList ∧
    (∀ x ∈ step2, x.x > 0) ∧
    Point.PointFinsetInGeneralPosition (insert ![0,0] step2)
  := by
  have ⟨step1, step1_seqv, step1_xInj, step1_gp⟩ := step1 l gp
  sorry


/-! ## STEP 3: PROJECTION -/

def step3 : ∃ step3 : Finset Point,
    ∃ step2 : Finset Point,
    σ_equivalence l.toList (insert ![0,0] step2).toList ∧
    ∃ eqv : step2 ≃ step3,
      (∀ x y z : step2, σ x y z = σ (eqv x) (eqv y) (eqv z)) ∧
      (∀ x y : step2, σ ![0,0] x y = orientWithInfty (eqv x) (eqv y)) ∧
      (Point.PointFinsetInGeneralPosition step3) ∧
      (∀ x ∈ step3, ∀ y ∈ step3, x.x = y.x → x = y)
  := by
  have ⟨step2, step2_seqv, step2_xInj, step2_gp⟩ := step2 l gp
  sorry


/-! ## STEP 4: SORT -/

def step4 : ∃ step4 : List Point,
    step4.Sorted (·.x < ·.x) ∧
    ∃ step2 : Finset Point,
    σ_equivalence l.toList (insert ![0,0] step2).toList ∧
    σ_equivalence step2.toList step4 ∧
    (Point.PointFinsetInGeneralPosition step4.toFinset)
  := by
  have ⟨step3,step2,seqv_l_2,eqv,seqv_2_3,seqv_2_3_infty,gp,gp_infty⟩ := step3 l gp
  sorry

-- TODO: most of WB's properties?

/-! ## STEP 5: CONSTRUCT -/

def step5 : ∃ w : WBPoints,
    σ_equivalence l.toList w.points
  := by
  sorry
