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

/-! ## STEP 1: ROTATE -/

variable (l : Finset Point) (gp : Point.PointFinsetInGeneralPosition l)

def step1 : Finset Point :=
  let _ := l
  let _ := gp
  let _ := distinct_rotate_list l.toList sorry
  sorry

theorem step1.σ_equivalence : σ_equivalence l.toList (step1 l gp).toList := by
  sorry

theorem step1.no_same_x : ∀ᵉ (x ∈ step1 l gp) (y ∈ step1 l gp), x.x = y.x → x = y := by
  sorry

theorem step1.gen_pos : Point.PointFinsetInGeneralPosition (step1 l gp) := by
  sorry


/-! ## STEP 2: TRANSLATE -/

def step2 : Finset Point :=
  let _ := l
  let _ := gp
  sorry

theorem step2.σ_equivalence : σ_equivalence (step1 l gp).toList (insert ![0,0] (step2 l gp)).toList := by
  sorry

theorem step2.x_pos : ∀ x ∈ step2 l gp, x.x > 0 := by
  sorry

theorem step2.gen_pos : Point.PointFinsetInGeneralPosition (insert ![0,0] (step2 l gp)) := by
  sorry


/-! ## STEP 3: PROJECTION -/

/-- Takes origin :: l to other stuff -/
def step3 : Finset Point :=
  let _ := l
  let _ := gp
  sorry

theorem step3.eqv {l gp} : step2 l gp ≃ step3 l gp := by
  sorry

theorem step3.σ_eq_σ : ∀ x y z : step2 l gp, σ x y z = σ (eqv x) (eqv y) (eqv z) := by
  sorry

theorem step3.σ_eq_orientWithInfty : ∀ x y : step2 l gp, σ ![0,0] x y = orientWithInfty (eqv x) (eqv y) := by
  sorry

theorem step3.gen_pos : Point.PointFinsetInGeneralPosition (step3 l gp) := by
  sorry

theorem step3.gen_pos_with_infty : ∀ x ∈ step3 l gp, ∀ y ∈ step3 l gp, x.x = y.x → x = y := by
  sorry


/-! ## STEP 4: SORT -/

def step4 : List Point :=
  let _ := l
  let _ := gp
  sorry

-- TODO: most of WB's properties?

/-! ## STEP 5: CONSTRUCT -/

def step5 : WBPoints := sorry

theorem step5.equivalent (pts: Finset Point) :
    ∃ L : List Point, L.Nodup ∧ pts = L.toFinset ∧
    ∃ wbp : WBPoints, σ_equivalence L wbp.points := by
  sorry
