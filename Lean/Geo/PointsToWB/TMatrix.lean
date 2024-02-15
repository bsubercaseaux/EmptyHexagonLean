import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Algebra.Basic
import Geo.Orientations
import Geo.ToMathlib
import Geo.SigmaEquiv

namespace Geo

def pt_to_vec (p : Point) : Matrix (Fin 3) (Fin 1) Real :=
  !![p.x; p.y; 1]

def vec_to_pt (v : Matrix (Fin 3) (Fin 1) Real) : Point :=
  ![v 0 0, v 1 0]

def pt_transform (M : Matrix (Fin 3) (Fin 3) Real) (p : Point) : Point :=
  let A := M * (pt_to_vec p)
  vec_to_pt A


/-- `M` is an affine transformation matrix. -/
structure TMatrix (M : Matrix (Fin 3) (Fin 3) Real) : Prop :=
  det_pos : (0 : ℝ) < Matrix.det M
  third_row : M ⟨2, by trivial⟩ = ![0, 0, 1]

namespace TMatrix

def toLinearMatrix (T : TMatrix M) : Matrix (Fin 2) (Fin 2) Real :=
  !![M 0 0, M 0 1 ; M 1 0 , M 1 1]

theorem det_eq_det_toLinearMatrix (T : TMatrix M)
  : Matrix.det M = Matrix.det T.toLinearMatrix := by
  -- prove by unfolding everything
  sorry

noncomputable def toAffineMap (T : TMatrix M) : Point →ᵃ[ℝ] Point where
  toFun := pt_transform M
  linear := Matrix.toEuclideanLin T.toLinearMatrix
  map_vadd' := by
    intro p1 p2
    -- godawful proof we're so sorry
    simp [toLinearMatrix, pt_transform, Matrix.toEuclideanLin,
      Matrix.vecTail, Matrix.vecHead, Point.x, Point.y]
    simp [vec_to_pt, pt_to_vec, Matrix.mul_apply]
    simp [Finset.univ, Fintype.elems, List.finRange]
    simp [WithLp.equiv, Equiv.refl]
    ext <;> simp [Point.x, Point.y] <;> ring

theorem pts_to_matrix_pt_transform (p q r : Point) {M : Matrix (Fin 3) (Fin 3) Real} (T : TMatrix M) :
    pts_to_matrix (pt_transform M p) (pt_transform M q) (pt_transform M r) = M * pts_to_matrix p q r := by
  unfold pts_to_matrix
  ext i j
  fin_cases i
  <;> simp [Matrix.mul_apply, pt_transform, vec_to_pt, pt_to_vec, T.third_row, Finset.univ, Fintype.elems, List.finRange]
  <;> fin_cases j <;> simp

theorem pt_transform_preserves_sigma (p q r : Point) (T : TMatrix M) :
    σ (pt_transform M p) (pt_transform M q) (pt_transform M r) = σ p q r := by
  unfold σ matrix_det
  simp [pts_to_matrix_pt_transform p q r T, Matrix.det_mul, mul_pos_iff_of_pos_left T.det_pos, Orientation.ofReal]
  congr 2  -- Cayden TODO: There's a better way to do this through mul_neg_iff
  rw [mul_neg_iff, eq_iff_iff]
  constructor
  · rintro (⟨_, h⟩ | ⟨h, _⟩)
    · exact h
    · exact absurd T.det_pos (lt_asymm h)
  · intro h
    exact Or.inl ⟨T.det_pos, h⟩

theorem toEquivσ (S: Set Point) (T: TMatrix M) :
  S ≃σ ((pt_transform M) '' S) where
  f := by
    let eqv := LinearMap.equivOfDetNeZero T.toAffineMap.linear (by
      have := T.det_pos
      simp [toAffineMap]
      stop
      aesop)
    have := eqv.injective
    simp [LinearMap.equivOfDetNeZero, LinearEquiv.ofIsUnitDet] at this
    clear eqv
    stop
    exact Equiv.Set.image (⇑f) S this

  hσ := by
    stop
    set resulting_pts := transform_points pts M
    have same_length : pts.length = resulting_pts.length := by
      simp
      unfold transform_points
      simp [List.map]

    have same_orientation : ∀ {i j k} (hi : i < pts.length) (hj : j < pts.length) (hk : k < pts.length),
      σ (pts.get ⟨i, hi⟩) (pts.get ⟨j, hj⟩) (pts.get ⟨k, hk⟩) =
      σ (resulting_pts.get ⟨i, by rw [←same_length] ; exact hi⟩)
                    (resulting_pts.get ⟨j, by rw [←same_length] ; exact hj⟩)
                    (resulting_pts.get ⟨k, by rw [←same_length] ; exact hk⟩) := by
        intros i j k hi hj hk
        have ti : pt_transform (pts.get ⟨i, hi⟩) M = resulting_pts.get ⟨i, by rw [←same_length] ; exact hi⟩ := by
          simp [transform_points]

        have tj : pt_transform (pts.get ⟨j, hj⟩) M = resulting_pts.get ⟨j, by rw [←same_length] ; exact hj⟩ := by
          simp [transform_points]
        have tk : pt_transform (pts.get ⟨k, hk⟩) M = resulting_pts.get ⟨k, by rw [←same_length] ; exact hk⟩ := by
          simp [transform_points]

        rw [←ti, ←tj, ←tk]
        rw [transform_preserve_sigma]
        exact T
    exact ⟨same_length, same_orientation⟩
