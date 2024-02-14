import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Algebra.Basic
import Geo.Orientations
import Geo.ToMathlib

namespace Geo

def pt_to_vec (p : Point) : Matrix (Fin 3) (Fin 1) Real :=
  !![p.x; p.y; 1]

def vec_to_pt (v : Matrix (Fin 3) (Fin 1) Real) : Point :=
  ![v 0 0, v 1 0]

def pt_transform (p : Point) (M : Matrix (Fin 3) (Fin 3) Real) : Point :=
  let A := M * (pt_to_vec p)
  vec_to_pt A


theorem σ_equiv_transitivity {pts pts' pts'' : List Point} :
    σ_equivalence pts pts' → σ_equivalence pts' pts'' →  σ_equivalence pts pts'' := by
  intro h₁ h₂
  constructor
  intro i j k hi hj hk
  rw [h₁.2 hi hj hk]
  rw [h₁.1] at hi hj hk
  rw [h₂.2 hi hj hk]
  rw [h₁.1, h₂.1]

/-- `M` is an affine transformation matrix. -/
structure TMatrix (M : Matrix (Fin 3) (Fin 3) Real) : Prop :=
  det_pos : (0 : ℝ) < Matrix.det M
  third_row : M ⟨2, by trivial⟩ = ![0, 0, 1]

theorem transform_equivalence (p q r : Point) {M : Matrix (Fin 3) (Fin 3) Real} (T : TMatrix M) :
    pts_to_matrix (pt_transform p M) (pt_transform q M) (pt_transform r M) = M * pts_to_matrix p q r := by
  unfold pts_to_matrix
  ext i j
  fin_cases i
  <;> simp [Matrix.mul_apply, pt_transform, vec_to_pt, pt_to_vec, T.third_row, Finset.univ, Fintype.elems, List.finRange]
  <;> fin_cases j <;> simp

theorem transform_preserve_sigma (p q r : Point) (T : TMatrix M) :
    σ p q r = σ (pt_transform p M) (pt_transform q M) (pt_transform r M) := by
  unfold σ matrix_det
  simp [transform_equivalence p q r T, Matrix.det_mul, mul_pos_iff_of_pos_left T.det_pos]
  congr 2  -- Cayden TODO: There's a better way to do this through mul_neg_iff
  rw [mul_neg_iff, eq_iff_iff]
  constructor
  · intro h
    exact Or.inl ⟨T.det_pos, h⟩
  · rintro (⟨_, h⟩ | ⟨h, _⟩)
    · exact h
    · exact absurd T.det_pos (lt_asymm h)

def transform_points (pts: List Point) (M : Matrix (Fin 3) (Fin 3) Real) : List Point :=
  pts.map (λ p => pt_transform p M)

theorem transform_returns_σ_equivalent (pts: List Point) (T: TMatrix M) :
  σ_equivalence pts (transform_points pts M) := by
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
