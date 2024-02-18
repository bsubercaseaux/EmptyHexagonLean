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

-- CC: Since we unfold a lot of definitions, having a computation can help
theorem pt_transform_eq (M : Matrix (Fin 3) (Fin 3) Real) (p : Point) :
    pt_transform M p = ![M 0 0 * p.x + M 0 1 * p.y + M 0 2, M 1 0 * p.x + M 1 1 * p.y + M 1 2] := by
  simp [pt_transform, pt_to_vec, vec_to_pt, Matrix.mul_apply, Finset.univ, Fintype.elems, List.finRange, add_assoc]
  rfl
lemma pt_to_vec_inv_vec_to_pt (v : Matrix (Fin 3) (Fin 1) Real)  (last1 : v 2 0 = 1 ): pt_to_vec (vec_to_pt v) = v := by
  simp [pt_to_vec, vec_to_pt]
  apply Matrix.ext ; intro i j
  fin_cases i
  simp ; fin_cases j ; simp
  simp ; fin_cases j ; simp
  simp ; fin_cases j ; simp
  exact Eq.symm last1


lemma pt_transform_by_prod (p : Point) (M₁ M₂ : Matrix (Fin 3) (Fin 3) Real)
  (third_row: M₂ ⟨2, by trivial⟩ = ![0, 0, 1]) :
  pt_transform (M₁ * M₂) p = pt_transform M₁ (pt_transform M₂ p) := by
  unfold pt_transform
  simp [Matrix.mul_assoc]
  let v := M₂ * pt_to_vec p
  have t : v 2 0 = 1 := by
    dsimp
    unfold pt_to_vec
    rw [Matrix.mul_apply]
    rw [Fin.sum_univ_three]
    have : M₂ 2 = ![0,0,1] := third_row
    rw [this]; simp
  rw [pt_to_vec_inv_vec_to_pt v t]

/-- `M` is an affine transformation matrix. -/
structure TMatrix (M : Matrix (Fin 3) (Fin 3) Real) : Prop :=
  det_pos : (0 : ℝ) < Matrix.det M
  third_row : M ⟨2, by trivial⟩ = ![0, 0, 1]

namespace TMatrix

def toLinearMatrix (T : TMatrix M) : Matrix (Fin 2) (Fin 2) Real :=
  !![M 0 0, M 0 1 ; M 1 0 , M 1 1]

theorem det_eq_det_toLinearMatrix (T : TMatrix M) : M.det = T.toLinearMatrix.det := by
  rw [toLinearMatrix, Matrix.det_fin_three]
  have htr := T.third_row
  have : M ⟨2, by trivial⟩ = M 2 := rfl
  rw [this] at htr
  simp [htr]

noncomputable def toAffineMap (T : TMatrix M) : Point →ᵃ[ℝ] Point where
  toFun := pt_transform M
  linear := Matrix.toEuclideanLin T.toLinearMatrix
  map_vadd' := by
    intro p1 p2
    simp_rw [vadd_eq_add, pt_transform_eq]
    simp [toLinearMatrix, Matrix.toEuclideanLin_eq_toLin]
    show _ = Matrix.mulVec !![M 0 0, M 0 1 ; M 1 0 , M 1 1] p2 + _
    simp [Matrix.mulVec, Matrix.vecHead, Matrix.vecTail, mul_add]
    ring_nf

theorem pts_to_matrix_pt_transform (p q r : Point) {M : Matrix (Fin 3) (Fin 3) Real} (T : TMatrix M) :
    pts_to_matrix (pt_transform M p) (pt_transform M q) (pt_transform M r) = M * pts_to_matrix p q r := by
  simp_rw [pt_transform_eq, pts_to_matrix]
  ext i j
  fin_cases i
  <;> simp [Matrix.mul_apply, Finset.univ, Fintype.elems, List.finRange, T.third_row]
  <;> fin_cases j <;> simp [add_assoc] <;> rfl

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
      rw [det_eq_det_toLinearMatrix] at this
      simp [toAffineMap, Matrix.toEuclideanLin_eq_toLin]
      exact ne_of_gt this)
    replace eqv := eqv.injective
    simp [LinearMap.equivOfDetNeZero, LinearEquiv.ofIsUnitDet] at eqv
    exact Equiv.Set.image _ S eqv
  hσ := by
    intro p q r
    simp [pt_transform_preserves_sigma p q r T]


def mul {M₁ M₂ : Matrix (Fin 3) (Fin 3) Real} (t1: TMatrix M₁) (t2: TMatrix M₂) : TMatrix (M₁ * M₂) := by
  have det_pos : Matrix.det (M₁ * M₂) > 0 := by
    rw [Matrix.det_mul]
    exact mul_pos t1.det_pos t2.det_pos
  have third_row : (M₁ * M₂) ⟨2, by trivial⟩ = ![0, 0, 1] := by
    ext i
    simp [Matrix.mul_apply]
    simp [t1.third_row, t2.third_row]
    fin_cases i <;> simp
    simp [Finset.univ, Fintype.elems, List.finRange, t2.third_row]
    simp [Finset.univ, Fintype.elems, List.finRange, t2.third_row]
    simp [Finset.univ, Fintype.elems, List.finRange, t2.third_row]

  exact ⟨det_pos, third_row⟩
