import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Algebra.Basic
import Geo.Definitions.Orientations
import Geo.ToMathlib

namespace Geo

def ptToVec (p : Point) : Matrix (Fin 3) (Fin 1) Real :=
  !![p.x; p.y; 1]

def vecToPt (v : Matrix (Fin 3) (Fin 1) Real) : Point :=
  ![v 0 0, v 1 0]

def ptTransform (M : Matrix (Fin 3) (Fin 3) Real) (p : Point) : Point :=
  let A := M * (ptToVec p)
  vecToPt A

-- CC: Since we unfold a lot of definitions, having a computation can help
theorem ptTransform_eq (M : Matrix (Fin 3) (Fin 3) Real) (p : Point) :
    ptTransform M p = ![M 0 0 * p.x + M 0 1 * p.y + M 0 2, M 1 0 * p.x + M 1 1 * p.y + M 1 2] := by
  simp [ptTransform, ptToVec, vecToPt, Matrix.mul_apply, Finset.univ, Fintype.elems, List.finRange, add_assoc]
  rfl
lemma pt_to_vec_inv_vec_to_pt (v : Matrix (Fin 3) (Fin 1) Real)  (last1 : v 2 0 = 1 ): ptToVec (vecToPt v) = v := by
  simp [ptToVec, vecToPt]
  apply Matrix.ext ; intro i j
  fin_cases i
  simp ; fin_cases j ; simp
  simp ; fin_cases j ; simp
  simp ; fin_cases j ; simp
  exact Eq.symm last1


lemma ptTransform_by_prod (p : Point) (M₁ M₂ : Matrix (Fin 3) (Fin 3) Real)
  (third_row: M₂ ⟨2, by trivial⟩ = ![0, 0, 1]) :
  ptTransform (M₁ * M₂) p = ptTransform M₁ (ptTransform M₂ p) := by
  unfold ptTransform
  simp [Matrix.mul_assoc]
  let v := M₂ * ptToVec p
  have t : v 2 0 = 1 := by
    dsimp
    unfold ptToVec
    rw [Matrix.mul_apply]
    rw [Fin.sum_univ_three]
    have : M₂ 2 = ![0,0,1] := third_row
    rw [this]; simp
  rw [pt_to_vec_inv_vec_to_pt v t]

/-- `M` is an affine transformation matrix. -/
structure TMatrix (M : Matrix (Fin 3) (Fin 3) Real) : Prop where
  det_pos : (0 : ℝ) < Matrix.det M
  third_row : M ⟨2, by trivial⟩ = ![0, 0, 1]

namespace TMatrix

def toLinearMatrix (_T : TMatrix M) : Matrix (Fin 2) (Fin 2) Real :=
  !![M 0 0, M 0 1 ; M 1 0 , M 1 1]

theorem det_eq_det_toLinearMatrix (T : TMatrix M) : M.det = T.toLinearMatrix.det := by
  rw [toLinearMatrix, Matrix.det_fin_three]
  have htr := T.third_row
  have : M ⟨2, by trivial⟩ = M 2 := rfl
  rw [this] at htr
  simp [htr]

noncomputable def toAffineMap (T : TMatrix M) : Point →ᵃ[ℝ] Point where
  toFun := ptTransform M
  linear := Matrix.toEuclideanLin T.toLinearMatrix
  map_vadd' := by
    intro p1 p2
    simp_rw [vadd_eq_add, ptTransform_eq]
    simp [toLinearMatrix, Matrix.toEuclideanLin_eq_toLin]
    show _ = Matrix.mulVec !![M 0 0, M 0 1 ; M 1 0 , M 1 1] p2 + _
    simp [Matrix.mulVec, Matrix.vecHead, Matrix.vecTail, mul_add]
    ring_nf

theorem Point.toMatrix_ptTransform (p q r : Point) {M : Matrix (Fin 3) (Fin 3) Real} (T : TMatrix M) :
    Point.toMatrix (ptTransform M p) (ptTransform M q) (ptTransform M r) = M * Point.toMatrix p q r := by
  simp_rw [ptTransform_eq, Point.toMatrix]
  ext i j
  fin_cases i
  <;> simp [Matrix.mul_apply, Finset.univ, Fintype.elems, List.finRange, T.third_row]
  <;> fin_cases j <;> simp [add_assoc] <;> rfl

theorem ptTransform_preserves_sigma (p q r : Point) (T : TMatrix M) :
    σ (ptTransform M p) (ptTransform M q) (ptTransform M r) = σ p q r := by
  unfold σ Point.det
  simp [Point.toMatrix_ptTransform p q r T,
    Matrix.det_mul, mul_pos_iff_of_pos_left T.det_pos, Orientation.ofReal]
  congr 2  -- Cayden TODO: There's a better way to do this through mul_neg_iff
  rw [mul_neg_iff, eq_iff_iff]
  constructor
  · rintro (⟨_, h⟩ | ⟨h, _⟩)
    · exact h
    · exact absurd T.det_pos (lt_asymm h)
  · intro h
    exact Or.inl ⟨T.det_pos, h⟩

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
