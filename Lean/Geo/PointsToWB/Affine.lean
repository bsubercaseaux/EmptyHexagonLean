import Mathlib.Data.Set.Countable
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Intervals.IsoIoo
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Geo.PointsToWB.TMatrix

namespace Geo
noncomputable section
open Real Classical

/-! ## Rotation -/

/-- Matrix representing a counterclockwise rotation by `θ`. -/
def Matrix.rotateBy (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

def rotationMap (θ : ℝ) : Point →ₗ[ℝ] Point :=
  Matrix.toEuclideanLin (Matrix.rotateBy θ)

@[simp]
lemma rotationMap_x (θ : ℝ) (P : Point) : (rotationMap θ P).x = cos θ * P.x - sin θ * P.y := by
  -- such beautiful formal proofs
  simp [Matrix.vecHead, Matrix.vecTail, rotationMap, Matrix.toEuclideanLin,
    Matrix.toLin', Matrix.rotateBy, Point.x, Point.y]
  ring

@[simp]
lemma rotationMap_y (θ : ℝ) (P : Point) : (rotationMap θ P).y = sin θ * P.x + cos θ * P.y := by
  simp [Matrix.vecHead, Matrix.vecTail, rotationMap, Matrix.toEuclideanLin,
    Matrix.rotateBy, Point.x, Point.y]

theorem injective_rotationMap (θ : ℝ) : Function.Injective (rotationMap θ) := by
  apply LinearMap.injective_iff_surjective.mpr
  intro P
  use (rotationMap (-θ)) P
  have := sin_sq_add_cos_sq θ
  ext <;> simp only [rotationMap_x, rotationMap_y, cos_neg, sin_neg]
  linear_combination Point.x P * this
  linear_combination Point.y P * this

/-- `Matrix.rotateBy` as an affine transformation matrix. -/
def Matrix.rotateByAffine (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos θ, -Real.sin θ, 0; Real.sin θ, Real.cos θ, 0; 0, 0, 1]

lemma TMatrix.rotateByAffine (θ : ℝ) : TMatrix (Matrix.rotateByAffine θ) where
  det_pos := by simp [Matrix.det_fin_three, Matrix.rotateByAffine, ← Real.cos_sub]
  third_row := by simp [Matrix.rotateByAffine]; rfl

lemma pt_transform_rotateByAffine (p : Point) : pt_transform (Matrix.rotateByAffine θ) p = rotationMap θ p := by
  ext <;> simp [pt_transform, Matrix.rotateByAffine, Point.x, Point.y, vec_to_pt, pt_to_vec]; ring

/-- Given two distinct points `P, Q`,
if there is an angle `θ ∈ (-π/2, π/2)` rotating by which results
in their having the same `x` coordinate,
then this angle must be `arctan ((P.x - Q.x)/(P.y - Q.y))`. -/
lemma rotationMap_angle_unique (P Q : Point) : P ≠ Q →
    ∀ θ ∈ Set.Ioo (-(π/2)) (π/2), (rotationMap θ P).x = (rotationMap θ Q).x →
      θ = Real.arctan ((P.x - Q.x) / (P.y - Q.y)) := by
  intro hne
  intro θ hθ heq
  have heq : (P.x - Q.x) * cos θ = (P.y - Q.y) * sin θ := by
    rw [rotationMap_x, rotationMap_x] at heq
    linarith
  have poscoscospos : 0 < cos θ := Real.cos_pos_of_mem_Ioo hθ
  by_cases hy : P.y = Q.y
  . have : (P.x - Q.x) * cos θ = 0 := by rw [hy] at heq; linarith
    cases mul_eq_zero.mp this
    next hx =>
      exfalso
      have : P.x = Q.x := by linarith
      exact hne (Point.ext this hy)
    . linarith
  . have : P.y - Q.y ≠ 0 := fun h => hy (by linarith)
    have : (P.x - Q.x) / (P.y - Q.y) = sin θ / cos θ := by
      field_simp [heq, div_self this, mul_comm]
    have : (P.x - Q.x) / (P.y - Q.y) = tan θ := by
      simp [this, tan_eq_sin_div_cos]
    have := congrArg arctan this
    rw [Set.mem_Ioo] at hθ
    rw [arctan_tan hθ.left hθ.right] at this
    rw [this]

open Cardinal in
theorem distinct_rotate_finset (A : Set Point) (h : Set.Countable A) :
    ∃ (θ : ℝ), (rotationMap θ)''A |>.Pairwise (·.x ≠ ·.x) :=
  let badAngles := Set.image2 (fun P Q => Real.arctan ((P.x - Q.x) / (P.y - Q.y))) A A
  let goodAngles := { θ ∈ Set.Ioo (-(π/2)) (π/2) | (rotationMap θ)''A |>.Pairwise (·.x ≠ ·.x) }
  have sub : Set.Ioo (-(π/2)) (π/2) \ badAngles ⊆ goodAngles := by
    intro θ hθ
    simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_image2, not_exists, not_and] at hθ ⊢
    have ⟨hInt, hArctan⟩ := hθ; clear hθ
    refine ⟨hInt, Set.InjOn.pairwise_ne (Set.InjOn.image_of_comp ?_)⟩
    rw [Set.InjOn]
    intro P hP Q hQ rotEq
    dsimp at rotEq
    by_cases hEq : P = Q
    . assumption
    . exfalso
      apply hArctan P hP Q hQ
      rw [rotationMap_angle_unique P Q hEq θ hInt rotEq]
  have cBad : Set.Countable badAngles := Set.Countable.image2 h h _
  have uInt : #(Set.Ioo (-(π/2)) (π/2)) = 𝔠 := mk_Ioo_real (neg_lt_self (by positivity))
  have uInt : ¬Set.Countable (Set.Ioo (-(π/2)) (π/2)) := by
    rw [← Cardinal.le_aleph0_iff_set_countable, uInt]
    simp [aleph0_lt_continuum]
  have uGood : ¬Set.Countable goodAngles := fun h =>
    have : Set.Countable (Set.Ioo (-(π/2)) (π/2) \ badAngles) :=
      Set.MapsTo.countable_of_injOn (f := id) sub (Set.injOn_id _) h
    uInt (this.of_diff cBad)
  have : Set.Nonempty goodAngles := Set.Infinite.nonempty (fun h => uGood h.countable)
  ⟨this.some, (Set.mem_setOf_eq ▸ this.some_mem).right⟩

/-! ## Translation -/

def translation_matrix (s t : Real) : Matrix (Fin 3) (Fin 3) Real :=
  ![![1, 0, s], ![0, 1, t], ![0, 0, 1]]

def translation_transform (s t : Real) : TMatrix (translation_matrix s t) where
  det_pos := by simp [Matrix.det_fin_three, translation_matrix, Matrix.vecHead, Matrix.vecTail]
  third_row := rfl

lemma translation_translates (p : Point) (s t : Real) :
  pt_transform (translation_matrix s t) p = ![p.x + s, p.y + t] := by
  simp [pt_transform, translation_matrix, pt_to_vec, vec_to_pt, Matrix.mul_apply,
      Finset.univ, Fintype.elems, List.finRange]
