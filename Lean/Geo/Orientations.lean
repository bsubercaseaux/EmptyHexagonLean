import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Algebra.Basic
import Geo.Point
import Geo.Slope

namespace Geo

inductive Orientation : Type
  | CW -- clockwise :=  -
  | CCW -- counter clockwise:= +
  | Collinear -- := 0

open Orientation

def pts_to_matrix (a b c : Point) : Matrix (Fin 3) (Fin 3) Real :=
  Matrix.of ![![a.x, b.x, c.x], ![a.y, b.y, c.y], ![1, 1, 1]]

def matrix_det (a b c : Point) : Real :=
  Matrix.det (pts_to_matrix a b c)

lemma matrix_det_eq_det_pts (a b c : Point) :
  matrix_det a b c = determinant_pts a b c := by
    unfold matrix_det determinant_pts pts_to_matrix
    rw [Matrix.det_fin_three]
    simp [Matrix.vecHead, Matrix.vecTail]
    ring_nf

noncomputable def σ (p q r : Point) : Orientation :=
  if matrix_det p q r > 0 then CCW
  else if matrix_det p q r < 0 then CW
  else Collinear

theorem slope_iff_orientation {p q r : Point} (h : IsSortedPoints₃ p q r) (hGp : GeneralPosition₃ p q r) :
    σ p q r = CCW ↔ slope p q < slope p r := by
  unfold σ slope
  have qp_dx_pos : 0 < q.x - p.x := by linarith [h.sorted₁]
  have rp_dx_pos : 0 < r.x - p.x := by linarith [h.sorted₂]
  split
  {
    next det_pqr_pos =>
      simp only [true_iff]
      rw [matrix_det_eq_det_pts] at det_pqr_pos
      unfold determinant_pts at det_pqr_pos
      have : (r.x - p.x) * (q.y - p.y) < (r.y - p.y) * (q.x - p.x) := by linarith
      rw [div_lt_div_iff qp_dx_pos rp_dx_pos]
      linarith
  }
  {
    next det_pqr_not_pos =>
      split
      {
        next det_pqr_neg =>
          simp only [false_iff, not_lt]
          rw [matrix_det_eq_det_pts] at det_pqr_neg
          unfold determinant_pts at det_pqr_neg
          rw [div_le_div_iff rp_dx_pos qp_dx_pos]
          linarith
      }
      {
        next det_pqr_nonneg =>
          simp only [false_iff, not_lt]
          rw [matrix_det_eq_det_pts] at det_pqr_nonneg det_pqr_not_pos
          have det_pqr_zero : determinant_pts p q r = 0 := by linarith
          have := hGp.det_ne_zero
          contradiction
      }
  }


theorem σ_prop_1  (p q r s : Point) (h : IsSortedPoints₄ p q r s) (hGp : GeneralPosition₄ p q r s) :
    (σ p q r = CCW) ∧ (σ q r s = CCW) → (σ p r s = CCW) := by
  rw [slope_iff_orientation h.sorted₁ hGp.gp₁,
    slope_iff_orientation h.sorted₃ hGp.gp₃,
    slope_iff_orientation h.sorted₄ hGp.gp₄]
  rw [slope_lt_iff_lt h.sorted₃.sorted₁ h.sorted₃.sorted₂]
  intro h_land

  rw [slope_lt_iff_lt h.sorted₁.sorted₁ h.sorted₁.sorted₂] at h_land
  rw [←slope_lt_iff_lt' h.sorted₁.sorted₁ h.sorted₁.sorted₂] at h_land
  rw [slope_lt_iff_lt h.sorted₄.sorted₁ h.sorted₄.sorted₂] at h_land
  linarith
