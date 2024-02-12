import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Algebra.Basic
import Geo.Point
import Geo.Slope

namespace Geo
noncomputable section
open Classical

inductive Orientation : Type
  | CW -- clockwise :=  -
  | CCW -- counter clockwise:= +
  | Collinear -- := 0
  deriving DecidableEq

open Orientation Point

def pts_to_matrix (a b c : Point) : Matrix (Fin 3) (Fin 3) Real :=
  Matrix.of ![![a.x, b.x, c.x], ![a.y, b.y, c.y], ![1, 1, 1]]

def matrix_det (a b c : Point) : Real :=
  Matrix.det (pts_to_matrix a b c)

lemma matrix_det_eq_det_pts (a b c : Point) :
  matrix_det a b c = det a b c := by
    unfold matrix_det det pts_to_matrix
    rw [Matrix.det_fin_three]
    simp [Matrix.vecHead, Matrix.vecTail]
    ring_nf

noncomputable def σ (p q r : Point) : Orientation :=
  if matrix_det p q r > 0 then CCW
  else if matrix_det p q r < 0 then CW
  else Collinear

theorem Point.InGeneralPosition₃.σ_ne {p q r : Point} :
    InGeneralPosition₃ p q r → σ p q r ≠ .Collinear := by
  rw [InGeneralPosition₃, σ, matrix_det_eq_det_pts]
  split <;> first | split; simp | simp
  have : det p q r = 0 := by linarith
  simpa

theorem Point.InGeneralPosition₃.σ_cases {p q r : Point} :
    InGeneralPosition₃ p q r → σ p q r = .CCW ∨ σ p q r = .CW := by
  intro h
  cases h' : σ p q r <;> try tauto
  have := h.σ_ne
  contradiction

theorem Point.InGeneralPosition₃.σ_iff {p q r : Point} :
    InGeneralPosition₃ p q r → (σ p q r ≠ .CCW ↔ σ p q r = .CW) := by
  intro h; cases h.σ_cases <;> simp_all

theorem Point.InGeneralPosition₃.σ_iff' {p q r : Point} :
    InGeneralPosition₃ p q r → (σ p q r ≠ .CW ↔ σ p q r = .CCW) := by
  intro h; cases h.σ_cases <;> simp_all

theorem slope_iff_orientation {p q r : Point} (h : Sorted₃ p q r) (hGp : InGeneralPosition₃ p q r) :
    σ p q r = CCW ↔ slope p q < slope p r := by
  unfold σ Point.slope
  have qp_dx_pos : 0 < q.x - p.x := by linarith [h.h₁]
  have rp_dx_pos : 0 < r.x - p.x := by linarith [h.h₂]
  split
  {
    next det_pqr_pos =>
      simp only [true_iff]
      rw [matrix_det_eq_det_pts] at det_pqr_pos
      unfold det at det_pqr_pos
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
          unfold det at det_pqr_neg
          rw [div_le_div_iff rp_dx_pos qp_dx_pos]
          linarith
      }
      {
        next det_pqr_nonneg =>
          simp only [false_iff, not_lt]
          rw [matrix_det_eq_det_pts] at det_pqr_nonneg det_pqr_not_pos
          have det_pqr_zero : det p q r = 0 := by linarith
          contradiction
      }
  }

structure σ_equivalence (pts pts' : List Point) : Prop :=
    same_length : pts.length = pts'.length
    same_orientation : ∀ {i j k} (hi : i < pts.length) (hj : j < pts.length) (hk : k < pts.length),
        σ (pts.get ⟨i, hi⟩) (pts.get ⟨j, hj⟩) (pts.get ⟨k, hk⟩) =
        σ (pts'.get ⟨i, by rw [←same_length] ; exact hi⟩)
                      (pts'.get ⟨j, by rw [←same_length] ; exact hj⟩)
                      (pts'.get ⟨k, by rw [←same_length] ; exact hk⟩)

theorem σ_prop₁ {p q r s : Point} (h : Sorted₄ p q r s) (hGp : InGeneralPosition₄ p q r s) :
    σ p q r = CCW → σ q r s = CCW → σ p r s = CCW := by
  rw [slope_iff_orientation h.h₁ hGp.gp₁,
    slope_iff_orientation h.sorted₃ hGp.gp₃,
    slope_iff_orientation h.sorted₄ hGp.gp₄]
  rw [slope_lt_iff_lt h.sorted₁]
  intro h₁ h₂
  rw [← slope_lt_iff_lt' h.sorted₁] at h₁
  rw [slope_lt_iff_lt h.sorted₄] at h₂
  have := lt_trans h₁ h₂
  rw [← slope_lt_iff_lt h.sorted₃] at this
  exact this

theorem σ_prop₂ {p q r s : Point} (h : Sorted₄ p q r s) (hGp : InGeneralPosition₄ p q r s) :
    σ p q r = CCW → σ p r s = CCW → σ p q s = CCW := by
  sorry

theorem σ_prop₃ {p q r s : Point} (h : Sorted₄ p q r s) (hGp : InGeneralPosition₄ p q r s) :
    σ p q r = CW → σ q r s = CW → σ p r s = CW := by
  sorry

theorem σ_prop₄ {p q r s : Point} (h : Sorted₄ p q r s) (hGp : InGeneralPosition₄ p q r s) :
    σ p q r = CW → σ p r s = CW → σ p q s = CW := by
  sorry

/-- For distinct points in general position (`{a,p,q,r}.size = 4`),
this means that `a` is strictly in the triangle `pqr`. --/
def PtInTriangle (a : Point) (p q r : Point) : Prop :=
  a ∈ convexHull ℝ {p, q, r}

/-- The point `a` is strictly (not on the boundary) in the triangle `pqr`. -/
def σPtInTriangle (a p q r : Point) : Prop :=
  σ p q r = σ p a r ∧
  σ p a q = σ p r q ∧
  σ q a r = σ q p r

theorem σPtInTriangle_iff {a p q r : Point} (gp : Point.PointFinsetInGeneralPosition {a,p,q,r}) :
    σPtInTriangle a p q r ↔ PtInTriangle a p q r := by
  sorry -- geometry and signotope stuff TODO(Bernardo)
