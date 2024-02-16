import Std.Data.List.Lemmas
import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Algebra.Basic
import Geo.Orientations
import Geo.ToMathlib
import Geo.PointsToWB.TMatrix
import Geo.Definitions.WBPoints
import Geo.PointsToWB.Affine
import Geo.PointsToWB.Projective
import Geo.SigmaEquiv

open Classical

noncomputable section

namespace Geo

variable (l : Finset Point) (hl : Finset.card l ≥ 3) (gp : Point.PointFinsetInGeneralPosition l)

/-! ## STEP 1: ROTATE -/

def step1 : ∃ step1 : Finset Point,
    ∃ _ : l ≃σ step1,
    (∀ᵉ (x ∈ step1) (y ∈ step1), x.x = y.x → x = y)
  := by
  let _ := l
  let _ := gp
  have ⟨θ,h⟩ := distinct_rotate_finset l l.countable_toSet
  let T := TMatrix.rotateByAffine θ
  use l.image T.toAffineMap
  refine ⟨?seqv, ?xInj⟩
  case seqv =>
    simp [TMatrix.toAffineMap]
    exact T.toEquivσ l
  case xInj =>
    intro x hx y hy
    contrapose
    intro hne
    apply h
    · simpa [TMatrix.toAffineMap, pt_transform_rotateByAffine] using hx
    · simpa [TMatrix.toAffineMap, pt_transform_rotateByAffine] using hy
    · exact hne

/-! ## STEP 2: TRANSLATE -/

def step2 : ∃ step2 : Finset Point,
    ∃ eqv : l ≃σ (insert ![0,0] step2),
    (∀ x ∈ step2, x.x > 0) ∧
    (∀ᵉ (x ∈ step2) (y ∈ step2), x.x = y.x → x = y)
  := by
  have ⟨step1, step1_seqv, step1_xInj, step1_gp⟩ := step1 l gp
  sorry

/-! ## STEP 3: PROJECTION -/

def step3 : ∃ step3 : Finset Point,
    ∃ step2 : Finset Point,
    ∃ _ : l ≃σ (insert ![0,0] step2),
    ∃ eqv : step2 ≃σ step3,
      (∀ᵉ (x ∈ step2) (y ∈ step2), σ ![0,0] x y = orientWithInfty (eqv x) (eqv y)) ∧
      (∀ᵉ (x ∈ step3) (y ∈ step3), x.x = y.x → x = y)
  := by
  have ⟨step2, step2_seqv, step2_xInj, step2_gp⟩ := step2 l gp
  sorry

/-! ## STEP 4&5: SORT & CONSTRUCT HIGH-UP POINT -/

def finset_sort (S : Finset Point) : List Point :=
  S.toList.insertionSort (·.x <= ·.x)

theorem finset_sort_sorted (S : Finset Point) : (finset_sort S).Sorted (·.x <= ·.x) :=
  List.sorted_insertionSort (·.x <= ·.x) (S.toList)

def step45 : ∃ w : WBPoints, Nonempty (l ≃σ w.toFinset) := by
  have ⟨step3, step2, seqv_l_2, seqv_2_3, σ_2_2, nodup3⟩ := step3 l
  let step4 := finset_sort step3
  -- TODO: step₃ ≃σ step₄.toFinset
  have step4_sorted : step4.Sorted (·.x < ·.x) := sorry
  have ⟨z, hleft, horiented⟩ := exists_pt_st_orientations_preserved step4 step4_sorted
  have seqv_03_w : insert ![0,0] step3 ≃σ (z :: step4).toFinset :=
    sorry
  refine ⟨{
    leftmost := z
    rest := step4
    sorted' := List.sorted_cons.2 ⟨hleft, step4_sorted⟩
    gp' := fun {p q r} h => ?_
    oriented := ?_
  }, ⟨seqv_l_2.trans ?_⟩⟩
  -- NOTE: InGeneralPosition₃ should follow from seqv_03_w ≃σ above
  . sorry
  -- · refine Point.InGeneralPosition₃.iff_ne_collinear.2 fun eq => ?_
  --   rw [σ, Orientation.ofReal_eq_collinear, matrix_det_eq_det_pts] at eq
  --   cases h <;> rename_i h
  --   · exact gp (by simpa [Finset.subset_iff] using h.subset) eq
  --   · have := h.subset; simp at this
  --     have := horiented _ this.1 _ this.2
  --     simp [σ, matrix_det_eq_det_pts, eq, Orientation.ofReal] at this
  --     simp [orientWithInfty, Orientation.ofReal_eq_collinear, sub_eq_zero] at this
  --     have := sorted.sublist h; simp at this
  --     exact ne_of_gt this ‹_›
  . sorry
  -- · refine sorted.imp_of_mem fun {a b} ha hb h => ?_
  --   rwa [← horiented _ ha _ hb, orientWithInfty, Orientation.ofReal_eq_ccw, sub_pos]
  have seqv_02_03 : insert ![0,0] step2 ≃σ insert ![0,0] step3 :=
    sorry
  exact seqv_02_03.trans seqv_03_w

#exit

def step4 : ∃ left4 : Point,
    ∃ step4 : List Point,
    (lef4 :: step4).Sorted (·.x < ·.x) ∧
    -- ∃ step2 : Finset Point,
    -- ∃ _ : l ≃σ (insert ![0,0] step2),
    ∃ _ : l ≃σ (left4 :: step4).toFinset,
    (Point.PointFinsetInGeneralPosition step4.toFinset)
  := by
  have ⟨step3,step2,seqv_l_2,eqv,seqv_2_3,seqv_2_3_infty,gp,gp_infty⟩ := step3 l gp
  sorry

-- TODO: most of WB's properties?

/-! ## STEP 5: CONSTRUCT -/

def step5 : ∃ w : WBPoints, Nonempty (l ≃σ w.toFinset)
  := by
  have ⟨step4, sorted, step2, seqv_l_2, seqv_2_4, gp⟩ := step4 l gp
  have ⟨z, hleft, horiented⟩ := exists_pt_st_orientations_preserved step4 sorted
  refine ⟨{
    leftmost := z
    rest := step4
    sorted := List.sorted_cons.2 ⟨hleft, sorted⟩
    gp := fun {p q r} h => ?_
    oriented := ?_
  }, ⟨seqv_l_2.trans ?_⟩⟩
  · refine Point.InGeneralPosition₃.iff_ne_collinear.2 fun eq => ?_
    rw [σ, Orientation.ofReal_eq_collinear, matrix_det_eq_det_pts] at eq
    cases h <;> rename_i h
    · exact gp (by simpa [Finset.subset_iff] using h.subset) eq
    · have := h.subset; simp at this
      have := horiented _ this.1 _ this.2
      simp [σ, matrix_det_eq_det_pts, eq, Orientation.ofReal] at this
      simp [orientWithInfty, Orientation.ofReal_eq_collinear, sub_eq_zero] at this
      have := sorted.sublist h; simp at this
      exact ne_of_gt this ‹_›
  · refine sorted.imp_of_mem fun {a b} ha hb h => ?_
    rwa [← horiented _ ha _ hb, orientWithInfty, Orientation.ofReal_eq_ccw, sub_pos]
  · simp [WBPoints.toFinset, WBPoints.points]
    sorry
