import Std.Data.List.Lemmas
import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Algebra.Basic
import Geo.PlaneGeometry

namespace Geo

def pt_transform (p : Point) (M : Matrix (Fin 3) (Fin 3) Real) : Point :=
  let x' := (M 0 0) * p.x + (M 0 1) * p.y + (M 0 2) * 1
  let y' := (M 1 0) * p.x + (M 1 1) * p.y + (M 1 2) * 1
  ![x', y']

def pt_to_vec (p : Point) : Matrix (Fin 3) (Fin 1) Real :=
  !![p.x; p.y; 1]

def vec_to_pt (v : Matrix (Fin 3) (Fin 1) Real) : Point :=
  ![v 0 0, v 1 1]

def pt_transform_2 (p : Point) (M : Matrix (Fin 3) (Fin 3) Real) : Point :=
  let A := M * (pt_to_vec p)
  vec_to_pt A


theorem σ_equiv_transitivity
  {pts pts' pts'' : List Point}
  (eq1 : σ_equivalence pts pts')
  (eq2 : σ_equivalence pts' pts'')
  : σ_equivalence pts pts'' := by sorry

/-- `M` is an affine transformaition matrix. -/
structure TMatrix (M : Matrix (Fin 3) (Fin 3) Real) : Prop :=
  det_pos : Matrix.det M > 0
  third_row : M 2 0 = 0 ∧ M 2 1 = 0 ∧ M 2 2 = 1

theorem transform_equivalence (p q r : Point) (T : TMatrix M) :
    pts_to_matrix (pt_transform p M) (pt_transform q M) (pt_transform r M)
  = M * pts_to_matrix p q r := by
    have eq : M * pts_to_matrix p q r = Matrix.of (![![M 0 0, M 0 1, M 0 2], ![M 1 0, M 1 1, M 1 2], ![M 2 0, M 2 1, M 2 2]]) * (Matrix.of ![![p.x, q.x, r.x], ![p.y, q.y, r.y], ![1, 1, 1]]) := by
      unfold pts_to_matrix
      rw [← Matrix.eta_fin_three]

    rw [eq]
    unfold pts_to_matrix pt_transform
    rw [T.third_row.1, T.third_row.2.1, T.third_row.2.2]
    simp
    ring_nf

theorem transform_preserve_omega (p q r : Point) (T : TMatrix M) :
  σ p q r = σ (pt_transform p M) (pt_transform q M) (pt_transform r M) := by
  unfold σ
  have det_M_pos : Matrix.det M > 0 := by
        exact T.det_pos
  unfold matrix_det
  rw [transform_equivalence p q r T]
  rw [Matrix.det_mul]
  split
  {
    next det_pqr_pos =>
      split
      { trivial }
      {
      split; nlinarith; nlinarith
      }
  }
  {
    next det_pqr_not_pos =>
      split
      {

        split
        {nlinarith}
        {
          split ; trivial ; nlinarith
        }
      }
      {
        split
        {nlinarith}
        {
          split; nlinarith ; trivial
        }
      }
  }

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
          simp
          unfold transform_points
          simp
        have tj : pt_transform (pts.get ⟨j, hj⟩) M = resulting_pts.get ⟨j, by rw [←same_length] ; exact hj⟩ := by
          simp
          unfold transform_points
          simp
        have tk : pt_transform (pts.get ⟨k, hk⟩) M = resulting_pts.get ⟨k, by rw [←same_length] ; exact hk⟩ := by
          simp
          unfold transform_points
          simp
        rw [←ti, ←tj, ←tk]
        rw [transform_preserve_omega]
        exact T
    exact ⟨same_length, same_orientation⟩


def translation_matrix (s t : Real) : Matrix (Fin 3) (Fin 3) Real :=
  Matrix.of ![![1, 0, s], ![0, 1, t], ![0, 0, 1]]

def translation_transform (s t : Real) :
  TMatrix (translation_matrix s t) := by
  have det_eq_one : Matrix.det (translation_matrix s t) = 1 := by
    rw [Matrix.det_fin_three]
    unfold translation_matrix
    simp [Matrix.vecHead, Matrix.vecTail]

  have third_row : (translation_matrix s t) 2 0 = 0 ∧ (translation_matrix s t) 2 1 = 0 ∧ (translation_matrix s t) 2 2 = 1 := by
    unfold translation_matrix
    simp [Matrix.vecHead, Matrix.vecTail]

  exact ⟨by linarith, third_row⟩

lemma translation_translates (p : Point) (s t : Real) :
  pt_transform p (translation_matrix s t) = ![p.x + s, p.y + t] := by
  unfold pt_transform translation_matrix
  simp

lemma symmetry_breaking_1 (pts: List Point) :
  ∃ (pts': List Point), (σ_equivalence pts pts') ∧ (pts ≠ [] → (pts'.get? 0) = some ![0, 0]) := by
  by_cases h : pts = []
  {
    let pts' : List Point := []
    have hle : pts.length = pts'.length  := by
      simp
      simp [h]

    have h1: σ_equivalence pts pts' := by
        exact ⟨hle, by intros i j k hi hj hk; rw [h] at hi; contradiction⟩
    exact ⟨[], ⟨h1, by intro; contradiction ⟩⟩
  }
  {
    let p1 := pts.head h
    let s := -p1.x
    let t := -p1.y
    let T := translation_transform s t
    let MT := translation_matrix s t
    let pts' := transform_points pts MT
    have h1 : σ_equivalence pts pts' := transform_returns_σ_equivalent pts T
    have h2 : pts'.get? 0 = some ![0, 0] := by
      have h3 : pt_transform p1 MT = ![0, 0] := by
        rw [translation_translates]
        simp
      simp
      unfold transform_points
      unfold List.map
      rw [←h3]
      simp
      split
      {
        contradiction
      }
      {
        simp
      }
    exact ⟨pts', ⟨h1, by intro; exact h2⟩⟩
  }

structure ccw_sorting (pts : List Point) : Prop :=
  ccw_sorting_head : pts ≠ [] → ∀ {q r}, List.Sublist [pts.head h, q, r] pts
        → σ (pts.head h) q r = Orientation.CCW

structure fully_sorted (pts : List Point) : Prop :=
    ccw_sorting_head : ccw_sorting pts
    sorted : Point.PointListSorted pts

structure first_quadrant (pts : List Point) : Prop :=
  non_neg_coordinates : ∀ p ∈ pts, p.x ≥ 0 ∧ p.y ≥ 0

structure origin_head (pts : List Point) : Prop :=
  ohprop : pts ≠ [] → pts.get? 0 = some ![0, 0]

lemma origin_head_empty (pts : List Point) (h : pts = []) : origin_head pts := by
  exact ⟨by intro; contradiction⟩

structure good_positioning (pts : List Point) : Prop :=
  sorted : Point.PointListSorted pts
  first_q : first_quadrant pts
  oh : origin_head pts

theorem to_origin_head (pts : List Point) :
    ∃ (pts': List Point), (σ_equivalence pts pts') ∧ origin_head pts' := by
  by_cases h : pts = []
  {
    let pts' : List Point := []
    have hle : pts.length = pts'.length  := by
      simp
      simp [h]

    have h1: σ_equivalence pts pts' := by
        exact ⟨hle, by intros i j k hi hj hk; rw [h] at hi; contradiction⟩
    let e : List Point := []
    have ohe : origin_head e := by
      exact origin_head_empty e rfl
    exact ⟨e, ⟨h1, ohe ⟩⟩
  }
  {
    let p1 := pts.head h
    let s := -p1.x
    let t := -p1.y
    let T := translation_transform s t
    let MT := translation_matrix s t
    let pts' := transform_points pts MT
    have h1 : σ_equivalence pts pts' := transform_returns_σ_equivalent pts T
    have h2 : pts'.get? 0 = some ![0, 0] := by
      have h3 : pt_transform p1 MT = ![0, 0] := by
        rw [translation_translates]
        simp
      simp
      unfold transform_points
      unfold List.map
      rw [←h3]
      simp
      split
      {
        contradiction
      }
      {
        simp
      }
    have oh : origin_head pts' := by
      exact ⟨by intro; exact h2⟩
    exact ⟨pts', ⟨h1, oh⟩⟩
  }

theorem first_trans (pts: List Point) (pts_sorted : Point.PointListSorted pts) :
  ∃ (pts': List Point), (σ_equivalence pts pts') ∧ (good_positioning pts') := by
  sorry


theorem sb_1_rest (pts: List Point) (h: pts ≠ [])
  (pz : pts.get? 0 = some ![0, 0]) (pts_sorted : Point.PointListSorted pts) :
    ∃ (pts': List Point), (σ_equivalence pts pts') ∧ (∀ i : Fin pts'.length, (pts'.get i).x ≥ 0 ∧ (pts'.get i).y ≥ 0) := by

  let abs_y := pts.map (λ p => abs p.y)
  have h2 : abs_y ≠ [] := by
    simp [h]
  have hh : List.length abs_y > 0 := by
    exact List.length_pos_of_ne_nil h2
  let max_abs_y : Real :=  List.maximum_of_length_pos hh

  let scaling_y_band : Matrix (Fin 3) (Fin 3) Real := Matrix.of ![![1, 0, 0], ![0, 1/(max_abs_y + 0.1), 0], ![0, 0, 1]]
  have det_scaling_y_band_pos : Matrix.det scaling_y_band > 0 := by
    rw [Matrix.det_fin_three]
    simp
    unfold List.maximum_of_length_pos
    unfold WithBot.unbot
    simp
    split
    {
     contradiction
    }
    {
      next a b c d e =>
        suffices : b >= 0
        ring_nf
        linarith
        have : b ∈ List.map (fun p ↦ |p.y|) pts := by
          apply List.maximum_mem
          exact d
        rw [List.mem_map] at this
        apply Exists.elim this
        intro a1 a2
        rw [←a2.2]
        apply abs_nonneg
    }
  let scaling_y_band_transform : TMatrix scaling_y_band := by
    exact ⟨det_scaling_y_band_pos, by simp [Matrix.vecHead, Matrix.vecTail]⟩


  let pts' := transform_points pts scaling_y_band
  have band_effect : ∀ p ∈ pts', p.y ≥ -1 ∧ p.y ≤ 1 := by
    intros p hp
    have pts'_eq : pts' = pts.map (λ p => pt_transform p scaling_y_band) := by
      simp [transform_points]
    rw [pts'_eq] at hp
    have: ∃ p1 ∈ pts, pt_transform p1 scaling_y_band = p := by
      apply List.exists_of_mem_map hp
    apply Exists.elim this
    intro a1 a2
    rw [←a2.2]
    -- simp
    unfold pt_transform
    -- simp
    have t: abs (a1.y) ∈ abs_y := by
      simp
      exact ⟨a1, by {
        exact ⟨a2.1, by rfl⟩
      } ⟩
    have abs_a1_le_max_abs_y : abs (a1.y) ≤ max_abs_y := by
      simp
      apply List.not_lt_maximum_of_mem' at t
      have: List.maximum abs_y = List.maximum (List.map (fun p ↦ |p.y|) pts) := by
        simp only []
      rw [←this]
      exact le_of_not_lt t

    let max_abs_y' := max_abs_y + 0.1
    have max_abs_y'_pos : 0 < max_abs_y' := by
      calc
        0 ≤ |a1.y| := by apply abs_nonneg
        _ ≤ max_abs_y := by linarith
        _ < max_abs_y' := by ring_nf ; linarith

    have max_abs_y'_inv_pos : 0 < max_abs_y'⁻¹ := by
      rw [inv_pos]
      exact max_abs_y'_pos

    simp
    have left :  -1 ≤ max_abs_y'⁻¹ * a1.y := by
      suffices : -max_abs_y' ≤ a1.y
      -- have ee: -max_abs_y' * max_abs_y'⁻¹ ≤ -|a1.y| * max_abs_y'⁻¹ := by
      --   apply mul_le_mul_of_nonneg_left
      --   linarith
      have e: -1 * max_abs_y' ≤ a1.y := by
        linarith
      have ed: -1 * max_abs_y' * max_abs_y'⁻¹ ≤ a1.y * max_abs_y'⁻¹ := by
        -- apply mul_le_mul_of_nonneg_left
        nlinarith

      have edd: -1 * max_abs_y' * max_abs_y'⁻¹ ≤  max_abs_y'⁻¹ * a1.y := by
        -- apply mul_le_mul_of_nonneg_left
        nlinarith
      have eddy: 1 = max_abs_y' * max_abs_y'⁻¹ := by
        rw [mul_comm, inv_mul_cancel]
        linarith
      nlinarith

      have e1: -max_abs_y' ≤ -max_abs_y := by
        ring_nf
        linarith
      have e2: -max_abs_y ≤ -|a1.y| := by
        linarith
      have e3: -|a1.y| ≤ a1.y := by
        apply neg_le_of_abs_le
        linarith
      linarith

    have right : max_abs_y'⁻¹ * a1.y ≤ 1 := by
        have : max_abs_y'⁻¹ * a1.y ≤ max_abs_y'⁻¹ * max_abs_y := by
          apply mul_le_mul_of_nonneg_left
          have : a1.y ≤ |a1.y| := by
            rw [le_abs]
            apply Or.inl
            simp

          linarith
          rw [inv_nonneg]

          calc
            _ ≤ |a1.y| := by apply abs_nonneg
            _  ≤ max_abs_y := by linarith
          ring_nf
          simp
          linarith

        have inestrict : max_abs_y'⁻¹ ≥ 0:= by
          linarith

        have e1 : max_abs_y'⁻¹ * a1.y ≤ max_abs_y'⁻¹ * max_abs_y := by linarith
        have e2 : max_abs_y'⁻¹ * max_abs_y ≤ max_abs_y'⁻¹ * max_abs_y' := by
          apply mul_le_mul_of_nonneg_left
          simp
          ring_nf
          linarith
          apply le_of_lt
          linarith

        have e3 : max_abs_y'⁻¹ * max_abs_y' = 1 := by
          rw [inv_mul_cancel]
          linarith

        linarith


    exact ⟨left, right⟩

    --- now we want to transform the pts so that the p2.x > 1
    --- if there's a single pt, we're ready
  by_cases h : pts.length = 1
  {
  exact Exists.intro pts' ⟨transform_returns_σ_equivalent pts scaling_y_band_transform, by
    intros i
    have : List.length pts' = 1 := by
      simp
      unfold transform_points
      rw [List.length_map]
      exact h

    simp [List.get]
    rw [this] at i

    -- have : i.1 < 1 := by
    --   exact i.isLt
    -- next ip ik =>
    --   cases ip
    --   next v v2 v3 =>
    --     have v20 : v2 = 0 := by
    --       linarith

    sorry
    ⟩
    -- exact band_effect (pts'.get ⟨0, by rw [←h] ; exact hi⟩) (pts'.get ⟨0, by rw [←h] ; exact hi⟩).2⟩
  }
  {
    sorry
  }

theorem symmetry_breaking (pts: List Point)  : ---  fully_sorted pts' h' ∧
    ∃ (pts': List Point), σ_equivalence pts pts' ∧ fully_sorted pts' := by

    have first_transformation:  ∃ pts'' : List Point, (σ_equivalence pts pts'') ∧ first_quadrant pts'' ∧ origin_head pts'' := by
      sorry

    apply Exists.elim first_transformation
    intro pts'' h

    have second_transformation: ∃ pts' : List Point, (σ_equivalence pts'' pts') ∧ fully_sorted pts' := by
      sorry

    apply Exists.elim second_transformation
    intro pts' h'

    have h1 : σ_equivalence pts pts' := by
      exact σ_equiv_transitivity h.1 h'.1
    sorry
