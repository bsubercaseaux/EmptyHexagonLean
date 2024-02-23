import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Between
import Geo.Definitions.Point
import Geo.Definitions.Slope
import Geo.ToMathlib

namespace Geo
noncomputable section
open Classical

inductive Orientation : Type
  | CW -- clockwise :=  -
  | CCW -- counter clockwise:= +
  | Collinear -- := 0
  deriving DecidableEq

def Orientation.neg : Orientation → Orientation
  | CW => CCW
  | CCW => CW
  | Collinear => Collinear

instance : Neg Orientation := ⟨Orientation.neg⟩

instance : InvolutiveNeg Orientation :=
  ⟨fun o => by cases o <;> simp [Neg.neg, Orientation.neg]⟩

@[simp]
theorem Orientation.neg_cw : -CW = CCW := by rfl

@[simp]
theorem Orientation.neg_ccw : -CCW = CW := by rfl

@[simp]
theorem Orientation.neg_collinear : -Collinear = Collinear := by rfl

@[simp]
theorem Orientation.eq_neg_self (o : Orientation) : (o = -o) ↔ (o = .Collinear) := by
  cases o <;> simp [neg]

@[simp]
theorem Orientation.neg_self_eq (o : Orientation) : (-o = o) ↔ (o = .Collinear) := by
  cases o <;> simp [neg]

def Orientation.ofReal (r : ℝ) : Orientation :=
  if 0 < r then CCW
  else if r < 0 then CW
  else Collinear

theorem Orientation.ofReal_mul_left (r a : ℝ) (h : 0 < a) : ofReal (a * r) = ofReal r := by
  simp [ofReal, mul_pos_iff_of_pos_left h, mul_neg_iff_of_pos_left h]

theorem Orientation.ofReal_neg (r : ℝ) : ofReal (-r) = -ofReal r := by
  simp [ofReal]; split_ifs <;> try rfl
  cases lt_asymm ‹_› ‹_›

theorem Orientation.ofReal_eq_ccw (r : ℝ) : ofReal r = .CCW ↔ 0 < r := by
  simp [ofReal]; split_ifs <;> simp [*]

theorem Orientation.ofReal_eq_collinear (r : ℝ) : ofReal r = .Collinear ↔ r = 0 := by
  simp [ofReal]; split_ifs <;> simp [*, ne_of_lt, ne_of_gt]
  exact le_antisymm (not_lt.1 ‹_›) (not_lt.1 ‹_›)

theorem Orientation.ofReal_eq_cw (r : ℝ) : ofReal r = .CW ↔ r < 0 := by
  simp [ofReal]; split_ifs <;> simp [*, le_of_lt]

open Orientation Point

def pts_to_matrix (a b c : Point) : Matrix (Fin 3) (Fin 3) Real :=
  !![a.x, b.x, c.x ; a.y, b.y, c.y ; 1, 1, 1]

-- TODO: deduplicate det and matrix_det
def matrix_det (a b c : Point) : Real :=
  Matrix.det (pts_to_matrix a b c)

lemma matrix_det_eq_det_pts (a b c : Point) :
  matrix_det a b c = det a b c := by
    unfold matrix_det det pts_to_matrix
    rw [Matrix.det_fin_three]
    simp [Matrix.vecHead, Matrix.vecTail]
    ring_nf

noncomputable def σ (p q r : Point) : Orientation :=
  .ofReal (matrix_det p q r)

theorem σ_perm₁ (p q r : Point) : σ p q r = -σ q p r := by
  have : det p q r = -det q p r := by
    unfold det
    linarith
  simp only [σ, matrix_det_eq_det_pts, this, ofReal]
  split_ifs <;> { first | rfl | exfalso; linarith }

theorem σ_perm₂ (p q r : Point) : σ p q r = -σ p r q := by
  have : det p q r = -det p r q := by
    unfold det
    linarith
  simp only [σ, matrix_det_eq_det_pts, this, ofReal]
  split_ifs <;> { first | rfl | exfalso; linarith }

-- NOTE(WN): This is annoying to have to prove.
-- Does mathlib have a theory of antisymmetric functions, or tensors or something?
theorem σ_self₁ (p q : Point) : σ p q q = .Collinear := by
  have : σ p q q = -σ p q q := by conv => lhs; rw [σ_perm₂]
  simpa using this

theorem σ_self₂ (p q : Point) : σ q p q = .Collinear := by
  have : σ q p q = -σ q p q := by conv =>
    lhs; rw [σ_perm₁, σ_perm₂, σ_perm₁]; simp only [neg_neg]
  simpa using this

theorem σ_self₃ (p q : Point) : σ q q p = .Collinear := by
  have : σ q q p = -σ q q p := by conv => lhs; rw [σ_perm₁]
  simpa using this

theorem Point.InGeneralPosition₃.not_mem_seg :
    InGeneralPosition₃ p q r → p ∉ convexHull ℝ {q, r} := mt fun h => by
  rw [convexHull_pair] at h
  obtain ⟨a, b, _, _, eq, rfl⟩ := h
  simp [det]
  linear_combination eq * (q 1 * r 0 - q 0 * r 1)

theorem Point.InGeneralPosition₃.iff_ne_collinear {p q r : Point} :
    InGeneralPosition₃ p q r ↔ σ p q r ≠ .Collinear := by
  rw [InGeneralPosition₃, σ, matrix_det_eq_det_pts, ofReal]
  split
  . simp; linarith
  . split
    . simp; linarith
    . simp; linarith

theorem Point.InGeneralPosition₃.σ_ne {p q r : Point} :
    InGeneralPosition₃ p q r → σ p q r ≠ .Collinear := by
  intro h
  exact iff_ne_collinear.mp h

theorem Point.InGeneralPosition₃.perm₁ {p q r : Point} :
    InGeneralPosition₃ p q r → InGeneralPosition₃ q p r := by
  simp_rw [iff_ne_collinear]
  rw [σ_perm₁ p q r]
  intro h h'
  rw [h'] at h
  contradiction

theorem Point.InGeneralPosition₃.perm₂ {p q r : Point} :
    InGeneralPosition₃ p q r → InGeneralPosition₃ p r q := by
  simp_rw [iff_ne_collinear]
  rw [σ_perm₂ p q r]
  intro h h'
  rw [h'] at h
  contradiction

theorem Point.InGeneralPosition₃.of_perm (h : [p, q, r].Perm [p', q', r']) :
    InGeneralPosition₃ p q r ↔ InGeneralPosition₃ p' q' r' := by
  suffices ∀ {p q r p' q' r'}, [p, q, r].Perm [p', q', r'] →
    InGeneralPosition₃ p q r → InGeneralPosition₃ p' q' r' from ⟨this h, this h.symm⟩
  clear p q r p' q' r' h; intro p q r p' q' r' h gp
  rw [← List.mem_permutations] at h; change _ ∈ [_,_,_,_,_,_] at h; simp at h
  obtain h|h|h|h|h|h := h <;> obtain ⟨rfl,rfl,rfl⟩ := h
  · exact gp
  · exact gp.perm₁
  · exact gp.perm₁.perm₂.perm₁
  · exact gp.perm₂.perm₁
  · exact gp.perm₁.perm₂
  · exact gp.perm₂

theorem Point.PointListInGeneralPosition.subperm : PointListInGeneralPosition l ↔
    ∀ {{p q r : Point}}, [p, q, r].Subperm l → InGeneralPosition₃ p q r := by
  refine ⟨fun H _ _ _ ⟨l, p, h⟩ => ?_, fun H _ _ _ h => H h.subperm⟩
  match l, p.length_eq with
  | [p',q',r'], _ => exact (Point.InGeneralPosition₃.of_perm p).1 (H h)

theorem Point.PointListInGeneralPosition.subperm₄ : PointListInGeneralPosition l →
    ∀ {{p q r s : Point}}, [p, q, r, s].Subperm l → InGeneralPosition₄ p q r s := by
  intro gp p q r s sub
  constructor <;> {
    apply subperm.mp gp
    refine List.Subperm.trans ?_ sub -- `trans` doesn't seem to work?
    subperm_tac
  }

theorem Point.PointListInGeneralPosition.perm (h : l.Perm l') :
    PointListInGeneralPosition l ↔ PointListInGeneralPosition l' := by
  suffices ∀ {l l'}, l.Perm l' →
    PointListInGeneralPosition l → PointListInGeneralPosition l' from ⟨this h, this h.symm⟩
  clear l l' h; intro l l' p gp _ _ _ h
  exact PointListInGeneralPosition.subperm.1 gp <| List.subperm_iff.2 ⟨_, p.symm, h⟩

theorem Point.InGeneralPosition₃.ne₁ {p q r : Point} (h : InGeneralPosition₃ p q r) : p ≠ q := by
  rintro rfl; exact h.σ_ne (σ_self₃ _ _)

theorem Point.InGeneralPosition₃.ne₂ {p q r : Point} (h : InGeneralPosition₃ p q r) : p ≠ r :=
  h.perm₂.ne₁

theorem Point.InGeneralPosition₃.ne₃ {p q r : Point} (h : InGeneralPosition₃ p q r) : q ≠ r :=
  h.perm₁.ne₂

open scoped Matrix
theorem collinear_iff : σ p q r = .Collinear ↔ _root_.Collinear ℝ {p, q, r} := by
  rw [σ, Orientation.ofReal_eq_collinear, matrix_det_eq_det_pts]
  constructor <;> intro H
  · if h : q = r then subst r; simp [collinear_pair] else
    apply collinear_insert_of_mem_affineSpan_pair
    have : ⟪r - q, r - q⟫_ℝ ≠ 0 := mt inner_self_eq_zero.1 <| sub_ne_zero.2 <| Ne.symm h
    convert AffineMap.lineMap_mem_affineSpan_pair (k := ℝ)
      (⟪r - q, p - q⟫_ℝ / ⟪r - q, r - q⟫_ℝ) _ _ using 1
    simp only [AffineMap.lineMap_apply_module']; rw [Point.det] at H
    rw [← sub_eq_iff_eq_add, ← sub_eq_zero, ← smul_eq_zero_iff_right this,
      smul_sub, smul_smul, mul_div_cancel' _ this]
    ext <;> simp [norm_sq_eq_inner]
    · linear_combination H * (q 1 - r 1)
    · linear_combination H * (r 0 - q 0)
  · let ⟨v, H⟩ := (collinear_iff_of_mem (p₀ := p) (by simp)).1 H
    simp at H; obtain ⟨⟨a, rfl⟩, b, rfl⟩ := H
    simp [Point.det]; ring

theorem Point.InGeneralPosition₃.iff_collinear :
    InGeneralPosition₃ p q r ↔ ¬_root_.Collinear ℝ {p, q, r} := by
  rw [Point.InGeneralPosition₃.iff_ne_collinear, Ne, collinear_iff]

theorem Point.InGeneralPosition₃.iff_not_mem_seg : InGeneralPosition₃ p q r ↔
    p ∉ convexHull ℝ {q, r} ∧ q ∉ convexHull ℝ {p, r} ∧ r ∉ convexHull ℝ {p, q} := by
  constructor
  · intro h
    exact ⟨h.not_mem_seg, h.perm₁.not_mem_seg, h.perm₂.perm₁.not_mem_seg⟩
  · rw [Point.InGeneralPosition₃.iff_collinear, ← not_or, ← not_or]; refine mt fun h => ?_
    simp; obtain h | h | h := h.wbtw_or_wbtw_or_wbtw
    · right; left; exact mem_segment_iff_wbtw.2 h
    · right; right; exact mem_segment_iff_wbtw.2 h.symm
    · left; exact mem_segment_iff_wbtw.2 h.symm

theorem Point.InGeneralPosition₃.σ_cases {p q r : Point} :
    InGeneralPosition₃ p q r → σ p q r = .CCW ∨ σ p q r = .CW := by
  intro h
  cases h' : σ p q r <;> try tauto
  have := h.σ_ne
  contradiction

theorem Point.PointListInGeneralPosition.nodup {l : List Point}
    (h : 3 ≤ l.length) (gp : PointListInGeneralPosition l) : l.Nodup := by
  let a :: l := l
  simp; constructor
  · let b :: l := l
    simp [not_or]; constructor
    · let c :: l := l
      exact (gp <| .cons₂ _ <| .cons₂ _ <| .cons₂ _ <| List.nil_sublist _).ne₁
    · intro ha
      exact (gp <| .cons₂ _ <| .cons₂ _ <| List.singleton_sublist.2 ha).ne₂ rfl
  · refine List.nodup_iff_sublist.2 fun b h => (gp <| .cons₂ _ h).ne₃ rfl

theorem Point.InGeneralPosition₃.σ_iff {p q r : Point} :
    InGeneralPosition₃ p q r → (σ p q r ≠ .CCW ↔ σ p q r = .CW) := by
  intro h; cases h.σ_cases <;> simp_all

theorem Point.InGeneralPosition₃.σ_iff' {p q r : Point} :
    InGeneralPosition₃ p q r → (σ p q r ≠ .CW ↔ σ p q r = .CCW) := by
  intro h; cases h.σ_cases <;> simp_all

-- NOTE(WN): These lemmas are a bit upsetting.
-- Ideally we'd redefine `σ : Point³ → Bool` by arbitrarily mapping `.Collinear` to `true`.
theorem Point.InGeneralPosition₃.σ_iff₂ :
    InGeneralPosition₃ p q r → InGeneralPosition₃ s t u → ((σ p q r = .CCW ↔ σ s t u = .CCW) ↔ σ p q r = σ s t u) := by
  intro h h'
  cases h.σ_cases <;> cases h'.σ_cases <;> simp_all

theorem Point.InGeneralPosition₃.σ_iff₂' :
    InGeneralPosition₃ p q r → InGeneralPosition₃ s t u → ((σ p q r ≠ .CCW ↔ σ s t u = .CCW) ↔ σ p q r ≠ σ s t u) := by
  intro h h'
  cases h.σ_cases <;> cases h'.σ_cases <;> simp_all

theorem slope_iff_orientation {p q r : Point} (h : Sorted₃ p q r) (hGp : InGeneralPosition₃ p q r) :
    σ p q r = CCW ↔ slope p q < slope p r := by
  unfold σ Point.slope
  have qp_dx_pos : 0 < q.x - p.x := by linarith [h.h₁]
  have rp_dx_pos : 0 < r.x - p.x := by linarith [h.h₂]
  simp only [ofReal]
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

theorem no_equal_slopes {p q r : Point} (h : Sorted₃ p q r) (hGp : InGeneralPosition₃ p q r) :
  slope p q ≠ slope p r := by
  by_contra slope_eq
  have p_lt_q_x: p.x < q.x := by linarith [h.h₁]
  have q_lt_r_x: q.x < r.x := by linarith [h.h₂]
  have p_lt_r_x: p.x < r.x := by linarith
  unfold Point.slope at slope_eq
  rw [Commute.div_eq_div_iff] at slope_eq
  have det_0: det p q r = 0 := by
    unfold det
    linarith
  unfold InGeneralPosition₃ at hGp
  tauto
  unfold Commute
  unfold SemiconjBy
  linarith
  linarith
  linarith

theorem slope_iff_orientation' {p q r : Point} (h : Sorted₃ p q r) (hGp : InGeneralPosition₃ p q r) :
    σ p q r = CW ↔ slope p q > slope p r := by
    rw [←Point.InGeneralPosition₃.σ_iff]
    apply Iff.intro
    { intro hσ
      have: ¬(σ p q r = CCW) :=  by
        {aesop}
      rw [slope_iff_orientation h hGp] at this
      have: Point.slope p q ≥ Point.slope p r := by
        {aesop}
      have not_eq: Point.slope p q ≠ Point.slope p r := by
        {
          exact no_equal_slopes h hGp
        }
      have not_eq': Point.slope p r ≠ Point.slope p q := by
        {
          exact Ne.symm not_eq
        }
      apply lt_of_le_of_ne this not_eq'
    }
    {
      intro hS
      suffices: ¬(σ p q r = CCW)
      { aesop }
      {
        rw [slope_iff_orientation h hGp]
        linarith
      }
    }
    exact hGp

@[deprecated]
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
  rw [slope_iff_orientation h.h₁ hGp.gp₁,
    slope_iff_orientation h.sorted₃ hGp.gp₃,
    slope_iff_orientation h.sorted₂ hGp.gp₂]
  intro h₁ h₂
  linarith

theorem σ_prop₃ {p q r s : Point} (h : Sorted₄ p q r s) (hGp : InGeneralPosition₄ p q r s) :
    σ p q r = CW → σ q r s = CW → σ p r s = CW := by
  intro h₁ h₂
  rw [slope_iff_orientation' h.h₁ hGp.gp₁] at h₁
  rw [slope_iff_orientation' h.sorted₄ hGp.gp₄] at h₂
  rw [slope_iff_orientation' h.sorted₃ hGp.gp₃]
  rw [slope_gt_iff_gt h.sorted₃]
  rw [slope_gt_iff_gt h.sorted₁] at h₁
  have hh: Point.slope p q > Point.slope q s := by linarith
  rw [slope_gt_iff_gt h.sorted₄] at h₂
  have h2: Point.slope p r > Point.slope q r := by
    rw [slope_gt_iff_gt' h.sorted₁]
    exact h₁
  linarith

theorem σ_prop₄ {p q r s : Point} (h : Sorted₄ p q r s) (hGp : InGeneralPosition₄ p q r s) :
    σ p q r = CW → σ p r s = CW → σ p q s = CW := by
  intro h₁ h₂
  rw [slope_iff_orientation' h.h₁ hGp.gp₁] at h₁
  rw [slope_iff_orientation' h.sorted₃ hGp.gp₃] at h₂
  rw [slope_iff_orientation' h.sorted₂ hGp.gp₂]
  linarith
