import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Algebra.Basic
import Geo.Point
import Geo.Slope
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

open Orientation Point

def pts_to_matrix (a b c : Point) : Matrix (Fin 3) (Fin 3) Real :=
  !![a.x, b.x, c.x ; a.y, b.y, c.y ; 1, 1, 1]

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

/-- For distinct points in general position (`{a,p,q,r}.size = 4`),
this means that `a` is strictly in the triangle `pqr`. --/
def PtInTriangle (a : Point) (p q r : Point) : Prop :=
  a ∈ convexHull ℝ {p, q, r}

/-- The point `a` is strictly (not on the boundary) in the triangle `pqr`. -/
def σPtInTriangle (a p q r : Point) : Prop :=
  σ p q r = σ p a r ∧
  σ p a q = σ p r q ∧
  σ q a r = σ q p r

theorem not_mem_σPtInTriangle₁ {p q r : Point} :
    InGeneralPosition₃ p q r → ¬σPtInTriangle q p q r := by
  intro h ⟨_, h', _⟩
  rw [σ_self₁, σ_perm₂] at h'
  have := congrArg (-·) h'
  simp only [neg_neg, neg_collinear] at this
  have := this ▸ h.σ_ne
  contradiction

theorem PtInTriangle.perm₁ : PtInTriangle a p q r → PtInTriangle a q p r := by
  unfold PtInTriangle
  intro
  have : ({q, p, r} : Set Point) = {p, q, r} := Set.insert_comm q p {r}
  rwa [this]

theorem PtInTriangle.perm₂ : PtInTriangle a p q r → PtInTriangle a p r q := by
  unfold PtInTriangle
  intro
  have : ({r, q} : Set Point) = {q, r} := Set.pair_comm r q
  have : ({p, r, q} : Set Point) = {p, q, r} := congrArg (insert p) this
  rwa [this]

theorem σPtInTriangle.perm₁ : σPtInTriangle a p q r → σPtInTriangle a q p r := by
  unfold σPtInTriangle
  intro ⟨h₁, h₂, h₃⟩
  conv in σ q a p => rw [σ_perm₁, σ_perm₂, σ_perm₁]
  conv in σ q r p => rw [σ_perm₁, σ_perm₂, σ_perm₁]
  simp [*]

theorem σPtInTriangle.perm₂ : σPtInTriangle a p q r → σPtInTriangle a p r q := by
  unfold σPtInTriangle
  intro ⟨h₁, h₂, h₃⟩
  conv in σ r a q => rw [σ_perm₁, σ_perm₂, σ_perm₁]
  conv in σ r p q => rw [σ_perm₁, σ_perm₂, σ_perm₁]
  simp [*]

-- TODO: bernardo is proving this, copy actual proof later
theorem σPtInTriangle_iff'' {a p q r : Point} (gp : Point.PointFinsetInGeneralPosition {a,p,q,r}) :
  σ p q r = .CCW → (σPtInTriangle a p q r ↔ PtInTriangle a p q r) := sorry

theorem σPtInTriangle_iff {a p q r : Point} (gp : Point.PointFinsetInGeneralPosition {a,p,q,r}) :
    σPtInTriangle a p q r ↔ PtInTriangle a p q r := by
  have : ({p,q,r} : Finset Point) ⊆ {a,p,q,r} := Finset.subset_insert a {p, q, r}
  rcases (gp this).σ_cases with h | h
  . exact σPtInTriangle_iff'' gp h
  . have hccw : σ p r q = .CCW := by rw [σ_perm₂, h]; rfl
    have : ({a,p,q,r} : Finset Point) = {a,p,r,q} := by ext; simp; tauto
    have : Point.PointFinsetInGeneralPosition {a,p,r,q} := by rwa [this] at gp
    have := σPtInTriangle_iff'' this hccw
    exact ⟨
      fun h => PtInTriangle.perm₂ (this.mp (σPtInTriangle.perm₂ h)),
      fun h => σPtInTriangle.perm₂ (this.mpr (PtInTriangle.perm₂ h))⟩
