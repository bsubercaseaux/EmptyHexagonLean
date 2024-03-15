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

inductive Orientation : Type where
  | cw -- clockwise :=  -
  | ccw -- counter clockwise := +
  | collinear -- := 0
  deriving DecidableEq

def Orientation.neg : Orientation → Orientation
  | cw => ccw
  | ccw => cw
  | collinear => collinear

instance : Neg Orientation := ⟨Orientation.neg⟩

instance : InvolutiveNeg Orientation :=
  ⟨fun o => by cases o <;> simp [Neg.neg, Orientation.neg]⟩

@[simp]
theorem Orientation.neg_cw : -cw = ccw := by rfl

@[simp]
theorem Orientation.neg_ccw : -ccw = cw := by rfl

@[simp]
theorem Orientation.neg_collinear : -collinear = collinear := by rfl

@[simp]
theorem Orientation.eq_neg_self (o : Orientation) : (o = -o) ↔ (o = .collinear) := by
  cases o <;> simp [neg]

@[simp]
theorem Orientation.neg_self_eq (o : Orientation) : (-o = o) ↔ (o = .collinear) := by
  cases o <;> simp [neg]

instance : HXor Bool Orientation Orientation :=
  ⟨fun
    | true,  o => -o
    | false, o => o⟩

@[simp]
lemma Orientation.false_xor (o : Orientation) : false ^^^ o = o := rfl

@[simp]
lemma Orientation.true_xor (o : Orientation) : true ^^^ o = -o := rfl

@[simp]
lemma Orientation.not_xor (a : Bool) (o : Orientation) : -(a ^^^ o) = (!a) ^^^ o := by
  cases a <;> cases o <;> simp

@[simp]
lemma Orientation.xor_neg (a : Bool) (o : Orientation) : a ^^^ (-o) = (!a) ^^^ o := by
  cases a <;> cases o <;> simp

@[simp]
lemma Orientation.xor_eq_xor (a : Bool) (o o' : Orientation) : (a ^^^ o = a ^^^ o') ↔ o = o' := by
  cases a <;> simp

@[simp]
lemma Orientation.xor_collinear (a : Bool) : a ^^^ collinear = collinear := by
  cases a <;> rfl

@[simp]
lemma Orientation.xor_eq_collinear (a : Bool) (o : Orientation) :
    (a ^^^ o = collinear) ↔ o = collinear := by
  cases a <;> cases o <;> simp

@[simp]
lemma Orientation.xor_xor (a b : Bool) (o : Orientation) : a ^^^ (b ^^^ o) = (xor a b) ^^^ o := by
  cases a <;> cases b <;> simp

def Orientation.ofReal (r : ℝ) : Orientation :=
  if 0 < r then ccw
  else if r < 0 then cw
  else collinear

theorem Orientation.ofReal_mul_left (r a : ℝ) (h : 0 < a) : ofReal (a * r) = ofReal r := by
  simp [ofReal, mul_pos_iff_of_pos_left h, mul_neg_iff_of_pos_left h]

theorem Orientation.ofReal_neg (r : ℝ) : ofReal (-r) = -ofReal r := by
  simp [ofReal]; split_ifs <;> try rfl
  cases lt_asymm ‹_› ‹_›

theorem Orientation.ofReal_eq_ccw (r : ℝ) : ofReal r = .ccw ↔ 0 < r := by
  simp [ofReal]; split_ifs <;> simp [*]

theorem Orientation.ofReal_eq_collinear (r : ℝ) : ofReal r = .collinear ↔ r = 0 := by
  simp [ofReal]; split_ifs <;> simp [*, ne_of_lt, ne_of_gt]
  exact le_antisymm (not_lt.1 ‹_›) (not_lt.1 ‹_›)

theorem Orientation.ofReal_eq_cw (r : ℝ) : ofReal r = .cw ↔ r < 0 := by
  simp [ofReal]; split_ifs <;> simp [*, le_of_lt]

theorem Orientation.ofReal_ne_ccw (r : ℝ) : ofReal r ≠ .ccw ↔ r ≤ 0 := by simp [ofReal_eq_ccw]

theorem Orientation.ofReal_ne_cw (r : ℝ) : ofReal r ≠ .cw ↔ 0 ≤ r := by simp [ofReal_eq_cw]

open Orientation Point

noncomputable def σ (p q r : Point) : Orientation :=
  .ofReal (det p q r)

theorem σ_eq_ccw : σ p q r = .ccw ↔ det p q r > 0 := by rw [σ, ofReal_eq_ccw]

theorem σ_eq_cw : σ p q r = .cw ↔ det p q r < 0 := by rw [σ, ofReal_eq_cw]

theorem σ_ne_cw : σ p q r ≠ .cw ↔ 0 ≤ det p q r := by rw [σ, ofReal_ne_cw]

theorem σ_eq_co : σ p q r = .collinear ↔ det p q r = 0 := by rw [σ, ofReal_eq_collinear]

theorem σ_perm₁ (p q r : Point) : σ p q r = -σ q p r := by
  simp only [σ, det_eq, det_perm₁ p q r, ofReal]
  split_ifs <;> first | rfl | exfalso; linarith

theorem σ_perm₂ (p q r : Point) : σ p q r = -σ p r q := by
  simp only [σ, det_eq, det_perm₂ p q r, ofReal]
  split_ifs <;> first | rfl | exfalso; linarith

-- NOTE(WN): This is annoying to have to prove.
-- Does mathlib have a theory of antisymmetric functions, or tensors or something?
theorem σ_self₁ (p q : Point) : σ p q q = .collinear := by
  have : σ p q q = -σ p q q := by conv => lhs; rw [σ_perm₂]
  simpa using this

theorem σ_self₂ (p q : Point) : σ q p q = .collinear := by
  have : σ q p q = -σ q p q := by conv =>
    lhs; rw [σ_perm₁, σ_perm₂, σ_perm₁]; simp only [neg_neg]
  simpa using this

theorem σ_self₃ (p q : Point) : σ q q p = .collinear := by
  have : σ q q p = -σ q q p := by conv => lhs; rw [σ_perm₁]
  simpa using this

theorem det_add_det (a b c d) : det a b c + det a c d = det a b d + det b c d := by
  simp only [det_eq]; ring

theorem σ_trans (h1 : σ a b c = .ccw) (h2 : σ a c d = .ccw) (h3 : σ a d b = .ccw) :
    σ b c d = .ccw := by
  rw [σ_eq_ccw] at *
  rw [det_perm₂] at h3
  linarith [det_add_det a b c d]

theorem Point.InGenPos₃.iff_ne_collinear {p q r : Point} :
    InGenPos₃ p q r ↔ σ p q r ≠ .collinear := by
  rw [InGenPos₃, Ne, ← σ_eq_co]

theorem Point.InGenPos₃.σ_ne {p q r : Point} :
    InGenPos₃ p q r → σ p q r ≠ .collinear := iff_ne_collinear.1

theorem Point.InGenPos₃.ne₁ {p q r : Point} (h : InGenPos₃ p q r) : p ≠ q := by
  rintro rfl; exact h.σ_ne (σ_self₃ _ _)

theorem Point.InGenPos₃.ne₂ {p q r : Point} (h : InGenPos₃ p q r) : p ≠ r :=
  h.perm₂.ne₁

theorem Point.InGenPos₃.ne₃ {p q r : Point} (h : InGenPos₃ p q r) : q ≠ r :=
  h.perm₁.ne₂

open scoped Matrix
theorem collinear_iff : σ p q r = .collinear ↔ Collinear ℝ {p, q, r} := by
  rw [σ, Orientation.ofReal_eq_collinear]
  constructor <;> intro H
  · if h : q = r then subst r; simp [collinear_pair] else
    apply collinear_insert_of_mem_affineSpan_pair
    have : ⟪r - q, r - q⟫_ℝ ≠ 0 := mt inner_self_eq_zero.1 <| sub_ne_zero.2 <| Ne.symm h
    convert AffineMap.lineMap_mem_affineSpan_pair (k := ℝ)
      (⟪r - q, p - q⟫_ℝ / ⟪r - q, r - q⟫_ℝ) _ _ using 1
    simp only [AffineMap.lineMap_apply_module']; rw [det_eq] at H
    rw [← sub_eq_iff_eq_add, ← sub_eq_zero, ← smul_eq_zero_iff_right this,
      smul_sub, smul_smul, mul_div_cancel' _ this]
    ext <;> simp [norm_sq_eq_inner]
    · linear_combination H * (q 1 - r 1)
    · linear_combination H * (r 0 - q 0)
  · let ⟨v, H⟩ := (collinear_iff_of_mem (p₀ := p) (by simp)).1 H
    simp at H; obtain ⟨⟨a, rfl⟩, b, rfl⟩ := H
    simp [det_eq]; ring

theorem Point.InGenPos₃.iff_collinear :
    InGenPos₃ p q r ↔ ¬Collinear ℝ {p, q, r} := by
  rw [Point.InGenPos₃.iff_ne_collinear, Ne, collinear_iff]

theorem Point.InGenPos₃.iff_not_mem_seg : InGenPos₃ p q r ↔
    p ∉ convexHull ℝ {q, r} ∧ q ∉ convexHull ℝ {p, r} ∧ r ∉ convexHull ℝ {p, q} := by
  constructor
  · intro h
    exact ⟨h.not_mem_seg, h.perm₁.not_mem_seg, h.perm₂.perm₁.not_mem_seg⟩
  · rw [Point.InGenPos₃.iff_collinear, ← not_or, ← not_or]; refine mt fun h => ?_
    simp; obtain h | h | h := h.wbtw_or_wbtw_or_wbtw
    · right; left; exact mem_segment_iff_wbtw.2 h
    · right; right; exact mem_segment_iff_wbtw.2 h.symm
    · left; exact mem_segment_iff_wbtw.2 h.symm

theorem Point.InGenPos₃.σ_cases {p q r : Point} :
    InGenPos₃ p q r → σ p q r = .ccw ∨ σ p q r = .cw := by
  intro h
  cases h' : σ p q r <;> try tauto
  have := h.σ_ne
  contradiction

theorem Point.ListInGenPos.nodup {l : List Point}
    (h : 3 ≤ l.length) (gp : ListInGenPos l) : l.Nodup := by
  let a :: l := l
  simp; constructor
  · let b :: l := l
    simp [not_or]; constructor
    · let c :: l := l
      exact (gp <| .cons₂ _ <| .cons₂ _ <| .cons₂ _ <| List.nil_sublist _).ne₁
    · intro ha
      exact (gp <| .cons₂ _ <| .cons₂ _ <| List.singleton_sublist.2 ha).ne₂ rfl
  · refine List.nodup_iff_sublist.2 fun b h => (gp <| .cons₂ _ h).ne₃ rfl

theorem Point.InGenPos₃.σ_iff {p q r : Point} :
    InGenPos₃ p q r → (σ p q r ≠ .ccw ↔ σ p q r = .cw) := by
  intro h; cases h.σ_cases <;> simp_all

theorem Point.InGenPos₃.σ_iff' {p q r : Point} :
    InGenPos₃ p q r → (σ p q r ≠ .cw ↔ σ p q r = .ccw) := by
  intro h; cases h.σ_cases <;> simp_all

-- NOTE(WN): These lemmas are a bit upsetting.
-- Ideally we'd redefine `σ : Point³ → Bool` by arbitrarily mapping `.collinear` to `true`.
theorem Point.InGenPos₃.σ_iff₂ :
    InGenPos₃ p q r → InGenPos₃ s t u →
    ((σ p q r = .ccw ↔ σ s t u = .ccw) ↔ σ p q r = σ s t u) := by
  intro h h'
  cases h.σ_cases <;> cases h'.σ_cases <;> simp_all

theorem Point.InGenPos₃.σ_iff₂' :
    InGenPos₃ p q r → InGenPos₃ s t u →
    ((σ p q r ≠ .ccw ↔ σ s t u = .ccw) ↔ σ p q r ≠ σ s t u) := by
  intro h h'
  cases h.σ_cases <;> cases h'.σ_cases <;> simp_all

theorem slope_iff_orientation {p q r : Point} (h : Sorted₃ p q r) (gp : InGenPos₃ p q r) :
    σ p q r = ccw ↔ slope p q < slope p r := by
  unfold σ Point.slope
  have qp_dx_pos : 0 < q.x - p.x := by linarith [h.h₁]
  have rp_dx_pos : 0 < r.x - p.x := by linarith [h.h₂]
  simp only [ofReal]
  split
  · next det_pqr_pos =>
    simp only [true_iff]
    rw [det_eq] at det_pqr_pos
    have : (r.x - p.x) * (q.y - p.y) < (r.y - p.y) * (q.x - p.x) := by linarith
    rw [div_lt_div_iff qp_dx_pos rp_dx_pos]
    linarith
  · next det_pqr_not_pos =>
    split
    · next det_pqr_neg =>
      simp only [false_iff, not_lt]
      rw [det_eq] at det_pqr_neg
      rw [div_le_div_iff rp_dx_pos qp_dx_pos]
      linarith
    · next det_pqr_nonneg =>
      simp only [false_iff, not_lt]
      have det_pqr_zero : det p q r = 0 := by linarith
      contradiction

theorem no_equal_slopes {p q r : Point} (h : Sorted₃ p q r) (gp : InGenPos₃ p q r) :
    slope p q ≠ slope p r := by
  by_contra slope_eq
  have p_lt_q_x : p.x < q.x := by linarith [h.h₁]
  have q_lt_r_x : q.x < r.x := by linarith [h.h₂]
  have p_lt_r_x : p.x < r.x := by linarith
  unfold Point.slope at slope_eq
  rw [Commute.div_eq_div_iff] at slope_eq
  · have det_0 : det p q r = 0 := by rw [det_eq]; linarith
    unfold InGenPos₃ at gp
    tauto
  · unfold Commute
    unfold SemiconjBy
    linarith
  · linarith
  · linarith

theorem slope_iff_orientation' {p q r : Point} (h : Sorted₃ p q r) (gp : InGenPos₃ p q r) :
    σ p q r = cw ↔ slope p q > slope p r := by
    rw [← gp.σ_iff]
    constructor
    · intro hσ
      have : ¬(σ p q r = ccw) := by aesop
      rw [slope_iff_orientation h gp] at this
      have : Point.slope p q ≥ Point.slope p r := by aesop
      have not_eq : Point.slope p q ≠ Point.slope p r := no_equal_slopes h gp
      exact lt_of_le_of_ne this not_eq.symm
    · intro hS
      suffices ¬(σ p q r = ccw) by aesop
      rw [slope_iff_orientation h gp]
      linarith

theorem σ_prop₁ {p q r s : Point} (h : Sorted₄ p q r s) (gp : InGenPos₄ p q r s) :
    σ p q r = ccw → σ q r s = ccw → σ p r s = ccw := by
  rw [slope_iff_orientation h.h₁ gp.gp₁,
    slope_iff_orientation h.sorted₃ gp.gp₃,
    slope_iff_orientation h.sorted₄ gp.gp₄]
  rw [slope_lt_iff_lt h.sorted₁]
  intro h₁ h₂
  rw [← slope_lt_iff_lt' h.sorted₁] at h₁
  rw [slope_lt_iff_lt h.sorted₄] at h₂
  have := lt_trans h₁ h₂
  rw [← slope_lt_iff_lt h.sorted₃] at this
  exact this

theorem σ_prop₂ {p q r s : Point} (h : Sorted₄ p q r s) (gp : InGenPos₄ p q r s) :
    σ p q r = ccw → σ p r s = ccw → σ p q s = ccw := by
  rw [slope_iff_orientation h.h₁ gp.gp₁,
    slope_iff_orientation h.sorted₃ gp.gp₃,
    slope_iff_orientation h.sorted₂ gp.gp₂]
  exact lt_trans

theorem σ_prop₃ {p q r s : Point} (h : Sorted₄ p q r s) (gp : InGenPos₄ p q r s) :
    σ p q r = cw → σ q r s = cw → σ p r s = cw := by
  intro h₁ h₂
  rw [slope_iff_orientation' h.h₁ gp.gp₁] at h₁
  rw [slope_iff_orientation' h.sorted₄ gp.gp₄] at h₂
  rw [slope_iff_orientation' h.sorted₃ gp.gp₃]
  rw [slope_gt_iff_gt h.sorted₃]
  rw [slope_gt_iff_gt h.sorted₁] at h₁
  have hh : Point.slope p q > Point.slope q s := by linarith
  rw [slope_gt_iff_gt h.sorted₄] at h₂
  have h2 : Point.slope p r > Point.slope q r := by rwa [slope_gt_iff_gt' h.sorted₁]
  linarith

theorem σ_prop₄ {p q r s : Point} (h : Sorted₄ p q r s) (gp : InGenPos₄ p q r s) :
    σ p q r = cw → σ p r s = cw → σ p q s = cw := by
  intro h₁ h₂
  rw [slope_iff_orientation' h.h₁ gp.gp₁] at h₁
  rw [slope_iff_orientation' h.sorted₃ gp.gp₃] at h₂
  rw [slope_iff_orientation' h.sorted₂ gp.gp₂]
  linarith

theorem σ_prop₁' {p q r s : Point} (h : Sorted₄ p q r s) (gp : InGenPos₄ p q r s) :
    σ p q r = ccw → σ q r s = ccw → σ p q s = ccw :=
  fun h₁ h₂ => σ_prop₂ h gp h₁ (σ_prop₁ h gp h₁ h₂)

theorem σ_prop₂' {p q r s : Point} (h : Sorted₄ p q r s) (gp : InGenPos₄ p q r s) :
    σ p q s = ccw → σ q r s = ccw → σ p r s = ccw := by
  intro h₁ h₂; by_contra h₃
  have := σ_prop₄ h gp
  simp_rw [← gp.gp₁.σ_iff, ← gp.gp₂.σ_iff, ← gp.gp₃.σ_iff] at this
  refine this (h₃ <| σ_prop₁ h gp · h₂) h₃ h₁

theorem σ_prop₃' {p q r s : Point} (h : Sorted₄ p q r s) (gp : InGenPos₄ p q r s) :
    σ p q r = cw → σ q r s = cw → σ p q s = cw :=
  fun h₁ h₂ => σ_prop₄ h gp h₁ (σ_prop₃ h gp h₁ h₂)

theorem σ_prop₄' {p q r s : Point} (h : Sorted₄ p q r s) (gp : InGenPos₄ p q r s) :
    σ p q s = cw → σ q r s = cw → σ p r s = cw := by
  intro h₁ h₂; by_contra h₃
  have := σ_prop₂ h gp
  simp_rw [← gp.gp₁.σ_iff', ← gp.gp₂.σ_iff', ← gp.gp₃.σ_iff'] at this
  refine this (h₃ <| σ_prop₃ h gp · h₂) h₃ h₁
