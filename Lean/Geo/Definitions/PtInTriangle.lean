import Geo.Definitions.Point
import Geo.Definitions.WBPoints
import Geo.Orientations
import Geo.PointsToWB.TMatrix
import Geo.PointsToWB.Affine

/-! We define `PtInTriangle`, `σPtInTriangle`,
and show their equivalence for points in general position. -/

namespace Geo
open Point List Orientation

noncomputable section
open Classical

/-- `PtInTriangle a p q r` means that `a` is in the triangle `pqr`,
possibly on the boundary. -/
def PtInTriangle (a : Point) (p q r : Point) : Prop :=
  a ∈ convexHull ℝ {p, q, r}

lemma xlt_convexHull {s : Set Point} (x₀ : ℝ) :
    (∀ p ∈ s, p.x < x₀) → ∀ p ∈ convexHull ℝ s, p.x < x₀ := by
  intro ub _ hp
  let H := {p : Point | p.x < x₀}
  let cvxH : Convex ℝ H :=
    convex_halfspace_lt ⟨fun _ _ => rfl, fun _ _ => rfl⟩ x₀
  have : s ⊆ H := ub
  have : convexHull ℝ s ⊆ H :=
    convexHull_min ub cvxH
  exact this hp

lemma xgt_convexHull {s : Set Point} (x₀ : ℝ) :
    (∀ p ∈ s, x₀ < p.x) → ∀ p ∈ convexHull ℝ s, x₀ < p.x := by
  intro ub _ hp
  let H := {p : Point | x₀ < p.x}
  let cvxH : Convex ℝ H :=
    convex_halfspace_gt ⟨fun _ _ => rfl, fun _ _ => rfl⟩ x₀
  have : s ⊆ H := ub
  have : convexHull ℝ s ⊆ H :=
    convexHull_min ub cvxH
  exact this hp

lemma xBounded_of_PtInTriangle' {x a b c : Point} :
    Sorted₃ a b c → PtInTriangle x a b c → a.x ≤ x.x ∧ x.x ≤ c.x := by
  unfold PtInTriangle
  intro sorted tri
  let S := { p : Point | a.x ≤ p.x } ∩ { p : Point | p.x ≤ c.x }
  have cvxS : Convex ℝ S :=
    Convex.inter
      (convex_halfspace_ge ⟨fun _ _ => rfl, fun _ _ => rfl⟩ a.x)
      (convex_halfspace_le ⟨fun _ _ => rfl, fun _ _ => rfl⟩ c.x)
  have abcS : {a, b, c} ⊆ S := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    rcases hx with rfl | rfl | rfl
    . exact ⟨le_rfl, le_of_lt <| sorted.h₁.trans sorted.h₂⟩
    . exact ⟨le_of_lt sorted.h₁, le_of_lt sorted.h₂⟩
    . exact ⟨le_of_lt <| sorted.h₁.trans sorted.h₂, le_rfl⟩
  have : x ∈ S := convexHull_min abcS cvxS tri
  simpa only [Set.mem_inter_iff, Set.mem_setOf_eq] using this

theorem PtInTriangle.perm₁ : PtInTriangle a p q r → PtInTriangle a q p r := by
  simp [PtInTriangle, Set.insert_comm]

theorem PtInTriangle.perm₂ : PtInTriangle a p q r → PtInTriangle a p r q := by
  simp [PtInTriangle, Set.pair_comm]

/-- `σPtInTriangle a p q r` means that `a` is in the triangle `pqr` strictly,
i.e., not on the boundary. -/
def σPtInTriangle (a p q r : Point) : Prop :=
  σ p q a = σ p q r ∧
  σ p a r = σ p q r ∧
  σ a q r = σ p q r

theorem not_mem_σPtInTriangle {p q r : Point} :
    InGeneralPosition₃ p q r → ¬σPtInTriangle q p q r := by
  intro h ⟨h', _, _⟩
  rw [σ_self₁] at h'
  have := h.σ_ne
  rw [← h'] at this
  contradiction

theorem σPtInTriangle.perm₁ : σPtInTriangle a p q r → σPtInTriangle a q p r := by
  unfold σPtInTriangle
  intro ⟨h₁, h₂, h₃⟩
  rw [σ_perm₁ p q r, σ_perm₁, neg_inj] at h₁ h₂ h₃
  exact ⟨h₁, h₃, h₂⟩

theorem σPtInTriangle.perm₂ : σPtInTriangle a p q r → σPtInTriangle a p r q := by
  unfold σPtInTriangle
  intro ⟨h₁, h₂, h₃⟩
  rw [σ_perm₂ p q r, σ_perm₂, neg_inj] at h₁ h₂ h₃
  exact ⟨h₂, h₁, h₃⟩

theorem σPtInTriangle.perm (h : [p, q, r].Perm [p', q', r']) :
    σPtInTriangle a p q r ↔ σPtInTriangle a p' q' r' :=
  perm₃_induction (fun _ _ _ => (·.perm₁)) (fun _ _ _ => (·.perm₂)) h

theorem σPtInTriangle.gp₄_of_gp₃ :
    InGeneralPosition₃ p q r → σPtInTriangle a p q r → InGeneralPosition₄ a p q r := by
  intro gp ⟨tri₁, tri₂, tri₃⟩
  have gp := gp.σ_ne
  constructor
  · rwa [InGeneralPosition₃.iff_ne_collinear, σ_perm₁, ← σ_perm₂, tri₁]
  · apply InGeneralPosition₃.perm₁; rwa [InGeneralPosition₃.iff_ne_collinear, tri₂]
  · rwa [InGeneralPosition₃.iff_ne_collinear, tri₃]
  · assumption

/-! ## Proof of equivalence between σPtInTriangle and PtInTriangle -/

-- TODO: deduplicate with PointsToWB.Affine
noncomputable def rotateTranslate (p : Point) (θ : ℝ) (tx ty : ℝ) : Point :=
  ![p 0 * (Real.cos θ) - p 1 * (Real.sin θ) + tx, p 0 * (Real.sin θ) + p 1 * (Real.cos θ) + ty]

def translateMap (p : Point) : Point →ᵃ[ℝ] Point :=
  AffineMap.const ℝ Point p + AffineMap.id ℝ Point

theorem translateMap_apply (x : Point) : translateMap p x = p + x := by
  simp [translateMap]

def rotateTranslateMap (θ : ℝ) (p : Point) : Point →ᵃ[ℝ] Point :=
  AffineMap.comp (translateMap p) (rotationMap θ).toAffineMap

theorem injective_rotateTranslateMap (θ : ℝ) (p : Point) :
    Function.Injective (rotateTranslateMap θ p) := by
  unfold rotateTranslateMap
  apply Function.Injective.comp (g := translateMap p)
  . exact fun x y h => add_left_cancel h
  . simp [injective_rotationMap]

lemma ptTransform_translateMap (p t : Point) :
    ptTransform (translationMatrix t.x t.y) p = translateMap t p := by
  ext <;> simp [ptTransform, translationMatrix, Point.x, Point.y, vecToPt, ptToVec];
  ring_nf
  rw [translateMap_apply]
  simp
  rw [Matrix.mul_apply]
  rw [Fin.sum_univ_three]
  simp [add_comm]
  rw [Matrix.mul_apply]
  rw [Fin.sum_univ_three]
  simp
  rw [translateMap_apply]
  simp [add_comm]

noncomputable def rotate (θ : ℝ) (p : Point) : Point :=
  ![p 0 * (Real.cos θ) - p 1 * (Real.sin θ), p 0 * (Real.sin θ) + p 1 * (Real.cos θ)]

theorem rotateTranslateTransform (θ : ℝ) (t p : Point) :
    (rotateTranslateMap θ t p) =
    ptTransform (translationMatrix t.x t.y * Matrix.rotateByAffine θ) p := by
  rw [ptTransform_by_prod]
  unfold rotateTranslateMap
  simp
  rw [← ptTransform_rotateByAffine, ptTransform_translateMap]; rfl

lemma rotateTranslateTMatrix (θ : ℝ) (t : Point) :
    TMatrix (translationMatrix t.x t.y * Matrix.rotateByAffine θ) :=
  TMatrix.mul (translationTransform t.x t.y) (TMatrix.rotateByAffine θ)

theorem convex3combo (S : Set Point) (CS : Convex ℝ S) (a b c : Point)
    (aS : a ∈ S) (bS : b ∈ S) (cS : c ∈ S) (α β γ : ℝ) (sum1 : α + β + γ = 1)
    (α0 : α ≥ 0) (β0 : β ≥ 0) (γ0 : γ ≥ 0) : α • a + β • b + γ • c ∈ S := by
  by_cases case : α + β = 0
  · have α0 : α = 0 := by linarith
    have β0 : β = 0 := by linarith
    have γ1 : γ = 1 := by linarith
    rw [α0, β0, γ1]
    simp
    exact cS
  · let α' := α / (α + β)
    let β' := β / (α + β)
    have α'0 : α' ≥ 0 := div_nonneg α0 (by linarith)
    have β'0 : β' ≥ 0 := div_nonneg β0 (by linarith)

    have αβsum : α' + β' = 1 := by rwa [div_add_div_same, div_self]
    let combo := α' • a + β' • b
    have comboInS : combo ∈ S := CS aS bS α'0 β'0 αβsum
    let fSum := α + β
    have fSumNN : fSum ≥ 0 := by simp; linarith
    have fSumγ : fSum + γ = 1 := by rw [sum1]
    let combo2 := fSum • combo + γ • c
    have combo2InS : combo2 ∈ S := CS comboInS cS fSumNN γ0 fSumγ

    have combo2Eq : combo2 = α • a + β • b + γ • c := by
      simp only [smul_add, ← smul_assoc]; field_simp
      rw [mul_comm, mul_div_assoc, div_self case]; field_simp
      rw [mul_comm, mul_div_assoc, div_self case]; field_simp

    rwa [← combo2Eq]

noncomputable def arProjX_p_q (a r : Point) : ℝ :=
  (r.y * a.x - r.x * a.y) / (r.y - a.y)

theorem arProjX_between_p_q {a p q r : Point}
    (py0 : p.y = 0) (qy0 : q.y = 0)
    (det_qar_neg : det q a r < 0) (det_par_pos : det p a r > 0)
    (ar_y_order : r.y > a.y) :
    p.x <  (arProjX_p_q a r) ∧ (arProjX_p_q a r) < q.x := by
  have order_aProjX_qX : (arProjX_p_q a r) < q.x := by
    unfold arProjX_p_q
    suffices linearized : q.x * (r.y - a.y) > r.y * a.x - r.x * a.y by
      simp at linearized
      rw [div_lt_iff']
      linarith
      linarith only [ar_y_order]
    simp [det_eq, qy0] at det_qar_neg
    linarith

  have order_aProjX_pX : p.x < (arProjX_p_q a r) := by
    unfold arProjX_p_q
    suffices linearized : p.x * (r.y - a.y) < r.y * a.x - r.x * a.y by
      rw [lt_div_iff']
      linarith
      linarith only [ar_y_order]
    simp [det_eq, py0] at det_par_pos
    linarith
  exact ⟨order_aProjX_pX, order_aProjX_qX⟩

theorem convexComboOfCollinearAndXOrdered (p q x : Point)
    (collinear : det p q x = 0) (xOrder1 : p.x < x.x) (xOrder2 : x.x < q.x) :
    ∃ (α β : ℝ), α + β = 1 ∧ α ≥ 0 ∧ β ≥ 0 ∧ α • p + β • q = x := by
  -- because they're on the same line and a is between their y coordinates
  let α := (q.x - x.x) / (q.x - p.x)
  let β := (x.x - p.x) / (q.x - p.x)
  use α, β
  have αβSum : α + β = 1 := by
    rw [div_add_div_same]
    simp
    rw [div_self]
    linarith
  use αβSum
  have α0 : α ≥ 0 := div_nonneg (by linarith) (by linarith)
  have β0 : β ≥ 0 := div_nonneg (by linarith) (by linarith)
  use α0, β0
  simp
  rw [det_eq] at collinear
  have : q.x - p.x ≠ 0 := by linarith
  ext <;> field_simp [this] <;> linarith [collinear]

theorem convexComboOfCollinearAndYOrdered (p q x : Point)
    (collinear : det p q x = 0) (yOrder1 : p.y < x.y) (yOrder2 : x.y < q.y) :
    ∃ (α β : ℝ), α + β = 1 ∧ α ≥ 0 ∧ β ≥ 0 ∧ α • p + β • q = x := by
  -- because they're on the same line and a is between their y coordinates
  let α := (q.y - x.y) / (q.y - p.y)
  let β := (x.y - p.y) / (q.y - p.y)
  use α, β
  have αβSum : α + β = 1 := by
    rw [div_add_div_same]
    simp
    rw [div_self]
    linarith
  use αβSum
  have α0 : α ≥ 0 := div_nonneg (by linarith) (by linarith)
  have β0 : β ≥ 0 := div_nonneg (by linarith) (by linarith)
  use α0, β0
  simp
  rw [det_eq] at collinear
  have : q.y - p.y ≠ 0 := by linarith
  ext <;> field_simp [this] <;> linarith [collinear]

def IsConvexCombo₂ (x p q : Point) : Prop :=
  ∃ (α β : ℝ), α + β = 1 ∧ α ≥ 0 ∧ β ≥ 0 ∧ α • p + β • q = x

def IsConvexCombo₃ (a p q r : Point) : Prop :=
  ∃ (α β γ : ℝ), α + β + γ = 1 ∧ α ≥ 0 ∧ β ≥ 0 ∧ γ ≥ 0 ∧ α • p + β • q + γ • r = a

theorem convexComboTransitive {p q r a x : Point}
    (h₁ : IsConvexCombo₂ x p q) (h₂ : IsConvexCombo₂ a x r) : IsConvexCombo₃ a p q r := by
  rcases h₁ with ⟨α₁, β₁, hαβ, hα₁, hβ₁, h_convex₁⟩
  rcases h₂ with ⟨α₂, β₂, hαβ₂, hα₂, hβ₂, h_convex₂⟩
  subst h_convex₁
  simp at h_convex₂
  unfold IsConvexCombo₃
  use α₂ • α₁, α₂ • β₁, β₂
  constructor
  · have h₁ : α₂ * (α₁ + β₁) = α₂ * 1 := congrArg (HMul.hMul α₂) hαβ
    rw [mul_one] at h₁
    conv at h₁ => rhs; rw [eq_sub_of_add_eq hαβ₂]
    replace h₁ := add_eq_of_eq_sub h₁
    simp [mul_add] at h₁
    simp [h₁]
  · simp only [smul_eq_mul, ge_iff_le]
    use smul_nonneg hα₂ hα₁, mul_nonneg hα₂ hβ₁, hβ₂
    rwa [← smul_assoc, ← smul_assoc] at h_convex₂

theorem PtInTriangle_of_σPtInTriangle {a p q r : Point}
    (spq : p.x < q.x)
    (symm : σ p q r = .ccw) (py0 : p.y = 0) (qy0 : q.y = 0) :
    σPtInTriangle a p q r → PtInTriangle a p q r := by
  unfold PtInTriangle
  intro ⟨h1, h2, h3⟩
  have det_pqr_pos : det p q r > 0 := by
    rw [σ_eq_ccw] at symm
    linarith
  have det_qpr_neg : det q p r < 0 := by
    rw [det_perm₁] at det_pqr_pos
    linarith

  have det_qar_neg : det q a r < 0 := by
    rw [← σ_eq_cw] at det_qpr_neg ⊢
    rw [σ_perm₁, h3, ← σ_perm₁]; exact det_qpr_neg

  have det_par_pos : det p a r > 0 := by
    rw [← σ_eq_ccw, h2, symm]

  let aProjXPt : Point := ![arProjX_p_q a r, 0]

  have pqa_pos : det p q a > 0 := by
    have : σ p q a = .ccw := by rw [h1]; exact symm
    rwa [σ_eq_ccw] at this
  have y_order : aProjXPt.y = 0 ∧ a.y > 0 ∧ r.y > a.y := by
    use rfl
    constructor
    . rw [det_eq, py0, qy0] at pqa_pos
      simp at pqa_pos
      nlinarith
    · simp [det_eq, py0] at det_par_pos
      simp [det_eq, qy0] at det_qar_neg
      nlinarith

  have arProjX_bet_p_q := arProjX_between_p_q py0 qy0 det_qar_neg det_par_pos y_order.2.2

  have arProjXPt_p_q_XOrdered : p.x < aProjXPt.x ∧ aProjXPt.x < q.x := arProjX_bet_p_q

  have p_q_arProjXPt_collinear : det p q aProjXPt = 0 := by
    rw [det_eq, py0, qy0]
    simp

  have aProjXPt_IsConvexCombOf_p_q :=
    convexComboOfCollinearAndXOrdered p q
      aProjXPt p_q_arProjXPt_collinear arProjXPt_p_q_XOrdered.1 arProjXPt_p_q_XOrdered.2

  have aProjX_r_a_collinear : det aProjXPt r a = 0 := by
    rw [det_eq]
    dsimp
    unfold arProjX_p_q
    have : r.y - a.y ≠ 0 := by linarith
    apply mul_right_cancel₀ (b := r.y - a.y) this
    field_simp [this]
    ring

  have a_IsConvexCombOf_aProjXPt_r :=
      convexComboOfCollinearAndYOrdered aProjXPt r a aProjX_r_a_collinear y_order.2.1 y_order.2.2

  have a_IsConvexCombOf_p_q_r :
      ∃ (α β γ : ℝ), α + β + γ = 1 ∧ α ≥ 0 ∧ β ≥ 0 ∧ γ ≥ 0 ∧ α • p + β • q + γ • r = a :=
    convexComboTransitive aProjXPt_IsConvexCombOf_p_q a_IsConvexCombOf_aProjXPt_r

  have cHullIsConvex : Convex ℝ (convexHull ℝ {p , q, r}) :=
    convex_convexHull ℝ {p , q, r}

  have sSetHull : {p, q, r} ⊆ convexHull ℝ {p , q, r} :=
    subset_convexHull ℝ {p , q, r}

  have pInChull : p ∈ convexHull ℝ {p , q, r} := by
    rw [Set.subset_def] at sSetHull
    simp at sSetHull
    exact sSetHull.1
  have qInChull : q ∈ convexHull ℝ {p , q, r} := by
    rw [Set.subset_def] at sSetHull
    simp at sSetHull
    exact sSetHull.2.1
  have rInChull : r ∈ convexHull ℝ {p , q, r} := by
    rw [Set.subset_def] at sSetHull
    simp at sSetHull
    exact sSetHull.2.2

  have ⟨α, β, γ, αβγSum, α0, β0, γNN, ccEq⟩ := a_IsConvexCombOf_p_q_r
  have c3c := convex3combo (convexHull ℝ {p, q, r}) cHullIsConvex p q r  pInChull qInChull rInChull
  have := c3c α β γ αβγSum α0 β0 γNN
  rw [ccEq] at this
  exact this

theorem σPtInTriangle_of_PtInTriangle {a p q r : Point} (gp : Point.InGeneralPosition₄ a p q r)
    (symm : σ p q r = .ccw) (h : PtInTriangle a p q r) : σ p q a = .ccw := by
  rw [← gp.gp₁.perm₁.perm₂.σ_iff', Ne, σ_eq_cw, not_lt]
  refine convexHull_min ?_ ((convex_Ici 0).affine_preimage (detAffineMap p q)) h
  simp [Set.subset_def]
  simp [← σ_ne_cw, σ_self₁, σ_self₂, symm]

theorem PtInTriangleInvariantUnderTransform {a p q r : Point} (t : Point) (θ : ℝ) :
    PtInTriangle a p q r ↔
    PtInTriangle
      (rotateTranslateMap θ t a) (rotateTranslateMap θ t p)
      (rotateTranslateMap θ t q) (rotateTranslateMap θ t r) := by
  unfold PtInTriangle
  have := AffineMap.image_convexHull {p,q,r} (rotateTranslateMap θ t)
  simp [Set.image_insert_eq] at this
  rw [← this]
  set S := convexHull ℝ {p,q,r}
  symm
  apply Function.Injective.mem_set_image
  exact injective_rotateTranslateMap θ t

theorem rotateTranslatePreserveσ (θ : ℝ) (t p q r : Point) :
    σ p q r =
    σ (rotateTranslateMap θ t p) (rotateTranslateMap θ t q) (rotateTranslateMap θ t r) := by
  rw [rotateTranslateTransform]
  rw [rotateTranslateTransform]
  rw [rotateTranslateTransform]
  set T := (translationMatrix (Point.x t) (Point.y t) * Matrix.rotateByAffine θ)
  have : TMatrix T := by exact rotateTranslateTMatrix θ t
  symm
  apply TMatrix.ptTransform_preserves_sigma p q r this

theorem σPtInTriangleInvariantUnderTransform {a p q r : Point}  (t : Point) (θ : ℝ) :
    σPtInTriangle a p q r ↔
    σPtInTriangle
      (rotateTranslateMap θ t a) (rotateTranslateMap θ t p)
      (rotateTranslateMap θ t q) (rotateTranslateMap θ t r) := by
  simp only [σPtInTriangle, ← rotateTranslatePreserveσ]

theorem extraPiDoesntChange0y (θ : ℝ)  (p : Point) :
    (rotationMap θ p).y = 0 ↔ (rotationMap (θ + Real.pi) p).y = 0 := by
  constructor <;> intro h <;> simp at * <;> linarith

lemma translate_to_0_change (p t : Point) : (translateMap t p).y = 0 ↔ p.y + t.y = 0 := by
  rw [translateMap_apply]
  simp
  constructor <;> intro h <;> linarith

theorem extraPiDoesntChange0y' (θ : ℝ)  (p : Point) :
    (rotateTranslateMap θ ![0, -(rotationMap θ p).y] p).y = 0 ↔
    ((rotateTranslateMap (θ + Real.pi) ![0, -(rotationMap (θ + Real.pi) p).y]) p).y = 0 := by
  constructor <;>
  · unfold rotateTranslateMap
    intro h
    simp at *
    rw [translate_to_0_change] at h
    rw [translate_to_0_change]
    simp
    simp at h
    linarith

theorem existsNiceRotTrans {p q : Point} (diff : p ≠ q) : ∃ (θ : ℝ) (t : Point),
      (rotateTranslateMap θ t p).y = 0
    ∧ (rotateTranslateMap θ t q).y = 0
    ∧ (rotateTranslateMap θ t p).x < (rotateTranslateMap θ t q).x := by
  by_cases same_x : p.x = q.x
  · by_cases p_above_q : p.y > q.y
    · use Real.pi/2
      let p' := rotationMap (Real.pi/2) p
      let q' := rotationMap (Real.pi/2) q
      use ![0, -p'.y]
      constructor
      . unfold rotateTranslateMap
        simp
        rw [translateMap_apply]
        simp

      . constructor
        . have same_y' : p'.y = q'.y := by simp; assumption
          rw [same_y']
          unfold rotateTranslateMap
          simp
          rw [translateMap_apply]
          simp
        . unfold rotateTranslateMap
          simp
          rw [translateMap_apply]
          rw [translateMap_apply]
          simp
          ring_nf
          linarith
    · have p_below_q : p.y < q.y := by
        by_contra C
        have same_y : p.y = q.y := le_antisymm (le_of_not_gt p_above_q) (le_of_not_gt C)
        refine diff.elim ?_
        ext <;> assumption

      use -(Real.pi/2)
      let p' := rotationMap (-(Real.pi/2)) p
      let q' := rotationMap (-(Real.pi/2)) q
      use ![0, -p'.y]
      constructor
      . unfold rotateTranslateMap
        simp
        rw [translateMap_apply]
        simp
      . constructor
        . have same_y' : p'.y = q'.y := by simp; assumption
          rw [same_y']
          unfold rotateTranslateMap
          simp
          rw [translateMap_apply]
          simp
        . unfold rotateTranslateMap
          simp
          rw [translateMap_apply]
          rw [translateMap_apply]
          simp
          ring_nf
          linarith
  · obtain ⟨S, eq⟩ : ∃ x, x = (q.y - p.y) / (q.x - p.x) := ⟨_, rfl⟩
    let θ := -Real.arctan (S)
    let p' := rotationMap θ p
    let t := ![0, -p'.y]

    have rpy0 : (rotateTranslateMap θ t p).y = 0 := by
      unfold rotateTranslateMap
      simp
      rw [translateMap_apply]
      simp
      ring_nf

    have rqy0 : (rotateTranslateMap θ t q).y = 0 := by
      unfold rotateTranslateMap
      simp
      rw [translateMap_apply]
      simp
      rw [Real.sin_arctan]
      rw [Real.cos_arctan]
      open Real in
      calc -(1 / sqrt (1 + S ^ 2) * p.y) + S / sqrt (1 + S ^ 2) * p.x
          + (-(S / sqrt (1 + S ^ 2) * q.x) + 1 / sqrt (1 + S ^ 2) * q.y)
        _ = (1 / sqrt (1 + S ^ 2))*(-p.y + q.y) + S / sqrt (1 + S ^ 2) * p.x
          + (-(S / sqrt (1 + S ^ 2) * q.x)) := by ring_nf
        _ = (1 / sqrt (1 + S ^ 2))*(-p.y + q.y)
          + (S / sqrt (1 + S ^ 2) * (p.x - q.x)) := by ring_nf
        _ = ((q.y - p.y) - (S* (q.x - p.x))) / sqrt (1 + S ^ 2) := by ring_nf
        _ = ((q.y - p.y) - ((q.y - p.y) / (q.x - p.x) * (q.x - p.x))) /
            sqrt (1 + ((q.y - p.y) / (q.x - p.x) ) ^ 2) := by rw [eq]
        _ = 0 := by
          field_simp [(sub_ne_zero.2 same_x)]
          rw [@mul_div_cancel _ _ _ _ (sub_ne_zero.2 (Ne.symm same_x))]; simp

    have post_neq : (rotateTranslateMap θ t p).x ≠ (rotateTranslateMap θ t q).x := by
      have prev :  (rotateTranslateMap θ t p).y = (rotateTranslateMap θ t q).y := by linarith
      have injc :  (rotateTranslateMap θ t p) ≠ (rotateTranslateMap θ t q) := by
        intro pq
        apply diff
        apply injective_rotateTranslateMap _ _ pq
      intro pxqx
      apply injc (Point.ext pxqx prev)

    by_cases post_lt : (rotateTranslateMap θ t p).x < (rotateTranslateMap θ t q).x
    · use θ, t
    · rw [not_lt] at post_lt
      have : (rotateTranslateMap θ t q).x < (rotateTranslateMap θ t p).x :=
        lt_of_le_of_ne post_lt post_neq.symm
      let θ' := θ + Real.pi
      let p'' := rotationMap θ' p

      let t'' := ![0, -p''.y]
      use θ', t''
      have g1 : (rotateTranslateMap θ' t'' p).y = 0 := by
        unfold rotateTranslateMap
        simp
        rw [translateMap_apply]
        simp
        ring_nf
      have g2 : (rotateTranslateMap θ' t'' q).y = 0 := by
        unfold rotateTranslateMap
        simp
        rw [translateMap_apply]
        simp
        rw [Real.sin_arctan, Real.cos_arctan]
        field_simp
        calc p.y + -(S * p.x) + (S * q.x + -q.y)
          _ = p.y + -S * p.x + S * q.x + -q.y := by ring_nf
          _ = p.y + S * (q.x - p.x) + -q.y := by ring_nf
          _ = (p.y - q.y) + S * (q.x - p.x) := by ring_nf
          _ = (p.y - q.y) + ((q.y - p.y) / (q.x - p.x)) * (q.x - p.x) := by rw [eq]
          _ = 0 := by
            field_simp [sub_ne_zero.2 same_x]
            rw [@mul_div_cancel _ _ _ _ (sub_ne_zero.2 (Ne.symm same_x))]; simp
      have g3 : (rotateTranslateMap θ' t'' p).x < (rotateTranslateMap θ' t'' q).x := by
        unfold rotateTranslateMap
        simp
        rw [translateMap_apply, translateMap_apply]
        simp
        unfold rotateTranslateMap at this
        simp at this
        rw [translateMap_apply, translateMap_apply] at this
        simp at this
        nlinarith
      exact ⟨g1, g2, g3⟩

theorem PtInTriangle_of_σPtInTriangle' {a p q r : Point} (gp : Point.InGeneralPosition₄ a p q r)
    (symm : σ p q r = .ccw) :
    σPtInTriangle a p q r → PtInTriangle a p q r  := by
  intro h
  have p_neq_q : p ≠ q := by
    have l := gp.4
    unfold Point.InGeneralPosition₃ at l
    rw [Point.det_eq] at l
    by_contra C
    simp [C] at l
    ring_nf at l
    tauto

  have ⟨θ, t, h1, h2, h3⟩ := existsNiceRotTrans p_neq_q
  set p' := rotateTranslateMap θ t p
  set q' := rotateTranslateMap θ t q
  set r' := rotateTranslateMap θ t r
  set a' := rotateTranslateMap θ t a
  have a'inTri : σPtInTriangle a' p' q' r' := by
    rw [← σPtInTriangleInvariantUnderTransform]
    exact h
  have symm' : σ p' q' r' = .ccw := by
    rw [← rotateTranslatePreserveσ]
    exact symm
  have := PtInTriangle_of_σPtInTriangle h3 symm' h1 h2 a'inTri
  rw [← PtInTriangleInvariantUnderTransform] at this
  exact this

theorem σPtInTriangle_iff_of_CCW {a p q r : Point} (gp : Point.InGeneralPosition₄ a p q r)
    (symm : σ p q r = .ccw) :
    σPtInTriangle a p q r ↔ PtInTriangle a p q r := by
  constructor
  · exact PtInTriangle_of_σPtInTriangle' gp symm
  · refine fun H => ⟨?_, ?_, ?_⟩ <;> rw [symm]
    · exact σPtInTriangle_of_PtInTriangle gp symm H
    · rw [σ_perm₂, ← σ_perm₁, σPtInTriangle_of_PtInTriangle
        gp.perm₃.perm₂ (by rw [σ_perm₁, ← σ_perm₂, symm]) H.perm₂.perm₁]
    · rw [σ_perm₁, ← σ_perm₂, σPtInTriangle_of_PtInTriangle
        gp.perm₂.perm₃ (by rw [σ_perm₂, ← σ_perm₁, symm]) H.perm₁.perm₂]

theorem σPtInTriangle_iff {a p q r : Point} (gp : Point.InGeneralPosition₄ a p q r) :
    σPtInTriangle a p q r ↔ PtInTriangle a p q r := by
  rcases gp.gp₄.σ_cases with h | h
  . exact σPtInTriangle_iff_of_CCW gp h
  . have hccw : σ p r q = .ccw := by rw [σ_perm₂, h]; rfl
    have : InGeneralPosition₄ a p r q := ⟨gp.gp₂, gp.gp₁, gp.gp₃.perm₂, gp.gp₄.perm₂⟩
    have := σPtInTriangle_iff_of_CCW this hccw
    exact ⟨
      fun h => PtInTriangle.perm₂ (this.mp (σPtInTriangle.perm₂ h)),
      fun h => σPtInTriangle.perm₂ (this.mpr (PtInTriangle.perm₂ h))⟩
