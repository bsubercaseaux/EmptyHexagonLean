import Geo.Definitions.Point
import Geo.Definitions.CanonicalPoints
import Geo.Orientations
import Geo.Canonicalization.TMatrix
import Geo.Canonicalization.Affine

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

theorem σPtInTriangle_of_PtInTriangle {a p q r : Point} (gp : Point.InGeneralPosition₄ a p q r)
    (symm : σ p q r = .ccw) (h : PtInTriangle a p q r) : σ p q a = .ccw := by
  rw [← gp.gp₁.perm₁.perm₂.σ_iff', Ne, σ_eq_cw, not_lt]
  refine convexHull_min ?_ ((convex_Ici 0).affine_preimage (detAffineMap p q)) h
  simp [Set.subset_def]
  simp [← σ_ne_cw, σ_self₁, σ_self₂, symm]

theorem PtInTriangle_of_σPtInTriangle {a p q r : Point}
    (symm : σ p q r = .ccw) (H : σPtInTriangle a p q r) : PtInTriangle a p q r := by
  simp [σPtInTriangle, symm, PtInTriangle] at H ⊢; simp [σ_eq_ccw] at H symm
  have := linear_combination_mem_convexHull
    (s := Finset.univ) (v := ![r, q, p])
    (w := ![det p q a / det p q r, det p a r / det p q r, det a q r / det p q r])
  simp [Fin.forall_fin_succ, le_of_lt, div_pos, H, symm, Finset.sum_fin_eq_sum_range,
    Finset.sum_range_succ, ← add_div] at this
  convert ← this ?_ using 1
  · rw [← smul_right_inj (ne_of_gt symm)]; simp [smul_smul, mul_div_cancel' _ (ne_of_gt symm)]
    ext <;> simp [det_eq, x, y] <;> ring
  · rw [det_add_det, det_perm₁ a, add_neg_cancel_right, div_self (ne_of_gt symm)]

theorem σPtInTriangle_iff_of_CCW {a p q r : Point} (gp : Point.InGeneralPosition₄ a p q r)
    (symm : σ p q r = .ccw) :
    σPtInTriangle a p q r ↔ PtInTriangle a p q r := by
  constructor
  · exact PtInTriangle_of_σPtInTriangle symm
  · refine fun H => ⟨?_, ?_, ?_⟩ <;> rw [symm]
    · exact σPtInTriangle_of_PtInTriangle gp symm H
    · rw [σ_perm₂, ← σ_perm₁, σPtInTriangle_of_PtInTriangle
        gp.perm₃.perm₂ (by rw [σ_perm₁, ← σ_perm₂, symm]) H.perm₂.perm₁]
    · rw [σ_perm₁, ← σ_perm₂, σPtInTriangle_of_PtInTriangle
        gp.perm₂.perm₃ (by rw [σ_perm₂, ← σ_perm₁, symm]) H.perm₁.perm₂]

theorem σPtInTriangle_iff {a p q r : Point} (gp : Point.InGeneralPosition₄ a p q r) :
    σPtInTriangle a p q r ↔ PtInTriangle a p q r := by
  rcases gp.gp₄.σ_cases with h | h
  · exact σPtInTriangle_iff_of_CCW gp h
  · have : InGeneralPosition₄ a p r q := ⟨gp.gp₂, gp.gp₁, gp.gp₃.perm₂, gp.gp₄.perm₂⟩
    have := σPtInTriangle_iff_of_CCW this (by rw [σ_perm₂, h]; rfl)
    exact ⟨(this.1 ·.perm₂ |>.perm₂), (this.2 ·.perm₂ |>.perm₂)⟩
