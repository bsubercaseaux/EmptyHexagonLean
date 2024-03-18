import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Algebra.Basic
import Geo.Definitions.Orientations
import Geo.ToMathlib
import Geo.Canonicalization.TMatrix

namespace Geo

noncomputable def projectiveMap : Point → Point := fun pt =>
  ![pt.y / pt.x, 1 / pt.x]

noncomputable def orientWithInfty (p1 p2 : Point) :=
  Orientation.ofReal (p2.x - p1.x)

theorem orientWithInfty_swap : -orientWithInfty p1 p2 = orientWithInfty p2 p1 := by
  simp [orientWithInfty, ← Orientation.ofReal_neg]

theorem orientWithInfty_preserved {p1 p2 : Point} (h1 : p1.x > 0) (h2 : p2.x > 0) :
    σ 0 p1 p2 = orientWithInfty (projectiveMap p1) (projectiveMap p2) := by
  simp [projectiveMap, σ, orientWithInfty, Point.det_eq]
  convert Orientation.ofReal_mul_left _ _ (mul_pos h1 h2) using 2
  field_simp; ring

theorem orientations_preserved {p1 p2 p3 : Point} (h1 : p1.x > 0) (h2 : p2.x > 0) (h3 : p3.x > 0) :
    σ p1 p2 p3 = σ (projectiveMap p1) (projectiveMap p2) (projectiveMap p3) := by
  simp [projectiveMap, σ, Point.det_eq]
  convert Orientation.ofReal_mul_left _ _ (mul_pos h1 <| mul_pos h2 h3) using 2
  field_simp; ring

theorem exists_pt_st_orientations_preserved (pts : List Point) (hsort : pts.Sorted (·.x < ·.x)) :
    ∃ z : Point,
      (∀ p ∈ pts, z.x < p.x) ∧
      (∀ p1 ∈ pts, ∀ p2 ∈ pts, orientWithInfty p1 p2 = σ z p1 p2) := by
  obtain ⟨a, ha⟩ : ∃ a, ∀ x ∈ pts, a < x.x := exists_lt_list pts (·.x)
  obtain ⟨b, hb⟩ : ∃ b,
    ∀ x ∈ (do
      let p1 ← pts; let p2 ← pts
      pure <| -(a * p1.y + p1.x * p2.y - p1.y * p2.x - p2.y * a) / (p2.x - p1.x)), x < b :=
    exists_gt_list _ id
  refine ⟨![a, b], ha, ?_⟩
  intro p1 h1 p2 h2
  wlog h : p1.x < p2.x generalizing p1 p2
  · rcases lt_or_eq_of_le (not_lt.1 h) with h | h
    · rw [← orientWithInfty_swap, σ_perm₂, this _ h2 _ h1 h]
    · by_cases eq : p1 = p2
      · subst eq
        simp [orientWithInfty, σ, Point.det_eq]; ring_nf
      · have : IsIrrefl Point (·.x < ·.x) := ⟨fun _ => lt_irrefl _⟩
        have := hsort.imp (S := fun a b : Point => a.x ≠ b.x) ne_of_lt
        cases this.forall (fun _ _ => Ne.symm) h1 h2 eq h.symm
  simp [σ, orientWithInfty, Point.det_eq]
  simp at hb
  have := hb _ _ h1 _ h2 rfl
  unfold Orientation.ofReal
  rw [if_pos, if_pos] <;> simp [h]
  rw [div_lt_iff (sub_pos_of_lt h)] at this
  rw [← sub_pos] at this ⊢
  convert this using 1; ring
