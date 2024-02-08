import Mathlib.Data.List.Sort
import Geo.PlaneGeometry
import Geo.SymmetryBreaking
import Geo.Slope
import Geo.Point

namespace Geo
noncomputable section
open Classical
open Orientation

-- structure Triangle (S: Finset Point) : Prop :=
--   --
--   triangle: S.card = 3
--   triangle_list : S.toList.length = 3
--   no_three_collinear: σ (S.toList.get ⟨0, by linarith⟩) (S.toList.get ⟨1, by linarith⟩) (S.toList.get ⟨2, by linarith⟩) ≠ Orientation.Collinear

-- NB: should probably prove that this is equiv. to the defn in terms of convex combinations
-- NB: This is for points *strictly* in the triangle
def pt_in_triangle (a : Point) (p q r : Point) : Prop :=
  ∃ p' q' r', ({p', q', r'} : Set Point) = {p, q, r} ∧
    IsSortedPoints₃ p' q' r' ∧
    IsSortedPoints₃ p' a r' ∧
    a ≠ q' ∧ -- this isn't needed if p,q,r are in GP
    σ p' q' r' = σ p' a r' ∧
    σ p' a q' = σ p' r' q' ∧
    σ q' a r' = σ q' p' r'

/-- S is an empty triangle relative to pts -/
structure EmptyTriangleIn (p q r : Point) (pts : Finset Point) : Prop :=
  gp : GeneralPosition₃ p q r
  empty: ∀ a ∈ pts, ¬(pt_in_triangle a p q r)


structure validTriple (n : Nat) :=
  (i j k : Fin n)
  (ordered: i < j ∧ j < k)

structure σ_assignment (n : Nat) :=
  (σ_a : validTriple n → Orientation)

  def get_σ_assignment (pts : Finset Point) :
    σ_assignment (pts.card):=
    let sorted_pts : List Point := finset_sort pts

  ⟨λ t => σ (sorted_pts.get ⟨t.i, by
                                 {have hi : t.i < (List.length sorted_pts) := by
                                       {have fi: t.i < (Finset.card pts) := by {
                                          have h := t.i.2;
                                          exact h}
                                        have same_length: (List.length sorted_pts) = (Finset.card pts) := by
                                          {rw [finset_sort_length_eq]};
                                        linarith
                                       }
                                  exact hi}⟩)
            (sorted_pts.get ⟨t.j, by
                                 {have hj : t.j < (List.length sorted_pts) := by
                                    {
                                      have hj: t.j < (Finset.card pts) := by {
                                        have h := t.j.2;
                                        exact h}
                                      have same_length: (List.length sorted_pts) = (Finset.card pts) := by
                                        {rw [finset_sort_length_eq]};
                                      linarith
                                    }
                                  exact hj}⟩)

          (sorted_pts.get ⟨t.k, by
                                 {have hk : t.k < (List.length sorted_pts) := by
                                    {
                                      have hk: t.k < (Finset.card pts) := by {
                                        have h := t.k.2;
                                        exact h}
                                      have same_length: (List.length sorted_pts) = (Finset.card pts) := by
                                        {rw [finset_sort_length_eq]};
                                      linarith
                                    }
                                  exact hk}⟩)⟩

def σ_get_L (l : List Point) (t : validTriple l.length)
    : Orientation :=
  let σ_a :=  get_σ_assignment (l.toFinset)
  have eq_length : l.length = (l.toFinset).card := by
    sorry
  let nt : validTriple (l.toFinset).card := ⟨⟨t.i.val, by
    {
     have : ↑t.i < (List.length l) := by
      exact t.i.2

     simp_rw [eq_length] at this;
     exact this
    }⟩,
    ⟨t.j.val, by
    {
     have : ↑t.j < (List.length l) := by
      exact t.j.2

     simp_rw [eq_length] at this;
     exact this
    }⟩,
    ⟨t.k.val, by
    {
     have : ↑t.k < (List.length l) := by
      exact t.k.2

     simp_rw [eq_length] at this;
     exact this
    }⟩, t.ordered⟩
  σ_a.σ_a nt

inductive σ_property_L :  Prop
| base : (σ_get_L l valid_triple = Orientation.CCW) → σ_property_L
-- | base2 : (σ_get_L l valid_triple = Orientation.CW) → σ_property_L
| and : σ_property_L → σ_property_L → σ_property_L
| or : σ_property_L → σ_property_L → σ_property_L
| not : σ_property_L → σ_property_L
-- | exists : σ_property_L → σ_property_L -- ? rethink?

def σ_get_A (assignment : σ_assignment n) (t : validTriple n) : Orientation :=
  assignment.σ_a t

inductive σ_property_A (assignment : σ_assignment n) :  Prop
| base : (σ_get_A assignment valid_triple = Orientation.CCW) → σ_property_A assignment
-- | base2 : (σ_get_A assignment valid_triple = Orientation.CW) → σ_property_A
| and : σ_property_A assignment → σ_property_A assignment → σ_property_A assignment
| or : σ_property_A assignment → σ_property_A assignment → σ_property_A assignment
| not : σ_property_A assignment → σ_property_A assignment
-- | exists : σ_property_A → σ_property_A

def eval_σ_property_from_σ_assignment
    (assignment : σ_assignment n) (property : σ_property_A assignment)
    : Prop :=
    sorry

def eval_σ_property_from_pt_list (pts : List Point)
    (property: σ_property_L) : Prop :=
    sorry

def get_σ_property_A_from_L (property: σ_property_L) :
  σ_property_A :=
  sorry

theorem σ_property_equiv (pts: Finset Point) (property: σ_property_L):
  eval_σ_property_from_pt_list (finset_sort pts) property ↔
  eval_σ_property_from_σ_assignment (get_σ_assignment pts) (get_σ_property_A_from_L property):=
  by sorry


theorem existential_implication (property: σ_property_L):
    ∃ (pts: Finset Point), eval_σ_property_from_pt_list (finset_sort pts) property →
    ∃ (assignment : σ_assignment pts.card),
      eval_σ_property_from_σ_assignment assignment (get_σ_property_A_from_L property) :=
  by sorry

theorem existential_assignment_to_cnf (property: σ_property_A):
∃ (assignment : σ_assignment pts.card),
      eval_σ_property_from_σ_assignment assignment property
    -> Satisfiable (CNF_from_property_A property) :=
    sorry

---- Imagine we want to prove that no finset F of 5 points satisfies the following:
--- let L = finset_sort F
--- P (L of size 5) → Prop := σ (L.get 0) (L.get 1) (L.get 2) = Orientation.CCW
--- and σ (L.get 0) (L.get 1) (L.get 2) = Orientation.CW


--- A_P (σ_A 5) →  Prop := (σ_A 0 1 2) = Orientation.CCW
--- and (σ_A 0 1 2) = Orientation.CW

--- The space of (σ_A 5) is finite.
---- None of the σ_A 5 satisfy A_P.

--- There's φ_AP :  (p 0 1 2) ⊓ (p 0 1 2)ᶜ ⊓ (p 0 1 3 ⇒ p 0 1 4)
---- ::= ¬ ∃ τ, τ ⊨ φ_AP
      ---> ¬ ∃ σ_A 5, σ_A 5 ⊨_A A_P
          ---> ¬ ∃ L 5, L 5 ⊨_L P

  --- P : σ_L_property
  ---- A_P : σ_A_property := get_σ_property_A_from_L P
  ----  Theorem: L ⊧_L P → get_σ_assignment L ⊧_A A_P
  ------ Theorem: ¬∃ σ_assignment, σ_assignment ⊧_A A_P → ¬∃ L, L ⊧_L P

----- If no σ_A satisfies A_P, then

-- there will be some φ : PropFun ? s.t.
-- if eval_σ_property_from_pt_list (finset_sort pts) property
-- then ∃ (τ : PropAssignment ?), τ ⊨ φ

-- theorem points_to_orientations (l : List Point) :
--   ∃ (σ_p : List Orientation),


---
-- def ptSet_to_σ_assignment (P: Finset Point) :
--   σ_assignment P :=
--   ---


theorem EmptyTriangle10TheoremLists (pts : List Point)
    (gp : GeneralPositionList pts)
    (h : pts.length = 10) :
    ∃ (p q r : Point), List.Sublist [p, q, r] pts ∧ EmptyTriangleIn p q r pts := by
  sorry

theorem EmptyTriangle10Theorem (pts : Finset Point)
    (gp : GeneralPosition pts)
    (h : pts.card = 10) :
    ∃ (p q r : Point), {p, q, r} ⊆ pts ∧ EmptyTriangleIn p q r pts := by
  sorry

example (P Q R S : Prop) : (P ↔ Q) → (R ↔ S) → ((P ∧ R) ↔ (Q ∧ S)) := by
  tauto
