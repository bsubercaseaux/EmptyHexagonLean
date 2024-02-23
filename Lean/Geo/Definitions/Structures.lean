import Geo.Definitions.Point
import Geo.Definitions.PtInTriangle

/-! Definitions of geometric structures that we will prove must exist. -/

namespace Geo

/-- `EmptyShapeIn S P` means that `S` carves out an empty shape in `P`:
the convex hull of `S` contains no point of `P`
other than those already in `S`. -/
def EmptyShapeIn (S P : Set Point) : Prop :=
  ∀ p ∈ P \ S, p ∉ convexHull ℝ S

/-- `ConvexPoints S` means that `S` consists of extremal points of its convex hull,
i.e. the point set encloses a convex polygon. -/
def ConvexPoints (S : Set Point) : Prop :=
  ∀ a ∈ S, a ∉ convexHull ℝ (S \ {a})

def ConvexEmptyIn (S P : Set Point) : Prop :=
  ConvexPoints S ∧ EmptyShapeIn S P

theorem ConvexEmptyIn.antitone_left {S₁ S₂ P : Set Point} :
    S₁ ⊆ S₂ → ConvexEmptyIn S₂ P → ConvexEmptyIn S₁ P := by
  intro S₁S₂ ⟨convex, empty⟩
  constructor
  . intro a aS₁ aCH
    have : S₁ \ {a} ⊆ S₂ \ {a} := Set.diff_subset_diff S₁S₂ (le_refl _)
    apply convex a (S₁S₂ aS₁) (convexHull_mono this aCH)
  . intro p pPS₁ pCH
    have : p ∈ convexHull ℝ S₂ := convexHull_mono S₁S₂ pCH
    refine empty p ?_ this
    rw [Set.mem_diff] at pPS₁ ⊢
    refine ⟨pPS₁.left, ?_⟩
    intro pS₂
    have : S₁ ⊆ S₂ \ {p} := fun x xS₁ => by
      rw [Set.mem_diff, Set.mem_singleton_iff]
      refine ⟨S₁S₂ xS₁, fun xp => ?_⟩
      rw [xp] at xS₁
      exact pPS₁.right xS₁
    have : p ∈ convexHull ℝ (S₂ \ {p}) := convexHull_mono this pCH
    exact convex p pS₂ this

theorem ConvexEmptyIn.iff {S P : Set Point} :
    S ⊆ P →
    (ConvexEmptyIn S P ↔ ∀ S' ⊆ S, EmptyShapeIn S' P) := by
  intro SP
  constructor
  . intro ce _ S'S
    exact ce.antitone_left S'S |>.right
  . intro allempty
    refine ⟨?_, allempty S le_rfl⟩
    intro a aS aCH
    apply allempty (S \ {a}) (Set.diff_subset ..) a (by simp [SP aS]) aCH

theorem ConvexEmptyIn.iff_triangles {s : Finset Point} {S : Set Point} :
    ConvexEmptyIn s S ↔ ∀ (t : Finset Point), t.card = 3 → t ⊆ s → ConvexEmptyIn t S := by
  constructor
  . intro ce _ _ ts
    apply ce.antitone_left ts
  . sorry -- harder, needs triangulation?

def HasEmptyNGon (n : Nat) (S : Set Point) : Prop :=
  ∃ s : Finset Point, s.card = n ∧ ↑s ⊆ S ∧ ConvexEmptyIn s S

def HasEmptyTriangle : Set Point → Prop := HasEmptyNGon 3

open Classical
theorem HasEmptyTriangle.iff (S : Set Point) :
    HasEmptyTriangle S ↔
    ∃ᵉ (a ∈ S) (b ∈ S) (c ∈ S), Point.InGeneralPosition₃ a b c ∧
      ∀ s ∈ S \ {a,b,c}, ¬PtInTriangle s a b c := by
  simp [HasEmptyTriangle, HasEmptyNGon, PtInTriangle]
  constructor
  · intro ⟨s, h1, h2, h3, h4⟩
    match s, s.exists_mk, h1 with | _, ⟨[a,b,c], h1, rfl⟩, _ => ?_
    have s_eq : (Finset.mk (Multiset.ofList [a,b,c]) h1 : Set _) = {a, b, c} := by ext; simp
    simp [not_or, Set.subset_def] at h1 h2 h3 ⊢
    refine ⟨a, h2.1, b, h2.2.1, c, h2.2.2, ?_, ?_⟩
    · refine Point.InGeneralPosition₃.iff_not_mem_seg.2 ⟨?_, ?_, ?_⟩ <;>
        refine (h3 _ (by simp) <| convexHull_mono ?_ ·) <;> simp [Set.subset_def]
      · exact ⟨Ne.symm h1.1.1, Ne.symm h1.1.2⟩
      · exact ⟨h1.1.1, Ne.symm h1.2⟩
      · exact ⟨h1.1.2, h1.2⟩
    · simpa [not_or, EmptyShapeIn, s_eq] using h4
  · intro ⟨a, ha, b, hb, c, hc, h1, h2⟩
    let s : Finset Point := ⟨[a,b,c], by simp [h1.ne₁, h1.ne₂, h1.ne₃]⟩
    have s_eq : s = {a,b,c} := by ext; simp
    refine ⟨s, rfl, ?_, ?_, ?_⟩
    · simp [Set.subset_def, ha, hb, hc]
    · simp [s_eq]; intro p hp hp2; simp at hp
      rw [Point.InGeneralPosition₃.iff_not_mem_seg] at h1
      obtain h|h|h := hp <;> subst p
      · exact h1.1 (convexHull_mono (by simp) hp2)
      · exact h1.2.1 (convexHull_mono (by simp [Set.subset_def]) hp2)
      · exact h1.2.2 (convexHull_mono (by simp [Set.subset_def]) hp2)
    · simpa [s_eq, EmptyShapeIn] using h2

def HasEmptyHexagon : Set Point → Prop := HasEmptyNGon 6

def σIsEmptyTriangleFor (a b c : Point) (S : Set Point) : Prop :=
  ∀ s ∈ S, ¬σPtInTriangle s a b c

def σHasEmptyTriangle (S : Set Point) : Prop :=
  ∃ᵉ (a ∈ S) (b ∈ S) (c ∈ S),
    a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ σIsEmptyTriangleFor a b c S
