import Geo.Definitions.Point
import Geo.Definitions.PtInTriangle

/-! Definitions of geometric structures that we will prove must exist. -/

namespace Geo

/-- `IsEmptyShapeIn S P` means that `S` carves out an empty shape in `P`:
the convex hull of `S` contains no point of `P`
other than those already in `S`. -/
def IsEmptyShapeIn (S P : Set Point) : Prop :=
  ∀ p ∈ P \ S, p ∉ convexHull ℝ S

/-- `ConvexPoints S` means that `S` consists of extremal points of its convex hull,
i.e. the point set encloses a convex polygon. -/
def ConvexPoints (S : Set Point) : Prop :=
  ∀ a ∈ S, a ∉ convexHull ℝ (S \ {a})

def HasEmptyNGon (n : Nat) (S : Set Point) : Prop :=
  ∃ s : Finset Point, s.card = n ∧ ↑s ⊆ S ∧ ConvexPoints s ∧ IsEmptyShapeIn s S

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
    · simpa [not_or, IsEmptyShapeIn, s_eq] using h4
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
    · simpa [s_eq, IsEmptyShapeIn] using h2

def HasEmptyHexagon : Set Point → Prop := HasEmptyNGon 6

def σIsEmptyTriangleFor (a b c : Point) (S : Set Point) : Prop :=
  ∀ s ∈ S, ¬σPtInTriangle s a b c

def σHasEmptyTriangle (S : Set Point) : Prop :=
  ∃ᵉ (a ∈ S) (b ∈ S) (c ∈ S),
    a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ σIsEmptyTriangleFor a b c S
