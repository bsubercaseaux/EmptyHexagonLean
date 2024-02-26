import Mathlib.Analysis.Convex.Caratheodory
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

open Classical
theorem ConvexPoints.triangle_iff {a b c : Point} {h : [a, b, c].Nodup} :
    ConvexPoints (Finset.mk (α := Point) [a,b,c] h) ↔ Point.InGeneralPosition₃ a b c := by
  constructor <;> intro h2
  · simp [not_or, Set.subset_def] at h ⊢
    refine Point.InGeneralPosition₃.iff_not_mem_seg.2 ⟨?_, ?_, ?_⟩ <;>
      refine (h2 _ (by simp) <| convexHull_mono ?_ ·) <;> simp [Set.subset_def]
    · exact ⟨Ne.symm h.1.1, Ne.symm h.1.2⟩
    · exact ⟨h.1.1, Ne.symm h.2⟩
    · exact ⟨h.1.2, h.2⟩
  · have s_eq : Finset.mk (α := Point) [a,b,c] h = {a,b,c} := by ext; simp
    simp [s_eq]; intro p hp hp2; simp at hp
    rw [Point.InGeneralPosition₃.iff_not_mem_seg] at h2
    obtain h|h|h := hp <;> subst p
    · exact h2.1 (convexHull_mono (by simp) hp2)
    · exact h2.2.1 (convexHull_mono (by simp [Set.subset_def]) hp2)
    · exact h2.2.2 (convexHull_mono (by simp [Set.subset_def]) hp2)

theorem ConvexPoints.lt_3 {s : Finset Point} (hs : s.card < 3) : ConvexPoints s := by
  intro a ha hn
  rw [← Finset.coe_erase] at hn
  have := Nat.le_of_lt_succ <| (Finset.card_erase_lt_of_mem ha).trans_le (Nat.le_of_lt_succ hs)
  generalize e1 : s.erase a = s' at *
  match s'.exists_mk, this with
  | ⟨[], _, (eq : s' = ∅)⟩, _ => subst eq; simp at hn
  | ⟨[b], h1, (eq : s' = {b})⟩, _ =>
    subst eq; simp at hn; subst b
    simpa using congrArg (a ∈ ·) e1

theorem ConvexPoints.triangle' {s : Finset Point} {S : List Point}
    (hs : s.card ≤ 3) (sS : s ⊆ S.toFinset) (gp : Point.PointListInGeneralPosition S) :
    ConvexPoints s := by
  cases lt_or_eq_of_le hs with
  | inl hs => exact ConvexPoints.lt_3 hs
  | inr hs =>
    match s, s.exists_mk with | _, ⟨[a,b,c], h1, rfl⟩ => ?_
    rw [ConvexPoints.triangle_iff]
    apply Point.PointListInGeneralPosition.subperm.1 gp
    exact List.subperm_of_subset h1 (by simpa [Finset.subset_iff] using sS)

theorem ConvexPoints.antitone_left {S₁ S₂ : Set Point} (S₁S₂ : S₁ ⊆ S₂)
    (convex : ConvexPoints S₂) : ConvexPoints S₁ := by
  intro a aS₁ aCH
  have : S₁ \ {a} ⊆ S₂ \ {a} := Set.diff_subset_diff S₁S₂ (le_refl _)
  apply convex a (S₁S₂ aS₁) (convexHull_mono this aCH)

def ConvexEmptyIn (S P : Set Point) : Prop :=
  ConvexPoints S ∧ EmptyShapeIn S P

theorem ConvexEmptyIn.antitone_left {S₁ S₂ P : Set Point} (S₁S₂ : S₁ ⊆ S₂) :
    ConvexEmptyIn S₂ P → ConvexEmptyIn S₁ P := by
  refine fun ⟨convex, empty⟩ => ⟨convex.antitone_left S₁S₂, fun p pPS₁ pCH => ?_⟩
  refine empty p ⟨pPS₁.left, ?_⟩ (convexHull_mono S₁S₂ pCH)
  refine fun pS₂ => convex p pS₂ (convexHull_mono ?_ pCH)
  exact fun x xS₁ => ⟨S₁S₂ xS₁, fun xp => pPS₁.right (xp ▸ xS₁)⟩

theorem ConvexEmptyIn.iff {S P : Set Point} (SP : S ⊆ P) :
    ConvexEmptyIn S P ↔ ∀ S' ⊆ S, EmptyShapeIn S' P := by
  constructor
  · intro ce _ S'S
    exact ce.antitone_left S'S |>.right
  · intro allempty
    refine ⟨?_, allempty S le_rfl⟩
    intro a aS aCH
    apply allempty (S \ {a}) (Set.diff_subset ..) a (by simp [SP aS]) aCH

theorem ConvexEmptyIn.iff_triangles {s : Finset Point} {S : Set Point}
    (sS : ↑s ⊆ S) (sz : 3 ≤ s.card) :
    ConvexEmptyIn s S ↔ ∀ (t : Finset Point), t.card = 3 → t ⊆ s → ConvexEmptyIn t S := by
  constructor
  · intro ce _ _ ts
    apply ce.antitone_left ts
  · rw [ConvexEmptyIn.iff sS]
    intro H S' hS' p ⟨pS, pn⟩ pS'
    obtain ⟨S', rfl⟩ := (s.finite_toSet.subset hS').exists_finset_coe
    rw [convexHull_eq_union] at pS'; simp at pS'
    obtain ⟨t, indep, tS', ht⟩ := pS'
    have : t.card ≤ 3 := by simpa using indep.card_le_finrank_succ'
    obtain ⟨u, tu, us, hu⟩ := Finset.exists_intermediate_set (3 - t.card)
      (by rwa [Nat.sub_add_cancel this]) (tS'.trans hS')
    have := H _ (by rwa [Nat.sub_add_cancel this] at hu) us
    refine this.2 _ ⟨pS, fun pu => ?_⟩ (convexHull_mono tu ht)
    exact this.1 p pu (convexHull_mono (Set.subset_diff_singleton tu (mt (tS' ·) pn)) ht)

theorem ConvexEmptyIn.iff_triangles' {s : Finset Point} {S : List Point}
    (sS : s ⊆ S.toFinset) (gp : Point.PointListInGeneralPosition S) :
    ConvexEmptyIn s S.toFinset ↔
    ∀ (t : Finset Point), t.card = 3 → t ⊆ s → EmptyShapeIn t S.toFinset := by
  if sz : 3 ≤ s.card then
    have' sS' : (s:Set _) ⊆ S.toFinset := sS
    rw [ConvexEmptyIn.iff_triangles sS' sz]
    simp (config := {contextual := true}) [ConvexEmptyIn,
      fun a b => ConvexPoints.triangle' a (subset_trans b sS) gp]
  else
    constructor <;> intro
    · intro _ h1 h2; cases sz (h1 ▸ Finset.card_le_card h2)
    · refine ⟨ConvexPoints.lt_3 (not_le.1 sz), fun p ⟨pS, pn⟩ pS' => pn ?_⟩
      have := Nat.le_of_lt_succ <| not_le.1 sz
      match s.exists_mk, this with
      | ⟨[], _, (eq : s = ∅)⟩, _ => subst eq; simp at pS'
      | ⟨[a], _, (eq : s = {a})⟩, _ => subst eq; simpa using pS'
      | ⟨[a,b], h1, eq⟩, _ =>
        have : s = {a, b} := eq ▸ by ext; simp
        have gp' := Point.PointListInGeneralPosition.subperm.1 gp <|
          List.subperm_of_subset (.cons (a := p) (by simpa [this] using pn) h1) <|
          List.cons_subset.2 ⟨by simpa using pS, by simpa [this, Finset.insert_subset_iff] using sS⟩
        cases gp'.not_mem_seg (by simpa [this] using pS')

def HasEmptyNGon (n : Nat) (S : Set Point) : Prop :=
  ∃ s : Finset Point, s.card = n ∧ ↑s ⊆ S ∧ ConvexEmptyIn s S

def HasEmptyTriangle : Set Point → Prop := HasEmptyNGon 3

theorem HasEmptyTriangle.iff (S : Set Point) :
    HasEmptyTriangle S ↔
    ∃ᵉ (a ∈ S) (b ∈ S) (c ∈ S), Point.InGeneralPosition₃ a b c ∧
      ∀ s ∈ S \ {a,b,c}, ¬PtInTriangle s a b c := by
  simp [HasEmptyTriangle, HasEmptyNGon, PtInTriangle]
  constructor
  · intro ⟨s, h1, h2, h3, h4⟩
    match s, s.exists_mk with | _, ⟨[a,b,c], h1, rfl⟩ => ?_
    have s_eq : (Finset.mk (Multiset.ofList [a,b,c]) h1 : Set _) = {a, b, c} := by ext; simp
    simp [not_or, Set.subset_def] at h1 h2 h3 ⊢
    refine ⟨a, h2.1, b, h2.2.1, c, h2.2.2, ConvexPoints.triangle_iff.1 h3, ?_⟩
    simpa [not_or, EmptyShapeIn, s_eq] using h4
  · intro ⟨a, ha, b, hb, c, hc, h1, h2⟩
    let s : Finset Point := ⟨[a,b,c], by simp [h1.ne₁, h1.ne₂, h1.ne₃]⟩
    have s_eq : s = {a,b,c} := by ext; simp
    refine ⟨s, rfl, ?_, ConvexPoints.triangle_iff.2 h1, ?_⟩
    · simp [Set.subset_def, ha, hb, hc]
    · simpa [s_eq, EmptyShapeIn] using h2

def HasEmptyHexagon : Set Point → Prop := HasEmptyNGon 6

def σIsEmptyTriangleFor (a b c : Point) (S : Set Point) : Prop :=
  ∀ s ∈ S, ¬σPtInTriangle s a b c

def σHasEmptyTriangle (S : Set Point) : Prop :=
  ∃ᵉ (a ∈ S) (b ∈ S) (c ∈ S),
    a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ σIsEmptyTriangleFor a b c S