import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Join
import Geo.Definitions.Point
import Geo.Definitions.PtInTriangle

/-! Definitions of geometric structures that we will prove must exist. -/

namespace Geo

/-- `EmptyShapeIn S P` means that `S` carves out an empty shape in `P`:
the convex hull of `S` contains no point of `P`
other than those already in `S`. -/
def EmptyShapeIn (S P : Set Point) : Prop :=
  ∀ p ∈ P \ S, p ∉ convexHull ℝ S

theorem EmptyShapeIn.rfl {S : Set Point} : EmptyShapeIn S S := by
  intro _ h
  simp at h

theorem emptyShapeIn_congr_right {S : Set Point} (h : ∀ p ∉ S, p ∈ P₁ ↔ p ∈ P₂) :
    EmptyShapeIn S P₁ ↔ EmptyShapeIn S P₂ :=
  forall_congr' fun _ => imp_congr_left <| and_congr_left (h _)

/-- `ConvexIndep S` means that `S` consists of extremal points of its convex hull,
i.e. the point set encloses a convex polygon. Also known as a "convex-independent set". -/
def ConvexIndep (S : Set Point) : Prop :=
  ∀ a ∈ S, a ∉ convexHull ℝ (S \ {a})

open Classical
theorem ConvexIndep.triangle_iff {a b c : Point} {h : [a, b, c].Nodup} :
    ConvexIndep (Finset.mk (α := Point) [a,b,c] h) ↔ Point.InGenPos₃ a b c := by
  constructor <;> intro h2
  · simp [not_or, Set.subset_def] at h ⊢
    refine Point.InGenPos₃.iff_not_mem_seg.2 ⟨?_, ?_, ?_⟩ <;>
      refine (h2 _ (by simp) <| convexHull_mono ?_ ·) <;> simp [Set.subset_def]
    · exact ⟨Ne.symm h.1.1, Ne.symm h.1.2⟩
    · exact ⟨h.1.1, Ne.symm h.2⟩
    · exact ⟨h.1.2, h.2⟩
  · have s_eq : Finset.mk (α := Point) [a,b,c] h = {a,b,c} := by ext; simp
    simp [s_eq]; intro p hp hp2; simp at hp
    rw [Point.InGenPos₃.iff_not_mem_seg] at h2
    obtain h|h|h := hp <;> subst p
    · exact h2.1 (convexHull_mono (by simp) hp2)
    · exact h2.2.1 (convexHull_mono (by simp [Set.subset_def]) hp2)
    · exact h2.2.2 (convexHull_mono (by simp [Set.subset_def]) hp2)

theorem ConvexIndep.lt_3 {s : Finset Point} (hs : s.card < 3) : ConvexIndep s := by
  intro a ha hn
  rw [← Finset.coe_erase] at hn
  have := Nat.le_of_lt_succ <| (Finset.card_erase_lt_of_mem ha).trans_le (Nat.le_of_lt_succ hs)
  generalize e1 : s.erase a = s' at *
  match s'.exists_mk, this with
  | ⟨[], _, (eq : s' = ∅)⟩, _ => subst eq; simp at hn
  | ⟨[b], h1, (eq : s' = {b})⟩, _ =>
    subst eq; simp at hn; subst b
    simpa using congrArg (a ∈ ·) e1

theorem ConvexIndep.triangle' {s : Finset Point} {S : Finset Point}
    (hs : s.card ≤ 3) (sS : s ⊆ S) (gp : Point.SetInGenPos S) :
    ConvexIndep s := by
  cases lt_or_eq_of_le hs with
  | inl hs => exact ConvexIndep.lt_3 hs
  | inr hs =>
    match s, s.exists_mk with | _, ⟨[a,b,c], h1, rfl⟩ => ?_
    rw [ConvexIndep.triangle_iff]
    refine gp ?_ h1
    intro _ _
    simp [Finset.subset_iff] at *
    aesop

theorem ConvexIndep.antitone {S₁ S₂ : Set Point} (S₁S₂ : S₁ ⊆ S₂)
    (convex : ConvexIndep S₂) : ConvexIndep S₁ := by
  intro a aS₁ aCH
  have : S₁ \ {a} ⊆ S₂ \ {a} := Set.diff_subset_diff S₁S₂ (le_refl _)
  apply convex a (S₁S₂ aS₁) (convexHull_mono this aCH)

def ConvexEmptyIn (S P : Set Point) : Prop :=
  ConvexIndep S ∧ EmptyShapeIn S P

theorem ConvexEmptyIn.antitone_left {S₁ S₂ P : Set Point} (S₁S₂ : S₁ ⊆ S₂) :
    ConvexEmptyIn S₂ P → ConvexEmptyIn S₁ P := by
  refine fun ⟨convex, empty⟩ => ⟨convex.antitone S₁S₂, fun p pPS₁ pCH => ?_⟩
  refine empty p ⟨pPS₁.left, ?_⟩ (convexHull_mono S₁S₂ pCH)
  refine fun pS₂ => convex p pS₂ (convexHull_mono ?_ pCH)
  exact fun x xS₁ => ⟨S₁S₂ xS₁, fun xp => pPS₁.right (xp ▸ xS₁)⟩

@[simp]
theorem ConvexEmptyIn.refl_iff {S : Set Point} :
    ConvexEmptyIn S S ↔ ConvexIndep S :=
  ⟨(·.left), (⟨·, EmptyShapeIn.rfl⟩)⟩

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

theorem ConvexEmptyIn.iff_triangles' {s : Finset Point} {S : Finset Point}
    (sS : s ⊆ S) (gp : Point.SetInGenPos S) :
    ConvexEmptyIn s S ↔
    ∀ (t : Finset Point), t.card = 3 → t ⊆ s → EmptyShapeIn t S := by
  if sz : 3 ≤ s.card then
    have' sS' : (s:Set _) ⊆ S := sS
    rw [ConvexEmptyIn.iff_triangles sS' sz]
    simp (config := {contextual := true}) [ConvexEmptyIn,
      fun a b => ConvexIndep.triangle' a (subset_trans b sS) gp]
  else
    constructor <;> intro
    · intro _ h1 h2; cases sz (h1 ▸ Finset.card_le_card h2)
    · refine ⟨ConvexIndep.lt_3 (not_le.1 sz), fun p ⟨pS, pn⟩ pS' => pn ?_⟩
      have := Nat.le_of_lt_succ <| not_le.1 sz
      match s.exists_mk, this with
      | ⟨[], _, (eq : s = ∅)⟩, _ => subst eq; simp at pS'
      | ⟨[a], _, (eq : s = {a})⟩, _ => subst eq; simpa using pS'
      | ⟨[a,b], h1, eq⟩, _ =>
        have : s = {a, b} := eq ▸ by ext; simp
        have gp' : Point.InGenPos₃ p a b := by
          apply gp
          · intro _ _; aesop
          · aesop
        cases gp'.not_mem_seg (by simpa [this] using pS')

theorem ConvexEmptyIn.iff_triangles'' {s : Finset Point} {S : Finset Point}
    (sS : s ⊆ S) (gp : Point.SetInGenPos S) :
    ConvexEmptyIn s S ↔
    ∀ᵉ (a ∈ s) (b ∈ s) (c ∈ s), a ≠ b → a ≠ c → b ≠ c →
      ∀ p ∈ S \ {a,b,c}, ¬PtInTriangle p a b c := by
  simp_rw [iff_triangles' sS gp, Finset.card_eq_three, EmptyShapeIn, PtInTriangle]
  constructor
  . intro H a ha b hb c hc ab ac bc p hp
    have := H {a,b,c} ⟨a,b,c,ab,ac,bc,rfl⟩
    simp at this
    apply this
    . intro x h
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl | rfl <;> assumption
    . simp_all
    . simp_all
  . intro h t ⟨a,b,c,ab,ac,bc,tabc⟩ ts p hp
    cases tabc
    simp only [Finset.coe_insert, Finset.coe_singleton] at hp ⊢
    apply h a (ts (by subfinset_tac)) b (ts (by subfinset_tac)) c (ts (by subfinset_tac)) ab ac bc
    simp at hp ⊢
    assumption

theorem ConvexIndep.iff_triangles' {s : Finset Point} (gp : Point.SetInGenPos s) :
    ConvexIndep s ↔ ∀ (t : Finset Point), t.card = 3 → t ⊆ s → EmptyShapeIn t s := by
  have : s = s.toList.toFinset := s.toList_toFinset.symm
  rw [← ConvexEmptyIn.refl_iff, ← ConvexEmptyIn.iff_triangles' subset_rfl]
  exact gp

theorem ConvexIndep.iff_triangles'' {s : Finset Point} (gp : Point.SetInGenPos s) :
    ConvexIndep s ↔
    ∀ᵉ (a ∈ s) (b ∈ s) (c ∈ s), a ≠ b → a ≠ c → b ≠ c →
      ∀ p ∈ s \ {a,b,c}, ¬PtInTriangle p a b c := by
  rw [← ConvexEmptyIn.refl_iff, ← ConvexEmptyIn.iff_triangles'' subset_rfl]
  exact gp

open Point in
theorem split_convexHull (cvx : ConvexIndep S) :
  ∀ {a b}, a ∈ S → b ∈ S →
    convexHull ℝ S ⊆
    convexHull ℝ {x ∈ S | σ a b x ≠ .ccw} ∪
    convexHull ℝ {x ∈ S | σ a b x ≠ .cw} := by
  suffices ∀ {a b}, a ∈ S → b ∈ S →
      let S1 := {x ∈ S | σ a b x ≠ .ccw}
      let S2 := {x ∈ S | σ a b x ≠ .cw}
      ∀ p, σ a b p ≠ .cw → p ∈ convexHull ℝ S → p ∈ convexHull ℝ S1 ∨ p ∈ convexHull ℝ S2 by
    intro a b ha hb p hp
    by_cases h : σ a b p = .cw
    · cases this hb ha _ (by rw [σ_perm₁, h]; decide) hp with
      | inl h => right; (with_reducible convert h using 4); rw [Ne, ← neg_inj, ← σ_perm₁]; rfl
      | inr h => left; (with_reducible convert h using 4); rw [Ne, ← neg_inj, ← σ_perm₁]; rfl
    · exact this ha hb _ h hp
  intro a b ha hb S1 S2 p hp hn
  have : S = S1 ∪ S2 := by
    ext x; refine (and_iff_left <| imp_iff_not_or.1 (· ▸ by decide)).symm.trans and_or_left
  by_cases ab : a = b
  · subst ab
    refine .inl (convexHull_mono ?_ hn)
    exact fun x hx => ⟨hx, by simp [σ_self₃]⟩
  rcases Set.eq_empty_or_nonempty S1 with eq1 | ne1
  · clear_value S1 S2; simp [eq1] at this; subst S
    exact .inr hn
  rcases Set.eq_empty_or_nonempty S2 with eq2 | ne2
  · clear_value S1 S2; simp [eq2] at this; subst S
    exact .inl hn
  replace := congrArg (convexHull ℝ) this
  rw [convexHull_union ne1 ne2] at this
  let ⟨u, hu, v, hv, hp2⟩ := mem_convexJoin.1 <| this ▸ hn
  have hcvx {z} (this : z ∈ convexHull ℝ S) (ngp : ¬Point.InGenPos₃ a b z) :
      z ∈ convexHull ℝ {a, b} := by
    by_contra zab
    have {a b} (ha : a ∈ S) (hb : b ∈ S) (ab : a ≠ b) (zab : z ∉ convexHull ℝ {a, b}) :
        a ∉ convexHull ℝ {b, z} := fun h => by
      rw [← Set.insert_eq_of_mem ha, ← Set.insert_diff_singleton,
        convexHull_insert (s := S \ {a}) ⟨b, hb, ab.symm⟩] at this
      have hba : b ∈ convexHull ℝ (S \ {a}) := subset_convexHull _ _ ⟨hb, ab.symm⟩
      obtain ⟨w, hw1, hw2⟩ := by simp at this; exact this
      simp at h
      rw [mem_segment_iff_wbtw] at hw2 h
      have := h.trans_ne_left hw2 (zab <| · ▸ subset_convexHull _ _ (by simp))
      exact cvx _ ha <| (convex_convexHull ..).segment_subset hba hw1 (mem_segment_iff_wbtw.2 this)
    exact ngp <| Point.InGenPos₃.iff_not_mem_seg.2
      ⟨this ha hb ab zab, this hb ha (Ne.symm ab) (Set.pair_comm .. ▸ zab), zab⟩
  have hu0 : detAffineMap a b u ≤ 0 := by
    refine convexHull_min ?_ ((convex_Iic 0).affine_preimage (detAffineMap a b)) hu
    intro x ⟨_, hx⟩
    simpa [σ_eq_ccw] using hx
  have hv0 : 0 ≤ detAffineMap a b v := by
    refine convexHull_min ?_ ((convex_Ici 0).affine_preimage (detAffineMap a b)) hv
    intro x ⟨_, hx⟩
    simpa [σ_eq_cw] using hx
  have ⟨z, hz1, hz2⟩ : 0 ∈ detAffineMap a b '' segment ℝ u v := by
    rw [image_segment]; apply Icc_subset_segment
    exact ⟨hu0, hv0⟩
  have zab : z ∈ convexHull ℝ {a, b} := hcvx
    (by rw [this, mem_convexJoin]; exact ⟨_, hu, _, hv, hz1⟩)
    (by simpa [Point.InGenPos₃] using hz2)
  if hp' : Point.InGenPos₃ a b p then ?_ else
    right; refine convexHull_mono ?_ (hcvx hn hp')
    simp [S2, Set.subset_def, ha, hb, σ_self₁, σ_self₂]
  have : p ∈ segment ℝ v z := by
    simp [mem_segment_iff_wbtw] at hp2 hz1 ⊢
    refine (hp2.trans_left_right <| (hz1.wbtw_or_wbtw hp2).resolve_right fun h => ?_).symm
    rw [← mem_segment_iff_wbtw] at h
    have := ((convex_Iic 0).affine_preimage (detAffineMap a b)).segment_subset hu0 hz2.le h
    simp [σ_eq_cw] at hp this
    exact hp' <| this.antisymm hp
  right; refine (convex_convexHull ..).segment_subset hv ?_ this
  simp at zab; refine segment_subset_convexHull ?_ ?_ zab <;> simp [S2, ha, hb, σ_self₁, σ_self₂]

theorem EmptyShapeIn.split (cvx : ConvexIndep S) (ha : a ∈ S) (hb : b ∈ S)
    (H1 : EmptyShapeIn {x ∈ S | σ a b x ≠ .ccw} P)
    (H2 : EmptyShapeIn {x ∈ S | σ a b x ≠ .cw} P) : EmptyShapeIn S P := fun _ ⟨pP, pS⟩ hn =>
  (split_convexHull cvx ha hb hn).elim (H1 _ ⟨pP, mt And.left pS⟩) (H2 _ ⟨pP, mt And.left pS⟩)

def HasEmptyKGon (n : Nat) (P : Set Point) : Prop :=
  ∃ S : Finset Point, S.card = n ∧ ↑S ⊆ P ∧ ConvexEmptyIn S P

def HasConvexKGon (n : Nat) (P : Set Point) : Prop :=
  ∃ S : Finset Point, S.card = n ∧ ↑S ⊆ P ∧ ConvexIndep S

end Geo
