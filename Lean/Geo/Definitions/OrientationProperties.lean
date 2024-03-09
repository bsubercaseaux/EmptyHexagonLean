import Geo.Definitions.Structures
import Geo.Definitions.SigmaEquiv

namespace Geo
open Classical

def σIsEmptyTriangleFor (a b c : Point) (S : Set Point) : Prop :=
  ∀ s ∈ S, ¬σPtInTriangle s a b c

-- def σHasEmptyTriangle (S : Set Point) : Prop :=
--   ∃ᵉ (a ∈ S) (b ∈ S) (c ∈ S),
--     a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ σIsEmptyTriangleFor a b c S

-- lemma σHasEmptyTriangle_iff_HasEmptyTriangle (gp : Point.PointListInGeneralPosition pts) :
--     σHasEmptyTriangle pts.toFinset ↔ HasEmptyTriangle pts.toFinset := by
--   rw [HasEmptyTriangle.iff]
--   constructor
--   . intro ⟨a, ha, b, hb, c, hc, ab, ac, bc, empty⟩
--     use a, ha, b, hb, c, hc
--     have gp₃ : Point.InGeneralPosition₃ a b c := by
--       apply Point.PointListInGeneralPosition.subperm.mp gp
--       apply List.subperm_of_subset (by simp [*])
--       sublist_tac
--     refine ⟨gp₃, ?_⟩
--     intro s hs tri
--     simp only [List.coe_toFinset, Set.mem_diff, Set.mem_setOf_eq, Set.mem_insert_iff,
--       Set.mem_singleton_iff, not_or] at hs
--     have ⟨hs, _, _, _⟩ := hs
--     apply empty s (by simp [hs])
--     rwa [σPtInTriangle_iff]
--     apply gp.subperm₄
--     apply List.subperm_of_subset (by simp [*])
--     sublist_tac
--   . intro ⟨a, ha, b, hb, c, hc, gp', empty⟩
--     use a, ha, b, hb, c, hc, gp'.ne₁, gp'.ne₂, gp'.ne₃
--     intro s hs
--     by_cases sb : s = b
--     . rw [sb]
--       apply not_mem_σPtInTriangle gp'
--     by_cases sa : s = a
--     . intro h
--       apply not_mem_σPtInTriangle gp'.perm₁
--       apply σPtInTriangle.perm₁
--       rwa [sa] at h
--     by_cases sc : s = c
--     . intro h
--       apply not_mem_σPtInTriangle gp'.perm₂
--       apply σPtInTriangle.perm₂
--       rwa [sc] at h
--     have gp₄ : Point.InGeneralPosition₄ s a b c := by
--       apply gp.subperm₄
--       apply List.subperm_of_subset (by simp [*, gp'.ne₁, gp'.ne₂, gp'.ne₃])
--       sublist_tac
--     rw [σPtInTriangle_iff gp₄]
--     apply empty
--     simp at hs
--     simp [hs, not_or, *]

def σHasEmptyNGon (n : Nat) (S : Set Point) : Prop :=
  ∃ s : Finset Point, s.card = n ∧ ↑s ⊆ S ∧
    ∀ᵉ (a ∈ s) (b ∈ s) (c ∈ s), a ≠ b → a ≠ c → b ≠ c →
      σIsEmptyTriangleFor a b c S

theorem σIsEmptyTriangleFor_iff_diff (gp : Point.InGeneralPosition₃ a b c) :
    σIsEmptyTriangleFor a b c S ↔ σIsEmptyTriangleFor a b c (S\{a,b,c}) := by
  refine ⟨fun H x h => H x h.1, fun H x h hn => H x ⟨h, ?_⟩ hn⟩
  rintro (rfl|rfl|rfl)
  · exact not_mem_σPtInTriangle gp.perm₁ hn.perm₁
  · exact not_mem_σPtInTriangle gp hn
  · exact not_mem_σPtInTriangle gp.perm₂ hn.perm₂

theorem σHasEmptyNGon_iff_HasEmptyNGon (gp : Point.PointListInGeneralPosition pts) :
    σHasEmptyNGon n pts.toFinset ↔ HasEmptyNGon n pts.toFinset := by
  unfold σHasEmptyNGon HasEmptyNGon
  refine exists_congr fun s => and_congr_right' <| and_congr_right fun spts => ?_
  rw [ConvexEmptyIn.iff_triangles'' spts gp]
  simp [Set.subset_def] at spts; simp
  iterate 9 refine forall_congr' fun _ => ?_
  rw [σIsEmptyTriangleFor_iff_diff]
  · simp [not_or, σIsEmptyTriangleFor]
    repeat refine forall_congr' fun _ => ?_
    rw [σPtInTriangle_iff]; apply gp.subperm₄
    simp [*, List.subperm_of_subset]
  · apply Point.PointListInGeneralPosition.subperm.1 gp
    simp [*, List.subperm_of_subset]

lemma σPtInTriangle_congr (e : S ≃σ T) :
    ∀ (_ : a ∈ S) (_ : p ∈ S) (_ : q ∈ S) (_ : r ∈ S),
      σPtInTriangle (e.f a) (e.f p) (e.f q) (e.f r) ↔ σPtInTriangle a p q r := by
  simp (config := {contextual := true}) [σPtInTriangle, e.σ_eq]

open List
theorem σHasEmptyNGon_3_iff (gp : Point.PointListInGeneralPosition pts) :
    σHasEmptyNGon 3 pts.toFinset ↔
      ∃ a b c, [a, b, c] <+~ pts ∧ σIsEmptyTriangleFor a b c pts.toFinset := by
  constructor
  · intro ⟨s, hs1, ss, hs2⟩
    match s, s.exists_mk with | _, ⟨[a,b,c], h1, rfl⟩ => ?_
    have sp := subperm_of_subset (l₂ := pts) h1 (by simpa [Set.subset_def] using ss)
    refine ⟨a, b, c, sp, fun p hp hn => ?_⟩
    have := (hs2 a · b · c ·)
    simp [not_or] at h1 hp; simp [h1] at this
    refine this _ ?_ hn
    simp [hp]
  · intro ⟨a, b, c, sp, H⟩
    have nd := sp.nodup (gp.nodup sp.length_le)
    have ⟨s, hs1, hs2⟩ : ∃ s : Finset Point, s = ⟨[a, b, c], nd⟩ ∧ s.card = 3 := ⟨_, rfl, rfl⟩
    refine ⟨s, hs2, by simpa [hs1, Set.subset_def] using sp.subset, ?_⟩
    intro x hx y hy z hz xy xz yz u hu hn
    simp [not_or] at hu
    refine H u (by simp [hu]) <| (σPtInTriangle.perm ?_).1 hn
    have : ⟨[x, y, z], by simp [*]⟩ = s :=
      Finset.eq_of_subset_of_card_le (by simp [Finset.subset_iff, hx, hy, hz]) (by simp [hs2])
    exact Multiset.coe_eq_coe.1 <| Finset.val_inj.2 <| this.trans hs1

-- lemma σIsEmptyTriangleFor_congr (e : S ≃σ T) :
--     ∀ (_ : p ∈ S) (_ : q ∈ S) (_ : r ∈ S),
--       σIsEmptyTriangleFor (e.f p) (e.f q) (e.f r) T ↔ σIsEmptyTriangleFor p q r S  := by
--   simp [σIsEmptyTriangleFor]
--   intro hp hq hr
--   refine ⟨fun h => ?_, fun h => ?_⟩
--   . intro s hs
--     simp at h hs
--     have := h (e.f s) (e.mem hs)
--     rwa [σPtInTriangle_congr e hs hp hq hr] at this
--   . intro t ht
--     have ⟨s, hs, est⟩ := e.mem_iff.mp ht
--     rw [← est, σPtInTriangle_congr e hs hp hq hr]
--     apply h s hs

lemma OrientationProperty_σHasEmptyNGon : OrientationProperty (σHasEmptyNGon n) := by
  unfold σHasEmptyNGon
  intro S T e ⟨s, scard, sS, h⟩
  refine ⟨s.image e, ?_, ?_, ?_⟩
  . rwa [s.card_image_of_injOn (e.bij.right.left.mono sS)]
  . intro x; simp
    rintro _ hx rfl
    exact e.bij.left (sS hx)
  . have injs : Set.InjOn e s := e.bij.right.left.mono sS
    simp (config := { contextual := true }) only [injs.eq_iff,
      Finset.mem_image, Finset.mem_coe, σIsEmptyTriangleFor,
      and_imp, forall_exists_index, forall_apply_eq_imp_iff₂, ne_eq, not_or,
      Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
    -- The part below is very explicit, maybe could be automated.
    intro a ha b hb c hc ab ac bc p hp
    have : e.symm p ∈ S := e.symm.bij.left hp
    have : p = e (e.symm p) := e.apply_symm_apply hp |>.symm
    rw [this, σPtInTriangle_congr e (e.symm.bij.left hp) (sS ha) (sS hb) (sS hc)]
    exact h a ha b hb c hc ab ac bc (e.symm p) (e.symm.bij.left hp)

theorem σIsEmptyTriangleFor_exists (gp : Point.PointListInGeneralPosition S)
    (abc : [a, b, c] <+~ S) :
    ∃ b' ∈ S, σ a b' c = σ a b c ∧ (b' = b ∨ σPtInTriangle b' a b c) ∧
      σIsEmptyTriangleFor a b' c S.toFinset := by
  have nd := gp.nodup abc.length_le
  have gp' := Point.PointListInGeneralPosition.subperm.1 gp
  have ss := abc.subset; simp at ss
  let _ : Preorder Point := {
    le := fun x y => PtInTriangle x a y c
    le_refl := fun z => subset_convexHull _ _ <| by simp
    le_trans := fun u v w uv vw => by
      simp [PtInTriangle] at uv vw ⊢
      refine convexHull_min ?_ (convex_convexHull ..) uv
      simp [Set.subset_def, *]; constructor <;> apply subset_convexHull <;> simp
  }
  have ⟨b', hb1, hb2⟩ := Finset.exists_minimal
    (S.toFinset.filter fun x => σ a x c = σ a b c ∧ x ≤ b)
    ⟨b, by simp [ss]; apply subset_convexHull; simp⟩
  simp at hb1 hb2
  have abc' : Point.InGeneralPosition₃ a b' c := by
    rw [Point.InGeneralPosition₃.iff_ne_collinear, hb1.2.1,
      ← Point.InGeneralPosition₃.iff_ne_collinear]; exact gp' abc
  refine ⟨_, hb1.1, hb1.2.1, ?_, fun z hz hn => ?_⟩
  · refine or_iff_not_imp_left.2 fun h => ?_
    refine (σPtInTriangle_iff <| gp.subperm₄ ?_).2 hb1.2.2
    refine subperm_of_subset ?_ (List.cons_subset.2 ⟨hb1.1, abc.subset⟩)
    exact nodup_cons.2 ⟨by simp [not_or, h, abc'.ne₁.symm, abc'.ne₃], abc.nodup nd⟩
  simp at hz
  have gp4 := hn.gp₄_of_gp₃ abc'
  have zb' : z ≤ b' := (σPtInTriangle_iff gp4).1 hn
  have := (σPtInTriangle_iff gp4.perm₁.perm₂.perm₁).2 <|
    hb2 _ hz (by rw [σ_perm₂, hn.2.1, ← σ_perm₂, hb1.2.1]) (zb'.trans hb1.2.2) zb'
  refine Point.InGeneralPosition₃.iff_ne_collinear.1 abc' <| (Orientation.eq_neg_self _).1 ?_
  rw [← σ_perm₂, ← hn.1, ← hn.2.1, σ_perm₂, this.1, ← σ_perm₂]

def σCCWPoints : List Point → Prop
  | [] => True
  | a :: l => l.Pairwise (σ a · · = .CCW) ∧ σCCWPoints l

theorem σCCWPoints_append : σCCWPoints (l₁ ++ l₂) ↔
    σCCWPoints l₁ ∧ σCCWPoints l₂ ∧
    (∀ a ∈ l₁, l₂.Pairwise (σ a · · = .CCW)) ∧
    (∀ c ∈ l₂, l₁.Pairwise (σ · · c = .CCW)) := by
  induction l₁ generalizing l₂ with | nil => simp [σCCWPoints] | cons a l₁ IH => ?_
  simp [σCCWPoints, pairwise_append, forall_and, IH]; aesop

theorem σCCWPoints.cycle (H : σCCWPoints (l₁ ++ l₂)) : σCCWPoints (l₂ ++ l₁) := by
  simp [σCCWPoints_append] at H ⊢
  let ⟨H1, H2, H3, H4⟩ := H
  exact ⟨H2, H1,
    fun c hc => (H4 c hc).imp <| Eq.trans (by rw [σ_perm₁, ← σ_perm₂]),
    fun a ha => (H3 a ha).imp <| Eq.trans (by rw [σ_perm₂, ← σ_perm₁])⟩

theorem σCCWPoints.join
    (H1 : σCCWPoints (b :: a :: l₁))
    (H2 : σCCWPoints (a :: b :: l₂))
    (hj : ∀ᵉ (c ∈ l₁) (d ∈ l₂), σ a c d = .CCW ∧ σ c b d = .CCW) :
    σCCWPoints (a :: l₁ ++ b :: l₂) := by
  simp [σCCWPoints, σCCWPoints_append, pairwise_append] at H1 H2 ⊢; simp [H1, H2]
  obtain ⟨⟨bac, bcc⟩, acc, -⟩ := H1
  obtain ⟨⟨abd, add⟩, bdd, -⟩ := H2
  refine ⟨⟨abd, fun c hc => ⟨?_, fun d hd => ?_⟩⟩,
    fun c hc => ⟨fun d hd => ?_, ?_⟩, ?_, fun d hd => ?_⟩
  · rw [σ_perm₂, ← σ_perm₁]; exact bac _ hc
  · exact (hj _ hc _ hd).1
  · exact (hj _ hc _ hd).2
  · refine (Pairwise.and_mem.1 add).imp₂ (fun d e ⟨hd, he, ade⟩ bdd => ?_) bdd
    have abe := abd _ he
    have ⟨dac, cbd⟩ := hj _ hc _ hd
    have ⟨eac, cbe⟩ := hj _ hc _ he
    sorry
  · sorry
  · sorry

end Geo
