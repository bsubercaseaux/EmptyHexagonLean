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
      σIsEmptyTriangleFor a b c (S \ {a,b,c})

theorem σHasEmptyNGon_iff_HasEmptyNGon (gp : Point.PointListInGeneralPosition pts) :
    σHasEmptyNGon n pts.toFinset ↔ HasEmptyNGon n pts.toFinset := by
  unfold σHasEmptyNGon HasEmptyNGon
  refine exists_congr fun s => and_congr_right' <| and_congr_right fun spts => ?_
  rw [ConvexEmptyIn.iff_triangles'' spts gp]
  simp [Set.subset_def] at spts; simp [not_or, σIsEmptyTriangleFor]
  repeat refine forall_congr' fun _ => ?_
  rw [σPtInTriangle_iff]; apply gp.subperm₄
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
    simp [hp, not_or]
    have := hn.gp₄_of_gp₃ (Point.PointListInGeneralPosition.subperm.1 gp sp)
    exact ⟨this.gp₁.ne₁, this.gp₃.ne₁, this.gp₃.ne₂⟩
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
    intro a ha b hb c hc ab ac bc p hp pa pb pc
    have : e.symm p ∈ S := e.symm.bij.left hp
    have : p = e (e.symm p) := e.apply_symm_apply hp |>.symm
    rw [this, σPtInTriangle_congr e (e.symm.bij.left hp) (sS ha) (sS hb) (sS hc)]
    apply h a ha b hb c hc ab ac bc (e.symm p) (e.symm.bij.left hp)
    . intro h
      rw [← h, e.apply_symm_apply hp] at pa
      contradiction
    . intro h
      rw [← h, e.apply_symm_apply hp] at pb
      contradiction
    . intro h
      rw [← h, e.apply_symm_apply hp] at pc
      contradiction

end Geo
