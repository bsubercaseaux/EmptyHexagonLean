import Geo.Definitions.Structures
import Geo.Definitions.SigmaEmbed

namespace Geo
open Classical

def σIsEmptyTriangleFor (a b c : Point) (S : Set Point) : Prop :=
  ∀ s ∈ S, ¬σPtInTriangle s a b c

def σHasEmptyTriangle (S : Set Point) : Prop :=
  ∃ᵉ (a ∈ S) (b ∈ S) (c ∈ S),
    a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ σIsEmptyTriangleFor a b c S

lemma σHasEmptyTriangle_iff_HasEmptyTriangle (gp : Point.PointListInGeneralPosition pts) :
    σHasEmptyTriangle pts.toFinset ↔ HasEmptyTriangle pts.toFinset := by
  rw [HasEmptyTriangle.iff]
  constructor
  . intro ⟨a, ha, b, hb, c, hc, ab, ac, bc, empty⟩
    use a, ha, b, hb, c, hc
    have gp₃ : Point.InGeneralPosition₃ a b c := by
      apply Point.PointListInGeneralPosition.subperm.mp gp
      apply List.subperm_of_subset (by simp [*])
      sublist_tac
    refine ⟨gp₃, ?_⟩
    intro s hs tri
    simp only [List.coe_toFinset, Set.mem_diff, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff, not_or] at hs
    have ⟨hs, _, _, _⟩ := hs
    apply empty s (by simp [hs])
    rwa [σPtInTriangle_iff]
    apply gp.subperm₄
    apply List.subperm_of_subset (by simp [*])
    sublist_tac
  . intro ⟨a, ha, b, hb, c, hc, gp', empty⟩
    use a, ha, b, hb, c, hc, gp'.ne₁, gp'.ne₂, gp'.ne₃
    intro s hs
    by_cases sb : s = b
    . rw [sb]
      apply not_mem_σPtInTriangle gp'
    by_cases sa : s = a
    . intro h
      apply not_mem_σPtInTriangle gp'.perm₁
      apply σPtInTriangle.perm₁
      rwa [sa] at h
    by_cases sc : s = c
    . intro h
      apply not_mem_σPtInTriangle gp'.perm₂
      apply σPtInTriangle.perm₂
      rwa [sc] at h
    have gp₄ : Point.InGeneralPosition₄ s a b c := by
      apply gp.subperm₄
      apply List.subperm_of_subset (by simp [*, gp'.ne₁, gp'.ne₂, gp'.ne₃])
      sublist_tac
    rw [σPtInTriangle_iff gp₄]
    apply empty
    simp at hs
    simp [hs, not_or, *]

def σHasEmptyNGon (n : Nat) (S : Set Point) : Prop :=
  ∃ s : Finset Point, s.card = n ∧ ↑s ⊆ S ∧
    ∀ᵉ (a ∈ s) (b ∈ s) (c ∈ s), a ≠ b → a ≠ c → b ≠ c →
      ∀ p ∈ S \ {a,b,c}, ¬σPtInTriangle p a b c

theorem σHasEmptyNGon_iff_HasEmptyNGon (gp : Point.PointListInGeneralPosition pts) :
    σHasEmptyNGon n pts.toFinset ↔ HasEmptyNGon n pts.toFinset := by
  unfold σHasEmptyNGon HasEmptyNGon
  refine exists_congr fun s => and_congr_right' <| and_congr_right fun spts => ?_
  rw [ConvexEmptyIn.iff_triangles'' spts gp]
  simp [Set.subset_def] at spts; simp [not_or]
  repeat refine forall_congr' fun _ => ?_
  rw [σPtInTriangle_iff]; apply gp.subperm₄
  simp [*, List.subperm_of_subset]

lemma σPtInTriangle_congr (e : S ≼σ T) :
    ∀ (_ : a ∈ S) (_ : p ∈ S) (_ : q ∈ S) (_ : r ∈ S),
      σPtInTriangle (e.f a) (e.f p) (e.f q) (e.f r) ↔ σPtInTriangle a p q r := by
  simp (config := {contextual := true}) [σPtInTriangle, e.σ_eq]

lemma σIsEmptyTriangleFor_congr (e : S ≼σ T) :
    ∀ (_ : p ∈ S) (_ : q ∈ S) (_ : r ∈ S),
      σIsEmptyTriangleFor (e.f p) (e.f q) (e.f r) T.toFinset ↔ σIsEmptyTriangleFor p q r S.toFinset  := by
  unfold σIsEmptyTriangleFor
  intro hp hq hr
  refine ⟨fun h => ?_, fun h => ?_⟩
  sorry; sorry
  -- . intro s hs
  --   have := h (e s) (e.bij.left hs)
  --   rwa [σPtInTriangle_congr e hs hp hq hr] at this
  -- . intro s hs
  --   have := h (e.symm s) (e.symm.bij.left hs)
  --   rwa [← σPtInTriangle_congr e (e.symm.bij.left hs) hp hq hr, e.apply_symm_apply hs] at this

lemma OrientationProperty_σHasEmptyNGon : OrientationProperty (σHasEmptyNGon n ·.toFinset) := by
  unfold σHasEmptyNGon
  sorry
  -- intro S T e ⟨s, scard, sS, h⟩
  -- refine ⟨s.image e, ?_, ?_, ?_⟩
  -- . rwa [s.card_image_of_injOn (e.bij.right.left.mono sS)]
  -- . intro x; simp
  --   rintro _ hx rfl
  --   exact e.bij.left (sS hx)
  -- . have injs : Set.InjOn e s := e.bij.right.left.mono sS
  --   simp (config := { contextual := true }) only [injs.eq_iff,
  --     Finset.mem_image, Finset.mem_coe,
  --     and_imp, forall_exists_index, forall_apply_eq_imp_iff₂, ne_eq, not_or,
  --     Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
  --   -- The part below is very explicit, maybe could be automated.
  --   intro a ha b hb c hc ab ac bc p hp pa pb pc
  --   have : e.symm p ∈ S := e.symm.bij.left hp
  --   have : p = e (e.symm p) := e.apply_symm_apply hp |>.symm
  --   rw [this, σPtInTriangle_congr e (e.symm.bij.left hp) (sS ha) (sS hb) (sS hc)]
  --   apply h a ha b hb c hc ab ac bc (e.symm p) (e.symm.bij.left hp)
  --   . intro h
  --     rw [← h, e.apply_symm_apply hp] at pa
  --     contradiction
  --   . intro h
  --     rw [← h, e.apply_symm_apply hp] at pb
  --     contradiction
  --   . intro h
  --     rw [← h, e.apply_symm_apply hp] at pc
  --     contradiction

end Geo
