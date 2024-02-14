import Geo.Orientations

namespace Geo
noncomputable section
open Classical
open List

-- This is in fact an isomorphism of 'signotope algebras'
-- (perhaps oriented spaces?),
-- that is sets S equipped with an operation S³ → Orientation
-- which satisfy antisymmetry and some other axioms.
-- Sets of points are examples of signotope algebras.
structure σEquiv (S T : Set Point) :=
  (f : S ≃ T)
  (hσ : ∀ (p q r : S), σ p q r = σ (f p) (f q) (f r))

infix:50 " ≃σ " => σEquiv

def σEquiv.refl (S : Set Point) : S ≃σ S :=
  ⟨Equiv.refl _, by simp⟩

def σEquiv.symm : S ≃σ T → T ≃σ S :=
  fun ⟨f, h⟩ => ⟨f.symm, by simp [h]⟩

def σEquiv.trans : S ≃σ T → T ≃σ U → S ≃σ U :=
  fun ⟨f, hf⟩ ⟨g, hg⟩ => ⟨f.trans g, by simp [hg, hf]⟩

instance : EquivLike (S ≃σ T) S T where
  coe e := e.f.toFun
  inv e := e.f.invFun
  left_inv e := e.f.left_inv
  right_inv e := e.f.right_inv
  coe_injective' e₁ e₂ h₁ h₂ := by have := EquivLike.coe_injective' e₁.f e₂.f h₁ h₂; cases e₁; cases e₂; congr

instance : FunLike (S ≃σ T) S T :=
  EmbeddingLike.toDFunLike

def OrientationProperty (P : Set Point → Prop) :=
  ∀ S T, S ≃σ T → P S → P T

theorem OrientationProperty.not : OrientationProperty P → OrientationProperty (¬P ·) := by
  unfold OrientationProperty
  intro h S T hσ hS hT
  exact hS (h _ _ hσ.symm hT)

-- Same as σPtInTriangle, here for reference
def σPtInTriangle' (a p q r : Point) : Prop :=
  σ p q r = σ p a r ∧
  σ p a q = σ p r q ∧
  σ q a r = σ q p r

lemma σPtInTriangle'_of_σEquiv (f : S ≃σ T) (a p q r : S) :
    σPtInTriangle' a p q r → σPtInTriangle' (f a) (f p) (f q) (f r) := by
  simp only [σPtInTriangle', f.hσ]
  exact id

/-- `{p, q, r}` make up a triangle that contains no point in `S`. -/
def σIsEmptyTriangleFor (p q r : Point) (S : Set Point) :=
  Finset.card {p, q, r} = 3 ∧ -- TODO: maybe remove this part of the condition?
    ∀ a ∈ S, ¬σPtInTriangle' a p q r

def σHasEmptyTriangle (S : Set Point) : Prop :=
  ∃ p q r : S, σIsEmptyTriangleFor p q r S

theorem OrientationProperty_σHasEmptyTriangle : OrientationProperty σHasEmptyTriangle := by
  intro S T f ⟨p, q, r, h, h'⟩
  use f p, f q, f r
  constructor
  . sorry -- boring bijection card
  . intro t ht ht'
    sorry
    -- simp only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at ht
    -- have ⟨ht, htp, htq, htr⟩ := ht
    -- apply h' (f.symm ⟨t, ht⟩)
    -- simp only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    -- refine ⟨by simp, ?_, ?_, ?_⟩
    -- . sorry -- boring bijection coe
    -- . sorry -- ditto
    -- . sorry -- ditto
    -- . sorry -- use σPtInTriangle_of_σEquiv
