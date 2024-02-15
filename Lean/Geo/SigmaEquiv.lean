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
