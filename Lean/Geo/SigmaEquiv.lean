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

namespace σEquiv

@[refl]
def refl (S : Set Point) : S ≃σ S :=
  ⟨Equiv.refl _, by simp⟩

@[symm]
def symm : S ≃σ T → T ≃σ S :=
  fun ⟨f, h⟩ => ⟨f.symm, by simp [h]⟩

@[trans]
def trans : S ≃σ T → T ≃σ U → S ≃σ U :=
  fun ⟨f, hf⟩ ⟨g, hg⟩ => ⟨f.trans g, by simp [hg, hf]⟩

open Point in

theorem GP_of_σEquiv_of_GP {S T : Finset Point} :
  S ≃σ T → PointFinsetInGeneralPosition S → PointFinsetInGeneralPosition T := by
  sorry
  /-
  unfold PointFinsetInGeneralPosition
  intro hEquiv hgp p q r hmem
  --have := hEquiv
  replace hEquiv := hEquiv.symm
  rw [InGeneralPosition₃.iff_ne_collinear]
  have hp : p ∈ T := hmem (Finset.mem_insert.mpr (Or.inl rfl))
  have hq : q ∈ T := hmem (by simp)
  have hr : r ∈ T := hmem (by simp)

  let ⟨p', hp'⟩ := hEquiv.f ⟨p, hp⟩
  let ⟨q', hq'⟩ := hEquiv.f ⟨q, hq⟩
  let ⟨r', hr'⟩ := hEquiv.f ⟨r, hr⟩
  have : {p', q', r'} ⊆ S := by
    sorry
    done
  have := hgp this
  rwa [InGeneralPosition₃.iff_ne_collinear] at this


  --have := theorem Point.InGeneralPosition₃.iff_ne_collinear {p q r : Point} :
  --  InGeneralPosition₃ p q r ↔ σ p q r ≠ .Collinear
  sorry
  done -/

end σEquiv

instance : EquivLike (S ≃σ T) S T where
  coe e := e.f.toFun
  inv e := e.f.invFun
  left_inv e := e.f.left_inv
  right_inv e := e.f.right_inv
  coe_injective' e₁ e₂ h₁ h₂ := by have := EquivLike.coe_injective' e₁.f e₂.f h₁ h₂; cases e₁; cases e₂; congr

instance : FunLike (S ≃σ T) S T :=
  EmbeddingLike.toDFunLike

/-- Extend the equivalence by `x ↦ y`,
assuming that signotopes are all preserved. -/
def σEquiv.extend (x y : Point) (e : S ≃σ T) :
    (∀ᵉ (ha : a ∈ S) (hb : b ∈ S), σ x a b = σ y (e ⟨a, ha⟩) (e ⟨b, hb⟩)) →
    x ∉ S → y ∉ T → S ∪ {x} ≃σ T ∪ {y} :=
  sorry

def OrientationProperty (P : Set Point → Prop) :=
  ∀ S T, S ≃σ T → P S → P T

theorem OrientationProperty.not : OrientationProperty P → OrientationProperty (¬P ·) := by
  unfold OrientationProperty
  intro h S T hσ hS hT
  exact hS (h _ _ hσ.symm hT)
