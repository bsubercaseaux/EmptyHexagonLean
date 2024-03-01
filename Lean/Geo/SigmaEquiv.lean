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
  (f : Point → Point)
  (bij' : Set.BijOn f S T)
  (σ_eq' : ∀ᵉ (p ∈ S) (q ∈ S) (r ∈ S), σ p q r = σ (f p) (f q) (f r))

infix:50 " ≃σ " => σEquiv

namespace σEquiv

instance : FunLike (S ≃σ T) Point Point where
  coe e := e.f
  coe_injective' a b h := by cases a; cases b; cases h; rfl

lemma σ_eq (e : S ≃σ T) : ∀ᵉ (p ∈ S) (q ∈ S) (r ∈ S), σ p q r = σ (e p) (e q) (e r) :=
  e.σ_eq'

lemma bij (e : S ≃σ T) : Set.BijOn e S T := e.bij'

lemma mem_iff (e : S ≃σ T) : y ∈ T ↔ ∃ x ∈ S, e x = y :=
  iff_of_eq (congrArg (y ∈ ·) e.bij.image_eq.symm)

@[refl]
def refl (S : Set Point) : S ≃σ S :=
  ⟨id, Set.bijOn_id S, fun _ _ _ _ _ _ => rfl⟩

def symm : S ≃σ T → T ≃σ S :=
  fun ⟨f, bij, hσ⟩ =>
    have inv := Set.BijOn.invOn_invFunOn bij |>.symm
    have bij := bij.symm inv
    ⟨f.invFunOn S,
    bij,
    by
      intro p hp q hq r hr
      rw [hσ _ (bij.left hp) _ (bij.left hq) _ (bij.left hr),
        inv.left hp, inv.left hq, inv.left hr]⟩

lemma symm_invOn (e : S ≃σ T) : Set.InvOn e.symm e S T :=
  e.bij.invOn_invFunOn

@[trans]
def trans : S ≃σ T → T ≃σ U → S ≃σ U :=
  fun ⟨f, fbij, fσ⟩ ⟨g, gbij, gσ⟩ =>
    ⟨g ∘ f,
    gbij.comp fbij,
    by
      intro p hp q hq r hr
      rw [fσ _ hp _ hq _ hr, gσ _ (fbij.left hp) _ (fbij.left hq) _ (fbij.left hr)]
      rfl⟩

@[simp]
theorem symm_apply_apply (e : S ≃σ T) : p ∈ S → e.symm (e p) = p := by
  intro hp
  rw [(symm_invOn e).left hp]

@[simp]
theorem apply_symm_apply (e : S ≃σ T) : p ∈ T → e (e.symm p) = p := by
  intro hp
  rw [(symm_invOn e).right hp]

end σEquiv

def OrientationProperty (P : Set Point → Prop) :=
  ∀ {{S T}}, S ≃σ T → P S → P T

theorem OrientationProperty.not : OrientationProperty P → OrientationProperty (¬P ·) := by
  unfold OrientationProperty
  intro h S T hσ hS hT
  exact hS (h hσ.symm hT)
