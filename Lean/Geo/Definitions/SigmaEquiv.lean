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
structure σEquiv (S T : Set Point) where
  f : Point → Point
  bij' : Set.BijOn f S T
  parity : Bool
  σ_eq' : ∀ᵉ (p ∈ S) (q ∈ S) (r ∈ S), σ p q r = parity ^^^ σ (f p) (f q) (f r)

infix:50 " ≃σ " => σEquiv

namespace σEquiv

instance : CoeFun (S ≃σ T) (fun _ => Point → Point) where
  coe e := e.f

lemma σ_eq (e : S ≃σ T) : ∀ᵉ (p ∈ S) (q ∈ S) (r ∈ S), σ p q r = e.parity ^^^ σ (e p) (e q) (e r) :=
  e.σ_eq'

lemma bij (e : S ≃σ T) : Set.BijOn e S T := e.bij'

lemma mem_iff (e : S ≃σ T) : y ∈ T ↔ ∃ x ∈ S, e x = y :=
  iff_of_eq (congrArg (y ∈ ·) e.bij.image_eq.symm)

theorem mem (σ : S ≃σ T) (h : x ∈ S) : σ.f x ∈ T :=
  σ.mem_iff.2 ⟨_, h, rfl⟩

@[refl]
def refl (S : Set Point) : S ≃σ S :=
  ⟨id, Set.bijOn_id S, false, fun _ _ _ _ _ _ => rfl⟩

def symm : S ≃σ T → T ≃σ S
  | ⟨f, bij, parity, hσ⟩ => by
    have inv := Set.BijOn.invOn_invFunOn bij |>.symm
    have bij := bij.symm inv
    refine ⟨f.invFunOn S, bij, parity, fun p hp q hq r hr => ?_⟩
    rw [hσ _ (bij.left hp) _ (bij.left hq) _ (bij.left hr),
      inv.left hp, inv.left hq, inv.left hr]
    simp

lemma symm_invOn (e : S ≃σ T) : Set.InvOn e.symm e S T :=
  e.bij.invOn_invFunOn

@[trans]
def trans : S ≃σ T → T ≃σ U → S ≃σ U
  | ⟨f, fbij, fp, fσ⟩, ⟨g, gbij, gp, gσ⟩ => by
    refine ⟨g ∘ f, gbij.comp fbij, xor fp gp, fun p hp q hq r hr => ?_⟩
    rw [fσ _ hp _ hq _ hr, gσ _ (fbij.left hp) _ (fbij.left hq) _ (fbij.left hr)]
    simp

@[simp]
theorem symm_apply_apply (e : S ≃σ T) (hp : p ∈ S) : e.symm (e p) = p := by
  rw [(symm_invOn e).left hp]

@[simp]
theorem apply_symm_apply (e : S ≃σ T) (hp : p ∈ T) : e (e.symm p) = p := by
  rw [(symm_invOn e).right hp]

end σEquiv

def OrientationProperty (P : Set Point → Prop) :=
  ∀ {{S T}}, S ≃σ T → P S → P T

theorem OrientationProperty.not : OrientationProperty P → OrientationProperty (¬P ·) := by
  unfold OrientationProperty
  intro h S T hσ hS hT
  exact hS (h hσ.symm hT)
