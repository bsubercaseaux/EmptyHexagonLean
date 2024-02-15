import Geo.SAT.WBAssn
import Geo.SAT.Encoding
import Geo.SigmaEquiv

namespace Geo
open List
open Classical

def HasEmptyTriangle (pts : Set Point) : Prop :=
  ∃ p q r, [p, q, r].Nodup ∧ {p,q,r} ⊆ pts ∧ ∀ a ∈ pts, a ∉ ({p, q, r} : Set Point) → ¬PtInTriangle a p q r

def σHasEmptyTriangle (pts : Set Point) : Prop :=
  ∃ p q r, [p, q, r].Nodup ∧ {p,q,r} ⊆ pts ∧ ∀ a ∈ pts, a ∉ ({p, q, r} : Set Point) → ¬σPtInTriangle a p q r

/- JG: is this the right definition ^ or is below the right definition:

/-- `{p, q, r}` make up a triangle that contains no point in `S`. -/
def σIsEmptyTriangleFor (p q r : Point) (S : Set Point) :=
  Finset.card {p, q, r} = 3 ∧ -- TODO: maybe remove this part of the condition?
    ∀ a ∈ S, ¬σPtInTriangle' a p q r

def σHasEmptyTriangle (S : Set Point) : Prop :=
  ∃ p q r : S, σIsEmptyTriangleFor p q r S

-/


theorem σHasEmptyTriangle_iff {pts : Finset Point} (gp : Point.PointFinsetInGeneralPosition pts) :
    σHasEmptyTriangle pts ↔ HasEmptyTriangle pts := by
  unfold σHasEmptyTriangle HasEmptyTriangle
  apply exists_congr; intro p
  apply exists_congr; intro q
  apply exists_congr; intro r
  simp [-List.nodup_cons]; intro hnodup hsubset
  apply forall_congr'; intro a
  apply imp_congr_right; intro ha
  apply imp_congr_right; intro hane
  rw [σPtInTriangle_iff]
  intro a b c h
  apply gp
  trans
  · exact h
  · intro; aesop

lemma σPtInTriangle_of_σEquiv (f : S ≃σ T) (a p q r : S) :
    σPtInTriangle a p q r → σPtInTriangle (f a) (f p) (f q) (f r) := by
  simp only [σPtInTriangle, f.hσ]
  exact id


theorem OrientationProperty_σHasEmptyTriangle : OrientationProperty σHasEmptyTriangle := by
  intro S T f ⟨p, q, r, h, h'⟩
  stop -- JG: see comment below `σHasEmptyTriangle`
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


theorem fundamentalTheoremOfSymmetryBreaking {P : Set Point → Prop} {L : Finset Point} (gp : Point.PointFinsetInGeneralPosition L) :
    OrientationProperty P → P L →
    ∃ (w : WBPoints), w.length = L.card ∧ P w.points.toFinset := by
  sorry

open LeanSAT Encode in
theorem fromLeanSAT :
    ¬∃ (w : WBPoints), w.length = 10 ∧ ¬σHasEmptyTriangle w.points.toFinset := by
  have := cnfUnsat
  rw [VEncCNF.toICnf_equisatisfiable] at this
  simp at this ⊢
  intro w hw
  let τ := w.toPropAssn
  replace this := (hw.symm ▸ this) τ
  by_contra h
  apply this; clear this
  apply w.satisfies_noHoles
  sorry -- TODO(Wojciech?)


theorem EmptyTriangle10TheoremLists (pts : Finset Point) (gp : Point.PointFinsetInGeneralPosition pts) (h : pts.card = 10) :
    HasEmptyTriangle pts := by
  by_contra h'
  rw [← σHasEmptyTriangle_iff gp] at h'
  have ⟨w, hw, hw'⟩ := fundamentalTheoremOfSymmetryBreaking gp OrientationProperty_σHasEmptyTriangle.not h'
  apply fromLeanSAT
  use w, hw.trans h
