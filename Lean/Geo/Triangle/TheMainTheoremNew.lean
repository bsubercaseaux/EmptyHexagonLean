import Geo.PointsToWB.SymmetryBreakingNew
import Geo.SigmaEquiv

import Geo.Triangle.WBAssnNew
import Geo.Triangle.EncodingNew

namespace Geo
open List
open Classical

lemma HasEmptyTriangle_iff_σHasEmptyTriangle (gp : Point.PointListInGeneralPosition pts) :
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
    simp only [coe_toFinset, Set.mem_diff, Set.mem_setOf_eq, Set.mem_insert_iff,
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

lemma OrientationProperty_σHasEmptyTriangle : OrientationProperty σHasEmptyTriangle := by
  unfold σHasEmptyTriangle
  intro S T ST ⟨a, ha, b, hb, c, hc, ab, ac, bc, empty⟩
  refine ⟨ST ⟨a, ha⟩, Subtype.property _, ST ⟨b, hb⟩, Subtype.property _, ST ⟨c, hc⟩, Subtype.property _, ?_⟩
  simp [Subtype.coe_injective.eq_iff, ab, ac, bc]
  intro s hs ⟨tri₁, tri₂, tri₃⟩
  apply empty (ST.symm ⟨s, hs⟩) (Subtype.property _)
  refine ⟨?_, ?_, ?_⟩
  . have := ST.symm.hσ (ST ⟨a, ha⟩) (ST ⟨b, hb⟩) ⟨s, hs⟩
    rw [this] at tri₁
    have := ST.hσ ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩
    have := tri₁.trans this.symm
    simpa using this
  . have := ST.symm.hσ (ST ⟨a, ha⟩) (ST ⟨c, hc⟩) ⟨s, hs⟩
    rw [this] at tri₂
    have := ST.hσ ⟨a, ha⟩ ⟨c, hc⟩ ⟨b, hb⟩
    have := tri₂.trans this.symm
    simpa using this
  . have := ST.symm.hσ (ST ⟨b, hb⟩) (ST ⟨c, hc⟩) ⟨s, hs⟩
    rw [this] at tri₃
    have := ST.hσ ⟨b, hb⟩ ⟨c, hc⟩ ⟨a, ha⟩
    have := tri₃.trans this.symm
    simpa using this

open LeanSAT.Model.PropFun in
theorem EmptyTriangle10TheoremLists (pts : List Point) (gp : Point.PointListInGeneralPosition pts) (h : pts.length = 10) :
    HasEmptyTriangle pts.toFinset := by
  by_contra h'
  have noσtri : ¬σHasEmptyTriangle pts.toFinset := mt (HasEmptyTriangle_iff_σHasEmptyTriangle gp).1 h'
  have ⟨w, ⟨hw⟩⟩ := @symmetry_breaking pts (h ▸ by decide) gp
  have noσtri' : ¬σHasEmptyTriangle w.toFinset :=
    OrientationProperty_σHasEmptyTriangle.not (hw.toEquiv w.nodup) noσtri
  have len10 : w.length = 10 := hw.length_eq.symm.trans h
  with_reducible have := (LeanSAT.PropForm.toICnf_sat _).2 ⟨w.toPropAssn, w.satisfies_noHoles noσtri'⟩
  rw [len10] at this
  exact cnfUnsat this

/- 'Geo.EmptyTriangle10TheoremLists' depends on axioms: [propext, Classical.choice, Quot.sound, Geo.cnfUnsat] -/
#print axioms EmptyTriangle10TheoremLists
