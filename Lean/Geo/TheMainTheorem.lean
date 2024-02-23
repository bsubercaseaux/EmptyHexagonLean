import Geo.SAT.WBAssn
import Geo.SAT.Encoding
import Geo.PointsToWB.SymmetryBreakingNew
import Geo.SigmaEquiv

namespace Geo
open List
open Classical

lemma HasEmptyTriangle_of_σHasEmptyTriangle (gp : Point.PointListInGeneralPosition pts) :
    σHasEmptyTriangle pts.toFinset → HasEmptyTriangle pts.toFinset := by
  intro ⟨a, ha, b, hb, c, hc, ab, ac, bc, empty⟩
  rw [HasEmptyTriangle.iff]
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
  have noσtri : ¬σHasEmptyTriangle pts.toFinset := fun h => h' <| HasEmptyTriangle_of_σHasEmptyTriangle gp h
  have ⟨w, hw⟩ := @symmetry_breaking pts (by omega) gp
  have noσtri' : ¬σHasEmptyTriangle w.toFinset :=
    hw.elim fun e => OrientationProperty_σHasEmptyTriangle.not (e.toEquiv w.nodup) noσtri
  have len10 : w.length = 10 := hw.elim fun e => e.length_eq.symm.trans h
  have := cnfUnsat
  rw [LeanSAT.Encode.VEncCNF.toICnf_equisatisfiable, ← len10] at this
  apply this
  exact ⟨_, w.satisfies_noHoles noσtri'⟩

/- 'Geo.EmptyTriangle10TheoremLists' depends on axioms: [propext, Classical.choice, Quot.sound, Geo.cnfUnsat] -/
#print axioms EmptyTriangle10TheoremLists
