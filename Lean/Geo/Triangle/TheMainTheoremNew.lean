import Geo.PointsToWB.SymmetryBreakingNew
import Geo.Triangle.WBAssnNew
import Geo.Triangle.EncodingNew

namespace Geo
open Classical LeanSAT Model

axiom triangleCnfUnsat : (Geo.triangleEncoding 10 |>.toICnf compare).2.isUnsat

theorem EmptyTriangle10TheoremLists (pts : List Point) (gp : Point.PointListInGeneralPosition pts) (h : pts.length = 10) :
    HasEmptyNGon 3 pts.toFinset := by
  by_contra h'
  have noσtri : ¬σHasEmptyNGon 3 pts.toFinset := mt (σHasEmptyNGon_iff_HasEmptyNGon gp).1 h'
  have ⟨w, ⟨hw⟩⟩ := @symmetry_breaking pts (h ▸ by decide) gp
  have noσtri' : ¬σHasEmptyNGon 3 w.toFinset :=
    OrientationProperty_σHasEmptyNGon.not (hw.toEquiv w.nodup) noσtri
  have len10 : w.length = 10 := hw.length_eq.symm.trans h
  with_reducible have := (LeanSAT.PropForm.toICnf_sat _).2 ⟨w.toPropAssn, w.satisfies_triangleEncoding noσtri'⟩
  rw [len10] at this
  exact triangleCnfUnsat this

/- 'Geo.EmptyTriangle10TheoremLists' depends on axioms: [propext, Classical.choice, Quot.sound, Geo.cnfUnsat] -/
#print axioms EmptyTriangle10TheoremLists
