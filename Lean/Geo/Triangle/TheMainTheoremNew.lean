import Geo.PointsToWB.SymmetryBreakingNew
import Geo.Triangle.WBAssnNew
import Geo.Triangle.EncodingNew

namespace Geo
open Classical LeanSAT Model

axiom triangleCnfUnsat : (Geo.triangleCNF 10).isUnsat

theorem EmptyTriangle10TheoremLists (pts : List Point) (gp : Point.PointListInGeneralPosition pts)
    (h : pts.length ≥ 10) : HasEmptyNGon 3 pts.toFinset := by
  refine HasEmptyNGon_extension gp (fun pts gp h => ?_) (by decide) h
  by_contra h'
  have noσtri : ¬σHasEmptyNGon 3 pts.toFinset := mt (σHasEmptyNGon_iff_HasEmptyNGon gp).1 h'
  have ⟨w, ⟨hw⟩⟩ := @symmetry_breaking pts (h ▸ by decide) gp
  have noσtri' : ¬σHasEmptyNGon 3 w.toFinset :=
    OrientationProperty_σHasEmptyNGon.not (hw.toEquiv w.nodup) noσtri
  have len10 : w.length = 10 := hw.length_eq.symm.trans h
  apply triangleCnfUnsat
  with_reducible
    have := (LeanSAT.PropForm.toICnf_sat _).2 ⟨w.toPropAssn, w.satisfies_triangleEncoding noσtri'⟩
    rw [len10] at this
    rwa [triangleCNF]

/-
'Geo.EmptyTriangle10TheoremLists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Geo.triangleCnfUnsat,
 mathlibSorry]
-/
#print axioms EmptyTriangle10TheoremLists
