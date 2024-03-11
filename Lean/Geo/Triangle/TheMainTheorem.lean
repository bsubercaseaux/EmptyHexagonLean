import Geo.Canonicalization.SymmetryBreaking
import Geo.Triangle.Assn
import Geo.Triangle.Encoding

namespace Geo
open Classical LeanSAT Model

axiom triangleCnfUnsat : (Geo.triangleCNF 10).isUnsat

theorem EmptyTriangle10TheoremLists (pts : List Point) (gp : Point.PointListInGeneralPosition pts)
    (h : pts.length ≥ 10) : HasEmptyKGon 3 pts.toFinset := by
  refine HasEmptyKGon_extension gp (fun pts gp h => ?_) (by decide) h
  by_contra h'
  have noσtri : ¬σHasEmptyKGon 3 pts.toFinset := mt (σHasEmptyKGon_iff_HasEmptyKGon gp).1 h'
  have ⟨w, ⟨hw⟩⟩ := @symmetry_breaking pts (h ▸ by decide) gp
  have noσtri' : ¬σHasEmptyKGon 3 w.toFinset :=
    OrientationProperty_σHasEmptyKGon.not (hw.toEquiv w.nodup) noσtri
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
