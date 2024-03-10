import Geo.PointsToWB.SymmetryBreakingNew
import Geo.Hexagon.WBAssnNew
import Geo.Hexagon.EncodingNew

namespace Geo
open Classical LeanSAT Model

axiom hexagonCnfUnsat : (Geo.hexagonCNF 30).isUnsat

theorem EmptyHexagon30TheoremLists (pts : List Point) (gp : Point.PointListInGeneralPosition pts)
    (h : pts.length ≥ 30) : HasEmptyNGon 6 pts.toFinset := by
  refine HasEmptyNGon_extension gp (fun pts gp h => ?_) (by decide) h
  by_contra h'
  have noσtri : ¬σHasEmptyNGon 6 pts.toFinset := mt (σHasEmptyNGon_iff_HasEmptyNGon gp).1 h'
  have ⟨w, ⟨hw⟩⟩ := @symmetry_breaking pts (h ▸ by decide) gp
  have noσtri' : ¬σHasEmptyNGon 6 w.toFinset :=
    OrientationProperty_σHasEmptyNGon.not (hw.toEquiv w.nodup) noσtri
  have len10 : w.length = 30 := hw.length_eq.symm.trans h
  apply hexagonCnfUnsat
  with_reducible
    have := (PropForm.toICnf_sat _).2 ⟨w.toPropAssn, w.satisfies_hexagonEncoding noσtri'⟩
    rw [len10] at this
    rwa [hexagonCNF]

/-
'Geo.EmptyHexagon30TheoremLists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Geo.hexagonCnfUnsat,
 mathlibSorry]
-/
#print axioms EmptyHexagon30TheoremLists
