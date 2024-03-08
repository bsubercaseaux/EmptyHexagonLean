import Geo.PointsToWB.SymmetryBreakingNew
import Geo.Hexagon.WBAssnNew
import Geo.Hexagon.EncodingNew

namespace Geo
open Classical LeanSAT Model

axiom hexagonCnfUnsat : (Geo.hexagonEncoding 30 |>.toICnf compare).2.isUnsat

theorem EmptyHexagon30TheoremLists (pts : List Point) (gp : Point.PointListInGeneralPosition pts) (h : pts.length = 30) :
    HasEmptyNGon 6 pts.toFinset := by
  by_contra h'
  have noσtri : ¬σHasEmptyNGon 6 pts.toFinset := mt (σHasEmptyNGon_iff_HasEmptyNGon gp).1 h'
  have ⟨w, ⟨hw⟩⟩ := @symmetry_breaking pts (h ▸ by decide) gp
  have noσtri' : ¬σHasEmptyNGon 6 w.toFinset :=
    OrientationProperty_σHasEmptyNGon.not (hw.toEquiv w.nodup) noσtri
  have len10 : w.length = 30 := hw.length_eq.symm.trans h
  with_reducible have := (LeanSAT.PropForm.toICnf_sat _).2 ⟨w.toPropAssn, w.satisfies_hexagonEncoding noσtri'⟩
  rw [len10] at this
  exact hexagonCnfUnsat this

/- 'Geo.EmptyHexagon10TheoremLists' depends on axioms: [propext, Classical.choice, Quot.sound, Geo.cnfUnsat] -/
#print axioms EmptyHexagon30TheoremLists
