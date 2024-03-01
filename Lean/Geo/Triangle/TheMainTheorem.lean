import Geo.PointsToWB.SymmetryBreakingNew
import Geo.SigmaEquiv
import Geo.Definitions.OrientationProperties

import Geo.Triangle.WBAssn
import Geo.Triangle.Encoding

namespace Geo
open List
open Classical


open LeanSAT.Model.PropFun in
theorem EmptyTriangle10TheoremLists (pts : List Point) (gp : Point.PointListInGeneralPosition pts) (h : pts.length = 10) :
    HasEmptyTriangle pts.toFinset := by
  by_contra h'
  have noσtri : ¬σHasEmptyTriangle pts.toFinset := mt (HasEmptyTriangle_iff_σHasEmptyTriangle gp).1 h'
  have ⟨w, ⟨hw⟩⟩ := @symmetry_breaking pts (h ▸ by decide) gp
  have noσtri' : ¬σHasEmptyTriangle w.toFinset :=
    OrientationProperty_σHasEmptyTriangle.not (hw.toEquiv w.nodup) noσtri
  have len10 : w.length = 10 := hw.length_eq.symm.trans h
  have := cnfUnsat
  rw [LeanSAT.Encode.VEncCNF.toICnf_equisatisfiable, ← len10] at this
  apply this
  exact ⟨_, w.satisfies_noHoles noσtri'⟩

/- 'Geo.EmptyTriangle10TheoremLists' depends on axioms: [propext, Classical.choice, Quot.sound, Geo.cnfUnsat] -/
#print axioms EmptyTriangle10TheoremLists
