import Geo.Canonicalization.SymmetryBreaking
import Geo.Hexagon.GonAssn
import Geo.Hexagon.GonEncoding

namespace Geo
open Classical LeanSAT Model

axiom unsat_6gon_cnf : (Geo.hexagonCNF' (rlen := 17-1)).isUnsat

theorem gon_6_theorem (pts : List Point) (gp : Point.ListInGenPos pts)
    (h : pts.length ≥ 17) : HasConvexKGon 6 pts.toFinset := by
  refine HasConvexKGon_extension gp (fun pts gp h => ?_) h
  by_contra h'
  have noσgon : ¬σHasConvexKGon 6 pts.toFinset := mt (σHasConvexKGon_iff_HasConvexKGon gp).1 h'
  have ⟨w, ⟨hw⟩⟩ := @symmetry_breaking pts (h ▸ by decide) gp
  have noσgon' : ¬σHasConvexKGon 6 w.toFinset :=
    OrientationProperty_σHasConvexKGon.not (hw.toEquiv w.nodup) noσgon
  have rlen_eq : w.rlen = 16 := Nat.succ_inj.1 <| hw.length_eq.symm.trans h
  apply unsat_6gon_cnf
  with_reducible
    have := (PropForm.toICnf_sat _).2 ⟨w.toPropAssn False, w.satisfies_hexagonEncoding' noσgon'⟩
    rw [rlen_eq] at this
    rwa [hexagonCNF']

/--
info: 'Geo.gon_6_theorem' depends on axioms:
[propext, Classical.choice, Quot.sound, Geo.unsat_6gon_cnf, mathlibSorry]
-/
#guard_msgs in #print axioms gon_6_theorem
