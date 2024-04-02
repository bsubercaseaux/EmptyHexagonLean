import Geo.Canonicalization.SymmetryBreaking
import Geo.Definitions.hNotation
import Geo.Hexagon.Assn
import Geo.Hexagon.Encoding

namespace Geo
open Classical LeanSAT Model

-- /-- This asserts that the CNF produced by `lake exe encode gon 6 17` is UNSAT -/
-- axiom unsat_6gon_cnf : (Geo.hexagonCNF (rlen := 17-1) (holes := false)).isUnsat

-- theorem gon_6_theorem (pts : List Point) (gp : Point.ListInGenPos pts)
--     (h : pts.length ≥ 17) : HasConvexKGon 6 pts.toFinset := by
--   refine HasConvexKGon_extension gp (fun pts gp h => ?_) h
--   by_contra h'
--   have noσgon : ¬σHasConvexKGon 6 pts.toFinset := mt (σHasConvexKGon_iff_HasConvexKGon gp).1 h'
--   have ⟨w, ⟨hw⟩⟩ := @symmetry_breaking pts (h ▸ by decide) gp
--   have noσgon' : ¬σHasEmptyKGonIf 6 (holes := false) w.toFinset :=
--     OrientationProperty_σHasConvexKGon.not (hw.toEquiv w.nodup) noσgon
--   have rlen_eq : w.rlen = 16 := Nat.succ_inj.1 <| hw.length_eq.symm.trans h
--   apply unsat_6gon_cnf
--   with_reducible
--     have := (PropForm.toICnf_sat _).2 ⟨w.toPropAssn false, w.satisfies_hexagonEncoding noσgon'⟩
--     rw [rlen_eq] at this
--     rwa [hexagonCNF]

variable (unsat_6hole_cnf : (Geo.hexagonCNF (rlen := 30-1) (holes := true)).isUnsat) in
theorem hole_6_theorem : holeNumber 6 ≤ 30 := by
  refine holeNumber_le.2 fun pts h _ gp => by_contra fun h' => ?_
  have noσtri : ¬σHasEmptyKGon 6 pts.toFinset := mt (σHasEmptyKGon_iff_HasEmptyKGon gp).1 h'
  have ⟨w, ⟨hw⟩⟩ := @symmetry_breaking pts (h ▸ by decide) gp
  have noσtri' : ¬σHasEmptyKGonIf 6 (holes := true) w.toFinset :=
    OrientationProperty_σHasEmptyKGon.not (hw.toEquiv w.nodup) noσtri
  have rlen29 : w.rlen = 29 := Nat.succ_inj.1 <| hw.length_eq.symm.trans h
  apply unsat_6hole_cnf
  with_reducible
    have := (PropForm.toICnf_sat _).2 ⟨w.toPropAssn, w.satisfies_hexagonEncoding noσtri'⟩
    rw [rlen29] at this
    rwa [hexagonCNF]
