import Geo.Canonicalization.SymmetryBreaking
import Geo.Definitions.hNotation
import Geo.Gon.Assn
import Geo.Gon.Encoding

namespace Geo
open Classical LeanSAT Model

theorem gon_theorem (unsat : (Geo.gonCNF k (r+2)).isUnsat) : gonNumber k ≤ r + 3 := by
  refine gonNumber_le.2 fun pts h _ gp => by_contra fun h' => ?_
  have noσgon : ¬σHasConvexKGon k pts.toFinset := mt (σHasConvexKGon_iff_HasConvexKGon gp).1 h'
  have ⟨w, ⟨hw⟩⟩ := @symmetry_breaking pts (h ▸ Nat.le_add_left ..) gp
  have noσgon' : ¬σHasConvexKGon k w.toFinset :=
    OrientationProperty_σHasConvexKGon.not (hw.toEquiv w.nodup) noσgon
  have rlen9 : w.rlen = r+2 := Nat.succ_inj.1 <| hw.length_eq.symm.trans h
  apply unsat
  with_reducible
    have := (LeanSAT.PropForm.toICnf_sat _).2 ⟨w.toPropAssn _, w.satisfies_gonEncoding k noσgon'⟩
    rw [rlen9] at this
    rwa [gonCNF]
