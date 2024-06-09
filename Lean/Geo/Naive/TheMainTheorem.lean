import Geo.Canonicalization.SymmetryBreaking
import Geo.Definitions.hNotation
import Geo.Naive.Assn
import Geo.Naive.Encoding

namespace Geo
open Classical LeanSAT Model

theorem empty_kgon_naive (unsat : (Geo.naiveCNF k (r+2)).isUnsat) : holeNumber k ≤ r + 3 := by
  refine holeNumber_le.2 fun pts h _ gp => by_contra fun h' => ?_
  have noσtri : ¬σHasEmptyKGon k pts.toFinset := mt (σHasEmptyKGon_iff_HasEmptyKGon gp.toFinset).1 h'
  have ⟨w, ⟨hw⟩⟩ := @symmetry_breaking pts (h ▸ Nat.le_add_left ..) gp
  have noσtri' : ¬σHasEmptyKGon k w.toFinset :=
    OrientationProperty_σHasEmptyKGon.not (hw.toEquiv w.nodup) noσtri
  have rlen9 : w.rlen = r+2 := Nat.succ_inj.1 <| hw.length_eq.symm.trans h
  apply unsat
  with_reducible
    have := (LeanSAT.PropForm.toICnf_sat _).2 ⟨w.toPropAssn, w.satisfies_naiveEncoding k noσtri'⟩
    rw [rlen9] at this
    rwa [naiveCNF]
