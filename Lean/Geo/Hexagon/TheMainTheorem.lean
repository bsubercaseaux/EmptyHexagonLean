import Geo.Canonicalization.SymmetryBreaking
import Geo.Definitions.hNotation
import Geo.Hexagon.Assn
import Geo.Hexagon.Encoding

namespace Geo
open Classical LeanSAT Model

variable (unsat_6hole_cnf : (Geo.hexagonCNF (rlen := 30-1) (holes := true)).isUnsat)

theorem hole_6_theorem : ∀ (pts : Finset Point),
    Point.SetInGenPos pts → pts.card = 30 → HasEmptyKGon 6 pts := by
  intro pts gp h
  by_contra h'
  have noσtri : ¬σHasEmptyKGon 6 pts := mt (σHasEmptyKGon_iff_HasEmptyKGon gp).1 h'
  have ⟨w, ⟨hw⟩⟩ := @symmetry_breaking pts.toList (by simp [h]) gp.toList
  have noσtri' : ¬σHasEmptyKGonIf 6 (holes := true) w.toFinset :=
    OrientationProperty_σHasEmptyKGon.not (hw.toEquiv w.nodup) (by simpa using noσtri)
  have rlen29 : w.rlen = 29 := Nat.succ_inj.1 <| hw.length_eq.symm.trans (by simp; simpa using h)
  apply unsat_6hole_cnf
  with_reducible
    have := (PropForm.toICnf_sat _).2 ⟨w.toPropAssn, w.satisfies_hexagonEncoding noσtri'⟩
    rw [rlen29] at this
    rwa [hexagonCNF]

theorem hole_6_theorem' : holeNumber 6 ≤ ↑(30 : Nat) := by
  rw [holeNumber_le]
  intro pts h nodup genpos
  apply hole_6_theorem
  · exact unsat_6hole_cnf
  · apply genpos.toFinset
  · rw [List.toFinset_card_of_nodup nodup]; exact h
