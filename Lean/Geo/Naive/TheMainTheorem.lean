import Geo.Canonicalization.SymmetryBreaking
import Geo.Naive.Assn
import Geo.Naive.Encoding

namespace Geo
open Classical LeanSAT Model

theorem empty_kgon_naive (rlen_le : 2 ≤ rlen) (unsat : (Geo.naiveCNF k rlen).isUnsat)
    (pts : List Point) (gp : Point.ListInGenPos pts)
    (h : pts.length ≥ rlen+1) : HasEmptyKGon k pts.toFinset := by
  refine HasEmptyKGon_extension gp (fun pts gp h => ?_) (Nat.succ_le_succ rlen_le) h
  by_contra h'
  have noσtri : ¬σHasEmptyKGon k pts.toFinset := mt (σHasEmptyKGon_iff_HasEmptyKGon gp).1 h'
  have ⟨w, ⟨hw⟩⟩ := @symmetry_breaking pts (h ▸ Nat.succ_le_succ rlen_le) gp
  have noσtri' : ¬σHasEmptyKGon k w.toFinset :=
    OrientationProperty_σHasEmptyKGon.not (hw.toEquiv w.nodup) noσtri
  have rlen9 : w.rlen = rlen := Nat.succ_inj.1 <| hw.length_eq.symm.trans h
  apply unsat
  with_reducible
    have := (LeanSAT.PropForm.toICnf_sat _).2 ⟨w.toPropAssn, w.satisfies_naiveEncoding k noσtri'⟩
    rw [rlen9] at this
    rwa [naiveCNF]

axiom unsat_3hole_cnf : (Geo.naiveCNF (k := 3) (rlen := 3-1)).isUnsat

theorem hole_3_theorem : ∀ (pts : List Point),
    Point.ListInGenPos pts → pts.length ≥ 3 → HasEmptyKGon 3 pts.toFinset :=
  empty_kgon_naive (by decide) unsat_3hole_cnf

axiom unsat_4hole_cnf : (Geo.naiveCNF (k := 4) (rlen := 5-1)).isUnsat

theorem hole_4_theorem : ∀ (pts : List Point),
    Point.ListInGenPos pts → pts.length ≥ 5 → HasEmptyKGon 4 pts.toFinset :=
  empty_kgon_naive (by decide) unsat_4hole_cnf

axiom unsat_5hole_cnf : (Geo.naiveCNF (k := 5) (rlen := 10-1)).isUnsat

theorem hole_5_theorem : ∀ (pts : List Point),
    Point.ListInGenPos pts → pts.length ≥ 10 → HasEmptyKGon 5 pts.toFinset :=
  empty_kgon_naive (by decide) unsat_5hole_cnf

/--
info: 'Geo.hole_3_theorem' depends on axioms:
[propext, Classical.choice, Quot.sound, mathlibSorry, Geo.unsat_3hole_cnf]
-/
#guard_msgs in #print axioms hole_3_theorem

/--
info: 'Geo.hole_4_theorem' depends on axioms:
[propext, Classical.choice, Quot.sound, mathlibSorry, Geo.unsat_4hole_cnf]
-/
#guard_msgs in #print axioms hole_4_theorem

/--
info: 'Geo.hole_5_theorem' depends on axioms:
[propext, Classical.choice, Quot.sound, mathlibSorry, Geo.unsat_5hole_cnf]
-/
#guard_msgs in #print axioms hole_5_theorem
