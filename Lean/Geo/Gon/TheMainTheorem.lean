import Geo.Canonicalization.SymmetryBreaking
import Geo.Gon.Assn
import Geo.Gon.Encoding

namespace Geo
open Classical LeanSAT Model

theorem gon_theorem (rlen_le : 2 ≤ rlen) (unsat : (Geo.gonCNF k rlen).isUnsat)
    (pts : List Point) (gp : Point.ListInGenPos pts)
    (h : pts.length ≥ rlen+1) : HasConvexKGon k pts.toFinset := by
  refine HasConvexKGon_extension gp (fun pts gp h => ?_) h
  by_contra h'
  have noσgon : ¬σHasConvexKGon k pts.toFinset := mt (σHasConvexKGon_iff_HasConvexKGon gp).1 h'
  have ⟨w, ⟨hw⟩⟩ := @symmetry_breaking pts (h ▸ Nat.succ_le_succ rlen_le) gp
  have noσgon' : ¬σHasConvexKGon k w.toFinset :=
    OrientationProperty_σHasConvexKGon.not (hw.toEquiv w.nodup) noσgon
  have rlen9 : w.rlen = rlen := Nat.succ_inj.1 <| hw.length_eq.symm.trans h
  apply unsat
  with_reducible
    have := (LeanSAT.PropForm.toICnf_sat _).2 ⟨w.toPropAssn _, w.satisfies_gonEncoding k noσgon'⟩
    rw [rlen9] at this
    rwa [gonCNF]

/-- This asserts that the CNF produced by `lake exe encode gon 3 3` is UNSAT -/
axiom unsat_3gon_cnf : (Geo.gonCNF (k := 3) (rlen := 3-1)).isUnsat

theorem gon_3_theorem : ∀ (pts : List Point),
    Point.ListInGenPos pts → pts.length ≥ 3 → HasConvexKGon 3 pts.toFinset :=
  gon_theorem (by decide) unsat_3gon_cnf

/-- This asserts that the CNF produced by `lake exe encode gon 4 5` is UNSAT -/
axiom unsat_4gon_cnf : (Geo.gonCNF (k := 4) (rlen := 5-1)).isUnsat

theorem gon_4_theorem : ∀ (pts : List Point),
    Point.ListInGenPos pts → pts.length ≥ 5 → HasConvexKGon 4 pts.toFinset :=
  gon_theorem (by decide) unsat_4gon_cnf

/-- This asserts that the CNF produced by `lake exe encode gon 5 9` is UNSAT -/
axiom unsat_5gon_cnf : (Geo.gonCNF (k := 5) (rlen := 9-1)).isUnsat

theorem gon_5_theorem : ∀ (pts : List Point),
    Point.ListInGenPos pts → pts.length ≥ 9 → HasConvexKGon 5 pts.toFinset :=
  gon_theorem (by decide) unsat_5gon_cnf

/-- This asserts that the CNF produced by `lake exe encode gon 6 17` is UNSAT -/
axiom unsat_6gon_cnf : (Geo.gonCNF (k := 6) (rlen := 17-1)).isUnsat

theorem gon_6_theorem : ∀ (pts : List Point),
    Point.ListInGenPos pts → pts.length ≥ 17 → HasConvexKGon 6 pts.toFinset :=
  gon_theorem (by decide) unsat_6gon_cnf

/--
info: 'Geo.gon_3_theorem' depends on axioms:
[propext, Classical.choice, Quot.sound, mathlibSorry, Geo.unsat_3gon_cnf]
-/
#guard_msgs in #print axioms gon_3_theorem

/--
info: 'Geo.gon_4_theorem' depends on axioms:
[propext, Classical.choice, Quot.sound, mathlibSorry, Geo.unsat_4gon_cnf]
-/
#guard_msgs in #print axioms gon_4_theorem

/--
info: 'Geo.gon_5_theorem' depends on axioms:
[propext, Classical.choice, Quot.sound, mathlibSorry, Geo.unsat_5gon_cnf]
-/
#guard_msgs in #print axioms gon_5_theorem

/--
info: 'Geo.gon_6_theorem' depends on axioms:
[propext, Classical.choice, Quot.sound, mathlibSorry, Geo.unsat_6gon_cnf]
-/
#guard_msgs in #print axioms gon_6_theorem
