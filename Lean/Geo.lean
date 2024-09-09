import Geo.Naive.TheMainTheorem
import Geo.Gon.TheMainTheorem
import Geo.Hexagon.TheMainTheorem
import Geo.LowerBound.HoleCheckerProof

/-! ## The definitions involved in the Empty Hexagon theorem -/

/- We work over the Euclidean plane `ℝ²`. -/
recall Geo.Point := Fin 2 → ℝ

/- `EmptyShapeIn S P` means that `S` carves out an empty shape in `P`:
the convex hull of `S` contains no point of `P`
other than those already in `S`. -/
recall Geo.EmptyShapeIn (S P : Set Point) : Prop :=
  ∀ p ∈ P \ S, p ∉ convexHull ℝ S

/- `ConvexIndep S` means that `S` consists of extremal points of its convex hull,
i.e. the point set encloses a convex polygon. Also known as a "convex-independent set". -/
recall Geo.ConvexIndep (S : Set Point) : Prop :=
  ∀ a ∈ S, a ∉ convexHull ℝ (S \ {a})

recall Geo.HasConvexKGon (n : Nat) (P : Set Point) : Prop :=
  ∃ S : Finset Point, S.card = n ∧ ↑S ⊆ P ∧ ConvexIndep S

recall Geo.HasEmptyKGon (n : Nat) (P : Set Point) : Prop :=
  ∃ S : Finset Point, S.card = n ∧ ↑S ⊆ P ∧ ConvexIndep S ∧ EmptyShapeIn S P

/- `gonNumber k` is the smallest number `n` such that every set of `n` or more points
in general position contains a convex-independent set of size `k`. -/
recall Geo.gonNumber (k : Nat) : ENat :=
  sInf { n | ∀ (pts : Finset Point), pts.card = n → Point.SetInGenPos pts → HasConvexKGon k pts }

/- `holeNumber k` is the smallest number `n` such that every set of `n` or more points
in general position contains an empty convex-independent set of size `k`. -/
recall Geo.holeNumber (k : Nat) : ENat :=
  sInf { n | ∀ (pts : Finset Point), pts.card = n → Point.SetInGenPos pts → HasEmptyKGon k pts }

namespace Geo
open HoleChecker

/-! ## Smaller values of `gonNumber` and `holeNumber` -/

/-- This asserts that the CNF produced by `lake exe encode gon 3 3` is UNSAT -/
axiom unsat_3gon_cnf : (Geo.gonCNF (k := 3) (rlen := 3-1)).isUnsat

theorem gonNumber_3 : gonNumber 3 = 3 :=
  le_antisymm (gon_theorem unsat_3gon_cnf) (gon_lower_bound [(1, 0), (2, 1)])

/-- This asserts that the CNF produced by `lake exe encode gon 4 5` is UNSAT -/
axiom unsat_4gon_cnf : (Geo.gonCNF (k := 4) (rlen := 5-1)).isUnsat

theorem gonNumber_4 : gonNumber 4 = 5 :=
  le_antisymm (gon_theorem unsat_4gon_cnf) (gon_lower_bound [(1, 0), (2, 4), (3, 2), (4, 1)])

/-- This asserts that the CNF produced by `lake exe encode gon 5 9` is UNSAT -/
axiom unsat_5gon_cnf : (Geo.gonCNF (k := 5) (rlen := 9-1)).isUnsat

theorem gonNumber_5 : gonNumber 5 = 9 :=
  le_antisymm (gon_theorem unsat_5gon_cnf) (gon_lower_bound
    [(1, 3), (2, 0), (3, 2), (4, 1), (6, 3), (7, 1), (8, 4), (9, 0)])

/-- This asserts that the CNF produced by `lake exe encode gon 6 17` is UNSAT -/
axiom unsat_6gon_cnf : (Geo.gonCNF (k := 6) (rlen := 17-1)).isUnsat

theorem gonNumber_6 : gonNumber 6 = 17 :=
  le_antisymm (gon_theorem unsat_6gon_cnf) (gon_lower_bound [
    (1, 7), (4, 9), (5, 19), (6, 11), (7, 14), (20, 8), (22, 9), (23, 10),
    (24, 0), (25, 3), (26, 5), (34, 19), (35, 15), (36, 13), (37, 12), (43, 7)
  ])

/-- This asserts that the CNF produced by `lake exe encode hole 3 3` is UNSAT -/
axiom unsat_3hole_cnf : (Geo.naiveCNF (k := 3) (rlen := 3-1)).isUnsat

theorem holeNumber_3 : holeNumber 3 = 3 :=
  le_antisymm (empty_kgon_naive unsat_3hole_cnf) (hole_lower_bound [(1, 0), (2, 1)])

/-- This asserts that the CNF produced by `lake exe encode hole 4 5` is UNSAT -/
axiom unsat_4hole_cnf : (Geo.naiveCNF (k := 4) (rlen := 5-1)).isUnsat

theorem holeNumber_4 : holeNumber 4 = 5 :=
  le_antisymm (empty_kgon_naive unsat_4hole_cnf) (hole_lower_bound
    [(1, 0), (2, 4), (3, 2), (4, 1)])

/-- This asserts that the CNF produced by `lake exe encode hole 5 10` is UNSAT -/
axiom unsat_5hole_cnf : (Geo.naiveCNF (k := 5) (rlen := 10-1)).isUnsat

theorem holeNumber_5 : holeNumber 5 = 10 :=
  le_antisymm (empty_kgon_naive unsat_5hole_cnf) (hole_lower_bound
    [(1, 0), (6, 4), (9, 7), (11, 2), (12, 3), (13, 1), (14, 2), (17, 4), (28, 0)])

/-! ## The main theorem -/

/-- This asserts that the CNF produced by `lake exe encode hole 6 30` is UNSAT -/
axiom unsat_6hole_cnf : (Geo.hexagonCNF (rlen := 30-1) (holes := true)).isUnsat

/--
**The Empty Hexagon Number**: Every set of `30` or more points in general position
(and no fewer) contains an empty hexagon.
-/
theorem holeNumber_6 : holeNumber 6 = 30 :=
  le_antisymm (hole_6_theorem' unsat_6hole_cnf) (hole_lower_bound [
    (1, 1260), (16, 743), (22, 531), (37, 0), (306, 592), (310, 531), (366, 552), (371, 487),
    (374, 525), (392, 575), (396, 613), (410, 539), (416, 550), (426, 526), (434, 552), (436, 535),
    (446, 565), (449, 518), (450, 498), (453, 542), (458, 526), (489, 537), (492, 502), (496, 579),
    (516, 467), (552, 502), (754, 697), (777, 194), (1259, 320)
  ])

end Geo

/-! ## Axiom checks -/

open Geo

/--
info: 'Geo.gonNumber_3' depends on axioms: [Classical.choice,
 propext,
 Quot.sound,
 mathlibSorry,
 Geo.unsat_3gon_cnf,
 Lean.ofReduceBool]
-/
#guard_msgs in #print axioms gonNumber_3

/--
info: 'Geo.gonNumber_4' depends on axioms: [Classical.choice,
 propext,
 Quot.sound,
 mathlibSorry,
 Geo.unsat_4gon_cnf,
 Lean.ofReduceBool]
-/
#guard_msgs in #print axioms gonNumber_4

/--
info: 'Geo.gonNumber_5' depends on axioms: [Classical.choice,
 propext,
 Quot.sound,
 mathlibSorry,
 Geo.unsat_5gon_cnf,
 Lean.ofReduceBool]
-/
#guard_msgs in #print axioms gonNumber_5

/--
info: 'Geo.gonNumber_6' depends on axioms: [Classical.choice,
 propext,
 Quot.sound,
 mathlibSorry,
 Geo.unsat_6gon_cnf,
 Lean.ofReduceBool]
-/
#guard_msgs in #print axioms gonNumber_6

/--
info: 'Geo.holeNumber_3' depends on axioms: [Classical.choice,
 propext,
 Quot.sound,
 mathlibSorry,
 Geo.unsat_3hole_cnf,
 Lean.ofReduceBool]
-/
#guard_msgs in #print axioms holeNumber_3

/--
info: 'Geo.holeNumber_4' depends on axioms: [Classical.choice,
 propext,
 Quot.sound,
 mathlibSorry,
 Geo.unsat_4hole_cnf,
 Lean.ofReduceBool]
-/
#guard_msgs in #print axioms holeNumber_4

/--
info: 'Geo.holeNumber_5' depends on axioms: [Classical.choice,
 propext,
 Quot.sound,
 mathlibSorry,
 Geo.unsat_5hole_cnf,
 Lean.ofReduceBool]
-/
#guard_msgs in #print axioms holeNumber_5

/--
info: 'Geo.holeNumber_6' depends on axioms: [Classical.choice,
 propext,
 Quot.sound,
 mathlibSorry,
 Geo.unsat_6hole_cnf,
 Lean.ofReduceBool]
-/
#guard_msgs in #print axioms holeNumber_6
