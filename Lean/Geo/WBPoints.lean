import LeanSAT.Model.PropFun
import Geo.Point
import Geo.Orientations
import Geo.Formula

namespace Geo

noncomputable section
open Point

theorem nodup_of_gp (l : List Point) :
    3 < l.length → PointListInGeneralPosition l → l.Nodup :=
  sorry

/-- A well-behaved list of points: in general position, sorted by `x`. -/
structure WBPoints where
  points : List Point
  sorted : PointListSorted points
  gp : PointListInGeneralPosition points
  -- ccw : SortedCCW

def finset_sort (S : Finset Point) : List Point :=
  S.toList.insertionSort (·.x <= ·.x)

theorem finset_sort_sorted (S : Finset Point) : (finset_sort S).Sorted (·.x <= ·.x) :=
  List.sorted_insertionSort (·.x <= ·.x) (S.toList)

namespace WBPoints
open List Finset Classical
open LeanSAT Model PropFun

def toFinset (w : WBPoints) : Finset Point := w.points.toFinset

def fromFinset {S : Finset Point} (hS : PointFinsetInGeneralPosition S)
    (hX : Set.Pairwise S.toSet (·.x ≠ ·.x)) : WBPoints :=
  { points := finset_sort S
    -- nodup := (Perm.nodup_iff (perm_insertionSort _ _)).mpr (Finset.nodup_toList S)
    sorted := by
      unfold PointListSorted Sorted
      rw [List.Pairwise.imp_mem]
      have := List.sorted_insertionSort (·.x ≤ ·.x) (toList S)
      unfold Sorted at this
      sorry
      done
    gp := by
      sorry
      done}

theorem nodupX (w : WBPoints) : w.points.Pairwise (·.x ≠ ·.x) :=
  Pairwise.imp ne_of_lt w.sorted

theorem nodup (w : WBPoints) : w.points.Nodup :=
  w.nodupX.imp fun hx h => by rw [h] at hx; contradiction

abbrev length (w : WBPoints) : Nat := w.points.length

instance : GetElem WBPoints Nat Point (fun w i => i < w.length) where
  getElem w i h := w.points[i]'h

/-
/-- If `p < a,q < r` and `a ≠ q`, this means that
the `a`-th point is contained in the triangle `pqr`.
Otherwise it probably means something but we don't care what. -/
-- NOTE(WN): we may have to enforce the ordering restrictions,
-- but I am not currently seeing where that is needed
--  so I left the `def` without them for simplicity.
def isInTriangle (w : WBPoints) (a p q r : Fin w.length) : Prop :=
  σ w[p] w[q] w[r] = σ w[p] w[a] w[r] ∧
  σ w[p] w[a] w[q] = σ w[p] w[r] w[q] ∧
  σ w[p] w[a] w[r] = σ w[q] w[p] w[r]

/-- Aka a 3-hole. -/
def isEmptyTriangle (w : WBPoints) (p q r : Fin w.length) : Prop :=
  ∀ (x : Fin w.length), ¬w.isInTriangle x p q r
  -/

-- NOTE(WN): an attempt at going straight to the `PropAssn` from `WBPoints`.
-- We also discussed going through an intermediate `(OrderedTriple n → Orientation)` function.
-- I am hoping avoiding it will simplify things.
-- def toPropAssn (w : WBPoints) : PropAssignment (Var w.length)
--   | .sigma a b c ..    => σ w[a] w[b] w[c] = .CCW
--   | .inside x a b c .. => decide $ σPtInTriangle w[x] w[a] w[b] w[c]
--   | .hole a b c ..     => decide $ w.isEmptyTriangle a b c

-- theorem satisfies_signotopeAxiom (w : WBPoints) (i j k l : Fin w.length) :
--     w.toPropAssn ⊨ signotopeAxiom i j k l :=
--   sorry

-- theorem satisfies_signotopeAxioms (w : WBPoints) : w.toPropAssn ⊨ signotopeAxioms w.length :=
--   sorry

/-
def insideDefinitions (n : Nat) : PropFun (Var n) :=
  -- TODO(WN): Might not need split. See discussion in Encoding.lean.
  ∀ {x}, a < x < b:
    I{x, a, b, c} ↔ ((s{a, b, c} ↔ s{a, x, c}) ∧ (!s{a, x, b} ↔ s{a, b, c}))
  ∀ {x}, b < x < c:
    I{x, a, b, c} ↔ ((s{a, b, c} ↔ s{a, x, c}) ∧ (!s{b, x, c} ↔ s{a, b, c}))

theorem insideTriangle_toPropAssn (σ : OrientationAssn n) :
    σ.IsInside x a b c ↔ σ.toPropAssn ⊨ insideDefinitions n ⊓ inside x a b c

/-- If `x` is inside triangle `abc`, then triangle `abc` isn't a hole. -/
def holeConstraints (n : Nat) : PropFun (Var n) :=
  ∀ {x}, a < x < c, with x ≠ b:
    I{x, a, b, c} → !H{a, b, c}

theorem hasHole_toPropAssn :
    ¬L.isEmptyTriangle a b c → L.toPropAssn ⊨ insideDefinitions n ⊓ holeConstraints n ⊓ (hole a b c)ᶜ

def noHoles (n : Nat) : PropFun (Var n) :=
  ∀ a < b < c:
    !H{a, b, c}

/-- What the CNF encodes. -/
def theFormula (n : Nat) : PropFun (Var n) :=
  signotopeAxioms n ⊓ insideDefinitions n ⊓ holeConstraints n ⊓ noHoles n

theorem satisfies_noHoles :
    ∀ a b c, ¬w.isEmptyTriangle a b c → w.toPropAssn ⊨ theFormula
-/

end WBPoints
