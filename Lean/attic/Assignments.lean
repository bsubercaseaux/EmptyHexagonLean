import Geo.Orientations
import LeanSAT.Model.PropAssn

/-! Every `σ_assignment` of orientations to triples
has a corresponding propositinal assignment
which satisfies certain propositional formulas
depending on which properties are true of the `σ_assignment`. -/

namespace Geo
open LeanSAT Model

structure OrderedTriple (n : Nat) where
  (i j k : Fin n)
  (ordered: i < j ∧ j < k)

/-- An assignment of orientations, `true` for `CCW` and `false` for `CW`.
`Collinear` is excluded.

Some such assignments are realizable as lists of `n` points in the plane,
others are not. -/
abbrev OrientationAssn (n : Nat) :=
  OrderedTriple n → Bool

-- TODO: this is just here for reference, import it instead
inductive Var (n : Nat)
  | sigma  (t : OrderedTriple n)
  | inside (x a b c : Fin n)
  | hole   (a b c : Fin n)

namespace OrientationAssn

def OrientationAssn.isTriangle (a : Fin n) (t : OrderedTriple n) :=
    σ p' q' r' = σ p' a r' ∧
    σ p' a q' = σ p' r' q' ∧
    σ q' a r' = σ q' p' r'

end OrientationAssn


def OrientationAssn.toPropAssn (σ : OrientationAssn n) : PropAssignment (Var n)
  | .sigma t => σ t
  | .inside x a b c => sorry -- use Decidable (σ.IsInsideTriangle x a b c)
  | .hole a b c => sorry

/-
def signotopeAxioms (n : Nat) : PropFun (Var n) :=
  ∀ 1 ≤ a < b < c ≤ n:
    (s{a, b, c} ∧ s{a, c, d}) → s{a, b, d}
    (s{a, b, c} ∧ s{b, c, d}) → s{a, c, d}
    (!s{a, b, c} ∧ !s{a, c, d}) → !s{a, b, d}
    (!s{a, b, c} ∧ !s{b, c, d}) → !s{a, c, d}

def insideDefinitions (n : Nat) : PropFun (Var n) :=
  ∀ {x}, a < x < b:
    I{x, a, b, c} ↔ ((s{a, b, c} ↔ s{a, x, c}) ∧ (!s{a, x, b} ↔ s{a, b, c}))
  ∀ {x}, b < x < c:
    I{x, a, b, c} ↔ ((s{a, b, c} ↔ s{a, x, c}) ∧ (!s{b, x, c} ↔ s{a, b, c}))

/-- If `x` is inside triangle `abc`, then triangle `abc` isn't a hole. -/
def holeConstraints (n : Nat) : PropFun (Var n) :=
  ∀ {x}, a < x < c, with x ≠ b:
    I{x, a, b, c} → !H{a, b, c}

def noHoles (n : Nat) : PropFun (Var n) :=
  ∀ a < b < c:
    !H{a, b, c}

def theFormula (n : Nat) : PropFun (Var n) :=
  signotopeAxioms n ⊓ insideDefinitions n ⊓ holeConstraints n ⊓ noHoles n

theorem satisfies_signotopeAxioms (pts : Points) :
    pts.toOrientationAssn.toPropAssn ⊨ signotopeAxioms n

theorem insideTriangle_toPropAssn (σ : OrientationAssn n) :
    σ.IsInside x a b c ↔ σ.toPropAssn ⊨ insideDefinitions n ⊓ inside x a b c

theorem hasHole_toPropAssn :
    !w.IsHole a b c → σ.toPropAssn ⊨ insideDefinitions n ⊓ holeConstraints n ⊓ !hole a b c

theorem noHoles_toPropAssn :
    w.NoHoles → w.toPropAssn ⊨ theFormula



-/
