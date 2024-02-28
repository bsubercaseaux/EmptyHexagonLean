import LeanSAT.Model.PropFun
import Mathlib.Data.Fintype.Prod

/-! The CNF that we produce, as a `PropPred`. -/

namespace Geo
open LeanSAT Model PropFun

def PropPred (ν) := PropAssignment ν → Prop

instance : SemanticEntails (PropAssignment ν) (PropPred ν) := ⟨(· |> ·)⟩

inductive Var (n : Nat)
  | sigma  (a b c : Fin n)
  | inside (x a b c : Fin n)
  | hole3  (a b c : Fin n)
  | hole4U (a c d : Fin n)
  | hole4D (a c d : Fin n)
  | hole5U (a d e : Fin n)
  | hole5D (a d e : Fin n)
  deriving DecidableEq, Ord

def orientationConstraint (a b c d : Fin n) : PropFun (Var n) :=
  let sabc := Var.sigma a b c
  let sacd := Var.sigma a c d
  let sabd := Var.sigma a b d
  let sbcd := Var.sigma b c d
  [propfun|
    ( {sabc} ∧  {sacd} →  {sabd}) ∧
    ( {sabc} ∧  {sbcd} →  {sacd}) ∧
    (¬{sabc} ∧ ¬{sacd} → ¬{sabd}) ∧
    (¬{sabc} ∧ ¬{sbcd} → ¬{sacd})
  ]

def orientationConstraints (n : Nat) : PropPred (Var n) :=
  fun τ => ∀ a b c d, a < b → b < c → c < d →
    τ ⊨ orientationConstraint a b c d

/-- Symmetry breaking that the leftmost point is CCW with respect to any two other sorted points -/
def pointsCCW (n : Nat) : PropPred (Var n) := fun τ =>
  ∀ a b,
    have : NeZero n := ⟨by have := Fin.size_positive a; aesop⟩
    0 < a → a < b → τ (Var.sigma 0 a b)

def xIsInsideDef (a b c x : Fin n) : PropPred (Var n) := fun τ =>
  let sabc := Var.sigma a b c
  let saxc := Var.sigma a x c
  let saxb := Var.sigma a x b
  let sbxc := Var.sigma b x c
  let I := Var.inside x a b c
  ( a < x → x < b →
    τ ⊨ [propfun| {I} ↔ (({sabc} ↔ {saxc}) ∧ (¬{saxb} ↔ {sabc})) ]
  ) ∧ (
    b < x → x < c →
    τ ⊨ [propfun| {I} ↔ (({sabc} ↔ {saxc}) ∧ (¬{sbxc} ↔ {sabc})) ]
  )

/-- Defines "is inside triangle" variables. -/
def insideDefs (n : Nat) : PropPred (Var n) := fun τ =>
  ∀ a b c, a < b → b < c →
    ∀ x, (τ |> xIsInsideDef a b c x)

/-- Defines "3-hole" variables.

  Triangle abc is a hole iff all x are not inside triangle abc. -/
def hole3Defs (n : Nat) : PropPred (Var n) := fun τ =>
  ∀ {a b c}, a < b → b < c →
    (τ (Var.hole3 a b c) ↔
      (∀ x, a < x → x < c → x ≠ b → !τ (Var.inside x a b c)))

/-- Asserts that no 3-holes exist. -/
def noHole3s (n : Nat) : PropPred (Var n) := fun τ =>
  ∀ a b c, a < b → b < c → !τ (Var.hole3 a b c)

/-- Defines "4-hole" variables.

Note that these variables are only meaningful when
-/
def hole4Def (a c d : Fin n) : PropPred (Var n) := fun τ =>
  (∀ b, ¬ τ (Var.sigma a b c) → ¬ τ (Var.sigma b c d) → τ (Var.hole4U a c d)) ∧
  (∀ b,   τ (Var.sigma a b c) →   τ (Var.sigma b c d) → τ (Var.hole4D a c d))

def hole4Defs (n : Nat) : PropPred (Var n) := fun τ =>
  ∀ a c d, a < c → c < d →
    (hole4Def a c d) τ

#exit

/-- The abstract formula encoding empty triangle on `n` points. -/
def theFormula (n : Nat) : PropAssignment (Var n) → Prop := fun τ =>
  (τ |> orientationConstraints n) ∧
  (τ |> insideDefs n) ∧
  (τ |> holeDefs n) ∧
  (τ |> noHoles n) ∧
  (τ |> pointsCCW n)
