import LeanSAT.Model.PropFun
import Mathlib.Data.Fintype.Prod

/-! The CNF that we produce, as a `PropFun`. -/

namespace Geo
open LeanSAT Model

inductive Var (n : Nat)
  | sigma  (a b c : Fin n)
  | inside (x a b c : Fin n)
  | hole   (a b c : Fin n)
  deriving DecidableEq

def signotopeAxiom (a b c d : Fin n) : PropFun (Var n) :=
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

/-- Orientation constraints.

  ∀ 1 ≤ a < b < c ≤ n:
    ∀ {d}, c < d:
      !s{a, b, c} ∨ !s{a, c, d} ∨  s{a, b, d} ≃ (s{a, b, c} ∧ s{a, c, d}) → s{a, b, d}
      !s{a, b, c} ∨ !s{b, c d}  ∨  s{a, c, d} ≃ (s{a, b, c} ∧ s{b, c, d}) → s{a, c, d}

      (We take the top grouping and do them again, except negating the actual variables)

       s{a, b, c} ∨  s{a, c, d} ∨ !s{a, b, d} ≃ (!s{a, b, c} ∧ !s{a, c, d}) → !s{a, b, d}
       s{a, b, c} ∨  s{b, c, d} ∨ !s{a, c, d} ≃ (!s{a, b, c} ∧ !s{b, c, d}) → !s{a, c, d} -/
def signotopeAxioms (n : Nat) : PropFun (Var n) :=
  let U : Multiset (Fin n) := Finset.univ.val
  PropFun.all (U.map (fun a =>
    PropFun.all (U.map fun b =>
      PropFun.all (U.map fun c =>
        PropFun.all (U.map fun d =>
          if a < b ∧ b < c ∧ c < d then signotopeAxiom a b c d else ⊤)))))

def xIsInside (a b c x : Fin n) : PropFun (Var n) :=
  let sabc := Var.sigma a b c
  let saxc := Var.sigma a x c
  let saxb := Var.sigma a x b
  let sbxc := Var.sigma b x c
  let I := Var.inside x a b c
  if a < x ∧ x < b then
    [propfun| {I} ↔ (({sabc} ↔ {saxc}) ∧ (¬{saxb} ↔ {sabc})) ]
  else if b < x ∧ x < c then
    [propfun| {I} ↔ (({sabc} ↔ {saxc}) ∧ (¬{sbxc} ↔ {sabc})) ]
  else
    ⊤

/-- The "inside triangles" constraints.

  (We split on whether the candidate point "x" to be inside is before or after "b")

  ∀ {x}, a < x < b:
    I{x, a, b, c} ↔ ((s{a, b, c} ↔ s{a, x, c}) ∧ (!s{a, x, b} ↔ s{a, b, c}))

  ∀ {x}, b < x < c:
    I{x, a, b, c} ↔ ((s{a, b, c} ↔ s{a, x, c}) ∧ (!s{b, x, c} ↔ s{a, b, c})) -/
def insideConstraints (n : Nat) : PropFun (Var n) :=
  let U : Multiset (Fin n) := Finset.univ.val
  PropFun.all (U.map (fun a =>
    PropFun.all (U.map fun b =>
      PropFun.all (U.map fun c =>
        PropFun.all (U.map fun x =>
          if a < b ∧ b < c then
            xIsInside a b c x
          else
            ⊤)))))

def notHoleOfPointInside (a b c : Fin n) : PropFun (Var n) :=
  let U : Multiset (Fin n) := Finset.univ.val
  PropFun.all (U.map (fun x =>
    if a < x ∧ x < c ∧ x ≠ b then
      [propfun| {Var.inside x a b c} → ¬{Var.hole a b c} ]
    else
      ⊤))

def hasPointInside (a b c : Fin n) : PropFun (Var n) :=
  let U : Multiset (Fin n) := Finset.univ.val
  PropFun.any (U.map (fun x =>
    if a < x ∧ x < c ∧ x ≠ b then
      Var.inside x a b c
    else
      ⊥))

/-- ∀ {x}, a < x < c, with x ≠ b:
      I{x, a, b, c} → !H{a, b, c}

    !H{a, b, c} → ⋁_{a < x < c, x ≠ b} I{x, a, b, c}

  (Triangle abc is not a hole iff some x is inside triangle abc.) -/
def holeConstraints (n : Nat) : PropFun (Var n) :=
  let U : Multiset (Fin n) := Finset.univ.val
  PropFun.all (U.map (fun a =>
    PropFun.all (U.map fun b =>
      PropFun.all (U.map fun c =>
        if a < b ∧ b < c then
          [propfun|
            {notHoleOfPointInside a b c} ∧
            (¬{Var.hole a b c} → {hasPointInside a b c})
          ]
        else
          ⊤))))

def noHoles (n : Nat) : PropFun (Var n) :=
  let U : Multiset (Fin n) := Finset.univ.val
  PropFun.all (U.map (fun a =>
    PropFun.all (U.map fun b =>
      PropFun.all (U.map fun c =>
        if a < b ∧ b < c then
          (Var.hole a b c)ᶜ
        else ⊤))))

def theFormula (n : Nat) : PropFun (Var n) :=
  signotopeAxioms n ⊓ insideConstraints n ⊓ holeConstraints n ⊓ noHoles n
