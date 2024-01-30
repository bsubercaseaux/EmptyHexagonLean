import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Algebra.Basic

structure Point where
  x : Real
  y : Real
-- deriving DecidableEq

def determinant_pts (a b c : Point) : Real :=
  a.x * b.y + b.x * c.y + c.x * a.y - a.y * b.x - b.y * c.x - c.y * a.x

structure IsSortedPoints₃ (p q r : Point) : Prop :=
  sorted₁ : p.x < q.x
  sorted₂ : q.x < r.x
  det_ne_zero : determinant_pts p q r ≠ 0

structure IsSortedPoints (pts : List Point) : Prop :=
  all_triples_sorted : ∀ {p q r}, List.Sublist [p, q, r] pts → IsSortedPoints₃ p q r

theorem is_sorted_three {p q r : Point} : IsSortedPoints [p, q, r] ↔ IsSortedPoints₃ p q r := by
  constructor
  . intro h
    apply h.all_triples_sorted
    apply List.Sublist.refl
  . intro h
    constructor
    intro _ _ _ hSub
    cases List.Sublist.eq_of_length hSub rfl
    assumption

structure IsSortedPoints₄ (p q r s : Point) : Prop :=
  sorted₁ : IsSortedPoints₃ p q r
  sorted₂ : IsSortedPoints₃ p q s
  sorted₃ : IsSortedPoints₃ p r s
  sorted₄ : IsSortedPoints₃ q r s

theorem is_sorted_four {p q r s : Point} : IsSortedPoints [p, q, r, s] ↔ IsSortedPoints₄ p q r s := by
  constructor
  . intro h
    constructor <;> {
      apply h.all_triples_sorted
      aesop (add safe List.Sublist.refl, safe List.Sublist.cons_cons, unsafe List.Sublist.cons)
    }
  . intro h
    constructor
    intro p' q' r' hSub
    cases' hSub with hSub hSub hSub hSub hSub hSub hSub hSub
    . cases List.Sublist.eq_of_length hSub rfl
      exact h.sorted₄
    cases' hSub with hSub hSub hSub hSub hSub hSub hSub hSub
    . cases List.Sublist.eq_of_length hSub rfl
      exact h.sorted₃
    cases' hSub with hSub hSub hSub hSub hSub hSub hSub hSub
    . cases List.Sublist.eq_of_length hSub rfl
      exact h.sorted₂
    exact h.sorted₁
