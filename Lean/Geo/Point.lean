import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

noncomputable section
open Classical

abbrev Point := EuclideanSpace ℝ (Fin 2)
abbrev Point.x (P : Point) : ℝ := P 0
abbrev Point.y (P : Point) : ℝ := P 1
@[ext]
theorem Point.ext {P Q : Point} : P.x = Q.x → P.y = Q.y → P = Q := by
  intros; ext i
  match i with | ⟨0, _⟩ | ⟨1, _⟩ => assumption

instance : IsTotal Point (fun P Q => P.x <= Q.x) :=
  ⟨fun _ _ => LE.isTotal.total _ _⟩

instance : IsTrans Point (fun P Q => P.x <= Q.x) :=
  ⟨fun _ _ _ _ _ => by linarith⟩

def finset_sort (S : Finset Point) : List Point :=
  S.toList.insertionSort (·.x <= ·.x)

theorem finset_sort_sorted (S : Finset Point) : (finset_sort S).Sorted (·.x <= ·.x) :=
  List.sorted_insertionSort (·.x <= ·.x) (S.toList)

def determinant_pts (a b c : Point) : Real :=
  a.x * b.y + b.x * c.y + c.x * a.y - a.y * b.x - b.y * c.x - c.y * a.x

structure GeneralPosition₃ (p q r : Point) : Prop :=
  det_ne_zero : determinant_pts p q r ≠ 0

structure GeneralPosition₄ (p q r s : Point) : Prop :=
  gp₁ : GeneralPosition₃ p q r
  gp₂ : GeneralPosition₃ p q s
  gp₃ : GeneralPosition₃ p r s
  gp₄ : GeneralPosition₃ q r s

structure GeneralPosition (pts: Finset Point) : Prop :=
  no_three_collinear: ∀ p q r, {p, q, r} ⊆ pts → GeneralPosition₃ p q r

structure IsSortedPoints₃ (p q r : Point) : Prop :=
  sorted₁ : p.x < q.x
  sorted₂ : q.x < r.x

theorem ne_first_of_IsSortedPoints₃ {p q r : Point} :
    IsSortedPoints₃ p q r → p ≠ q := by
  rintro h rfl
  exact LT.lt.false h.sorted₁

theorem ne_last_of_IsSortedPoints₃ {p q r : Point} :
    IsSortedPoints₃ p q r → q ≠ r := by
  rintro h rfl
  exact LT.lt.false h.sorted₂

structure IsSortedPoints (pts : List Point) : Prop :=
  triples_sorted : ∀ {p q r}, List.Sublist [p, q, r] pts → IsSortedPoints₃ p q r

structure IsSortedPoints' (pts : List Point) : Prop :=
  parwise_sorted : List.Sorted (·.x < ·.x) pts

-- Either pick one predicate, or prove they are equivalent
theorem is_sorted_equiv : IsSortedPoints pts ↔ IsSortedPoints' pts := sorry

theorem is_sorted_three {p q r : Point} : IsSortedPoints [p, q, r] ↔ IsSortedPoints₃ p q r := by
  constructor
  . intro h
    apply h.triples_sorted
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
      apply h.triples_sorted
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
