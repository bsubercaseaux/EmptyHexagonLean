import Std.Data.List.Basic
import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

namespace Geo

noncomputable section
open Classical

abbrev Point := EuclideanSpace ℝ (Fin 2)

namespace Point

variable {p q r s t : Point}

abbrev x (p : Point) : ℝ := p 0
abbrev y (p : Point) : ℝ := p 1

-- Cayden asks: would it be worth it to define a Triple type, like Prod?

@[ext] theorem ext : p.x = q.x → p.y = q.y → p = q := by
  intros; ext i
  match i with | ⟨0, _⟩ | ⟨1, _⟩ => assumption

instance : IsTotal Point (fun P Q => P.x <= Q.x) :=
  ⟨fun _ _ => LE.isTotal.total _ _⟩

instance : IsTrans Point (fun P Q => P.x <= Q.x) :=
  ⟨fun _ _ _ _ _ => by linarith⟩

def det (p q r : Point) : ℝ :=
  p.x * q.y + q.x * r.y + r.x * p.y - p.y * q.x - q.y * r.x - r.y * p.x

structure InGeneralPosition₃ (p q r : Point) : Prop :=
  det_ne_zero : det p q r ≠ 0

structure InGeneralPosition₄ (p q r s : Point) : Prop :=
  gp₁ : InGeneralPosition₃ p q r
  gp₂ : InGeneralPosition₃ p q s
  gp₃ : InGeneralPosition₃ p r s
  gp₄ : InGeneralPosition₃ q r s

open List in
def PointListInGeneralPosition (l : List Point) : Prop :=
  ∀ {p q r : Point}, [p, q, r] <+ l → InGeneralPosition₃ p q r

open Finset in
def PointFinsetInGeneralPosition (S : Finset Point) : Prop :=
  ∀ {p q r}, {p, q, r} ⊆ S → InGeneralPosition₃ p q r

/-! # Sorted (along x-coordinates) -/

structure Sorted₃ (p q r : Point) : Prop :=
  h₁ : p.x < q.x
  h₂ : q.x < r.x

structure Sorted₄ (p q r s : Point) : Prop :=
  h₁ : Sorted₃ p q r
  h₂ : r.x < s.x

open List in
def PointListSorted (l : List Point) : Prop := l.Sorted (·.x < ·.x)

theorem Sorted₃_of_Sorted₄ : Sorted₄ p q r s → Sorted₃ p q r :=
  fun h => h.1

theorem Sorted₃_of_Sorted₄' : Sorted₄ p q r s → Sorted₃ q r s :=
  fun h => ⟨h.1.h₂, h.2⟩

-- Cayden says: TODO better names. And should h₁ and h₂ be names of Sorted₃/Sorted₄?
theorem Sorted₃124_of_Sorted₄ : Sorted₄ p q r s → Sorted₃ p q s :=
  fun h => ⟨h.1.h₁, lt_trans h.1.h₂ h.2⟩

theorem Sorted₃134_of_Sorted₄ : Sorted₄ p q r s → Sorted₃ p r s :=
  fun h => ⟨lt_trans h.1.h₁ h.1.h₂, h.2⟩

theorem ne_first_of_Sorted₃ : Sorted₃ p q r → p ≠ q := by
  rintro h rfl
  exact LT.lt.false h.h₁

theorem ne_last_of_Sorted₃ : Sorted₃ p q r → q ≠ r := by
  rintro h rfl
  exact LT.lt.false h.h₂

end Point

open Point

-- Cayden says: "Points" is too general a name. Maybe "WBPoints", for well-behaved points?
structure Points where
  points : List Point
  nodup : points.Nodup
  sorted : PointListSorted points
  gp : PointListInGeneralPosition points

namespace Points

open List Finset
#check List.insertionSort
#check List.Pairwise.sublist
#check List.Sorted

def toFinset (P : Points) : Finset Point := P.points.toFinset

def fromFinset {S : Finset Point} (hS : PointFinsetInGeneralPosition S)
    (hX : Set.Pairwise S.toSet (·.x ≠ ·.x)) : Points :=
  { points := S.toList.insertionSort (·.x ≤ ·.x)
    nodup := (Perm.nodup_iff (perm_insertionSort _ _)).mpr (Finset.nodup_toList S)
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

theorem x_ne (P : Points) : P.points.Pairwise (·.x ≠ ·.x) :=
  Pairwise.imp ne_of_lt P.sorted

end Points

def finset_sort (S : Finset Point) : List Point :=
  S.toList.insertionSort (·.x <= ·.x)

theorem finset_sort_sorted (S : Finset Point) : (finset_sort S).Sorted (·.x <= ·.x) :=
  List.sorted_insertionSort (·.x <= ·.x) (S.toList)

-- Cayden says: Below is "dead code" for previous definitions of sorting, etc.
#exit

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

end Geo
