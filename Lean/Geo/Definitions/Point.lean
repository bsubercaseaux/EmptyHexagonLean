import Std.Data.List.Basic
import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-- Solves goals of the form `[a,b,c] <+ [p,a,q,b,r,c]`,
i.e., `List.Sublist` between two concrete lists. -/
macro "sublist_tac" : tactic => `(tactic| aesop (add safe List.Sublist.refl, safe List.Sublist.cons_cons, unsafe List.Sublist.cons))
macro "subfinset_tac" : tactic => `(tactic| aesop (add safe Finset.mem_singleton, safe Finset.mem_insert_self, unsafe Finset.mem_insert_of_mem))
macro "subperm_tac" : tactic => `(tactic| aesop (add safe List.Subperm.refl, safe List.subperm.cons, unsafe List.Subperm.cons_right, unsafe List.Subperm.cons_left))

namespace Geo
open List

abbrev Point := EuclideanSpace ℝ (Fin 2)

namespace Point

variable {p q r s t : Point}

@[pp_dot] abbrev x (p : Point) : ℝ := p 0
@[pp_dot] abbrev y (p : Point) : ℝ := p 1

-- Cayden asks: would it be worth it to define a Triple type, like Prod?

@[ext] theorem ext : p.x = q.x → p.y = q.y → p = q := by
  intros; ext i
  match i with | ⟨0, _⟩ | ⟨1, _⟩ => assumption

theorem eq_iff : p = q ↔ (p.x = q.x ∧ p.y = q.y) := by
  aesop (add safe ext)

instance : IsTotal Point (fun P Q => P.x <= Q.x) :=
  ⟨fun _ _ => LE.isTotal.total _ _⟩

instance : IsTrans Point fun P Q => P.x <= Q.x :=
  ⟨fun _ _ _ _ _ => by linarith⟩

def toMatrix (a b c : Point) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![a.x, b.x, c.x ; a.y, b.y, c.y ; 1, 1, 1]

def det (a b c : Point) : Real := (toMatrix a b c).det

lemma det_eq (a b c : Point) :
    det a b c = a.x * b.y + b.x * c.y + c.x * a.y - a.y * b.x - b.y * c.x - c.y * a.x := by
  unfold det toMatrix
  rw [Matrix.det_fin_three]
  simp [Matrix.vecHead, Matrix.vecTail]
  ring_nf

/-! # In general position -/

def InGeneralPosition₃ (p q r : Point) : Prop :=
  det p q r ≠ 0

structure InGeneralPosition₄ (p q r s : Point) : Prop where
  gp₁ : InGeneralPosition₃ p q r
  gp₂ : InGeneralPosition₃ p q s
  gp₃ : InGeneralPosition₃ p r s
  gp₄ : InGeneralPosition₃ q r s

def PointListInGeneralPosition (l : List Point) : Prop :=
  ∀ {{p q r : Point}}, [p, q, r] <+ l → InGeneralPosition₃ p q r

def PointListInGeneralPosition.to₄ {l : List Point} :
    PointListInGeneralPosition l →
    ∀ {p q r s : Point}, [p, q, r, s] <+ l → InGeneralPosition₄ p q r s := by
  intro h _ _ _ _ h'
  constructor <;> { refine h (Sublist.trans ?_ h'); sublist_tac }

/-! # Sorted (strictly, along x-coordinates) -/

structure Sorted₃ (p q r : Point) : Prop where
  h₁ : p.x < q.x
  h₂ : q.x < r.x

structure Sorted₄ (p q r s : Point) : Prop where
  h₁ : Sorted₃ p q r
  h₂ : r.x < s.x

theorem Sorted₄.sorted₁ : Sorted₄ p q r s → Sorted₃ p q r :=
  fun h => h.1

theorem Sorted₄.sorted₂ : Sorted₄ p q r s → Sorted₃ p q s :=
  fun h => ⟨h.1.h₁, lt_trans h.1.h₂ h.2⟩

theorem Sorted₄.sorted₃ : Sorted₄ p q r s → Sorted₃ p r s :=
  fun h => ⟨lt_trans h.1.h₁ h.1.h₂, h.2⟩

theorem Sorted₄.sorted₄ : Sorted₄ p q r s → Sorted₃ q r s :=
  fun h => ⟨h.1.h₂, h.2⟩

theorem Sorted₃.ne₁ : Sorted₃ p q r → p ≠ q := by
  rintro h rfl
  exact LT.lt.false h.h₁

theorem Sorted₃.ne₂ : Sorted₃ p q r → q ≠ r := by
  rintro h rfl
  exact LT.lt.false h.h₂

def PointListSorted (l : List Point) : Prop := l.Sorted (·.x < ·.x)

theorem PointListSorted.to₃ {l : List Point} :
    PointListSorted l →
    ∀ {p q r : Point}, [p, q, r] <+ l → Sorted₃ p q r := by
  intro h _ _ _ h'
  have := h.sublist h'
  constructor
  . have := pairwise_iff_get.mp this ⟨0, ?_⟩ ⟨1, ?_⟩ ?_
    . simpa using this
    all_goals { simp; try constructor }
  . have := pairwise_iff_get.mp this ⟨1, ?_⟩ ⟨2, ?_⟩ ?_
    . simpa using this
    all_goals { simp; try constructor }

theorem PointListSorted.to₄ {l : List Point} :
    PointListSorted l →
    ∀ {p q r s : Point}, [p, q, r, s] <+ l → Sorted₄ p q r s := by
  intro h p q r s h'
  have : [p, q, r] <+ l := by
    refine Sublist.trans ?_ h'
    sublist_tac
  have h₁ := h.to₃ this
  have : [q, r, s] <+ l := by
    refine Sublist.trans ?_ h'
    sublist_tac
  have := h.to₃ this
  exact ⟨h₁, this.h₂⟩

end Geo.Point
