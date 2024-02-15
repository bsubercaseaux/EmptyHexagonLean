import Std.Data.List.Basic
import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

syntax "sublist_tac" : tactic
/-- Solves goals of the form `[a,b,c] <+ [p,a,q,b,r,c]`,
i.e., `List.Sublist` between two concrete lists. -/
macro_rules
  | `(tactic| sublist_tac) => `(tactic| aesop (add safe List.Sublist.refl, safe List.Sublist.cons_cons, unsafe List.Sublist.cons))

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

<<<<<<< HEAD:Lean/Geo/Definitions/Point.lean
instance : IsTotal Point fun P Q => P.x <= Q.x :=
=======
theorem eq_iff : p = q ↔ (p.x = q.x ∧ p.y = q.y) := by
  aesop (add safe ext)

instance : IsTotal Point (fun P Q => P.x <= Q.x) :=
>>>>>>> 8112270 (NewThingy is ready):Lean/Geo/Point.lean
  ⟨fun _ _ => LE.isTotal.total _ _⟩

instance : IsTrans Point fun P Q => P.x <= Q.x :=
  ⟨fun _ _ _ _ _ => by linarith⟩

def det (p q r : Point) : ℝ :=
  p.x * q.y + q.x * r.y + r.x * p.y - p.y * q.x - q.y * r.x - r.y * p.x

/-! # In general position -/

def InGeneralPosition₃ (p q r : Point) : Prop :=
  det p q r ≠ 0

structure InGeneralPosition₄ (p q r s : Point) : Prop :=
  gp₁ : InGeneralPosition₃ p q r
  gp₂ : InGeneralPosition₃ p q s
  gp₃ : InGeneralPosition₃ p r s
  gp₄ : InGeneralPosition₃ q r s

def PointListInGeneralPosition (l : List Point) : Prop :=
  ∀ {p q r : Point}, [p, q, r] <+ l → InGeneralPosition₃ p q r

def PointListInGeneralPosition.to₄ {l : List Point} :
    PointListInGeneralPosition l →
    ∀ {p q r s : Point}, [p, q, r, s] <+ l → InGeneralPosition₄ p q r s := by
  intro h _ _ _ _ h'
  constructor <;> { refine h (Sublist.trans ?_ h'); sublist_tac }

open Classical in
def PointFinsetInGeneralPosition (S : Finset Point) : Prop :=
  ∀ {{p q r}}, {p, q, r} ⊆ S → InGeneralPosition₃ p q r

-- theorem nodup_of_gp (l : List Point) :
--     3 < l.length → PointListInGeneralPosition l → l.Nodup :=
--   sorry

/-! # Sorted (strictly, along x-coordinates) -/

structure Sorted₃ (p q r : Point) : Prop :=
  h₁ : p.x < q.x
  h₂ : q.x < r.x

structure Sorted₄ (p q r s : Point) : Prop :=
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
