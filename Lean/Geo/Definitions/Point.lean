import Std.Data.List.Basic
import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Geo.ToMathlib

/-- Solves goals of the form `[a,b,c] <+ [p,a,q,b,r,c]`,
i.e., `List.Sublist` between two concrete lists. -/
macro "sublist_tac" : tactic => `(tactic| aesop (add safe List.Sublist.refl, safe List.Sublist.cons_cons, unsafe List.Sublist.cons))
macro "subfinset_tac" : tactic => `(tactic| aesop (add safe Finset.mem_singleton, safe Finset.mem_insert_self, unsafe Finset.mem_insert_of_mem))
macro "subperm_tac" : tactic => `(tactic| aesop (add safe List.Subperm.refl, safe List.subperm.cons, unsafe List.Subperm.cons_right, unsafe List.Subperm.cons_left))
macro "subset_tac" : tactic => `(tactic| aesop (add safe subset_refl, safe Set.insert_subset_insert, unsafe Set.insert_subset))

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

theorem ext_iff : p = q ↔ p.x = q.x ∧ p.y = q.y := by
  aesop (add safe ext)

instance : IsTotal Point fun P Q => P.x <= Q.x :=
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

noncomputable def detAffineMap (p q : Point) : Point →ᵃ[ℝ] ℝ where
  toFun r := det p q r
  linear.toFun r := q.x * r.y + r.x * p.y - q.y * r.x - r.y * p.x
  linear.map_add' a b := by simp [x, y]; ring
  linear.map_smul' a b := by simp [x, y]; ring
  map_vadd' a b := by simp [det_eq, x, y]; ring

@[simp] theorem detAffineMap_apply : detAffineMap p q r = det p q r := rfl

theorem det_perm₁ (p q r) : det p q r = -det q p r := by simp only [det_eq]; ring

theorem det_perm₂ (p q r) : det p q r = -det p r q := by simp only [det_eq]; ring

/-! # In general position -/

def InGenPos₃ (p q r : Point) : Prop :=
  det p q r ≠ 0

theorem InGenPos₃.perm₁ {p q r : Point} :
    InGenPos₃ p q r → InGenPos₃ q p r := by
  simp [InGenPos₃, det_perm₁ p q r]

theorem InGenPos₃.perm₂ {p q r : Point} :
    InGenPos₃ p q r → InGenPos₃ p r q := by
  simp [InGenPos₃, det_perm₂ p q r]

theorem InGenPos₃.of_perm (h : [p, q, r].Perm [p', q', r']) :
    InGenPos₃ p q r ↔ InGenPos₃ p' q' r' :=
  perm₃_induction (fun _ _ _ => (·.perm₁)) (fun _ _ _ => (·.perm₂)) h

theorem InGenPos₃.not_mem_seg :
    InGenPos₃ p q r → p ∉ convexHull ℝ {q, r} := mt fun h => by
  rw [convexHull_pair] at h
  obtain ⟨a, b, _, _, eq, rfl⟩ := h
  simp [det_eq]
  linear_combination eq * (q 1 * r 0 - q 0 * r 1)

structure InGenPos₄ (p q r s : Point) : Prop where
  gp₁ : InGenPos₃ p q r
  gp₂ : InGenPos₃ p q s
  gp₃ : InGenPos₃ p r s
  gp₄ : InGenPos₃ q r s

theorem InGenPos₄.perm₁ : InGenPos₄ p q r s → InGenPos₄ q p r s
  | ⟨H1, H2, H3, H4⟩ => ⟨H1.perm₁, H2.perm₁, H4, H3⟩

theorem InGenPos₄.perm₂ : InGenPos₄ p q r s → InGenPos₄ p r q s
  | ⟨H1, H2, H3, H4⟩ => ⟨H1.perm₂, H3, H2, H4.perm₁⟩

theorem InGenPos₄.perm₃ : InGenPos₄ p q r s → InGenPos₄ p q s r
  | ⟨H1, H2, H3, H4⟩ => ⟨H2, H1, H3.perm₂, H4.perm₂⟩

def ListInGenPos (l : List Point) : Prop :=
  ∀ {{p q r : Point}}, [p, q, r] <+ l → InGenPos₃ p q r

def ListInGenPos.to₄ {l : List Point} :
    ListInGenPos l →
    ∀ {p q r s : Point}, [p, q, r, s] <+ l → InGenPos₄ p q r s := by
  intro h _ _ _ _ h'
  constructor <;> { refine h (Sublist.trans ?_ h'); sublist_tac }

theorem ListInGenPos.subperm : ListInGenPos l ↔
    ∀ {{p q r : Point}}, [p, q, r].Subperm l → InGenPos₃ p q r := by
  refine ⟨fun H _ _ _ ⟨l, p, h⟩ => ?_, fun H _ _ _ h => H h.subperm⟩
  match l, p.length_eq with
  | [p',q',r'], _ => exact (Point.InGenPos₃.of_perm p).1 (H h)

theorem ListInGenPos.subperm₄ : ListInGenPos l →
    ∀ {{p q r s : Point}}, [p, q, r, s].Subperm l → InGenPos₄ p q r s := by
  intro gp p q r s sub
  constructor <;> {
    apply subperm.mp gp
    refine List.Subperm.trans ?_ sub -- `trans` doesn't seem to work?
    subperm_tac
  }

theorem ListInGenPos.mono_subperm : List.Subperm l l' →
    Point.ListInGenPos l' → Point.ListInGenPos l :=
  fun sp H _ _ _ h => subperm.1 H (h.subperm.trans sp)

theorem ListInGenPos.mono_sublist : List.Sublist l l' →
    Point.ListInGenPos l' → Point.ListInGenPos l :=
  fun lsub => mono_subperm lsub.subperm

theorem ListInGenPos.perm (h : l.Perm l') :
    ListInGenPos l ↔ ListInGenPos l' := by
  suffices ∀ {l l'}, l.Perm l' →
    ListInGenPos l → ListInGenPos l' from ⟨this h, this h.symm⟩
  clear l l' h; intro l l' p gp _ _ _ h
  exact ListInGenPos.subperm.1 gp <| List.subperm_iff.2 ⟨_, p.symm, h⟩

def SetInGenPos (S : Set Point) : Prop :=
  ∀ {{p q r : Point}}, {p,q,r} ⊆ S → List.Nodup [p,q,r] →
    InGenPos₃ p q r

theorem SetInGenPos.to₄ {S : Set Point} :
    SetInGenPos S →
    ∀ {{p q r s : Point}}, {p,q,r,s} ⊆ S → List.Nodup [p,q,r,s] →
      InGenPos₄ p q r s := by
  intro h _ _ _ _ pqrsS nd
  constructor <;>
    { apply h (subset_trans ?_ pqrsS); aesop; subset_tac }

def SetInGenPos.mono {S T : Set Point} : S ⊆ T →
    SetInGenPos T → SetInGenPos S :=
  fun ST gp _ _ _ pqrS => gp (pqrS.trans ST)

open Classical in
theorem ListInGenPos.toFinset {l : List Point} :
    ListInGenPos l → SetInGenPos l.toFinset := by
  intro h p q r
  intros
  apply ListInGenPos.subperm.mp h
  apply List.subperm_of_subset
  assumption
  aesop

open Classical in
theorem SetInGenPos.of_nodup {l : List Point} :
    SetInGenPos l.toFinset → l.Nodup → ListInGenPos l := by
  intro h nd p q r pqrl
  apply h
  intro; have := pqrl.subset; aesop
  exact nd.sublist pqrl

open Classical in
theorem SetInGenPos.toList {s : Finset Point} :
    SetInGenPos s → ListInGenPos s.toList := by
  intro h
  apply of_nodup
  simp [h]
  apply Finset.nodup_toList

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

theorem Sorted₃.ofList {l : List Point} :
    l.Sorted (·.x < ·.x) →
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

theorem Sorted₄.ofList {l : List Point} :
    l.Sorted (·.x < ·.x) →
    ∀ {p q r s : Point}, [p, q, r, s] <+ l → Sorted₄ p q r s := by
  intro h p q r s h'
  have : [p, q, r] <+ l := by
    refine Sublist.trans ?_ h'
    sublist_tac
  have h₁ := Sorted₃.ofList h this
  have : [q, r, s] <+ l := by
    refine Sublist.trans ?_ h'
    sublist_tac
  have := Sorted₃.ofList h this
  exact ⟨h₁, this.h₂⟩

end Geo.Point
