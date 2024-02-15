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
  leftmost : Point
  rest : List Point
  sorted : PointListSorted (leftmost :: rest)
  gp : PointListInGeneralPosition (leftmost :: rest)
  oriented : rest.Pairwise (σ leftmost · · = .CCW)

def WBPoints.points (w : WBPoints) := w.leftmost :: w.rest

def finset_sort (S : Finset Point) : List Point :=
  S.toList.insertionSort (·.x <= ·.x)

theorem finset_sort_sorted (S : Finset Point) : (finset_sort S).Sorted (·.x <= ·.x) :=
  List.sorted_insertionSort (·.x <= ·.x) (S.toList)

namespace WBPoints
open List Finset Classical
open LeanSAT Model PropFun

def toFinset (w : WBPoints) : Finset Point := w.points.toFinset

theorem nodupX (w : WBPoints) : w.points.Pairwise (·.x ≠ ·.x) :=
  Pairwise.imp ne_of_lt w.sorted

theorem nodup (w : WBPoints) : w.points.Nodup :=
  w.nodupX.imp fun hx h => by rw [h] at hx; contradiction

abbrev length (w : WBPoints) : Nat := w.points.length

instance : GetElem WBPoints Nat Point (fun w i => i < w.length) where
  getElem w i h := w.points[i]'h

-- TODO: use a definition from an earlier module
def σIsEmptyTriangleFor (a b c : Point) (S : Finset Point) : Prop :=
  ∀ s ∈ S \ {a,b,c}, ¬σPtInTriangle s a b c

def toPropAssn (w : WBPoints) : PropAssignment (Var w.length)
  | .sigma a b c ..    => σ w[a] w[b] w[c] = .CCW
  | .inside x a b c .. => decide $ σPtInTriangle w[x] w[a] w[b] w[c]
  | .hole a b c ..     => decide $ σIsEmptyTriangleFor w[a] w[b] w[c] w.toFinset

theorem satisfies_signotopeAxiom (w : WBPoints) (i j k l : Fin w.length) :
    i < j → j < k → k < l → w.toPropAssn ⊨ signotopeAxiom i j k l := by
  intro hij hjk hkl
  have : [w[i], w[j], w[k], w[l]] <+ w.points := by
    have : [w[i], w[j], w[k], w[l]] = [i,j,k,l].map w.points.get := by
      simp [GetElem.getElem, List.getElem_eq_get]
    rw [this]
    apply map_get_sublist
    have := hjk.trans hkl
    simp [hij, hjk, hkl, hij.trans hjk, hij.trans this, this]
  have s : Sorted₄ w[i] w[j] w[k] w[l] := w.sorted.to₄ this
  have gp : InGeneralPosition₄ w[i] w[j] w[k] w[l] :=
    PointListInGeneralPosition.to₄ w.gp this
  simp only [signotopeAxiom, satisfies_conj, satisfies_impl, satisfies_var,
    toPropAssn, decide_eq_true_eq, and_imp, satisfies_neg]
  constructor
  . exact σ_prop₂ s gp
  constructor
  . exact σ_prop₁ s gp
  constructor
  . simp_rw [gp.gp₁.σ_iff, gp.gp₂.σ_iff, gp.gp₃.σ_iff]
    exact σ_prop₄ s gp
  . simp_rw [gp.gp₁.σ_iff, gp.gp₄.σ_iff, gp.gp₃.σ_iff]
    exact σ_prop₃ s gp

theorem satisfies_signotopeAxioms (w : WBPoints) : w.toPropAssn ⊨ signotopeAxioms w.length := by
  unfold signotopeAxioms
  simp only [signotopeAxioms, satisfies_all, Multiset.mem_map, mem_val, mem_univ, true_and,
    forall_exists_index, forall_apply_eq_imp_iff]
  intro i j k l
  split
  . apply satisfies_signotopeAxiom <;> tauto
  exact satisfies_tr

theorem insideDefs_aux₁ {a x b c : Point} : Sorted₄ a x b c → InGeneralPosition₄ a x b c →
    (σPtInTriangle x a b c ↔
      ((σ a b c = .CCW ↔ σ a x c = .CCW) ∧ (σ a x b ≠ .CCW ↔ σ a b c = .CCW))) := by
  intro sorted gp
  simp only [σPtInTriangle, σ_perm₁ b x c, σ_perm₂ a c b, σ_perm₁ b a c, gp.gp₁.σ_iff]
  cases gp.gp₁.σ_cases <;> cases gp.gp₂.σ_cases <;> cases gp.gp₃.σ_cases <;> cases gp.gp₄.σ_cases <;> simp_all [-getElem_fin]
  next h₁ h₂ h₃ h₄ =>
    rw [σ_prop₁ sorted gp h₁ h₄] at h₃
    contradiction
  next h₁ h₂ h₃ h₄ =>
    rw [σ_prop₃ sorted gp h₁ h₄] at h₃
    contradiction

theorem insideDefs_aux₂ {a b x c : Point} : Sorted₄ a b x c → InGeneralPosition₄ a b x c →
    (σPtInTriangle x a b c ↔
      ((σ a b c = .CCW ↔ σ a x c = .CCW) ∧ (σ b x c ≠ .CCW ↔ σ a b c = .CCW))) := by
  intro sorted gp
  simp only [σPtInTriangle, σ_perm₂ a x b, σ_perm₂ a c b, σ_perm₁ b a c, gp.gp₄.σ_iff]
  cases gp.gp₁.σ_cases <;> cases gp.gp₂.σ_cases <;> cases gp.gp₃.σ_cases <;> cases gp.gp₄.σ_cases <;> simp_all [-getElem_fin]
  next h₁ h₂ h₃ h₄ =>
    rw [σ_prop₁ sorted gp h₁ h₄] at h₃
    contradiction
  next h₁ h₂ h₃ h₄ =>
    rw [σ_prop₃ sorted gp h₁ h₄] at h₃
    contradiction

theorem satisfies_insideDefs (w : WBPoints) : w.toPropAssn ⊨ insideDefs w.length := by
  unfold insideDefs xIsInsideDef
  simp only [satisfies_all, Multiset.mem_map, forall_exists_index, forall_apply_eq_imp_iff, mem_val, mem_univ, true_and]
  intro a b c x
  split_ifs <;> first | exact satisfies_tr | unfold toPropAssn
  next abc axb =>
    have : [w[a], w[x], w[b], w[c]] <+ w.points := by
      have : [w[a], w[x], w[b], w[c]] = [a,x,b,c].map w.points.get := by
        simp [GetElem.getElem, List.getElem_eq_get]
      rw [this]
      apply map_get_sublist
      simp [abc.left, axb.left, abc.left.trans abc.right, axb.right, axb.right.trans abc.right, abc.right]
    simp [-getElem_fin, insideDefs_aux₁ (w.sorted.to₄ this) (PointListInGeneralPosition.to₄ w.gp this) ]
  next abc _ bxc =>
    have : [w[a], w[b], w[x], w[c]] <+ w.points := by
      have : [w[a], w[b], w[x], w[c]] = [a,b,x,c].map w.points.get := by
        simp [GetElem.getElem, List.getElem_eq_get]
      rw [this]
      apply map_get_sublist
      simp [abc.left, abc.left.trans bxc.left, abc.left.trans abc.right, bxc.left, abc.right, bxc.right]
    simp [-getElem_fin, insideDefs_aux₂ (w.sorted.to₄ this) (PointListInGeneralPosition.to₄ w.gp this)]

theorem satisfies_holeDefs (w : WBPoints) : w.toPropAssn ⊨ holeDefs w.length := by
  sorry -- TODO: we should agree on a defn of σIsEmptyTriangleFor globally first

theorem satisfies_noHoles (w : WBPoints) :
    (∀ (a b c : Point), {a,b,c} ⊆ w.toFinset → ¬σIsEmptyTriangleFor a b c w.toFinset) →
    w.toPropAssn ⊨ theFormula w.length := by
  unfold theFormula
  intro noholes
  simp only [noHoles, satisfies_conj, satisfies_signotopeAxioms, satisfies_insideDefs, and_self,
    satisfies_holeDefs, satisfies_all, Multiset.mem_map, mem_val, mem_univ, true_and,
    forall_exists_index, forall_apply_eq_imp_iff]
  intro a b c
  split_ifs
  . unfold toPropAssn
    simp only [satisfies_neg, satisfies_var, decide_eq_true_eq]
    apply noholes
    intro _ hx
    apply List.mem_toFinset.mpr
    simp only [mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx | hx <;> { rw [hx]; apply List.get_mem }
  . exact satisfies_tr

end WBPoints
