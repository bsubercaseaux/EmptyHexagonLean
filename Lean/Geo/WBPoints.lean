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

/-- A well-behaved list of points: in general position, sorted by `x`,
and containing at least one point `leftmost`
such that all signotopes `σ leftmost a b` are `CCW`. -/
structure WBPoints where
  leftmost : Point
  rest : List Point
  sorted' : PointListSorted (leftmost :: rest)
  gp' : PointListInGeneralPosition (leftmost :: rest)
  oriented : rest.Pairwise (σ leftmost · · = .CCW)

def finset_sort (S : Finset Point) : List Point :=
  S.toList.insertionSort (·.x <= ·.x)

theorem finset_sort_sorted (S : Finset Point) : (finset_sort S).Sorted (·.x <= ·.x) :=
  List.sorted_insertionSort (·.x <= ·.x) (S.toList)

namespace WBPoints
open List Finset Classical
open LeanSAT Model PropFun

def points (w : WBPoints) := w.leftmost :: w.rest

def toFinset (w : WBPoints) : Finset Point := w.points.toFinset

theorem sorted (w : WBPoints) : PointListSorted w.points :=
  w.sorted'

theorem gp (w : WBPoints) : PointListInGeneralPosition w.points :=
  w.gp'

theorem nodupX (w : WBPoints) : w.points.Pairwise (·.x ≠ ·.x) :=
  Pairwise.imp ne_of_lt w.sorted

theorem nodup (w : WBPoints) : w.points.Nodup :=
  w.nodupX.imp fun hx h => by rw [h] at hx; contradiction

abbrev length (w : WBPoints) : Nat := w.points.length

instance : GetElem WBPoints Nat Point (fun w i => i < w.length) where
  getElem w i h := w.points[i]'h

theorem sorted_get (w : WBPoints) {i j : Fin w.length} :
    i < j → w[i].x < w[j].x := by
  intro ij
  apply List.pairwise_iff_get.mp w.sorted _ _ ij

theorem of_sorted_get (w : WBPoints) {i j : Fin w.length} :
    w[i].x < w[j].x → i < j := by
  intro wiwj
  by_contra h
  rcases lt_or_eq_of_le (not_lt.mp h) with h | h
  . have := w.sorted_get h
    linarith
  . rw [h] at wiwj
    linarith

theorem of_eqx (w : WBPoints) {i j : Fin w.length} :
    w[i].x = w[j].x → i = j := by
  intro h
  by_contra h
  rcases Ne.lt_or_lt h with h | h <;> {
    have := w.sorted_get h
    linarith
  }

-- TODO: use a definition from an earlier module
def σIsEmptyTriangleFor (a b c : Point) (S : Finset Point) : Prop :=
  ∀ s ∈ S, ¬σPtInTriangle s a b c

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

lemma xBounded_of_PtInTriangle {x a b c : Point} :
    Sorted₃ a b c → PtInTriangle x a b c → a.x ≤ x.x ∧ x.x ≤ c.x := by
  unfold PtInTriangle
  intro sorted tri
  let S := { p : Point | a.x ≤ p.x } ∩ { p : Point | p.x ≤ c.x }
  have cvxS : Convex ℝ S :=
    Convex.inter
      (convex_halfspace_ge ⟨fun _ _ => rfl, fun _ _ => rfl⟩ a.x)
      (convex_halfspace_le ⟨fun _ _ => rfl, fun _ _ => rfl⟩ c.x)
  have abcS : {a, b, c} ⊆ S := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    rcases hx with rfl | rfl | rfl
    . exact ⟨le_rfl, le_of_lt <| sorted.h₁.trans sorted.h₂⟩
    . exact ⟨le_of_lt sorted.h₁, le_of_lt sorted.h₂⟩
    . exact ⟨le_of_lt <| sorted.h₁.trans sorted.h₂, le_rfl⟩
  have : x ∈ S := convexHull_min abcS cvxS tri
  simpa only [Set.mem_inter_iff, Set.mem_setOf_eq] using this

-- TODO: Use the real actual proof
lemma σiff {x a b c : Point} : σPtInTriangle x a b c ↔ PtInTriangle x a b c := sorry

theorem satisfies_holeDefs (w : WBPoints) : w.toPropAssn ⊨ holeDefs w.length := by
  unfold holeDefs notHoleOfPointInside hasPointInside
  simp only [satisfies_all, Multiset.mem_map, forall_exists_index, forall_apply_eq_imp_iff, mem_val, mem_univ, true_and]
  intro a b c
  split_ifs <;> try exact satisfies_tr
  simp only [ne_eq, satisfies_conj, satisfies_all, Multiset.mem_map, mem_val, mem_univ, true_and,
    forall_exists_index, forall_apply_eq_imp_iff, satisfies_impl, satisfies_neg, satisfies_var,
    Bool.not_eq_true, satisfies_any, exists_exists_eq_and]
  constructor
  . intro x
    split_ifs <;> try exact satisfies_tr
    simp only [satisfies_impl, satisfies_var, toPropAssn, decide_eq_true_eq, satisfies_neg,
      σIsEmptyTriangleFor, not_forall, not_not, exists_prop, toFinset, List.mem_toFinset]
    intro h
    exact ⟨w[x], List.get_mem _ x _, h⟩
  . intro h
    simp only [toPropAssn, σIsEmptyTriangleFor, decide_eq_false_iff_not, not_forall,
      not_not, exists_prop] at h
    have ⟨x, hx, tri⟩ := h
    rcases List.get_of_mem <| List.mem_toFinset.mp hx with ⟨i, rfl⟩
    have : List.get w.points i = w[i] := rfl
    rw [this] at tri hx
    clear this
    use i
    split_ifs
    . simp only [toPropAssn, satisfies_var, decide_eq_true_eq, tri]
    next h =>
      exfalso
      simp only [not_and, not_not] at h
      have sub : [w[a],w[b],w[c]] <+ w.points := by
        have : [w[a],w[b],w[c]] = [a,b,c].map w.points.get := by
          simp [GetElem.getElem, List.getElem_eq_get]
        rw [this]
        apply map_get_sublist
        aesop (add unsafe lt_trans)
      have ⟨wawi, wiwc⟩ := xBounded_of_PtInTriangle (w.sorted.to₃ sub) (σiff.mp tri)
      have : i ≠ a := fun h => by
        rw [h] at tri
        have := not_mem_σPtInTriangle (w.gp sub).perm₁
        have := tri.perm₁
        contradiction
      have : w[a].x < w[i].x := by
        apply lt_of_le_of_ne wawi
        intro h
        exact this <| w.of_eqx h.symm
      have ai : a < i := w.of_sorted_get this
      have : i ≠ c := fun h => by
        rw [h] at tri
        have := not_mem_σPtInTriangle (w.gp sub).perm₂
        have := tri.perm₂
        contradiction
      have : w[i].x < w[c].x := by
        apply lt_of_le_of_ne wiwc
        intro h
        exact this <| w.of_eqx h
      have ic : i < c := w.of_sorted_get this
      rw [h ai ic] at tri
      apply not_mem_σPtInTriangle (w.gp sub) tri

theorem satisfies_leftmostCCWDefs (w : WBPoints) : w.toPropAssn ⊨ pointsCCW w.length := by
  sorry

theorem satisfies_noHoles (w : WBPoints) :
    (∀ (a b c : Point), {a,b,c} ⊆ w.toFinset → ¬σIsEmptyTriangleFor a b c w.toFinset) →
    w.toPropAssn ⊨ theFormula w.length := by
  unfold theFormula
  intro noholes
  simp only [noHoles, satisfies_conj, satisfies_signotopeAxioms, satisfies_insideDefs, and_self,
    satisfies_holeDefs, satisfies_all, Multiset.mem_map, mem_val, mem_univ, true_and,
    forall_exists_index, forall_apply_eq_imp_iff, satisfies_leftmostCCWDefs, and_true]
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
