import Geo.Definitions.WBPoints
import Geo.Definitions.PtInTriangle
import Geo.Definitions.Structures
import Geo.Definitions.OrientationProperties
import Geo.Orientations

import Geo.Triangle.Formula

namespace Geo.WBPoints
open List
open Classical

open LeanSAT.Model PropFun

open Point

open Classical in
noncomputable def toPropAssn (w : WBPoints) : PropAssignment (Var w.length)
  | .sigma a b c ..    => σ w[a] w[b] w[c] = .CCW
  | .inside x a b c .. => decide $ σPtInTriangle w[x] w[a] w[b] w[c]
  | .hole a b c ..     => decide $ σIsEmptyTriangleFor w[a] w[b] w[c] w.toFinset

theorem satisfies_orientationConstraint (w : WBPoints) (i j k l : Fin w.length) :
    i < j → j < k → k < l → w.toPropAssn ⊨ orientationConstraint i j k l := by
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
  simp only [orientationConstraint, satisfies_conj, satisfies_impl, satisfies_var,
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

theorem satisfies_orientationConstraints (w : WBPoints) : w.toPropAssn |> orientationConstraints w.length := by
  unfold toPropAssn
  simp only [orientationConstraints, satisfies_all, Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and,
    forall_exists_index, forall_apply_eq_imp_iff]
  intros
  apply satisfies_orientationConstraint <;> assumption

theorem insideDefs_aux₁ {a x b c : Point} : Sorted₄ a x b c → InGeneralPosition₄ a x b c →
    (σPtInTriangle x a b c ↔
      ((σ a b c = .CCW ↔ σ a x c = .CCW) ∧ (σ a x b ≠ .CCW ↔ σ a b c = .CCW))) := by
  intro sorted gp
  simp only [σPtInTriangle,
    σ_perm₂ a b x,
    σ_perm₂ a c x,
    σ_perm₂ a c b,
    σ_perm₂ b c x, σ_perm₁ b x c,
    σ_perm₂ b c a, σ_perm₁ b a c,
    gp.gp₁.σ_iff]
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
  simp only [σPtInTriangle,
    σ_perm₂ a c x,
    σ_perm₂ a c b,
    σ_perm₂ b c x,
    σ_perm₂ b c a, σ_perm₁ b a c,
    gp.gp₄.σ_iff]
  cases gp.gp₁.σ_cases <;> cases gp.gp₂.σ_cases <;> cases gp.gp₃.σ_cases <;> cases gp.gp₄.σ_cases <;> simp_all [-getElem_fin]
  next h₁ h₂ h₃ h₄ =>
    rw [σ_prop₁ sorted gp h₁ h₄] at h₃
    contradiction
  next h₁ h₂ h₃ h₄ =>
    rw [σ_prop₃ sorted gp h₁ h₄] at h₃
    contradiction

theorem satisfies_insideDefs (w : WBPoints) : w.toPropAssn |> insideDefs w.length := by
  unfold insideDefs xIsInsideDef
  simp only [satisfies_all, Multiset.mem_map, forall_exists_index, forall_apply_eq_imp_iff, Finset.mem_val,
    Finset.mem_univ, true_and]
  intro a b c hab hbc x
  constructor
  · intro hax hxb
    have : [w[a], w[x], w[b], w[c]] <+ w.points := by
      have : [w[a], w[x], w[b], w[c]] = [a,x,b,c].map w.points.get := by
        simp [GetElem.getElem, List.getElem_eq_get]
      rw [this]
      apply map_get_sublist
      have : a < c := hab.trans hbc
      have : x < c := hxb.trans hbc
      simp [*]
    simp [toPropAssn, -getElem_fin]
    exact insideDefs_aux₁ (w.sorted.to₄ this) (PointListInGeneralPosition.to₄ w.gp this)
  · intro hbx hxc
    have : [w[a], w[b], w[x], w[c]] <+ w.points := by
      have : [w[a], w[b], w[x], w[c]] = [a,b,x,c].map w.points.get := by
        simp [GetElem.getElem, List.getElem_eq_get]
      rw [this]
      apply map_get_sublist
      have : a < x := hab.trans hbx
      have : a < c := hab.trans hbc
      simp [*]
    simp [toPropAssn, -getElem_fin]
    exact insideDefs_aux₂ (w.sorted.to₄ this) (PointListInGeneralPosition.to₄ w.gp this)

/-- There used to be a declaration in `Formula.lean` called
`notHoleOfPointInside`; it is just one direction of `holeDefs` -/
theorem satisfies_notHoleOfPointInside (w : WBPoints) (a b c : Fin w.length) :
    (∃ x, w.toPropAssn (Var.inside x a b c)) → ¬ w.toPropAssn (Var.hole a b c) := by
  simp only [satisfies_all, Multiset.mem_map, forall_exists_index, forall_apply_eq_imp_iff, Finset.mem_val, Finset.mem_univ, true_and]
  intro x
  simp only [toPropAssn, decide_eq_true_eq, σIsEmptyTriangleFor, toFinset, coe_toFinset,
    Set.mem_setOf_eq, not_forall, not_not, exists_prop]
  intro h
  exact ⟨w[x], List.get_mem _ x _, h⟩

theorem satisfies_hasPointInside (w : WBPoints) (a b c : Fin w.length) :
    a < b → b < c →
    ¬ w.toPropAssn (Var.hole a b c) → ∃ x, a < x ∧ x < c ∧ x ≠ b ∧ w.toPropAssn (Var.inside x a b c) := by
  intro ab bc
  unfold toPropAssn σIsEmptyTriangleFor
  simp only [Finset.mem_coe, getElem_fin, decide_eq_true_eq, not_forall, not_not, exists_prop,
    forall_exists_index, and_imp]
  intro x hx tri
  rcases List.get_of_mem <| List.mem_toFinset.mp hx with ⟨i, rfl⟩
  have : List.get w.points i = w[i] := rfl
  rw [this] at tri hx
  clear this
  use i
  have sub : [w[a],w[b],w[c]] <+ w.points := by
    have : [w[a],w[b],w[c]] = [a,b,c].map w.points.get := by
      simp [GetElem.getElem, List.getElem_eq_get]
    rw [this]
    apply map_get_sublist
    aesop (add unsafe lt_trans)
  have ia : i ≠ a := fun h => by
    rw [h] at tri
    have := not_mem_σPtInTriangle (w.gp sub).perm₁
    have := tri.perm₁
    contradiction
  have ib : i ≠ b := fun h => by
    rw [h] at tri
    have := not_mem_σPtInTriangle (w.gp sub).perm₁.perm₁
    contradiction
  have ic : i ≠ c := fun h => by
    rw [h] at tri
    have := not_mem_σPtInTriangle (w.gp sub).perm₂
    have := tri.perm₂
    contradiction
  have : InGeneralPosition₄ w[i] w[a] w[b] w[c] := tri.gp₄_of_gp₃ (w.gp sub)
  have ⟨wawi, wiwc⟩ := xBounded_of_PtInTriangle (w.sorted.to₃ sub) ((σPtInTriangle_iff this).mp tri)
  have : w[a].x < w[i].x := by
    apply lt_of_le_of_ne wawi
    intro h
    exact ia <| w.of_eqx h.symm
  have ai : a < i := w.of_sorted_get this
  have : w[i].x < w[c].x := by
    apply lt_of_le_of_ne wiwc
    intro h
    exact ic <| w.of_eqx h
  have ic : i < c := w.of_sorted_get this
  simp_all

theorem satisfies_holeDefs (w : WBPoints) : w.toPropAssn |> holeDefs w.length := by
  simp [holeDefs]
  intro a b c hab hbc
  constructor
  · intro h x _ _ _
    have := satisfies_notHoleOfPointInside w a b c
    rw [imp_not_comm] at this
    specialize this h
    simp at this
    apply this
  · intro h
    by_contra contra
    have ⟨x,hax,hxc,hxb,hinside⟩ := satisfies_hasPointInside w a b c hab hbc contra
    specialize h x hax hxc hxb
    rw [h] at hinside
    contradiction

theorem satisfies_leftmostCCWDefs (w : WBPoints) : w.toPropAssn |> pointsCCW w.length := by
  unfold pointsCCW
  simp
  intro i j h0i hij
  have ⟨k, hk⟩ : ∃ k, i.1 = k + 1 := by
    apply Nat.exists_eq_succ_of_ne_zero
    have : 0 < i.1 := h0i
    linarith
  have ⟨l, hl⟩ : ∃ l, j.1 = l + 1 := by
    apply Nat.exists_eq_succ_of_ne_zero
    have : 0 < j.1 := h0i.trans hij
    linarith
  unfold toPropAssn
  cases i
  cases j
  simp at hk hl
  simp [GetElem.getElem, points, hk, hl]
  apply List.pairwise_iff_get.mp w.oriented
  simp at *
  linarith

theorem satisfies_noHoles (w : WBPoints) :
    ¬σHasEmptyTriangle w.toFinset →
    (w.toPropAssn |> theFormula w.length) := by
  unfold theFormula
  intro noholes
  simp only [noHoles, satisfies_conj, satisfies_orientationConstraints, satisfies_insideDefs, and_self,
    satisfies_holeDefs, satisfies_all, Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and,
    forall_exists_index, forall_apply_eq_imp_iff, satisfies_leftmostCCWDefs, and_true]
  intro a b c hab hbc
  unfold toPropAssn
  simp only [getElem_fin, Bool.not_eq_true', decide_eq_false_iff_not]
  simp only [σHasEmptyTriangle, not_exists, not_and] at noholes
  apply noholes _ (w.get_mem_toFinset a) _ (w.get_mem_toFinset b) _ (w.get_mem_toFinset c)
    (fun h' => ne_of_lt hab <| (w.of_eqx <| congrArg (·.x) h'))
    (fun h' => ne_of_lt (hab.trans hbc) <| (w.of_eqx <| congrArg (·.x) h'))
    (fun h' => ne_of_lt hbc <| (w.of_eqx <| congrArg (·.x) h'))

end WBPoints
