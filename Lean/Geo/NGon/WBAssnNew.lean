import Geo.Definitions.WBPoints
import Geo.Definitions.PtInTriangle
import Geo.Definitions.Structures
import Geo.Definitions.OrientationProperties
import Geo.Orientations
import Geo.Triangle.EncodingNew

namespace Geo.WBPoints
open List
open Classical

open LeanSAT.Model PropFun

open Point

def isCap (w : WBPoints) (a c d : Fin w.length) (o : Orientation) :=
  ∃ b, a < b ∧ b < c ∧ c < d ∧
    σ w[a] w[b] w[c] = o ∧ σ w[a] w[c] w[d] = o

def isCapF (w : WBPoints) (a d e : Fin w.length) :=
  ∃ c : Fin w.length, isCap w a c d .CW ∧
    σ w[c] w[d] w[e] = .CW ∧ σIsEmptyTriangleFor w[a] w[c] w[e] w.toFinset

@[simp] def toPropAssn (w : WBPoints) : Var w.length → Prop
  | .sigma a b c    => σ w[a] w[b] w[c] = .CCW
  | .inside x a b c => σPtInTriangle w[x] w[a] w[b] w[c]
  | .hole a b c     => σIsEmptyTriangleFor w[a] w[b] w[c] w.toFinset
  | .cap a c d      => isCap w a c d .CW
  | .cup a c d      => isCap w a c d .CCW
  | .capF a d e     => isCapF w a d e

attribute [-simp] getElem_fin

theorem satisfies_signotopeClause (w : WBPoints) (i j k l : Fin w.length) :
    i < j → j < k → k < l → (signotopeClause i j k l).eval w.toPropAssn := by
  simp [signotopeClause]
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
  constructor
  . exact σ_prop₂ s gp
  constructor
  . exact σ_prop₁ s gp
  constructor
  . simp_rw [gp.gp₁.σ_iff, gp.gp₂.σ_iff, gp.gp₃.σ_iff]
    exact σ_prop₄ s gp
  . simp_rw [gp.gp₁.σ_iff, gp.gp₄.σ_iff, gp.gp₃.σ_iff]
    exact σ_prop₃ s gp

theorem satisfies_signotopeClauses (w : WBPoints) : (signotopeClauses w.length).eval w.toPropAssn := by
  simp (config := {contextual := true}) [signotopeClauses, satisfies_signotopeClause]

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
  cases gp.gp₁.σ_cases <;> cases gp.gp₂.σ_cases <;> cases gp.gp₃.σ_cases <;>
    cases gp.gp₄.σ_cases <;> simp_all
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
  cases gp.gp₁.σ_cases <;> cases gp.gp₂.σ_cases <;> cases gp.gp₃.σ_cases <;> cases gp.gp₄.σ_cases <;> simp_all
  next h₁ h₂ h₃ h₄ =>
    rw [σ_prop₁ sorted gp h₁ h₄] at h₃
    contradiction
  next h₁ h₂ h₃ h₄ =>
    rw [σ_prop₃ sorted gp h₁ h₄] at h₃
    contradiction

theorem satisfies_insideClauses (w : WBPoints) : (insideClauses w.length).eval w.toPropAssn := by
  simp [insideClauses, xIsInsideClause]
  intro a b hab c hbc x
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
    exact insideDefs_aux₂ (w.sorted.to₄ this) (PointListInGeneralPosition.to₄ w.gp this)

theorem satisfies_holeDefClauses (w : WBPoints) : (holeDefClauses w.length).eval w.toPropAssn := by
  simp [holeDefClauses, σIsEmptyTriangleFor, mem_toFinset_iff]
  intro a b ab c bc
  refine ⟨fun H _ _ _ _ => H _, fun H i tri => ?_⟩
  have sub : [w[a],w[b],w[c]] <+ w.points := by
    have : [w[a],w[b],w[c]] = [a,b,c].map w.points.get := by
      simp [GetElem.getElem, List.getElem_eq_get]
    rw [this]
    apply map_get_sublist
    aesop (add unsafe lt_trans)
  have gp₄ : InGeneralPosition₄ w[i] w[a] w[b] w[c] := tri.gp₄_of_gp₃ (w.gp sub)
  have ib : i ≠ b := mt (congrArg (w[·])) gp₄.gp₃.ne₁
  have ⟨wawi, wiwc⟩ := xBounded_of_PtInTriangle (w.sorted.to₃ sub) ((σPtInTriangle_iff gp₄).mp tri)
  have ai : a < i := w.of_sorted_get <| by
    apply lt_of_le_of_ne wawi
    intro h
    exact gp₄.gp₁.ne₁ <| w.of_eqx h.symm ▸ rfl
  have ic : i < c := w.of_sorted_get <| by
    apply lt_of_le_of_ne wiwc
    intro h
    exact gp₄.gp₃.ne₂ <| w.of_eqx h ▸ rfl
  exact H i ai ic ib tri

theorem satisfies_leftmostCCWDefs (w : WBPoints) : (leftmostCCWClauses w.length).eval w.toPropAssn := by
  simp [leftmostCCWClauses]
  intro i h0i j hij
  let ⟨i+1, hi⟩ := i; let ⟨j+1, hj⟩ := j
  exact List.pairwise_iff_get.1 w.oriented
    ⟨_, Nat.lt_of_succ_lt_succ hi⟩ ⟨_, Nat.lt_of_succ_lt_succ hj⟩ (Nat.lt_of_succ_lt_succ hij)

theorem satisfies_noHoles (w : WBPoints) :
    ¬σHasEmptyTriangle w.toFinset →
    (theEncoding w.length).eval w.toPropAssn := by
  simp [theEncoding, satisfies_signotopeClauses, satisfies_insideClauses, satisfies_holeDefClauses,
    satisfies_leftmostCCWDefs, noHoleClauses, σIsEmptyTriangleFor, mem_toFinset_iff, σHasEmptyTriangle]
  intro noholes a b hab c hbc
  exact noholes a b (ne_of_lt hab <| w.of_eqx <| · ▸ rfl)
                  c (ne_of_lt (hab.trans hbc) <| w.of_eqx <| · ▸ rfl)
                    (ne_of_lt hbc <| w.of_eqx <| · ▸ rfl)

end WBPoints
