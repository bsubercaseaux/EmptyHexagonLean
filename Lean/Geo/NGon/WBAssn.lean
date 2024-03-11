import Geo.Definitions.WBPoints
import Geo.Definitions.PtInTriangle
import Geo.Definitions.Structures
import Geo.Definitions.OrientationProperties
import Geo.Orientations
import Geo.NGon.Encoding

namespace Geo.WBPoints
open List Classical LeanSAT.Model PropFun Point
attribute [-simp] getElem_fin

def isCap (w : WBPoints) (a c d : Fin w.length) (o : Orientation) :=
  ∃ b, a < b ∧ b < c ∧ c < d ∧
    σ w[a] w[b] w[c] = o ∧ σ w[b] w[c] w[d] = o

def isCapF (w : WBPoints) (a c d : Fin w.length) :=
  c < d ∧ ∃ b : Fin w.length, isCap w a b c .CW ∧
    σ w[b] w[c] w[d] = .CW ∧ σIsEmptyTriangleFor w[a] w[b] w[d] w.toFinset

@[simp] def toPropAssn (w : WBPoints) : Var w.length → Prop
  | .sigma a b c    => σ w[a] w[b] w[c] = .CCW
  | .inside x a b c => σPtInTriangle w[x] w[a] w[b] w[c]
  | .hole a b c     => σIsEmptyTriangleFor w[a] w[b] w[c] w.toFinset
  | .cap a c d      => isCap w a c d .CW
  | .cup a c d      => isCap w a c d .CCW
  | .capF a d e     => isCapF w a d e

theorem satisfies_signotopeClauses (w : WBPoints) :
    (signotopeClauses w.length).eval w.toPropAssn := by
  simp [signotopeClauses]
  intro i _ j hij k hjk l hkl
  have s : Sorted₄ w[i] w[j] w[k] w[l] := w.sorted₄ hij hjk hkl
  have gp : InGeneralPosition₄ w[i] w[j] w[k] w[l] := w.gp₄ hij hjk hkl
  constructor
  . exact σ_prop₂ s gp
  -- constructor
  -- . exact σ_prop₁ s gp
  -- constructor
  . simp_rw [gp.gp₁.σ_iff, gp.gp₂.σ_iff, gp.gp₃.σ_iff]
    exact σ_prop₄ s gp
  -- . simp_rw [gp.gp₁.σ_iff, gp.gp₄.σ_iff, gp.gp₃.σ_iff]
  --   exact σ_prop₃ s gp

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
  cases gp.gp₁.σ_cases <;> cases gp.gp₂.σ_cases <;>
    cases gp.gp₃.σ_cases <;> cases gp.gp₄.σ_cases <;> simp_all
  next h₁ h₂ h₃ h₄ =>
    rw [σ_prop₁ sorted gp h₁ h₄] at h₃
    contradiction
  next h₁ h₂ h₃ h₄ =>
    rw [σ_prop₃ sorted gp h₁ h₄] at h₃
    contradiction

theorem satisfies_insideClauses (w : WBPoints) : (insideClauses w.length).eval w.toPropAssn := by
  simp [insideClauses]
  intro a _ b hab c hbc x
  constructor
  · intro hax hxb
    exact (insideDefs_aux₁ (w.sorted₄ hax hxb hbc) (w.gp₄ hax hxb hbc)).1
  · intro hbx hxc
    exact (insideDefs_aux₂ (w.sorted₄ hab hbx hxc) (w.gp₄ hab hbx hxc)).1

theorem satisfies_holeDefClauses (w : WBPoints) : (holeDefClauses w.length).eval w.toPropAssn := by
  simp [holeDefClauses, σIsEmptyTriangleFor, mem_toFinset_iff]
  intro a _ b ab c bc H i tri
  have gp₄ : InGeneralPosition₄ w[i] w[a] w[b] w[c] := tri.gp₄_of_gp₃ (w.gp₃ ab bc)
  have ib : i ≠ b := mt (congrArg (w[·])) gp₄.gp₃.ne₁
  have ⟨wawi, wiwc⟩ := xBounded_of_PtInTriangle' (w.sorted₃ ab bc) ((σPtInTriangle_iff gp₄).mp tri)
  have ai : a < i := w.lt_iff.1 <| by
    apply lt_of_le_of_ne wawi
    intro h
    exact gp₄.gp₁.ne₁ <| w.eq_iff.1 h.symm ▸ rfl
  have ic : i < c := w.lt_iff.1 <| by
    apply lt_of_le_of_ne wiwc
    intro h
    exact gp₄.gp₃.ne₂ <| w.eq_iff.1 h ▸ rfl
  exact H i ai ic ib tri

theorem satisfies_leftmostCCWDefs (w : WBPoints) :
    (leftmostCCWClauses w.length).eval w.toPropAssn := by
  simp [leftmostCCWClauses]
  intro i h0i j hij
  let ⟨i+1, hi⟩ := i; let ⟨j+1, hj⟩ := j
  exact List.pairwise_iff_get.1 w.oriented
    ⟨_, Nat.lt_of_succ_lt_succ hi⟩ ⟨_, Nat.lt_of_succ_lt_succ hj⟩ (Nat.lt_of_succ_lt_succ hij)

theorem satisfies_revLexClausesCore {F : Fin n → _} {F' : Fin m → _}
    (hF : ∀ a a', a'.1 = a.1 + 1 → ((F' a').eval τ ↔ F a))
    (ha : a'.1 = a.1 + 1) (hb : b'.1 = b.1 + 1) (hacc : acc → acc'.eval τ) :
    RevLexMid F a b acc → (revLexClausesCore (α := α) F' a' b' acc').eval τ := by
  unfold RevLexMid revLexClausesCore
  have : a' < b' ↔ a < b := by simp [Fin.lt_def, -Fin.val_fin_lt, ha, hb]
  simp [this]; split
  · apply satisfies_revLexClausesCore hF <;> simp [ha, hb]
    · rw [Fin.lt_def] at *; omega
    · simp [hF _ _ ha, hF _ _ hb]
      exact .imp_right <| .imp_right hacc
  · exact hacc

theorem satisfies_revLexClauses (w : WBPoints) : (revLexClauses w.length).eval w.toPropAssn := by
  simp [revLexClauses, length, points]
  intro h5w
  have := w.lex (by omega)
  simp [σRevLex, RevLexMid3] at this
  refine satisfies_revLexClausesCore ?_ (by simp) (by simp; omega) (by simp) this
  rintro ⟨a, ha⟩ ⟨_, ha'⟩ ⟨⟩; simp [getElem, points]

theorem satisfies_baseEncoding (w : WBPoints) : (baseEncoding w.length).eval w.toPropAssn := by
  simp [baseEncoding, satisfies_signotopeClauses, satisfies_insideClauses, satisfies_holeDefClauses,
    satisfies_leftmostCCWDefs, satisfies_revLexClauses]

end WBPoints
