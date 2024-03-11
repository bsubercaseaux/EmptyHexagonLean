import Geo.Definitions.CanonicalPoints
import Geo.Definitions.PtInTriangle
import Geo.Definitions.Structures
import Geo.Definitions.OrientationProperties
import Geo.Orientations
import Geo.KGon.Encoding

namespace Geo.CanonicalPoints
open List Classical LeanSAT.Model PropFun Point
attribute [-simp] getElem_fin

def isCap (w : CanonicalPoints) (a c d : Fin w.rlen) (o : Orientation) :=
  ∃ b, a < b ∧ b < c ∧ c < d ∧
    σ w+[a] w+[b] w+[c] = o ∧ σ w+[b] w+[c] w+[d] = o

def isCapF (w : CanonicalPoints) (a c d : Fin w.rlen) :=
  c < d ∧ ∃ b : Fin w.rlen, isCap w a b c .cw ∧
    σ w+[b] w+[c] w+[d] = .cw ∧ σIsEmptyTriangleFor w+[a] w+[b] w+[d] w.toFinset

@[simp] def toPropAssn (w : CanonicalPoints) : Var w.rlen → Prop
  | .sigma a b c    => σ w+[a] w+[b] w+[c] = .ccw
  | .inside x a b c => σPtInTriangle w+[x] w+[a] w+[b] w+[c]
  | .hole a b c     => σIsEmptyTriangleFor w+[a] w+[b] w+[c] w.toFinset
  | .cap a c d      => isCap w a c d .cw
  | .cup a c d      => isCap w a c d .ccw
  | .capF a d e     => isCapF w a d e

theorem satisfies_signotopeClauses (w : CanonicalPoints) :
    (signotopeClauses w.rlen).eval w.toPropAssn := by
  simp [signotopeClauses]
  intro i j hij k hjk l hkl
  have s := w.sorted₄' hij hjk hkl
  have gp := w.gp₄' hij hjk hkl
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
      ((σ a b c = .ccw ↔ σ a x c = .ccw) ∧ (σ a x b ≠ .ccw ↔ σ a b c = .ccw))) := by
  intro sorted gp
  simp only [σPtInTriangle, σ_perm₂ a b x]
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
      ((σ a b c = .ccw ↔ σ a x c = .ccw) ∧ (σ b x c ≠ .ccw ↔ σ a b c = .ccw))) := by
  intro sorted gp
  simp only [σPtInTriangle, σ_perm₁ x b c]
  cases gp.gp₁.σ_cases <;> cases gp.gp₂.σ_cases <;>
    cases gp.gp₃.σ_cases <;> cases gp.gp₄.σ_cases <;> simp_all
  next h₁ h₂ h₃ h₄ =>
    rw [σ_prop₁ sorted gp h₁ h₄] at h₃
    contradiction
  next h₁ h₂ h₃ h₄ =>
    rw [σ_prop₃ sorted gp h₁ h₄] at h₃
    contradiction

theorem satisfies_insideClauses (w : CanonicalPoints) : (insideClauses w.rlen).eval w.toPropAssn := by
  simp [insideClauses]
  intro a b hab c hbc x
  constructor
  · intro hax hxb
    exact (insideDefs_aux₁ (w.sorted₄' hax hxb hbc) (w.gp₄' hax hxb hbc)).1
  · intro hbx hxc
    exact (insideDefs_aux₂ (w.sorted₄' hab hbx hxc) (w.gp₄' hab hbx hxc)).1

theorem satisfies_holeDefClauses (w : CanonicalPoints) : (holeDefClauses w.rlen).eval w.toPropAssn := by
  simp [holeDefClauses, σIsEmptyTriangleFor, mem_toFinset_iff]
  intro a b ab c bc H i tri
  have gp₄ : InGeneralPosition₄ w[i] w+[a] w+[b] w+[c] := tri.gp₄_of_gp₃ (w.gp₃' ab bc)
  have ib : i ≠ b.succ := mt (congrArg (w[·])) gp₄.gp₃.ne₁
  have ⟨wawi, wiwc⟩ := xBounded_of_PtInTriangle' (w.sorted₃' ab bc) ((σPtInTriangle_iff gp₄).mp tri)
  have ai : a.succ < i := w.lt_iff.1 <| by
    apply lt_of_le_of_ne wawi
    intro h
    exact gp₄.gp₁.ne₁ <| w.eq_iff.1 h.symm ▸ rfl
  have ic : i < c.succ := w.lt_iff.1 <| by
    apply lt_of_le_of_ne wiwc
    intro h
    exact gp₄.gp₃.ne₂ <| w.eq_iff.1 h ▸ rfl
  obtain rfl | ⟨i,rfl⟩ := i.eq_zero_or_eq_succ
  · cases ai
  · exact H i (Fin.succ_lt_succ_iff.1 ai) (Fin.succ_lt_succ_iff.1 ic) (mt Fin.succ_inj.2 ib) tri

theorem satisfies_revLexClausesCore {F : Fin n → _} {F' : Fin m → _}
    (hF : ∀ a a', a'.1 = a.1 → ((F' a').eval τ ↔ F a))
    (ha : a'.1 = a.1) (hb : b'.1 = b.1) (hacc : acc → acc'.eval τ) :
    RevLexMid F a b acc → (revLexClausesCore (α := α) F' a' b' acc').eval τ := by
  unfold RevLexMid revLexClausesCore
  have : a' < b' ↔ a < b := by simp [Fin.lt_def, -Fin.val_fin_lt, ha, hb]
  simp [this]; split
  · apply satisfies_revLexClausesCore hF <;> simp [ha, hb]
    simp [hF _ _ ha, hF _ _ hb]
    exact .imp_right <| .imp_right hacc
  · exact hacc

theorem satisfies_revLexClauses (w : CanonicalPoints) : (revLexClauses w.rlen).eval w.toPropAssn := by
  simp [revLexClauses, length, points]
  intro h4w
  have := w.lex (by omega)
  simp [σRevLex, RevLexMid3] at this
  refine satisfies_revLexClausesCore ?_ rfl rfl (by simp) this
  rintro ⟨a, ha⟩ ⟨_, ha'⟩ ⟨⟩; simp [getElem, points]

theorem satisfies_baseEncoding (w : CanonicalPoints) : (baseEncoding w.rlen).eval w.toPropAssn := by
  simp [baseEncoding, satisfies_signotopeClauses, satisfies_insideClauses, satisfies_holeDefClauses,
    satisfies_revLexClauses]

end CanonicalPoints
