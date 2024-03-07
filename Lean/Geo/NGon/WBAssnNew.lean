import Geo.Definitions.WBPoints
import Geo.Definitions.PtInTriangle
import Geo.Definitions.Structures
import Geo.Definitions.OrientationProperties
import Geo.Orientations
import Geo.NGon.EncodingNew

namespace Geo.WBPoints
open List
open Classical

open LeanSAT.Model PropFun

open Point

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

attribute [-simp] getElem_fin

theorem satisfies_signotopeClauses (w : WBPoints) :
    (signotopeClauses w.length).eval w.toPropAssn := by
  simp [signotopeClauses]
  intro i j hij k hjk l hkl
  have s : Sorted₄ w[i] w[j] w[k] w[l] := w.sorted₄ hij hjk hkl
  have gp : InGeneralPosition₄ w[i] w[j] w[k] w[l] := w.gp₄ hij hjk hkl
  constructor
  . exact σ_prop₂ s gp
  constructor
  . exact σ_prop₁ s gp
  constructor
  . simp_rw [gp.gp₁.σ_iff, gp.gp₂.σ_iff, gp.gp₃.σ_iff]
    exact σ_prop₄ s gp
  . simp_rw [gp.gp₁.σ_iff, gp.gp₄.σ_iff, gp.gp₃.σ_iff]
    exact σ_prop₃ s gp

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
  intro a b hab c hbc x
  constructor
  · intro hax hxb
    exact (insideDefs_aux₁ (w.sorted₄ hax hxb hbc) (w.gp₄ hax hxb hbc)).1
  · intro hbx hxc
    exact (insideDefs_aux₂ (w.sorted₄ hab hbx hxc) (w.gp₄ hab hbx hxc)).1

theorem satisfies_holeDefClauses (w : WBPoints) : (holeDefClauses w.length).eval w.toPropAssn := by
  simp [holeDefClauses, σIsEmptyTriangleFor, mem_toFinset_iff]
  intro a b ab c bc H i tri
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

theorem satisfies_triangleEncoding (w : WBPoints) :
    ¬σHasEmptyTriangle w.toFinset →
    (triangleEncoding w.length).eval w.toPropAssn := by
  simp [triangleEncoding, satisfies_baseEncoding, noHoleClauses,
    σIsEmptyTriangleFor, mem_toFinset_iff, σHasEmptyTriangle]
  intro noholes a b hab c hbc
  exact noholes a b (ne_of_lt hab <| w.eq_iff.1 <| · ▸ rfl)
                  c (ne_of_lt (hab.trans hbc) <| w.eq_iff.1 <| · ▸ rfl)
                    (ne_of_lt hbc <| w.eq_iff.1 <| · ▸ rfl)

theorem satisfies_capDef (w : WBPoints) {a b c d : Fin (length w)}
    (ab : a < b) (bc : b < c) (cd : c < d) : (capDef a b c d).eval w.toPropAssn := by
  simp [capDef, isCap]; intro h1 h2
  exact ⟨_, ab, bc, cd, (w.gp₃ ab bc).σ_iff.1 h1, (w.gp₃ bc cd).σ_iff.1 h2⟩

theorem satisfies_capDef2 (w : WBPoints) {a c d : Fin (length w)} :
    (capDef2 a c d).eval w.toPropAssn := by
  simp [capDef2, isCap]; intro b ab bc cd h1 h2
  have gp := w.gp₄ ab bc cd
  exact gp.gp₃.σ_iff.2 <| σ_prop₃ (w.sorted₄ ab bc cd) gp h1 h2

theorem satisfies_cupDef (w : WBPoints) {a b c d : Fin (length w)}
    (ab : a < b) (bc : b < c) (cd : c < d) : (cupDef a b c d).eval w.toPropAssn := by
  simp [cupDef, isCap]; intro h1 h2
  exact ⟨_, ab, bc, cd, h1, h2⟩

theorem satisfies_cupDef2 (w : WBPoints) {a c d : Fin (length w)} :
    (cupDef2 a c d).eval w.toPropAssn := by
  simp [cupDef2, isCap]; intro b ab bc cd h1 h2
  exact σ_prop₁ (w.sorted₄ ab bc cd) (w.gp₄ ab bc cd) h1 h2

theorem satisfies_capFDef (w : WBPoints) {a b c d : Fin (length w)} (bc : b < c) (cd : c < d)
    (hh : σIsEmptyTriangleFor w[a] w[b] w[d] w.toFinset) : (capFDef a b c d).eval w.toPropAssn := by
  simp [capFDef, isCapF]; intro h1 h2
  exact ⟨cd, _, h2, (w.gp₃ bc cd).σ_iff.1 h1, hh⟩

theorem satisfies_no6Hole3Below {w : WBPoints} (hw : ¬σHasEmptyNGon 6 w.toFinset)
    {a c d e : Fin (length w)}
    (ha : (0 : Fin (w.rest.length+1)) < a) (de : d < e)
    (ace : σIsEmptyTriangleFor w[a] w[c] w[e] w.toFinset) :
    (no6Hole3Below a c d e).eval w.toPropAssn := by
  simp [no6Hole3Below]; intro ⟨b, ab, bc, cd, abc, bcd⟩ cde
  sorry

theorem satisfies_no6Hole4Above {w : WBPoints} (hw : ¬σHasEmptyNGon 6 w.toFinset)
    {a d e f : Fin (length w)}
    (ha : (0 : Fin (w.rest.length+1)) < a) (ef : e < f) :
    (no6Hole4Above a d e f).eval w.toPropAssn := by
  simp [no6Hole4Above]; intro ⟨de, c, ⟨b, ab, bc, cd, abc, bcd⟩, cde, ace⟩
  refine (w.gp₃ de ef).σ_iff'.1 fun def_ => ?_
  sorry

theorem satisfies_no6Hole2Below {w : WBPoints} (hw : ¬σHasEmptyNGon 6 w.toFinset)
    {a c e f : Fin (length w)}
    (ha : (0 : Fin (w.rest.length+1)) < a) (ce : c ≠ e) :
    (no6Hole2Below a c f e).eval w.toPropAssn := by
  simp [no6Hole2Below]; intro ⟨b, ab, bc, cf, abc, bcd⟩ ⟨d, ad, de, ef, ade, def_⟩ hh
  split_ifs at hh with ce <;> simp at hh
  · sorry
  · replace ce := lt_of_le_of_ne (not_lt.1 ce) (Ne.symm ‹_›)
    sorry

theorem satisfies_no6Hole1Below {w : WBPoints} (hw : ¬σHasEmptyNGon 6 w.toFinset)
    {a d e f : Fin (length w)}
    (ha : (0 : Fin (w.rest.length+1)) < a) (df : d < f) (ae : a < e) (ef : e < f) (de : d ≠ e) :
    (no6Hole1Below a d f e).eval w.toPropAssn := by
  simp [no6Hole1Below]; intro ⟨df, c, ⟨b, ab, bc, cd, abc, bcd⟩, cdf, acf⟩ aef
  sorry

theorem satisfies_hexagonEncoding (w : WBPoints) (hw : ¬σHasEmptyNGon 6 w.toFinset) :
    (hexagonEncoding w.length).eval w.toPropAssn := by
  simp [hexagonEncoding, satisfies_baseEncoding, no6HoleClauses1, no6HoleClauses2, no6HoleClauses3]
  refine ⟨
    fun a ha b ab c bc d cd => ⟨?_, ?_, fun _ => ⟨fun hh => ⟨?_, ?_⟩, fun _ => ?_⟩⟩,
    fun a _ b _ c _ => ⟨?_, ?_⟩,
    fun a ha b _ c bc p ap pc bp => ⟨fun _ _ => ?_, fun _ => ?_⟩⟩
  · with_reducible exact satisfies_capDef w ab bc cd
  · with_reducible exact satisfies_cupDef w ab bc cd
  · with_reducible exact satisfies_capFDef w bc cd hh
  · with_reducible exact satisfies_no6Hole3Below hw ha cd hh
  · with_reducible exact satisfies_no6Hole4Above hw ha cd
  · with_reducible exact satisfies_capDef2 w
  · with_reducible exact satisfies_cupDef2 w
  · with_reducible exact satisfies_no6Hole2Below hw ha bp
  · with_reducible exact satisfies_no6Hole1Below hw ha bc ap pc bp

end WBPoints
