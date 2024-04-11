import Geo.Definitions.CanonicalPoints
import Geo.Definitions.PtInTriangle
import Geo.Definitions.Structures
import Geo.Definitions.OrientationProperties
import Geo.Definitions.Orientations
import Geo.KGon.Encoding

namespace Geo.CanonicalPoints
open List Classical LeanSAT.Model PropFun Point
attribute [-simp] getElem_fin

def isArc (w : CanonicalPoints) (o : Orientation) (sz : Nat) (a c d : Fin w.rlen) :=
  match sz with
  | 0 => σ w+[a] w+[c] w+[d] = o
  | l+1 => c < d ∧ ∃ b, a < b ∧ b < c ∧
    isArc w o l a b c ∧ σ w+[b] w+[c] w+[d] = o

theorem isArc_succ {w : CanonicalPoints} {o : Orientation} {sz : Nat} {a c d : Fin w.rlen} :
    isArc w o (sz+1) a c d → isArc w o sz a c d
  | ⟨cd, b, ab, bc, h1, h2⟩ => match sz with
    | 0 => match o with
      | .ccw => σ_prop₁ (w.sorted₄' ab bc cd) (w.gp₄' ab bc cd) h1 h2
      | .cw => σ_prop₃ (w.sorted₄' ab bc cd) (w.gp₄' ab bc cd) h1 h2
      | .collinear => nomatch (w.gp₃' bc cd).σ_ne h2
    | _+1 => ⟨cd, b, ab, bc, isArc_succ h1, h2⟩

def isCapF (w : CanonicalPoints) (a c d : Fin w.rlen) (holes := true) :=
  c < d ∧ ∃ b : Fin w.rlen, isArc w .cw 1 a b c ∧
    σ w+[b] w+[c] w+[d] = .cw ∧ (holes → σIsEmptyTriangleFor w+[a] w+[b] w+[d] w.toFinset)

@[simp] def toPropAssn (w : CanonicalPoints) (holes := true) : Var w.rlen → Prop
  | .sigma a b c     => σ w+[a] w+[b] w+[c] = .ccw
  | .inside x a b c  => σPtInTriangle w+[x] w+[a] w+[b] w+[c]
  | .hole₀ a b c     => holes → σIsEmptyTriangleFor w[a] w+[b] w+[c] w.toFinset
  | .arc1 o sz a c d => isArc w o (sz+1) a c d
  | .capF a d e      => isCapF w a d e holes

@[simp] theorem eval_holeIf (w : CanonicalPoints) {a b c : Fin w.rlen} :
    (holeIf holes a b c).eval (w.toPropAssn holes) ↔
    (holes → σIsEmptyTriangleFor w+[a] w+[b] w+[c] w.toFinset) := by
  simp [holeIf, Var.hole]; cases holes <;> simp

theorem satisfies_signotopeClauses1 (w : CanonicalPoints) :
    (signotopeClauses1 w.rlen).eval (w.toPropAssn holes) := by
  simp [signotopeClauses1]
  intro i j hij k hjk l hkl
  have s := w.sorted₄' hij hjk hkl
  have gp := w.gp₄' hij hjk hkl
  constructor
  · exact σ_prop₂ s gp
  · simp_rw [gp.gp₁.σ_iff, gp.gp₂.σ_iff, gp.gp₃.σ_iff]
    exact σ_prop₄ s gp

theorem satisfies_signotopeClauses2 (w : CanonicalPoints) :
    (signotopeClauses2 w.rlen).eval (w.toPropAssn holes) := by
  simp [signotopeClauses2]
  intro i j hij k hjk l hkl
  have s := w.sorted₄' hij hjk hkl
  have gp := w.gp₄' hij hjk hkl
  constructor
  · exact σ_prop₁ s gp
  · simp_rw [gp.gp₁.σ_iff, gp.gp₄.σ_iff, gp.gp₃.σ_iff]
    exact σ_prop₃ s gp

theorem insideDefs_aux₁ {a x b c : Point} : Sorted₄ a x b c → InGenPos₄ a x b c →
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

theorem insideDefs_aux₂ {a b x c : Point} : Sorted₄ a b x c → InGenPos₄ a b x c →
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

theorem satisfies_insideClauses (w : CanonicalPoints) : (insideClauses w.rlen).eval (w.toPropAssn holes) := by
  simp [insideClauses]
  intro a b hab c hbc x
  constructor
  · intro hax hxb tri
    have ⟨l,r⟩ := (insideDefs_aux₁ (w.sorted₄' hax hxb hbc) (w.gp₄' hax hxb hbc)).1 tri
    constructor
    · exact l
    · rw [←r]
  · intro hbx hxc tri
    have ⟨l,r⟩ := (insideDefs_aux₂ (w.sorted₄' hab hbx hxc) (w.gp₄' hab hbx hxc)).1 tri
    constructor
    · exact l
    · rw [←r]

theorem holeDefs_aux (w : CanonicalPoints) {b c : Fin (rlen w)} {a i : Fin (length w)}
    (ab : a < b.succ) (bc : b < c)
    (H : ∀ i, a < i.succ → i < c → ¬i = b → ¬σPtInTriangle w+[i] w[a] w+[b] w+[c]) :
    ¬σPtInTriangle w[i] w[a] w+[b] w+[c] := fun tri => by
  have gp₃ := CanonicalPoints.gp₃ (k := c.succ) ab bc.succ₂
  have sorted₃ := CanonicalPoints.sorted₃ (k := c.succ) ab bc.succ₂
  have gp₄ : InGenPos₄ w[i] w[a] w+[b] w+[c] := tri.gp₄_of_gp₃ gp₃
  have ib : i ≠ b.succ := mt (congrArg (w[·])) gp₄.gp₃.ne₁
  have ⟨wawi, wiwc⟩ := xBounded_of_PtInTriangle' sorted₃ ((σPtInTriangle_iff gp₄).mp tri)
  have ai : a < i := w.lt_iff.1 <| by
    apply lt_of_le_of_ne wawi
    intro h
    exact gp₄.gp₁.ne₁ <| w.eq_iff.1 h.symm ▸ rfl
  have ic : i < c.succ := w.lt_iff.1 <| by
    apply lt_of_le_of_ne wiwc
    intro h
    exact gp₄.gp₃.ne₂ <| w.eq_iff.1 h ▸ rfl
  obtain rfl | ⟨i,rfl⟩ := i.eq_zero_or_eq_succ
  · cases ai
  · exact H i ai (Fin.succ_lt_succ_iff.1 ic) (mt Fin.succ_inj.2 ib) tri

theorem satisfies_holeDefClauses0 (w : CanonicalPoints) :
    (holeDefClauses0 w.rlen).eval (w.toPropAssn holes) := by
  simp [holeDefClauses0, σIsEmptyTriangleFor, mem_toFinset_iff]
  intro b c bc H _
  intro i
  refine holeDefs_aux w (Fin.succ_pos _) bc fun i _ ic ib ⟨h1, h2, h3⟩ => ?_
  obtain ib | ib := lt_or_gt_of_ne ib
  · rw [σ_perm₂] at h1
    have h1 := (congrArg (-·) (w.σ_0 ib)).symm.trans h1 -- FIXME: rw
    have h1 := h1.trans (w.σ_0 bc) -- FIXME: rw
    cases h1
  · rw [σ_perm₁, H i ib ic] at h3
    have h3 := h3.trans (w.σ_0 bc) -- FIXME: rw
    cases h3

theorem satisfies_holeDefClauses1 (w : CanonicalPoints) :
    (holeDefClauses1 w.rlen).eval (w.toPropAssn holes) := by
  simp [holeDefClauses1, σIsEmptyTriangleFor, mem_toFinset_iff]
  intro a b ab c bc H _ i
  exact holeDefs_aux w ab.succ₂ bc (fun i h => H i (Fin.succ_lt_succ_iff.1 h))

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
termination_by b

theorem satisfies_revLexClauses (w : CanonicalPoints) :
    (revLexClauses w.rlen).eval (w.toPropAssn holes) := by
  simp [revLexClauses, length, points]
  intro h4w
  have := w.lex (by rw [rlen] at h4w; omega)
  simp [σRevLex, RevLexMid3] at this
  refine satisfies_revLexClausesCore ?_ rfl rfl (by simp) this
  rintro ⟨a, ha⟩ ⟨_, ha'⟩ ⟨⟩; simp [getElem, points]

theorem satisfies_baseEncoding (w : CanonicalPoints) :
    (baseEncoding w.rlen holes).eval (w.toPropAssn holes) := by
  simp [baseEncoding, satisfies_signotopeClauses1, satisfies_insideClauses,
    satisfies_holeDefClauses1, satisfies_revLexClauses]

@[simp] theorem eval_arc (w : CanonicalPoints) {a b c : Fin w.rlen} (ab : a < b) (bc : b < c) :
    (arc o sz a b c).eval (w.toPropAssn holes) ↔ isArc w o sz a b c := by
  simp [arc]; split
  · simp [isArc]; split <;> simp
    · exact (w.gp₃' ab bc).σ_iff
    · exact (w.gp₃' ab bc).σ_ne
  · simp

theorem satisfies_arcDefClauses1 (w : CanonicalPoints) :
    (arcDefClauses1 w.rlen o sz).eval (w.toPropAssn holes) := by
  simp [arcDefClauses1, isArc]; intro a b ab c bc d cd h1 h2
  have ab : a < b := Nat.lt_of_le_of_lt (Nat.le_add_right ..) ab
  simp [ab, bc, cd] at h1 h2
  exact ⟨cd, _, ab, bc, h1, h2⟩

theorem satisfies_arcDefClauses2 (w : CanonicalPoints) :
    (arcDefClauses2 w.rlen o sz).eval (w.toPropAssn holes) := by
  simp [arcDefClauses2]; intro a b ab c bc H
  have ab : a < b := Nat.lt_of_le_of_lt (Nat.le_add_right ..) ab
  simp [ab, bc]; exact isArc_succ H

theorem satisfies_arcDefClausesUpTo (w : CanonicalPoints) :
    (arcDefClausesUpTo w.rlen o sz).eval (w.toPropAssn holes) := by
  simp [arcDefClausesUpTo, satisfies_arcDefClauses1, satisfies_arcDefClauses2]

theorem satisfies_capFDefClauses (w : CanonicalPoints) :
    (capFDefClauses w.rlen holes).eval (w.toPropAssn holes) := by
  simp [capFDefClauses, isCapF]; intro a b _ c bc d cd h1 h2 hh
  exact ⟨cd, _, h1, (w.gp₃' bc cd).σ_iff.1 h2, hh⟩

end CanonicalPoints
