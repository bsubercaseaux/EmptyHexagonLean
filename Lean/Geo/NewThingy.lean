import Geo.Point
import Geo.WBPoints
import Geo.Orientations

namespace Geo
open List

open Classical

/-- For distinct points in general position (`{a,p,q,r}.size = 4`),
this means that `a` is strictly in the triangle `pqr`. --/
def PtInTriangle2 (a : Point) (p q r : Point) : Prop :=
  a ∈ convexHull ℝ {p, q, r}


/-- The point `a` is strictly (not on the boundary) in the triangle `pqr`. -/
def σPtInTriangle2 (a p q r : Point) : Prop :=
  (σ p q a = σ p q r) ∧
  (σ p r a = σ p r q) ∧
  (σ q r a = σ q r p)


def ptInsideHalfPlaneCCW (p q a : Point) : Prop :=
  (σ p q a = Orientation.CCW) ∨ (σ p q a = Orientation.Collinear)

def halfPlaneCCW (p q : Point) : Set Point :=
  {a | ptInsideHalfPlaneCCW p q a}

def ptInsideHalfPlaneCW (p q a : Point) : Prop :=
  (σ p q a = Orientation.CW) ∨ (σ p q a = Orientation.Collinear)

def halfPlaneCW (p q : Point) : Set Point :=
  {a | ptInsideHalfPlaneCW p q a}

theorem σ_CCW_iff_pos_det (p q r: Point) : σ p q r = Orientation.CCW ↔ matrix_det p q r > 0 := by
  apply Iff.intro
  unfold σ
  aesop
  unfold σ
  aesop

theorem σ_CW_iff_neg_det (p q r: Point) : σ p q r = Orientation.CW ↔ matrix_det p q r < 0 := by
  apply Iff.intro
  unfold σ
  aesop
  unfold σ
  split
  intro h; linarith
  intro h2
  split
  tauto
  tauto


theorem σ_Co_iff_pos_0 (p q r: Point) : σ p q r = Orientation.Collinear ↔ matrix_det p q r = 0 := by
  apply Iff.intro
  unfold σ
  split
  aesop
  split
  aesop
  intro
  linarith
  unfold σ
  intro
  split
  aesop
  aesop

theorem detIffHalfPlaneCCW (p q a: Point): a ∈ halfPlaneCCW p q ↔ matrix_det p q a ≥ 0 := by
  apply Iff.intro
  {
    intro h
    unfold halfPlaneCCW at h
    unfold ptInsideHalfPlaneCCW at h
    simp at h
    rw [σ_CCW_iff_pos_det] at h
    rw [σ_Co_iff_pos_0] at h
    apply le_of_lt_or_eq
    tauto
  }
  {
    intro h
    unfold halfPlaneCCW
    simp
    unfold ptInsideHalfPlaneCCW
    rw [σ_CCW_iff_pos_det]
    rw [σ_Co_iff_pos_0]
    have := lt_or_eq_of_le h
    tauto
  }



def determinant_pts (a b c : Point) : Real :=
  a.x * b.y + b.x * c.y + c.x * a.y - a.y * b.x - b.y * c.x - c.y * a.x


theorem fix_mismatch_example (α : ℝ) (h1 : ¬α = 0) : 0 ≠ α := by

  -- Direct method to restate the hypothesis in the expected form
  intro h2 -- Assume α = 0 to derive a contradiction, given h1
  apply h1  -- Apply ¬α = 0 to the assumption α = 0 to get a contradiction
  linarith


theorem HalfPlanesAreConvex {p q : Point} : Convex ℝ (halfPlaneCCW p q) := by
  unfold halfPlaneCCW
  unfold Convex
  intro a
  intro h
  unfold StarConvex
  intro b
  intro ypq
  intro α β
  intro hα hβ
  intro hαβ
  unfold ptInsideHalfPlaneCCW at *
  simp [] at ypq
  simp [] at h
  rw [σ_CCW_iff_pos_det] at *
  rw [σ_Co_iff_pos_0] at *
  simp
  rw [σ_CCW_iff_pos_det]
  rw [σ_Co_iff_pos_0] at *

  have h' : matrix_det p q a ≥ 0 := by {
    apply le_of_lt_or_eq
    clear ypq
    tauto
  }
  have ypq' : matrix_det p q b ≥ 0 := by {
    apply le_of_lt_or_eq
    clear h
    tauto
  }

  suffices : matrix_det p q (α • a + β • b) ≥ 0
  {
    rcases lt_or_eq_of_le this with h | h
    . exact Or.inl h
    . apply Or.inr; rw [h]
  }
  clear ypq h

  rw [matrix_det_eq_det_pts] at *
  unfold Point.det at *

  by_cases h1 : α = 0
  {
    rw [h1]
    ring_nf
    have h2 : β = 1 := by linarith
    rw [h2]
    ring_nf
    simp at *
    ring_nf at *
    linarith
  }
  {
  simp at *

  -- simp [collinar] at *
  -- linarith


  have h3 : α > 0 := by {
    apply lt_of_le_of_ne
    exact hα
    apply fix_mismatch_example at h1
    exact h1
  }

  -- have ss :(α * a 1 + β * b 1) * Point.x p = α * (Point.y a * Point.x p) + β * (Point.y b * Point.x p) := by ring

  -- rw [ss]

  by_cases hb : β = 0
  {
    have h4 : α = 1 := by linarith
    simp only [] at *
    rw [h4]
    rw [hb]
    ring_nf
    simp []
    linarith
  }
  have h5 : β > 0 := by {
    apply lt_of_le_of_ne
    exact hβ
    apply fix_mismatch_example at hb
    exact hb
  }

  have αh : α * (Point.y a * Point.x p) ≤ α * (Point.x p * Point.y q + Point.x q * Point.y a + Point.x a * Point.y p - Point.y p * Point.x q - Point.y q * Point.x a) := by {
    nlinarith
  }

  have βypq : β * (Point.y b * Point.x p) ≤ β * (Point.x p * Point.y q + Point.x q * Point.y b + Point.x b * Point.y p - Point.y p * Point.x q - Point.y q * Point.x b) := by {
    nlinarith
  }

  have mix : α * (Point.y a * Point.x p) + β * (Point.y b * Point.x p) ≤ α * (Point.x p * Point.y q + Point.x q * Point.y a + Point.x a * Point.y p - Point.y p * Point.x q - Point.y q * Point.x a) + β * (Point.x p * Point.y q + Point.x q * Point.y b + Point.x b * Point.y p - Point.y p * Point.x q - Point.y q * Point.x b) := by {
    nlinarith
  }
  ring_nf at mix
  have ls: α * (Point.x p) * (Point.y q) + β * (Point.x p) * (Point.y q) = Point.x p * Point.y q :=
    by
    calc α * (Point.x p) * (Point.y q) + β * (Point.x p) * (Point.y q) = (α + β) * (Point.x p) * (Point.y q) := by ring
      _ = Point.x p * Point.y q := by {
        rw [hαβ]
        simp
      }
  have mix2: α * (Point.y a * Point.x p) + β * (Point.y b * Point.x p) ≤ (α * (Point.x p * Point.y q) + β * (Point.x p * Point.y q))  + α * (Point.x q * Point.y a) + β * (Point.x q * Point.y b) + α * (Point.x a * Point.y p) + β * (Point.x b * Point.y p) - α * (Point.y p * Point.x q) - β * (Point.y p * Point.x q) - α * (Point.y q * Point.x a) - β * (Point.y q * Point.x b) := by {
    nlinarith
  }
  have mix3: α * (Point.y a * Point.x p) + β * (Point.y b * Point.x p) ≤ (Point.x p * Point.y q) + α * (Point.x q * Point.y a) + β * (Point.x q * Point.y b) + α * (Point.x a * Point.y p) + β * (Point.x b * Point.y p) - α * (Point.y p * Point.x q) - β * (Point.y p * Point.x q) - α * (Point.y q * Point.x a) - β * (Point.y q * Point.x b) := by {
    linarith
  }
  have exp : Point.y (α • a + β • b) = α * (Point.y a) + β * (Point.y b) := by {
    simp []
  }
  have exp2 : Point.x (α • a + β • b) = α * (Point.x a) + β * (Point.x b) := by {
    simp []
  }

  save
  rw [←exp]
  rw [←exp2]
  ring_nf at *


  have mx: Point.x p * Point.y q - (Point.y q) * α * (Point.x a)  - Point.y q * β * Point.x b +
   - Point.x p * α * Point.y a - Point.x p * β * Point.y b +
          (Point.x q * α * Point.y a - Point.x q * α * Point.y p) +
        (Point.x q * β * Point.y b - Point.x q * β * Point.y p) +
      α * Point.x a * Point.y p +
    β * Point.x b * Point.y p ≥ 0 := by {
      nlinarith
  }
  ring_nf at mx
  ring_nf
  -- (-(α * Point.y p * Point.x q) - Point.y p * Point.x q * β)
  have ls2: α * (Point.y p) * (Point.x q) + β * (Point.y p) * (Point.x q) = Point.y p * Point.x q :=
    by
    calc α * (Point.y p) * (Point.x q) + β * (Point.y p) * (Point.x q) = (α + β) * (Point.y p) * (Point.x q) := by ring
      _ = Point.y p * Point.x q := by {
        rw [hαβ]
        simp
      }
  rw [exp]
  rw [exp2]
  ring_nf at *
  nlinarith
  }

example : True := by trivial

theorem det_symmetry (a b c : Point) : matrix_det a b c = -matrix_det b a c := by
  rw [matrix_det_eq_det_pts]
  rw [matrix_det_eq_det_pts]
  unfold Point.det
  linarith

theorem det_symmetry' (a b c : Point) : matrix_det a b c = matrix_det b c a := by
  rw [matrix_det_eq_det_pts]
  rw [matrix_det_eq_det_pts]
  unfold Point.det
  linarith

theorem  det_antisymmetry (a b c : Point) : matrix_det a b c = -matrix_det b a c := by
  rw [matrix_det_eq_det_pts]
  rw [matrix_det_eq_det_pts]
  unfold Point.det
  linarith

theorem det_antisymmetry' (a b c : Point) : matrix_det a b c = -matrix_det a c b := by
  rw [matrix_det_eq_det_pts]
  rw [matrix_det_eq_det_pts]
  unfold Point.det
  linarith


theorem convex3combo (S : Set Point) (CS: Convex ℝ S) : ∀ (a b c : Point), a ∈ S → b ∈ S → c ∈ S
  → ∀ (α β γ : ℝ), α + β + γ = 1 → α ≥ 0 → β ≥ 0 → γ ≥ 0 → α • a + β • b + γ • c ∈ S := by
  intro a b c
  intro aS bS cS
  intro α β γ
  intro sum1 αNN βNN γNN
  by_cases case : α + β = 0
  {
    have α0 : α = 0 := by linarith
    have β0 : β = 0 := by linarith
    have γ1 : γ = 1 := by linarith
    rw [α0, β0, γ1]
    simp
    exact cS
  }
  {
    let α' := α / (α + β)
    let β' := β / (α + β)
    have α'NN : α' ≥ 0 := by
      apply div_nonneg; exact αNN; linarith
    have β'NN : β' ≥ 0 := by
      apply div_nonneg; exact βNN; linarith

    have αβsum : α' + β' = 1 := by
      rw [div_add_div_same]
      rw [div_self]
      exact case
    let combo := α' • a + β' • b
    have comboInS : combo ∈ S := by
      exact CS aS bS α'NN β'NN αβsum
    let fSum := α + β
    have fSumNN : fSum ≥ 0 := by {
     simp; linarith
    }
    have fSumγ : fSum + γ = 1 := by {
      rw [sum1]
    }
    let combo2 := fSum • combo + γ • c
    have combo2InS : combo2 ∈ S := by
      exact CS comboInS cS fSumNN γNN fSumγ

    have combo2Eq : combo2 = α • a + β • b + γ • c := by {
      simp
      sorry
    }
    rw [←combo2Eq]
    exact combo2InS
  }


theorem PtInTriangle2_of_σPtInTriange2 {a p q r : Point} (gp : Point.InGeneralPosition₄ a  p q r)
      (symm: σ p q r = Orientation.CCW) (py0: p.y = 0) (qy0: q.y = 0):
       σPtInTriangle2 a p q r → PtInTriangle2 a p q r  := by
      unfold PtInTriangle2
      intro ⟨h1, h2, h3⟩
      have det_pqr_pos : matrix_det p q r > 0 := by {
        rw [σ_CCW_iff_pos_det] at symm
        linarith
      }
      have det_qpr_neg : matrix_det q p r < 0 := by {
        rw [det_antisymmetry] at det_pqr_pos
        linarith
      }

      have anti : σ p q r = - σ p r q := by {
        rw [σ_perm₂]
      }
      have : σ p a r = σ p q r := by {
        rw [σ_perm₂]
        rw [anti]
        sorry -- ask WN
      }

      have det_par_pos : matrix_det p a r > 0 := by {
        rw [σ_perm₂] at h2
        rw [←σ_CCW_iff_pos_det]
        aesop
      }
      let aProjX := (r.y * a.x - r.x * a.y)/(r.y - a.y)
      have order_aProjX_pX : p.x ≤ aProjX := by {
        simp
        suffices linearized: p.x * r.y - p.x * a.y ≤ r.y * a.x - r.x * a.y by
        {
          sorry -- ask WN
        }
        rw [matrix_det_eq_det_pts] at det_par_pos
        unfold Point.det at det_par_pos
        rw [py0] at det_par_pos
        simp at det_par_pos
        linarith
      }
      have det_qar_neg : matrix_det q a r < 0 := by {

        rw [←σ_CW_iff_neg_det]
        rw [←σ_CW_iff_neg_det] at det_qpr_neg
        rw [σ_perm₂] at h3
        have: σ q r p = - σ q a r := by {
          aesop
        }
        rw [σ_perm₂] at this
        sorry -- ask WN
      }
      have order_aProjX_qX : aProjX ≤ q.x := by {
        simp
        suffices linearized: q.x * r.y - q.x * a.y ≥ r.y * a.x - r.x * a.y by
        {
          sorry -- ask WN
        }
        rw [matrix_det_eq_det_pts] at det_qar_neg
        unfold Point.det at det_qar_neg
        rw [qy0] at det_qar_neg
        simp at det_qar_neg
        linarith
      }

      let aProjXPt : Point := ![aProjX, 0]

      have aProjXPt_IsConvexCombOf_p_q :
        ∃ (α β : ℝ), α + β = 1 ∧ α ≥ 0 ∧ β ≥ 0 ∧ α • p + β • q = aProjXPt := by {
          sorry -- ask WN
        }
      have aProjX_a_r_collinear : matrix_det aProjXPt a r = 0 := by {
        rw [matrix_det_eq_det_pts]
        unfold Point.det
        simp
        sorry -- ask WN
      }

      have y_order : aProjXPt.y = 0 ∧ a.y > 0 ∧ r.y > a.y := by {
        sorry -- ask WN
      }

      have a_IsConvexCombOf_aProjXPt_r :
        ∃ (α β : ℝ), α + β = 1 ∧ α ≥ 0 ∧ β ≥ 0 ∧ α • aProjXPt + β • r = a := by {
          -- because they're on the same line and a is between their y coordinates
          sorry -- ask WN
        }

      have a_IsConvexCombOf_p_q_r :
        ∃ (α β γ : ℝ), α + β + γ = 1 ∧ α ≥ 0 ∧ β ≥ 0 ∧ γ ≥ 0 ∧ α • p + β • q + γ • r = a := by {
          -- transitivity of combexCombo
          sorry -- ask WN
        }

      have cHullIsConvex: Convex ℝ (convexHull ℝ {p , q, r}) := by {
        exact convex_convexHull ℝ {p , q, r}
      }

      have sSetHull : {p, q, r} ⊆ convexHull ℝ {p , q, r} := by {
        exact subset_convexHull ℝ {p , q, r}
      }

      have pInChull : p ∈ convexHull ℝ {p , q, r} := by {
        rw [Set.subset_def] at sSetHull
        simp at sSetHull
        exact sSetHull.1
      }
      have qInChull : q ∈ convexHull ℝ {p , q, r} := by {
        rw [Set.subset_def] at sSetHull
        simp at sSetHull
        exact sSetHull.2.1
      }
      have rInChull : r ∈ convexHull ℝ {p , q, r} := by {
        rw [Set.subset_def] at sSetHull
        simp at sSetHull
        exact sSetHull.2.2
      }

      have ⟨α, β, γ, αβγSum, αNN, βNN, γNN, ccEq⟩ := a_IsConvexCombOf_p_q_r
      have c3c := convex3combo (convexHull ℝ {p, q, r}) cHullIsConvex p q r  pInChull qInChull rInChull
      have := c3c α β γ αβγSum αNN βNN γNN
      rw [ccEq] at this
      exact this

theorem σPtInTriangle2_of_PtInTriange2 {a p q r : Point} (gp : Point.InGeneralPosition₄ a  p q r)
      (symm: σ p q r = Orientation.CCW) :
      PtInTriangle2 a p q r → σPtInTriangle2 a p q r := by
    intro h
    unfold PtInTriangle2 at h
    unfold σPtInTriangle2
    let halfPlanePQ := halfPlaneCCW p q
    let halfPlaneQR := halfPlaneCCW q r
    let halfPlaneRP := halfPlaneCCW r p
    have pInPQ: p ∈ halfPlanePQ := by
      {
        simp; rw [detIffHalfPlaneCCW]
        rw [matrix_det_eq_det_pts]; unfold Point.det
        linarith
      }
    have pInRP: p ∈ halfPlaneRP := by
      {
        simp; rw [detIffHalfPlaneCCW]
        rw [matrix_det_eq_det_pts]; unfold Point.det
        linarith
      }
    have pInQR: p ∈ halfPlaneQR := by
      {
        simp; rw [detIffHalfPlaneCCW]
        rw [σ_CCW_iff_pos_det] at symm
        rw [←det_symmetry']
        linarith
      }
    have qInPQ: q ∈ halfPlanePQ := by
      {
        simp; rw [detIffHalfPlaneCCW]
        rw [matrix_det_eq_det_pts]; unfold Point.det
        linarith
      }
    have qInQR: q ∈ halfPlaneQR := by
      {
        simp; rw [detIffHalfPlaneCCW]
        rw [matrix_det_eq_det_pts]; unfold Point.det
        linarith
      }
    have qInRP: q ∈ halfPlaneRP := by
      {
        simp; rw [detIffHalfPlaneCCW]
        rw [σ_CCW_iff_pos_det] at symm
        rw [det_symmetry']
        linarith
      }

    have rInPQ: r ∈ halfPlanePQ := by
      {
        simp
        rw [detIffHalfPlaneCCW]
        rw [σ_CCW_iff_pos_det] at symm
        linarith
      }
    have rInQR: r ∈ halfPlaneQR := by
      {
        simp; rw [detIffHalfPlaneCCW]
        rw [matrix_det_eq_det_pts]; unfold Point.det
        linarith
      }
    have rInRP: r ∈ halfPlaneRP := by
      {
        simp; rw [detIffHalfPlaneCCW]
        rw [matrix_det_eq_det_pts]; unfold Point.det
        linarith
      }

    let inter := halfPlanePQ ∩ (halfPlaneQR ∩ halfPlaneRP)
    have pInter: p ∈ inter := Set.mem_inter pInPQ (Set.mem_inter pInQR pInRP)
    have qInter: q ∈ inter := Set.mem_inter qInPQ (Set.mem_inter qInQR qInRP)
    have rInter: r ∈ inter := Set.mem_inter rInPQ (Set.mem_inter rInQR rInRP)

    have cRP: Convex ℝ (halfPlaneRP) := by exact HalfPlanesAreConvex
    have cPQ: Convex ℝ (halfPlanePQ) := by exact HalfPlanesAreConvex
    have cQR: Convex ℝ (halfPlaneQR) := by exact HalfPlanesAreConvex
    have interConvex : Convex ℝ inter := by exact Convex.inter cPQ (Convex.inter cQR cRP)

    have sub_set_inter : {p, q, r} ⊆ inter := by
    {
        simp_rw [Set.subset_def]
        simp; exact ⟨pInter, ⟨qInter, rInter⟩⟩
    }

    have aInInter: a ∈ inter := by
      {
        unfold convexHull at h
        simp at h
        apply h inter sub_set_inter interConvex
      }


    have aInHalfPQ: a ∈ halfPlanePQ := by aesop
    have aInHalfRP: a ∈ halfPlaneRP := by aesop
    have aInHalfQR: a ∈ halfPlaneQR := by aesop

    have pqa_non_0 : matrix_det p q a ≠ 0 := by
      {
        have l := gp.1
        unfold Point.InGeneralPosition₃ at l
        rw [←matrix_det_eq_det_pts] at l
        rw [det_symmetry'] at l
        exact l
      }
    have pra_non_0 : matrix_det p r a ≠ 0 := by
      {
        have l := gp.2
        unfold Point.InGeneralPosition₃ at l
        rw [←matrix_det_eq_det_pts] at l
        rw [det_symmetry'] at l
        exact l
      }
    have qra_non_0 : matrix_det q r a ≠ 0 := by
      {
        have l := gp.3
        unfold Point.InGeneralPosition₃ at l
        rw [←matrix_det_eq_det_pts] at l
        rw [det_symmetry'] at l
        exact l
      }

    have pqr_pos : matrix_det p q r > 0 := by
      {
        rw [σ_CCW_iff_pos_det] at symm
        linarith
      }

    have pqa_CCW : σ p q a = Orientation.CCW := by
      {
        rw [detIffHalfPlaneCCW] at aInHalfPQ
        rw [σ_CCW_iff_pos_det]
        apply lt_of_le_of_ne aInHalfPQ (Ne.symm pqa_non_0)
      }
    have goal1: σ p q a = σ p q r := Eq.trans pqa_CCW (Eq.symm symm)
    use goal1

    have pra_neg : matrix_det p r a < 0 := by
        {
          apply lt_of_le_of_ne
          rw [detIffHalfPlaneCCW] at aInHalfRP
          rw [det_antisymmetry] at aInHalfRP
          linarith
          exact pra_non_0
        }
    have prq_neg : matrix_det p r q < 0 := by
        {
          rw [det_antisymmetry'] at pqr_pos
          linarith
        }
    have goal2: σ p r a = σ p r q := by
      {
        rw [←σ_CW_iff_neg_det] at pra_neg
        rw [←σ_CW_iff_neg_det] at prq_neg
        aesop
      }
    use goal2

    have qrp_pos : matrix_det q r p > 0 := by
      {
        rw [←det_symmetry']; exact pqr_pos
      }
    have qra_pos : matrix_det q r a > 0 := by
      {
        rw [detIffHalfPlaneCCW] at aInHalfQR
        apply lt_of_le_of_ne aInHalfQR (Ne.symm qra_non_0)
      }
    rw [←σ_CCW_iff_pos_det] at qrp_pos
    rw [←σ_CCW_iff_pos_det] at qra_pos
    exact Eq.trans qra_pos (Eq.symm qrp_pos)



noncomputable def rotateTranslate (p : Point) (θ : ℝ) (tx ty : ℝ) : Point :=
  ![p 0 * (Real.cos θ) - p 1 * (Real.sin θ) + tx, p 0 * (Real.sin θ) + p 1 * (Real.cos θ) + ty]

noncomputable def rotate (θ : ℝ) (p : Point) : Point :=
  ![p 0 * (Real.cos θ) - p 1 * (Real.sin θ), p 0 * (Real.sin θ) + p 1 * (Real.cos θ)]

theorem rotateTranslateIsoCC (p q: Point) (θ tx ty : ℝ) {α β : ℝ} (hα: α ≥ 0) (hβ: β ≥ 0) (hαβ: α + β = 1) :
  rotateTranslate (α • p + β • q) θ tx ty = α • (rotateTranslate p θ tx ty) + β • (rotateTranslate q θ tx ty) := by
  unfold rotateTranslate
  ring_nf
  simp
  ring_nf
  sorry


noncomputable def rotateTranslateSet (S : Set Point) (θ : ℝ) (tx ty : ℝ) : Set Point :=
  {rotateTranslate p θ tx ty | p ∈ S}

theorem rotateTranslateOfConvexIsConvex (S: Set Point) (CS: Convex ℝ S) (θ : ℝ) (tx ty : ℝ) : Convex ℝ (rotateTranslateSet S θ tx ty) := by
  unfold Convex
  intro x hx
  unfold StarConvex
  intro y hy
  intro α β hα hβ hαβ
  unfold Convex at CS
  unfold rotateTranslateSet at hx
  unfold rotateTranslateSet at hy
  simp at hx hy
  have ⟨preX, preXinS, x_post_preX⟩ := hx
  have ⟨preY, preYinS, y_post_preY⟩ := hy
  have CC := CS preXinS preYinS hα hβ hαβ
  let CC_wit := α • preX + β • preY
  have CC_wit_in_S : CC_wit ∈ S := by
    exact CC
  have rt : rotateTranslate CC_wit θ tx ty  = α • (rotateTranslate preX θ tx ty) + β • (rotateTranslate preY θ tx ty) := by
      exact rotateTranslateIsoCC preX preY θ tx ty hα hβ hαβ
  have rt2 : rotateTranslate CC_wit θ tx ty = α • x + β • y := by
    rw [rt]
    rw [x_post_preX]
    rw [y_post_preY]
  exact ⟨CC_wit, CC_wit_in_S, rt2⟩




theorem PtInTriangle2InvariantUnderTransform {a p q r : Point} (gp : Point.InGeneralPosition₄ a  p q r)
      (symm: σ p q r = Orientation.CCW) (tx ty : ℝ) (θ : ℝ) :
      PtInTriangle2 a p q r ↔ PtInTriangle2 (rotateTranslate a θ tx ty) (rotateTranslate p θ tx ty) (rotateTranslate q θ tx ty) (rotateTranslate r θ tx ty) := by
      apply Iff.intro
      {

        intro h
        unfold PtInTriangle2 at h
        unfold convexHull at h
        simp at h


        unfold PtInTriangle2
        unfold convexHull
        simp
        intro postS hpostS cpostS
        sorry
      }
      {
        intro h
        unfold PtInTriangle2 at h
        unfold convexHull at h
        simp at h

        unfold PtInTriangle2
        unfold convexHull
        simp
        intro postS hpostS cpostS
        sorry
      }


theorem PtInTriangle2_of_σPtInTriange2' {a p q r : Point} (gp : Point.InGeneralPosition₄ a  p q r)
      (symm: σ p q r = Orientation.CCW):
       σPtInTriangle2 a p q r → PtInTriangle2 a p q r  := by
       intro h

       sorry


theorem σPtInTriangle_iff2 {a p q r : Point} (gp : Point.InGeneralPosition₄ a  p q r)
      (symm: σ p q r = Orientation.CCW) :
    σPtInTriangle2 a p q r ↔ PtInTriangle2 a p q r := by
    apply Iff.intro
    exact PtInTriangle2_of_σPtInTriange2' gp symm
    exact σPtInTriangle2_of_PtInTriange2 gp symm

def HasEmptyTriangle (pts : List Point) : Prop :=
  ∃ p q r, Sublist [p, q, r] pts ∧ ∀ a ∈ pts, a ∉ ({p, q, r} : Set Point) → ¬PtInTriangle a p q r

def σHasEmptyTriangle (pts : List Point) : Prop :=
  ∃ p q r, Sublist [p, q, r] pts ∧ ∀ a ∈ pts, a ∉ ({p, q, r} : Set Point) → ¬σPtInTriangle a p q r

def σHasEmptyTriangle2 (pts : List Point) : Prop :=
  ∃ i j k : (Fin pts.length),  (i < j ∧ j < k) ∧ ∀ a: (Fin pts.length), a ∉ ({i , j, k} : Set (Fin pts.length))  → ¬(σPtInTriangle2 pts[a] pts[i] pts[j] pts[k])


theorem σHasEmptyTriangle_iff_σHasEmptyTriangle2 {pts : List Point} (gp : Point.PointListInGeneralPosition pts) :
    σHasEmptyTriangle pts ↔ σHasEmptyTriangle2 pts := by
  unfold σHasEmptyTriangle σHasEmptyTriangle2
  sorry -- obvious, TODO WN

theorem σHasEmptyTriangle_iff {pts : List Point} (gp : Point.PointListInGeneralPosition pts) :
    σHasEmptyTriangle2 pts ↔ HasEmptyTriangle pts := by
  unfold σHasEmptyTriangle2 HasEmptyTriangle
  sorry -- obvious, TODO WN

/-
/-- The convex hull of `S` contains none of the points in `T`,
except those that are already in `S`. -/
def IsEmptyWrt (S T : Finset Point) :=
  ∀ p ∈ T, p ∉ S → p ∉ convexHull ℝ S
--def σMathyHasEmptyTriangle (pts : List Point) : Prop :=
  -- ∃ p q r, Sublist [p, q, r] pts ∧ MathyIsEmptyWrt {p, q, r} pts.toFinset
-- theorem HasEmptyTriangle_iff_Mathy (pts : List Point) (gp : Point.PointListInGeneralPosition pts) :
 --   HasEmptyTriangle pts ↔ MathyHasEmptyTriangle pts := by
 --  sorry
 -/
infix:50 " ~_σ " => σ_equivalence
def OrientationProperty (P : List Point → Prop) :=
  ∀ l₁ l₂, (Point.PointListInGeneralPosition l₁ ∧ Point.PointListInGeneralPosition l₂)  →  l₁ ~_σ l₂ → (P l₁ ↔ P l₂)

theorem OrientationProperty.not : OrientationProperty P → OrientationProperty (¬P ·) := by
  unfold OrientationProperty
  intro h l₁ l₂ hσ
  simp [h l₁ l₂ hσ]
  have := h l₁ l₂ hσ
  aesop


theorem OrientationProperty_σHasEmptyTriangle : OrientationProperty σHasEmptyTriangle := by
  unfold OrientationProperty
  intro l₁ l₂ gps h


  rw [σHasEmptyTriangle_iff_σHasEmptyTriangle2]
  rw [σHasEmptyTriangle_iff_σHasEmptyTriangle2]

  unfold σHasEmptyTriangle2

  apply Iff.intro
  {
    intro he

    have ⟨p, q, r, h'⟩ := he
    unfold σPtInTriangle2 at h'
    unfold σPtInTriangle2

    rcases h with ⟨sameLength,sameOrientations⟩

    -- p' is a copy of p but of type (Fin l₂.length)
    rcases p with ⟨p, p_lt⟩
    rcases q with ⟨q, q_lt⟩
    rcases r with ⟨r, r_lt⟩

    use ⟨p, by linarith⟩, ⟨q, by linarith⟩, ⟨r, by linarith⟩
    simp

    rcases h' with ⟨h'1, h'2⟩
    apply And.intro

    simp at h'1
    exact h'1

    intro a
    intro ha
    rcases a with ⟨a, a_lt⟩
    have h2a := h'2 ⟨a, by linarith⟩
    simp at ha
    simp at h2a
    have rh2a := h2a ha
    simp at rh2a
    have Hpqr := sameOrientations p_lt q_lt r_lt
    have alt1 : a < l₁.length := by linarith
    have Hpqa := sameOrientations p_lt q_lt alt1
    have Hpra := sameOrientations p_lt r_lt alt1
    have Hqra := sameOrientations q_lt r_lt alt1
    have Hprq := sameOrientations p_lt r_lt q_lt
    have Hqrp := sameOrientations q_lt r_lt p_lt
    rw [←Hpqr, ←Hpqa, ←Hpra, ←Hqra, ←Hprq, ←Hqrp]

    exact rh2a
  }
  {
    intro he

    have ⟨p, q, r, h'⟩ := he
    unfold σPtInTriangle2 at h'
    unfold σPtInTriangle2

    rcases h with ⟨sameLength,sameOrientations⟩

    -- p' is a copy of p but of type (Fin l₂.length)
    rcases p with ⟨p, p_lt⟩
    rcases q with ⟨q, q_lt⟩
    rcases r with ⟨r, r_lt⟩

    use ⟨p, by linarith⟩, ⟨q, by linarith⟩, ⟨r, by linarith⟩
    simp

    rcases h' with ⟨h'1, h'2⟩
    apply And.intro

    simp at h'1
    exact h'1

    intro a
    intro ha
    rcases a with ⟨a, a_lt⟩
    have h2a := h'2 ⟨a, by linarith⟩
    simp at ha
    simp at h2a
    have rh2a := h2a ha
    simp at rh2a
    rw [←sameLength] at p_lt q_lt r_lt
    have Hpqr := sameOrientations p_lt q_lt r_lt
    have alt1 : a < l₁.length := by linarith
    have Hpqa := sameOrientations p_lt q_lt alt1
    have Hpra := sameOrientations p_lt r_lt alt1
    have Hqra := sameOrientations q_lt r_lt alt1
    have Hprq := sameOrientations p_lt r_lt q_lt
    have Hqrp := sameOrientations q_lt r_lt p_lt
    rw [Hpqr, Hpqa, Hpra, Hqra, Hprq, Hqrp]

    exact rh2a
  }
  exact gps.2
  exact gps.1


theorem fundamentalTheoremOfSymmetryBreaking {P : List Point → Prop} {L : List Point} (gp : Point.PointListInGeneralPosition L) :
    OrientationProperty P → P L →
    ∃ (w : WBPoints), w.length = L.length ∧ P w.points := by
  sorry -- TODO(Bernardo)

theorem fromLeanSAT :
    ¬∃ (w : WBPoints), w.length = 10 ∧ ¬σHasEmptyTriangle w.points := by
  sorry

theorem EmptyTriangle10TheoremLists (pts : List Point) (gp : Point.PointListInGeneralPosition pts) (h : pts.length = 10) :
    HasEmptyTriangle pts := by
  by_contra h'
  rw [← σHasEmptyTriangle_iff gp] at h'
  rw [←σHasEmptyTriangle_iff_σHasEmptyTriangle2] at h'
  have ⟨w, hw, hw'⟩ := fundamentalTheoremOfSymmetryBreaking gp OrientationProperty_σHasEmptyTriangle.not h'
  apply fromLeanSAT
  use w, hw.trans h
  exact gp
