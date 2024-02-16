import Geo.Definitions.Point
import Geo.Definitions.WBPoints
import Geo.Orientations
import Geo.PointsToWB.SymmetryBreaking

namespace Geo
noncomputable section

open List Orientation

open Classical

variable {p q r a : Point}

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
  (σ p q a = .CCW) ∨ (σ p q a = .Collinear)

def halfPlaneCCW (p q : Point) : Set Point :=
  {a | ptInsideHalfPlaneCCW p q a}

def ptInsideHalfPlaneCW (p q a : Point) : Prop :=
  (σ p q a = .CW) ∨ (σ p q a = .Collinear)

def halfPlaneCW (p q : Point) : Set Point :=
  {a | ptInsideHalfPlaneCW p q a}

theorem σ_CCW_iff_pos_det : σ p q r = .CCW ↔ matrix_det p q r > 0 := by
  rw [σ, ofReal_eq_ccw]

theorem σ_CW_iff_neg_det : σ p q r = .CW ↔ matrix_det p q r < 0 := by
  rw [σ, ofReal_eq_cw]

theorem σ_Co_iff_pos_0 : σ p q r = .Collinear ↔ matrix_det p q r = 0 := by
  rw [σ, ofReal_eq_collinear]

theorem detIffHalfPlaneCCW : a ∈ halfPlaneCCW p q ↔ matrix_det p q a ≥ 0 := by
  simp [halfPlaneCCW, ptInsideHalfPlaneCCW]
  constructor
  · rintro (h | h)
    · exact le_of_lt $ σ_CCW_iff_pos_det.mp h
    · exact le_of_eq $ symm $ σ_Co_iff_pos_0.mp h
  · intro h
    rcases eq_or_lt_of_le h with (h | h)
    · exact Or.inr $ σ_Co_iff_pos_0.mpr h.symm
    · exact Or.inl $ σ_CCW_iff_pos_det.mpr h

#check Convex
#check Matrix.dotProduct

open Matrix in
theorem HalfPlanesAreConvex : Convex ℝ (halfPlaneCCW p q) := by
  convert convex_halfspace_ge (f := fun r => Matrix.dotProduct r (p - q)) _ (p.x * q.y + q.x - p.y) using 1
  · ext
    simp [detIffHalfPlaneCCW, matrix_det_eq_det_pts, Point.det, Point.x, Point.y]--exact detIffHalfPlaneCCW
    -- use show _ ↔ _ ≤ _
    dsimp
    done

#exit
  infer_instance
  infer_instance
  simp [matrix_det_eq_det_pts, Point.det]
  have : Point →ₗ[ℝ] ℝ :=
    { toFun := fun r => Matrix.dotProduct r (p - q)
    --r.x * (p.y - q.y) - p.x * r.y + q.x * r.y,
      map_add' := by
        intro x y
        simp [Point.x, Point.y]
        ring
        done,
      map_smul' := by simp }
  apply IsLinearMap_sub

  done

  let S := { p : Point | a.x ≤ p.x } ∩ { p : Point | p.x ≤ c.x }
  have cvxS : Convex ℝ S :=
    Convex.inter
      (convex_halfspace_ge ⟨fun _ _ => rfl, fun _ _ => rfl⟩ a.x)
      (convex_halfspace_le ⟨fun _ _ => rfl, fun _ _ => rfl⟩ c.x)

#exit
  simp [Convex, StarConvex, detIffHalfPlaneCCW]
  intro x hx y hy α β hα hβ hαβ
  rcases eq_or_lt_of_le hα with (rfl | hα)
  · rw [zero_add] at hαβ; subst hαβ
    rw [zero_smul, one_smul, zero_add]
    exact hy
  · rcases eq_or_lt_of_le hβ with (rfl | hβ)
    · rw [add_zero] at hαβ; subst hαβ
      rw [zero_smul, one_smul, add_zero]
      exact hx
      done
    · rw [matrix_det_eq_det_pts, Point.det] at hx hy ⊢

      done
#exit



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
  done

#exit
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

  have h3 : α > 0 := by {
    apply lt_of_le_of_ne
    exact hα
    apply fix_mismatch_example at h1
    exact h1
  }

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
      simp only [smul_add, ← smul_assoc]
      have neq := fix_mismatch_example case
      field_simp
      rw [mul_comm]
      rw [mul_div_assoc]
      rw [div_self]
      field_simp
      rw [mul_comm]
      rw [mul_div_assoc]
      rw [div_self]
      field_simp

      exact Ne.symm neq
      exact Ne.symm neq
    }
    rw [←combo2Eq]
    exact combo2InS
  }


noncomputable def arProjX_p_q (a r : Point) : ℝ :=
  (r.y * a.x - r.x * a.y) / (r.y - a.y)


theorem arProjX_between_p_q {a p q r : Point}
      (py0: p.y = 0) (qy0: q.y = 0)
      (det_qar_neg : matrix_det q a r < 0) (det_par_pos : matrix_det p a r > 0)
      (ar_y_order : r.y > a.y)
      :
      p.x <  (arProjX_p_q a r) ∧ (arProjX_p_q a r) < q.x := by

       have order_aProjX_qX : (arProjX_p_q a r) < q.x := by {
          unfold arProjX_p_q
          suffices linearized: q.x * (r.y - a.y) > r.y * a.x - r.x * a.y by
          {
            simp at linearized
            rw [div_lt_iff']
            linarith
            linarith only [ar_y_order]
          }
          rw [matrix_det_eq_det_pts] at det_qar_neg
          unfold Point.det at det_qar_neg
          rw [qy0] at det_qar_neg
          simp at det_qar_neg
          linarith
       }

       have order_aProjX_pX : p.x < (arProjX_p_q a r) := by {
          unfold arProjX_p_q
          suffices linearized: p.x * (r.y - a.y) < r.y * a.x - r.x * a.y by
          {
            rw [lt_div_iff']
            linarith
            linarith only [ar_y_order]
          }
          rw [matrix_det_eq_det_pts] at det_par_pos
          unfold Point.det at det_par_pos
          rw [py0] at det_par_pos
          simp at det_par_pos
          linarith
       }
       exact ⟨order_aProjX_pX, order_aProjX_qX⟩

theorem convexComboOfCollinearAndXOrdered (p q x : Point) (collinear: matrix_det p q x = 0) (xOrder1: p.x < x.x) (xOrder2: x.x < q.x) :
        ∃ (α β : ℝ), α + β = 1 ∧ α ≥ 0 ∧ β ≥ 0 ∧ α • p + β • q = x := by {
          -- because they're on the same line and a is between their y coordinates
          let α := (q.x - x.x) / (q.x - p.x)
          let β := (x.x - p.x) / (q.x - p.x)
          use α
          use β
          have αβSum : α + β = 1 := by {
            rw [div_add_div_same]
            simp
            rw [div_self]
            linarith
          }
          use αβSum
          have αNN : α ≥ 0 := by {
            apply div_nonneg; linarith
            linarith
          }
          have βNN : β ≥ 0 := by {
            apply div_nonneg; linarith
            linarith
          }
          use αNN
          use βNN
          simp
          rw [matrix_det_eq_det_pts] at collinear
          unfold Point.det at collinear
          have : q.x - p.x ≠ 0 := by linarith
          ext

          field_simp [this]
          linarith [collinear]

          field_simp [this]
          linarith [collinear]
        }


theorem convexComboOfCollinearAndYOrdered (p q x : Point) (collinear: matrix_det p q x = 0) (yOrder1: p.y < x.y) (yOrder2: x.y < q.y) :
        ∃ (α β : ℝ), α + β = 1 ∧ α ≥ 0 ∧ β ≥ 0 ∧ α • p + β • q = x := by {
          -- because they're on the same line and a is between their y coordinates
          let α := (q.y - x.y) / (q.y - p.y)
          let β := (x.y - p.y) / (q.y - p.y)
          use α
          use β
          have αβSum : α + β = 1 := by {
            rw [div_add_div_same]
            simp
            rw [div_self]
            linarith
          }
          use αβSum
          have αNN : α ≥ 0 := by {
            apply div_nonneg; linarith
            linarith
          }
          have βNN : β ≥ 0 := by {
            apply div_nonneg; linarith
            linarith
          }
          use αNN
          use βNN
          simp
          rw [matrix_det_eq_det_pts] at collinear
          unfold Point.det at collinear
          have : q.y - p.y ≠ 0 := by linarith
          ext

          field_simp [this]
          linarith [collinear]

          field_simp [this]
          linarith [collinear]
        }

def IsConvexCombo₂ (x p q : Point) : Prop :=
  ∃ (α β : ℝ), α + β = 1 ∧ α ≥ 0 ∧ β ≥ 0 ∧ α • p + β • q = x

def IsConvexCombo₃ (a p q r : Point) : Prop :=
  ∃ (α β γ : ℝ), α + β + γ = 1 ∧ α ≥ 0 ∧ β ≥ 0 ∧ γ ≥ 0 ∧ α • p + β • q + γ • r = a

theorem convexComboTransitive {p q r a x: Point} :
    IsConvexCombo₂ x p q → IsConvexCombo₂ a x r → IsConvexCombo₃ a p q r := by
  intro h₁ h₂
  unfold IsConvexCombo₂ at h₁ h₂
  rcases h₁ with ⟨α₁, β₁, hαβ, hα₁, hβ₁, h_convex₁⟩
  rcases h₂ with ⟨α₂, β₂, hαβ₂, hα₂, hβ₂, h_convex₂⟩
  subst h_convex₁
  simp at h_convex₂
  unfold IsConvexCombo₃
  use α₂ • α₁, α₂ • β₁, β₂
  constructor
  · have h₁ : α₂ * (α₁ + β₁) = α₂ * 1 := by
      exact congrArg (HMul.hMul α₂) hαβ
    rw [mul_one] at h₁
    conv at h₁ => rhs; rw [eq_sub_of_add_eq hαβ₂]
    replace h₁ := add_eq_of_eq_sub h₁
    simp [mul_add] at h₁
    simp [h₁]
  · simp only [smul_eq_mul, ge_iff_le]
    use smul_nonneg hα₂ hα₁, mul_nonneg hα₂ hβ₁, hβ₂
    rwa [← smul_assoc, ← smul_assoc] at h_convex₂


theorem PtInTriangle2_of_σPtInTriange2 {a p q r : Point}
      (spq: p.x < q.x)
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
        simp [h2]
      }

      have det_qar_neg : matrix_det q a r < 0 := by {
        rw [←σ_CW_iff_neg_det]
        rw [←σ_CW_iff_neg_det] at det_qpr_neg
        rw [σ_perm₂] at h3
        have: σ q r p = - σ q a r := by {
          aesop
        }
        rw [σ_perm₂] at this
        simp at this
        aesop
      }

      have det_par_pos : matrix_det p a r > 0 := by {
        rw [σ_perm₂] at h2
        rw [←σ_CCW_iff_pos_det]
        aesop
      }

      let aProjXPt : Point := ![(arProjX_p_q a r), 0]

      have pqa_pos : matrix_det p q a > 0 := by {

        have : σ p q a = Orientation.CCW := by {
          rw [h1]
          exact symm
        }
        rw [σ_CCW_iff_pos_det] at this
        exact this
      }
      have y_order : aProjXPt.y = 0 ∧ a.y > 0 ∧ r.y > a.y := by {
        use rfl
        constructor
        . rw [matrix_det_eq_det_pts] at pqa_pos
          unfold Point.det at pqa_pos
          rw [py0, qy0] at pqa_pos
          simp at pqa_pos
          nlinarith
        . rw [matrix_det_eq_det_pts] at det_par_pos
          rw [matrix_det_eq_det_pts] at det_qar_neg
          unfold Point.det at det_par_pos
          unfold Point.det at det_qar_neg
          rw [py0] at det_par_pos
          rw [qy0] at det_qar_neg
          simp at det_par_pos
          simp at det_qar_neg
          nlinarith
      }

      have arProjX_bet_p_q := arProjX_between_p_q py0 qy0 det_qar_neg det_par_pos y_order.2.2

      have arProjXPt_p_q_XOrdered : p.x < aProjXPt.x ∧ aProjXPt.x < q.x := by {
        exact arProjX_bet_p_q
      }

      have p_q_arProjXPt_collinear : matrix_det p q aProjXPt = 0 := by {
        rw [matrix_det_eq_det_pts]
        unfold Point.det
        rw [py0, qy0]
        simp
      }

      have aProjXPt_IsConvexCombOf_p_q :=
        convexComboOfCollinearAndXOrdered p q aProjXPt p_q_arProjXPt_collinear arProjXPt_p_q_XOrdered.1 arProjXPt_p_q_XOrdered.2


      have aProjX_r_a_collinear : matrix_det aProjXPt r a = 0 := by {
        rw [matrix_det_eq_det_pts]
        unfold Point.det
        dsimp
        unfold arProjX_p_q
        have : r.y - a.y ≠ 0 := by linarith
        apply mul_right_cancel₀ (b := r.y - a.y) this
        field_simp [this]
        ring
      }

      have a_IsConvexCombOf_aProjXPt_r :=
          convexComboOfCollinearAndYOrdered aProjXPt r a aProjX_r_a_collinear y_order.2.1 y_order.2.2

      have a_IsConvexCombOf_p_q_r :
        ∃ (α β γ : ℝ), α + β + γ = 1 ∧ α ≥ 0 ∧ β ≥ 0 ∧ γ ≥ 0 ∧ α • p + β • q + γ • r = a := by {
          exact convexComboTransitive aProjXPt_IsConvexCombOf_p_q a_IsConvexCombOf_aProjXPt_r
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

def translateMap (p : Point) : Point →ᵃ[ℝ] Point :=
  AffineMap.const ℝ Point p + AffineMap.id ℝ Point

theorem translateMap_apply (x : Point) : translateMap p x = p + x := by
  simp [translateMap]

def rotateTranslateMap (θ : ℝ) (p : Point) : Point →ᵃ[ℝ] Point :=
  AffineMap.comp (translateMap p) (rotationMap θ).toAffineMap


theorem injective_rotateTranslateMap (θ : ℝ) (p : Point) : Function.Injective (rotateTranslateMap θ p) := by
  unfold rotateTranslateMap
  apply Function.Injective.comp (g := translateMap p)
  . exact fun x y h => add_left_cancel h
  . simp [injective_rotationMap]

lemma pt_transform_translateMap (p  t: Point)  : pt_transform p (translation_matrix t.x t.y) = translateMap t p := by
  ext <;> simp [pt_transform, translation_matrix, Point.x, Point.y, vec_to_pt, pt_to_vec];
  ring_nf
  rw [translateMap_apply]
  simp
  rw [Matrix.mul_apply]
  rw [Fin.sum_univ_three]
  simp [add_comm]
  rw [Matrix.mul_apply]
  rw [Fin.sum_univ_three]
  simp
  rw [translateMap_apply]
  simp [add_comm]


noncomputable def rotate (θ : ℝ) (p : Point) : Point :=
  ![p 0 * (Real.cos θ) - p 1 * (Real.sin θ), p 0 * (Real.sin θ) + p 1 * (Real.cos θ)]

noncomputable def rotateTranslateSet (S : Set Point) (θ : ℝ) (tx ty : ℝ) : Set Point :=
  {rotateTranslate p θ tx ty | p ∈ S}

theorem PtInTriangle2InvariantUnderTransform {a p q r : Point}  (t : Point) (θ : ℝ) :
      PtInTriangle2 a p q r ↔ PtInTriangle2 (rotateTranslateMap θ t a) (rotateTranslateMap θ t p) (rotateTranslateMap θ t q) (rotateTranslateMap θ t r) := by
      unfold PtInTriangle2
      have := AffineMap.image_convexHull {p,q,r} (rotateTranslateMap θ t)
      simp [Set.image_insert_eq] at this
      rw [← this]
      set S := convexHull ℝ {p,q,r}
      symm
      apply Function.Injective.mem_set_image
      exact injective_rotateTranslateMap θ t

theorem rotateTranslateTransform (θ : ℝ) (t p : Point):
(rotateTranslateMap θ t p) = pt_transform p ((translation_matrix t.x t.y)*(Matrix.rotateByAffine θ)) := by
  rw [pt_transform_by_prod]
  unfold rotateTranslateMap
  simp
  rw [←pt_transform_rotateByAffine]
  rw [pt_transform_translateMap]
  unfold Matrix.rotateByAffine
  rfl

lemma rotateTranslateTMatrix (θ : ℝ) (t : Point) :
  TMatrix (translation_matrix t.x t.y * Matrix.rotateByAffine θ) := by
  have : TMatrix (translation_matrix t.x t.y) := by {
    exact translation_transform t.x t.y
  }
  exact TMatrix.mul this (TMatrix.rotateByAffine θ)

theorem rotateTranslatePreserveσ (θ : ℝ) (t p q r : Point) :
      σ p q r = σ (rotateTranslateMap θ t p) (rotateTranslateMap θ t q) (rotateTranslateMap θ t r) := by
      rw [rotateTranslateTransform]
      rw [rotateTranslateTransform]
      rw [rotateTranslateTransform]
      set T := (translation_matrix (Point.x t) (Point.y t) * Matrix.rotateByAffine θ)
      have : TMatrix T := by exact rotateTranslateTMatrix θ t
      apply transform_preserve_sigma p q r this


theorem σPtInTriangle2InvariantUnderTransform {a p q r : Point}  (t : Point) (θ : ℝ) :
      σPtInTriangle2 a p q r ↔ σPtInTriangle2 (rotateTranslateMap θ t a) (rotateTranslateMap θ t p) (rotateTranslateMap θ t q) (rotateTranslateMap θ t r) := by
      unfold σPtInTriangle2
      rw [←rotateTranslatePreserveσ]
      rw [←rotateTranslatePreserveσ]
      rw [←rotateTranslatePreserveσ]
      rw [←rotateTranslatePreserveσ]
      rw [←rotateTranslatePreserveσ]
      rw [←rotateTranslatePreserveσ]


theorem extraPiDoesntChange0y (θ : ℝ)  (p : Point) :
      (rotationMap θ p).y = 0 ↔ (rotationMap (θ + Real.pi) p).y = 0 := by
      apply Iff.intro
      {
        intro h
        simp at *
        linarith
      }
      {
        intro h
        simp at *
        linarith
      }


lemma translate_to_0_change (p t: Point) : (translateMap t p).y = 0 ↔ p.y + t.y = 0 := by
  rw [translateMap_apply]
  simp
  constructor
  . intro h; linarith
  . intro h; linarith


theorem extraPiDoesntChange0y' (θ : ℝ)  (p : Point) :
      (rotateTranslateMap θ ![0, -(rotationMap θ p).y] p).y = 0 ↔ ((rotateTranslateMap (θ + Real.pi) ![0, -(rotationMap (θ + Real.pi) p).y]) p).y = 0 := by
      apply Iff.intro
      {
        unfold rotateTranslateMap
        intro h
        simp at *
        rw [translate_to_0_change] at h
        rw [translate_to_0_change]
        simp
        simp at h
        linarith
      }
      {
        unfold rotateTranslateMap
        intro h
        simp at *
        rw [translate_to_0_change] at h
        rw [translate_to_0_change]
        simp
        simp at h
        linarith
      }


theorem existsNiceRotTrans {p q : Point} (diff: p ≠ q): ∃ (θ : ℝ) (t : Point),
              (rotateTranslateMap θ t p).y = 0
            ∧ (rotateTranslateMap θ t q).y = 0
            ∧ (rotateTranslateMap θ t p).x < (rotateTranslateMap θ t q).x := by
            by_cases same_x : p.x = q.x
            {
              by_cases p_above_q: p.y > q.y
              {
                use Real.pi/2
                let p' := rotationMap (Real.pi/2) p
                let q' := rotationMap (Real.pi/2) q
                use ![0, -p'.y]
                constructor
                . unfold rotateTranslateMap
                  simp
                  rw [translateMap_apply]
                  simp

                . constructor
                  . have same_y' : p'.y = q'.y := by {
                      simp
                      assumption
                    }
                    rw [same_y']
                    unfold rotateTranslateMap
                    simp
                    rw [translateMap_apply]
                    simp
                  . unfold rotateTranslateMap
                    simp
                    rw [translateMap_apply]
                    rw [translateMap_apply]
                    simp
                    ring_nf
                    linarith
              }
              {
                have p_below_q: p.y < q.y := by {
                  by_contra C
                  have same_y : p.y = q.y := by
                  {
                    exact _root_.le_antisymm (le_of_not_gt p_above_q) (le_of_not_gt C)
                  }
                  refine diff.elim ?_
                  ext <;> assumption
                }

                use -(Real.pi/2)
                let p' := rotationMap (-(Real.pi/2)) p
                let q' := rotationMap (-(Real.pi/2)) q
                use ![0, -p'.y]
                constructor
                . unfold rotateTranslateMap
                  simp
                  rw [translateMap_apply]
                  simp
                . constructor
                  . have same_y' : p'.y = q'.y := by {
                      simp
                      assumption
                    }
                    rw [same_y']
                    unfold rotateTranslateMap
                    simp
                    rw [translateMap_apply]
                    simp
                  . unfold rotateTranslateMap
                    simp
                    rw [translateMap_apply]
                    rw [translateMap_apply]
                    simp
                    ring_nf
                    linarith
              }
            }
            {
              obtain ⟨S, eq⟩: ∃ x, x = (q.y - p.y) / (q.x - p.x) := ⟨_, rfl⟩
              let θ := -Real.arctan (S)
              let p' := rotationMap θ p
              let t := ![0, -p'.y]

              have rpy0 : (rotateTranslateMap θ t p).y = 0 := by {
                unfold rotateTranslateMap
                simp
                rw [translateMap_apply]
                simp
                ring_nf
              }

              have rqy0 : (rotateTranslateMap θ t q).y = 0 := by {
                unfold rotateTranslateMap
                simp
                rw [translateMap_apply]
                simp
                rw [Real.sin_arctan]
                rw [Real.cos_arctan]
                calc -(1 / Real.sqrt (1 + S ^ 2) * Point.y p) + S / Real.sqrt (1 + S ^ 2) * Point.x p
                    + (-(S / Real.sqrt (1 + S ^ 2) * Point.x q) + 1 / Real.sqrt (1 + S ^ 2) * Point.y q)
                  _  = (1 / Real.sqrt (1 + S ^ 2))*(-Point.y p + Point.y q) + S / Real.sqrt (1 + S ^ 2) * Point.x p
                    + (-(S / Real.sqrt (1 + S ^ 2) * Point.x q)) := by ring_nf
                  _  =  (1 / Real.sqrt (1 + S ^ 2))*(-Point.y p + Point.y q) + (S / Real.sqrt (1 + S ^ 2) * (Point.x p - Point.x q)) := by ring_nf
                  _  =  ((Point.y q - Point.y p)  - (S* (q.x - p.x))) / Real.sqrt (1 + S ^ 2) := by ring_nf
                  _  =  ((Point.y q - Point.y p)  - ((q.y - p.y) / (q.x - p.x) * (q.x - p.x))) / Real.sqrt (1 + ((q.y - p.y) / (q.x - p.x) ) ^ 2) := by rw [eq]
                  _  = 0 :=  by field_simp [(sub_ne_zero.2 same_x)]; rw [@mul_div_cancel _ _ _ _ (sub_ne_zero.2 (Ne.symm same_x))]; simp
              }

              have post_neq : (rotateTranslateMap θ t p).x ≠ (rotateTranslateMap θ t q).x := by {
                have prev :  (rotateTranslateMap θ t p).y = (rotateTranslateMap θ t q).y := by linarith
                have injc :  (rotateTranslateMap θ t p) ≠ (rotateTranslateMap θ t q) := by {
                    intro pq
                    apply diff
                    apply injective_rotateTranslateMap _ _ pq
                  }
                intro pxqx
                apply injc (Point.ext pxqx prev)
              }

              by_cases post_lt : (rotateTranslateMap θ t p).x < (rotateTranslateMap θ t q).x
              {
                use θ, t
              }
              {
                rw [not_lt] at post_lt
                have : (rotateTranslateMap θ t q).x < (rotateTranslateMap θ t p).x := by apply lt_of_le_of_ne; exact post_lt; exact (Ne.symm post_neq)
                let θ' := θ + Real.pi
                let p'' := rotationMap θ' p



                let t'' := ![0, -p''.y]
                use θ', t''
                have g1: (rotateTranslateMap θ' t'' p).y = 0 := by {
                  unfold rotateTranslateMap
                  simp
                  rw [translateMap_apply]
                  simp
                  ring_nf
                }
                have g2: (rotateTranslateMap θ' t'' q).y = 0 := by {
                  unfold rotateTranslateMap
                  simp
                  rw [translateMap_apply]
                  simp
                  rw [Real.sin_arctan, Real.cos_arctan]
                  field_simp
                  calc Point.y p + -(S * Point.x p) + (S * Point.x q + -Point.y q)
                    _ = Point.y p + -S * Point.x p + S * Point.x q + -Point.y q := by ring_nf
                    _ = Point.y p + S * (Point.x q - Point.x p) + -Point.y q := by ring_nf
                    _ = (Point.y p - Point.y q) + S * (Point.x q - Point.x p) := by ring_nf
                    _ = (Point.y p - Point.y q) + ((Point.y q - Point.y p) / (Point.x q - Point.x p)) * (Point.x q - Point.x p) := by rw [eq]
                    _ = 0 := by field_simp [(sub_ne_zero.2 same_x)]; rw [@mul_div_cancel _ _ _ _ (sub_ne_zero.2 (Ne.symm same_x))]; simp
                }
                have g3: (rotateTranslateMap θ' t'' p).x < (rotateTranslateMap θ' t'' q).x := by {
                  unfold rotateTranslateMap
                  simp
                  rw [translateMap_apply, translateMap_apply]
                  simp
                  unfold rotateTranslateMap at this
                  simp at this
                  rw [translateMap_apply, translateMap_apply] at this
                  simp at this
                  nlinarith
                }
                exact ⟨g1, g2, g3⟩
              }
            }

theorem PtInTriangle2_of_σPtInTriange2' {a p q r : Point} (gp : Point.InGeneralPosition₄ a  p q r)
      (symm: σ p q r = Orientation.CCW):
       σPtInTriangle2 a p q r → PtInTriangle2 a p q r  := by
       intro h
       have p_neq_q : p ≠ q := by {
         have l := gp.4
         unfold Point.InGeneralPosition₃ at l
         unfold Point.det at l
         by_contra C
         simp [C] at l
         ring_nf at l
         tauto
       }

       have ⟨θ, t, h1, h2, h3⟩ := existsNiceRotTrans p_neq_q
       set p' := rotateTranslateMap θ t p
       set q' := rotateTranslateMap θ t q
       set r' := rotateTranslateMap θ t r
       set a' := rotateTranslateMap θ t a
       have a'inTri : σPtInTriangle2 a' p' q' r' := by {
         rw [←σPtInTriangle2InvariantUnderTransform]
         exact h
       }
       have symm' : σ p' q' r' = Orientation.CCW := by {
          rw [←rotateTranslatePreserveσ]
          exact symm
       }
       have := PtInTriangle2_of_σPtInTriange2 h3 symm' h1 h2 a'inTri
       rw [←PtInTriangle2InvariantUnderTransform] at this
       exact this


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


infix:50 " ~_σ " => σ_equivalence
def OrientationProperty (P : List Point → Prop) :=
  ∀ l₁ l₂, (Point.PointListInGeneralPosition l₁ ∧ Point.PointListInGeneralPosition l₂)  →  l₁ ~_σ l₂ → (P l₁ ↔ P l₂)

theorem OrientationProperty.not : OrientationProperty P → OrientationProperty (¬P ·) := by
  unfold OrientationProperty
  intro h l₁ l₂ hσ
  simp [h l₁ l₂ hσ]
  have := h l₁ l₂ hσ
  aesop


theorem σHasEmptyTriangle_iff_σHasEmptyTriangle2 {pts : List Point} (gp : Point.PointListInGeneralPosition pts) :
    σHasEmptyTriangle pts ↔ σHasEmptyTriangle2 pts := by
  unfold σHasEmptyTriangle σHasEmptyTriangle2
  sorry -- obvious, TODO WN

theorem σHasEmptyTriangle_iff {pts : List Point} (gp : Point.PointListInGeneralPosition pts) :
    σHasEmptyTriangle2 pts ↔ HasEmptyTriangle pts := by
  unfold σHasEmptyTriangle2 HasEmptyTriangle
  sorry -- obvious, TODO WN

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
