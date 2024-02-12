import Geo.Point
import Geo.WBPoints
import Geo.toMathlib
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

-- σ p q r = .CCW
theorem σPtInTriangle_iff2 {a p q r : Point} (gp : Point.PointListInGeneralPosition [a, p, q, r])
      (symm: σ p q r = Orientation.CCW) :
    σPtInTriangle2 a p q r ↔ PtInTriangle2 a p q r := by
    apply Iff.intro
    {
     intro h
     unfold σPtInTriangle2 at h
     unfold PtInTriangle2
     have h1 := h.1
     have h2 := h.2.1
     have h3 := h.2.2
     let halfPlanePQ := halfPlaneCCW p q
     unfold halfPlaneCCW at halfPlanePQ
     have h4: σ p q a = Orientation.CCW := by
        rw [←symm]
        exact h1
     have h5: a ∈ halfPlanePQ := by
        {
          rw [detIffHalfPlaneCCW]
          rw [σ_CCW_iff_pos_det] at h4
          linarith
        }
     let halfPlaneQR := halfPlaneCCW q r
     have symm_conseq: σ q r p = Orientation.CCW := by
        {sorry}
     have qraCCW: σ q r a = Orientation.CCW := by
        {
          rw [←symm_conseq]
          exact h3
        }
     have h6: a ∈ halfPlaneQR := by
          {
            rw [detIffHalfPlaneCCW]
            rw [σ_CCW_iff_pos_det] at qraCCW
            linarith
          }
     let halfPlaneRP := halfPlaneCCW r p
     have symm_conseq2: σ r p q = Orientation.CCW := by
          {sorry}
     have rpaCCW: σ r p a = Orientation.CCW := by
          {
              rw [←symm_conseq2]
              sorry
          }
     have h7: a ∈ halfPlaneRP := by
            {
              rw [detIffHalfPlaneCCW]
              rw [σ_CCW_iff_pos_det] at rpaCCW
              linarith
            }
     have cRP: Convex ℝ (halfPlaneCCW r p) := by
        {
          exact HalfPlanesAreConvex
        }
     have cPQ: Convex ℝ (halfPlaneCCW p q) := by
          {
            exact HalfPlanesAreConvex
          }
     have cQR: Convex ℝ (halfPlaneCCW q r) := by
              {
                exact HalfPlanesAreConvex
              }
     let inter := halfPlaneCCW p q ∩ (halfPlaneCCW q r ∩ halfPlaneCCW r p)
     have interConvex : Convex ℝ inter := by
        {
          exact Convex.inter cPQ (Convex.inter cQR cRP)
        }
     have h8: a ∈ inter := Set.mem_inter h5 (Set.mem_inter h6 h7)
     have pPQ: p ∈ halfPlaneCCW p q := by
        {
          unfold halfPlaneCCW
          simp
          unfold ptInsideHalfPlaneCCW
          right
          rw [σ_Co_iff_pos_0]
          rw [matrix_det_eq_det_pts]
          unfold Point.det
          linarith
        }
     have pRP: p ∈ halfPlaneCCW r p := by
        {
          unfold halfPlaneCCW
          simp
          unfold ptInsideHalfPlaneCCW
          right
          rw [σ_Co_iff_pos_0]
          rw [matrix_det_eq_det_pts]
          unfold Point.det
          linarith
        }
     have pQR: p ∈ halfPlaneCCW q r:= by
        {
          unfold halfPlaneCCW
          simp
          unfold ptInsideHalfPlaneCCW
          left
          exact symm_conseq
        }
     have pInter: p ∈ inter := Set.mem_inter pPQ (Set.mem_inter pQR pRP)
     have qPQ: q ∈ halfPlaneCCW p q := by
          {
            unfold halfPlaneCCW
            simp
            unfold ptInsideHalfPlaneCCW
            right
            rw [σ_Co_iff_pos_0]
            rw [matrix_det_eq_det_pts]
            unfold Point.det
            linarith
          }
     have qQR: q ∈ halfPlaneCCW q r := by
          {
            unfold halfPlaneCCW
            simp
            unfold ptInsideHalfPlaneCCW
            right
            rw [σ_Co_iff_pos_0]
            rw [matrix_det_eq_det_pts]
            unfold Point.det
            linarith
          }
     have qRP: q ∈ halfPlaneCCW r p := by
          {
            unfold halfPlaneCCW
            simp
            unfold ptInsideHalfPlaneCCW
            left
            exact symm_conseq2
          }
     have qInter: q ∈ inter := Set.mem_inter qPQ (Set.mem_inter qQR qRP)
     have rPQ: r ∈ halfPlaneCCW p q := by
            {
              unfold halfPlaneCCW
              simp
              unfold ptInsideHalfPlaneCCW
              left
              exact symm
            }
     have rQR: r ∈ halfPlaneCCW q r := by
              {
                unfold halfPlaneCCW
                simp
                unfold ptInsideHalfPlaneCCW
                right
                rw [σ_Co_iff_pos_0]
                rw [matrix_det_eq_det_pts]
                unfold Point.det
                linarith
              }
     have rRP: r ∈ halfPlaneCCW r p := by
                {
                  unfold halfPlaneCCW
                  simp
                  unfold ptInsideHalfPlaneCCW
                  right
                  rw [σ_Co_iff_pos_0]
                  rw [matrix_det_eq_det_pts]
                  unfold Point.det
                  linarith
                }
     have rInter: r ∈ inter := Set.mem_inter rPQ (Set.mem_inter rQR rRP)
    --  unfold convexHull
    -- inter : Set Point
    -- interConvex
    -- r, p, q, a ∈ inter
    --
     apply mem_convexHull_iff.mpr
     intro S Spqr convexS

     ---- Convexity implies:
      ----- ∀ x, y ∈ S, ∀ α, β, α + β = 1, α, β ≥ 0
        ----→ α • x + β • y ∈ S

        -- By induction:
          --- ∀ x₁, …, xₙ ∈ S, ∀ α₁, …, αₙ, α₁ + … + αₙ = 1, α₁, …, αₙ ≥ 0
            ----→ α₁ • x₁ + … + αₙ • xₙ ∈ S
      --- Claim: in a two dimensional space,
        --- any point in a convex set L
        --- can be written as a convex combination of any three points in L as long as those 3 points are not collinear


     -- w.t.s. that inter ⊆ S
      ----  let x ∈ inter
        --- Claim: there are α, β, γ such that
          ---  x = α • p + β • q + γ • r
            -- with α + β + γ = 1, α, β, γ ≥ 0
          --- Proof of Claim:
             ---

     sorry
    }
    {
     sorry
    }
    ---
    ----
    /--
     (-->)
        Assume σPtInTriangle a p q r.
        This means that a is on the same side that the lines
        pq, qr, and rp are on.
        Let α be the half plane to the right of pq
        Let β be the half plane above/below the line pr
        Let γ be the half plane to the left of qr
        Then by the σ properties we should have
        that a ∈ α ∩ β ∩ γ.
        Now, each of this is convex. So ther intersection
        is convex. Moreover, {p, q, r} ∈ α ∩ β ∩ γ.
        which implies that a ∈ α ∩ β ∩ γ ⊆ convHull {p, q, r}.
        and thus we have ptInTriangle a p q r.
      (<---)
        Assume ptInTriangle a p q r.
        Then a ∈ convHull {p, q, r}.
        This implies a is in every convex set that contains {p, q, r}.
        This implies a is in the intersection of the half planes
        and thus it signotopes work as expected.



    -/
  -- geometry and signotope stuff TODO(Bernardo)

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


theorem OrientationProperty_σHas      EmptyTriangle : OrientationProperty σHasEmptyTriangle := by
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
