import Std.Data.List.Lemmas
import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Algebra.Basic
import Geo.Orientations
import Geo.ToMathlib
import Geo.PointsToWB.TMatrix
import Geo.Definitions.WBPoints
import Geo.PointsToWB.Affine
import Geo.PointsToWB.Projective
import Geo.SigmaEquiv

open Classical
open scoped List

namespace Geo

structure σEmbed (S T : List Point) :=
  (f : Point → Point)
  (perm : S.map f ~ T)
  (σ : ∀ p q r, p ∈ S → q ∈ S → r ∈ S → σ (f p) (f q) (f r) = σ p q r)

infix:50 " ≼σ " => σEmbed

theorem σEmbed.mem_iff (σ : S ≼σ T) : y ∈ T ↔ ∃ x ∈ S, σ.f x = y :=
  σ.perm.mem_iff.symm.trans (by simp)

theorem σEmbed.mem (σ : S ≼σ T) (h : x ∈ S) : σ.f x ∈ T := σ.mem_iff.2 ⟨_, h, rfl⟩

def σEmbed.permRight (σ : S ≼σ T) (h : T ~ T') : S ≼σ T' :=
  { σ with perm := σ.perm.trans h }

def σEmbed.permLeft (σ : S ≼σ T) (h : S ~ S') : S' ≼σ T :=
  { σ with perm := (h.symm.map _).trans σ.perm, σ := by simpa [h.symm.mem_iff] using σ.σ }

def σEmbed.range (σ : S ≼σ T) : List Point := S.map σ.f

theorem σEmbed.length_eq (σ : S ≼σ T) : S.length = T.length := by simp [← σ.perm.length_eq]

def σEmbed.refl (S : List Point) : S ≼σ S := ⟨id, by simp, by simp⟩

def σEmbed.trans (f : S ≼σ T) (g : T ≼σ U) : S ≼σ U := by
  refine ⟨g.f ∘ f.f, by simpa using (f.perm.map _).trans g.perm, fun p q r hp hq hr => ?_⟩
  simp [f.σ _ _ _ hp hq hr, g.σ _ _ _ (f.mem hp) (f.mem hq) (f.mem hr)]

noncomputable def σEmbed.toEquiv (f : S ≼σ T) (h : T.Nodup) : S.toFinset ≃σ T.toFinset := by
  refine ⟨Equiv.ofBijective (fun x => ⟨f.f x.1, ?_⟩) ⟨?_, ?_⟩, ?c⟩
  case c =>
    simp [Equiv.ofBijective, DFunLike.coe, EquivLike.coe]
    exact fun _ ha _ hb _ hc => (f.σ _ _ _ ha hb hc).symm
  · rcases x with ⟨x, hx⟩; simp at hx ⊢; exact f.mem hx
  · intro ⟨a, ha⟩ ⟨b, hb⟩ eq; simp at ha hb eq ⊢
    by_contra ne
    exact (List.pairwise_map.1 (f.perm.nodup_iff.2 h)).forall (fun _ _ => Ne.symm) ha hb ne eq
  · intro ⟨b, hb⟩; simp at hb ⊢
    exact f.mem_iff.1 hb

def OrientationProperty' (P : List Point → Prop) :=
  ∀ {{S T}}, S ≼σ T → (P S ↔ P T)

theorem OrientationProperty'.not : OrientationProperty' P → OrientationProperty' (¬P ·) :=
  fun h _ _ hσ => not_congr (h hσ)

theorem σEmbed.gp : OrientationProperty' Point.PointListInGeneralPosition := fun S T f => by
  rw [← Point.PointListInGeneralPosition.perm f.perm]
  simp only [Point.PointListInGeneralPosition, ← List.mem_sublists, List.sublists_map]
  simp [Point.InGeneralPosition₃.iff_ne_collinear]
  constructor
  · intro | H, _, _, _, [p',q',r'], sl, rfl => ?_
    have := sl.subset; simp at this
    rw [f.σ _ _ _ this.1 this.2.1 this.2.2]; exact H sl
  · intro H p q r sl
    have := sl.subset; simp at this
    rw [← f.σ _ _ _ this.1 this.2.1 this.2.2]; exact H _ sl rfl

variable {l : List Point} (hl : 3 ≤ l.length) (gp : Point.PointListInGeneralPosition l)

theorem σEmbed.len_ge_3 (σ : l ≼σ l') : 3 ≤ l'.length := σ.length_eq ▸ hl

theorem symmetry_breaking : ∃ w : WBPoints, Nonempty (l ≼σ w.points) := by

  -- step 1: rotate
  have ⟨l1, σ1, hl1⟩ : ∃ l1, ∃ _ : l ≼σ l1, l1.Pairwise (·.x ≠ ·.x) := by
    have ⟨θ, hθ⟩ := distinct_rotate_finset _ l.finite_toSet.countable
    refine have σ := ⟨rotationMap θ, .rfl, fun p q r _ _ _ => ?hσ⟩; ⟨_, σ, ?_⟩
    case hσ =>
      simpa [pt_transform_rotateByAffine] using
        (TMatrix.rotateByAffine θ).pt_transform_preserves_sigma p q r
    have := (σ.gp.1 gp).nodup (σ.len_ge_3 hl)
    exact this.imp_of_mem fun ha hb => hθ (by simpa using ha) (by simpa using hb)

  -- step 2: translate
  have ⟨l2, σ2, l2_lt /-, l2_pw -/⟩ : ∃ l2, ∃ _ : l ≼σ 0 :: l2,
      (∀ p ∈ l2, 0 < p.x) /- ∧ l2.Pairwise (·.x ≠ ·.x) -/ := by
    cases e : l1.argmin (·.x) with
    | none => simp at e; cases e; cases σ1.len_ge_3 hl
    | some a => ?_
    let l1' := l1.erase a
    have p1 : l1 ~ a :: l1' := List.perm_cons_erase (List.argmin_mem e)
    let f := (· - a)
    have σ2 : l1 ≼σ 0 :: l1'.map f := { f, perm := (p1.map _).trans (by simp), σ := ?σ }
    case σ =>
      have eq (p) : pt_transform (translation_matrix (-a.x) (-a.y)) p = p - a := by
        ext <;> simp [translation_translates] <;> rfl
      intro p q r _ _ _
      simpa [eq] using (translation_transform (-a.x) (-a.y)).pt_transform_preserves_sigma p q r
    have ⟨ha, _hl1'⟩ := List.pairwise_cons.1 (hl1.perm p1 Ne.symm)
    refine ⟨_, σ1.trans σ2, ?_ /- , hl1'.map _ fun _ _ => mt sub_left_inj.1 -/⟩
    simp; intro a h'
    exact lt_of_le_of_ne (List.le_of_mem_argmin (List.mem_of_mem_erase h') e) (ha _ h')
  clear l1 σ1 hl1

  -- step 3: projection
  have ⟨l3, σ3, l3_orient, l3_ne⟩ : ∃ l3, ∃ f : l2 ≼σ l3,
      (∀ x y, x ∈ l2 → y ∈ l2 → orientWithInfty (f.f x) (f.f y) = σ 0 x y) ∧
      l3.Pairwise (·.x ≠ ·.x) := by
    refine
      let σ := ⟨projectiveMap, .rfl, fun _ _ _ hp hq hr => ?hσ⟩
      have horient := ?_; ⟨_, σ, horient, ?_⟩
    case hσ => exact (orientations_preserved (l2_lt _ hp) (l2_lt _ hq) (l2_lt _ hr)).symm
    · intro _ _ hp hq; exact (orientWithInfty_preserved (l2_lt _ hp) (l2_lt _ hq)).symm
    · refine List.pairwise_map.2 <| List.pairwise_iff_forall_sublist.2 fun h => Ne.symm ?_
      have := σ2.gp.1 gp <| .cons₂ _ h
      have h := h.subset; simp at h
      rwa [Point.InGeneralPosition₃.iff_ne_collinear, ← horient _ _ h.1 h.2,
        orientWithInfty, Ne, Orientation.ofReal_eq_collinear, sub_eq_zero] at this

  -- step 4: sort
  have ⟨l4, σ4, l4_orient, l4_lt⟩ : ∃ l4, ∃ f : l2 ≼σ l4,
      (∀ x y, x ∈ l2 → y ∈ l2 → orientWithInfty (f.f x) (f.f y) = σ 0 x y) ∧
      l4.Pairwise (·.x < ·.x) := by
    let l4 := l3.mergeSort (·.x ≤ ·.x)
    have p4 : l3 ~ l4 := (l3.perm_mergeSort _).symm
    refine ⟨l4, σ3.permRight p4, l3_orient, (l3_ne.perm p4 Ne.symm).imp₂ ?_ (l3.sorted_mergeSort _)⟩
    exact fun _ _ h1 h2 => lt_of_le_of_ne h2 h1
  clear l3 σ3 l3_orient l3_ne

  -- step 5: bring ∞ back into the range
  have ⟨z, hleft, horiented⟩ := exists_pt_st_orientations_preserved l4 l4_lt
  have l2_nz : ∀ p ∈ l2, p ≠ 0 := by rintro _ h rfl; exact lt_irrefl _ (l2_lt _ h)
  have σ5 : l ≼σ z :: l4 := σ2.trans {
    f := fun p => if p = 0 then z else σ4.f p
    perm := by
      simp; refine List.map_congr ?_ ▸ σ4.perm
      intro _ hx; rw [if_neg (l2_nz _ hx)]
    σ := by
      simp
      have {p q} (hp : p ∈ l2) (hq : q ∈ l2) : σ z (σEmbed.f σ4 p) (σEmbed.f σ4 q) = σ 0 p q := by
        rw [← horiented _ (σ4.mem hp) _ (σ4.mem hq), l4_orient _ _ hp hq]
      rintro _ _ _ (rfl | hp) (rfl | hq) (rfl | hr)
        <;> try simp [σ_self₁, σ_self₂, σ_self₃, *]
      · rw [σ_perm₁, this hp hr, ← σ_perm₁]
      · rw [σ_perm₂, σ_perm₁, this hp hq, ← σ_perm₁, ← σ_perm₂]
      · exact σ4.σ _ _ _ hp hq hr
  }

  -- step 6: construct
  exact ⟨{
    leftmost := z
    rest := l4
    sorted' := List.sorted_cons.2 ⟨hleft, l4_lt⟩
    gp' := σ5.gp.1 gp
    oriented := l4_lt.imp_of_mem fun ha hb h => by
      rwa [← horiented _ ha _ hb, orientWithInfty, Orientation.ofReal_eq_ccw, sub_pos]
  }, ⟨σ5⟩⟩
