import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Algebra.Basic
import Geo.ToMathlib
import Geo.Definitions.SigmaEmbed
import Geo.Definitions.CanonicalPoints
import Geo.Definitions.Structures
import Geo.Definitions.OrientationProperties
import Geo.Canonicalization.TMatrix
import Geo.Canonicalization.Affine
import Geo.Canonicalization.Projective

namespace Geo
open Classical
open scoped List

def σEmbed.reverse (S : List Point) : S ≼σ S.reverse :=
  ⟨id, by simp [List.reverse_perm S |>.symm], false, by simp⟩

def σEmbed.flipX (S : List Point) : S ≼σ S.map flipX :=
  ⟨Geo.flipX, by simp, true, by
    simp [Geo.σ, Geo.flipX, Point.det_eq, Orientation.true_xor, ← Orientation.ofReal_neg]
    intros; congr 1; ring⟩

lemma sorted_reverse_flipX {S : List Point} :
    S.Sorted (·.x < ·.x) → (S.reverse.map Geo.flipX).Sorted (·.x < ·.x) := by
  simp [List.Sorted, List.pairwise_map, flipX, List.pairwise_reverse]

lemma orientWithInfty_flipX (P Q : Point) :
    orientWithInfty (flipX P) (flipX Q) = -orientWithInfty P Q := by
  simp [orientWithInfty, flipX, ← Orientation.ofReal_neg]
  congr 1; ring

theorem σEmbed_rotate (l : List Point) (h : l.Nodup) :
    ∃ l', ∃ _ : l ≼σ l', l'.Pairwise (·.x ≠ ·.x) := by
  have ⟨θ, hDistinct⟩ := distinct_rotate_list _ h
  refine have σ := ⟨rotationMap θ, .rfl, false, fun p q r _ _ _ => ?hσ⟩; ⟨_, σ, hDistinct⟩
  case hσ =>
    simpa [ptTransform_rotateByAffine] using
      (TMatrix.rotateByAffine θ).ptTransform_preserves_sigma p q r

variable {l : List Point} (hl : 3 ≤ l.length) (gp : Point.ListInGenPos l)

theorem σEmbed.len_ge_3 (σ : l ≼σ l') : 3 ≤ l'.length := σ.length_eq ▸ hl

theorem symmetry_breaking : ∃ w : CanonicalPoints, Nonempty (l ≼σ w.points) := by

  -- step 1: rotate
  have ⟨l1, σ1, hl1⟩ : ∃ l1, ∃ _ : l ≼σ l1, l1.Pairwise (·.x ≠ ·.x) :=
    σEmbed_rotate l (gp.nodup hl)

  -- step 2: translate
  have ⟨l2, σ2, l2_lt /-, l2_pw -/⟩ : ∃ l2, ∃ _ : l ≼σ 0 :: l2,
      (∀ p ∈ l2, 0 < p.x) /- ∧ l2.Pairwise (·.x ≠ ·.x) -/ := by
    cases e : l1.argmin (·.x) with
    | none => simp at e; cases e; cases σ1.len_ge_3 hl
    | some a => ?_
    let l1' := l1.erase a
    have p1 : l1 ~ a :: l1' := List.perm_cons_erase (List.argmin_mem e)
    let f := (· - a)
    have σ2 : l1 ≼σ 0 :: l1'.map f := { f, perm := (p1.map _).trans (by simp), σ_eq := ?σ_eq }
    case σ_eq =>
      have eq (p) : ptTransform (translationMatrix (-a.x) (-a.y)) p = p - a := by
        ext <;> simp [translation_translates] <;> rfl
      intro p q r _ _ _
      simpa [eq] using (translationTransform (-a.x) (-a.y)).ptTransform_preserves_sigma p q r
    have ⟨ha, _hl1'⟩ := List.pairwise_cons.1 (hl1.perm p1 Ne.symm)
    refine ⟨_, σ1.trans σ2, ?_ /- , hl1'.map _ fun _ _ => mt sub_left_inj.1 -/⟩
    simp; intro a h'
    exact lt_of_le_of_ne (List.le_of_mem_argmin (List.mem_of_mem_erase h') e) (ha _ h')
  clear l1 σ1 hl1

  -- step 3: projection
  have ⟨l3, σ3, l3_orient, l3_ne⟩ : ∃ l3, ∃ f : l2 ≼σ l3,
      (∀ x y, x ∈ l2 → y ∈ l2 → orientWithInfty (f.f x) (f.f y) = f.parity ^^^ σ 0 x y) ∧
      l3.Pairwise (·.x ≠ ·.x) := by
    refine
      let σ := ⟨projectiveMap, .rfl, false, fun _ _ _ hp hq hr => ?hσ⟩
      have horient := ?_; ⟨_, σ, horient, ?_⟩
    case hσ => exact (orientations_preserved (l2_lt _ hp) (l2_lt _ hq) (l2_lt _ hr)).symm
    · intro _ _ hp hq; exact (orientWithInfty_preserved (l2_lt _ hp) (l2_lt _ hq)).symm
    · refine List.pairwise_map.2 <| List.pairwise_iff_forall_sublist.2 fun h => Ne.symm ?_
      have := (OrientationProperty'.gp σ2).1 gp <| .cons₂ _ h
      have h := h.subset; simp at h horient
      rwa [Point.InGenPos₃.iff_ne_collinear, ← horient _ _ h.1 h.2,
        orientWithInfty, Ne, Orientation.ofReal_eq_collinear, sub_eq_zero] at this

  -- step 4: sort
  have ⟨l4, σ4, l4_orient, l4_lt⟩ : ∃ l4, ∃ f : l2 ≼σ l4,
      (∀ x y, x ∈ l2 → y ∈ l2 → orientWithInfty (f.f x) (f.f y) = f.parity ^^^ σ 0 x y) ∧
      l4.Pairwise (·.x < ·.x) := by
    let l4 := l3.mergeSort (·.x ≤ ·.x)
    have p4 : l3 ~ l4 := (l3.perm_mergeSort _).symm
    refine ⟨l4, σ3.permRight p4, l3_orient, (l3_ne.perm p4 Ne.symm).imp₂ ?_ (l3.sorted_mergeSort _)⟩
    exact fun _ _ h1 h2 => lt_of_le_of_ne h2 h1
  clear l3 σ3 l3_orient l3_ne
  save

  -- step 5: left-right flip
  have ⟨l5, σ5, l5_orient, l5_lt, l5_adj⟩ : ∃ l5, ∃ f : l2 ≼σ l5,
      (∀ p q, p ∈ l2 → q ∈ l2 → orientWithInfty (f.f p) (f.f q) = f.parity ^^^ σ 0 p q) ∧
      l5.Pairwise (·.x < ·.x) ∧ σRevLex l5 := by
    if l4_adj : σRevLex l4 then
      exact ⟨l4, σ4, l4_orient, l4_lt, l4_adj⟩
    else
      have l4_rev_adj : σRevLex (l4.reverse.map flipX) :=
        (σRevLex_total l4).elim (by intro; contradiction) id
      refine ⟨
        l4.reverse.map flipX,
        σ4.trans (σEmbed.reverse _) |>.trans (σEmbed.flipX _),
        ?_,
        sorted_reverse_flipX l4_lt, l4_rev_adj⟩
      simp (config := {contextual := true})
        [σEmbed.trans, σEmbed.reverse, σEmbed.flipX, orientWithInfty_flipX, l4_orient]
  clear l4 σ4 l4_orient l4_lt

  -- step 6: bring ∞ back into the range
  have ⟨z, hleft, horiented⟩ := exists_pt_st_orientations_preserved l5 l5_lt
  have l2_nz : ∀ p ∈ l2, p ≠ 0 := by rintro _ h rfl; exact lt_irrefl _ (l2_lt _ h)
  have σ5 : l ≼σ z :: l5 := σ2.trans {
    f := fun p => if p = 0 then z else σ5.f p
    perm := by
      simp; refine List.map_congr ?_ ▸ σ5.perm
      intro _ hx; rw [if_neg (l2_nz _ hx)]
    parity := σ5.parity
    σ_eq := by
      simp
      have {p q} (hp : p ∈ l2) (hq : q ∈ l2) : σ z (σ5.f p) (σ5.f q) = σ5.parity ^^^ σ 0 p q := by
        rw [← horiented _ (σ5.mem hp) _ (σ5.mem hq), l5_orient _ _ hp hq]
      rintro _ _ _ (rfl | hp) (rfl | hq) (rfl | hr)
        <;> try simp [σ_self₁, σ_self₂, σ_self₃, *]
      · rw [σ_perm₁, this hp hr, σ_perm₁]; simp
      · rw [σ_perm₂, σ_perm₁, this hp hq, σ_perm₁, σ_perm₂]; simp
      · exact σ5.σ_eq _ _ _ hp hq hr
  }

  -- step 7: construct
  exact ⟨{
    leftmost := z
    rest := l5
    sorted' := List.sorted_cons.2 ⟨hleft, l5_lt⟩
    gp' := (OrientationProperty'.gp σ5).mp gp
    lex := l5_adj
    oriented := l5_lt.imp_of_mem fun ha hb h => by
      rwa [← horiented _ ha _ hb, orientWithInfty, Orientation.ofReal_eq_ccw, sub_pos]
  }, ⟨σ5⟩⟩

-- WN: I put this here since it uses some σEmbed lemmas.
theorem HasEmptyKGon_extension :
    (∀ l : List Point, Point.ListInGenPos l → l.length = n → HasEmptyKGon k l.toFinset) →
    3 ≤ n → n ≤ l.length → HasEmptyKGon k l.toFinset := by
  intro H threen llength
  rw [← σHasEmptyKGon_iff_HasEmptyKGon gp]

  have ⟨l₁, σ₁, distinct⟩ := σEmbed_rotate l (gp.nodup <| threen.trans llength)
  replace gp := (OrientationProperty'.gp σ₁).mp gp
  replace llength := σ₁.length_eq ▸ llength
  replace σ₁ := σ₁.toEquiv (gp.nodup <| threen.trans llength)
  suffices σHasEmptyKGon k l₁.toFinset from
    OrientationProperty_σHasEmptyKGon σ₁.symm this

  let l₂ := l₁.insertionSort (·.x ≤ ·.x)
  have l₂l₁ : l₂ ~ l₁ := l₁.perm_insertionSort _
  replace gp := Point.ListInGenPos.perm l₂l₁ |>.mpr gp
  replace llength : n ≤ l₂.length := l₂l₁.length_eq ▸ llength
  replace distinct := distinct.perm l₂l₁.symm Ne.symm
  have l₂sorted : l₂.Sorted (·.x < ·.x) :=
    List.pairwise_iff_get.mpr fun i j ij =>
      have that := List.pairwise_iff_get.mp (l₁.sorted_insertionSort (·.x ≤ ·.x)) i j ij
      have := List.pairwise_iff_get.mp distinct i j ij
      lt_of_le_of_ne that this
  suffices σHasEmptyKGon k l₂.toFinset by
    rwa [List.toFinset_eq_of_perm _ _ l₂l₁] at this

  rw [σHasEmptyKGon_iff_HasEmptyKGon gp]
  let left := l₂.take n
  let right := l₂.drop n
  have leftl₂ : left <+ l₂ := List.take_sublist ..
  have leftlength := List.length_take_of_le llength
  have := H left (gp.mono_sublist leftl₂) leftlength

  unfold HasEmptyKGon at this ⊢
  have ⟨s, scard, sleft, ⟨convex, empty⟩⟩ := this
  refine ⟨s, scard, ?_, convex, ?_⟩
  . exact sleft.trans leftl₂.toFinset_subset
  . simp (config := {zeta := false}) only
      [EmptyShapeIn, List.mem_toFinset, Set.mem_diff, Finset.mem_coe] at empty ⊢
    intro p ⟨pl₂, ps⟩
    by_cases pleft : p ∈ left
    . apply empty p ⟨pleft, ps⟩
    intro pCH
    have pright : p ∈ right := by
      by_contra
      rw [← List.take_append_drop n l₂, List.mem_append] at pl₂
      cases pl₂ <;> contradiction
    apply lt_irrefl p.x
    refine xlt_convexHull (s := s) (x₀ := p.x) ?_ _ pCH
    intro q qleft
    replace qleft := List.mem_toFinset.mp <| sleft qleft
    have ⟨⟨i, ilt⟩, hi⟩ := List.get_of_mem qleft
    have ⟨j, hj⟩ := List.get_of_mem pright
    rw [← hi, ← hj, List.get_take', List.get_drop']
    rw [leftlength] at ilt
    apply List.pairwise_iff_get.mp l₂sorted
    simp; omega
