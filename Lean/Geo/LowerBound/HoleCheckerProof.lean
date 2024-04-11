import Geo.Definitions.Structures
import Geo.Definitions.OrientationProperties
import Geo.Definitions.hNotation
import Geo.LowerBound.HoleChecker
import Geo.Canonicalization.Projective

namespace Geo
namespace HoleChecker
open Classical List

@[coe] def NPoint.toPoint (p : NPoint) : Point := ![p.1, p.2]

instance : Coe NPoint Point := ⟨NPoint.toPoint⟩
local notation "↑'" pts:max => List.map NPoint.toPoint pts

@[simp] theorem NPoint.toPoint_x (p : NPoint) : p.toPoint.x = p.1 := by simp [toPoint]
@[simp] theorem NPoint.toPoint_y (p : NPoint) : p.toPoint.y = p.2 := by simp [toPoint]

theorem toPoint_inj {p q : NPoint} (h : p.toPoint = q.toPoint) : p = q := by
  apply Prod.ext <;> apply (Nat.cast_inj (R := ℝ)).1
  · rw [← NPoint.toPoint_x, h, NPoint.toPoint_x]
  · rw [← NPoint.toPoint_y, h, NPoint.toPoint_y]

theorem ccw_iff (a b c : NPoint) : ccw a b c ↔ σ a b c = .ccw := by
  simp [ccw, σ, Orientation.ofReal_eq_ccw, Point.det_eq]
  rw [← Nat.cast_lt (α := ℝ), ← sub_pos, ← sub_pos (b := _*_)]
  congr! 1; simp; ring

theorem slope_lt {p a b : NPoint} (ha : p.1 < a.1) (hb : p.1 < b.1) :
    let slope q := mkRat (q.2 - p.2) (q.1 - p.1)
    slope a < slope b ↔ σ p a b = .ccw := by
  simp [Rat.mkRat_eq_div]; rw [← Rat.cast_lt (K := ℝ)]; simp
  rw [div_lt_div_iff (by simp [ha]) (by simp [hb]),
    Nat.cast_sub (le_of_lt ha), Nat.cast_sub (le_of_lt hb)]
  simp [σ, Orientation.ofReal_eq_ccw, Point.det_eq]
  rw [← sub_pos, ← sub_pos (b := _*_)]
  congr! 1; ring

def toSet (pts : Fin n → NPoint) : Set Point := Set.range (pts ·)

section
variable [MaybeHoles] {n : Nat} (p : NPoint) (pts : Fin n → NPoint) (hole : MaybeHoles.holes)

structure WFPoints : Prop where
  lt : p.1 < (pts i).1
  ccw : i < j → σ p (pts i) (pts j) = .ccw
  gp : i < j → j < k → Point.InGenPos₃ (pts i) (pts j) (pts k)

def Visible (i j : Fin n) :=
  i < j ∧ (MaybeHoles.holes → σIsEmptyTriangleFor p (pts i) (pts j) (toSet pts))

inductive CCWChain : Fin n → Fin n → List (Fin n) → Prop
  | nil : Visible p pts i j → CCWChain i j []
  | cons : Visible p pts i j → σ (pts i) (pts j) (pts k) = .ccw →
    CCWChain j k is → CCWChain i j (k::is)

variable {p pts} in
theorem CCWChain.head : CCWChain p pts i j is → Visible p pts i j
  | .nil h | .cons h .. => h

variable {p pts} in
theorem CCWChain.lt₂ : CCWChain p pts i j is → k ∈ is → j < k
  | .cons _ _ h3, hk =>
    match hk with
    | .head _ => h3.head.1
    | .tail _ hk => h3.head.1.trans (h3.lt₂ hk)

variable (wf : WFPoints p pts)

noncomputable def ptsProject (i : Fin n) : Point :=
  projectiveMap (ptTransform (translationMatrix (-p.1) (-p.2)) (pts i))

namespace WFPoints
variable {p pts}

theorem ccw_iff : σ p (pts i) (pts j) = .ccw ↔ i < j := by
  obtain h | rfl | h := lt_trichotomy i j <;> simp [*, wf.ccw, σ_self₁, lt_asymm]
  rw [σ_perm₂]; simp [wf.ccw h]

theorem translate_pos (i) :
    0 < (ptTransform (translationMatrix (-p.1) (-p.2)) (pts i)).x := by
  simp [translation_translates]; exact wf.lt

theorem ptsProject_ccw (ij : i < j) : (ptsProject p pts i).x < (ptsProject p pts j).x := by
  simpa [orientWithInfty, Orientation.ofReal_eq_ccw] using
    (Eq.trans (by congr; rw [translation_translates]; ext <;> simp) <|
      orientWithInfty_preserved (wf.translate_pos i) (wf.translate_pos j))
    |>.symm.trans <|
    ((translationTransform ..).ptTransform_preserves_sigma ..).trans (wf.ccw ij)

theorem ptsProject_σ (i j k) :
    σ (ptsProject p pts i) (ptsProject p pts j) (ptsProject p pts k) =
    σ (pts i) (pts j) (pts k) := by
  simp [ptsProject, ← orientations_preserved,
      wf.translate_pos, (translationTransform ..).ptTransform_preserves_sigma]

theorem ptsProject_gp (ij : i < j) (jk : j < k) :
    Point.InGenPos₃ (ptsProject p pts i) (ptsProject p pts j) (ptsProject p pts k) := by
  simpa [wf.ptsProject_σ, Point.InGenPos₃.iff_ne_collinear] using wf.gp ij jk

theorem ptsProject_gp₄ (ij : i < j) (jk : j < k) (kl : k < l) :
    Point.InGenPos₄ (ptsProject p pts i) (ptsProject p pts j)
      (ptsProject p pts k) (ptsProject p pts l) where
  gp₁ := wf.ptsProject_gp ij jk
  gp₂ := wf.ptsProject_gp ij (jk.trans kl)
  gp₃ := wf.ptsProject_gp (ij.trans jk) kl
  gp₄ := wf.ptsProject_gp jk kl

theorem gp₀ (ij : i < j) : Point.InGenPos₃ p (pts i) (pts j) :=
  Point.InGenPos₃.iff_ne_collinear.2 <| wf.ccw ij ▸ by decide

theorem gp₀₄ (ij : i < j) (jk : j < k) : Point.InGenPos₄ p (pts i) (pts j) (pts k) where
  gp₁ := wf.gp₀ ij
  gp₂ := wf.gp₀ (ij.trans jk)
  gp₃ := wf.gp₀ jk
  gp₄ := wf.gp ij jk

theorem setGP' : Point.SetInGenPos (insert ↑p (toSet pts)) := by
  convert Point.ListInGenPos.toFinset (l := p :: (List.finRange n).map (pts ·)) ?_
  · ext; simp [toSet]
  · intro a b c h
    match a, h with
    | a, .cons _ h =>
      match a, b, c, sublist_map.1 h with | _, _, _, ⟨[a,b,c], rfl, h⟩ => ?_
      have := (List.pairwise_lt_finRange _).sublist h; simp only [pairwise_cons] at this
      exact wf.gp (this.1 _ (.head _)) (this.2.1 _ (.head _))
    | _, .cons₂ _ h =>
      match b, c, sublist_map.1 h with | _, _, ⟨[b,c], rfl, h⟩ => ?_
      have := (List.pairwise_lt_finRange _).sublist h; simp only [pairwise_cons] at this
      exact wf.gp₀ (this.1 _ (.head _))

nonrec theorem σ_prop₁ (ab : a < b) (bc : b < c) (cd : c < d)
    (h1 : σ (pts a) (pts b) (pts c) = .ccw) (h2 : σ (pts b) (pts c) (pts d) = .ccw) :
    σ (pts a) (pts c) (pts d) = .ccw := by
  rw [← wf.ptsProject_σ] at h1 h2 ⊢
  exact σ_prop₁ ⟨⟨wf.ptsProject_ccw ab, wf.ptsProject_ccw bc⟩, wf.ptsProject_ccw cd⟩
    (wf.ptsProject_gp₄ ab bc cd) h1 h2

nonrec theorem σ_prop₁' (ab : a < b) (bc : b < c) (cd : c < d)
    (h1 : σ (pts a) (pts b) (pts c) = .ccw) (h2 : σ (pts b) (pts c) (pts d) = .ccw) :
    σ (pts a) (pts b) (pts d) = .ccw := by
  rw [← wf.ptsProject_σ] at h1 h2 ⊢
  exact σ_prop₁' ⟨⟨wf.ptsProject_ccw ab, wf.ptsProject_ccw bc⟩, wf.ptsProject_ccw cd⟩
    (wf.ptsProject_gp₄ ab bc cd) h1 h2

nonrec theorem σ_prop₃' (ab : a < b) (bc : b < c) (cd : c < d)
    (h1 : σ (pts a) (pts b) (pts c) ≠ .ccw) (h2 : σ (pts b) (pts c) (pts d) ≠ .ccw) :
    σ (pts a) (pts b) (pts d) ≠ .ccw := by
  simp only [(wf.gp ab bc).σ_iff, (wf.gp bc cd).σ_iff, (wf.gp ab (bc.trans cd)).σ_iff] at h1 h2 ⊢
  rw [← wf.ptsProject_σ] at h1 h2 ⊢
  exact σ_prop₃' ⟨⟨wf.ptsProject_ccw ab, wf.ptsProject_ccw bc⟩, wf.ptsProject_ccw cd⟩
    (wf.ptsProject_gp₄ ab bc cd) h1 h2

theorem of_visible (ab : a < b) (bc : b < c) (H : Visible p pts a c) :
    σ (pts a) (pts b) (pts c) = .ccw := by
  refine (wf.gp ab bc).σ_iff'.1 fun hn => ?_
  refine H.2 hole _ ⟨b, rfl⟩ ⟨?_, ?_, ?_⟩
  · exact (wf.ccw ab).trans (wf.ccw H.1).symm
  · exact (wf.ccw bc).trans (wf.ccw H.1).symm
  · rw [σ_perm₁, hn, wf.ccw H.1]; rfl

theorem visible_iff_σIsEmptyTriangleFor (ab : a < b) :
    Visible p pts a b ↔ σIsEmptyTriangleFor p (pts a) (pts b) (toSet pts) :=
  (and_iff_right ab).trans (imp_iff_right hole)

theorem visible_iff_σIsEmptyTriangleFor' (ab : a < b) :
    Visible p pts a b ↔ σIsEmptyTriangleFor p (pts a) (pts b) (insert ↑p (toSet pts)) :=
  (visible_iff_σIsEmptyTriangleFor hole ab).trans <|
    σIsEmptyTriangleFor_congr_right (wf.gp₀ ab) fun q h _ _ => by simp [h]

theorem visible_iff_emptyShapeIn' (ab : a < b) :
    Visible p pts a b ↔ EmptyShapeIn {↑p, ↑(pts a), ↑(pts b)} (insert ↑p (toSet pts)) :=
  have := wf.gp₀ ab
  (wf.visible_iff_σIsEmptyTriangleFor' hole ab).trans <| σIsEmptyTriangleFor_iff'' wf.setGP'
    (by simp) (by simp [toSet]) (by simp [toSet]) this.ne₁ this.ne₂ this.ne₃

theorem visible_iff_emptyShapeIn (ab : a < b) :
    Visible p pts a b ↔ EmptyShapeIn {↑p, ↑(pts a), ↑(pts b)} (toSet pts) := by
  refine (wf.visible_iff_emptyShapeIn' hole ab).trans <|
    emptyShapeIn_congr_right (by simp (config := {contextual:=true}) [not_or])

theorem visible_succ (a : Fin n) (h) : let b := ⟨a+1, h⟩; Visible p pts a b := by
  intro b; have ab : a < b := Nat.lt_succ_self _
  refine ⟨ab, fun _ => ?_⟩; rintro _ ⟨c, rfl⟩ ⟨h1, h2, -⟩
  rw [wf.ccw ab, wf.ccw_iff] at h1 h2
  exact h1.not_le <| Nat.le_of_lt_succ h2

theorem visible_trans
    (h1 : Visible p pts a b) (h2 : Visible p pts b c) (ccw : σ (pts a) (pts b) (pts c) = .ccw) :
    Visible p pts a c := by
  have ac := h1.1.trans h2.1
  refine ⟨ac, fun hole => (visible_iff_σIsEmptyTriangleFor hole ac).1 ?_⟩
  have := σCCWPoints.split_emptyShapeIn p [pts a] (pts b) [pts c] (P := toSet pts)
    (by simp [σCCWPoints, wf.ccw, h1.1, h2.1, ac, ccw])
    (by simpa using (wf.visible_iff_emptyShapeIn hole h1.1).1 h1)
    (by have := (wf.visible_iff_emptyShapeIn hole h2.1).1 h2; simp at this ⊢
        rwa [Set.pair_comm, Set.insert_comm])
  refine (wf.visible_iff_emptyShapeIn hole ac).2 ?_
  intro q ⟨hq1, hq2⟩ hq
  if eq : q = pts b then
    subst eq
    rw [σ_perm₁, ((σPtInTriangle_iff (wf.gp₀₄ h1.1 h2.1).perm₂.perm₁).2 hq).2.2,
      wf.ccw (h1.1.trans h2.1)] at ccw; cases ccw
  else
    exact this q ⟨hq1, by simp [not_or] at hq2 ⊢; simp [eq, hq2]⟩ <|
      convexHull_mono (by simp [Set.subset_def]) hq

theorem CCWChain.ccw (H : CCWChain p pts a b is) (hk : c ∈ is) :
    σ (pts a) (pts b) (pts c) = .ccw :=
  let .cons _ h2 h3 := H
  match hk with
  | .head _ => h2
  | .tail _ hk => wf.σ_prop₁' H.head.1 h3.head.1 (h3.lt₂ hk) h2 <| CCWChain.ccw h3 hk
termination_by is

theorem CCWChain.pairwise : CCWChain p pts i j is → (i::j::is).Pairwise (Visible p pts)
  | .nil h => by simp [h]
  | .cons h1 h2 h3 => by
    have H := CCWChain.pairwise h3
    refine pairwise_cons.2 ⟨forall_mem_cons.2 ⟨h1, fun k hk => ?_⟩, H⟩
    refine wf.visible_trans h1 ((pairwise_cons.1 H).1 k hk) ?_
    obtain _ | ⟨_, hk⟩ := hk
    · exact h2
    · exact CCWChain.ccw wf (.cons h1 h2 h3) (.tail _ hk)

theorem ccwChain_iff_pairwise
  (tri : ¬MaybeHoles.holes → ∀ {a b c}, a ∈ i::j::is → b ∈ i::j::is → c ∈ i::j::is →
    a < b → b < c → σ (pts a) (pts b) (pts c) = .ccw) :
  CCWChain p pts i j is ↔ (i::j::is).Pairwise (Visible p pts) := by
  refine ⟨CCWChain.pairwise wf, fun h => ?_⟩
  induction is generalizing i j with
  | nil => constructor; simpa using h
  | cons k is ih =>
    have ⟨h1, h2⟩ := pairwise_cons.1 h; simp at h1
    have jk := ((pairwise_cons.1 h2).1 _ (.head _)).1
    refine .cons h1.1 ?_ <|
      ih (fun hole a b c ha hb hc => tri hole (.tail _ ha) (.tail _ hb) (.tail _ hc)) h2
    if hole : MaybeHoles.holes then exact wf.of_visible hole h1.1.1 jk h1.2.1
    else exact tri hole (by simp) (by simp) (by simp) h1.1.1 jk

end WFPoints

inductive Queues.Ordered : (lo : Nat) → (j : Fin n) →
    (Q : (x : Fin n) → x < j → List (Fin n)) → List (Fin n) → Prop where
  | nil : lo = j.1 → Queues.Ordered lo j Q []
  | cons {i : Fin n} (h : Visible p pts i j) :
    (∀ k ∈ Q i h.1, σ (pts k) (pts i) (pts j) ≠ .ccw) →
    Queues.Ordered lo i (fun x hx => Q x (hx.trans h.1)) (Q i h.1) →
    Queues.Ordered (i+1) j Q l →
    Queues.Ordered lo j Q (i :: l)

variable {p pts} in
theorem Queues.Ordered.le : Queues.Ordered p pts lo j Q l → lo ≤ j
  | .nil eq => eq.le
  | .cons _ _ hq hl => hq.le.trans (Nat.le_of_lt hl.le)

variable {p pts} in
theorem Queues.Ordered.mem_bdd : Queues.Ordered p pts lo j Q l → a ∈ l → lo ≤ a ∧ a < j
  | .cons _ _ hq hl, .head _ => ⟨hq.le, hl.le⟩
  | .cons _ _ hq hl, .tail _ h => (hl.mem_bdd h).imp_left (Nat.le_succ_of_le hq.le).trans

variable {p pts} in
theorem Queues.Ordered.congr {Q Q'} (H : ∀ x h, lo ≤ x.1 → Q x h = Q' x h)
    (ord : Queues.Ordered p pts lo j Q l) : Queues.Ordered p pts lo j Q' l := by
  induction ord with
  | nil eq => exact .nil eq
  | cons ij h1 h2 h3 IH2 IH3 =>
    have := H _ h3.le h2.le
    exact .cons ij (this ▸ h1)
      (this ▸ IH2 fun x hx1 => H x (hx1.trans_le (Nat.le_of_lt h3.le)))
      (IH3 fun x hx1 hx2 => H x hx1 (h2.le.trans (Nat.le_of_lt hx2)))

inductive Queues.OrderedTail : (lo : Nat) → (j : Fin n) →
    (Q : (x : Fin n) → x < j → List (Fin n)) → List (Fin n) → Prop where
  | nil : Queues.OrderedTail 0 j Q []
  | cons {i : Fin n} (h : Visible p pts i j) :
    (∀ k ∈ Q i h.1, σ (pts k) (pts i) (pts j) ≠ .ccw) →
    Queues.Ordered p pts lo i (fun x hx => Q x (hx.trans h.1)) (Q i h.1) →
    Queues.OrderedTail lo j Q l →
    Queues.OrderedTail (i+1) j Q (i :: l)

theorem Queues.OrderedTail.apply
    (h1 : OrderedTail p pts lo j Q l)
    (h2 : Ordered p pts lo j Q r) : Ordered p pts 0 j Q (List.reverseAux l r) := by
  induction h1 generalizing r with
  | nil => exact h2
  | cons v o1 o2 _ ih => exact ih <| .cons v o1 o2 h2

variable {p pts} in
theorem Queues.OrderedTail.congr {Q Q'} (H : ∀ x h, x.1 < lo → Q x h = Q' x h)
    (ord : Queues.OrderedTail p pts lo j Q l) : Queues.OrderedTail p pts lo j Q' l := by
  induction ord with
  | nil => exact .nil
  | cons v h1 h2 _ ih =>
    have := H _ v.1 (Nat.lt_succ_self _)
    exact .cons v (this ▸ h1)
      (this ▸ h2.congr fun x hx1 _ => H _ _ (Nat.lt_succ_of_lt hx1))
      (ih fun x hx1 hx2 => H _ _ (hx2.trans (Nat.lt_succ.2 h2.le)))

variable {p pts} in
theorem Queues.Ordered.not_visible
    {i : Fin n} {Q} (ij : i < j)
    (hσ : ∀ k ∈ l, σ (pts k) (pts i) (pts j) ≠ .ccw)
    (H : Queues.Ordered p pts lo i Q l)
    (loa : lo ≤ a.1) (vis : Visible p pts a j) : i ≤ a := by
  induction H with
  | nil eq => subst eq; exact loa
  | @cons c Q lo l b v h1 h2 h3 ih1 ih2 =>
    let ⟨hσ1, hσ2⟩ := forall_mem_cons.1 hσ
    refine ih2 ij hσ2 (Nat.lt_of_le_of_ne (ih1 (v.1.trans ij) ?_ loa) fun ab => ?_)
    · exact fun d hd => wf.σ_prop₃' (h2.mem_bdd hd).2 v.1 ij (h1 _ hd) hσ1
    · cases Fin.eq_of_val_eq ab; exact hσ1 <| wf.of_visible hole v.1 ij vis

def MaybeHoles.graph.WF (g : MaybeHoles.graph n) (P : Fin n → Fin n → Prop) : Prop :=
  ∀ i in_ out, MaybeHoles.edges g i = (in_, out) →
    (∀ j, j ∈ in_ ↔ P j i) ∧ (∀ j, j ∈ out ↔ P i j) ∧
    in_.Pairwise (· > ·) ∧ out.Pairwise (· > ·)

def VisibilityGraph.WF (g : VisibilityGraph n) := @MaybeHoles.graph.WF .yes _ g

theorem VisibilityGraph.WF.cast {g : VisibilityGraph n}
    (H : g.WF P) (hP : ∀ i j, P i j ↔ P' i j) : g.WF P' := by
  convert ← H; ext i j; apply hP

def VisibleLT (i j i' j') := Visible p pts i' j' ∧ (j'.1 < j ∨ j'.1 = j ∧ i'.1 < i)

theorem VisibilityGraph.WF.add (vis : Visible p pts i j)
    (H : WF g (VisibleLT p pts i j)) : WF (g.add i j) (VisibleLT p pts (i + 1) j) := by
  intro k in_ out eq
  simp [VisibilityGraph.add, MaybeHoles.edges] at eq
  have := H k (g.edges[k.1]'(g.sz.symm ▸ k.2)).1 (g.edges[k.1]'(g.sz.symm ▸ k.2)).2 rfl
  iterate 2 rw [Array.getElem_modify (hj := by simp [g.sz, *])] at eq
  split at eq <;> split at eq <;> rename_i jk ik
  · cases Nat.ne_of_gt vis.1 (jk.trans ik.symm)
  · cases Fin.eq_of_val_eq jk
    cases eq; simp [this]; refine ⟨fun i' => ?_, fun j' => ?_, fun i' v => ?_⟩
    · by_cases hi : i' = i <;> simp [hi]
      · refine ⟨vis, .inr ⟨rfl, Nat.lt_succ_self _⟩⟩
      · refine and_congr_right fun _ => or_congr_right <| and_congr_right fun _ => ?_
        exact (Nat.lt_succ_iff_lt_or_eq.trans <| or_iff_left (Fin.vne_of_ne hi)).symm
    · refine and_congr_right fun _ => or_congr_right <| and_congr_right fun _ => ?_
      exact (Nat.lt_succ_iff_lt_or_eq.trans <| or_iff_left (Ne.symm ik)).symm
    · exact (v.2.resolve_left (lt_irrefl _)).2
  · cases Fin.eq_of_val_eq ik
    cases eq; simp [this]; refine ⟨fun i' => ?_, fun j' => ?_, fun i' v => ?_⟩
    · exact and_congr_right fun _ => or_congr_right <| and_congr_right (Ne.symm jk · |>.elim)
    · by_cases hj : j' = j <;> simp [hj]
      · refine ⟨vis, .inr ⟨rfl, Nat.lt_succ_self _⟩⟩
      · exact and_congr_right fun _ => or_congr_right <|
          and_congr_right (hj.elim <| Fin.eq_of_val_eq ·)
    · have := v.2
      exact v.2.resolve_right (lt_irrefl _ ·.2)
  · simp [eq] at this; simp [this]; refine ⟨fun i' => ?_, fun j' => ?_⟩
    · exact and_congr_right fun _ => or_congr_right <| and_congr_right (jk ·.symm |>.elim)
    · refine and_congr_right fun _ => or_congr_right <| and_congr_right fun _ => ?_
      exact (Nat.lt_succ_iff_lt_or_eq.trans <| or_iff_left (Ne.symm ik)).symm

def ProceedIH {i j : Fin n} (hi : i < j)
    (F : Queues n j → BelowList n j → Queues n j × BelowList n j) :=
  ∀ {{lo}} {Q : Queues n j} {Q_j : BelowList n j},
    Queues.OrderedTail p pts lo j (fun k h => Q.q[k.1]'(Q.sz ▸ h)) Q_j.1 →
    Queues.Ordered p pts lo i (fun k h => Q.q[k.1]'(Q.sz ▸ h.trans hi)) (Q.q[i.1]'(Q.sz ▸ hi)) →
    Q.graph.WF (VisibleLT p pts lo j) →
    ∀ {Q' Q_j'}, F Q Q_j = (Q', Q_j') →
    Q'.graph.WF (VisibleLT p pts (i+1) j) ∧
    (∀ (k : Fin n) (h : k < j), ¬(lo ≤ k ∧ k ≤ i) → Q'.q[k.1]'(Q'.sz ▸ h) = Q.q[k.1]'(Q.sz ▸ h)) ∧
    Queues.OrderedTail p pts (i+1) j (fun k h => Q'.q[k.1]'(Q'.sz ▸ h)) Q_j'.1

theorem of_proceed_loop
    {i j : Fin n} (ij : Visible p pts i j) {Q : Queues n j} {Q_j : BelowList n j} {Q_i} (ha)
    {IH} (hIH : ∀ a (ha : a < i), Visible p pts a j → ProceedIH p pts (ha.trans ij.1) (IH a ha))
    (Hj : Queues.OrderedTail p pts lo j (fun k h => Q.q[k.1]'(Q.sz ▸ h)) Q_j.1)
    (ord : Queues.Ordered p pts lo i (fun k h => Q.q[k.1]'(Q.sz ▸ h.trans ij.1)) Q_i)
    (g_wf : Q.graph.WF (VisibleLT p pts lo j))
    {Q' Q_j'} (eq : proceed.loop pts i j ij.1 IH Q Q_j Q_i ha = (Q', Q_j')) :
    ∃ a Q₁ Q_i₁ Q_j₁, proceed.finish i j ij.1 Q₁ Q_i₁ Q_j₁ = (Q', Q_j') ∧
      Q₁.graph.WF (VisibleLT p pts i j) ∧
      (∀ k ∈ Q_i₁.1, σ (pts k) (pts i) (pts j) ≠ .ccw) ∧
      lo ≤ a ∧ Queues.Ordered p pts a i (fun k h => Q.q[k.1]'(Q.sz ▸ h.trans ij.1)) Q_i₁.1 ∧
      (∀ (k : Fin n) (h : k < j), ¬(lo ≤ k ∧ k < a) → Q₁.q[k.1]'(Q₁.sz ▸ h) = Q.q[k.1]'(Q.sz ▸ h)) ∧
      Queues.OrderedTail p pts a j (fun k h => Q₁.q[k.1]'(Q₁.sz ▸ h)) Q_j₁.1 := by
  cases ord with
  | nil _ => subst lo; refine ⟨_, _, _, _, eq, g_wf, nofun, le_rfl, .nil rfl, fun _ _ _ => rfl, Hj⟩
  | @cons _ _ _ l a ai hσ hQi hl =>
    let ⟨_, hl'⟩ := ha
    simp (config := {iota := false}) [proceed.loop] at eq
    split at eq <;> rename_i ccw <;> rw [ccw_iff] at ccw
    · split at eq; rename_i Q₁ Q_j₁ eqIH
      obtain ⟨g₁_wf, hQQ, hQj₁⟩ := hIH _ _ (wf.visible_trans ai ij ccw) Hj hQi g_wf eqIH
      have ⟨b, Q₂, Q_i₂, Q_j₂, h1, h2, hQi₂, ab, h3, h4, h5⟩ := of_proceed_loop ij hl' hIH hQj₁
        (hl.congr fun x xi ax => (hQQ _ (xi.trans ij.1) fun ⟨_, h⟩ => h.not_lt ax).symm) g₁_wf eq
      refine ⟨_, _, _, _, h1, h2, hQi₂, hQi.le.trans (Nat.le_of_lt ab), h3.congr ?_, ?_, h5⟩
      · exact fun x xi bx => hQQ _ (xi.trans ij.1) fun ⟨_, h⟩ => (bx.trans h).not_lt ab
      · refine fun k hk hn => (h4 k hk (mt ?_ hn)).trans (hQQ _ hk (mt ?_ hn))
        · exact .imp_left fun h => hQi.le.trans (Nat.le_of_lt h)
        · exact .imp_right fun (h : k.1 ≤ _) => h.trans_lt ab
    · have hσ' : ∀ k ∈ a :: l, σ (pts k) (pts i) (pts j) ≠ .ccw := by
        refine forall_mem_cons.2 ⟨ccw, fun k hk => ?_⟩
        have ⟨ak, ki⟩ := hl.mem_bdd hk
        exact mt (wf.σ_prop₁ ak ki ij.1 (wf.of_visible hole ak ki ai)) ccw
      have hQ' := hQi.cons ai hσ hl
      refine ⟨_, _, _, _, eq, ?_, hσ', le_rfl, hQ', fun _ _ _ => rfl, Hj⟩
      convert g_wf using 1; ext i' j'
      refine and_congr_right fun ij' => or_congr_right <| and_congr_right fun jj =>
        ⟨fun ii => not_le.1 fun loi => ?_, (·.trans_le <| hQi.le.trans (Nat.le_of_lt hl.le))⟩
      cases Fin.eq_of_val_eq jj
      exact (hQ'.not_visible hole wf ij.1 hσ' loi ij').not_lt ii

theorem of_proceed {i j : Fin n} (ij : Visible p pts i j) :
    ProceedIH p pts ij.1 (proceed pts i j ij.1) := by
  intro lo Q Q_j Hj ord g_wf Q' Q_j' eq
  simp [proceed] at eq
  have ⟨a, Q₁, Q_i₁, Q_j₁, eq, g₁_wf, hQi₁', _, hQi₁, hQQ, hQj₁⟩ :=
    of_proceed_loop p pts hole wf ij _ (fun a _ v => of_proceed v) Hj ord g_wf eq
  injection eq with eqQ eqQj; subst eqQj
  constructor
  · subst Q'; exact g₁_wf.add ij
  · have {k : Fin n} (hk : k < j) : Q'.q[k.1]'(Q'.sz ▸ hk) =
      if i.1 = k.1 then Q_i₁.1 else Q₁.q[k.1]'(Q₁.sz ▸ hk) := by subst Q'; exact Array.get_set ..
    constructor
    · intro k hk hn
      rw [this hk, if_neg (mt (fun ik => ?_) hn),
        hQQ _ hk (mt (.imp_right (·.le.trans hQi₁.le)) hn)]
      cases Fin.eq_of_val_eq ik; exact ⟨ord.le, le_rfl⟩
    · refine .cons ij ?_ (this ij.1 ▸ if_pos rfl ▸ hQi₁.congr ?_) (hQj₁.congr ?_)
      · rwa [this ij.1, if_pos rfl]
      · intro x xj xa; rw [this xj, if_neg (xa.trans_le hQi₁.le).ne']
      · intro x xi xa; have xj := xi.trans ij.1
        rw [this xj, if_neg (Nat.ne_of_gt xi), hQQ _ xj fun ⟨_, h⟩ => h.not_le xa]

theorem mkVisibilityGraph_loop_wf
    {Q : Queues n (i+1)} (hi : i < n)
    (H : Queues.Ordered p pts 0 ⟨i, hi⟩
      (fun k h => Q.q[k.1]'(Q.sz ▸ Nat.lt_succ_of_lt h))
      (Q.q[i]'(Q.sz ▸ Nat.lt_succ_self _)))
    (g_wf : Q.graph.WF (VisibleLT p pts 0 (i+1))) :
    (mkVisibilityGraph.loop pts i Q).WF (Visible p pts) := by
  unfold mkVisibilityGraph.loop; dsimp (config := {iota := false}) only; split
  · split; rename_i h _ Q' Q_j' eq
    have ⟨g'_wf, _, h2⟩ := of_proceed _ _ hole wf (wf.visible_succ ..) (by exact .nil) H g_wf eq
    refine mkVisibilityGraph_loop_wf h ?_ ?_
    · have (Qj hj) (k:Nat) (hk) : (Q'.push h ⟨Qj, hj⟩).q[k]'hk =
        if h : k < Q'.q.size then Q'.q[k] else Qj := Array.get_push ..
      simp only [← Q'.sz] at this
      rw [this, dif_neg (lt_irrefl _)]
      convert h2.apply (.nil rfl) using 1; funext k hk
      rw [this, dif_pos (by exact hk)]
    · refine g'_wf.cast fun i' j' => ?_
      simp only [VisibleLT, not_lt_zero', and_false, or_false, and_congr_right_iff]
      refine fun h => .trans ?_ Nat.lt_succ_iff_lt_or_eq.symm
      exact or_congr_right <| and_iff_left_of_imp (· ▸ h.1)
  · exact g_wf.cast fun i' j' => and_iff_left <| .inl <| j'.2.trans_le (not_lt.1 ‹_›)
termination_by n - i

theorem mkVisibilityGraph_wf : (mkVisibilityGraph pts).WF (Visible p pts) := by
  unfold mkVisibilityGraph; split
  · refine mkVisibilityGraph_loop_wf p pts hole wf ‹_› (.nil rfl) (fun i in_ out eq => ?_)
    cases eq.symm.trans (List.get_replicate ..)
    simp [VisibleLT]
    suffices ∀ i j, Visible p pts i j → j.1 ≠ 0 from ⟨(this · _), this _⟩
    intro i j ⟨h, _⟩; exact ((Nat.zero_le _).trans_lt h).ne'
  · intro i; cases ‹¬_› i.pos

def LMapWF (lmap : Std.RBMap (Fin n ×ₗ Fin n) ℕ compare) (r i j) :=
  ∃ k, lmap.find? (i, j) = some (k+1) ∧ k < r ∧ ∀ is, CCWChain p pts i j is → is.length ≤ k

section

theorem of_maxChainCoreOrdered_inner
    {lmap} (H : maxChainCoreOrdered.loop.inner pts q lmap i finish out m = some lmap')
    (outss : out <+ out₀)
    (hout1 : out₀.Pairwise (· > ·))
    (hout2 : ∀ o ∈ out₀, Visible p pts q o)
    (hout : P → ∀ o is, CCWChain p pts i q (o::is) → o ∈ out ∨ is.length < m)
    (hlmap : P → ∀ i j, Visible p pts i j → q < j → LMapWF p pts lmap r i j) :
    ∃ out' m', finish out' m' = some lmap' ∧ m ≤ m' ∧ out' <+ out₀ ∧
      (∀ o ∈ out, σ (pts i) (pts q) (pts o) ≠ .ccw → o ∈ out') ∧
      (P → ∀ o is, CCWChain p pts i q (o::is) → is.length < m') := by
  match out with
  | [] =>
    simp [maxChainCoreOrdered.loop.inner] at H
    exact ⟨_, _, H, le_rfl, outss, by simp, fun hp o is h => (hout hp o is h).resolve_left nofun⟩
  | o::out =>
    have hout1' := pairwise_cons.1 (hout1.sublist outss)
    simp [maxChainCoreOrdered.loop.inner] at H; split at H <;> rename_i hccw <;> rw [ccw_iff] at hccw
    · obtain ⟨out', m', h1, h2, h3, h4, h5⟩ := by
        refine of_maxChainCoreOrdered_inner H (sublist_of_cons_sublist outss) hout1 hout2
          (fun hp o is h => ?_) hlmap
        obtain (⟨⟩ | _) | _ := hout hp _ _ h
        · refine .inr <| lt_max_of_lt_right ?_
          have .cons _ _ h := h
          have qo := h.head
          have ⟨k, h1, _, h3⟩ := hlmap hp _ _ qo qo.1
          simp [Std.RBMap.find!, h1]
          exact Nat.lt_succ_of_le (h3 _ h)
        · exact .inl ‹_›
        · exact .inr <| lt_max_of_lt_left ‹_›
      refine ⟨out', m', h1, (le_max_left ..).trans h2, h3,
        forall_mem_cons.2 ⟨fun h => (h hccw).elim, h4⟩, h5⟩
    · refine ⟨_, _, H, le_rfl, outss, fun _ h _ => h, fun hp o' is h => ?_⟩
      refine (hout hp o' is h).resolve_left fun hn => ?_
      have .cons iq ccw' qo' := h
      obtain _ | ⟨_, hn⟩ := hn <;> [exact hccw ccw'; skip]
      have o'o := hout1'.1 _ hn
      exact hccw <| wf.σ_prop₁' iq.1 qo'.head.1 o'o ccw' <|
        wf.of_visible hole qo'.head.1 o'o (hout2 _ <| outss.subset (.head _))

theorem of_maxChainCoreUnordered_inner
    {lmap} (H : maxChainCoreUnordered.inner pts q lmap i finish out m = some lmap')
    (outss : out <+ out₀)
    (hout1 : out₀.Pairwise (· > ·))
    (hout2 : ∀ o ∈ out₀, Visible p pts q o)
    (hout : ∀ o is, CCWChain p pts i q (o::is) → o ∈ out ∨ is.length < m)
    (hlmap : ∀ i j, Visible p pts i j → q < j → LMapWF p pts lmap r i j) :
    ∃ m', finish m' = some lmap' ∧ ∀ o is, CCWChain p pts i q (o::is) → is.length < m' := by
  match out with
  | [] =>
    simp [maxChainCoreUnordered.inner] at H
    exact ⟨_, H, fun o is h => (hout o is h).resolve_left nofun⟩
  | o::out =>
    simp [maxChainCoreUnordered.inner] at H
    refine of_maxChainCoreUnordered_inner H (sublist_of_cons_sublist outss) hout1 hout2
      (fun o is h => ?_) hlmap
    obtain (⟨⟩ | _) | _ := hout _ _ h
    · have .cons _ hccw h := h
      refine .inr <| if_pos ((ccw_iff ..).2 hccw) ▸ lt_max_of_lt_right ?_
      have qo := h.head
      have ⟨k, h1, _, h3⟩ := hlmap _ _ qo qo.1
      simp [Std.RBMap.find!, h1]
      exact Nat.lt_succ_of_le (h3 _ h)
    · exact .inl ‹_›
    · right; split <;> [exact lt_max_of_lt_left ‹_›; assumption]

theorem of_maxChainCoreOrdered_loop
    {lmap} (H : maxChainCoreOrdered.loop pts r q lmap in_ out m = some lmap')
    (hin1 : in_.Pairwise (· > ·))
    (hin2 : ∀ i ∈ in_, Visible p pts i q)
    (hout1 : out.Pairwise (· > ·))
    (hout2 : ∀ o ∈ out, Visible p pts q o)
    (vis : m < r → ∀ i o is, CCWChain p pts i q (o::is) →
      i ∈ in_ ∧ o ∈ out ∨ is.length < m)
    (hlmap : m < r → ∀ i j, Visible p pts i j → q < j ∨ q = j ∧ i ∉ in_ → LMapWF p pts lmap r i j) :
    m < r ∧ ∀ i j, Visible p pts i j → q ≤ j → LMapWF p pts lmap' r i j := by
  match in_ with
  | [] =>
    simp [maxChainCoreOrdered.loop] at H; obtain ⟨H, rfl⟩ := H
    exact ⟨H, fun i j v qj => hlmap H i j v <| qj.lt_or_eq.imp_right (⟨·, nofun⟩)⟩
  | i::in_ =>
    have hin1' := pairwise_cons.1 hin1
    have hin2' := forall_mem_cons.1 hin2
    simp [maxChainCoreOrdered.loop] at H
    have ⟨out', m', H, mm, ss, h1, h2⟩ :=
      of_maxChainCoreOrdered_inner p pts hole wf H (.refl _) hout1 hout2
        (fun mr o is h => (vis mr _ _ _ h).imp_left (·.2))
        (fun mr i j v h => hlmap mr i j v (.inl h))
    refine of_maxChainCoreOrdered_loop H hin1'.2 hin2'.2 (hout1.sublist ss)
      (fun _ h => hout2 _ (ss.subset h)) ?_ ?_ |>.imp_left (mm.trans_lt)
    · intro m'r i' o is h
      have mr := mm.trans_lt m'r
      obtain ⟨_ | ⟨_, hi⟩, ho⟩ | h := vis mr _ _ _ h
      · exact .inr (h2 mr _ _ h)
      · refine or_iff_not_imp_right.2 fun hl => ⟨hi, ?_⟩
        refine h1 _ ho fun hn => ?_
        let .cons _ _ h := h
        exact hl <| h2 mr _ _ <| .cons hin2'.1 hn h
      · exact .inr (h.trans_le mm)
    · intro m'r i' j' v qj
      have mr := mm.trans_lt m'r
      refine if qj' : _ then let ⟨k, h1, h2⟩ := hlmap mr i' j' v qj'; ⟨k, ?_, h2⟩ else ?_
      · rw [Std.RBMap.find?_insert, if_neg, h1]
        rw [lex_compare_eq_iff]; rintro ⟨⟩
        exact (qj'.resolve_left (lt_irrefl _)).2 (.head _)
      · obtain ⟨rfl, hi⟩ := qj.resolve_left (mt .inl qj')
        if eq : i' = i then ?_ else simp [eq, hi] at qj'
        subst i'
        refine ⟨_, ?_, m'r, fun is pw => ?_⟩
        · rw [Std.RBMap.find?_insert, if_pos]; rw [lex_compare_eq_iff]
        · match is with
          | [] => exact Nat.zero_le _
          | o :: is => exact h2 mr o is pw

theorem of_maxChainCoreUnordered
    {lmap} (H : maxChainCoreUnordered pts r q lmap in_ out = some lmap')
    (hin1 : in_.Pairwise (· > ·))
    (hin2 : ∀ i ∈ in_, Visible p pts i q)
    (hout1 : out.Pairwise (· > ·))
    (hout2 : ∀ o, o ∈ out ↔ Visible p pts q o)
    (hlmap : ∀ i j, Visible p pts i j → q < j ∨ q = j ∧ i ∉ in_ → LMapWF p pts lmap r i j) :
    ∀ i j, Visible p pts i j → q ≤ j → LMapWF p pts lmap' r i j := by
  match in_ with
  | [] =>
    simp [maxChainCoreUnordered] at H; obtain ⟨H, rfl⟩ := H
    exact fun i j v qj => hlmap i j v <| qj.lt_or_eq.imp_right (⟨·, nofun⟩)
  | i::in_ =>
    have hin1' := pairwise_cons.1 hin1
    have hin2' := forall_mem_cons.1 hin2
    simp [maxChainCoreUnordered] at H
    have ⟨m', H, h1⟩ :=
      of_maxChainCoreUnordered_inner p pts H (.refl _) hout1 (fun _ => (hout2 _).1)
        (fun o is h => have .cons _ _ h := h; .inl <| (hout2 _).2 h.head)
        (fun i j v h => hlmap i j v (.inl h))
    simp at H; let ⟨m'r, H⟩ := H
    refine of_maxChainCoreUnordered H hin1'.2 hin2'.2 hout1 hout2 fun i' j' v qj =>
      if qj' : _ then let ⟨k, h1, h2⟩ := hlmap i' j' v qj'; ⟨k, ?_, h2⟩ else ?_
    · rw [Std.RBMap.find?_insert, if_neg, h1]
      rw [lex_compare_eq_iff]; rintro ⟨⟩
      exact (qj'.resolve_left (lt_irrefl _)).2 (.head _)
    · obtain ⟨rfl, hi⟩ := qj.resolve_left (mt .inl qj')
      if eq : i' = i then ?_ else simp [eq, hi] at qj'
      subst i'
      refine ⟨_, ?_, m'r, fun is pw => ?_⟩
      · rw [Std.RBMap.find?_insert, if_pos]; rw [lex_compare_eq_iff]
      · match is with
        | [] => exact Nat.zero_le _
        | o :: is => exact h1 o is pw

variable {graph : MaybeHoles.graph n} (g_wf : graph.WF (Visible p pts)) in
theorem of_maxChain
    {lmap hq} (H : maxChain pts r graph lmap q hq = some ())
    (hlmap : ∀ i j, Visible p pts i j → q ≤ j → LMapWF p pts lmap r i j) :
    ∀ a b is, CCWChain p pts a b is → is.length < r := by
  clear hole
  match q with
  | 0 =>
    intro a b is his
    refine not_le.1 fun h => ?_
    have ⟨k, _, kr, hk⟩ := hlmap _ _ his.head (Nat.zero_le _)
    exact ((hk is his).trans_lt kr).not_le h
  | q+1 =>
    rw [maxChain] at H; split at H; rename_i in_ out eq; simp at H
    have ⟨hin2, hout2, hin1, hout1⟩ := g_wf ⟨q, hq⟩ _ _ eq
    split at H <;> rename_i hole <;>
      simp at H <;> refine let ⟨lmap', H1, H2⟩ := H; of_maxChain H2 ?_
    · simp [maxChainCoreOrdered] at H1; split at H1
      · cases H1; refine fun i j v qj => hlmap i j v <| lt_of_le_of_ne qj fun qj => ?_
        subst q; simpa using (hin2 _).2 v
      · refine (of_maxChainCoreOrdered_loop p pts hole wf H1 hin1
              (fun j => (hin2 j).1) hout1 (fun j => (hout2 j).1) ?_ ?_).2
        · refine fun _ i o is h => .inl ?_
          have .cons h1 _ h3 := h
          exact ⟨(hin2 _).2 h1, (hout2 _).2 h3.head⟩
        · exact fun _ i j v qj => hlmap i j v (qj.resolve_right fun ⟨rfl, h2⟩ => h2 ((hin2 _).2 v))
    · exact of_maxChainCoreUnordered p pts H1 hin1 (fun j => (hin2 j).1) hout1 hout2 fun i j v qj =>
        hlmap i j v (qj.resolve_right fun ⟨rfl, h2⟩ => h2 ((hin2 _).2 v))

end

structure MaybeHoles.WF : Prop where
  mkGraph_wf {p n} {pts : Fin n → NPoint} (wf : WFPoints p pts) :
    (MaybeHoles.mkGraph pts).WF (Visible p pts)

variable (hwf : MaybeHoles.WF)

theorem of_holeCheck {pts} (H : holeCheck r pts lo = some ()) :
    (pts.map (·.1)).Chain (· < ·) lo ∧
    Point.ListInGenPos (↑'pts) ∧
    ¬σHasEmptyKGonIf (r+3) MaybeHoles.holes {x | ∃ a ∈ pts, ↑a = x} := by
  clear hole
  induction pts generalizing lo with
  | nil =>
    simp [Point.ListInGenPos]; rw [σHasEmptyKGonIf_def]
    rintro ⟨x, h1, h2, -⟩
    cases (Finset.subset_empty (s := x)).1 (by simpa using h2 : ∀ s ∈ x, s ∈ ∅)
    cases h1
  | cons p pts IH =>
    revert H; rw [holeCheck]; lift_lets; intro slope sorted sorted' n graph
    simp (config := {zeta := false}); intro h1 h2 () h3 h4
    have ⟨h5, h6, h7⟩ := IH h4
    have perm : sorted ~ pts := perm_mergeSort ..
    have h5' : ∀ a ∈ sorted, p.1 < a.1 := fun a ha =>
      (pairwise_cons.1 (pairwise_map.1 h5.pairwise)).1 _ (perm.mem_iff.1 ha)
    have sccw : sorted.Pairwise (fun a b : NPoint => σ p a b = .ccw) := by
      have : IsTotal NPoint (slope · ≤ slope ·) := ⟨fun _ _ => le_total ..⟩
      have : IsTrans NPoint (slope · ≤ slope ·) := ⟨fun _ _ _ => le_trans⟩
      have : IsTrans NPoint (slope · < slope ·) := ⟨fun _ _ _ => lt_trans⟩
      have := chain'_iff_pairwise.1 <|
        (sorted_mergeSort ..).chain'.imp₂ (fun _ _ => lt_of_le_of_ne) h2
      refine this.imp_of_mem fun {a b} ha hb h => (slope_lt (h5' _ ha) (h5' _ hb)).1 h
    have gp : (↑'pts).Pairwise (Point.InGenPos₃ p) := by
      refine pairwise_map.2 <| (sccw.imp fun h => ?_).perm perm Point.InGenPos₃.perm₂
      rw [Point.InGenPos₃.iff_ne_collinear, h]; decide
    refine ⟨⟨h1, h5⟩, fun a b c h => ?_, ?_⟩
    · cases h with
      | cons _ h => exact h6 h
      | cons₂ _ h => exact pairwise_iff_forall_sublist.1 gp h
    · rw [σHasEmptyKGonIf_def]; rintro ⟨S, eq, ss, hS⟩
      if hp : ↑p ∈ S then ?_ else
        refine h7 <| σHasEmptyKGonIf_def.2
          ⟨S, eq, fun x hx => (ss hx).resolve_left (hp <| · ▸ hx), ?_⟩
        refine fun _ ha _ hb _ hc ab ac bc q hq => hS _ ha _ hb _ hc ab ac bc _ ?_
        revert hq; split <;> [exact .inr; exact id]
      obtain ⟨l, hl1, hl2, rfl⟩ :
          ∃ l, l <+ sorted ∧ l.length = r + 2 ∧ S = (↑'(p :: l)).toFinset := by
        let f : NPoint ↪ Point := ⟨NPoint.toPoint, fun _ _ => toPoint_inj⟩
        have ⟨u, hu, hs⟩ : ∃ u ⊆ pts.toFinset, S.erase ↑p = u.map f := by
          refine Finset.subset_map_iff.1 fun x => ?_
          simp; exact fun h1 h2 => (ss h2).resolve_left (Ne.symm h1)
        obtain ⟨l, nd, rfl⟩ := u.exists_list_nodup_eq
        have := subperm_of_subset nd (by simpa [Finset.subset_def, subset_def] using hu)
        have ⟨l', lp, ls⟩ := perm.subperm_left.2 this
        refine ⟨l', ls, ?_, ?_⟩
        · rw [lp.length_eq, ← toFinset_card_of_nodup nd, ← Finset.card_map,
            ← hs, Finset.card_erase_of_mem hp, eq]; rfl
        · ext x; by_cases xp : x = p <;> simp [xp, hp]
          simpa [xp, lp.mem_iff] using congrArg (x ∈ ·) hs
      let n' := sorted.length
      let pts' : Fin n' → NPoint := sorted.get
      have gp {i j k} (ij : i < j) (jk : j < k) : Point.InGenPos₃ (pts' i) (pts' j) (pts' k) := by
        have := List.map_get_sublist (is := [i, j, k]) <| show Pairwise (· < ·) _ from
          chain_iff_pairwise.1 <| .cons ij <| .cons jk .nil
        exact Point.ListInGenPos.subperm.1 h6 <| (perm.map _).subperm_left.1 (this.map _).subperm
      let graph' := MaybeHoles.mkGraph pts'
      replace h3 : maxChain pts' r graph' ∅ n' (Nat.le_refl n') = some () := h3
      obtain ⟨is : List (Fin n'), rfl : _ = map pts' is, iss : is.Sorted (·<·)⟩ :=
        List.sublist_eq_map_get hl1
      have sccw' : ∀ a b, a < b → σ p (pts' a) (pts' b) = .ccw := pairwise_iff_get.1 sccw
      have lt i : p.1 < (pts' i).1 := h5' _ (get_mem ..)
      have h5 i : p.toPoint ≠ pts' i :=
        mt toPoint_inj <| mt (congrArg (·.1)) (h5' _ (get_mem ..)).ne
      have mem {x} : x ∈ toSet pts' ↔ ∃ a ∈ pts, a.toPoint = x := by
        simp (config := {zeta := false}) only [← perm.mem_iff]
        simp only [toSet, Set.mem_range, mem_iff_get, exists_exists_eq_and]
      clear_value pts' n'
      have wf : WFPoints p pts' := { lt := @lt, ccw := @sccw', gp := gp }
      have iss' : is.Pairwise (Visible p pts') := by
        refine iss.imp_of_mem fun {a b} ha hb h => ?_
        have hS := hS p (by simp)
          (pts' a) (by simpa using .inr ⟨_, ha, rfl⟩)
          (pts' b) (by simpa using .inr ⟨_, hb, rfl⟩)
          (h5 _) (h5 _) (wf.gp₀ h).ne₃
        refine ⟨h, fun hole c hc => hS c ?_⟩
        simpa [hole] using .inr <| mem.1 hc
        -- · refine ⟨h, hole.elim, fun c ac cb => ?_⟩
        --   have := hS (pts' c) (.inr ⟨_, c, rfl⟩) -- c ?_ -- (by simpa [hole] using .inr <| mem.1 hc)
        --   stop sorry
      have tri (hole : ¬MaybeHoles.holes) {a b c} (ha : a ∈ is) (hb : b ∈ is) (hc : c ∈ is)
          (ab : a < b) (bc : b < c) : σ (pts' a) (pts' b) (pts' c) = .ccw := by
        have gp := wf.gp ab bc
        refine gp.σ_iff'.1 fun hn => ?_
        refine hS p (by simp)
          (pts' a) (by simpa using .inr ⟨_, ha, rfl⟩)
          (pts' c) (by simpa using .inr ⟨_, hc, rfl⟩)
          (h5 _) (h5 _) gp.ne₂
          (pts' b) (by simpa [hole] using .inr ⟨_, hb, rfl⟩) ⟨?_, ?_, ?_⟩
        · exact (wf.ccw ab).trans (wf.ccw (ab.trans bc)).symm
        · exact (wf.ccw bc).trans (wf.ccw (ab.trans bc)).symm
        · rw [σ_perm₁, hn, wf.ccw (ab.trans bc)]; rfl
      let a::b::is := is
      have iss' : CCWChain p pts' a b is := (wf.ccwChain_iff_pairwise tri).2 iss'
      refine (of_maxChain p pts' wf (hwf.mkGraph_wf wf) h3
        (fun _ j _ h => nomatch h.not_lt j.2) _ _ _ iss').ne ?_
      · simpa using hl2

theorem of_holeCheck' {pts} (H : holeCheck r pts lo = some ()) :
    (↑'pts).Nodup ∧ Point.ListInGenPos (↑'pts) ∧
    ¬σHasEmptyKGonIf (r+3) MaybeHoles.holes (↑'pts).toFinset := by
  let ⟨H1, H2, H3⟩ := of_holeCheck hwf H
  have := pairwise_map.1 <| chain'_iff_pairwise.1 (List.chain'_cons'.1 H1).2
  refine ⟨pairwise_map.2 <| this.imp fun h1 h2 => ?_, H2, by convert H3 using 2; ext; simp⟩
  cases toPoint_inj h2; exact lt_irrefl _ h1

end

theorem MaybeHoles.yes_wf : MaybeHoles.yes.WF where
  mkGraph_wf := mkVisibilityGraph_wf _ _ rfl

attribute [local instance] MaybeHoles.no in
theorem MaybeHoles.no_wf : MaybeHoles.no.WF where
  mkGraph_wf {p n pts} _ k in_ out eq := by
    simp [edges, mkGraph, tail_drop] at eq; simp [← eq]
    refine ⟨fun j' => ?_, fun j' => ?_,  ?_, ?_⟩
    · simp [mem_iff_get?, Visible]
      refine ⟨fun ⟨a, ha⟩ => ?_, fun h => ⟨j', ?_⟩⟩
      · cases le_or_lt k.1 a with
        | inl h => simp [get?_eq_none.2 ((length_take_le ..).trans h)] at ha
        | inr h => simp [get?_take h, get?_eq_some] at ha; obtain ⟨_, rfl⟩ := ha; assumption
      · simp [get?_take h, get?_eq_some]
    · simp [mem_iff_get?, get?_drop, get?_eq_some, Visible]
      refine ⟨fun ⟨a, _, h⟩ => h ▸ Nat.le_add_right .., fun h : k.1 + 1 ≤ j' => ?_⟩
      have := Nat.add_sub_cancel' h
      exact ⟨j'-(k+1), this.symm ▸ j'.2, Fin.eq_of_val_eq this⟩
    · exact pairwise_reverse.2 <| (List.pairwise_lt_finRange _).sublist (take_sublist ..)
    · exact pairwise_reverse.2 <| (List.pairwise_lt_finRange _).sublist (drop_sublist ..)

attribute [local instance] MaybeHoles.no in
theorem gon_lower_bound {r : Nat} (points : List NPoint)
    (checkIt : (holeCheck r points 0).isSome = true := by native_decide) :
    points.length + 1 ≤ gonNumber (r+3) := by
  let ⟨(), eq⟩ := Option.isSome_iff_exists.1 checkIt
  let ⟨H1, H2, H3⟩ := of_holeCheck' MaybeHoles.no_wf eq
  simpa using gonNumber_lower_bound (↑'points) H1 H2 (mt (σHasConvexKGon_iff_HasConvexKGon H2).2 H3)

theorem hole_lower_bound {r : Nat} (points : List NPoint)
    (checkIt : (holeCheck r points 0).isSome = true := by native_decide) :
    points.length + 1 ≤ holeNumber (r+3) := by
  let ⟨(), eq⟩ := Option.isSome_iff_exists.1 checkIt
  let ⟨H1, H2, H3⟩ := of_holeCheck' MaybeHoles.yes_wf eq
  simpa using holeNumber_lower_bound (↑'points) H1 H2 (mt (σHasEmptyKGon_iff_HasEmptyKGon H2).2 H3)
