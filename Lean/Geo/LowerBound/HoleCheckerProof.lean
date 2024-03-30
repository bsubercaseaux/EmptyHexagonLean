import Geo.Definitions.Structures
import Geo.Definitions.OrientationProperties
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

variable {n : Nat} (p : NPoint) (pts : Fin n → NPoint)

structure WFPoints : Prop where
  lt : p.1 < (pts i).1
  ccw : i < j → σ p (pts i) (pts j) = .ccw
  gp : i < j → j < k → Point.InGenPos₃ (pts i) (pts j) (pts k)

def Visible (i j : Fin n) := i < j ∧ σIsEmptyTriangleFor p (pts i) (pts j) (toSet pts)

variable (wf : WFPoints p pts)

noncomputable def ptsProject (i : Fin n) : Point :=
  projectiveMap (ptTransform (translationMatrix (-p.1) (-p.2)) (pts i))

namespace WFPoints
variable {p pts}

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

theorem setGP : Point.SetInGenPos (toSet pts) := wf.setGP'.mono (by simp)

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

theorem of_visible (ab : a < b) (bc : b < c) (H : Visible p pts a c) :
    σ (pts a) (pts b) (pts c) = .ccw := by
  refine (wf.gp ab bc).σ_iff'.1 fun hn => ?_
  refine H.2 _ ⟨b, rfl⟩ ⟨?_, ?_, ?_⟩
  · exact (wf.ccw ab).trans (wf.ccw H.1).symm
  · exact (wf.ccw bc).trans (wf.ccw H.1).symm
  · rw [σ_perm₁, hn, wf.ccw H.1]; rfl

theorem visible_iff_σIsEmptyTriangleFor' (ab : a < b) :
    Visible p pts a b ↔ σIsEmptyTriangleFor p (pts a) (pts b) (insert ↑p (toSet pts)) :=
  (and_iff_right ab).trans <| σIsEmptyTriangleFor_congr_right (wf.gp₀ ab) fun q h _ _ => by simp [h]

theorem visible_iff_emptyShapeIn' (ab : a < b) :
    Visible p pts a b ↔ EmptyShapeIn {↑p, ↑(pts a), ↑(pts b)} (insert ↑p (toSet pts)) :=
  have := wf.gp₀ ab
  (wf.visible_iff_σIsEmptyTriangleFor' ab).trans <| σIsEmptyTriangleFor_iff'' wf.setGP'
    (by simp) (by simp [toSet]) (by simp [toSet]) this.ne₁ this.ne₂ this.ne₃

theorem visible_iff_emptyShapeIn (ab : a < b) :
    Visible p pts a b ↔ EmptyShapeIn {↑p, ↑(pts a), ↑(pts b)} (toSet pts) := by
  refine (wf.visible_iff_emptyShapeIn' ab).trans <|
    emptyShapeIn_congr_right (by simp (config := {contextual:=true}) [not_or])

theorem visible_trans
    (h1 : Visible p pts a b) (h2 : Visible p pts b c) (ccw : σ (pts a) (pts b) (pts c) = .ccw) :
    Visible p pts a c := by
  have := σCCWPoints.split_emptyShapeIn p [pts a] (pts b) [pts c] (P := toSet pts)
    (by simp [σCCWPoints, wf.ccw, h1.1, h2.1, h1.1.trans h2.1, ccw])
    (by simpa using (wf.visible_iff_emptyShapeIn h1.1).1 h1)
    (by have := (wf.visible_iff_emptyShapeIn h2.1).1 h2; simp at this ⊢
        rwa [Set.pair_comm, Set.insert_comm])
  refine (wf.visible_iff_emptyShapeIn (h1.1.trans h2.1)).2 ?_
  intro q ⟨hq1, hq2⟩ hq
  if eq : q = pts b then
    subst eq
    rw [σ_perm₁, ((σPtInTriangle_iff (wf.gp₀₄ h1.1 h2.1).perm₂.perm₁).2 hq).2.2,
      wf.ccw (h1.1.trans h2.1)] at ccw; cases ccw
  else
    exact this q ⟨hq1, by simp [not_or] at hq2 ⊢; simp [eq, hq2]⟩ <|
      convexHull_mono (by simp [Set.subset_def]) hq

theorem visible_cons
    (h1 : Visible p pts a b)
    (h2 : σ (pts a) (pts b) (pts c) = .ccw)
    (H : (b::c::is).Pairwise (Visible p pts)) :
    (a::b::c::is).Pairwise (Visible p pts) := by
  refine pairwise_cons.2 ⟨forall_mem_cons.2 ⟨h1, forall_mem_cons.2 ?_⟩, H⟩
  simp at H
  refine ⟨wf.visible_trans h1 H.1.1 h2, fun d hd => ?_⟩
  refine wf.visible_trans h1 (H.1.2 _ hd) ?_
  have bc := H.1.1.1; have cd := (H.2.1 _ hd).1
  exact wf.σ_prop₁' h1.1 bc cd h2 <| wf.of_visible bc cd (H.1.2 _ hd)

end WFPoints

def VisibilityGraph.MemIn (g : VisibilityGraph n) (j i : Fin n) :=
  j ∈ (g.edges[i.1]'(g.sz.symm ▸ i.2)).1

def VisibilityGraph.MemOut (g : VisibilityGraph n) (i j : Fin n) :=
  j ∈ (g.edges[i.1]'(g.sz.symm ▸ i.2)).2

def VisibilityGraph.Mem (g : VisibilityGraph n) (i j : Fin n) :=
  g.MemIn i j ∧ g.MemOut i j

inductive Queues.Ordered : (lo : Nat) → (j : Fin n) →
    (Q : (x : Fin n) → x < j → List (Fin n)) → List (Fin n) → Prop where
  | nil : lo ≤ j.1 → Queues.Ordered lo j Q []
  | cons {i : Fin n} (h : i < j) :
    (∀ k ∈ Q i h, σ (pts k) (pts i) (pts j) ≠ .ccw) →
    Queues.Ordered lo i (fun x hx => Q x (hx.trans h)) (Q i h) →
    Queues.Ordered (i+1) j Q l →
    Queues.Ordered lo j Q (i :: l)

-- structure Queues.WF (Q : Queues n a) : Prop where
--   graph : ∀ i j, j.1 < a → Visible p pts i j → Q.graph.Mem i j
--   mem : ∀ (i j : Fin n) (h : i < a), j ∈ Q.q[i.1]'(Q.sz ▸ h) ↔
--     Visible p pts j i ∧ ∀ k, i < k → k < a → ¬Visible p pts j k

-- proceed i j := do
--   while Q[i] != 0 && ccw(Q[i].0, i, j) do
--     proceed Q[i].0 j
--     Q[i].dequeue
--   add i j
--   Q[j].enqueue i

--                  3
--
--
--          2
--   1
--             4          5
--
--             6
-- p               7
--
--
--                   8
--        9

--     1  2  3  4  5  6   7   8   9
-- 12     1
-- 23     1  2
--   14      2 1
--  24         12
-- 34          123
-- 45          123 4
--   16         23 4 1
--   26          3 4 12
--  46           3   124
-- 56            3   1245
-- 67            3   1245 6
--   18          3    245 6  1
--  68           3    245    16
-- 78            3    245    167
--  19           3    245     67 1
--   29          3     45     67 12
--   49          3      5     67 124
--  69           3      5      7 1246
--  79           3      5        12467
-- 89            3      5        124678

theorem of_proceed
    {i j : Fin n} {Q : Queues n j} (hi : i < j) {Q_j : BelowList n j}
    (Hj : ∀ r, Queues.Ordered pts lo j (fun k h => Q.q[k]'(Q.sz ▸ h)) r →
      Queues.Ordered pts 0 j (fun k h => Q.q[k]'(Q.sz ▸ h)) (Q_j.1.reverseAux r))
    {Q' Q_j' r} (eq : proceed pts i j hi Q Q_j = (Q', Q_j'))
    (hr : Queues.Ordered pts (i+1) j (fun k h => Q.q[k]'(Q.sz ▸ h)) r) :
    Queues.Ordered pts 0 j (fun k h => Q.q[k]'(Q.sz ▸ h)) (Q_j'.1.reverseAux r) := by
  sorry

def VisibilityGraph.WF' (g : VisibilityGraph n) (P : Fin n → Fin n → Prop) : Prop :=
  ∀ i : Fin n, ∀ in_ out, g.edges[i.1]'(g.sz.symm ▸ i.2) = (in_, out) →
    (∀ j, j ∈ in_ ↔ P j i) ∧ (∀ j, j ∈ out ↔ P i j) ∧
    in_.Pairwise (· > ·) ∧ out.Pairwise (· > ·)

def VisibilityGraph.WF (g : VisibilityGraph n) : Prop := g.WF' (Visible p pts)

theorem mkVisibilityGraph_loop_wf
    {Q : Queues n (i+1)} (hi : i < n)
    (H : Queues.Ordered pts 0 ⟨i, hi⟩
      (fun k h => Q.q[k]'(Q.sz ▸ Nat.lt_succ_of_lt h))
      (Q.q[i]'(Q.sz ▸ Nat.lt_succ_self _))) :
    (mkVisibilityGraph.loop pts i Q).WF p pts := by
  sorry

theorem mkVisibilityGraph_wf : (mkVisibilityGraph pts).WF p pts := by
  have := wf
  sorry

def LMapWF (lmap : Std.RBMap (Fin n ×ₗ Fin n) ℕ compare) (r i j) :=
  ∃ k, lmap.find? (i, j) = some (k+1) ∧ k < r ∧
    ∀ is, (i::j::is).Pairwise (Visible p pts) → is.length ≤ k

section

theorem of_maxChain_inner
    {lmap} (H : maxChain.loop.inner pts q lmap i finish out m = some lmap')
    (hout1 : out.Pairwise (· > ·))
    (hout2 : ∀ o ∈ out, Visible p pts q o)
    (hout : ∀ o is, (i::q::o::is).Pairwise (Visible p pts) → o ∈ out ∨ is.length < m)
    (hlmap : ∀ i j, Visible p pts i j → q.1 < j → LMapWF p pts lmap r i j) :
    ∃ out' m', finish out' m' = some lmap' ∧ m ≤ m' ∧ out' <+ out ∧
      (∀ o ∈ out, σ (pts i) (pts q) (pts o) ≠ .ccw → o ∈ out') ∧
      ∀ o is, (i::q::o::is).Pairwise (Visible p pts) → is.length < m' := by
  match out with
  | [] =>
    simp [maxChain.loop.inner] at H
    exact ⟨_, _, H, le_rfl, .slnil, fun., fun o is h => (hout o is h).resolve_left (fun.)⟩
  | o::out =>
    have hout1' := pairwise_cons.1 hout1
    have hout2' := forall_mem_cons.1 hout2
    simp [maxChain.loop.inner] at H; split at H
    · obtain ⟨out', m', h1, h2, h3, h4, h5⟩ := by
        refine of_maxChain_inner H hout1'.2 hout2'.2 (fun o is h => ?_) hlmap
        obtain (⟨⟩ | _) | _ := hout _ _ h
        · refine .inr <| lt_max_of_lt_right ?_
          have := (pairwise_cons.1 h).2
          have qo := (pairwise_cons.1 this).1 _ (.head _)
          have ⟨k, h1, _, h3⟩ := hlmap _ _ qo qo.1
          simp [Std.RBMap.find!, h1]
          exact Nat.lt_succ_of_le (h3 _ this)
        · exact .inl ‹_›
        · exact .inr <| lt_max_of_lt_left ‹_›
      exact ⟨out', m', h1, (le_max_left ..).trans h2, .cons _ h3,
        forall_mem_cons.2 ⟨fun h => (h (by rwa [← ccw_iff])).elim, h4⟩, h5⟩
    · next hccw =>
      refine ⟨_, _, H, le_rfl, .refl _, fun _ h _ => h, fun o' is h => ?_⟩
      refine (hout o' is h).resolve_left fun hn => ?_
      have vis := h.sublist (sublist_append_left [i,q,o'] is); simp at vis
      let ⟨⟨iq, io'⟩, qo'⟩ := vis
      have ccw' := wf.of_visible iq.1 qo'.1 io'
      rw [ccw_iff] at hccw
      obtain _ | ⟨_, hn⟩ := hn <;> [exact hccw ccw'; skip]
      have o'o := hout1'.1 _ hn
      exact hccw <| wf.σ_prop₁' iq.1 qo'.1 o'o ccw' <| wf.of_visible qo'.1 o'o hout2'.1

theorem of_maxChain_loop
    {lmap} (H : maxChain.loop pts r q lmap in_ out m = some lmap')
    (hin1 : in_.Pairwise (· > ·))
    (hin2 : ∀ i ∈ in_, Visible p pts i q)
    (hout1 : out.Pairwise (· > ·))
    (hout2 : ∀ o ∈ out, Visible p pts q o)
    (vis : ∀ i o is, (i::q::o::is).Pairwise (Visible p pts) → i ∈ in_ ∧ o ∈ out ∨ is.length < m)
    (hlmap : ∀ i j, Visible p pts i j → q.1 < j → LMapWF p pts lmap r i j) :
    m < r ∧ ∀ i j, Visible p pts i j →
      q.1 < j ∨ q.1 = j ∧ i ∈ in_ → LMapWF p pts lmap' r i j := by
  match in_ with
  | [] =>
    simp [maxChain.loop] at H; obtain ⟨H, rfl⟩ := H
    exact ⟨H, fun | _, _, v, .inl qi => hlmap _ _ v qi⟩
  | i::in_ =>
    have hin1' := pairwise_cons.1 hin1
    have hin2' := forall_mem_cons.1 hin2
    simp [maxChain.loop] at H
    have ⟨out', m', H, mm, ss, h1, h2⟩ :=
      of_maxChain_inner p pts wf H hout1 hout2 (fun o is h => (vis _ _ _ h).imp_left (·.2)) hlmap
    obtain ⟨h3, h4⟩ := by
      refine of_maxChain_loop H hin1'.2 hin2'.2 (hout1.sublist ss)
        (fun _ h => hout2 _ (ss.subset h)) ?_ ?_
      · intro i' o is h
        obtain ⟨_ | ⟨_, hi⟩, ho⟩ | h := vis _ _ _ h
        · exact .inr (h2 _ _ h)
        · refine or_iff_not_imp_right.2 fun hl => ⟨hi, h1 _ ho fun hn => ?_⟩
          exact hl <| h2 _ _ <| wf.visible_cons hin2'.1 hn (pairwise_cons.1 h).2
        · exact .inr (h.trans_le mm)
      · sorry
    sorry

variable {graph : VisibilityGraph n} (g_wf : graph.WF p pts) in
theorem of_maxChain
    {lmap hq} (H : maxChain pts r graph lmap q hq = some ())
    (hlmap : ∀ i j, Visible p pts i j → q ≤ j → LMapWF p pts lmap r i j) :
    ∀ is : List (Fin n), is.Pairwise (Visible p pts) → is.length < r + 2 := by
  match q with
  | 0 =>
    intro is his
    refine not_le.1 fun h => ?_
    let a::b::is := is
    have ⟨k, _, kr, hk⟩ :=
      hlmap _ _ ((pairwise_cons.1 his).1 _ (.head _)) (Nat.zero_le _)
    exact (Nat.add_lt_add_right ((hk is his).trans_lt kr) 2).not_le h
  | q+1 =>
    rw [maxChain] at H; split at H; rename_i in_ out eq; simp at H
    have ⟨hin2, hout2, hin1, hout1⟩ := g_wf ⟨q, hq⟩ _ _ eq
    let ⟨lmap', H1, H2⟩ := H
    rw [Array.get_eq_getElem] at eq
    refine of_maxChain H2 fun i j v qj =>
      (of_maxChain_loop p pts wf H1 hin1
        (fun j => (hin2 j).1) hout1 (fun j => (hout2 j).1) ?_ hlmap).2 _ _ v ?_
    · refine fun i o is h => .inl ?_
      simp only [pairwise_cons] at h
      exact ⟨(hin2 _).2 (h.1 _ (.head _)), (hout2 _).2 (h.2.1 _ (.head _))⟩
    · refine qj.lt_or_eq.imp_right fun qj => ⟨qj, ?_⟩
      cases Fin.eq_of_veq qj
      exact (hin2 _).2 v
end

theorem of_holeCheck {pts} (H : holeCheck r pts lo = some ()) :
    (pts.map (·.1)).Chain (· < ·) lo ∧
    Point.ListInGenPos (↑'pts) ∧
    ¬σHasEmptyKGon (r+3) {x | ∃ a ∈ pts, ↑a = x} := by
  induction pts generalizing lo with
  | nil =>
    simp [Point.ListInGenPos]
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
    · rintro ⟨S, eq, ss, hS⟩
      if hp : ↑p ∈ S then ?_ else
        refine h7 ⟨S, eq, fun x hx => (ss hx).resolve_left (hp <| · ▸ hx), ?_⟩
        exact fun  _ ha _ hb _ hc ab ac bc q hq => hS _ ha _ hb _ hc ab ac bc _ (.inr hq)
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
      let graph' := mkVisibilityGraph pts'
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
        refine iss.imp_of_mem fun {a b} ha hb h => ⟨h, fun c hc => ?_⟩
        refine hS p (by simp)
          (pts' a) (by simpa using .inr ⟨_, ha, rfl⟩)
          (pts' b) (by simpa using .inr ⟨_, hb, rfl⟩)
          (h5 _) (h5 _) (fun h' => ?_) c (.inr <| mem.1 hc)
        have := sccw' _ _ h; rw [h', σ_self₁] at this; cases this
      refine (of_maxChain p pts' wf ?_ h3 (fun _ j _ h => nomatch h.not_lt j.2) is iss').ne ?_
      · exact mkVisibilityGraph_wf p pts' wf
      · simpa using hl2

theorem holeCheck_points : (holeCheck (6-3) points 0).isSome = true := by native_decide

theorem hole_6_lower_bound : ∃ (pts : List Point),
    Point.ListInGenPos pts ∧ pts.length = 29 ∧ ¬HasEmptyKGon 6 pts.toFinset :=
  let ⟨(), eq⟩ := Option.isSome_iff_exists.1 holeCheck_points
  let ⟨_, H1, H2⟩ := of_holeCheck eq
  ⟨↑'points, H1, rfl, mt (σHasEmptyKGon_iff_HasEmptyKGon H1).2 (by convert H2 using 2; ext; simp)⟩
