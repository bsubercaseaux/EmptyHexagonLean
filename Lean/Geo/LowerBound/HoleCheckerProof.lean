import Geo.Definitions.Structures
import Geo.Definitions.OrientationProperties
import Geo.LowerBound.HoleChecker

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
def Visible (i j : Fin n) := i < j ∧ σIsEmptyTriangleFor p (pts i) (pts j) (toSet pts)

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

def VisibilityGraph.WF (g : VisibilityGraph n) : Prop :=
  ∀ i j, Visible p pts i j → g.Mem i j

theorem mkVisibilityGraph_loop_wf
    {Q : Queues n (i+1)} (hi : i < n)
    (H : Queues.Ordered pts 0 ⟨i, hi⟩
      (fun k h => Q.q[k]'(Q.sz ▸ Nat.lt_succ_of_lt h))
      (Q.q[i]'(Q.sz ▸ Nat.lt_succ_self _))) :
    (mkVisibilityGraph.loop pts i Q).WF p pts := by
  sorry

variable
  (ord : ∀ a b, a < b → σ p (pts a) (pts b) = .ccw)
  (gp : ∀ {i j k}, i < j → j < k → Point.InGenPos₃ (pts i) (pts j) (pts k)) in
theorem mkVisibilityGraph_wf : (mkVisibilityGraph pts).WF p pts := by
  have := ord
  have := @gp
  sorry

variable {r : ℕ} {graph : VisibilityGraph n} (g_wf : graph.WF p pts) in
theorem of_maxChain
    {lmap hq} (H : maxChain pts r graph lmap q hq = some ())
    (hlmap : ∀ i j, graph.MemOut i j → q ≤ i →
      ∃ k, lmap.find? (i, j) = some (k+1) ∧ k < r ∧
        ∀ is, (i::j::is).Pairwise (Visible p pts) → is.length ≤ k) :
    ∀ is : List (Fin n), is.Pairwise (Visible p pts) → is.length < r + 2 := by
  match q with
  | 0 =>
    intro is his
    refine not_le.1 fun h => ?_
    let a::b::is := is
    have ⟨k, eq, kr, hk⟩ :=
      hlmap _ _ (g_wf _ _ <| (pairwise_cons.1 his).1 _ (.head _)).2 (Nat.zero_le _)
    exact (Nat.add_lt_add_right ((hk is his).trans_lt kr) 2).not_le h
  | q+1 =>
    sorry

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
        have := List.sublist_iff_exists_index.2
          ⟨[i, j, k], chain_iff_pairwise.1 <| .cons ij <| .cons jk .nil, rfl⟩
        exact Point.ListInGenPos.subperm.1 h6 <| (perm.map _).subperm_left.1 (this.map _).subperm
      let graph' := mkVisibilityGraph pts'
      replace h3 : maxChain pts' r graph' ∅ n' (Nat.le_refl n') = some () := h3
      obtain ⟨is : List (Fin n'), iss : is.Sorted (·<·), rfl : map pts' is = _⟩ := hl1.exists_index
      have : ∀ a b, a < b → σ p (pts' a) (pts' b) = .ccw := pairwise_iff_get.1 sccw
      have h5 i : p.toPoint ≠ pts' i :=
        mt toPoint_inj <| mt (congrArg (·.1)) (h5' _ (get_mem ..)).ne
      have mem {x} : x ∈ toSet pts' ↔ ∃ a ∈ pts, a.toPoint = x := by
        simp (config := {zeta := false}) only [← perm.mem_iff]
        simp only [toSet, Set.mem_range, mem_iff_get, exists_exists_eq_and]
      clear_value pts' n'
      refine (of_maxChain p pts' ?_ h3 (fun i _ _ h => nomatch h.not_lt i.2) is ?_).ne ?_
      · exact mkVisibilityGraph_wf p pts' this gp
      · refine iss.imp_of_mem fun {a b} ha hb h => ⟨h, fun c hc => ?_⟩
        refine hS p (by simp)
          (pts' a) (by simpa using .inr ⟨_, ha, rfl⟩)
          (pts' b) (by simpa using .inr ⟨_, hb, rfl⟩)
          (h5 _) (h5 _) (fun h' => ?_) c (.inr <| mem.1 hc)
        have := this _ _ h; rw [h', σ_self₁] at this; cases this
      · simpa using hl2

theorem holeCheck_points : (holeCheck (6-3) points 0).isSome = true := by native_decide

theorem hole_6_lower_bound : ∃ (pts : List Point),
    Point.ListInGenPos pts ∧ pts.length = 29 ∧ ¬HasEmptyKGon 6 pts.toFinset :=
  let ⟨(), eq⟩ := Option.isSome_iff_exists.1 holeCheck_points
  let ⟨_, H1, H2⟩ := of_holeCheck eq
  ⟨↑'points, H1, rfl, mt (σHasEmptyKGon_iff_HasEmptyKGon H1).2 (by convert H2 using 2; ext; simp)⟩
