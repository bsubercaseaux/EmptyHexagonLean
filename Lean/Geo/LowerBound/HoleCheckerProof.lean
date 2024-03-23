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

def Visible (p : NPoint) (pts : Fin n → NPoint) (i j : Fin n) :=
  σIsEmptyTriangleFor p (pts i) (pts j) (toSet pts)

theorem of_holeCheck (H : holeCheck r pts lo = some ()) :
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
    have sccw : sorted.Pairwise (fun a b : NPoint => σ p a b = .ccw) := by
      have : IsTotal NPoint (slope · ≤ slope ·) := ⟨fun _ _ => le_total ..⟩
      have : IsTrans NPoint (slope · ≤ slope ·) := ⟨fun _ _ _ => le_trans⟩
      have : IsTrans NPoint (slope · < slope ·) := ⟨fun _ _ _ => lt_trans⟩
      have := chain'_iff_pairwise.1 <|
        (sorted_mergeSort ..).chain'.imp₂ (fun _ _ => lt_of_le_of_ne) h2
      have h5 := (pairwise_cons.1 (pairwise_map.1 h5.pairwise)).1
      refine this.imp_of_mem fun {a b} ha hb h => ?_
      have ha := h5 _ <| perm.mem_iff.1 ha
      have hb := h5 _ <| perm.mem_iff.1 hb
      exact (slope_lt ha hb).1 h
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
      sorry


theorem holeCheck_points : (holeCheck (6-3) points 0).isSome = true := by native_decide

theorem hole_6_lower_bound : ∃ (pts : List Point),
    Point.ListInGenPos pts ∧ pts.length = 29 ∧ ¬HasEmptyKGon 6 pts.toFinset :=
  let ⟨(), eq⟩ := Option.isSome_iff_exists.1 holeCheck_points
  let ⟨_, H1, H2⟩ := of_holeCheck eq
  ⟨↑'points, H1, rfl, mt (σHasEmptyKGon_iff_HasEmptyKGon H1).2 (by convert H2 using 2; ext; simp)⟩
