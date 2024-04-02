import Geo.Hexagon.TheMainTheorem
import Geo.Gon.TheMainTheorem
import Geo.LowerBound.HoleCheckerProof
import Mathlib.Data.ENat.Basic

namespace Geo
namespace HoleChecker
open Classical

def ForcedKGon (n : ENat) (k : Nat) :=
  ∀ (pts : List Point),
    pts.length ≥ n → Point.ListInGenPos pts
                   → HasConvexKGon k pts.toFinset

def ForcedKHole (n : ENat) (k : Nat) :=
  ∀ (pts : List Point),
    pts.length ≥ n → Point.ListInGenPos pts
                   → HasEmptyKGon k pts.toFinset

lemma ForcedKHoleMono {n m : ENat} {k : Nat} (h : n ≤ m) :
  ForcedKHole n k → ForcedKHole m k := by
  unfold ForcedKHole
  intro h1 pts h2 h3
  have length_h : ↑(pts.length) ≥ n := by
    apply ge_trans h2 h
  exact h1 pts length_h h3

lemma ForcedKGonMono {n m : ENat} {k : Nat} (h : n ≤ m) :
  ForcedKGon n k → ForcedKGon m k := by
  unfold ForcedKGon
  intro h1 pts h2 h3
  have length_h : ↑(pts.length) ≥ n := by
    apply ge_trans h2 h
  exact h1 pts length_h h3

noncomputable def h (k : Nat) : ENat :=
  sInf { n | ForcedKHole n k }

noncomputable def g (k : Nat) : ENat :=
  sInf { n | ForcedKGon n k }

lemma Forced6Hole30 : ForcedKHole 30 6 := by
    unfold ForcedKHole
    intro pts h1 h2
    apply Geo.hole_6_theorem pts h2 (by aesop)

lemma NoForced6Hole29 : ¬ ForcedKHole 29 6 := by
    unfold ForcedKHole
    push_neg
    have ⟨pts, gp, length29, no6hole⟩ := HoleChecker.hole_6_lower_bound
    use pts
    exact ⟨by aesop, gp, no6hole⟩

lemma NoForced6Gon16 : ¬ ForcedKGon 16 6 := by
    unfold ForcedKGon
    push_neg
    have ⟨pts, gp, length29, no6hole⟩ := HoleChecker.gon_6_lower_bound
    use pts
    exact ⟨by aesop, gp, no6hole⟩

lemma Forced6Gon17 : ForcedKGon 17 6 := by
    unfold ForcedKGon
    intro pts h1 h2
    apply Geo.gon_6_theorem pts h2 (by aesop)

lemma h_lowerBound (N k: Nat) (unforced: ¬ (ForcedKHole N k)) : h k ≥ (N + 1) := by
  unfold h
  apply le_sInf
  by_contra H
  push_neg at H; simp at H
  have ⟨a, fa, a_lt_N⟩ := H
  have a_le_N : a ≤ N := by
    apply ENat.le_of_lt_add_one
    exact a_lt_N
  have := ForcedKHoleMono a_le_N fa
  exact unforced this

lemma g_lowerBound (N k: Nat) (unforced: ¬ (ForcedKGon N k)) : g k ≥ (N + 1) := by
  unfold g
  apply le_sInf
  by_contra H
  push_neg at H; simp at H
  have ⟨a, fa, a_lt_N⟩ := H
  have a_le_N : a ≤ N := by
    apply ENat.le_of_lt_add_one
    exact a_lt_N
  have := ForcedKGonMono a_le_N fa
  exact unforced this

lemma lowerBound_h6 : h 6 ≥ 30 := by
  exact h_lowerBound 29 6 NoForced6Hole29


lemma upperBound_h6 : h 6 ≤ 30 := by
  unfold h
  apply sInf_le
  exact Forced6Hole30

lemma lowerBound_g6 : g 6 ≥ 17 := by
  exact g_lowerBound 16 6 NoForced6Gon16

lemma upperBound_g6 : g 6 ≤ 17 := by
  unfold g
  apply sInf_le
  exact Forced6Gon17

theorem empty_hexagon_number: h 6 = 30 := by
  exact le_antisymm upperBound_h6 lowerBound_h6

theorem convex_hexagon_number: g 6 = 17 := by
  exact le_antisymm upperBound_g6 lowerBound_g6

end HoleChecker

