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

lemma Forced6Gon17 : ForcedKGon 17 6 := by
    unfold ForcedKGon
    intro pts h1 h2
    apply Geo.gon_6_theorem pts h2 (by aesop)

lemma lowerBound_h6 : h 6 ≥ 30 := by
  unfold h
  apply le_sInf
  by_contra H
  push_neg at H
  simp at H
  have ⟨a, fa, a_lt_30⟩ := H
  have a_le_29 : a ≤ 29 := by
    apply ENat.le_of_lt_add_one
    exact a_lt_30
  have := ForcedKHoleMono a_le_29 fa
  have x := NoForced6Hole29
  aesop

lemma upperBound_h6 : h 6 ≤ 30 := by
  unfold h
  apply sInf_le
  exact Forced6Hole30

lemma upperBound_g6 : g 6 ≤ 17 := by
  unfold g
  apply sInf_le
  exact Forced6Gon17


theorem empty_hexagon_number: h 6 = 30 := by
  exact le_antisymm upperBound_h6 lowerBound_h6 
