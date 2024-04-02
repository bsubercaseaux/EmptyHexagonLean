import Geo.Canonicalization.SymmetryBreaking
-- import Geo.Hexagon.TheMainTheorem
-- import Geo.Gon.TheMainTheorem
-- import Geo.LowerBound.HoleCheckerProof
import Mathlib.Data.ENat.Basic

namespace Geo
open Classical

noncomputable def holeNumber (k : Nat) : ENat :=
  sInf { n | ∀ (pts : Finset Point), pts.card = n → Point.SetInGenPos pts → HasEmptyKGon k pts }

noncomputable def gonNumber (k : Nat) : ENat :=
  sInf { n | ∀ (pts : Finset Point), pts.card = n → Point.SetInGenPos pts → HasConvexKGon k pts }

theorem holeNumber_def' (k : Nat) : holeNumber k =
  sInf { n : ℕ∞ | ∀ (pts : List Point), pts.length = n →
    pts.Nodup → Point.ListInGenPos pts → HasEmptyKGon k pts.toFinset } := by
  unfold holeNumber; congr!
  refine ⟨fun H pts len nd gp => ?_, fun H pts len gp => ?_⟩
  · exact H _ (List.toFinset_card_of_nodup nd ▸ len) gp.toFinset
  · classical
    obtain ⟨pts, nd, rfl⟩ := List.toFinset_surj_on (Set.mem_univ pts)
    exact H _ (List.toFinset_card_of_nodup nd ▸ len) nd (gp.of_nodup nd)

theorem gonNumber_def' (k : Nat) : gonNumber k =
  sInf { n : ℕ∞ | ∀ (pts : List Point), pts.length = n →
    pts.Nodup → Point.ListInGenPos pts → HasConvexKGon k pts.toFinset } := by
  unfold gonNumber; congr!
  refine ⟨fun H pts len nd gp => ?_, fun H pts len gp => ?_⟩
  · exact H _ (List.toFinset_card_of_nodup nd ▸ len) gp.toFinset
  · classical
    obtain ⟨pts, nd, rfl⟩ := List.toFinset_surj_on (Set.mem_univ pts)
    exact H _ (List.toFinset_card_of_nodup nd ▸ len) nd (gp.of_nodup nd)

theorem holeNumber_le {n : Nat} : holeNumber k ≤ n ↔
    ∀ (pts : List Point), pts.length = n →
    pts.Nodup → Point.ListInGenPos pts → HasEmptyKGon k pts.toFinset := by
  rw [holeNumber_def']
  refine ⟨fun H => ?_, fun H => sInf_le fun pts eq => H pts (Nat.cast_inj.1 eq)⟩
  have ⟨n₀, eq, le⟩ := ENat.le_coe_iff.1 H
  rintro pts rfl nd gp
  have : (n₀ : ℕ∞) ∈ _ := by rw [← eq]; exact csInf_mem ⟨⊤, by simp⟩
  refine HasEmptyKGon_extension' gp (fun pts eq => this pts (Nat.cast_inj.2 eq)) nd le

theorem gonNumber_le {n : Nat} : gonNumber k ≤ n ↔
    ∀ (pts : List Point), pts.length = n →
    pts.Nodup → Point.ListInGenPos pts → HasConvexKGon k pts.toFinset := by
  rw [gonNumber_def']
  refine ⟨fun H => ?_, fun H => sInf_le fun pts eq => H pts (Nat.cast_inj.1 eq)⟩
  have ⟨n₀, eq, le⟩ := ENat.le_coe_iff.1 H
  rintro pts rfl nd gp
  have : (n₀ : ℕ∞) ∈ _ := by rw [← eq]; exact csInf_mem ⟨⊤, by simp⟩
  refine HasConvexKGon_extension gp (fun pts eq => this pts (Nat.cast_inj.2 eq)) nd le

theorem holeNumber_lower_bound (pts : List Point) (nd : pts.Nodup) (gp : Point.ListInGenPos pts)
    (nohole : ¬HasEmptyKGon k pts.toFinset) : pts.length + 1 ≤ holeNumber k :=
  ENat.add_one_le_of_lt <| not_le.1 <| mt (holeNumber_le.1 · _ rfl nd gp) nohole

theorem gonNumber_lower_bound (pts : List Point) (nd : pts.Nodup) (gp : Point.ListInGenPos pts)
    (nogon : ¬HasConvexKGon k pts.toFinset) : pts.length + 1 ≤ gonNumber k :=
  ENat.add_one_le_of_lt <| not_le.1 <| mt (gonNumber_le.1 · _ rfl nd gp) nogon
