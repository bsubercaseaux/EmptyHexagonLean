import Geo.Definitions.Point
import Geo.Definitions.ListLex
import Geo.Orientations

namespace Geo
open Point

/-- A well-behaved list of points: in general position, sorted by `x`,
and containing at least one point `leftmost`
such that all signotopes `σ leftmost a b`
for `leftmost < a < b` are `CCW`. -/
structure WBPoints where
  leftmost : Point
  rest : List Point
  sorted' : PointListSorted (leftmost :: rest)
  gp' : PointListInGeneralPosition (leftmost :: rest)
  oriented : rest.Pairwise (σ leftmost · · = .CCW)
  lex : σRevLex rest

namespace WBPoints
open List Finset Classical

def points (w : WBPoints) := w.leftmost :: w.rest

noncomputable def toFinset (w : WBPoints) : Finset Point := w.points.toFinset

theorem sorted (w : WBPoints) : PointListSorted w.points :=
  w.sorted'

theorem gp (w : WBPoints) : PointListInGeneralPosition w.points :=
  w.gp'

theorem nodupX (w : WBPoints) : w.points.Pairwise (·.x ≠ ·.x) :=
  Pairwise.imp ne_of_lt w.sorted

theorem nodup (w : WBPoints) : w.points.Nodup :=
  w.nodupX.imp fun hx h => by rw [h] at hx; contradiction

abbrev length (w : WBPoints) : Nat := w.points.length

instance : GetElem WBPoints Nat Point (fun w i => i < w.length) where
  getElem w i h := w.points[i]'h

theorem mem_toFinset_iff {w : WBPoints} {a : Point} :
    a ∈ w.toFinset ↔ ∃ i : Fin w.length, w[i] = a := by
  simp [GetElem.getElem, toFinset, List.mem_toFinset, List.mem_iff_get]

theorem get_mem_toFinset (w : WBPoints) (i : Fin w.length) :
    w[i] ∈ w.toFinset := mem_toFinset_iff.2 ⟨_, rfl⟩

theorem sorted_get (w : WBPoints) {i j : Fin w.length} :
    i < j → w[i].x < w[j].x := by
  intro ij
  apply List.pairwise_iff_get.mp w.sorted _ _ ij

theorem of_sorted_get (w : WBPoints) {i j : Fin w.length} :
    w[i].x < w[j].x → i < j := by
  intro wiwj
  by_contra h
  rcases lt_or_eq_of_le (not_lt.mp h) with h | h
  . have := w.sorted_get h
    linarith
  . rw [h] at wiwj
    linarith

theorem of_eqx (w : WBPoints) {i j : Fin w.length} :
    w[i].x = w[j].x → i = j := by
  intro h
  by_contra h
  rcases Ne.lt_or_lt h with h | h <;> {
    have := w.sorted_get h
    linarith
  }
