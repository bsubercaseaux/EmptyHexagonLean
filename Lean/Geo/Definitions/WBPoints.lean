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

theorem mem_points_iff {w : WBPoints} {a : Point} :
    a ∈ w.points ↔ ∃ i : Fin w.length, w[i] = a := by simp [GetElem.getElem, List.mem_iff_get]

theorem mem_toFinset_iff {w : WBPoints} {a : Point} :
    a ∈ w.toFinset ↔ ∃ i : Fin w.length, w[i] = a := by simp [mem_points_iff, toFinset]

theorem get_mem_toFinset (w : WBPoints) (i : Fin w.length) :
    w[i] ∈ w.toFinset := mem_toFinset_iff.2 ⟨_, rfl⟩

theorem sorted_get (w : WBPoints) {i j : Fin w.length} :
    i < j → w[i].x < w[j].x := by
  intro ij
  apply List.pairwise_iff_get.mp w.sorted _ _ ij

theorem lt_iff (w : WBPoints) {i j : Fin w.length} :
    w[i].x < w[j].x ↔ i < j := by
  refine ⟨fun wiwj => ?_, w.sorted_get⟩
  by_contra h
  rcases lt_or_eq_of_le (not_lt.mp h) with h | h
  . have := w.sorted_get h
    linarith
  . rw [h] at wiwj
    linarith

theorem le_iff (w : WBPoints) {i j : Fin w.length} :
    w[i].x ≤ w[j].x ↔ i ≤ j := by simpa using not_congr w.lt_iff

theorem eq_iff (w : WBPoints) {i j : Fin w.length} :
    w[i].x = w[j].x ↔ i = j := by simp [le_antisymm_iff, -getElem_fin, w.le_iff]

theorem eq_iff' (w : WBPoints) {i j : Fin w.length} :
    w[i] = w[j] ↔ i = j := ⟨fun h => w.eq_iff.1 (h ▸ rfl), congrArg _⟩

theorem sublist (w : WBPoints) {i j k : Fin w.length} (ij : i < j) (jk : j < k) :
    [w[i], w[j], w[k]] <+ w.points := by
  have : [w[i], w[j], w[k]] = [i,j,k].map w.points.get := by
    simp [GetElem.getElem, List.getElem_eq_get]
  rw [this]
  apply map_get_sublist
  simp [ij, jk, ij.trans jk]

theorem σ_0 (w : WBPoints) {i j : Fin w.length}
    (i0 : (0 : Fin (w.rest.length+1)) < i) (ij : i < j) :
    σ w[(0 : Fin (w.rest.length+1))] w[i] w[j] = .CCW := by
  let ⟨i+1,hi⟩ := i
  let ⟨j+1,hj⟩ := j
  exact pairwise_iff_get.1 w.oriented
    ⟨_, Nat.lt_of_succ_lt_succ hi⟩ ⟨_, Nat.lt_of_succ_lt_succ hj⟩ (Nat.lt_of_succ_lt_succ ij)

theorem gp₃ (w : WBPoints) {i j k : Fin w.length} (ij : i < j) (jk : j < k) :
    InGeneralPosition₃ w[i] w[j] w[k] := w.gp <| w.sublist ij jk

theorem gp₄ (w : WBPoints) {i j k l : Fin w.length} (ij : i < j) (jk : j < k) (kl : k < l) :
    InGeneralPosition₄ w[i] w[j] w[k] w[l] :=
  ⟨w.gp₃ ij jk, w.gp₃ ij (jk.trans kl), w.gp₃ (ij.trans jk) kl, w.gp₃ jk kl⟩

theorem sorted₃ (w : WBPoints) {i j k : Fin w.length} (ij : i < j) (jk : j < k) :
    Sorted₃ w[i] w[j] w[k] := ⟨w.lt_iff.2 ij, w.lt_iff.2 jk⟩

theorem sorted₄ (w : WBPoints) {i j k l : Fin w.length} (ij : i < j) (jk : j < k) (kl : k < l) :
    Sorted₄ w[i] w[j] w[k] w[l] := ⟨w.sorted₃ ij jk, w.lt_iff.2 kl⟩
