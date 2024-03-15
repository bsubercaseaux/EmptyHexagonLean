import Geo.Definitions.Point
import Geo.Definitions.ListLex
import Geo.Orientations

namespace Geo
open Point

/-- A list of points in *canonical position* is:
- sorted by `x`; and
- in general position; and
- contains a `leftmost` point such that
  all signotopes `σ leftmost a b` for `leftmost < a < b` are `ccw`; and
- lexicographically smaller than its mirror image. -/
structure CanonicalPoints where
  leftmost : Point
  rest : List Point
  sorted' : (leftmost :: rest).Sorted (·.x < ·.x)
  gp' : ListInGenPos (leftmost :: rest)
  oriented : rest.Pairwise (σ leftmost · · = .ccw)
  lex : σRevLex rest

namespace CanonicalPoints
open List Finset Classical

def points (w : CanonicalPoints) := w.leftmost :: w.rest

noncomputable def toFinset (w : CanonicalPoints) : Finset Point := w.points.toFinset

theorem sorted (w : CanonicalPoints) : w.points.Sorted (·.x < ·.x) :=
  w.sorted'

theorem gp (w : CanonicalPoints) : ListInGenPos w.points :=
  w.gp'

theorem nodupX (w : CanonicalPoints) : w.points.Pairwise (·.x ≠ ·.x) :=
  Pairwise.imp ne_of_lt w.sorted

theorem nodup (w : CanonicalPoints) : w.points.Nodup :=
  w.nodupX.imp fun hx h => by rw [h] at hx; contradiction

abbrev rlen (w : CanonicalPoints) : Nat := w.rest.length

abbrev length (w : CanonicalPoints) : Nat := w.rlen + 1

instance : GetElem CanonicalPoints Nat Point (fun w i => i < w.length) where
  getElem w i h := w.points[i]'h

theorem mem_points_iff {w : CanonicalPoints} {a : Point} :
    a ∈ w.points ↔ ∃ i : Fin w.length, w[i] = a := by
  simp [GetElem.getElem, List.mem_iff_get]; rfl

theorem mem_toFinset_iff {w : CanonicalPoints} {a : Point} :
    a ∈ w.toFinset ↔ ∃ i : Fin w.length, w[i] = a := by simp [mem_points_iff, toFinset]

theorem get_mem_toFinset (w : CanonicalPoints) (i : Fin w.length) :
    w[i] ∈ w.toFinset := mem_toFinset_iff.2 ⟨_, rfl⟩

theorem sorted_get (w : CanonicalPoints) {i j : Fin w.length} :
    i < j → w[i].x < w[j].x := by
  intro ij
  apply List.pairwise_iff_get.mp w.sorted _ _ ij

theorem lt_iff (w : CanonicalPoints) {i j : Fin w.length} :
    w[i].x < w[j].x ↔ i < j := by
  refine ⟨fun wiwj => ?_, w.sorted_get⟩
  by_contra h
  rcases lt_or_eq_of_le (not_lt.mp h) with h | h
  . have := w.sorted_get h
    linarith
  . rw [h] at wiwj
    linarith

theorem le_iff (w : CanonicalPoints) {i j : Fin w.length} :
    w[i].x ≤ w[j].x ↔ i ≤ j := by simpa using not_congr w.lt_iff

theorem eq_iff (w : CanonicalPoints) {i j : Fin w.length} :
    w[i].x = w[j].x ↔ i = j := by simp [le_antisymm_iff, -getElem_fin, w.le_iff]

theorem eq_iff' (w : CanonicalPoints) {i j : Fin w.length} :
    w[i] = w[j] ↔ i = j := ⟨fun h => w.eq_iff.1 (h ▸ rfl), congrArg _⟩

theorem sublist_of_chain (w : CanonicalPoints) {l : List (Fin w.length)} (hl : Chain' (· < ·) l) :
    l.map (w[·]) <+ w.points :=
  have : IsTrans (Fin w.points.length) (↑· < ↑·) := ⟨fun _ _ _ => Nat.lt_trans⟩
  map_get_sublist (l := w.points) (chain'_iff_pairwise.1 hl)

theorem sublist (w : CanonicalPoints) {i j k : Fin w.length} (ij : i < j) (jk : j < k) :
    [w[i], w[j], w[k]] <+ w.points := sublist_of_chain w <| .cons ij <| .cons jk <| .nil

theorem subset_map (w : CanonicalPoints) (l : List (Fin w.length)) :
    l.map (w[·]) ⊆ w.points := by simp [List.subset_def, mem_points_iff]

scoped macro:1200 w:term:max noWs "+[" a:term "]" : term => `($w[$(a).succ])

theorem subset_map' (w : CanonicalPoints) (l : List (Fin w.rlen)) : l.map (w+[·]) ⊆ w.points := by
  simp [List.subset_def, mem_points_iff]; exact fun i _ => ⟨i.succ, rfl⟩

theorem σ_0 (w : CanonicalPoints) {i j : Fin w.rlen}
    (ij : i < j) : σ w[0] w+[i] w+[j] = .ccw := by
  exact pairwise_iff_get.1 w.oriented i j ij

theorem gp₃ (w : CanonicalPoints) {i j k : Fin w.length} (ij : i < j) (jk : j < k) :
    InGenPos₃ w[i] w[j] w[k] := w.gp <| w.sublist ij jk

theorem gp₄ (w : CanonicalPoints) {i j k l : Fin w.length} (ij : i < j) (jk : j < k) (kl : k < l) :
    InGenPos₄ w[i] w[j] w[k] w[l] :=
  ⟨w.gp₃ ij jk, w.gp₃ ij (jk.trans kl), w.gp₃ (ij.trans jk) kl, w.gp₃ jk kl⟩

theorem sorted₃ (w : CanonicalPoints) {i j k : Fin w.length} (ij : i < j) (jk : j < k) :
    Sorted₃ w[i] w[j] w[k] := ⟨w.lt_iff.2 ij, w.lt_iff.2 jk⟩

theorem sorted₄ (w : CanonicalPoints) {i j k l : Fin w.length} (ij : i < j) (jk : j < k) (kl : k < l) :
    Sorted₄ w[i] w[j] w[k] w[l] := ⟨w.sorted₃ ij jk, w.lt_iff.2 kl⟩

alias _root_.LT.lt.succ₂ := Nat.succ_lt_succ -- HACK

theorem sorted₃' (w : CanonicalPoints) {i j k : Fin w.rlen} (ij : i < j) (jk : j < k) :
    Sorted₃ w+[i] w+[j] w+[k] := w.sorted₃ ij.succ₂ jk.succ₂

theorem sorted₄' (w : CanonicalPoints) {i j k l : Fin w.rlen} (ij : i < j) (jk : j < k) (kl : k < l) :
    Sorted₄ w+[i] w+[j] w+[k] w+[l] := w.sorted₄ ij.succ₂ jk.succ₂ kl.succ₂

theorem gp₃' (w : CanonicalPoints) {i j k : Fin w.rlen} (ij : i < j) (jk : j < k) :
    InGenPos₃ w+[i] w+[j] w+[k] := w.gp₃ ij.succ₂ jk.succ₂

theorem gp₄' (w : CanonicalPoints) {i j k l : Fin w.rlen} (ij : i < j) (jk : j < k) (kl : k < l) :
    InGenPos₄ w+[i] w+[j] w+[k] w+[l] := w.gp₄ ij.succ₂ jk.succ₂ kl.succ₂
