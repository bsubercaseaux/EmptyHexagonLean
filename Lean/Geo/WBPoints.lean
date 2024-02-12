import LeanSAT.Model.PropFun
import Geo.Point
import Geo.Orientations
import Geo.Formula

namespace Geo

noncomputable section
open Point

theorem nodup_of_gp (l : List Point) :
    3 < l.length → PointListInGeneralPosition l → l.Nodup :=
  sorry

/-- A well-behaved list of points: in general position, sorted by `x`. -/
structure WBPoints where
  points : List Point
  sorted : PointListSorted points
  gp : PointListInGeneralPosition points
  -- ccw : SortedCCW

def finset_sort (S : Finset Point) : List Point :=
  S.toList.insertionSort (·.x <= ·.x)

theorem finset_sort_sorted (S : Finset Point) : (finset_sort S).Sorted (·.x <= ·.x) :=
  List.sorted_insertionSort (·.x <= ·.x) (S.toList)

namespace WBPoints
open List Finset Classical
open LeanSAT Model PropFun

def toFinset (w : WBPoints) : Finset Point := w.points.toFinset

def fromFinset {S : Finset Point} (hS : PointFinsetInGeneralPosition S)
    (hX : Set.Pairwise S.toSet (·.x ≠ ·.x)) : WBPoints :=
  { points := finset_sort S
    -- nodup := (Perm.nodup_iff (perm_insertionSort _ _)).mpr (Finset.nodup_toList S)
    sorted := by
      unfold PointListSorted Sorted
      rw [List.Pairwise.imp_mem]
      have := List.sorted_insertionSort (·.x ≤ ·.x) (toList S)
      unfold Sorted at this
      sorry
      done
    gp := by
      sorry
      done}

theorem nodupX (w : WBPoints) : w.points.Pairwise (·.x ≠ ·.x) :=
  Pairwise.imp ne_of_lt w.sorted

theorem nodup (w : WBPoints) : w.points.Nodup :=
  w.nodupX.imp fun hx h => by rw [h] at hx; contradiction

abbrev length (w : WBPoints) : Nat := w.points.length

instance : GetElem WBPoints Nat Point (fun w i => i < w.length) where
  getElem w i h := w.points[i]'h

def toPropAssn (w : WBPoints) : PropAssignment (Var w.length)
  | .sigma a b c ..    => σ w[a] w[b] w[c] = .CCW
  | .inside x a b c .. => decide $ σPtInTriangle w[x] w[a] w[b] w[c]
  | .hole a b c ..     => decide $ True -- TODO: σIsEmptyTriangle w[a] w[b] w[c] w.points

theorem satisfies_signotopeAxiom (w : WBPoints) (i j k l : Fin w.length) :
    i < j → j < k → k < l → w.toPropAssn ⊨ signotopeAxiom i j k l := by
  intro hij hjk hkl
  have : [w[i], w[j], w[k], w[l]] <+ w.points := by
    have : [w[i], w[j], w[k], w[l]] = [i,j,k,l].map w.points.get := by
      simp [GetElem.getElem, List.getElem_eq_get]
    rw [this]
    apply map_get_sublist
    have := hjk.trans hkl
    simp [hij, hjk, hkl, hij.trans hjk, hij.trans this, this]
  have s : Sorted₄ w[i] w[j] w[k] w[l] := w.sorted.to₄ this
  have gp : InGeneralPosition₄ w[i] w[j] w[k] w[l] :=
    PointListInGeneralPosition.to₄ w.gp this
  simp only [signotopeAxiom, satisfies_conj, satisfies_impl, satisfies_var,
    toPropAssn, decide_eq_true_eq, and_imp, satisfies_neg]
  constructor
  . exact σ_prop₂ s gp
  constructor
  . exact σ_prop₁ s gp
  constructor
  . simp_rw [gp.gp₁.σ_iff, gp.gp₂.σ_iff, gp.gp₃.σ_iff]
    exact σ_prop₄ s gp
  . simp_rw [gp.gp₁.σ_iff, gp.gp₄.σ_iff, gp.gp₃.σ_iff]
    exact σ_prop₃ s gp

theorem satisfies_signotopeAxioms (w : WBPoints) : w.toPropAssn ⊨ signotopeAxioms w.length := by
  unfold signotopeAxioms
  simp only [signotopeAxioms, satisfies_all, Multiset.mem_map, mem_val, mem_univ, true_and,
    forall_exists_index, forall_apply_eq_imp_iff]
  intro i j k l
  split
  . apply satisfies_signotopeAxiom <;> tauto
  exact satisfies_tr

/-
theorem insideTriangle_toPropAssn (σ : OrientationAssn n) :
    σ.IsInside x a b c ↔ σ.toPropAssn ⊨ insideDefinitions n ⊓ inside x a b c

theorem hasHole_toPropAssn :
    ¬L.isEmptyTriangle a b c → L.toPropAssn ⊨ insideDefinitions n ⊓ holeConstraints n ⊓ (hole a b c)ᶜ

theorem satisfies_noHoles :
    ∀ a b c, ¬w.isEmptyTriangle a b c → w.toPropAssn ⊨ theFormula
-/

end WBPoints
