import Std.Data.List.Basic
import Mathlib.Tactic

theorem sublist_to_indexsequence
  {L₁ : List α} {L : List α} (h : List.Sublist L₁ L) :
  ∃ (indexList : List (Fin L.length)),
    indexList.length = L₁.length ∧
      (∀ (i : Fin indexList.length),
    L[indexList[i]] =  L₁.get? i)
      ∧ List.Sorted (· < ·) indexList  := by
      sorry
