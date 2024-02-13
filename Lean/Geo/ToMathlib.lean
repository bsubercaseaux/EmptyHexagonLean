import Std.Data.List.Basic
import Mathlib.Tactic

-- theorem sublist_to_indexsequence
--   {L₁ : List α} {L : List α} (h : List.Sublist L₁ L) :
--   ∃ (indexList : List (Fin L.length)),
--     indexList.length = L₁.length ∧
--       (∀ (i : Fin indexList.length),
--     L[indexList[i]] =  L₁.get? i)
--       ∧ List.Sorted (· < ·) indexList  := by
--       sorry

open List in
theorem List.mem_sublist {l l' : List α} : l <+ l' → a ∈ l → a ∈ l'
  | .slnil, h => h
  | .cons _ h, h' => mem_cons_of_mem _ (mem_sublist h h')
  | .cons₂ .., .head _ => mem_cons_self ..
  | .cons₂ _ h, .tail _ h' => mem_cons_of_mem _ (mem_sublist h h')

theorem List.of_Pairwise_toFinset [DecidableEq α] (as : List α) (R : α → α → Prop) :
    (∀ i j : Fin as.length, i < j → as[i] = as[j] → R as[i] as[j]) →
    as.toFinset.toSet.Pairwise R → as.Pairwise R := by
  rw [pairwise_iff_get]
  intro hRefl h i j hLt
  cases hEq : decide (as[i] = as[j])
  . have := of_decide_eq_false hEq
    exact h (mem_toFinset.mpr (as.get_mem ..)) (mem_toFinset.mpr (as.get_mem ..)) this
  . apply hRefl _ _ hLt (of_decide_eq_true hEq)

@[simp]
theorem List.toFinset_map [DecidableEq α] [DecidableEq β] (l : List α) (f : α → β) :
    (l.map f).toFinset = f '' l.toFinset := by
  ext; simp
