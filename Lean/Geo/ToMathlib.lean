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

-- Q: Why are `List.get [i]` *and* `l[i.1]` both simp normal forms? Should we have `List.get i = l[i.1]`?
-- There is also `List.getElem_eq_get : l[i] = l.get i` that never gets applied because `l[i]` is not simp-nf..
-- Mario: can have a `simp` lemma for this in std4.

open List in
theorem List.mem_sublist {l l' : List α} : l <+ l' → a ∈ l → a ∈ l' :=
  fun h h' => h.subset h'

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

theorem mul_neg_iff_of_pos_left {a b : ℝ} (h : 0 < a) : a * b < 0 ↔ b < 0 := by
  rw [← not_le, ← not_le, mul_nonneg_iff_right_nonneg_of_pos h]

theorem exists_lt_list (l : List α) (f : α → ℝ) : ∃ a, ∀ x ∈ l, a < f x := sorry
theorem exists_gt_list (l : List α) (f : α → ℝ) : ∃ a, ∀ x ∈ l, f x < a := sorry
