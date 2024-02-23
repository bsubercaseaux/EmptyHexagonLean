import Std.Data.List.Basic
import Mathlib.Tactic

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

theorem exists_lt_list (l : List α) (f : α → ℝ) : ∃ a, ∀ x ∈ l, a < f x := by
  induction' l with a l ih <;> simp
  have ⟨r, h⟩ := ih
  refine ⟨min (f a - 1) r, by simp (config := {contextual := true}) [h]⟩

theorem exists_gt_list (l : List α) (f : α → ℝ) : ∃ a, ∀ x ∈ l, f x < a := by
  have ⟨r, h⟩ := exists_lt_list l (-f ·)
  exact ⟨-r, fun _ hx => lt_neg.1 (h _ hx)⟩

theorem Finset.exists_mk (s : Finset A) : ∃ l : List A, ∃ h : l.Nodup, s = ⟨l, h⟩ := by
  rcases s with ⟨⟨l⟩, h⟩; exact ⟨_, _, rfl⟩

theorem AffineIndependent.card_le_finrank_succ' {k V P ι : Type*}
    [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P] [Module.Finite k V]
    [Fintype ι] {p : ι → P} (H : AffineIndependent k p) :
    Fintype.card ι ≤ FiniteDimensional.finrank k V + 1 :=
  H.card_le_finrank_succ.trans <| Nat.succ_le_succ (Submodule.finrank_le _)
