import Std.Data.List.Basic
import Mathlib.Tactic

-- Q: Why are `List.get [i]` *and* `l[i.1]` both simp normal forms? Should we have `List.get i = l[i.1]`?
-- There is also `List.getElem_eq_get : l[i] = l.get i` that never gets applied because `l[i]` is not simp-nf..
-- Mario: can have a `simp` lemma for this in std4.

open List in
theorem List.mem_sublist {l l' : List α} : l <+ l' → a ∈ l → a ∈ l' :=
  fun h h' => h.subset h'

open List in
theorem List.Sublist.toFinset_subset [DecidableEq α] {l l' : List α} :
    l <+ l' → l.toFinset ⊆ l'.toFinset := by
  intro h _ al
  simp only [List.mem_toFinset] at al ⊢
  apply h.subset al

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

@[simp] theorem Array.concatMap_data (arr : Array α) (f : α → Array β) :
    (arr.concatMap f).data = arr.data.bind fun a => (f a).data := by
  have (l acc) : (List.foldl (fun bs a ↦ bs ++ f a) acc l).data =
      acc.data ++ List.bind l fun a ↦ (f a).data := by
    induction l generalizing acc <;> simp [*]
  simp [concatMap, foldl_eq_foldl_data, this]; rfl

theorem Array.mem_concatMap (arr : Array α) (f : α → Array β) :
    b ∈ arr.concatMap f ↔ ∃ a ∈ arr, b ∈ f a := by simp [Array.mem_def]

@[simp] theorem Array.forall_mem_concatMap (arr : Array α) (f : α → Array β) (p : β → Prop) :
    (∀ x ∈ arr.concatMap f, p x) ↔ (∀ x ∈ arr, ∀ y ∈ f x, p y) := by
  simp [Array.mem_concatMap]; aesop

@[simp] theorem Array.exists_mem_concatMap (arr : Array α) (f : α → Array β) (p : β → Prop) :
    (∃ x ∈ arr.concatMap f, p x) ↔ (∃ x ∈ arr, ∃ y ∈ f x, p y) := by
  simp [Array.mem_concatMap]; aesop

theorem Std.RBNode.toArray_eq {t : RBNode α} : t.toArray = ⟨t.toList⟩ := by
  have (l : List α) (acc) : List.foldl (Array.push · ·) acc l = acc ++ l := by
    induction l generalizing acc <;> simp [*]
  simp [toArray, foldl_eq_foldl_toList, this]; apply Array.ext'; simp

theorem Std.RBSet.toArray_eq {cmp} {t : RBSet α cmp} : t.1.toArray = ⟨t.toList⟩ :=
  Std.RBNode.toArray_eq

namespace Array

theorem mem_iff_getElem {a} {as : Array α} : a ∈ as ↔ ∃ n: Fin as.size, as[n] = a := by
  simp [mem_def, -getElem_fin, getElem_fin_eq_data_get, List.mem_iff_get]

@[inline]
private unsafe def foldlM'Unsafe [Monad m]
    (as : Array α) (f : β → (a : α) → a ∈ as → m β) (init : β) : m β :=
  as.foldlM (fun b a => f b a lcProof) init

@[implemented_by foldlM'Unsafe]
def foldlM' [Monad m]
    (as : Array α) (f : β → (a : α) → a ∈ as → m β) (init : β) : m β :=
  let rec go (i : Nat) (acc : β) : m β := do
    if h : i < as.size then
      go (i+1) (← f acc (as.get ⟨i, h⟩) (by simp [mem_def, getElem_mem_data]))
    else
      pure acc
  go 0 init
termination_by _ => as.size - i

@[inline] def foldl' {α : Type u} {β : Type v}
    (as : Array α) (f : β → (a : α) → a ∈ as → β) (init : β) : β :=
  Id.run <| foldlM' as f init

def mapM'' [Monad m] (as : Array α) (f : (a : α) → a ∈ as → m β) : m (Array β) :=
  foldlM' as (fun acc a h => acc.push <$> f a h) (mkEmpty as.size)

def forM' [Monad m] (as : Array α) (f : (a : α) → a ∈ as → m Unit) : m Unit :=
  foldlM' as (fun _ a h => f a h) ()

end Array

namespace Array

theorem SatisfiesM_foldlM' [Monad m] [LawfulMonad m]
    {as : Array α} (motive : Nat → β → Prop) {init : β} (h0 : motive 0 init)
    {f : β → (a : α) → a ∈ as → m β}
    (hf : ∀ i : Fin as.size, ∀ b, motive i.1 b →
      SatisfiesM (motive (i.1 + 1)) (f b as[i] ⟨List.get_mem ..⟩)) :
    SatisfiesM (motive as.size) (as.foldlM' f init) := by
  let rec go {i b} (h₁ : i ≤ as.size) (H : motive i b) :
    SatisfiesM (motive as.size) (foldlM'.go as f i b) := by
    unfold foldlM'.go; split
    · next hi =>
      exact (hf ⟨i, hi⟩ b H).bind fun _ => go hi
    · next hi => exact Nat.le_antisymm h₁ (Nat.ge_of_not_lt hi) ▸ .pure H
  simp [foldlM']; exact go (Nat.zero_le _) h0
termination_by _ => as.size - i

theorem foldl'_induction
    {as : Array α} (motive : Nat → β → Prop) {init : β} (h0 : motive 0 init)
    {f : β → (a : α) → a ∈ as → β}
    (hf : ∀ i : Fin as.size, ∀ b, motive i.1 b → motive (i.1 + 1) (f b as[i] ⟨List.get_mem ..⟩)) :
    motive as.size (as.foldl' f init) := by
  have := SatisfiesM_foldlM' (m := Id) (as := as) (f := f) motive h0
  simp [SatisfiesM_Id_eq] at this
  exact this hf

theorem mem_sortAndDeduplicate [LinearOrder α] {as : Array α} :
    x ∈ as.sortAndDeduplicate ↔ x ∈ as := sorry

end Array

namespace Std.HashMap

theorem find?_empty [Hashable α] [BEq α] : (∅ : HashMap α β).find? k = none := sorry

theorem of_find?_insert [Hashable α] [BEq α] {m : HashMap α β} {a b} :
    (m.insert a b).find? k = some v → m.find? k = some v ∨ k = a ∧ v = b := sorry

end Std.HashMap
