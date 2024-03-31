import Std.Data.List.Basic
import Mathlib.Data.Complex.Abs
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.Convex.Between
import Mathlib.Analysis.Convex.Combination

-- Q: Why are `List.get [i]` *and* `l[i.1]` both simp normal forms? Should we have `List.get i = l[i.1]`?
-- There is also `List.getElem_eq_get : l[i] = l.get i` that never gets applied because `l[i]` is not simp-nf..
-- Mario: can have a `simp` lemma for this in std4.

theorem List.get_reverse'' (l : List α) (i : Fin l.reverse.length) :
    get (reverse l) i = get l (Fin.rev ⟨i, by simpa using i.2⟩) := by
  let j : Fin l.length := Fin.rev ⟨i, by simpa using i.2⟩
  have : j.1 = l.length - 1 - i := by simp [j]; omega
  convert List.get_reverse' _ _ (this ▸ j.2)

open List in
theorem List.mem_sublist {l l' : List α} : l <+ l' → a ∈ l → a ∈ l' :=
  fun h h' => h.subset h'

open List in
theorem List.Sublist.toFinset_subset [DecidableEq α] {l l' : List α} :
    l <+ l' → l.toFinset ⊆ l'.toFinset := by
  intro h _ al
  simp only [List.mem_toFinset] at al ⊢
  apply h.subset al

open List in
theorem List.Subperm.nodup : l <+~ l' →  l'.Nodup → l.Nodup
  | ⟨_, h1, h2⟩, H => h1.nodup_iff.1 <| H.sublist h2

open List in
theorem List.Subperm.cons : l <+~ l' → l <+~ a :: l'
  | ⟨l₂, hp, hs⟩ => ⟨l₂, hp, .cons _ hs⟩

open List in
theorem List.Subperm.cons₂ : l <+~ l' → a :: l <+~ a :: l'
  | ⟨l₂, hp, hs⟩ => ⟨a::l₂, .cons _ hp, .cons₂ _ hs⟩

theorem List.Chain.and : @Chain α R l a → Chain S l a → Chain (fun a b => R a b ∧ S a b) l a
  | .nil, .nil => .nil
  | .cons ha₁ h₁, .cons ha₂ h₂ => .cons ⟨ha₁, ha₂⟩ (h₁.and h₂)

theorem List.Chain'.and : ∀ {l}, @Chain' α R l → Chain' S l → Chain' (fun a b => R a b ∧ S a b) l
  | [], _, _ => trivial
  | _::_, h₁, h₂ => Chain.and h₁ h₂

theorem List.Chain'.imp₂ {R S T : α → α → Prop} (H : ∀ a b, R a b → S a b → T a b)
    (h1 : Chain' R l) (h2 : Chain' S l) : Chain' T l :=
  (h1.and h2).imp fun _ _ ⟨h1, h2⟩ => H _ _ h1 h2

theorem List.of_Pairwise_toFinset [DecidableEq α] (as : List α) (R : α → α → Prop) :
    (∀ i j : Fin as.length, i < j → as[i] = as[j] → R as[i] as[j]) →
    as.toFinset.toSet.Pairwise R → as.Pairwise R := by
  rw [pairwise_iff_get]
  intro hRefl h i j hLt
  cases hEq : decide (as[i] = as[j])
  . have := of_decide_eq_false hEq
    exact h (mem_toFinset.mpr (as.get_mem ..)) (mem_toFinset.mpr (as.get_mem ..)) this
  . apply hRefl _ _ hLt (of_decide_eq_true hEq)

open List in
theorem List.sublist_map {l₁ : List β} {l₂ : List α} {f : α → β} :
    l₁ <+ map f l₂ ↔ ∃ l', l₁ = map f l' ∧ l' <+ l₂ := by
  refine ⟨fun h => ?_, fun ⟨l', h1, h2⟩ => h1 ▸ h2.map _⟩
  generalize e : map f l₂ = l₂' at h
  induction h generalizing l₂ with
  | slnil => exact ⟨[], rfl, nil_sublist _⟩
  | cons _ _ ih =>
    let a :: l₂ := l₂; cases e
    obtain ⟨l', rfl, h2⟩ := ih rfl
    exact ⟨_, rfl, .cons _ h2⟩
  | cons₂ _ _ ih =>
    let a :: l₂ := l₂; cases e
    obtain ⟨l', rfl, h2⟩ := ih rfl
    exact ⟨_::_, rfl, .cons₂ _ h2⟩

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
  termination_by as.size - i
  go 0 init

@[inline] def foldl' {α : Type u} {β : Type v}
    (as : Array α) (f : β → (a : α) → a ∈ as → β) (init : β) : β :=
  Id.run <| foldlM' as f init

def mapM'' [Monad m] (as : Array α) (f : (a : α) → a ∈ as → m β) : m (Array β) :=
  foldlM' as (fun acc a h => acc.push <$> f a h) (mkEmpty as.size)

def forM' [Monad m] (as : Array α) (f : (a : α) → a ∈ as → m Unit) : m Unit :=
  foldlM' as (fun _ a h => f a h) ()

end Array

/-- An axiom that stands for things which have been proven, or should be proven,
in mathlib or std; but which we don't consider `sorry`s on our end. -/
axiom mathlibSorry (P : Prop) : P

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
  termination_by as.size - i
  simp [foldlM']; exact go (Nat.zero_le _) h0

theorem foldl'_induction
    {as : Array α} (motive : Nat → β → Prop) {init : β} (h0 : motive 0 init)
    {f : β → (a : α) → a ∈ as → β}
    (hf : ∀ i : Fin as.size, ∀ b, motive i.1 b → motive (i.1 + 1) (f b as[i] ⟨List.get_mem ..⟩)) :
    motive as.size (as.foldl' f init) := by
  have := SatisfiesM_foldlM' (m := Id) (as := as) (f := f) motive h0
  simp [SatisfiesM_Id_eq] at this
  exact this hf

theorem mem_sortAndDeduplicate [LinearOrder α] {as : Array α} :
    x ∈ as.sortAndDeduplicate ↔ x ∈ as := mathlibSorry _

end Array

namespace Std.HashMap

theorem find?_empty [Hashable α] [BEq α] : (∅ : HashMap α β).find? k = none := mathlibSorry _

theorem of_find?_insert [Hashable α] [BEq α] {m : HashMap α β} {a b} :
    (m.insert a b).find? k = some v → m.find? k = some v ∨ k = a ∧ v = b := mathlibSorry _

end Std.HashMap

namespace Std.RBMap

theorem find?_insert {cmp} [@TransCmp α cmp] (t : RBMap α β cmp) (k k' v) :
    (t.insert k v).find? k' = if cmp k' k = .eq then some v else t.find? k' := mathlibSorry _

end Std.RBMap

instance : @Std.TransCmp (Fin n ×ₗ Fin n) compare := mathlibSorry _

theorem lex_compare_eq_iff (a b : Fin n ×ₗ Fin n) : compare a b = .eq ↔ a = b := mathlibSorry _

theorem mem_affineSpan_pair [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]
    {p₁ p₂ p : P} : p ∈ line[k, p₁, p₂] ↔ ∃ r : k, r • (p₂ -ᵥ p₁) +ᵥ p₁ = p := by
  conv_lhs => rw [← vsub_vadd p p₁]
  rw [vadd_left_mem_affineSpan_pair]; simp only [eq_comm, eq_vadd_iff_vsub_eq]

theorem Wbtw.trans_ne_right [LinearOrderedField R] [AddCommGroup V] [Module R V] [AddTorsor V P]
    {w x y z : P} (h₁ : Wbtw R w x y) (h₂ : Wbtw R x y z) (ne : x ≠ y) : Wbtw R w y z := by
  replace h₂ := h₂.symm
  simp [wbtw_iff_right_eq_or_left_mem_image_Ici, ne, ne.symm] at h₁ h₂
  obtain ⟨r, hr, rfl⟩ := h₁
  obtain ⟨s, hs, rfl⟩ := h₂
  rw [AffineMap.lineMap_apply, ← AffineMap.lineMap_apply_one_sub, AffineMap.lineMap_apply]
  exact wbtw_smul_vadd_smul_vadd_of_nonneg_of_nonpos _ _ (zero_le_one.trans hr) (sub_nonpos.2 hs)

theorem Wbtw.trans_ne_left [LinearOrderedField R] [AddCommGroup V] [Module R V] [AddTorsor V P]
    {w x y z : P} (h₁ : Wbtw R w x y) (h₂ : Wbtw R x y z) (ne : x ≠ y) : Wbtw R w x z :=
  (Wbtw.trans_ne_right h₂.symm h₁.symm ne.symm).symm

theorem Wbtw.wbtw_or_wbtw [LinearOrderedField R] [AddCommGroup V] [Module R V] [AddTorsor V P]
    {w x y z : P} (h₁ : Wbtw R w x z) (h₂ : Wbtw R w y z) : Wbtw R w x y ∨ Wbtw R w y x := by
  obtain ⟨r, ⟨r0, _⟩, rfl⟩ := h₁
  obtain ⟨s, ⟨s0, _⟩, rfl⟩ := h₂
  exact wbtw_or_wbtw_smul_vadd_of_nonneg _ _ r0 s0

open BigOperators in
theorem linear_combination_mem_convexHull {k V : Type*}
    [LinearOrderedField k] [AddCommGroup V] [Module k V] {ι : Type*}
    (s : Finset ι) (v : ι → V) (w : ι → k) (h1 : ∀ i ∈ s, 0 ≤ w i) (h2 : ∑ i in s, w i = 1) :
    (∑ i in s, w i • v i) ∈ convexHull k (Set.range v) := by
  rw [← Finset.affineCombination_eq_linear_combination s v w h2]
  exact affineCombination_mem_convexHull h1 h2

theorem perm₃_induction {P : α → α → α → Prop}
    (H1 : ∀ {{a b c}}, P a b c → P b a c)
    (H2 : ∀ {{a b c}}, P a b c → P a c b)
    (h : [p, q, r].Perm [p', q', r']) : P p q r ↔ P p' q' r' := by
  suffices ∀ {p q r p' q' r'}, [p, q, r].Perm [p', q', r'] →
    P p q r → P p' q' r' from ⟨this h, this h.symm⟩
  clear p q r p' q' r' h; intro p q r p' q' r' h gp
  rw [← List.mem_permutations] at h; change _ ∈ [_,_,_,_,_,_] at h; simp at h
  obtain h|h|h|h|h|h := h <;> obtain ⟨rfl,rfl,rfl⟩ := h
  · exact gp
  · exact H1 gp
  · exact H1 <| H2 <| H1 gp
  · exact H1 <| H2 gp
  · exact H2 <| H1 gp
  · exact H2 gp
