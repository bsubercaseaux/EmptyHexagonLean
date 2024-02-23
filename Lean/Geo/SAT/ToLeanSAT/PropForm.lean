import Geo.ToMathlib
import Geo.SAT.ToLeanSAT.ToArray

namespace LeanSAT

inductive PropForm (v : Type) : Type
  | all' : Array (PropForm v) → PropForm v
  | any' : Array (PropForm v) → PropForm v
  | not' : PropForm v → PropForm v
  | iff' : PropForm v → PropForm v → PropForm v
  | lit (pos : Bool) : v → PropForm v
  | atomic' : PropForm v → PropForm v

namespace PropForm
def eval (τ : v → Prop) : PropForm v → Prop
  | all' as => ∀ a ∈ as, eval τ a
  | any' as => ∃ a, ∃ _ : a ∈ as, eval τ a
  | not' a => ¬eval τ a
  | iff' a b => eval τ a ↔ eval τ b
  | lit true a => τ a
  | lit false a => ¬τ a
  | atomic' a => eval τ a

@[match_pattern] protected def true : PropForm v := .all' #[]
@[simp] theorem eval_true (τ : v → Prop) : eval τ .true := by simp [PropForm.true, eval]

@[match_pattern] protected def false : PropForm v := .any' #[]
@[simp] theorem eval_false (τ : v → Prop) : ¬eval τ .false := by simp [PropForm.false, eval]

def conjs : PropForm v → Array (PropForm v)
  | .all' as => as
  | a => #[a]
theorem eval_conjs (τ : v → Prop) : (∀ a ∈ conjs f, eval τ a) ↔ eval τ f := by
  simp [PropForm.conjs]; split <;> simp [eval]

def disjs : PropForm v → Array (PropForm v)
  | .any' as => as
  | a => #[a]
theorem eval_disjs (τ : v → Prop) : (∃ a ∈ disjs f, eval τ a) ↔ eval τ f := by
  simp [PropForm.disjs]; split <;> simp [eval]

def all (as : Array (PropForm v)) : PropForm v :=
  match as.concatMap conjs with
  | #[a] => a
  | as => .all' as

@[simp] theorem eval_all (τ : v → Prop) : eval τ (all as) ↔ ∀ a ∈ as, eval τ a := by
  unfold all
  trans ∀ a ∈ as.concatMap conjs, eval τ a
  · generalize as.concatMap conjs = as'
    -- split -- FIXME: doesn't work, lean4#3843
    unfold all.match_1; simp; split
    · let ⟨[a]⟩ := as'; change eval τ a ↔ _; simp [Array.mem_def]
    · simp [eval]
  · simp [eval_conjs]

def any (as : Array (PropForm v)) : PropForm v :=
  match as.concatMap disjs with
  | #[a] => a
  | as => .any' as

@[simp] theorem eval_any (τ : v → Prop) : eval τ (any as) ↔ ∃ a ∈ as, eval τ a := by
  unfold any
  trans ∃ a ∈ as.concatMap disjs, eval τ a
  · generalize as.concatMap disjs = as'
    -- split -- FIXME: doesn't work, lean4#3843
    unfold all.match_1; simp; split
    · let ⟨[a]⟩ := as'; change eval τ a ↔ _; simp [Array.mem_def]
    · simp [eval]
  · simp [eval_disjs]

def and (a b : PropForm v) : PropForm v := .all (a.conjs ++ b.conjs)

@[simp] theorem eval_and (τ : v → Prop) : eval τ (.and a b) ↔ eval τ a ∧ eval τ b := by
  simp [and, or_imp, forall_and, eval_conjs]

def or (a b : PropForm v) : PropForm v := .any (a.disjs ++ b.disjs)

@[simp] theorem eval_or (τ : v → Prop) : eval τ (.or a b) ↔ eval τ a ∨ eval τ b := by
  simp [or, or_and_right, exists_or, eval_disjs]

@[match_pattern] def var (a : v) : PropForm v := .lit true a

@[simp] theorem eval_var (τ : v → Prop) : eval τ (.var i) ↔ τ i := by simp [var, eval]

instance : Coe v (PropForm v) := ⟨var⟩

@[match_pattern] def not : PropForm v → PropForm v
  | .not' a => a
  | .lit pos a => .lit (!pos) a
  | a => .not' a

@[simp] theorem eval_not (τ : v → Prop) : eval τ (.not a) ↔ ¬eval τ a := by
  simp [not]; split <;> (try cases ‹Bool›) <;> simp [eval]

def imp (a b : PropForm v) : PropForm v := .or (.not a) b

@[simp] theorem eval_imp (τ : v → Prop) : eval τ (.imp a b) ↔ (eval τ a → eval τ b) := by
  simp [imp, imp_iff_not_or]

def iff : PropForm v → PropForm v → PropForm v
  | .true, a | a, .true => a
  | .false, a | a, .false => .not a
  | .not' a, b => .iff' a (.not b)
  | a, b => .iff' a b

@[simp] theorem eval_iff (τ : v → Prop) : eval τ (.iff a b) ↔ (eval τ a ↔ eval τ b) := by
  sorry -- pending lean4#3843

def atomic : PropForm v → PropForm v
  | .atomic' a => .atomic' a
  | .lit pos a => .lit pos a
  | a => .atomic' a

@[simp] theorem eval_atomic (τ : v → Prop) : eval τ (.atomic a) ↔ eval τ a := by
  simp [atomic]; split <;> (try cases ‹Bool›) <;> simp [eval]

def forAll (as : σ) [ToArray as α] (f : α → PropForm v) : PropForm v :=
  .all <| ToArray.toArray as f

@[simp] theorem eval_forAll (τ : v → Prop) (as : σ) [ToArray as α] [LawfulToArray as α p] :
    eval τ (.forAll as f) ↔ ∀ a, p a → eval τ (f a) := by
  simp [forAll, LawfulToArray.toArray_eq, LawfulToArray.mem_base]

def «exists» (as : σ) [ToArray as α] (f : α → PropForm v) : PropForm v :=
  .any <| ToArray.toArray as f

@[simp] theorem eval_exists (τ : v → Prop) (as : σ) [ToArray as α] [LawfulToArray as α p] :
    eval τ (.exists as f) ↔ ∃ a, p a ∧ eval τ (f a) := by
  simp [PropForm.exists, LawfulToArray.toArray_eq, LawfulToArray.mem_base]

def guard (p : Prop) [Decidable p] (f : p → PropForm v) : PropForm v :=
  if hp : p then f hp else .true

@[simp] theorem eval_guard (τ : v → Prop) (p : Prop) {_ : Decidable p} (f : p → PropForm v) :
    eval τ (.guard p f) ↔ ∀ h : p, eval τ (f h) := by
  simp [guard]; split <;> simp [*]

end PropForm
