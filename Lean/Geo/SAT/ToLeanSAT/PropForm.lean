import Geo.ToMathlib
import Geo.SAT.ToLeanSAT.ToArray
import LeanSAT.Upstream.ToStd

namespace LeanSAT

inductive PropForm (v : Type) : Type where
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

protected partial def repr [Repr α] : PropForm α → Std.Format
  | .all' fs => .paren <| Std.Format.joinSep (fs.toList.map PropForm.repr) (" ∧" ++ Std.Format.line)
  | .any' fs => .paren <| Std.Format.joinSep (fs.toList.map PropForm.repr) (" ∨" ++ Std.Format.line)
  | .atomic' f => f!"atomic({PropForm.repr f})"
  | .lit true f => repr f
  | .lit false f => f!"!{repr f}"
  | .iff' a b => f!"({PropForm.repr a} ↔ {PropForm.repr b})"
  | .not' f => f!"¬{PropForm.repr f}"

instance [Repr α] : Repr (PropForm α) where
  reprPrec f _ := PropForm.repr f

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

set_option compiler.extract_closed false in -- lean4#1965
def all (as : Array (PropForm v)) : PropForm v :=
  match as.concatMap conjs with
  | #[a] => a
  | as => .all' as

@[simp] theorem eval_all' (τ : v → Prop) : eval τ (all' as) ↔ ∀ a ∈ as, eval τ a := by simp [eval]
@[simp] theorem eval_all (τ : v → Prop) : eval τ (all as) ↔ ∀ a ∈ as, eval τ a := by
  unfold all
  trans ∀ a ∈ as.concatMap conjs, eval τ a
  · generalize as.concatMap conjs = as'
    -- split -- FIXME: doesn't work, lean4#3843
    unfold all.match_1; simp; split
    · let ⟨[a]⟩ := as'; change eval τ a ↔ _; simp [Array.mem_def]
    · simp
  · simp [eval_conjs]

set_option compiler.extract_closed false in -- lean4#1965
def any (as : Array (PropForm v)) : PropForm v :=
  match as.concatMap disjs with
  | #[a] => a
  | as => .any' as

@[simp] theorem eval_any' (τ : v → Prop) : eval τ (any' as) ↔ ∃ a ∈ as, eval τ a := by simp [eval]
@[simp] theorem eval_any (τ : v → Prop) : eval τ (any as) ↔ ∃ a ∈ as, eval τ a := by
  unfold any
  trans ∃ a ∈ as.concatMap disjs, eval τ a
  · generalize as.concatMap disjs = as'
    -- split -- FIXME: doesn't work, lean4#3843
    unfold all.match_1; simp; split
    · let ⟨[a]⟩ := as'; change eval τ a ↔ _; simp [Array.mem_def]
    · simp
  · simp [eval_disjs]

def and (a b : PropForm v) : PropForm v := .all (a.conjs ++ b.conjs)

@[simp] theorem eval_and (τ : v → Prop) : eval τ (.and a b) ↔ eval τ a ∧ eval τ b := by
  simp [and, or_imp, forall_and, eval_conjs]

def or (a b : PropForm v) : PropForm v := .any (a.disjs ++ b.disjs)

@[simp] theorem eval_or (τ : v → Prop) : eval τ (.or a b) ↔ eval τ a ∨ eval τ b := by
  simp [or, or_and_right, exists_or, eval_disjs]

@[simp] theorem eval_lit' (τ : v → Prop) : eval τ (.lit pos i) ↔ (τ i ↔ pos) := by
  cases pos <;> simp [eval]

@[match_pattern] def var (a : v) : PropForm v := .lit true a

@[simp] theorem eval_var (τ : v → Prop) : eval τ (.var i) ↔ τ i := by simp [var]

instance : Coe v (PropForm v) := ⟨var⟩

@[match_pattern] def not : PropForm v → PropForm v
  | .not' a => a
  | .lit pos a => .lit (!pos) a
  | a => .not' a

@[simp] theorem eval_not' (τ : v → Prop) : eval τ (.not' a) ↔ ¬eval τ a := by simp [eval]

@[simp] theorem eval_not (τ : v → Prop) : eval τ (.not a) ↔ ¬eval τ a := by
  simp [not]; split <;> (try cases ‹Bool›) <;> simp

def imp (a b : PropForm v) : PropForm v := .or (.not a) b

@[simp] theorem eval_imp (τ : v → Prop) : eval τ (.imp a b) ↔ (eval τ a → eval τ b) := by
  simp [imp, imp_iff_not_or]

def iff : PropForm v → PropForm v → PropForm v
  | .true, a | a, .true => a
  | .false, a | a, .false => .not a
  | .not' a, b => .iff' a (.not b)
  | a, b => .iff' a b

@[simp] theorem eval_iff' (τ : v → Prop) : eval τ (.iff' a b) ↔ (eval τ a ↔ eval τ b) := by
   simp [eval]

attribute [-simp] eval_all' eval_any' in
@[simp] theorem eval_iff (τ : v → Prop) : eval τ (.iff a b) ↔ (eval τ a ↔ eval τ b) := by
  unfold iff iff.match_1 -- terrible proof, pending lean4#3843
  have not_iff_comm' {a b} : (¬a ↔ b) ↔ (a ↔ ¬b) := by rw [not_iff_comm, @Iff.comm a]
  cases a <;> simp <;> (try split_ifs)
    <;> (try rename Array.size _ = 0 => h; have := Array.eq_empty_of_size_eq_zero h
             subst this; simp; clear h)
    <;> cases b <;> simp <;> (try split_ifs)
    <;> (try rename Array.size _ = 0 => h; have := Array.eq_empty_of_size_eq_zero h
             subst this; simp; clear h)
    <;> simp [eval, not_iff_comm']

def atomic : PropForm v → PropForm v
  | .atomic' a => .atomic' a
  | .lit pos a => .lit pos a
  | a => .atomic' a

@[simp] theorem eval_atomic' (τ : v → Prop) : eval τ (.atomic' a) ↔ eval τ a := by simp [eval]

@[simp] theorem eval_atomic (τ : v → Prop) : eval τ (.atomic a) ↔ eval τ a := by
  simp [atomic]; split <;> (try cases ‹Bool›) <;> simp

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

/-- Expands out a formula directly as a CNF, without auxiliaries (unlike `PropForm.toICnf`).
Stops at `atomic` or literal subterms. -/
def flatCNF (f : PropForm v) : PropForm v :=
  .all (go f true (fun cl acc => acc.push <| .any cl) #[] #[])
where
  go : PropForm v → Bool →
    (Array (PropForm v) → Array (PropForm v) → Array (PropForm v)) →
    Array (PropForm v) → Array (PropForm v) → Array (PropForm v)
  | .not' a, pos, F, cl, acc => go a (!pos) F cl acc
  | .all' as, true, F, cl, acc => as.foldl' (fun acc a _ => go a true F cl acc) acc
  | .any' as, false, F, cl, acc => as.foldl' (fun acc a _ => go a false F cl acc) acc
  | .any' as, true, F, cl, acc => as.foldl' (fun G a _ F => G (go a true F)) (· cl acc) F
  | .all' as, false, F, cl, acc => as.foldl' (fun G a _ F => G (go a false F)) (· cl acc) F
  | .iff' a b, pos, F, cl, acc =>
    go b (!pos) (go a true F) cl <| go a false (go b pos F) cl acc
  | a, true, F, cl, acc => F (cl.push a) acc
  | a, false, F, cl, acc => F (cl.push (.not a)) acc

namespace eval_flatCNF
variable {τ : v → Prop}

abbrev R := Array (PropForm v)

abbrev evals (τ : v → Prop) (acc' cl acc : R) (A) :=
  (∀ a ∈ acc', eval τ a) ↔ (∀ a ∈ acc, eval τ a) ∧ (A ∨ ∃ a ∈ cl, eval τ a)

theorem goAll {α} (as : Array α) {FF : R → (a : α) → a ∈ as → R} {G : α → Prop} {acc cl A}
    (hFF : ∀ acc f h, evals τ (FF acc f h) cl acc (G f ∨ A)) :
    evals τ (as.foldl' FF acc) cl acc ((∀ a ∈ as, G a) ∨ A) := by
  refine Iff.trans (as.foldl'_induction (motive := fun i (acc' : R) =>
    evals τ acc' cl acc ((∀ j:Fin as.size, j < i → G as[j]) ∨ A)) (by simp) ?_) ?_
  · intro i acc IH; unfold evals at *
    simp [hFF, IH, Nat.lt_succ_iff_lt_or_eq, or_imp, forall_and,
      ← Fin.ext_iff, and_assoc, ← and_or_right]
  · simp [Array.mem_iff_getElem]

theorem goAny {α} (as : Array α) {FF : ∀ a ∈ as, (R → R → R) → R → R → R} {G : α → Prop}
    (hFF : ∀ f h {F A},
      (∀ cl acc, evals τ (F cl acc) cl acc A) →
      ∀ cl acc, evals τ (FF f h F cl acc) cl acc (G f ∨ A))
    {F A} (hF : ∀ cl acc, evals τ (F cl acc) cl acc A) (cl acc) :
    evals τ (as.foldl' (fun G a h F => G (FF a h F)) (· cl acc) F)
      cl acc ((∃ a ∈ as, G a) ∨ A) := by
  refine Iff.trans (as.foldl'_induction (motive := fun i (G' : (R → R → R) → R) =>
    ∀ {A F}, (∀ cl acc, evals τ (F cl acc) cl acc A) →
      evals τ (G' F) cl acc ((∃ j:Fin as.size, j < i ∧ G as[j]) ∨ A)) ?_ ?_ hF) ?_
  · simp; exact (· cl acc)
  · intro i G' IH F A hF
    rw [show ((∃ j, _) ∨ _) ↔ ?_ from ?_]; exact IH (hFF _ _ hF)
    simp [Nat.lt_succ_iff_lt_or_eq, or_and_right, exists_or, ← Fin.ext_iff, or_assoc]
  · simp [Array.mem_iff_getElem]

@[simp] theorem core (f pos) {F A} (hF : ∀ cl acc, evals τ (F cl acc) cl acc A) (cl acc) :
    evals τ (flatCNF.go f pos F cl acc) cl acc ((eval τ f ↔ pos) ∨ A) := by
  unfold flatCNF.go; split
  next /-not'-/ a => convert core a _ hF _ _ using 1; cases pos <;> simp
  iterate 2 next /-all'-/ as =>
    simp; refine goAll as fun acc f _ => (core f _ hF _ _).trans (by simp)
  iterate 2 next /-any'-/ as =>
    simp; refine (goAny as (fun f _ _ _ hF => core f _ hF) hF cl acc).trans (by simp)
  next /-iff'-/ a b =>
    unfold evals at *
    simp [core b (!pos) (core a true hF) cl, core a false (core b pos hF) cl]
    cases pos <;> simp <;> tauto
  iterate 2 next /-atom-/ a =>
    unfold evals at *
    simp [hF, or_imp, forall_and, or_and_right, exists_or, or_assoc, or_comm]
decreasing_by decreasing_with subst_vars; first | decreasing_trivial | simp_wf

end eval_flatCNF

@[simp] theorem eval_flatCNF (τ : v → Prop) (f : PropForm v) : eval τ (.flatCNF f) ↔ eval τ f := by
  simp [flatCNF]; rw [show _ ↔ _ from eval_flatCNF.core (A := False) ..]
    <;> simp [eval_flatCNF.evals, or_imp, forall_and]

end PropForm
