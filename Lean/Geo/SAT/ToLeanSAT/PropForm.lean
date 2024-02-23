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
@[match_pattern] protected def false : PropForm v := .any' #[]

def conjs : PropForm v → Array (PropForm v)
  | .all' as => as
  | a => #[a]

def disjs : PropForm v → Array (PropForm v)
  | .any' as => as
  | a => #[a]

def all (as : Array (PropForm v)) : PropForm v :=
  match as.concatMap conjs with
  | #[a] => a
  | as => .all' as

def any (as : Array (PropForm v)) : PropForm v :=
  match as.concatMap disjs with
  | #[a] => a
  | as => .any' as

def and (a b : PropForm v) : PropForm v := .all (a.conjs ++ b.conjs)

def or (a b : PropForm v) : PropForm v := .any (a.disjs ++ b.disjs)

@[match_pattern] def var (a : v) : PropForm v := .lit true a

instance : Coe v (PropForm v) := ⟨var⟩

@[match_pattern] def not : PropForm v → PropForm v
  | .not' a => a
  | .lit pos a => .lit (!pos) a
  | a => .not' a

def imp (a b : PropForm v) : PropForm v := .or (.not a) b

def iff : PropForm v → PropForm v → PropForm v
  | .true, a | a, .true => a
  | .false, a | a, .false => .not a
  | .not' a, b => .iff' a (.not b)
  | a, b => .iff' a b

def atomic : PropForm v → PropForm v
  | .atomic' a => .atomic' a
  | .lit pos a => .lit pos a
  | a => .atomic' a

def forAll (as : σ) [ToArray as α] (f : α → PropForm v) : PropForm v :=
  .all <| ToArray.toArray as f

def «exists» (as : σ) [ToArray as α] (f : α → PropForm v) : PropForm v :=
  .any <| ToArray.toArray as f

def guard (p : Prop) [Decidable p] (f : p → PropForm v) : PropForm v :=
  if hp : p then f hp else .true

end PropForm
