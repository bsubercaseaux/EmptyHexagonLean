import LeanSAT.Data.ICnf
import Geo.SAT.ToLeanSAT.PropForm

@[inline]
private unsafe def Array.foldlM'Unsafe [Monad m]
    (as : Array α) (f : β → (a : α) → a ∈ as → m β) (init : β) : m β :=
  as.foldlM (fun b a => f b a lcProof) init

@[implemented_by Array.foldlM'Unsafe]
def Array.foldlM' [Monad m]
    (as : Array α) (f : β → (a : α) → a ∈ as → m β) (init : β) : m β :=
  let rec go (i : Nat) (acc : β) : m β := do
    if h : i < as.size then
      go (i+1) (← f acc (as.get ⟨i, h⟩) (by simp [mem_def, getElem_mem_data]))
    else
      pure init
  go 0 init
termination_by _ => as.size - i

@[inline] def Array.foldl' {α : Type u} {β : Type v}
    (as : Array α) (f : β → (a : α) → a ∈ as → β) (init : β) : β :=
  Id.run <| Array.foldlM' as f init

def Array.mapM'' [Monad m] (as : Array α) (f : (a : α) → a ∈ as → m β) : m (Array β) :=
  foldlM' as (fun acc a h => acc.push <$> f a h) (Array.mkEmpty as.size)

def Array.forM' [Monad m] (as : Array α) (f : (a : α) → a ∈ as → m Unit) : m Unit :=
  foldlM' as (fun _ a h => f a h) ()

namespace LeanSAT
open Std

variable (cmp : v → v → Ordering)

def collectVars : PropForm v → RBSet v cmp → RBSet v cmp
  | .all' as, acc | .any' as, acc => as.foldl' (fun acc a _ => collectVars a acc) acc
  | .atomic' a, acc | .not' a, acc => collectVars a acc
  | .iff' a b, acc => collectVars b (collectVars a acc)
  | .lit _ a, acc => acc.insert a

@[inline] partial def binSearch (as : Array v) (k : v) : Nat :=
  let rec @[specialize] go (lo hi : Nat) : Nat :=
    if lo <= hi then
      let _ := Inhabited.mk k
      let m := (lo + hi)/2
      let a := as.get! m
      match cmp a k with
      | .lt => go (m+1) hi
      | .gt =>
        if m == 0 then 0 else
        go lo (m-1)
      | .eq => m
    else unreachable!
  go 0 as.size

namespace Encode

instance : Hashable ILit := inferInstanceAs (Hashable (Subtype _))
instance : Ord ILit := inferInstanceAs (Ord (Subtype _))

structure State (v : Type) where
  clauses : ICnf
  nextVar : IVar
  definitions : HashMap (Array ILit) IVar

abbrev M (v) := ReaderT (Array v) (StateT (State v) Id)

def encodeLit (pos : Bool) (i : v) : M v ILit := do
  let vars ← read
  let i := binSearch cmp vars i
  pure <| LitVar.mkLit _ i.succPNat pos

def getAny (as : Array ILit) : M v IVar := do
  let as := as.sortAndDeduplicate
  if let some i := (← get).definitions.find? as then
    return i
  modifyGet fun s =>
    let new := s.nextVar
    let definitions := s.definitions.insert as new
    let clauses := as.foldl (init := s.clauses) fun clauses a => clauses.push #[-a, new]
    let clauses := clauses.push (as.push (-new))
    (new, { s with definitions, clauses, nextVar := s.nextVar + 1 })

def toLit : PropForm v → Bool → M v ILit
  | .not' f, pos => toLit f (!pos)
  | .atomic' f, pos => toLit f pos
  | .lit pos i, pos' => encodeLit cmp (pos == pos') i
  | .all' as, pos =>
    return LitVar.mkLit _ (← getAny (← as.mapM'' fun a _ => toLit a false)) (!pos)
  | .any' as, pos =>
    return LitVar.mkLit _ (← getAny (← as.mapM'' fun a _ => toLit a true)) pos
  | .iff' a b, pos => do
    let a ← toLit a true
    let b ← toLit b true
    let a_imp_b ← getAny #[-a, b]
    let b_imp_a ← getAny #[a, -b]
    return LitVar.mkLit _ (← getAny #[-a_imp_b, -b_imp_a]) (!pos)

def pushFmla : PropForm v → Bool → Option IClause → M v (Option IClause)
  | _, _, none | .true, true, _ | .false, false, _ => pure none
  | .all' as, false, cl => as.foldlM' (init := cl) fun cl f _ => pushFmla f false cl
  | .any' as, true, cl => as.foldlM' (init := cl) fun cl f _ => pushFmla f true cl
  | .not' f, b, cl => pushFmla f (!b) cl
  | f, b, some cl => return some <| cl.push <| ← toLit cmp f b

def pushClause (cl : IClause) : M v Unit :=
  modify fun r => {r with clauses := r.clauses.push cl}

def toICnfAny (as : Array (PropForm v)) (pos : Bool) : M v Unit := do
  if let some cl ← as.foldlM (init := some #[]) fun cl f => pushFmla cmp f pos cl then
    pushClause cl

def pushICnfCore : PropForm v → Bool → M v Unit
  | .not' a, pos => pushICnfCore a (!pos)
  | .all' as, true => as.forM' fun a _ => pushICnfCore a true
  | .any' as, false => as.forM' fun a _ => pushICnfCore a false
  | .all' as, false => toICnfAny cmp as false
  | .any' as, true => toICnfAny cmp as true
  | .iff' a b, pos => do
    let a ← toLit cmp a true
    let b ← toLit cmp b pos
    pushClause #[-a, b]
    pushClause #[a, -b]
  | f, pos => toICnfAny cmp #[f] pos

end Encode

def PropForm.toICnf (fmla : PropForm v) : ICnf :=
  let vars := (collectVars cmp fmla ∅).1.toArray
  let (_, { clauses, .. }) := Encode.pushICnfCore cmp fmla true |>.run vars
    |>.run { clauses := #[], nextVar := vars.size.succPNat, definitions := {} }
  clauses

def Literal.eval [LitVar L v] (τ : v → Prop) (l : L) : Prop :=
  if LitVar.polarity l then τ (LitVar.toVar l) else ¬τ (LitVar.toVar l)

def Clause.eval [LitVar L v] (τ : v → Prop) (cnf : Clause L) : Prop :=
  ∃ l ∈ cnf, Literal.eval τ l

def Cnf.eval [LitVar L v] (τ : v → Prop) (cnf : Cnf L) : Prop :=
  ∀ cl ∈ cnf, Clause.eval τ cl

theorem PropForm.toICnf_sat [LinearOrder v] (f : PropForm v) :
    (∃ τ, Cnf.eval τ (f.toICnf compare)) ↔ ∃ τ, eval τ f := by
  sorry -- todo
