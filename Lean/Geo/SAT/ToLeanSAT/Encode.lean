import LeanSAT.Data.ICnf
import Geo.SAT.ToLeanSAT.PropForm

namespace LeanSAT
open Std

variable (cmp : v → v → Ordering)

def collectVars : PropForm v → RBSet v cmp → RBSet v cmp
  | .all' as, acc | .any' as, acc => as.foldl' (fun acc a _ => collectVars a acc) acc
  | .atomic' a, acc | .not' a, acc => collectVars a acc
  | .iff' a b, acc => collectVars b (collectVars a acc)
  | .lit _ a, acc => acc.insert a

@[inline] def binSearch (as : Array v) (k : v) : Nat :=
  let rec go (lo hi : Nat) : Nat :=
    if lo ≤ hi then
      let _ := Inhabited.mk k
      let m := (lo + hi)/2
      let a := as.get! m
      match cmp a k with
      | .lt => go (m+1) hi
      | .gt => if m = 0 then 0 else go lo (m-1)
      | .eq => m
    else unreachable!
  go 0 (as.size - 1)
termination_by _ => hi + 1 - lo
decreasing_by decreasing_with omega

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
  if let some cl ← as.foldlM' (init := some #[]) fun cl f _ => pushFmla cmp f pos cl then
    pushClause cl

def pushICnf : PropForm v → Bool → M v Unit
  | .not' a, pos => pushICnf a (!pos)
  | .all' as, true => as.forM' fun a _ => pushICnf a true
  | .any' as, false => as.forM' fun a _ => pushICnf a false
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
  let (_, { clauses, .. }) := Encode.pushICnf cmp fmla true |>.run vars
    |>.run { clauses := #[], nextVar := vars.size.succPNat, definitions := {} }
  clauses
