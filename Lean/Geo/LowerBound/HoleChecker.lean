import Std.Tactic.GuardExpr
import Std.Data.Rat
import Mathlib.Data.List.Sort
import Mathlib.Data.Prod.Lex

namespace Geo

namespace HoleChecker

def NPoint := Nat × Nat

def ccw (a b c : NPoint) : Bool :=
  a.1 * b.2 + b.1 * c.2 + c.1 * a.2 > a.2 * b.1 + b.2 * c.1 + c.2 * a.1

structure VisibilityGraph (n : Nat) where
  edges : Array (List (Fin n) × List (Fin n))
  sz : edges.size = n

instance : EmptyCollection (VisibilityGraph n) := ⟨mkArray n ([], []), by simp⟩

def VisibilityGraph.add (g : VisibilityGraph n) (i j : Fin n) : VisibilityGraph n where
  edges := g.edges
    |>.modify i (fun (in_, out) => (in_, j :: out))
    |>.modify j (fun (in_, out) => (i :: in_, out))
  sz := by simp [g.sz]

def Below (i : Nat)  : List (Fin n) → Prop
  | [] => True
  | a :: l => a < i ∧ Below i l

theorem below_iff : Below i l ↔ ∀ j ∈ l, j < i := by induction l <;> simp [Below, *]
theorem Below.reverse : Below i l.reverse ↔ Below i l := by simp [below_iff]

def BelowList (n i : Nat) := {l : List (Fin n) // Below i l}

structure Queues (n a : Nat) where
  graph : VisibilityGraph n := {}
  q : Array (List (Fin n))
  le : a ≤ n
  sz : a = q.size
  lt : ∀ i (h : i < a), Below i (q[i]'(by omega))

@[inline] def Queues.set (Q : Queues n a) (i : Fin a) (l : BelowList n i) : Queues n a where
  graph := Q.graph
  q := Q.q.set (i.cast Q.sz) l.1
  le := Q.le
  sz := by simp [Q.sz]
  lt i h := by
    rw [Array.get_set]; split
    · subst i; simpa using l.2
    · exact Q.lt i h

@[inline] def Queues.push (Q : Queues n a) (ha : a < n) (l : BelowList n a) : Queues n (a + 1) where
  graph := Q.graph
  q := Q.q.push l.1
  le := ha
  sz := by simp [Q.sz]
  lt i h := by
    rw [Array.get_push]; split
    · apply Q.lt i; rwa [Q.sz]
    · have := Nat.eq_of_lt_succ_of_not_lt h (by rwa [Q.sz])
      subst i; simpa using l.2

@[specialize] def proceed (pts : Fin n → NPoint) (i j : Fin n) (hi : i < j)
    (Q : Queues n j) (Q_j : BelowList n j) :
    Queues n j × BelowList n j :=
  let q := Q.q[i]'(Q.sz ▸ hi)
  have : Below i q := Q.lt i hi
  let IH := fun a (h : a < i) => proceed pts a j (h.trans hi)
  let rec finish (Q : Queues n j) (Q_i : BelowList n i) (Q_j : BelowList n j) :
      Queues n j × BelowList n j :=
    let Q := Q.set ⟨i, hi⟩ Q_i
    ({ Q with graph := Q.graph.add i j }, ⟨i :: Q_j.1, hi, Q_j.2⟩)
  let rec loop Q Q_j : ∀ Q_i : List (Fin n), Below i Q_i →
      Queues n j × BelowList n j
  | [], hQi => finish Q ⟨_, hQi⟩ Q_j
  | a :: q, ⟨ha, hq⟩ =>
    if ccw (pts a) (pts i) (pts j) then
      let (Q, Q_j) := IH a ha Q Q_j
      loop Q Q_j q hq
    else
      finish Q ⟨a::q, ha, hq⟩ Q_j
  loop Q Q_j q this

@[specialize] def mkVisibilityGraph (pts : Fin n → NPoint) : VisibilityGraph n :=
  if n0 : 0 < n then
    loop 0 {
      q := #[[]]
      le := n0
      sz := rfl
      lt := by simp; rintro _ rfl; constructor
    }
  else {}
where
  loop (i : Nat) (Q : Queues n (i+1)) : VisibilityGraph n :=
    let j := i + 1
    if hj : j < n then
      let (Q, Q_j) := proceed pts ⟨i, Q.le⟩ ⟨j, hj⟩ (Nat.lt_succ_self _) Q ⟨[], ⟨⟩⟩
      have := Nat.le_of_lt hj
      loop j (Q.push hj ⟨Q_j.1.reverse, Below.reverse.2 Q_j.2⟩)
    else
      Q.graph
  termination_by n - i

def maxChain (pts : Fin n → NPoint) (r : Nat) (graph : VisibilityGraph n)
    (lmap : Std.RBMap (Fin n ×ₗ Fin n) Nat compare) : ∀ i, i ≤ n → Option Unit
  | 0, _ => pure ()
  | p+1, hp => do
    let (in_, out) := graph.edges.get ⟨p, graph.sz.symm ▸ hp⟩
    let lmap ← if let [] := in_ then
      pure lmap
    else
      let p : Fin n := ⟨p, hp⟩
      let rec loop lmap
      | [], _, m => do
        guard <| m < r
        pure lmap
      | i::in_, out, m => do
        let finish out m :=
          loop (lmap.insert (i, p) (m+1)) in_ out m
        let rec inner
        | [], m => finish [] m
        | o::out, m => do
          if ccw (pts i) (pts p) (pts o) then
            inner out <| max m (lmap.find! (p, o))
          else finish (o::out) m
        inner out m
      loop lmap in_ out 0
    maxChain pts r graph lmap p (Nat.le_of_lt hp)

def holeCheck (r : Nat) (points : List NPoint) (lo : Nat) : Option Unit :=
  match points with
  | [] => return
  | p :: points => do
    guard <| lo < p.1
    let slope : NPoint → Rat := fun q => mkRat (q.2 - p.2) (q.1 - p.1)
    let sorted := points.mergeSort (slope · ≤ slope ·)
    guard <| sorted.Chain' (slope · ≠ slope ·)
    let sorted := Array.mk sorted
    let n := sorted.size
    let graph := mkVisibilityGraph (n := n) (fun i => sorted[i])
    maxChain (n := n) (fun i => sorted[i]) r graph {} n (Nat.le_refl _)
    holeCheck r points p.1
