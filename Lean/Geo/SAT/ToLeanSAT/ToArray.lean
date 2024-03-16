import Mathlib.Data.Nat.Defs

namespace LeanSAT

class ToArray (as : σ) (α : outParam Type) where
  toArray (f : α → β) : Array β

class LawfulToArray (as : σ) (α : outParam Type) [ToArray as α] (p : outParam (α → Prop)) where
  base : Array α
  toArray_eq : ToArray.toArray as f = base.map f
  mem_base : a ∈ base ↔ p a

instance : ToArray [:n] Nat where
  toArray f := n.fold (fun n a => a.push (f n)) (Array.mkEmpty n)

instance : LawfulToArray [:n] Nat (· < n) where
  base := Array.range n
  toArray_eq {_ _} := by
    apply Array.ext'; simp [ToArray.toArray, Array.range, Array.map_data, flip]
    induction n <;> simp [Nat.fold, *]
  mem_base {i} := by
    simp [Array.range, flip, Array.mem_def]
    induction n <;> simp [Nat.fold, *, Nat.lt_succ_iff_lt_or_eq]

instance : ToArray (Fin n) (Fin n) where
  toArray f := Array.ofFn f

instance : LawfulToArray (Fin n) (Fin n) fun _ => True where
  base := Array.ofFn id
  toArray_eq {_ f} := by
    apply Array.ext'; simp [ToArray.toArray, Array.range, Array.map_data, Array.ofFn, flip]
    let rec go {i} {acc acc' : Array _} (h : acc.data = List.map f acc'.data) :
        (Array.ofFn.go f i acc).data = List.map f (Array.ofFn.go id i acc').data := by
      simp (config := {singlePass := true}) only [Array.ofFn.go]
      split <;> [apply go; skip] <;> simp [*]
    termination_by n - i
    exact go rfl
  mem_base {j} := by
    simp [Array.ofFn, Array.mem_def]
    let rec go' {i : ℕ} {acc : Array _} (h : j.1 < i → j ∈ acc.data) :
        j ∈ (Array.ofFn.go id i acc).data := by
      simp (config := {singlePass := true}) only [Array.ofFn.go]
      split <;> rename_i h1
      · apply go'; intro h2; simp [Fin.ext_iff]
        exact (Nat.lt_succ_iff_lt_or_eq.1 h2).imp_left h
      · exact h (Nat.lt_of_lt_of_le j.2 (Nat.not_lt.1 h1))
    termination_by n - i
    apply go'; simp

instance (as : Array α) : ToArray as α where
  toArray f := as.map f

instance (as : Array α) : LawfulToArray as α (· ∈ as) where
  base := as
  toArray_eq := rfl
  mem_base := .rfl

instance (as : List α) : ToArray as α where
  toArray f := as.foldl (fun arr a => arr.push (f a)) #[]

instance (as : List α) : LawfulToArray as α (· ∈ as) where
  base := as.toArray
  toArray_eq {_ f} := by
    have (as acc) :
        (List.foldl (fun arr a => Array.push arr (f a)) acc as).data =
        acc.data ++ List.map f as := by
      induction as generalizing acc <;> simp [*]
    apply Array.ext'; simp [ToArray.toArray, this]
  mem_base := by simp
