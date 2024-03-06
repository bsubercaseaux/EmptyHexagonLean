import Mathlib.Data.Fin.Basic
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Sum.Order

/-! The CNF that we produce, as a `PropFun`. -/

namespace Geo

inductive Var (n : Nat)
  | sigma  (a b c : Fin n)
  | inside (x a b c : Fin n)
  | hole   (a b c : Fin n)
  | cap    (a c d : Fin n)
  | cup    (a c d : Fin n)
  | capF   (a d e : Fin n)
  deriving DecidableEq

-- TODO: make a deriving instance for `LinearOrder`
instance : LinearOrder (Var n) :=
  LinearOrder.lift'
    (β := (Fin n ×ₗ Fin n ×ₗ Fin n ⊕ₗ
           Fin n ×ₗ Fin n ×ₗ Fin n ×ₗ Fin n ⊕ₗ
           Fin n ×ₗ Fin n ×ₗ Fin n) ⊕ₗ
           Fin n ×ₗ Fin n ×ₗ Fin n ⊕ₗ
           Fin n ×ₗ Fin n ×ₗ Fin n ⊕ₗ
           Fin n ×ₗ Fin n ×ₗ Fin n)
    (fun
      | .sigma a b c => .inlₗ <| .inlₗ (a, b, c)
      | .inside x a b c => .inlₗ <| .inrₗ <| .inlₗ (x, a, b, c)
      | .hole a b c => .inlₗ <| .inrₗ <| .inrₗ (a, b, c)
      | .cap a c d => .inrₗ <| .inlₗ (a, c, d)
      | .capF a d e => .inrₗ <| .inrₗ <| .inlₗ (a, d, e)
      | .cup a c d => .inrₗ <| .inrₗ <| .inrₗ (a, c, d))
    (by rintro ⟨⟩ ⟨⟩ <;> simp <;> rintro ⟨⟩ <;> simp)

def Var.toCode : Var n → String
  | .sigma a b c => s!"0 0 {a} {b} {c}"
  | .inside x a b c => s!"1 {x} {a} {b} {c}"
  | .hole a b c => s!"2 0 {a} {b} {c}"
  | .cap a b c => s!"3 0 {a} {b} {c}"
  | .cup a b c => s!"4 0 {a} {b} {c}"
  | .capF a b c => s!"5 0 {a} {b} {c}"
