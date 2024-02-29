import LeanSAT.Model.PropFun
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Sum.Order

/-! The CNF that we produce, as a `PropFun`. -/

namespace Geo
open LeanSAT Model PropFun

inductive Var (n : Nat)
  | sigma  (a b c : Fin n)
  | inside (x a b c : Fin n)
  | hole   (a b c : Fin n)
  deriving DecidableEq

-- TODO: make a deriving instance for `LinearOrder`
instance : LinearOrder (Var n) :=
  LinearOrder.lift'
    (β := Fin n ×ₗ Fin n ×ₗ Fin n ⊕ₗ
          Fin n ×ₗ Fin n ×ₗ Fin n ×ₗ Fin n ⊕ₗ
          Fin n ×ₗ Fin n ×ₗ Fin n)
    (fun
      | .sigma a b c => .inlₗ (a, b, c)
      | .inside x a b c => .inrₗ <| .inlₗ (x, a, b, c)
      | .hole a b c => .inrₗ <| .inrₗ (a, b, c))
    (by rintro ⟨⟩ ⟨⟩ <;> simp <;> rintro ⟨⟩ <;> simp)
