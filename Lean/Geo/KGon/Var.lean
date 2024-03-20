import Mathlib.Data.Fin.Basic
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Sum.Order
import Geo.Definitions.Orientations

/-! The CNF that we produce, as a `PropFun`. -/

namespace Geo

inductive Var (n : Nat) where
  | sigma  (a b c : Fin n)
  | inside (x a b c : Fin n)
  | hole₀  (a : Fin (n+1)) (b c : Fin n)
  | arc    (o : Orientation) (sz : Nat) (a c d : Fin n)
  | capF   (a d e : Fin n)
  deriving DecidableEq

instance : Inhabited (Var (n+1)) := ⟨.sigma 0 0 0⟩

def Var.hole (a b c : Fin n) := Var.hole₀ a.succ b c
@[match_pattern] def Var.cap (a b c : Fin n) := Var.arc .cw 1 a b c
@[match_pattern] def Var.cup (a b c : Fin n) := Var.arc .ccw 1 a b c

instance : Repr (Var n) where
  reprPrec
  | .sigma a b c, _ => f!"σ {a.succ} {b.succ} {c.succ}"
  | .inside x a b c, _ => f!"inside {x.succ} {a.succ} {b.succ} {c.succ}"
  | .hole₀ a b c, _ => f!"hole {a} {b.succ} {c.succ}"
  | .arc o sz a b c, _ => f!"arc {repr o} {sz} {a.succ} {b.succ} {c.succ}"
  | .capF a b c, _ => f!"capF {a.succ} {b.succ} {c.succ}"

instance : LinearOrder Orientation :=
  LinearOrder.lift'
    (β := Nat)
    (fun
      | .cw => 0
      | .collinear => 1
      | .ccw => 2)
    (by rintro ⟨⟩ ⟨⟩ <;> simp)

-- TODO: make a deriving instance for `LinearOrder`
instance : LinearOrder (Var n) :=
  LinearOrder.lift'
    (β := (Fin n ×ₗ Fin n ×ₗ Fin n ⊕ₗ
           Fin n ×ₗ Fin n ×ₗ Fin n ×ₗ Fin n ⊕ₗ
           Fin (n+1) ×ₗ Fin n ×ₗ Fin n) ⊕ₗ
           Orientation ×ₗ Nat ×ₗ Fin n ×ₗ Fin n ×ₗ Fin n ⊕ₗ
           Fin n ×ₗ Fin n ×ₗ Fin n)
    (fun
      | .sigma a b c => .inlₗ <| .inlₗ (a, b, c)
      | .inside x a b c => .inlₗ <| .inrₗ <| .inlₗ (x, a, b, c)
      | .hole₀ a b c => .inlₗ <| .inrₗ <| .inrₗ (a, b, c)
      | .arc o sz a c d => .inrₗ <| .inlₗ (o, sz, a, c, d)
      | .capF a d e => .inrₗ <| .inrₗ (a, d, e))
    (by rintro ⟨⟩ ⟨⟩ <;> simp <;> rintro ⟨⟩ <;> simp)

def Var.toCode : Var n → String
  | .sigma a b c => s!"0 0 {a} {b} {c}"
  | .inside x a b c => s!"1 {x} {a} {b} {c}"
  | .hole₀ a b c => s!"2 0 {a} {b} {c}"
  | .arc .cw sz a b c => s!"3 {sz} {a} {b} {c}"
  | .arc .ccw sz a b c => s!"4 {sz} {a} {b} {c}"
  | .capF a b c => s!"5 0 {a} {b} {c}"
  | .arc .collinear .. => s!"!"
