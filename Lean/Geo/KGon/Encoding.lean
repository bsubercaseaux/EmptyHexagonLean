import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Range
import Geo.SAT.ToLeanSAT.EncodeProof
import Geo.KGon.Var

namespace Geo

open LeanSAT Var

def signotopeClauses1 (n : Nat) : PropForm (Var n) :=
  -- for all `a`, `b`, `c` with `a < b < c`
  .forAll (Fin n) fun a =>
  .forAll (Fin n) fun b =>
  .impP (a < b) fun _ =>
  .forAll (Fin n) fun c =>
  .impP (b < c) fun _ =>
  .forAll (Fin n) fun d =>
  .impP (c < d) fun _ =>
  .all #[
    -- (s{a, b, c} ∧ s{a, c, d}) → s{a, b, d} -- 1.1
    .imp (.and (sigma a b c) (sigma a c d)) (sigma a b d),
    -- (!s{a, b, c} ∧ !s{a, c, d}) → !s{a, b, d} -- 1.2
    .imp (.and (.not (sigma a b c)) (.not (sigma a c d))) (.not (sigma a b d))
  ]

def signotopeClauses2 (n : Nat) : PropForm (Var n) :=
  -- for all `a`, `b`, `c` with `a < b < c`
  .forAll (Fin n) fun a =>
  .forAll (Fin n) fun b =>
  .impP (a < b) fun _ =>
  .forAll (Fin n) fun c =>
  .impP (b < c) fun _ =>
  .forAll (Fin n) fun d =>
  .impP (c < d) fun _ =>
  .all #[
    -- (s{a, b, c} ∧ s{b, c, d}) → s{a, c, d} -- 2.1
    .imp (.and (sigma a b c) (sigma b c d)) (sigma a c d),
    -- (!s{a, b, c} ∧ !s{b, c, d}) → !s{a, c, d} -- 2.2
    .imp (.and (.not (sigma a b c)) (.not (sigma b c d))) (.not (sigma a c d))
  ]

def insideClauses (n : Nat) : PropForm (Var n) :=
  -- for all `a`, `b`, `c` with `a < b < c`
  .forAll (Fin n) fun a =>
  .forAll (Fin n) fun b =>
  .impP (a < b) fun _ =>
  .forAll (Fin n) fun c =>
  .impP (b < c) fun _ =>
  .forAll (Fin n) fun i =>
  .flatCNF <| .all #[
    -- a < x < b
    .impP (a < i ∧ i < b) fun _ =>
      -- NOTE(Bernardo): Each of those should be expressible as 8 clauses or so
      -- I{i, a, b, c} ↔ ((s{a, b, c} ↔ s{a, i, c}) ∧ (!s{a, i, b} ↔ s{a, b, c}))
      .imp (inside i a b c) (
        .and (.iff (sigma a b c) (sigma a i c)) (.iff (sigma a b c) (.not (sigma a i b))))
  , -- b < i < c
    .impP (b < i ∧ i < c) fun _ =>
      -- I{i, a, b, c} ↔ ((s{a, b, c} ↔ s{a, i, c}) ∧ (!s{b, i, c} ↔ s{a, b, c}))
      .imp (inside i a b c) (
        .and (.iff (sigma a b c) (sigma a i c)) (.iff (sigma a b c) (.not (sigma b i c))))
  ]

def holeDefClauses0 (n : Nat) : PropForm (Var n) :=
  .forAll (Fin n) fun b =>
  .forAll (Fin n) fun c =>
  .impP (b < c) fun _ =>
  .flatCNF <| .imp
    (.forAll (Fin n) fun x =>
      .impP (b < x ∧ x < c) fun _ =>
      Var.sigma b x c)
    (Var.hole₀ 0 b c)

def holeDefClauses1 (n : Nat) : PropForm (Var n) :=
  .forAll (Fin n) fun a =>
  .forAll (Fin n) fun b =>
  .impP (a < b) fun _ =>
  .forAll (Fin n) fun c =>
  .impP (b < c) fun _ =>
  .flatCNF <| .imp
    (.forAll (Fin n) fun i =>
      .impP (a < i ∧ i < c ∧ i ≠ b) fun _ =>
      .not (Var.inside i a b c))
    (Var.hole a b c)

def revLexClausesCore (F : Fin n → PropForm α) (a b : Fin n) (acc : PropForm α) : PropForm α :=
  if h : a < b then
    revLexClausesCore F
        ⟨a + 1, Nat.lt_of_le_of_lt h b.2⟩
        ⟨b - 1, Nat.lt_of_le_of_lt (Nat.sub_le ..) b.2⟩ <|
      .or (.and (F a) (.not (F b))) <|
      .and (.imp (F b) (F a)) acc
  else
    acc

def revLexClauses (n : Nat) : PropForm (Var n) :=
  .impP (4 ≤ n) fun _ =>
  revLexClausesCore (n := n-2) ⟨0, by omega⟩ ⟨n - 3, by omega⟩ .true
    (F := fun ⟨a, _⟩ => Var.sigma ⟨a, by omega⟩ ⟨a+1, by omega⟩ ⟨a+2, by omega⟩)

def baseEncoding (n : Nat) (holes : Bool) : PropForm (Var n) :=
  .all #[signotopeClauses1 n, revLexClauses n,
    .impP holes fun _ => .and (insideClauses n) (holeDefClauses1 n)]

def holeIf (holes : Bool) (a b c : Fin n) : PropForm (Var n) :=
  .impP holes fun _ => Var.hole a b c

def arc (o : Orientation) (sz : Nat) (a b c : Fin n) : PropForm (Var n) :=
  match sz with
  | 0 => match o with
    | .cw => .not (Var.sigma a b c)
    | .ccw => Var.sigma a b c
    | .collinear => .false
  | sz+1 => Var.arc1 o sz a b c

-- cap a c d:    b  c        cup a c d:  a ------ d
--            a ------ d                    b  c
--
-- arc .cw sz a c d:      .·· b  c        sz+3 points total
--                      a --------- d
--
--                      a --------- d
-- arc .ccw sz a c d:     ·.. b  c
--
def arcDefClauses1 (n : Nat) (o : Orientation) (sz : Nat) : PropForm (Var n) :=
  .forAll (Fin n) fun a =>
  .forAll (Fin n) fun b =>
  .impP (a.1+sz < b.1) fun _ =>
  .forAll (Fin n) fun c =>
  .impP (b < c) fun _ =>
  .forAll (Fin n) fun d =>
  .impP (c < d) fun _ =>
  .imp (.and (arc o sz a b c) (arc o 0 b c d)) (Var.arc1 o sz a c d)

def arcDefClauses2 (n : Nat) (o : Orientation) (sz : Nat) : PropForm (Var n) :=
  .forAll (Fin n) fun a =>
  .forAll (Fin n) fun c =>
  .impP (a.1+sz < c.1) fun _ =>
  .forAll (Fin n) fun d =>
  .impP (c < d) fun _ =>
  .imp (Var.arc1 o sz a c d) (arc o sz a c d)

-- ensures `Var.arc1 o i` is defined for 0 <= i < sz  (<= sz+1 intermediate points)
def arcDefClausesUpTo (n : Nat) (o : Orientation) (sz : Nat) : PropForm (Var n) :=
  .forAll (Fin sz) fun ⟨i, _⟩ =>
  .and (arcDefClauses1 n o i) (arcDefClauses2 n o i)

--                .   b
-- capF a c d:            c      (where a-b-d is a hole)
--             a ---------- d
def capFDefClauses (n : Nat) (holes : Bool) : PropForm (Var n) :=
  .forAll (Fin n) fun a =>
  .forAll (Fin n) fun b =>
  .impP (a.1+1 < b.1) fun _ =>
  .forAll (Fin n) fun c =>
  .impP (b < c) fun _ =>
  .forAll (Fin n) fun d =>
  .impP (c < d) fun _ =>
  .imp (.all #[Var.cap a b c, .not (Var.sigma b c d), holeIf holes a b d]) (Var.capF a c d)
