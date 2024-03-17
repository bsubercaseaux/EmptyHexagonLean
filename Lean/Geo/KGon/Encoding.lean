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
  .guard (a < b) fun _ =>
  .forAll (Fin n) fun c =>
  .guard (b < c) fun _ =>
  .forAll (Fin n) fun d =>
  .guard (c < d) fun _ =>
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
  .guard (a < b) fun _ =>
  .forAll (Fin n) fun c =>
  .guard (b < c) fun _ =>
  .forAll (Fin n) fun d =>
  .guard (c < d) fun _ =>
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
  .guard (a < b) fun _ =>
  .forAll (Fin n) fun c =>
  .guard (b < c) fun _ =>
  .forAll (Fin n) fun i =>
  .flatCNF <| .all #[
    -- a < x < b
    .guard (a < i ∧ i < b) fun _ =>
      -- NOTE(Bernardo): Each of those should be expressible as 8 clauses or so
      -- I{i, a, b, c} ↔ ((s{a, b, c} ↔ s{a, i, c}) ∧ (!s{a, i, b} ↔ s{a, b, c}))
      .imp (inside i a b c) (
        .and (.iff (sigma a b c) (sigma a i c)) (.iff (sigma a b c) (.not (sigma a i b))))
  , -- b < i < c
    .guard (b < i ∧ i < c) fun _ =>
      -- I{i, a, b, c} ↔ ((s{a, b, c} ↔ s{a, i, c}) ∧ (!s{b, i, c} ↔ s{a, b, c}))
      .imp (inside i a b c) (
        .and (.iff (sigma a b c) (sigma a i c)) (.iff (sigma a b c) (.not (sigma b i c))))
  ]

def holeDefClauses0 (n : Nat) : PropForm (Var n) :=
  .forAll (Fin n) fun b =>
  .forAll (Fin n) fun c =>
  .guard (b < c) fun _ =>
  .flatCNF <| .imp
    (.forAll (Fin n) fun x =>
      .guard (b < x ∧ x < c) fun _ =>
      Var.sigma b x c)
    (Var.hole₀ 0 b c)

def holeDefClauses1 (n : Nat) : PropForm (Var n) :=
  .forAll (Fin n) fun a =>
  .forAll (Fin n) fun b =>
  .guard (a < b) fun _ =>
  .forAll (Fin n) fun c =>
  .guard (b < c) fun _ =>
  .flatCNF <| .imp
    (.forAll (Fin n) fun i =>
      .guard (a < i ∧ i < c ∧ i ≠ b) fun _ =>
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
  .guard (4 ≤ n) fun _ =>
  revLexClausesCore (n := n-2) ⟨0, by omega⟩ ⟨n - 3, by omega⟩ .true
    (F := fun ⟨a, _⟩ => Var.sigma ⟨a, by omega⟩ ⟨a+1, by omega⟩ ⟨a+2, by omega⟩)

def baseEncoding (n : Nat) (holes : Bool) : PropForm (Var n) :=
  .all #[signotopeClauses1 n, revLexClauses n,
    .guard holes fun _ => .and (insideClauses n) (holeDefClauses1 n)]

def holeIf (holes : Bool) (a b c : Fin n) : PropForm (Var n) :=
  .guard holes fun _ => Var.hole a b c

-- cap a c d:    b  c
--            a ------ d
def capDef (a b c d : Fin n) : PropForm (Var n) :=
  .imp (.and (.not (Var.sigma a b c)) (.not (Var.sigma b c d))) (Var.cap a c d)

def capDef2 (a c d : Fin n) : PropForm (Var n) :=
  .imp (Var.cap a c d) (.not (Var.sigma a c d))

--            a ------ d
-- cup a c d:    b  c
def cupDef (a b c d : Fin n) : PropForm (Var n) :=
  .imp (.and (Var.sigma a b c) (Var.sigma b c d)) (Var.cup a c d)

def cupDef2 (a c d : Fin n) : PropForm (Var n) :=
  .imp (Var.cup a c d) (Var.sigma a c d)

--                .   b
-- capF a c d:            c      (where a-b-d is a hole)
--             a ---------- d
def capFDef (holes : Bool) (a b c d : Fin n) : PropForm (Var n) :=
  .imp (.all #[Var.cap a b c, .not (Var.sigma b c d), holeIf holes a b d]) (Var.capF a c d)

def capDefClauses1 (n : Nat) (holes : Bool) : PropForm (Var n) :=
  .forAll (Fin n) fun a =>
  .forAll (Fin n) fun b =>
  .guard (a < b) fun _ =>
  .forAll (Fin n) fun c =>
  .guard (b < c) fun _ =>
  .forAll (Fin n) fun d =>
  .guard (c < d) fun _ =>
  .flatCNF <| .all #[
    capDef a b c d, cupDef a b c d,
    .guard (a.1+1 < b.1) fun _ => capFDef holes a b c d
  ]

def capDefClauses2 (n : Nat) : PropForm (Var n) :=
  .forAll (Fin n) fun a =>
  .forAll (Fin n) fun c =>
  .guard (a.1+1 < c.1) fun _ =>
  .forAll (Fin n) fun d =>
  .guard (c < d) fun _ =>
  .all #[capDef2 a c d, cupDef2 a c d]

def baseKGonEncoding (n : Nat) (holes : Bool) : PropForm (Var n) :=
  .all #[baseEncoding n holes, capDefClauses1 n holes, capDefClauses2 n]
