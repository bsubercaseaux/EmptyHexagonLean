import Geo.Hexagon.Encoding

namespace Geo
open LeanSAT

def holeUnits (n : Nat) : PropForm (Var n) :=
  .forAll (Fin n) fun a =>
  .forAll (Fin n) fun b =>
  .forAll (Fin n) fun c =>
  .guard (a < b ∧ b < c) fun _ => .var (.hole a b c)

/-- `hexagonEncoding` with the holes trivialized.
Can be used to look for convex, not necessarily empty hexagons. -/
def hexagonEncoding' (n : Nat) : PropForm (Var n) :=
  .all #[hexagonEncoding n, holeUnits n]

def hexagonCNF' (rlen : Nat) : ICnf := (hexagonEncoding' rlen |>.toICnf compare).2
