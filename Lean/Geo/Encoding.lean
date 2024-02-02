import LeanSAT
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Range

open LeanSAT Encode VEncCNF

inductive Var (n : Nat)
| sigma  (a b c : Fin n) (hab : a < b) (hbc : b < c)
| inside (x a b c : Fin n) (hab : a < b) (hbc : b < c) (hax : a < x) (hxc : x < c)
| hole   (a b c : Fin n) (hab : a < b) (hbc : b < c)
deriving DecidableEq

instance : Fintype (Var n) := by sorry

def Array.finRange (n : Nat) : Array (Fin n) :=
  List.finRange n |> List.toArray

-- Cayden says TODO: The ↔ axioms for inside are missing, too much work without biImpl VEnc op
def trianglessss {n : Nat} (hn : n ≥ 3) : VEncCNF (Literal (Var n)) Unit ⊤ :=
  for_all (Array.finRange n) (fun a =>
    for_all (Array.finRange n) (fun b =>
      guard (a < b) (fun hab =>
        for_all (Array.finRange n) (fun c =>
          guard (b < c) (fun hbc =>
            -- Cayden notes: For whatever reason, "let" notation isn't allowed in these funs
            --let sabc := LitVar.mkPos <| Var.sigma a b c hab hbc
            --let habc := LitVar.mkPos <| Var.hole  a b c hab hbc
            seq

            -- Signotope axioms
            ( for_all (Array.finRange n) (fun d =>
                guard (c < d) (fun hcd =>
                  seq
                  ( andImply (#[
                      LitVar.mkPos <| Var.sigma a b c hab hbc,
                      LitVar.mkPos <| Var.sigma a c d (lt_trans hab hbc) hcd ])
                    (LitVar.mkPos <| Var.sigma a b d hab (lt_trans hbc hcd)) )
                  ( seq
                  ( andImply (#[
                      LitVar.mkPos <| Var.sigma a b c hab hbc,
                      LitVar.mkPos <| Var.sigma b c d hbc hcd ])
                    (LitVar.mkPos <| Var.sigma a c d (lt_trans hab hbc) hcd) )
                  ( seq
                  ( andImply (#[
                      LitVar.mkNeg <| Var.sigma a b c hab hbc,
                      LitVar.mkNeg <| Var.sigma a c d (lt_trans hab hbc) hcd ])
                    (LitVar.mkNeg <| Var.sigma a b d hab (lt_trans hbc hcd)) )
                  ( andImply (#[
                      LitVar.mkNeg <| Var.sigma a b c hab hbc,
                      LitVar.mkNeg <| Var.sigma b c d hbc hcd ])
                    (LitVar.mkNeg <| Var.sigma a c d (lt_trans hab hbc) hcd) ) ) )
                )
              )
            )

            ( seq

            ( seq
              -- a < x < b
              ( for_all (Array.finRange n) (fun x =>
                  guard (a < x ∧ x < b) (fun haxb =>
                    -- Ix → Habc
                    -- Cayden asks: Have a simple .impl operation?
                    addClause (#[
                      LitVar.mkNeg <| Var.inside x a b c hab hbc haxb.1 (lt_trans haxb.2 hbc),
                      LitVar.mkNeg <| Var.hole a b c hab hbc ] )
                  )
                )
              )

              -- b < x < c
              ( for_all (Array.finRange n) (fun x =>
                  guard (b < x ∧ x < c) (fun hbxc =>
                    -- Ix → Habc
                    -- Cayden asks: Have a simple .impl operation?
                    addClause (#[
                      LitVar.mkNeg <| Var.inside x a b c hab hbc (lt_trans hab hbxc.1) hbxc.2,
                      LitVar.mkNeg <| Var.hole a b c hab hbc ] )
                  )
                )
              )
            )

            -- No holes
            (addClause #[LitVar.mkNeg <| Var.hole a b c hab hbc]) )
          )
        )
      )
    )
  )
  |> mapProp sorry
