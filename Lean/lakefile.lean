import Lake
open Lake DSL

package «geo» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩
  ]
  -- add any additional package configuration options here

require «lean-sat» from git
  "https://github.com/digama0/LeanSAT.git" @ "v4.7.0"

@[default_target]
lean_lib «Geo» where

lean_exe run_geo where
  root := `Geo

lean_exe encode where
  root := `Geo.RunEncoding
