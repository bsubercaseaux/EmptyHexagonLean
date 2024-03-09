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
  "https://github.com/JamesGallicchio/LeanSAT.git" @ "main"

@[default_target]
lean_lib «Geo» where
  -- FIXME: this compiles all the exploratory stuff, remove it once the proof is done
  globs := #[.andSubmodules `Geo]

lean_exe run_geo where
  root := `Geo

lean_exe ngon where
  root := `Geo.NGon.RunEncoding
