import Lake
open Lake DSL

package "lean_proof_project" where
  -- add package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «LeanProject» where
  -- add library configuration options here
