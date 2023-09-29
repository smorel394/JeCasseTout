import Lake
open Lake DSL

package «JeCasseTout» where
  -- add any package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «JeCasseTout» where
  -- add any library configuration options here
