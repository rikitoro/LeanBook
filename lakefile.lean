import Lake
open Lake DSL

package "LeanBook" where
  version := v!"0.1.0"

@[default_target]
lean_lib «LeanBook» where
  globs := #[.submodules `LeanBook]
  -- add library configuration options here
