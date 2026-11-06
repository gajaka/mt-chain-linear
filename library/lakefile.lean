import Lake
open Lake DSL

package originalMTLibrary where
  leanOptions := #[⟨`autoImplicit, false⟩]
  requiresModuleSystem := true
  packagesDir := "../.lake/packages"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "56a005855ea17e0b0958f73ec801ae140b0a1679"

lean_lib PPGraph where
  srcDir := "."
  roots := #[`PPGraph, `PPGraph.All]
  globs := #[.andSubmodules `PPGraph]

@[default_target]
lean_lib GenericMT where
  srcDir := "."
  roots := #[`GenericMT]
