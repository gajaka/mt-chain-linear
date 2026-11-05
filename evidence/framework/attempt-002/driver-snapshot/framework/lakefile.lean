import Lake
open Lake DSL

package mtChainFramework where
  leanOptions := #[⟨`autoImplicit, false⟩]
  requiresModuleSystem := true

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "56a005855ea17e0b0958f73ec801ae140b0a1679"

require PPGraph from "../vendor/ppg-lean"

@[default_target]
lean_lib FrameworkAudit where
  roots := #[`FrameworkAudit]
