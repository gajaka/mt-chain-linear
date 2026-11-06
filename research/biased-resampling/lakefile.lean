import Lake
open Lake DSL

package mtBiasedResampling where
  leanOptions := #[⟨`autoImplicit, false⟩]
  requiresModuleSystem := true
  packagesDir := "../../.lake/packages"

require mtChainLinear from "../.."

@[default_target]
lean_lib BiasedResampling where
  srcDir := "formal"
  roots := #[`BiasedDefinitions, `BiasedLaw, `BiasedDrift, `AdaptiveWork,
    `GenericLower, `BiasedLower, `BiasedResults, `BiasedControls, `BiasedAudit]
