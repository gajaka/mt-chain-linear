import Lake
open Lake DSL

package mtChainLinear where
  leanOptions := #[⟨`autoImplicit, false⟩]
  requiresModuleSystem := true

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "56a005855ea17e0b0958f73ec801ae140b0a1679"

@[default_target]
lean_lib MTCore where
  srcDir := "formal/mt/core"
  roots := #[`ActualScan, `ActualStep, `Chain, `ChainKernel, `ChainLyapunov, `CompletionExpect, `Features, `FilteredKernel, `Filtering, `FinalQuadratic, `FreshDraws, `HistoryFiltering, `Intertwining, `KernelWork, `ObservedFeatures, `PayoffAverages, `PotentialAlgebra, `PotentialTransport, `RefreshDensity, `RegularDrift, `ScanBounds, `StoppedKernel, `TailLaw, `TailScan]

@[default_target]
lean_lib MTTightness where
  srcDir := "formal/mt/tightness"
  roots := #[`ExceptionalBound, `InitialBadMoment, `LinearAsymptotics, `LinearPotential, `LowerBound, `TightnessResults, `UniformScan]

@[default_target]
lean_lib MTPaper where
  srcDir := "formal/mt/paper"
  roots := #[`Accounting, `Barrier]

@[default_target]
lean_lib ThetaAudit where
  srcDir := "formal/theta-audit"
  roots := #[`ThetaIndependentAudit]
