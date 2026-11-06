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
  roots := #[
    `PPGraph.Core.Graph,
    `PPGraph.Core.Repair,
    `PPGraph.Dependency.Decomposition,
    `PPGraph.Dependency.Probabilistic,
    `PPGraph.Drift.Additive,
    `PPGraph.Finite.Drift.Basic,
    `PPGraph.Finite.Drift.Process,
    `PPGraph.Finite.Lumping.Basic,
    `PPGraph.Finite.Potential.Basic,
    `PPGraph.Finite.Potential.Expectation,
    `PPGraph.Finite.Potential.Refutation,
    `PPGraph.Finite.Potential.Tail,
    `PPGraph.Finite.Potential.TailCertificate,
    `PPGraph.Integration.MoserTardosRepair,
    `PPGraph.LLL.General,
    `PPGraph.MoserTardos.Bounds.ConstantLog,
    `PPGraph.MoserTardos.Bounds.Convergence,
    `PPGraph.MoserTardos.Bounds.Drift,
    `PPGraph.MoserTardos.Bounds.DriftCost,
    `PPGraph.MoserTardos.Bounds.Expectation,
    `PPGraph.MoserTardos.Bounds.OccurrenceExpectation,
    `PPGraph.MoserTardos.Bounds.Pegden,
    `PPGraph.MoserTardos.Bounds.Termination,
    `PPGraph.MoserTardos.Bounds.WeightSum,
    `PPGraph.MoserTardos.Counting.Counting,
    `PPGraph.MoserTardos.Counting.OccurrenceCounting,
    `PPGraph.MoserTardos.Counting.ResamplingCount,
    `PPGraph.MoserTardos.Probability.Intersection,
    `PPGraph.MoserTardos.Probability.OccurrenceProbability,
    `PPGraph.MoserTardos.Probability.PastIndependence,
    `PPGraph.MoserTardos.Probability.Probability,
    `PPGraph.MoserTardos.Probability.ProbabilityGeneral,
    `PPGraph.MoserTardos.Probability.RandomInitExpectation,
    `PPGraph.MoserTardos.Process.Basic,
    `PPGraph.MoserTardos.Process.FullResampling,
    `PPGraph.MoserTardos.Process.LogSpace,
    `PPGraph.MoserTardos.Process.Process,
    `PPGraph.MoserTardos.Process.RandomInitialization,
    `PPGraph.MoserTardos.Process.RandomTrajectory,
    `PPGraph.MoserTardos.Witness.Canonical,
    `PPGraph.MoserTardos.Witness.Check,
    `PPGraph.MoserTardos.Witness.CheckBirth,
    `PPGraph.MoserTardos.Witness.CheckBridge,
    `PPGraph.MoserTardos.Witness.CheckInvariance,
    `PPGraph.MoserTardos.Witness.CheckOrder,
    `PPGraph.MoserTardos.Witness.CheckShape,
    `PPGraph.MoserTardos.Witness.Correspondence,
    `PPGraph.MoserTardos.Witness.Growing,
    `PPGraph.MoserTardos.Witness.Injectivity,
    `PPGraph.MoserTardos.Witness.InjectivityBridge,
    `PPGraph.MoserTardos.Witness.LabelsAtDepthBridge,
    `PPGraph.MoserTardos.Witness.Occurrence,
    `PPGraph.MoserTardos.Witness.RealTree,
    `PPGraph.MoserTardos.Witness.ToGrowingTreeCheckBridge,
    `PPGraph.MoserTardos.Witness.WTreeCountable,
    `PPGraph.MoserTardos.Witness.WTreeToGrowingTree,
    `PPGraph.MoserTardos.Witness.Weight,
    `PPGraph.MoserTardos.Witness.Witness,
    `PPGraph.MoserTardos.Witness.WitnessFamily,
    `PPGraph.Repair.Hazards,
    `PPGraph.Repair.ObservableAlgebra,
    `PPGraph.Repair.ObservableKernel,
    `PPGraph.Repair.SemanticHazards
  ]

@[default_target]
lean_lib GenericMT where
  srcDir := "."
  roots := #[`GenericMT]
