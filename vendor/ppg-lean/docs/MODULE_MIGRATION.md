# Module migration

The 2026-10-25 reorganization moved 191 theory modules into subject directories
under `PPGraph/`. It changed source paths and import names while preserving public
declaration names, namespaces, theorem statements, proof bodies and mathematical
references. That inventory contained 1,824 explicitly declared theorems and
lemmas; the entry points below add no mathematical results.

Use the canonical import in the table when updating a downstream project.
`import PPGraph` remains available for the core graph theory through a small
facade over `PPGraph.Core.Graph`. `import PPGraph.All` imports the complete library,
currently 206 theory modules. The other former flat imports have no compatibility
shims.

For example:

```lean
import PPGraph.Certification.Parametric
```

The [machine-readable map](../tools/module-map.json) records the same mapping.
The [current inventory](THEORY_INDEX.md) records theorem counts and direct
project imports for every canonical module. Source and documentation paths are
relative to the repository: the inventory is in `docs/`, and the theory diagram
is in `assets/`.

Verification on macOS, 2026-10-25 passed a fresh 3,919-job build and the full
axiom audit of 1,824 explicit theorems/lemmas and all 4,893 project declarations.
Imported API comparison conserved 4,755 public and 138 private declarations,
including types, declaration kinds, flags and axiom dependencies. Comparison
permits only the exact module mapping in private-name prefixes and documented
compiler hygiene contexts within binder and universe names. User identifiers,
numeric uniqueness/scope counters, referenced constant names and expression/level
constructors remain intact. Theory source changes are confined to import lines.

| Former import | Canonical import | Source |
| --- | --- | --- |
| `PPGraph` | `PPGraph.Core.Graph` | [PPGraph/Core/Graph.lean](../PPGraph/Core/Graph.lean) |
| `PPGraphAdditiveDrift` | `PPGraph.Drift.Additive` | [PPGraph/Drift/Additive.lean](../PPGraph/Drift/Additive.lean) |
| `PPGraphAssessmentBridge` | `PPGraph.Certification.AssessmentBridge` | [PPGraph/Certification/AssessmentBridge.lean](../PPGraph/Certification/AssessmentBridge.lean) |
| `PPGraphBDD` | `PPGraph.Dependency.Decomposition` | [PPGraph/Dependency/Decomposition.lean](../PPGraph/Dependency/Decomposition.lean) |
| `PPGraphBDDCost` | `PPGraph.Dependency.Cost` | [PPGraph/Dependency/Cost.lean](../PPGraph/Dependency/Cost.lean) |
| `PPGraphBDDCount` | `PPGraph.Dependency.Count` | [PPGraph/Dependency/Count.lean](../PPGraph/Dependency/Count.lean) |
| `PPGraphBDDInfeasibility` | `PPGraph.Integration.DependencyInfeasibility` | [PPGraph/Integration/DependencyInfeasibility.lean](../PPGraph/Integration/DependencyInfeasibility.lean) |
| `PPGraphBDDLaplacian` | `PPGraph.Dependency.Laplacian` | [PPGraph/Dependency/Laplacian.lean](../PPGraph/Dependency/Laplacian.lean) |
| `PPGraphBDDMatrix` | `PPGraph.Dependency.Matrix` | [PPGraph/Dependency/Matrix.lean](../PPGraph/Dependency/Matrix.lean) |
| `PPGraphBDDMoserTardos` | `PPGraph.Integration.DependencyMoserTardos` | [PPGraph/Integration/DependencyMoserTardos.lean](../PPGraph/Integration/DependencyMoserTardos.lean) |
| `PPGraphBDDPartition` | `PPGraph.Dependency.Partition` | [PPGraph/Dependency/Partition.lean](../PPGraph/Dependency/Partition.lean) |
| `PPGraphBlocking` | `PPGraph.Certification.Blocking` | [PPGraph/Certification/Blocking.lean](../PPGraph/Certification/Blocking.lean) |
| `PPGraphCategorical` | `PPGraph.Core.Categorical` | [PPGraph/Core/Categorical.lean](../PPGraph/Core/Categorical.lean) |
| `PPGraphCertifiedDecision` | `PPGraph.Decision.CertifiedDecision` | [PPGraph/Decision/CertifiedDecision.lean](../PPGraph/Decision/CertifiedDecision.lean) |
| `PPGraphComplementarySlackness` | `PPGraph.Optimization.ComplementarySlackness` | [PPGraph/Optimization/ComplementarySlackness.lean](../PPGraph/Optimization/ComplementarySlackness.lean) |
| `PPGraphCorrectionDuality` | `PPGraph.Decision.CorrectionDuality` | [PPGraph/Decision/CorrectionDuality.lean](../PPGraph/Decision/CorrectionDuality.lean) |
| `PPGraphEquivBridge` | `PPGraph.Certification.EquivBridge` | [PPGraph/Certification/EquivBridge.lean](../PPGraph/Certification/EquivBridge.lean) |
| `PPGraphFarkasCertificate` | `PPGraph.Decision.FarkasCertificate` | [PPGraph/Decision/FarkasCertificate.lean](../PPGraph/Decision/FarkasCertificate.lean) |
| `PPGraphFiniteAbstraction` | `PPGraph.Decision.Abstraction` | [PPGraph/Decision/Abstraction.lean](../PPGraph/Decision/Abstraction.lean) |
| `PPGraphFiniteAbstractionRepair` | `PPGraph.Integration.AbstractionRepair` | [PPGraph/Integration/AbstractionRepair.lean](../PPGraph/Integration/AbstractionRepair.lean) |
| `PPGraphFiniteCore` | `PPGraph.Decision.FiniteCore` | [PPGraph/Decision/FiniteCore.lean](../PPGraph/Decision/FiniteCore.lean) |
| `PPGraphFiniteDrift` | `PPGraph.Finite.Drift.Basic` | [PPGraph/Finite/Drift/Basic.lean](../PPGraph/Finite/Drift/Basic.lean) |
| `PPGraphFiniteDriftProcess` | `PPGraph.Finite.Drift.Process` | [PPGraph/Finite/Drift/Process.lean](../PPGraph/Finite/Drift/Process.lean) |
| `PPGraphFiniteFeasibility` | `PPGraph.Decision.FiniteFeasibility` | [PPGraph/Decision/FiniteFeasibility.lean](../PPGraph/Decision/FiniteFeasibility.lean) |
| `PPGraphFiniteLumping` | `PPGraph.Finite.Lumping.Basic` | [PPGraph/Finite/Lumping/Basic.lean](../PPGraph/Finite/Lumping/Basic.lean) |
| `PPGraphFiniteLumpingUpdate` | `PPGraph.Finite.Lumping.Update` | [PPGraph/Finite/Lumping/Update.lean](../PPGraph/Finite/Lumping/Update.lean) |
| `PPGraphFiniteMTDrift` | `PPGraph.Integration.FiniteMTDrift` | [PPGraph/Integration/FiniteMTDrift.lean](../PPGraph/Integration/FiniteMTDrift.lean) |
| `PPGraphFinitePotential` | `PPGraph.Finite.Potential.Basic` | [PPGraph/Finite/Potential/Basic.lean](../PPGraph/Finite/Potential/Basic.lean) |
| `PPGraphFinitePotentialExpectation` | `PPGraph.Finite.Potential.Expectation` | [PPGraph/Finite/Potential/Expectation.lean](../PPGraph/Finite/Potential/Expectation.lean) |
| `PPGraphFinitePotentialExpectationMT` | `PPGraph.Integration.FinitePotentialExpectationMT` | [PPGraph/Integration/FinitePotentialExpectationMT.lean](../PPGraph/Integration/FinitePotentialExpectationMT.lean) |
| `PPGraphFinitePotentialMT` | `PPGraph.Integration.FinitePotentialMT` | [PPGraph/Integration/FinitePotentialMT.lean](../PPGraph/Integration/FinitePotentialMT.lean) |
| `PPGraphFinitePotentialRefutation` | `PPGraph.Finite.Potential.Refutation` | [PPGraph/Finite/Potential/Refutation.lean](../PPGraph/Finite/Potential/Refutation.lean) |
| `PPGraphFinitePotentialTail` | `PPGraph.Finite.Potential.Tail` | [PPGraph/Finite/Potential/Tail.lean](../PPGraph/Finite/Potential/Tail.lean) |
| `PPGraphFinitePotentialTailCertificate` | `PPGraph.Finite.Potential.TailCertificate` | [PPGraph/Finite/Potential/TailCertificate.lean](../PPGraph/Finite/Potential/TailCertificate.lean) |
| `PPGraphFinitePotentialTailMT` | `PPGraph.Integration.FinitePotentialTailMT` | [PPGraph/Integration/FinitePotentialTailMT.lean](../PPGraph/Integration/FinitePotentialTailMT.lean) |
| `PPGraphFiniteResampling` | `PPGraph.Finite.Resampling.Basic` | [PPGraph/Finite/Resampling/Basic.lean](../PPGraph/Finite/Resampling/Basic.lean) |
| `PPGraphFiniteTable` | `PPGraph.Finite.Resampling.Table` | [PPGraph/Finite/Resampling/Table.lean](../PPGraph/Finite/Resampling/Table.lean) |
| `PPGraphFiniteTableLaw` | `PPGraph.Finite.Resampling.TableLaw` | [PPGraph/Finite/Resampling/TableLaw.lean](../PPGraph/Finite/Resampling/TableLaw.lean) |
| `PPGraphFiniteUpdate` | `PPGraph.Finite.Update.Basic` | [PPGraph/Finite/Update/Basic.lean](../PPGraph/Finite/Update/Basic.lean) |
| `PPGraphFiniteUpdateIID` | `PPGraph.Finite.Update.IID` | [PPGraph/Finite/Update/IID.lean](../PPGraph/Finite/Update/IID.lean) |
| `PPGraphHLSAugmentedCoordinates` | `PPGraph.HLS.Probability.AugmentedCoordinates` | [PPGraph/HLS/Probability/AugmentedCoordinates.lean](../PPGraph/HLS/Probability/AugmentedCoordinates.lean) |
| `PPGraphHLSAugmentedDependence` | `PPGraph.HLS.Probability.AugmentedDependence` | [PPGraph/HLS/Probability/AugmentedDependence.lean](../PPGraph/HLS/Probability/AugmentedDependence.lean) |
| `PPGraphHLSAugmentedExistence` | `PPGraph.HLS.Bounds.AugmentedExistence` | [PPGraph/HLS/Bounds/AugmentedExistence.lean](../PPGraph/HLS/Bounds/AugmentedExistence.lean) |
| `PPGraphHLSAugmentedPair` | `PPGraph.HLS.Probability.AugmentedPair` | [PPGraph/HLS/Probability/AugmentedPair.lean](../PPGraph/HLS/Probability/AugmentedPair.lean) |
| `PPGraphHLSAugmentedSpace` | `PPGraph.HLS.Probability.AugmentedSpace` | [PPGraph/HLS/Probability/AugmentedSpace.lean](../PPGraph/HLS/Probability/AugmentedSpace.lean) |
| `PPGraphHLSBlockAssembly` | `PPGraph.HLS.Probability.BlockAssembly` | [PPGraph/HLS/Probability/BlockAssembly.lean](../PPGraph/HLS/Probability/BlockAssembly.lean) |
| `PPGraphHLSBlockIntersection` | `PPGraph.HLS.Probability.BlockIntersection` | [PPGraph/HLS/Probability/BlockIntersection.lean](../PPGraph/HLS/Probability/BlockIntersection.lean) |
| `PPGraphHLSBlockQueries` | `PPGraph.HLS.Probability.BlockQueries` | [PPGraph/HLS/Probability/BlockQueries.lean](../PPGraph/HLS/Probability/BlockQueries.lean) |
| `PPGraphHLSCanonicalEncoding` | `PPGraph.HLS.Encoding.CanonicalEncoding` | [PPGraph/HLS/Encoding/CanonicalEncoding.lean](../PPGraph/HLS/Encoding/CanonicalEncoding.lean) |
| `PPGraphHLSChoiceRecovery` | `PPGraph.HLS.Encoding.ChoiceRecovery` | [PPGraph/HLS/Encoding/ChoiceRecovery.lean](../PPGraph/HLS/Encoding/ChoiceRecovery.lean) |
| `PPGraphHLSChoiceSum` | `PPGraph.HLS.Bounds.ChoiceSum` | [PPGraph/HLS/Bounds/ChoiceSum.lean](../PPGraph/HLS/Bounds/ChoiceSum.lean) |
| `PPGraphHLSCliqueRanks` | `PPGraph.HLS.DAG.CliqueRanks` | [PPGraph/HLS/DAG/CliqueRanks.lean](../PPGraph/HLS/DAG/CliqueRanks.lean) |
| `PPGraphHLSCoinQueryLaw` | `PPGraph.HLS.Probability.CoinQueryLaw` | [PPGraph/HLS/Probability/CoinQueryLaw.lean](../PPGraph/HLS/Probability/CoinQueryLaw.lean) |
| `PPGraphHLSCoinSaving` | `PPGraph.HLS.Bounds.CoinSaving` | [PPGraph/HLS/Bounds/CoinSaving.lean](../PPGraph/HLS/Bounds/CoinSaving.lean) |
| `PPGraphHLSColoredExpansion` | `PPGraph.HLS.Encoding.ColoredExpansion` | [PPGraph/HLS/Encoding/ColoredExpansion.lean](../PPGraph/HLS/Encoding/ColoredExpansion.lean) |
| `PPGraphHLSDecisionBridge` | `PPGraph.Integration.HLSDecision` | [PPGraph/Integration/HLSDecision.lean](../PPGraph/Integration/HLSDecision.lean) |
| `PPGraphHLSDecoratedBudget` | `PPGraph.HLS.Bounds.DecoratedBudget` | [PPGraph/HLS/Bounds/DecoratedBudget.lean](../PPGraph/HLS/Bounds/DecoratedBudget.lean) |
| `PPGraphHLSExpansionDecoder` | `PPGraph.HLS.Encoding.ExpansionDecoder` | [PPGraph/HLS/Encoding/ExpansionDecoder.lean](../PPGraph/HLS/Encoding/ExpansionDecoder.lean) |
| `PPGraphHLSExpansionFamily` | `PPGraph.HLS.Encoding.ExpansionFamily` | [PPGraph/HLS/Encoding/ExpansionFamily.lean](../PPGraph/HLS/Encoding/ExpansionFamily.lean) |
| `PPGraphHLSExpansionGraph` | `PPGraph.HLS.DAG.ExpansionGraph` | [PPGraph/HLS/DAG/ExpansionGraph.lean](../PPGraph/HLS/DAG/ExpansionGraph.lean) |
| `PPGraphHLSExpansionReversibility` | `PPGraph.HLS.Encoding.ExpansionReversibility` | [PPGraph/HLS/Encoding/ExpansionReversibility.lean](../PPGraph/HLS/Encoding/ExpansionReversibility.lean) |
| `PPGraphHLSExpansionVertices` | `PPGraph.HLS.DAG.ExpansionVertices` | [PPGraph/HLS/DAG/ExpansionVertices.lean](../PPGraph/HLS/DAG/ExpansionVertices.lean) |
| `PPGraphHLSExpansionWeight` | `PPGraph.HLS.Bounds.ExpansionWeight` | [PPGraph/HLS/Bounds/ExpansionWeight.lean](../PPGraph/HLS/Bounds/ExpansionWeight.lean) |
| `PPGraphHLSExpectation` | `PPGraph.HLS.Bounds.Expectation` | [PPGraph/HLS/Bounds/Expectation.lean](../PPGraph/HLS/Bounds/Expectation.lean) |
| `PPGraphHLSFiniteDAG` | `PPGraph.HLS.DAG.FiniteDAG` | [PPGraph/HLS/DAG/FiniteDAG.lean](../PPGraph/HLS/DAG/FiniteDAG.lean) |
| `PPGraphHLSFootprintBlocks` | `PPGraph.HLS.Probability.FootprintBlocks` | [PPGraph/HLS/Probability/FootprintBlocks.lean](../PPGraph/HLS/Probability/FootprintBlocks.lean) |
| `PPGraphHLSLabelRanks` | `PPGraph.HLS.Encoding.LabelRanks` | [PPGraph/HLS/Encoding/LabelRanks.lean](../PPGraph/HLS/Encoding/LabelRanks.lean) |
| `PPGraphHLSMatching` | `PPGraph.HLS.DAG.Matching` | [PPGraph/HLS/DAG/Matching.lean](../PPGraph/HLS/DAG/Matching.lean) |
| `PPGraphHLSMatchingArcUniqueness` | `PPGraph.HLS.DAG.MatchingArcUniqueness` | [PPGraph/HLS/DAG/MatchingArcUniqueness.lean](../PPGraph/HLS/DAG/MatchingArcUniqueness.lean) |
| `PPGraphHLSMatchingSelection` | `PPGraph.HLS.DAG.MatchingSelection` | [PPGraph/HLS/DAG/MatchingSelection.lean](../PPGraph/HLS/DAG/MatchingSelection.lean) |
| `PPGraphHLSNodeIso` | `PPGraph.HLS.Encoding.NodeIso` | [PPGraph/HLS/Encoding/NodeIso.lean](../PPGraph/HLS/Encoding/NodeIso.lean) |
| `PPGraphHLSNormalization` | `PPGraph.HLS.Encoding.Normalization` | [PPGraph/HLS/Encoding/Normalization.lean](../PPGraph/HLS/Encoding/Normalization.lean) |
| `PPGraphHLSNormalizationCheck` | `PPGraph.HLS.Encoding.NormalizationCheck` | [PPGraph/HLS/Encoding/NormalizationCheck.lean](../PPGraph/HLS/Encoding/NormalizationCheck.lean) |
| `PPGraphHLSNormalizationReversal` | `PPGraph.HLS.Encoding.NormalizationReversal` | [PPGraph/HLS/Encoding/NormalizationReversal.lean](../PPGraph/HLS/Encoding/NormalizationReversal.lean) |
| `PPGraphHLSOrderedDAG` | `PPGraph.HLS.DAG.OrderedDAG` | [PPGraph/HLS/DAG/OrderedDAG.lean](../PPGraph/HLS/DAG/OrderedDAG.lean) |
| `PPGraphHLSOrderedReversal` | `PPGraph.HLS.Encoding.OrderedReversal` | [PPGraph/HLS/Encoding/OrderedReversal.lean](../PPGraph/HLS/Encoding/OrderedReversal.lean) |
| `PPGraphHLSOrdinalOccurrence` | `PPGraph.HLS.Bounds.OrdinalOccurrence` | [PPGraph/HLS/Bounds/OrdinalOccurrence.lean](../PPGraph/HLS/Bounds/OrdinalOccurrence.lean) |
| `PPGraphHLSOrientationScore` | `PPGraph.HLS.DAG.OrientationScore` | [PPGraph/HLS/DAG/OrientationScore.lean](../PPGraph/HLS/DAG/OrientationScore.lean) |
| `PPGraphHLSOriginRecovery` | `PPGraph.HLS.Encoding.OriginRecovery` | [PPGraph/HLS/Encoding/OriginRecovery.lean](../PPGraph/HLS/Encoding/OriginRecovery.lean) |
| `PPGraphHLSOriginalIso` | `PPGraph.HLS.Encoding.OriginalIso` | [PPGraph/HLS/Encoding/OriginalIso.lean](../PPGraph/HLS/Encoding/OriginalIso.lean) |
| `PPGraphHLSPairKeys` | `PPGraph.HLS.DAG.PairKeys` | [PPGraph/HLS/DAG/PairKeys.lean](../PPGraph/HLS/DAG/PairKeys.lean) |
| `PPGraphHLSPairProbability` | `PPGraph.HLS.Probability.PairProbability` | [PPGraph/HLS/Probability/PairProbability.lean](../PPGraph/HLS/Probability/PairProbability.lean) |
| `PPGraphHLSParameters` | `PPGraph.HLS.Parameters` | [PPGraph/HLS/Parameters.lean](../PPGraph/HLS/Parameters.lean) |
| `PPGraphHLSParitySelection` | `PPGraph.HLS.DAG.ParitySelection` | [PPGraph/HLS/DAG/ParitySelection.lean](../PPGraph/HLS/DAG/ParitySelection.lean) |
| `PPGraphHLSPolicyCounting` | `PPGraph.Integration.Policy.HLSCounting` | [PPGraph/Integration/Policy/HLSCounting.lean](../PPGraph/Integration/Policy/HLSCounting.lean) |
| `PPGraphHLSPolicyDAG` | `PPGraph.Integration.Policy.HLSDAG` | [PPGraph/Integration/Policy/HLSDAG.lean](../PPGraph/Integration/Policy/HLSDAG.lean) |
| `PPGraphHLSPolicyExpectation` | `PPGraph.Integration.Policy.HLSExpectation` | [PPGraph/Integration/Policy/HLSExpectation.lean](../PPGraph/Integration/Policy/HLSExpectation.lean) |
| `PPGraphHLSPrefixCheck` | `PPGraph.HLS.Encoding.PrefixCheck` | [PPGraph/HLS/Encoding/PrefixCheck.lean](../PPGraph/HLS/Encoding/PrefixCheck.lean) |
| `PPGraphHLSProductDiscount` | `PPGraph.HLS.Bounds.ProductDiscount` | [PPGraph/HLS/Bounds/ProductDiscount.lean](../PPGraph/HLS/Bounds/ProductDiscount.lean) |
| `PPGraphHLSQueryLaw` | `PPGraph.HLS.Probability.QueryLaw` | [PPGraph/HLS/Probability/QueryLaw.lean](../PPGraph/HLS/Probability/QueryLaw.lean) |
| `PPGraphHLSRealDAG` | `PPGraph.HLS.DAG.RealDAG` | [PPGraph/HLS/DAG/RealDAG.lean](../PPGraph/HLS/DAG/RealDAG.lean) |
| `PPGraphHLSRealDAGCounts` | `PPGraph.HLS.DAG.RealDAGCounts` | [PPGraph/HLS/DAG/RealDAGCounts.lean](../PPGraph/HLS/DAG/RealDAGCounts.lean) |
| `PPGraphHLSRefinedBudget` | `PPGraph.HLS.Bounds.RefinedBudget` | [PPGraph/HLS/Bounds/RefinedBudget.lean](../PPGraph/HLS/Bounds/RefinedBudget.lean) |
| `PPGraphHLSRefinedProbability` | `PPGraph.HLS.Probability.RefinedProbability` | [PPGraph/HLS/Probability/RefinedProbability.lean](../PPGraph/HLS/Probability/RefinedProbability.lean) |
| `PPGraphHLSRelativeCoins` | `PPGraph.HLS.Encoding.RelativeCoins` | [PPGraph/HLS/Encoding/RelativeCoins.lean](../PPGraph/HLS/Encoding/RelativeCoins.lean) |
| `PPGraphHLSRepairBridge` | `PPGraph.Integration.HLSRepair` | [PPGraph/Integration/HLSRepair.lean](../PPGraph/Integration/HLSRepair.lean) |
| `PPGraphHLSReversal` | `PPGraph.HLS.Encoding.Reversal` | [PPGraph/HLS/Encoding/Reversal.lean](../PPGraph/HLS/Encoding/Reversal.lean) |
| `PPGraphHLSReversalSlots` | `PPGraph.HLS.Encoding.ReversalSlots` | [PPGraph/HLS/Encoding/ReversalSlots.lean](../PPGraph/HLS/Encoding/ReversalSlots.lean) |
| `PPGraphHLSRootUnion` | `PPGraph.HLS.Probability.RootUnion` | [PPGraph/HLS/Probability/RootUnion.lean](../PPGraph/HLS/Probability/RootUnion.lean) |
| `PPGraphHLSStableEncoding` | `PPGraph.HLS.Encoding.StableEncoding` | [PPGraph/HLS/Encoding/StableEncoding.lean](../PPGraph/HLS/Encoding/StableEncoding.lean) |
| `PPGraphHLSSwappedTests` | `PPGraph.HLS.Encoding.SwappedTests` | [PPGraph/HLS/Encoding/SwappedTests.lean](../PPGraph/HLS/Encoding/SwappedTests.lean) |
| `PPGraphHLSTableCheck` | `PPGraph.HLS.Encoding.TableCheck` | [PPGraph/HLS/Encoding/TableCheck.lean](../PPGraph/HLS/Encoding/TableCheck.lean) |
| `PPGraphHLSTimeDAG` | `PPGraph.HLS.DAG.TimeDAG` | [PPGraph/HLS/DAG/TimeDAG.lean](../PPGraph/HLS/DAG/TimeDAG.lean) |
| `PPGraphHLSTopologicalOrder` | `PPGraph.HLS.DAG.TopologicalOrder` | [PPGraph/HLS/DAG/TopologicalOrder.lean](../PPGraph/HLS/DAG/TopologicalOrder.lean) |
| `PPGraphHLSUnitChecks` | `PPGraph.HLS.Probability.UnitChecks` | [PPGraph/HLS/Probability/UnitChecks.lean](../PPGraph/HLS/Probability/UnitChecks.lean) |
| `PPGraphHLSWitnessBudget` | `PPGraph.HLS.Bounds.WitnessBudget` | [PPGraph/HLS/Bounds/WitnessBudget.lean](../PPGraph/HLS/Bounds/WitnessBudget.lean) |
| `PPGraphHLSWitnessDAG` | `PPGraph.HLS.DAG.WitnessDAG` | [PPGraph/HLS/DAG/WitnessDAG.lean](../PPGraph/HLS/DAG/WitnessDAG.lean) |
| `PPGraphHLSWitnessLayers` | `PPGraph.HLS.DAG.WitnessLayers` | [PPGraph/HLS/DAG/WitnessLayers.lean](../PPGraph/HLS/DAG/WitnessLayers.lean) |
| `PPGraphInfeasibility` | `PPGraph.Decision.Infeasibility` | [PPGraph/Decision/Infeasibility.lean](../PPGraph/Decision/Infeasibility.lean) |
| `PPGraphInfeasibilityCounting` | `PPGraph.Decision.InfeasibilityCounting` | [PPGraph/Decision/InfeasibilityCounting.lean](../PPGraph/Decision/InfeasibilityCounting.lean) |
| `PPGraphLLL` | `PPGraph.LLL.General` | [PPGraph/LLL/General.lean](../PPGraph/LLL/General.lean) |
| `PPGraphLopsidedLLL` | `PPGraph.LLL.Lopsided` | [PPGraph/LLL/Lopsided.lean](../PPGraph/LLL/Lopsided.lean) |
| `PPGraphMeta` | `PPGraph.Core.Meta` | [PPGraph/Core/Meta.lean](../PPGraph/Core/Meta.lean) |
| `PPGraphMoserTardos` | `PPGraph.MoserTardos.Process.Basic` | [PPGraph/MoserTardos/Process/Basic.lean](../PPGraph/MoserTardos/Process/Basic.lean) |
| `PPGraphMoserTardosCanonical` | `PPGraph.MoserTardos.Witness.Canonical` | [PPGraph/MoserTardos/Witness/Canonical.lean](../PPGraph/MoserTardos/Witness/Canonical.lean) |
| `PPGraphMoserTardosCheck` | `PPGraph.MoserTardos.Witness.Check` | [PPGraph/MoserTardos/Witness/Check.lean](../PPGraph/MoserTardos/Witness/Check.lean) |
| `PPGraphMoserTardosCheckBirth` | `PPGraph.MoserTardos.Witness.CheckBirth` | [PPGraph/MoserTardos/Witness/CheckBirth.lean](../PPGraph/MoserTardos/Witness/CheckBirth.lean) |
| `PPGraphMoserTardosCheckBridge` | `PPGraph.MoserTardos.Witness.CheckBridge` | [PPGraph/MoserTardos/Witness/CheckBridge.lean](../PPGraph/MoserTardos/Witness/CheckBridge.lean) |
| `PPGraphMoserTardosCheckInvariance` | `PPGraph.MoserTardos.Witness.CheckInvariance` | [PPGraph/MoserTardos/Witness/CheckInvariance.lean](../PPGraph/MoserTardos/Witness/CheckInvariance.lean) |
| `PPGraphMoserTardosCheckOrder` | `PPGraph.MoserTardos.Witness.CheckOrder` | [PPGraph/MoserTardos/Witness/CheckOrder.lean](../PPGraph/MoserTardos/Witness/CheckOrder.lean) |
| `PPGraphMoserTardosCheckShape` | `PPGraph.MoserTardos.Witness.CheckShape` | [PPGraph/MoserTardos/Witness/CheckShape.lean](../PPGraph/MoserTardos/Witness/CheckShape.lean) |
| `PPGraphMoserTardosConstantLog` | `PPGraph.MoserTardos.Bounds.ConstantLog` | [PPGraph/MoserTardos/Bounds/ConstantLog.lean](../PPGraph/MoserTardos/Bounds/ConstantLog.lean) |
| `PPGraphMoserTardosConvergence` | `PPGraph.MoserTardos.Bounds.Convergence` | [PPGraph/MoserTardos/Bounds/Convergence.lean](../PPGraph/MoserTardos/Bounds/Convergence.lean) |
| `PPGraphMoserTardosCorrespondence` | `PPGraph.MoserTardos.Witness.Correspondence` | [PPGraph/MoserTardos/Witness/Correspondence.lean](../PPGraph/MoserTardos/Witness/Correspondence.lean) |
| `PPGraphMoserTardosCounting` | `PPGraph.MoserTardos.Counting.Counting` | [PPGraph/MoserTardos/Counting/Counting.lean](../PPGraph/MoserTardos/Counting/Counting.lean) |
| `PPGraphMoserTardosDrift` | `PPGraph.MoserTardos.Bounds.Drift` | [PPGraph/MoserTardos/Bounds/Drift.lean](../PPGraph/MoserTardos/Bounds/Drift.lean) |
| `PPGraphMoserTardosDriftCost` | `PPGraph.MoserTardos.Bounds.DriftCost` | [PPGraph/MoserTardos/Bounds/DriftCost.lean](../PPGraph/MoserTardos/Bounds/DriftCost.lean) |
| `PPGraphMoserTardosDriftRegion` | `PPGraph.Integration.MoserTardosDriftRegion` | [PPGraph/Integration/MoserTardosDriftRegion.lean](../PPGraph/Integration/MoserTardosDriftRegion.lean) |
| `PPGraphMoserTardosExpectation` | `PPGraph.MoserTardos.Bounds.Expectation` | [PPGraph/MoserTardos/Bounds/Expectation.lean](../PPGraph/MoserTardos/Bounds/Expectation.lean) |
| `PPGraphMoserTardosFullResampling` | `PPGraph.MoserTardos.Process.FullResampling` | [PPGraph/MoserTardos/Process/FullResampling.lean](../PPGraph/MoserTardos/Process/FullResampling.lean) |
| `PPGraphMoserTardosGrowing` | `PPGraph.MoserTardos.Witness.Growing` | [PPGraph/MoserTardos/Witness/Growing.lean](../PPGraph/MoserTardos/Witness/Growing.lean) |
| `PPGraphMoserTardosHistoryPolicy` | `PPGraph.Integration.Policy.History` | [PPGraph/Integration/Policy/History.lean](../PPGraph/Integration/Policy/History.lean) |
| `PPGraphMoserTardosInfeasibility` | `PPGraph.Integration.MoserTardosInfeasibility` | [PPGraph/Integration/MoserTardosInfeasibility.lean](../PPGraph/Integration/MoserTardosInfeasibility.lean) |
| `PPGraphMoserTardosInjectivity` | `PPGraph.MoserTardos.Witness.Injectivity` | [PPGraph/MoserTardos/Witness/Injectivity.lean](../PPGraph/MoserTardos/Witness/Injectivity.lean) |
| `PPGraphMoserTardosInjectivityBridge` | `PPGraph.MoserTardos.Witness.InjectivityBridge` | [PPGraph/MoserTardos/Witness/InjectivityBridge.lean](../PPGraph/MoserTardos/Witness/InjectivityBridge.lean) |
| `PPGraphMoserTardosIntersection` | `PPGraph.MoserTardos.Probability.Intersection` | [PPGraph/MoserTardos/Probability/Intersection.lean](../PPGraph/MoserTardos/Probability/Intersection.lean) |
| `PPGraphMoserTardosLabelsAtDepthBridge` | `PPGraph.MoserTardos.Witness.LabelsAtDepthBridge` | [PPGraph/MoserTardos/Witness/LabelsAtDepthBridge.lean](../PPGraph/MoserTardos/Witness/LabelsAtDepthBridge.lean) |
| `PPGraphMoserTardosLogSpace` | `PPGraph.MoserTardos.Process.LogSpace` | [PPGraph/MoserTardos/Process/LogSpace.lean](../PPGraph/MoserTardos/Process/LogSpace.lean) |
| `PPGraphMoserTardosOccurrence` | `PPGraph.MoserTardos.Witness.Occurrence` | [PPGraph/MoserTardos/Witness/Occurrence.lean](../PPGraph/MoserTardos/Witness/Occurrence.lean) |
| `PPGraphMoserTardosOccurrenceCounting` | `PPGraph.MoserTardos.Counting.OccurrenceCounting` | [PPGraph/MoserTardos/Counting/OccurrenceCounting.lean](../PPGraph/MoserTardos/Counting/OccurrenceCounting.lean) |
| `PPGraphMoserTardosOccurrenceExpectation` | `PPGraph.MoserTardos.Bounds.OccurrenceExpectation` | [PPGraph/MoserTardos/Bounds/OccurrenceExpectation.lean](../PPGraph/MoserTardos/Bounds/OccurrenceExpectation.lean) |
| `PPGraphMoserTardosOccurrenceProbability` | `PPGraph.MoserTardos.Probability.OccurrenceProbability` | [PPGraph/MoserTardos/Probability/OccurrenceProbability.lean](../PPGraph/MoserTardos/Probability/OccurrenceProbability.lean) |
| `PPGraphMoserTardosPastIndependence` | `PPGraph.MoserTardos.Probability.PastIndependence` | [PPGraph/MoserTardos/Probability/PastIndependence.lean](../PPGraph/MoserTardos/Probability/PastIndependence.lean) |
| `PPGraphMoserTardosPegden` | `PPGraph.MoserTardos.Bounds.Pegden` | [PPGraph/MoserTardos/Bounds/Pegden.lean](../PPGraph/MoserTardos/Bounds/Pegden.lean) |
| `PPGraphMoserTardosPolicy` | `PPGraph.Integration.Policy.MoserTardos` | [PPGraph/Integration/Policy/MoserTardos.lean](../PPGraph/Integration/Policy/MoserTardos.lean) |
| `PPGraphMoserTardosProbability` | `PPGraph.MoserTardos.Probability.Probability` | [PPGraph/MoserTardos/Probability/Probability.lean](../PPGraph/MoserTardos/Probability/Probability.lean) |
| `PPGraphMoserTardosProbabilityGeneral` | `PPGraph.MoserTardos.Probability.ProbabilityGeneral` | [PPGraph/MoserTardos/Probability/ProbabilityGeneral.lean](../PPGraph/MoserTardos/Probability/ProbabilityGeneral.lean) |
| `PPGraphMoserTardosProcess` | `PPGraph.MoserTardos.Process.Process` | [PPGraph/MoserTardos/Process/Process.lean](../PPGraph/MoserTardos/Process/Process.lean) |
| `PPGraphMoserTardosRandomInitExpectation` | `PPGraph.MoserTardos.Probability.RandomInitExpectation` | [PPGraph/MoserTardos/Probability/RandomInitExpectation.lean](../PPGraph/MoserTardos/Probability/RandomInitExpectation.lean) |
| `PPGraphMoserTardosRandomInitialization` | `PPGraph.MoserTardos.Process.RandomInitialization` | [PPGraph/MoserTardos/Process/RandomInitialization.lean](../PPGraph/MoserTardos/Process/RandomInitialization.lean) |
| `PPGraphMoserTardosRandomTrajectory` | `PPGraph.MoserTardos.Process.RandomTrajectory` | [PPGraph/MoserTardos/Process/RandomTrajectory.lean](../PPGraph/MoserTardos/Process/RandomTrajectory.lean) |
| `PPGraphMoserTardosRealTree` | `PPGraph.MoserTardos.Witness.RealTree` | [PPGraph/MoserTardos/Witness/RealTree.lean](../PPGraph/MoserTardos/Witness/RealTree.lean) |
| `PPGraphMoserTardosRepairBridge` | `PPGraph.Integration.MoserTardosRepair` | [PPGraph/Integration/MoserTardosRepair.lean](../PPGraph/Integration/MoserTardosRepair.lean) |
| `PPGraphMoserTardosResamplingCount` | `PPGraph.MoserTardos.Counting.ResamplingCount` | [PPGraph/MoserTardos/Counting/ResamplingCount.lean](../PPGraph/MoserTardos/Counting/ResamplingCount.lean) |
| `PPGraphMoserTardosTermination` | `PPGraph.MoserTardos.Bounds.Termination` | [PPGraph/MoserTardos/Bounds/Termination.lean](../PPGraph/MoserTardos/Bounds/Termination.lean) |
| `PPGraphMoserTardosToGrowingTreeCheckBridge` | `PPGraph.MoserTardos.Witness.ToGrowingTreeCheckBridge` | [PPGraph/MoserTardos/Witness/ToGrowingTreeCheckBridge.lean](../PPGraph/MoserTardos/Witness/ToGrowingTreeCheckBridge.lean) |
| `PPGraphMoserTardosWTreeCountable` | `PPGraph.MoserTardos.Witness.WTreeCountable` | [PPGraph/MoserTardos/Witness/WTreeCountable.lean](../PPGraph/MoserTardos/Witness/WTreeCountable.lean) |
| `PPGraphMoserTardosWTreeToGrowingTree` | `PPGraph.MoserTardos.Witness.WTreeToGrowingTree` | [PPGraph/MoserTardos/Witness/WTreeToGrowingTree.lean](../PPGraph/MoserTardos/Witness/WTreeToGrowingTree.lean) |
| `PPGraphMoserTardosWeight` | `PPGraph.MoserTardos.Witness.Weight` | [PPGraph/MoserTardos/Witness/Weight.lean](../PPGraph/MoserTardos/Witness/Weight.lean) |
| `PPGraphMoserTardosWeightSum` | `PPGraph.MoserTardos.Bounds.WeightSum` | [PPGraph/MoserTardos/Bounds/WeightSum.lean](../PPGraph/MoserTardos/Bounds/WeightSum.lean) |
| `PPGraphMoserTardosWitness` | `PPGraph.MoserTardos.Witness.Witness` | [PPGraph/MoserTardos/Witness/Witness.lean](../PPGraph/MoserTardos/Witness/Witness.lean) |
| `PPGraphMoserTardosWitnessFamily` | `PPGraph.MoserTardos.Witness.WitnessFamily` | [PPGraph/MoserTardos/Witness/WitnessFamily.lean](../PPGraph/MoserTardos/Witness/WitnessFamily.lean) |
| `PPGraphParametric` | `PPGraph.Certification.Parametric` | [PPGraph/Certification/Parametric.lean](../PPGraph/Certification/Parametric.lean) |
| `PPGraphParametricQuotient` | `PPGraph.Certification.ParametricQuotient` | [PPGraph/Certification/ParametricQuotient.lean](../PPGraph/Certification/ParametricQuotient.lean) |
| `PPGraphProbabilistic` | `PPGraph.Dependency.Probabilistic` | [PPGraph/Dependency/Probabilistic.lean](../PPGraph/Dependency/Probabilistic.lean) |
| `PPGraphQuotientBridge` | `PPGraph.Certification.QuotientBridge` | [PPGraph/Certification/QuotientBridge.lean](../PPGraph/Certification/QuotientBridge.lean) |
| `PPGraphRR` | `PPGraph.Core.RR` | [PPGraph/Core/RR.lean](../PPGraph/Core/RR.lean) |
| `PPGraphReachabilityRefutation` | `PPGraph.Decision.ReachabilityRefutation` | [PPGraph/Decision/ReachabilityRefutation.lean](../PPGraph/Decision/ReachabilityRefutation.lean) |
| `PPGraphRepair` | `PPGraph.Core.Repair` | [PPGraph/Core/Repair.lean](../PPGraph/Core/Repair.lean) |
| `PPGraphRepairDecision` | `PPGraph.Decision.RepairDecision` | [PPGraph/Decision/RepairDecision.lean](../PPGraph/Decision/RepairDecision.lean) |
| `PPGraphRepairUndecidability` | `PPGraph.Decision.Undecidability` | [PPGraph/Decision/Undecidability.lean](../PPGraph/Decision/Undecidability.lean) |
| `PPGraphSelection` | `PPGraph.Certification.Selection` | [PPGraph/Certification/Selection.lean](../PPGraph/Certification/Selection.lean) |
| `PPGraphSelfAssessment` | `PPGraph.Certification.SelfAssessment` | [PPGraph/Certification/SelfAssessment.lean](../PPGraph/Certification/SelfAssessment.lean) |
| `PPGraphShearer` | `PPGraph.Shearer.Basic` | [PPGraph/Shearer/Basic.lean](../PPGraph/Shearer/Basic.lean) |
| `PPGraphShearerBDD` | `PPGraph.Shearer.BDD` | [PPGraph/Shearer/BDD.lean](../PPGraph/Shearer/BDD.lean) |
| `PPGraphShearerBDDBudget` | `PPGraph.Shearer.BDDBudget` | [PPGraph/Shearer/BDDBudget.lean](../PPGraph/Shearer/BDDBudget.lean) |
| `PPGraphShearerBDDExpectation` | `PPGraph.Shearer.BDDExpectation` | [PPGraph/Shearer/BDDExpectation.lean](../PPGraph/Shearer/BDDExpectation.lean) |
| `PPGraphShearerComponentOccurrence` | `PPGraph.Shearer.ComponentOccurrence` | [PPGraph/Shearer/ComponentOccurrence.lean](../PPGraph/Shearer/ComponentOccurrence.lean) |
| `PPGraphShearerExpectation` | `PPGraph.Shearer.Expectation` | [PPGraph/Shearer/Expectation.lean](../PPGraph/Shearer/Expectation.lean) |
| `PPGraphShearerInduction` | `PPGraph.Shearer.Induction` | [PPGraph/Shearer/Induction.lean](../PPGraph/Shearer/Induction.lean) |
| `PPGraphShearerLayerProfile` | `PPGraph.Shearer.LayerProfile` | [PPGraph/Shearer/LayerProfile.lean](../PPGraph/Shearer/LayerProfile.lean) |
| `PPGraphShearerMT` | `PPGraph.Shearer.MT` | [PPGraph/Shearer/MT.lean](../PPGraph/Shearer/MT.lean) |
| `PPGraphShearerOccurrence` | `PPGraph.Shearer.Occurrence` | [PPGraph/Shearer/Occurrence.lean](../PPGraph/Shearer/Occurrence.lean) |
| `PPGraphShearerPolynomial` | `PPGraph.Shearer.Polynomial` | [PPGraph/Shearer/Polynomial.lean](../PPGraph/Shearer/Polynomial.lean) |
| `PPGraphShearerSequenceProbability` | `PPGraph.Shearer.SequenceProbability` | [PPGraph/Shearer/SequenceProbability.lean](../PPGraph/Shearer/SequenceProbability.lean) |
| `PPGraphShearerSlack` | `PPGraph.Shearer.Slack` | [PPGraph/Shearer/Slack.lean](../PPGraph/Shearer/Slack.lean) |
| `PPGraphShearerSlackExpectation` | `PPGraph.Shearer.SlackExpectation` | [PPGraph/Shearer/SlackExpectation.lean](../PPGraph/Shearer/SlackExpectation.lean) |
| `PPGraphShearerStable` | `PPGraph.Shearer.Stable` | [PPGraph/Shearer/Stable.lean](../PPGraph/Shearer/Stable.lean) |
| `PPGraphShearerWitness` | `PPGraph.Shearer.Witness` | [PPGraph/Shearer/Witness.lean](../PPGraph/Shearer/Witness.lean) |
| `PPGraphUnsatisfiableCore` | `PPGraph.Decision.UnsatisfiableCore` | [PPGraph/Decision/UnsatisfiableCore.lean](../PPGraph/Decision/UnsatisfiableCore.lean) |
| `PPGraphVariableLLL` | `PPGraph.LLL.Variable` | [PPGraph/LLL/Variable.lean](../PPGraph/LLL/Variable.lean) |


## Modules added after the reorganization

`PPGraph.Integration.CertificationDependency` was introduced on 2026-10-28 at
its current path. It has no former flat import. Its source-map `old_path` key
therefore equals its current path; the historical migration table above records
only modules that existed before the reorganization.

The later finite-read integration also added these modules at their current
paths, without old flat imports:

- `Integration.CertifiedQuotientExample`
- `Integration.FiniteReadCertificates`
- `Integration.FiniteAsciiJson`
- `Integration.IncludeAsciiBytes`
- `Integration.LucesObservedInputs`
- `Integration.LucesCertificateRepair`

Their source-map `old_path` keys likewise equal their current paths.

The repair-observable modules added on 2026-10-30 use the following canonical
imports. The flat names identify their earlier source organization; no flat
compatibility shims are installed. These additions are separate from the
191-module directory reorganization and its historical API comparison above.

| Earlier flat name | Canonical import | Source |
| --- | --- | --- |
| `PPGraphRepairHazards` | `PPGraph.Repair.Hazards` | [PPGraph/Repair/Hazards.lean](../PPGraph/Repair/Hazards.lean) |
| `PPGraphRepairHazardExamples` | `PPGraph.Repair.HazardExamples` | [PPGraph/Repair/HazardExamples.lean](../PPGraph/Repair/HazardExamples.lean) |
| `PPGraphRepairSemanticHazards` | `PPGraph.Repair.SemanticHazards` | [PPGraph/Repair/SemanticHazards.lean](../PPGraph/Repair/SemanticHazards.lean) |
| `PPGraphRepairSemanticHazardExamples` | `PPGraph.Repair.SemanticHazardExamples` | [PPGraph/Repair/SemanticHazardExamples.lean](../PPGraph/Repair/SemanticHazardExamples.lean) |
| `PPGraphRepairObservableAlgebra` | `PPGraph.Repair.ObservableAlgebra` | [PPGraph/Repair/ObservableAlgebra.lean](../PPGraph/Repair/ObservableAlgebra.lean) |
| `PPGraphRepairObservableKernel` | `PPGraph.Repair.ObservableKernel` | [PPGraph/Repair/ObservableKernel.lean](../PPGraph/Repair/ObservableKernel.lean) |
| `PPGraphRepairObservableExamples` | `PPGraph.Repair.ObservableExamples` | [PPGraph/Repair/ObservableExamples.lean](../PPGraph/Repair/ObservableExamples.lean) |
| `PPGraphRepairObservableSchemes` | `PPGraph.Repair.ObservableSchemes` | [PPGraph/Repair/ObservableSchemes.lean](../PPGraph/Repair/ObservableSchemes.lean) |

## API corrections on 2026-10-28

Numerical feasibility names now state their scope:

| Earlier name | Current name |
| --- | --- |
| `locally_repairable` | `lll_budget_feasible` |
| `coupled_obstruction` | `lll_budget_infeasible` |
| `repairable_or_coupled` | `lll_budget_feasible_or_infeasible` |
| `finest_quotient_pp_valid` | `finest_quotient_invariant` |

The renamed Selection invariant helper states only endpoint certification.
`finest_quotient_inherits_pp_valid` now proves actual `pp_valid` with a
well-defined quotient RR. `proj_is_pp_morphism` and `proj_is_pp_quotient` conclude
the shared categorical predicates, with explicit invariant/RR descent and edge
noncollapse arguments. Callers must supply these mathematical obligations;
source edges that collapse do not yield edges between distinct quotient nodes.
