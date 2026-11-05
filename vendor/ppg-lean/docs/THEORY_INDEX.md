# PPG module inventory

This inventory covers 206 PPG modules and 2,054 explicit theorem/lemma declarations.
Generated theorem constants are counted separately in the whole-library axiom audit.
Counts include structural laws, projections and helper lemmas. See [theorem scope](THEOREM_SCOPE.md).
The `PPGraph` facade and `PPGraph.All` import entry point add no mathematical results.

The complete per-declaration dependency report is [`reports/PPGRAPH_AXIOM_AUDIT.json`](../reports/PPGRAPH_AXIOM_AUDIT.json).
Reproduce it with `python3 tools/audit_ppgraph.py`.
The [module migration table](MODULE_MIGRATION.md) records historical flat imports and later additions.

| Family | Modules | Explicit theorems/lemmas |
| --- | ---: | ---: |
| `Core` | 5 | 62 |
| `Certification` | 8 | 110 |
| `Dependency` | 7 | 46 |
| `Repair` | 8 | 178 |
| `LLL` | 3 | 65 |
| `MoserTardos` | 44 | 388 |
| `Shearer` | 16 | 161 |
| `HLS` | 63 | 425 |
| `Drift` | 1 | 10 |
| `Finite` | 14 | 251 |
| `Decision` | 12 | 129 |
| `Optimization` | 1 | 5 |
| `Integration` | 24 | 224 |
| **Total** | **206** | **2,054** |

| Module | Explicit theorems/lemmas | Direct PPG imports |
| --- | ---: | --- |
| [PPGraph.Certification.AssessmentBridge](../PPGraph/Certification/AssessmentBridge.lean) | 8 | [PPGraph.Certification.Parametric](../PPGraph/Certification/Parametric.lean), [PPGraph.Certification.Blocking](../PPGraph/Certification/Blocking.lean), [PPGraph.Certification.SelfAssessment](../PPGraph/Certification/SelfAssessment.lean) |
| [PPGraph.Certification.Blocking](../PPGraph/Certification/Blocking.lean) | 7 | [PPGraph.Certification.Parametric](../PPGraph/Certification/Parametric.lean) |
| [PPGraph.Certification.EquivBridge](../PPGraph/Certification/EquivBridge.lean) | 4 | [PPGraph.Certification.Parametric](../PPGraph/Certification/Parametric.lean), [PPGraph.Certification.ParametricQuotient](../PPGraph/Certification/ParametricQuotient.lean), [PPGraph.Certification.Selection](../PPGraph/Certification/Selection.lean) |
| [PPGraph.Certification.Parametric](../PPGraph/Certification/Parametric.lean) | 24 | [PPGraph.Core.Graph](../PPGraph/Core/Graph.lean) |
| [PPGraph.Certification.ParametricQuotient](../PPGraph/Certification/ParametricQuotient.lean) | 25 | [PPGraph.Core.Graph](../PPGraph/Core/Graph.lean), [PPGraph.Certification.Parametric](../PPGraph/Certification/Parametric.lean), [PPGraph.Core.Categorical](../PPGraph/Core/Categorical.lean) |
| [PPGraph.Certification.QuotientBridge](../PPGraph/Certification/QuotientBridge.lean) | 7 | [PPGraph.Core.Graph](../PPGraph/Core/Graph.lean), [PPGraph.Certification.Parametric](../PPGraph/Certification/Parametric.lean), [PPGraph.Certification.ParametricQuotient](../PPGraph/Certification/ParametricQuotient.lean), [PPGraph.Core.Categorical](../PPGraph/Core/Categorical.lean) |
| [PPGraph.Certification.Selection](../PPGraph/Certification/Selection.lean) | 23 | [PPGraph.Core.Graph](../PPGraph/Core/Graph.lean), [PPGraph.Core.Categorical](../PPGraph/Core/Categorical.lean), [PPGraph.Certification.Parametric](../PPGraph/Certification/Parametric.lean) |
| [PPGraph.Certification.SelfAssessment](../PPGraph/Certification/SelfAssessment.lean) | 12 | [PPGraph.Core.Graph](../PPGraph/Core/Graph.lean), [PPGraph.Core.Repair](../PPGraph/Core/Repair.lean) |
| [PPGraph.Core.Categorical](../PPGraph/Core/Categorical.lean) | 10 | [PPGraph.Core.Graph](../PPGraph/Core/Graph.lean) |
| [PPGraph.Core.Graph](../PPGraph/Core/Graph.lean) | 22 | — |
| [PPGraph.Core.Meta](../PPGraph/Core/Meta.lean) | 12 | [PPGraph.Core.Graph](../PPGraph/Core/Graph.lean), [PPGraph.Core.RR](../PPGraph/Core/RR.lean) |
| [PPGraph.Core.RR](../PPGraph/Core/RR.lean) | 9 | [PPGraph.Core.Graph](../PPGraph/Core/Graph.lean) |
| [PPGraph.Core.Repair](../PPGraph/Core/Repair.lean) | 9 | [PPGraph.Core.Graph](../PPGraph/Core/Graph.lean) |
| [PPGraph.Decision.Abstraction](../PPGraph/Decision/Abstraction.lean) | 22 | [PPGraph.Decision.ReachabilityRefutation](../PPGraph/Decision/ReachabilityRefutation.lean) |
| [PPGraph.Decision.CertifiedDecision](../PPGraph/Decision/CertifiedDecision.lean) | 6 | [PPGraph.Decision.RepairDecision](../PPGraph/Decision/RepairDecision.lean) |
| [PPGraph.Decision.CorrectionDuality](../PPGraph/Decision/CorrectionDuality.lean) | 5 | [PPGraph.Decision.UnsatisfiableCore](../PPGraph/Decision/UnsatisfiableCore.lean) |
| [PPGraph.Decision.FarkasCertificate](../PPGraph/Decision/FarkasCertificate.lean) | 7 | [PPGraph.Decision.Infeasibility](../PPGraph/Decision/Infeasibility.lean) |
| [PPGraph.Decision.FiniteCore](../PPGraph/Decision/FiniteCore.lean) | 3 | [PPGraph.Decision.FiniteFeasibility](../PPGraph/Decision/FiniteFeasibility.lean), [PPGraph.Decision.UnsatisfiableCore](../PPGraph/Decision/UnsatisfiableCore.lean) |
| [PPGraph.Decision.FiniteFeasibility](../PPGraph/Decision/FiniteFeasibility.lean) | 13 | [PPGraph.Decision.Infeasibility](../PPGraph/Decision/Infeasibility.lean) |
| [PPGraph.Decision.Infeasibility](../PPGraph/Decision/Infeasibility.lean) | 14 | [PPGraph.Core.Repair](../PPGraph/Core/Repair.lean) |
| [PPGraph.Decision.InfeasibilityCounting](../PPGraph/Decision/InfeasibilityCounting.lean) | 10 | [PPGraph.Decision.FiniteFeasibility](../PPGraph/Decision/FiniteFeasibility.lean) |
| [PPGraph.Decision.ReachabilityRefutation](../PPGraph/Decision/ReachabilityRefutation.lean) | 12 | [PPGraph.Decision.Infeasibility](../PPGraph/Decision/Infeasibility.lean) |
| [PPGraph.Decision.RepairDecision](../PPGraph/Decision/RepairDecision.lean) | 13 | [PPGraph.Decision.FiniteFeasibility](../PPGraph/Decision/FiniteFeasibility.lean) |
| [PPGraph.Decision.Undecidability](../PPGraph/Decision/Undecidability.lean) | 14 | [PPGraph.Decision.ReachabilityRefutation](../PPGraph/Decision/ReachabilityRefutation.lean) |
| [PPGraph.Decision.UnsatisfiableCore](../PPGraph/Decision/UnsatisfiableCore.lean) | 10 | [PPGraph.Decision.Infeasibility](../PPGraph/Decision/Infeasibility.lean) |
| [PPGraph.Dependency.Cost](../PPGraph/Dependency/Cost.lean) | 5 | [PPGraph.Dependency.Decomposition](../PPGraph/Dependency/Decomposition.lean) |
| [PPGraph.Dependency.Count](../PPGraph/Dependency/Count.lean) | 6 | [PPGraph.Dependency.Decomposition](../PPGraph/Dependency/Decomposition.lean), [PPGraph.Dependency.Laplacian](../PPGraph/Dependency/Laplacian.lean) |
| [PPGraph.Dependency.Decomposition](../PPGraph/Dependency/Decomposition.lean) | 13 | [PPGraph.Dependency.Probabilistic](../PPGraph/Dependency/Probabilistic.lean) |
| [PPGraph.Dependency.Laplacian](../PPGraph/Dependency/Laplacian.lean) | 9 | [PPGraph.Dependency.Decomposition](../PPGraph/Dependency/Decomposition.lean) |
| [PPGraph.Dependency.Matrix](../PPGraph/Dependency/Matrix.lean) | 3 | [PPGraph.Dependency.Probabilistic](../PPGraph/Dependency/Probabilistic.lean) |
| [PPGraph.Dependency.Partition](../PPGraph/Dependency/Partition.lean) | 4 | [PPGraph.Dependency.Decomposition](../PPGraph/Dependency/Decomposition.lean) |
| [PPGraph.Dependency.Probabilistic](../PPGraph/Dependency/Probabilistic.lean) | 6 | — |
| [PPGraph.Drift.Additive](../PPGraph/Drift/Additive.lean) | 10 | — |
| [PPGraph.Finite.Drift.Basic](../PPGraph/Finite/Drift/Basic.lean) | 17 | [PPGraph.Drift.Additive](../PPGraph/Drift/Additive.lean) |
| [PPGraph.Finite.Drift.Process](../PPGraph/Finite/Drift/Process.lean) | 20 | [PPGraph.Finite.Drift.Basic](../PPGraph/Finite/Drift/Basic.lean) |
| [PPGraph.Finite.Lumping.Basic](../PPGraph/Finite/Lumping/Basic.lean) | 15 | [PPGraph.Finite.Potential.TailCertificate](../PPGraph/Finite/Potential/TailCertificate.lean) |
| [PPGraph.Finite.Lumping.Update](../PPGraph/Finite/Lumping/Update.lean) | 25 | [PPGraph.Finite.Lumping.Basic](../PPGraph/Finite/Lumping/Basic.lean), [PPGraph.Finite.Update.IID](../PPGraph/Finite/Update/IID.lean) |
| [PPGraph.Finite.Potential.Basic](../PPGraph/Finite/Potential/Basic.lean) | 27 | [PPGraph.Finite.Drift.Basic](../PPGraph/Finite/Drift/Basic.lean) |
| [PPGraph.Finite.Potential.Expectation](../PPGraph/Finite/Potential/Expectation.lean) | 19 | [PPGraph.Finite.Potential.Basic](../PPGraph/Finite/Potential/Basic.lean), [PPGraph.Finite.Drift.Process](../PPGraph/Finite/Drift/Process.lean) |
| [PPGraph.Finite.Potential.Refutation](../PPGraph/Finite/Potential/Refutation.lean) | 10 | [PPGraph.Finite.Potential.Basic](../PPGraph/Finite/Potential/Basic.lean) |
| [PPGraph.Finite.Potential.Tail](../PPGraph/Finite/Potential/Tail.lean) | 23 | [PPGraph.Finite.Potential.Expectation](../PPGraph/Finite/Potential/Expectation.lean), [PPGraph.Finite.Potential.Refutation](../PPGraph/Finite/Potential/Refutation.lean) |
| [PPGraph.Finite.Potential.TailCertificate](../PPGraph/Finite/Potential/TailCertificate.lean) | 4 | [PPGraph.Finite.Potential.Tail](../PPGraph/Finite/Potential/Tail.lean) |
| [PPGraph.Finite.Resampling.Basic](../PPGraph/Finite/Resampling/Basic.lean) | 31 | [PPGraph.Finite.Update.IID](../PPGraph/Finite/Update/IID.lean), [PPGraph.MoserTardos.Process.Process](../PPGraph/MoserTardos/Process/Process.lean) |
| [PPGraph.Finite.Resampling.Table](../PPGraph/Finite/Resampling/Table.lean) | 19 | [PPGraph.Finite.Resampling.Basic](../PPGraph/Finite/Resampling/Basic.lean), [PPGraph.MoserTardos.Process.RandomTrajectory](../PPGraph/MoserTardos/Process/RandomTrajectory.lean) |
| [PPGraph.Finite.Resampling.TableLaw](../PPGraph/Finite/Resampling/TableLaw.lean) | 10 | [PPGraph.Finite.Resampling.Table](../PPGraph/Finite/Resampling/Table.lean), [PPGraph.MoserTardos.Probability.Probability](../PPGraph/MoserTardos/Probability/Probability.lean) |
| [PPGraph.Finite.Update.Basic](../PPGraph/Finite/Update/Basic.lean) | 16 | [PPGraph.Finite.Drift.Process](../PPGraph/Finite/Drift/Process.lean) |
| [PPGraph.Finite.Update.IID](../PPGraph/Finite/Update/IID.lean) | 15 | [PPGraph.Finite.Update.Basic](../PPGraph/Finite/Update/Basic.lean) |
| [PPGraph.HLS.Bounds.AugmentedExistence](../PPGraph/HLS/Bounds/AugmentedExistence.lean) | 2 | [PPGraph.HLS.DAG.OrientationScore](../PPGraph/HLS/DAG/OrientationScore.lean), [PPGraph.HLS.Encoding.PrefixCheck](../PPGraph/HLS/Encoding/PrefixCheck.lean) |
| [PPGraph.HLS.Bounds.ChoiceSum](../PPGraph/HLS/Bounds/ChoiceSum.lean) | 2 | [PPGraph.HLS.Bounds.ExpansionWeight](../PPGraph/HLS/Bounds/ExpansionWeight.lean) |
| [PPGraph.HLS.Bounds.CoinSaving](../PPGraph/HLS/Bounds/CoinSaving.lean) | 9 | [PPGraph.MoserTardos.Probability.Intersection](../PPGraph/MoserTardos/Probability/Intersection.lean), [PPGraph.HLS.Parameters](../PPGraph/HLS/Parameters.lean) |
| [PPGraph.HLS.Bounds.DecoratedBudget](../PPGraph/HLS/Bounds/DecoratedBudget.lean) | 6 | [PPGraph.HLS.Bounds.WitnessBudget](../PPGraph/HLS/Bounds/WitnessBudget.lean), [PPGraph.HLS.DAG.Matching](../PPGraph/HLS/DAG/Matching.lean) |
| [PPGraph.HLS.Bounds.ExpansionWeight](../PPGraph/HLS/Bounds/ExpansionWeight.lean) | 4 | [PPGraph.HLS.Encoding.ExpansionFamily](../PPGraph/HLS/Encoding/ExpansionFamily.lean) |
| [PPGraph.HLS.Bounds.Expectation](../PPGraph/HLS/Bounds/Expectation.lean) | 8 | [PPGraph.HLS.Probability.RefinedProbability](../PPGraph/HLS/Probability/RefinedProbability.lean), [PPGraph.HLS.Probability.RootUnion](../PPGraph/HLS/Probability/RootUnion.lean), [PPGraph.MoserTardos.Bounds.Termination](../PPGraph/MoserTardos/Bounds/Termination.lean) |
| [PPGraph.HLS.Bounds.OrdinalOccurrence](../PPGraph/HLS/Bounds/OrdinalOccurrence.lean) | 6 | [PPGraph.HLS.DAG.RealDAGCounts](../PPGraph/HLS/DAG/RealDAGCounts.lean), [PPGraph.MoserTardos.Witness.Occurrence](../PPGraph/MoserTardos/Witness/Occurrence.lean) |
| [PPGraph.HLS.Bounds.ProductDiscount](../PPGraph/HLS/Bounds/ProductDiscount.lean) | 7 | [PPGraph.HLS.Bounds.RefinedBudget](../PPGraph/HLS/Bounds/RefinedBudget.lean) |
| [PPGraph.HLS.Bounds.RefinedBudget](../PPGraph/HLS/Bounds/RefinedBudget.lean) | 4 | [PPGraph.HLS.Bounds.ChoiceSum](../PPGraph/HLS/Bounds/ChoiceSum.lean) |
| [PPGraph.HLS.Bounds.WitnessBudget](../PPGraph/HLS/Bounds/WitnessBudget.lean) | 7 | [PPGraph.HLS.Encoding.CanonicalEncoding](../PPGraph/HLS/Encoding/CanonicalEncoding.lean), [PPGraph.Shearer.Slack](../PPGraph/Shearer/Slack.lean) |
| [PPGraph.HLS.DAG.CliqueRanks](../PPGraph/HLS/DAG/CliqueRanks.lean) | 12 | [PPGraph.HLS.Encoding.Normalization](../PPGraph/HLS/Encoding/Normalization.lean), [PPGraph.HLS.DAG.Matching](../PPGraph/HLS/DAG/Matching.lean) |
| [PPGraph.HLS.DAG.ExpansionGraph](../PPGraph/HLS/DAG/ExpansionGraph.lean) | 8 | [PPGraph.HLS.DAG.ExpansionVertices](../PPGraph/HLS/DAG/ExpansionVertices.lean), [PPGraph.HLS.Encoding.Normalization](../PPGraph/HLS/Encoding/Normalization.lean) |
| [PPGraph.HLS.DAG.ExpansionVertices](../PPGraph/HLS/DAG/ExpansionVertices.lean) | 7 | [PPGraph.HLS.Encoding.ExpansionDecoder](../PPGraph/HLS/Encoding/ExpansionDecoder.lean), [PPGraph.HLS.DAG.TopologicalOrder](../PPGraph/HLS/DAG/TopologicalOrder.lean), [PPGraph.HLS.DAG.OrderedDAG](../PPGraph/HLS/DAG/OrderedDAG.lean) |
| [PPGraph.HLS.DAG.FiniteDAG](../PPGraph/HLS/DAG/FiniteDAG.lean) | 6 | [PPGraph.HLS.Encoding.Normalization](../PPGraph/HLS/Encoding/Normalization.lean) |
| [PPGraph.HLS.DAG.Matching](../PPGraph/HLS/DAG/Matching.lean) | 13 | [PPGraph.HLS.Parameters](../PPGraph/HLS/Parameters.lean) |
| [PPGraph.HLS.DAG.MatchingArcUniqueness](../PPGraph/HLS/DAG/MatchingArcUniqueness.lean) | 1 | [PPGraph.HLS.DAG.PairKeys](../PPGraph/HLS/DAG/PairKeys.lean) |
| [PPGraph.HLS.DAG.MatchingSelection](../PPGraph/HLS/DAG/MatchingSelection.lean) | 15 | [PPGraph.HLS.DAG.ParitySelection](../PPGraph/HLS/DAG/ParitySelection.lean), [PPGraph.HLS.DAG.PairKeys](../PPGraph/HLS/DAG/PairKeys.lean) |
| [PPGraph.HLS.DAG.OrderedDAG](../PPGraph/HLS/DAG/OrderedDAG.lean) | 5 | [PPGraph.HLS.DAG.WitnessDAG](../PPGraph/HLS/DAG/WitnessDAG.lean) |
| [PPGraph.HLS.DAG.OrientationScore](../PPGraph/HLS/DAG/OrientationScore.lean) | 4 | [PPGraph.HLS.DAG.PairKeys](../PPGraph/HLS/DAG/PairKeys.lean), [PPGraph.HLS.DAG.FiniteDAG](../PPGraph/HLS/DAG/FiniteDAG.lean) |
| [PPGraph.HLS.DAG.PairKeys](../PPGraph/HLS/DAG/PairKeys.lean) | 6 | [PPGraph.HLS.DAG.CliqueRanks](../PPGraph/HLS/DAG/CliqueRanks.lean) |
| [PPGraph.HLS.DAG.ParitySelection](../PPGraph/HLS/DAG/ParitySelection.lean) | 6 | [PPGraph.HLS.DAG.CliqueRanks](../PPGraph/HLS/DAG/CliqueRanks.lean) |
| [PPGraph.HLS.DAG.RealDAG](../PPGraph/HLS/DAG/RealDAG.lean) | 10 | [PPGraph.HLS.DAG.TimeDAG](../PPGraph/HLS/DAG/TimeDAG.lean), [PPGraph.HLS.Encoding.PrefixCheck](../PPGraph/HLS/Encoding/PrefixCheck.lean), [PPGraph.HLS.Bounds.WitnessBudget](../PPGraph/HLS/Bounds/WitnessBudget.lean), [PPGraph.MoserTardos.Probability.RandomInitExpectation](../PPGraph/MoserTardos/Probability/RandomInitExpectation.lean) |
| [PPGraph.HLS.DAG.RealDAGCounts](../PPGraph/HLS/DAG/RealDAGCounts.lean) | 8 | [PPGraph.HLS.DAG.RealDAG](../PPGraph/HLS/DAG/RealDAG.lean) |
| [PPGraph.HLS.DAG.TimeDAG](../PPGraph/HLS/DAG/TimeDAG.lean) | 7 | [PPGraph.HLS.Encoding.NormalizationCheck](../PPGraph/HLS/Encoding/NormalizationCheck.lean) |
| [PPGraph.HLS.DAG.TopologicalOrder](../PPGraph/HLS/DAG/TopologicalOrder.lean) | 7 | [PPGraph.HLS.DAG.WitnessLayers](../PPGraph/HLS/DAG/WitnessLayers.lean) |
| [PPGraph.HLS.DAG.WitnessDAG](../PPGraph/HLS/DAG/WitnessDAG.lean) | 15 | [PPGraph.HLS.Encoding.Reversal](../PPGraph/HLS/Encoding/Reversal.lean) |
| [PPGraph.HLS.DAG.WitnessLayers](../PPGraph/HLS/DAG/WitnessLayers.lean) | 14 | [PPGraph.HLS.DAG.WitnessDAG](../PPGraph/HLS/DAG/WitnessDAG.lean), [PPGraph.Shearer.Stable](../PPGraph/Shearer/Stable.lean) |
| [PPGraph.HLS.Encoding.CanonicalEncoding](../PPGraph/HLS/Encoding/CanonicalEncoding.lean) | 9 | [PPGraph.HLS.Encoding.StableEncoding](../PPGraph/HLS/Encoding/StableEncoding.lean) |
| [PPGraph.HLS.Encoding.ChoiceRecovery](../PPGraph/HLS/Encoding/ChoiceRecovery.lean) | 4 | [PPGraph.HLS.Encoding.OriginalIso](../PPGraph/HLS/Encoding/OriginalIso.lean), [PPGraph.HLS.DAG.MatchingArcUniqueness](../PPGraph/HLS/DAG/MatchingArcUniqueness.lean) |
| [PPGraph.HLS.Encoding.ColoredExpansion](../PPGraph/HLS/Encoding/ColoredExpansion.lean) | 8 | [PPGraph.HLS.Encoding.OriginRecovery](../PPGraph/HLS/Encoding/OriginRecovery.lean), [PPGraph.HLS.Encoding.NormalizationReversal](../PPGraph/HLS/Encoding/NormalizationReversal.lean) |
| [PPGraph.HLS.Encoding.ExpansionDecoder](../PPGraph/HLS/Encoding/ExpansionDecoder.lean) | 4 | [PPGraph.HLS.DAG.PairKeys](../PPGraph/HLS/DAG/PairKeys.lean) |
| [PPGraph.HLS.Encoding.ExpansionFamily](../PPGraph/HLS/Encoding/ExpansionFamily.lean) | 4 | [PPGraph.HLS.Encoding.ChoiceRecovery](../PPGraph/HLS/Encoding/ChoiceRecovery.lean), [PPGraph.HLS.Bounds.DecoratedBudget](../PPGraph/HLS/Bounds/DecoratedBudget.lean) |
| [PPGraph.HLS.Encoding.ExpansionReversibility](../PPGraph/HLS/Encoding/ExpansionReversibility.lean) | 5 | [PPGraph.HLS.DAG.ExpansionGraph](../PPGraph/HLS/DAG/ExpansionGraph.lean), [PPGraph.HLS.Encoding.OrderedReversal](../PPGraph/HLS/Encoding/OrderedReversal.lean) |
| [PPGraph.HLS.Encoding.LabelRanks](../PPGraph/HLS/Encoding/LabelRanks.lean) | 10 | [PPGraph.HLS.Encoding.CanonicalEncoding](../PPGraph/HLS/Encoding/CanonicalEncoding.lean), [PPGraph.HLS.Encoding.TableCheck](../PPGraph/HLS/Encoding/TableCheck.lean) |
| [PPGraph.HLS.Encoding.NodeIso](../PPGraph/HLS/Encoding/NodeIso.lean) | 5 | [PPGraph.HLS.Encoding.Normalization](../PPGraph/HLS/Encoding/Normalization.lean) |
| [PPGraph.HLS.Encoding.Normalization](../PPGraph/HLS/Encoding/Normalization.lean) | 12 | [PPGraph.HLS.Encoding.LabelRanks](../PPGraph/HLS/Encoding/LabelRanks.lean) |
| [PPGraph.HLS.Encoding.NormalizationCheck](../PPGraph/HLS/Encoding/NormalizationCheck.lean) | 5 | [PPGraph.HLS.Encoding.Normalization](../PPGraph/HLS/Encoding/Normalization.lean), [PPGraph.HLS.Encoding.TableCheck](../PPGraph/HLS/Encoding/TableCheck.lean) |
| [PPGraph.HLS.Encoding.NormalizationReversal](../PPGraph/HLS/Encoding/NormalizationReversal.lean) | 3 | [PPGraph.HLS.Encoding.Normalization](../PPGraph/HLS/Encoding/Normalization.lean) |
| [PPGraph.HLS.Encoding.OrderedReversal](../PPGraph/HLS/Encoding/OrderedReversal.lean) | 2 | [PPGraph.HLS.DAG.OrderedDAG](../PPGraph/HLS/DAG/OrderedDAG.lean) |
| [PPGraph.HLS.Encoding.OriginRecovery](../PPGraph/HLS/Encoding/OriginRecovery.lean) | 5 | [PPGraph.HLS.Encoding.ExpansionReversibility](../PPGraph/HLS/Encoding/ExpansionReversibility.lean), [PPGraph.HLS.DAG.MatchingSelection](../PPGraph/HLS/DAG/MatchingSelection.lean) |
| [PPGraph.HLS.Encoding.OriginalIso](../PPGraph/HLS/Encoding/OriginalIso.lean) | 4 | [PPGraph.HLS.Encoding.ColoredExpansion](../PPGraph/HLS/Encoding/ColoredExpansion.lean), [PPGraph.HLS.Encoding.NodeIso](../PPGraph/HLS/Encoding/NodeIso.lean) |
| [PPGraph.HLS.Encoding.PrefixCheck](../PPGraph/HLS/Encoding/PrefixCheck.lean) | 8 | [PPGraph.HLS.Encoding.ReversalSlots](../PPGraph/HLS/Encoding/ReversalSlots.lean) |
| [PPGraph.HLS.Encoding.RelativeCoins](../PPGraph/HLS/Encoding/RelativeCoins.lean) | 6 | [PPGraph.HLS.Probability.AugmentedSpace](../PPGraph/HLS/Probability/AugmentedSpace.lean), [PPGraph.HLS.DAG.PairKeys](../PPGraph/HLS/DAG/PairKeys.lean) |
| [PPGraph.HLS.Encoding.Reversal](../PPGraph/HLS/Encoding/Reversal.lean) | 9 | — |
| [PPGraph.HLS.Encoding.ReversalSlots](../PPGraph/HLS/Encoding/ReversalSlots.lean) | 10 | [PPGraph.HLS.Encoding.TableCheck](../PPGraph/HLS/Encoding/TableCheck.lean) |
| [PPGraph.HLS.Encoding.StableEncoding](../PPGraph/HLS/Encoding/StableEncoding.lean) | 14 | [PPGraph.HLS.DAG.WitnessLayers](../PPGraph/HLS/DAG/WitnessLayers.lean) |
| [PPGraph.HLS.Encoding.SwappedTests](../PPGraph/HLS/Encoding/SwappedTests.lean) | 3 | [PPGraph.HLS.Encoding.PrefixCheck](../PPGraph/HLS/Encoding/PrefixCheck.lean) |
| [PPGraph.HLS.Encoding.TableCheck](../PPGraph/HLS/Encoding/TableCheck.lean) | 11 | [PPGraph.HLS.DAG.WitnessDAG](../PPGraph/HLS/DAG/WitnessDAG.lean), [PPGraph.Shearer.BDD](../PPGraph/Shearer/BDD.lean), [PPGraph.MoserTardos.Probability.Probability](../PPGraph/MoserTardos/Probability/Probability.lean) |
| [PPGraph.HLS.Parameters](../PPGraph/HLS/Parameters.lean) | 12 | — |
| [PPGraph.HLS.Probability.AugmentedCoordinates](../PPGraph/HLS/Probability/AugmentedCoordinates.lean) | 5 | [PPGraph.HLS.Probability.AugmentedSpace](../PPGraph/HLS/Probability/AugmentedSpace.lean), [PPGraph.HLS.DAG.MatchingSelection](../PPGraph/HLS/DAG/MatchingSelection.lean), [PPGraph.HLS.Encoding.TableCheck](../PPGraph/HLS/Encoding/TableCheck.lean) |
| [PPGraph.HLS.Probability.AugmentedDependence](../PPGraph/HLS/Probability/AugmentedDependence.lean) | 4 | [PPGraph.HLS.Probability.AugmentedPair](../PPGraph/HLS/Probability/AugmentedPair.lean), [PPGraph.HLS.Probability.AugmentedCoordinates](../PPGraph/HLS/Probability/AugmentedCoordinates.lean) |
| [PPGraph.HLS.Probability.AugmentedPair](../PPGraph/HLS/Probability/AugmentedPair.lean) | 5 | [PPGraph.HLS.Probability.CoinQueryLaw](../PPGraph/HLS/Probability/CoinQueryLaw.lean), [PPGraph.HLS.Encoding.RelativeCoins](../PPGraph/HLS/Encoding/RelativeCoins.lean), [PPGraph.HLS.Probability.PairProbability](../PPGraph/HLS/Probability/PairProbability.lean), [PPGraph.HLS.Bounds.AugmentedExistence](../PPGraph/HLS/Bounds/AugmentedExistence.lean) |
| [PPGraph.HLS.Probability.AugmentedSpace](../PPGraph/HLS/Probability/AugmentedSpace.lean) | 5 | [PPGraph.HLS.Bounds.CoinSaving](../PPGraph/HLS/Bounds/CoinSaving.lean), [PPGraph.HLS.Probability.QueryLaw](../PPGraph/HLS/Probability/QueryLaw.lean), [PPGraph.MoserTardos.Probability.RandomInitExpectation](../PPGraph/MoserTardos/Probability/RandomInitExpectation.lean) |
| [PPGraph.HLS.Probability.BlockAssembly](../PPGraph/HLS/Probability/BlockAssembly.lean) | 9 | [PPGraph.HLS.Probability.QueryLaw](../PPGraph/HLS/Probability/QueryLaw.lean) |
| [PPGraph.HLS.Probability.BlockIntersection](../PPGraph/HLS/Probability/BlockIntersection.lean) | 3 | [PPGraph.HLS.Probability.BlockAssembly](../PPGraph/HLS/Probability/BlockAssembly.lean), [PPGraph.HLS.Bounds.CoinSaving](../PPGraph/HLS/Bounds/CoinSaving.lean) |
| [PPGraph.HLS.Probability.BlockQueries](../PPGraph/HLS/Probability/BlockQueries.lean) | 4 | [PPGraph.HLS.Probability.FootprintBlocks](../PPGraph/HLS/Probability/FootprintBlocks.lean), [PPGraph.HLS.Encoding.ReversalSlots](../PPGraph/HLS/Encoding/ReversalSlots.lean) |
| [PPGraph.HLS.Probability.CoinQueryLaw](../PPGraph/HLS/Probability/CoinQueryLaw.lean) | 1 | [PPGraph.HLS.Probability.AugmentedSpace](../PPGraph/HLS/Probability/AugmentedSpace.lean) |
| [PPGraph.HLS.Probability.FootprintBlocks](../PPGraph/HLS/Probability/FootprintBlocks.lean) | 9 | [PPGraph.HLS.Probability.BlockIntersection](../PPGraph/HLS/Probability/BlockIntersection.lean) |
| [PPGraph.HLS.Probability.PairProbability](../PPGraph/HLS/Probability/PairProbability.lean) | 5 | [PPGraph.HLS.Probability.BlockQueries](../PPGraph/HLS/Probability/BlockQueries.lean), [PPGraph.HLS.Encoding.SwappedTests](../PPGraph/HLS/Encoding/SwappedTests.lean) |
| [PPGraph.HLS.Probability.QueryLaw](../PPGraph/HLS/Probability/QueryLaw.lean) | 5 | [PPGraph.HLS.Encoding.TableCheck](../PPGraph/HLS/Encoding/TableCheck.lean) |
| [PPGraph.HLS.Probability.RefinedProbability](../PPGraph/HLS/Probability/RefinedProbability.lean) | 3 | [PPGraph.HLS.Probability.UnitChecks](../PPGraph/HLS/Probability/UnitChecks.lean), [PPGraph.HLS.Bounds.ProductDiscount](../PPGraph/HLS/Bounds/ProductDiscount.lean) |
| [PPGraph.HLS.Probability.RootUnion](../PPGraph/HLS/Probability/RootUnion.lean) | 6 | [PPGraph.HLS.Bounds.OrdinalOccurrence](../PPGraph/HLS/Bounds/OrdinalOccurrence.lean), [PPGraph.HLS.Probability.UnitChecks](../PPGraph/HLS/Probability/UnitChecks.lean) |
| [PPGraph.HLS.Probability.UnitChecks](../PPGraph/HLS/Probability/UnitChecks.lean) | 9 | [PPGraph.HLS.Probability.AugmentedDependence](../PPGraph/HLS/Probability/AugmentedDependence.lean) |
| [PPGraph.Integration.AbstractionRepair](../PPGraph/Integration/AbstractionRepair.lean) | 12 | [PPGraph.Decision.Abstraction](../PPGraph/Decision/Abstraction.lean) |
| [PPGraph.Integration.CertificationDependency](../PPGraph/Integration/CertificationDependency.lean) | 10 | [PPGraph.Certification.Blocking](../PPGraph/Certification/Blocking.lean), [PPGraph.Certification.SelfAssessment](../PPGraph/Certification/SelfAssessment.lean), [PPGraph.Dependency.Decomposition](../PPGraph/Dependency/Decomposition.lean) |
| [PPGraph.Integration.CertifiedQuotientExample](../PPGraph/Integration/CertifiedQuotientExample.lean) | 8 | [PPGraph.Certification.QuotientBridge](../PPGraph/Certification/QuotientBridge.lean) |
| [PPGraph.Integration.DependencyInfeasibility](../PPGraph/Integration/DependencyInfeasibility.lean) | 10 | [PPGraph.Dependency.Partition](../PPGraph/Dependency/Partition.lean), [PPGraph.Decision.UnsatisfiableCore](../PPGraph/Decision/UnsatisfiableCore.lean) |
| [PPGraph.Integration.DependencyMoserTardos](../PPGraph/Integration/DependencyMoserTardos.lean) | 2 | [PPGraph.Dependency.Decomposition](../PPGraph/Dependency/Decomposition.lean), [PPGraph.MoserTardos.Process.Process](../PPGraph/MoserTardos/Process/Process.lean) |
| [PPGraph.Integration.FiniteAsciiJson](../PPGraph/Integration/FiniteAsciiJson.lean) | 0 | — |
| [PPGraph.Integration.FiniteMTDrift](../PPGraph/Integration/FiniteMTDrift.lean) | 18 | [PPGraph.Finite.Resampling.TableLaw](../PPGraph/Finite/Resampling/TableLaw.lean), [PPGraph.MoserTardos.Bounds.Drift](../PPGraph/MoserTardos/Bounds/Drift.lean) |
| [PPGraph.Integration.FinitePotentialExpectationMT](../PPGraph/Integration/FinitePotentialExpectationMT.lean) | 7 | [PPGraph.Finite.Potential.Expectation](../PPGraph/Finite/Potential/Expectation.lean), [PPGraph.Integration.FinitePotentialMT](../PPGraph/Integration/FinitePotentialMT.lean) |
| [PPGraph.Integration.FinitePotentialMT](../PPGraph/Integration/FinitePotentialMT.lean) | 15 | [PPGraph.Finite.Potential.Basic](../PPGraph/Finite/Potential/Basic.lean), [PPGraph.Integration.FiniteMTDrift](../PPGraph/Integration/FiniteMTDrift.lean) |
| [PPGraph.Integration.FinitePotentialTailMT](../PPGraph/Integration/FinitePotentialTailMT.lean) | 9 | [PPGraph.Finite.Potential.TailCertificate](../PPGraph/Finite/Potential/TailCertificate.lean), [PPGraph.Integration.FinitePotentialExpectationMT](../PPGraph/Integration/FinitePotentialExpectationMT.lean) |
| [PPGraph.Integration.FiniteReadCertificates](../PPGraph/Integration/FiniteReadCertificates.lean) | 10 | [PPGraph.Integration.CertificationDependency](../PPGraph/Integration/CertificationDependency.lean) |
| [PPGraph.Integration.HLSDecision](../PPGraph/Integration/HLSDecision.lean) | 9 | [PPGraph.Integration.HLSRepair](../PPGraph/Integration/HLSRepair.lean), [PPGraph.Integration.MoserTardosInfeasibility](../PPGraph/Integration/MoserTardosInfeasibility.lean), [PPGraph.Decision.RepairDecision](../PPGraph/Decision/RepairDecision.lean) |
| [PPGraph.Integration.HLSRepair](../PPGraph/Integration/HLSRepair.lean) | 3 | [PPGraph.HLS.Bounds.Expectation](../PPGraph/HLS/Bounds/Expectation.lean), [PPGraph.Integration.MoserTardosRepair](../PPGraph/Integration/MoserTardosRepair.lean) |
| [PPGraph.Integration.IncludeAsciiBytes](../PPGraph/Integration/IncludeAsciiBytes.lean) | 0 | — |
| [PPGraph.Integration.LucesCertificateRepair](../PPGraph/Integration/LucesCertificateRepair.lean) | 16 | [PPGraph.Integration.LucesObservedInputs](../PPGraph/Integration/LucesObservedInputs.lean), [PPGraph.Integration.FiniteAsciiJson](../PPGraph/Integration/FiniteAsciiJson.lean), [PPGraph.Integration.IncludeAsciiBytes](../PPGraph/Integration/IncludeAsciiBytes.lean) |
| [PPGraph.Integration.LucesObservedInputs](../PPGraph/Integration/LucesObservedInputs.lean) | 0 | [PPGraph.Integration.FiniteReadCertificates](../PPGraph/Integration/FiniteReadCertificates.lean) |
| [PPGraph.Integration.MoserTardosDriftRegion](../PPGraph/Integration/MoserTardosDriftRegion.lean) | 8 | [PPGraph.MoserTardos.Process.FullResampling](../PPGraph/MoserTardos/Process/FullResampling.lean), [PPGraph.Shearer.BDD](../PPGraph/Shearer/BDD.lean), [PPGraph.Shearer.Slack](../PPGraph/Shearer/Slack.lean), [PPGraph.HLS.DAG.Matching](../PPGraph/HLS/DAG/Matching.lean) |
| [PPGraph.Integration.MoserTardosInfeasibility](../PPGraph/Integration/MoserTardosInfeasibility.lean) | 9 | [PPGraph.Integration.MoserTardosRepair](../PPGraph/Integration/MoserTardosRepair.lean), [PPGraph.Decision.UnsatisfiableCore](../PPGraph/Decision/UnsatisfiableCore.lean), [PPGraph.Decision.FiniteFeasibility](../PPGraph/Decision/FiniteFeasibility.lean) |
| [PPGraph.Integration.MoserTardosRepair](../PPGraph/Integration/MoserTardosRepair.lean) | 12 | [PPGraph.Core.Repair](../PPGraph/Core/Repair.lean), [PPGraph.MoserTardos.Bounds.ConstantLog](../PPGraph/MoserTardos/Bounds/ConstantLog.lean) |
| [PPGraph.Integration.Policy.HLSCounting](../PPGraph/Integration/Policy/HLSCounting.lean) | 14 | [PPGraph.Integration.Policy.HLSDAG](../PPGraph/Integration/Policy/HLSDAG.lean), [PPGraph.HLS.Probability.RootUnion](../PPGraph/HLS/Probability/RootUnion.lean) |
| [PPGraph.Integration.Policy.HLSDAG](../PPGraph/Integration/Policy/HLSDAG.lean) | 16 | [PPGraph.Integration.Policy.MoserTardos](../PPGraph/Integration/Policy/MoserTardos.lean) |
| [PPGraph.Integration.Policy.HLSExpectation](../PPGraph/Integration/Policy/HLSExpectation.lean) | 13 | [PPGraph.HLS.Probability.RefinedProbability](../PPGraph/HLS/Probability/RefinedProbability.lean), [PPGraph.Integration.Policy.HLSCounting](../PPGraph/Integration/Policy/HLSCounting.lean), [PPGraph.Integration.Policy.History](../PPGraph/Integration/Policy/History.lean) |
| [PPGraph.Integration.Policy.History](../PPGraph/Integration/Policy/History.lean) | 9 | [PPGraph.Integration.Policy.MoserTardos](../PPGraph/Integration/Policy/MoserTardos.lean) |
| [PPGraph.Integration.Policy.MoserTardos](../PPGraph/Integration/Policy/MoserTardos.lean) | 14 | [PPGraph.HLS.DAG.RealDAGCounts](../PPGraph/HLS/DAG/RealDAGCounts.lean), [PPGraph.MoserTardos.Bounds.Termination](../PPGraph/MoserTardos/Bounds/Termination.lean), [PPGraph.MoserTardos.Counting.Counting](../PPGraph/MoserTardos/Counting/Counting.lean) |
| [PPGraph.LLL.General](../PPGraph/LLL/General.lean) | 30 | [PPGraph.Dependency.Probabilistic](../PPGraph/Dependency/Probabilistic.lean) |
| [PPGraph.LLL.Lopsided](../PPGraph/LLL/Lopsided.lean) | 6 | [PPGraph.LLL.General](../PPGraph/LLL/General.lean) |
| [PPGraph.LLL.Variable](../PPGraph/LLL/Variable.lean) | 29 | — |
| [PPGraph.MoserTardos.Bounds.ConstantLog](../PPGraph/MoserTardos/Bounds/ConstantLog.lean) | 9 | [PPGraph.MoserTardos.Bounds.Termination](../PPGraph/MoserTardos/Bounds/Termination.lean) |
| [PPGraph.MoserTardos.Bounds.Convergence](../PPGraph/MoserTardos/Bounds/Convergence.lean) | 2 | [PPGraph.MoserTardos.Witness.Weight](../PPGraph/MoserTardos/Witness/Weight.lean) |
| [PPGraph.MoserTardos.Bounds.Drift](../PPGraph/MoserTardos/Bounds/Drift.lean) | 20 | [PPGraph.Drift.Additive](../PPGraph/Drift/Additive.lean), [PPGraph.Integration.MoserTardosRepair](../PPGraph/Integration/MoserTardosRepair.lean) |
| [PPGraph.MoserTardos.Bounds.DriftCost](../PPGraph/MoserTardos/Bounds/DriftCost.lean) | 6 | [PPGraph.MoserTardos.Bounds.Drift](../PPGraph/MoserTardos/Bounds/Drift.lean) |
| [PPGraph.MoserTardos.Bounds.Expectation](../PPGraph/MoserTardos/Bounds/Expectation.lean) | 4 | [PPGraph.MoserTardos.Witness.Correspondence](../PPGraph/MoserTardos/Witness/Correspondence.lean) |
| [PPGraph.MoserTardos.Bounds.OccurrenceExpectation](../PPGraph/MoserTardos/Bounds/OccurrenceExpectation.lean) | 7 | [PPGraph.MoserTardos.Counting.OccurrenceCounting](../PPGraph/MoserTardos/Counting/OccurrenceCounting.lean), [PPGraph.MoserTardos.Probability.OccurrenceProbability](../PPGraph/MoserTardos/Probability/OccurrenceProbability.lean), [PPGraph.MoserTardos.Witness.WitnessFamily](../PPGraph/MoserTardos/Witness/WitnessFamily.lean) |
| [PPGraph.MoserTardos.Bounds.Pegden](../PPGraph/MoserTardos/Bounds/Pegden.lean) | 44 | [PPGraph.MoserTardos.Bounds.OccurrenceExpectation](../PPGraph/MoserTardos/Bounds/OccurrenceExpectation.lean), [PPGraph.MoserTardos.Witness.LabelsAtDepthBridge](../PPGraph/MoserTardos/Witness/LabelsAtDepthBridge.lean), [PPGraph.Integration.MoserTardosRepair](../PPGraph/Integration/MoserTardosRepair.lean) |
| [PPGraph.MoserTardos.Bounds.Termination](../PPGraph/MoserTardos/Bounds/Termination.lean) | 7 | [PPGraph.MoserTardos.Bounds.OccurrenceExpectation](../PPGraph/MoserTardos/Bounds/OccurrenceExpectation.lean) |
| [PPGraph.MoserTardos.Bounds.WeightSum](../PPGraph/MoserTardos/Bounds/WeightSum.lean) | 16 | [PPGraph.MoserTardos.Witness.Witness](../PPGraph/MoserTardos/Witness/Witness.lean), [PPGraph.MoserTardos.Witness.Weight](../PPGraph/MoserTardos/Witness/Weight.lean), [PPGraph.MoserTardos.Bounds.Convergence](../PPGraph/MoserTardos/Bounds/Convergence.lean) |
| [PPGraph.MoserTardos.Counting.Counting](../PPGraph/MoserTardos/Counting/Counting.lean) | 3 | [PPGraph.MoserTardos.Process.RandomTrajectory](../PPGraph/MoserTardos/Process/RandomTrajectory.lean), [PPGraph.MoserTardos.Witness.Injectivity](../PPGraph/MoserTardos/Witness/Injectivity.lean) |
| [PPGraph.MoserTardos.Counting.OccurrenceCounting](../PPGraph/MoserTardos/Counting/OccurrenceCounting.lean) | 3 | [PPGraph.MoserTardos.Witness.Occurrence](../PPGraph/MoserTardos/Witness/Occurrence.lean) |
| [PPGraph.MoserTardos.Counting.ResamplingCount](../PPGraph/MoserTardos/Counting/ResamplingCount.lean) | 14 | [PPGraph.MoserTardos.Bounds.Expectation](../PPGraph/MoserTardos/Bounds/Expectation.lean), [PPGraph.MoserTardos.Witness.InjectivityBridge](../PPGraph/MoserTardos/Witness/InjectivityBridge.lean) |
| [PPGraph.MoserTardos.Probability.Intersection](../PPGraph/MoserTardos/Probability/Intersection.lean) | 13 | — |
| [PPGraph.MoserTardos.Probability.OccurrenceProbability](../PPGraph/MoserTardos/Probability/OccurrenceProbability.lean) | 4 | [PPGraph.MoserTardos.Witness.Occurrence](../PPGraph/MoserTardos/Witness/Occurrence.lean), [PPGraph.MoserTardos.Witness.CheckBridge](../PPGraph/MoserTardos/Witness/CheckBridge.lean), [PPGraph.MoserTardos.Witness.CheckShape](../PPGraph/MoserTardos/Witness/CheckShape.lean), [PPGraph.MoserTardos.Probability.ProbabilityGeneral](../PPGraph/MoserTardos/Probability/ProbabilityGeneral.lean) |
| [PPGraph.MoserTardos.Probability.PastIndependence](../PPGraph/MoserTardos/Probability/PastIndependence.lean) | 2 | [PPGraph.MoserTardos.Process.RandomTrajectory](../PPGraph/MoserTardos/Process/RandomTrajectory.lean) |
| [PPGraph.MoserTardos.Probability.Probability](../PPGraph/MoserTardos/Probability/Probability.lean) | 15 | [PPGraph.MoserTardos.Witness.Check](../PPGraph/MoserTardos/Witness/Check.lean), [PPGraph.MoserTardos.Witness.CheckBirth](../PPGraph/MoserTardos/Witness/CheckBirth.lean), [PPGraph.MoserTardos.Process.LogSpace](../PPGraph/MoserTardos/Process/LogSpace.lean) |
| [PPGraph.MoserTardos.Probability.ProbabilityGeneral](../PPGraph/MoserTardos/Probability/ProbabilityGeneral.lean) | 6 | [PPGraph.MoserTardos.Witness.CheckBirth](../PPGraph/MoserTardos/Witness/CheckBirth.lean), [PPGraph.MoserTardos.Probability.Probability](../PPGraph/MoserTardos/Probability/Probability.lean) |
| [PPGraph.MoserTardos.Probability.RandomInitExpectation](../PPGraph/MoserTardos/Probability/RandomInitExpectation.lean) | 14 | [PPGraph.MoserTardos.Process.RandomInitialization](../PPGraph/MoserTardos/Process/RandomInitialization.lean), [PPGraph.MoserTardos.Counting.ResamplingCount](../PPGraph/MoserTardos/Counting/ResamplingCount.lean) |
| [PPGraph.MoserTardos.Process.Basic](../PPGraph/MoserTardos/Process/Basic.lean) | 3 | [PPGraph.Dependency.Probabilistic](../PPGraph/Dependency/Probabilistic.lean), [PPGraph.LLL.General](../PPGraph/LLL/General.lean) |
| [PPGraph.MoserTardos.Process.FullResampling](../PPGraph/MoserTardos/Process/FullResampling.lean) | 18 | [PPGraph.MoserTardos.Bounds.Drift](../PPGraph/MoserTardos/Bounds/Drift.lean), [PPGraph.MoserTardos.Probability.Probability](../PPGraph/MoserTardos/Probability/Probability.lean) |
| [PPGraph.MoserTardos.Process.LogSpace](../PPGraph/MoserTardos/Process/LogSpace.lean) | 1 | [PPGraph.MoserTardos.Process.Basic](../PPGraph/MoserTardos/Process/Basic.lean) |
| [PPGraph.MoserTardos.Process.Process](../PPGraph/MoserTardos/Process/Process.lean) | 2 | [PPGraph.MoserTardos.Process.Basic](../PPGraph/MoserTardos/Process/Basic.lean) |
| [PPGraph.MoserTardos.Process.RandomInitialization](../PPGraph/MoserTardos/Process/RandomInitialization.lean) | 3 | [PPGraph.MoserTardos.Process.RandomTrajectory](../PPGraph/MoserTardos/Process/RandomTrajectory.lean) |
| [PPGraph.MoserTardos.Process.RandomTrajectory](../PPGraph/MoserTardos/Process/RandomTrajectory.lean) | 10 | [PPGraph.MoserTardos.Process.LogSpace](../PPGraph/MoserTardos/Process/LogSpace.lean), [PPGraph.MoserTardos.Process.Process](../PPGraph/MoserTardos/Process/Process.lean) |
| [PPGraph.MoserTardos.Witness.Canonical](../PPGraph/MoserTardos/Witness/Canonical.lean) | 15 | [PPGraph.MoserTardos.Bounds.WeightSum](../PPGraph/MoserTardos/Bounds/WeightSum.lean) |
| [PPGraph.MoserTardos.Witness.Check](../PPGraph/MoserTardos/Witness/Check.lean) | 1 | [PPGraph.MoserTardos.Witness.CheckOrder](../PPGraph/MoserTardos/Witness/CheckOrder.lean), [PPGraph.MoserTardos.Process.RandomTrajectory](../PPGraph/MoserTardos/Process/RandomTrajectory.lean) |
| [PPGraph.MoserTardos.Witness.CheckBirth](../PPGraph/MoserTardos/Witness/CheckBirth.lean) | 22 | [PPGraph.MoserTardos.Witness.Check](../PPGraph/MoserTardos/Witness/Check.lean) |
| [PPGraph.MoserTardos.Witness.CheckBridge](../PPGraph/MoserTardos/Witness/CheckBridge.lean) | 2 | [PPGraph.MoserTardos.Witness.CheckShape](../PPGraph/MoserTardos/Witness/CheckShape.lean), [PPGraph.MoserTardos.Witness.RealTree](../PPGraph/MoserTardos/Witness/RealTree.lean), [PPGraph.MoserTardos.Witness.Check](../PPGraph/MoserTardos/Witness/Check.lean) |
| [PPGraph.MoserTardos.Witness.CheckInvariance](../PPGraph/MoserTardos/Witness/CheckInvariance.lean) | 5 | [PPGraph.MoserTardos.Witness.Check](../PPGraph/MoserTardos/Witness/Check.lean), [PPGraph.MoserTardos.Witness.InjectivityBridge](../PPGraph/MoserTardos/Witness/InjectivityBridge.lean) |
| [PPGraph.MoserTardos.Witness.CheckOrder](../PPGraph/MoserTardos/Witness/CheckOrder.lean) | 14 | [PPGraph.MoserTardos.Witness.Growing](../PPGraph/MoserTardos/Witness/Growing.lean) |
| [PPGraph.MoserTardos.Witness.CheckShape](../PPGraph/MoserTardos/Witness/CheckShape.lean) | 8 | [PPGraph.MoserTardos.Witness.CheckInvariance](../PPGraph/MoserTardos/Witness/CheckInvariance.lean), [PPGraph.MoserTardos.Witness.Check](../PPGraph/MoserTardos/Witness/Check.lean) |
| [PPGraph.MoserTardos.Witness.Correspondence](../PPGraph/MoserTardos/Witness/Correspondence.lean) | 9 | [PPGraph.MoserTardos.Witness.CheckBirth](../PPGraph/MoserTardos/Witness/CheckBirth.lean), [PPGraph.MoserTardos.Process.RandomTrajectory](../PPGraph/MoserTardos/Process/RandomTrajectory.lean) |
| [PPGraph.MoserTardos.Witness.Growing](../PPGraph/MoserTardos/Witness/Growing.lean) | 8 | [PPGraph.MoserTardos.Witness.Witness](../PPGraph/MoserTardos/Witness/Witness.lean) |
| [PPGraph.MoserTardos.Witness.Injectivity](../PPGraph/MoserTardos/Witness/Injectivity.lean) | 14 | [PPGraph.MoserTardos.Witness.Growing](../PPGraph/MoserTardos/Witness/Growing.lean) |
| [PPGraph.MoserTardos.Witness.InjectivityBridge](../PPGraph/MoserTardos/Witness/InjectivityBridge.lean) | 7 | [PPGraph.MoserTardos.Witness.RealTree](../PPGraph/MoserTardos/Witness/RealTree.lean), [PPGraph.MoserTardos.Witness.Canonical](../PPGraph/MoserTardos/Witness/Canonical.lean), [PPGraph.MoserTardos.Witness.Injectivity](../PPGraph/MoserTardos/Witness/Injectivity.lean) |
| [PPGraph.MoserTardos.Witness.LabelsAtDepthBridge](../PPGraph/MoserTardos/Witness/LabelsAtDepthBridge.lean) | 5 | [PPGraph.MoserTardos.Witness.CheckInvariance](../PPGraph/MoserTardos/Witness/CheckInvariance.lean), [PPGraph.MoserTardos.Witness.WTreeToGrowingTree](../PPGraph/MoserTardos/Witness/WTreeToGrowingTree.lean) |
| [PPGraph.MoserTardos.Witness.Occurrence](../PPGraph/MoserTardos/Witness/Occurrence.lean) | 7 | [PPGraph.MoserTardos.Probability.RandomInitExpectation](../PPGraph/MoserTardos/Probability/RandomInitExpectation.lean), [PPGraph.MoserTardos.Witness.WTreeCountable](../PPGraph/MoserTardos/Witness/WTreeCountable.lean) |
| [PPGraph.MoserTardos.Witness.RealTree](../PPGraph/MoserTardos/Witness/RealTree.lean) | 13 | [PPGraph.MoserTardos.Bounds.WeightSum](../PPGraph/MoserTardos/Bounds/WeightSum.lean), [PPGraph.MoserTardos.Witness.CheckBirth](../PPGraph/MoserTardos/Witness/CheckBirth.lean), [PPGraph.MoserTardos.Witness.CheckOrder](../PPGraph/MoserTardos/Witness/CheckOrder.lean) |
| [PPGraph.MoserTardos.Witness.ToGrowingTreeCheckBridge](../PPGraph/MoserTardos/Witness/ToGrowingTreeCheckBridge.lean) | 6 | [PPGraph.MoserTardos.Witness.WTreeToGrowingTree](../PPGraph/MoserTardos/Witness/WTreeToGrowingTree.lean), [PPGraph.MoserTardos.Witness.CheckInvariance](../PPGraph/MoserTardos/Witness/CheckInvariance.lean), [PPGraph.MoserTardos.Witness.CheckShape](../PPGraph/MoserTardos/Witness/CheckShape.lean), [PPGraph.MoserTardos.Witness.Check](../PPGraph/MoserTardos/Witness/Check.lean) |
| [PPGraph.MoserTardos.Witness.WTreeCountable](../PPGraph/MoserTardos/Witness/WTreeCountable.lean) | 1 | [PPGraph.MoserTardos.Witness.Witness](../PPGraph/MoserTardos/Witness/Witness.lean) |
| [PPGraph.MoserTardos.Witness.WTreeToGrowingTree](../PPGraph/MoserTardos/Witness/WTreeToGrowingTree.lean) | 11 | [PPGraph.MoserTardos.Witness.Growing](../PPGraph/MoserTardos/Witness/Growing.lean), [PPGraph.MoserTardos.Witness.Witness](../PPGraph/MoserTardos/Witness/Witness.lean), [PPGraph.MoserTardos.Witness.CheckOrder](../PPGraph/MoserTardos/Witness/CheckOrder.lean) |
| [PPGraph.MoserTardos.Witness.Weight](../PPGraph/MoserTardos/Witness/Weight.lean) | 3 | [PPGraph.MoserTardos.Witness.Witness](../PPGraph/MoserTardos/Witness/Witness.lean) |
| [PPGraph.MoserTardos.Witness.Witness](../PPGraph/MoserTardos/Witness/Witness.lean) | 5 | [PPGraph.MoserTardos.Process.Process](../PPGraph/MoserTardos/Process/Process.lean) |
| [PPGraph.MoserTardos.Witness.WitnessFamily](../PPGraph/MoserTardos/Witness/WitnessFamily.lean) | 6 | [PPGraph.MoserTardos.Bounds.WeightSum](../PPGraph/MoserTardos/Bounds/WeightSum.lean), [PPGraph.MoserTardos.Bounds.Convergence](../PPGraph/MoserTardos/Bounds/Convergence.lean) |
| [PPGraph.Optimization.ComplementarySlackness](../PPGraph/Optimization/ComplementarySlackness.lean) | 5 | — |
| [PPGraph.Repair.HazardExamples](../PPGraph/Repair/HazardExamples.lean) | 13 | [PPGraph.Repair.Hazards](../PPGraph/Repair/Hazards.lean) |
| [PPGraph.Repair.Hazards](../PPGraph/Repair/Hazards.lean) | 23 | [PPGraph.Dependency.Decomposition](../PPGraph/Dependency/Decomposition.lean) |
| [PPGraph.Repair.ObservableAlgebra](../PPGraph/Repair/ObservableAlgebra.lean) | 31 | [PPGraph.Repair.Hazards](../PPGraph/Repair/Hazards.lean) |
| [PPGraph.Repair.ObservableExamples](../PPGraph/Repair/ObservableExamples.lean) | 14 | [PPGraph.Repair.ObservableKernel](../PPGraph/Repair/ObservableKernel.lean) |
| [PPGraph.Repair.ObservableKernel](../PPGraph/Repair/ObservableKernel.lean) | 10 | [PPGraph.Repair.ObservableAlgebra](../PPGraph/Repair/ObservableAlgebra.lean), [PPGraph.Finite.Lumping.Basic](../PPGraph/Finite/Lumping/Basic.lean) |
| [PPGraph.Repair.ObservableSchemes](../PPGraph/Repair/ObservableSchemes.lean) | 34 | [PPGraph.Repair.ObservableAlgebra](../PPGraph/Repair/ObservableAlgebra.lean) |
| [PPGraph.Repair.SemanticHazardExamples](../PPGraph/Repair/SemanticHazardExamples.lean) | 26 | [PPGraph.Repair.SemanticHazards](../PPGraph/Repair/SemanticHazards.lean) |
| [PPGraph.Repair.SemanticHazards](../PPGraph/Repair/SemanticHazards.lean) | 27 | [PPGraph.Repair.Hazards](../PPGraph/Repair/Hazards.lean) |
| [PPGraph.Shearer.BDD](../PPGraph/Shearer/BDD.lean) | 4 | [PPGraph.Shearer.Polynomial](../PPGraph/Shearer/Polynomial.lean), [PPGraph.Dependency.Decomposition](../PPGraph/Dependency/Decomposition.lean) |
| [PPGraph.Shearer.BDDBudget](../PPGraph/Shearer/BDDBudget.lean) | 8 | [PPGraph.Shearer.Stable](../PPGraph/Shearer/Stable.lean), [PPGraph.Shearer.BDD](../PPGraph/Shearer/BDD.lean) |
| [PPGraph.Shearer.BDDExpectation](../PPGraph/Shearer/BDDExpectation.lean) | 9 | [PPGraph.Dependency.Partition](../PPGraph/Dependency/Partition.lean), [PPGraph.Shearer.BDDBudget](../PPGraph/Shearer/BDDBudget.lean), [PPGraph.Shearer.ComponentOccurrence](../PPGraph/Shearer/ComponentOccurrence.lean) |
| [PPGraph.Shearer.Basic](../PPGraph/Shearer/Basic.lean) | 9 | [PPGraph.Shearer.Polynomial](../PPGraph/Shearer/Polynomial.lean), [PPGraph.Shearer.Induction](../PPGraph/Shearer/Induction.lean), [PPGraph.LLL.Lopsided](../PPGraph/LLL/Lopsided.lean), [PPGraph.Shearer.BDD](../PPGraph/Shearer/BDD.lean) |
| [PPGraph.Shearer.ComponentOccurrence](../PPGraph/Shearer/ComponentOccurrence.lean) | 6 | [PPGraph.Shearer.Expectation](../PPGraph/Shearer/Expectation.lean) |
| [PPGraph.Shearer.Expectation](../PPGraph/Shearer/Expectation.lean) | 9 | [PPGraph.Shearer.SequenceProbability](../PPGraph/Shearer/SequenceProbability.lean), [PPGraph.MoserTardos.Bounds.Termination](../PPGraph/MoserTardos/Bounds/Termination.lean), [PPGraph.LLL.General](../PPGraph/LLL/General.lean) |
| [PPGraph.Shearer.Induction](../PPGraph/Shearer/Induction.lean) | 5 | — |
| [PPGraph.Shearer.LayerProfile](../PPGraph/Shearer/LayerProfile.lean) | 11 | [PPGraph.Shearer.Witness](../PPGraph/Shearer/Witness.lean) |
| [PPGraph.Shearer.MT](../PPGraph/Shearer/MT.lean) | 7 | [PPGraph.Shearer.Basic](../PPGraph/Shearer/Basic.lean), [PPGraph.Integration.MoserTardosRepair](../PPGraph/Integration/MoserTardosRepair.lean), [PPGraph.MoserTardos.Probability.Probability](../PPGraph/MoserTardos/Probability/Probability.lean) |
| [PPGraph.Shearer.Occurrence](../PPGraph/Shearer/Occurrence.lean) | 10 | [PPGraph.Shearer.LayerProfile](../PPGraph/Shearer/LayerProfile.lean), [PPGraph.MoserTardos.Witness.Occurrence](../PPGraph/MoserTardos/Witness/Occurrence.lean) |
| [PPGraph.Shearer.Polynomial](../PPGraph/Shearer/Polynomial.lean) | 14 | — |
| [PPGraph.Shearer.SequenceProbability](../PPGraph/Shearer/SequenceProbability.lean) | 8 | [PPGraph.MoserTardos.Probability.ProbabilityGeneral](../PPGraph/MoserTardos/Probability/ProbabilityGeneral.lean), [PPGraph.MoserTardos.Probability.OccurrenceProbability](../PPGraph/MoserTardos/Probability/OccurrenceProbability.lean), [PPGraph.Shearer.Occurrence](../PPGraph/Shearer/Occurrence.lean) |
| [PPGraph.Shearer.Slack](../PPGraph/Shearer/Slack.lean) | 10 | [PPGraph.Shearer.Stable](../PPGraph/Shearer/Stable.lean) |
| [PPGraph.Shearer.SlackExpectation](../PPGraph/Shearer/SlackExpectation.lean) | 2 | [PPGraph.Shearer.Slack](../PPGraph/Shearer/Slack.lean), [PPGraph.Shearer.Expectation](../PPGraph/Shearer/Expectation.lean) |
| [PPGraph.Shearer.Stable](../PPGraph/Shearer/Stable.lean) | 37 | [PPGraph.Shearer.Polynomial](../PPGraph/Shearer/Polynomial.lean) |
| [PPGraph.Shearer.Witness](../PPGraph/Shearer/Witness.lean) | 12 | [PPGraph.Shearer.Stable](../PPGraph/Shearer/Stable.lean), [PPGraph.Shearer.BDD](../PPGraph/Shearer/BDD.lean), [PPGraph.MoserTardos.Witness.LabelsAtDepthBridge](../PPGraph/MoserTardos/Witness/LabelsAtDepthBridge.lean) |
