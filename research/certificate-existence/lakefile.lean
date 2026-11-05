import Lake
open Lake DSL

package mtCertificateExistence where
  leanOptions := #[⟨`autoImplicit, false⟩]
  requiresModuleSystem := true
  packagesDir := "../../.lake/packages"

require mtChainLinear from "../.."

@[default_target]
lean_lib CertificateStudy where
  srcDir := "formal"
  roots := #[`NeighborAsymptotics, `NeighborBase, `NeighborDual, `NeighborFlux, `NeighborGauge, `NeighborProduct, `NeighborResults, `NeighborTransfer, `NeighborWitness, `SeparableBase, `SeparableProduct, `SeparableSequence, `SeparableWitness, `SeparationResults, `CertificateConstruction, `ExponentialObstruction, `NeighborEmbedding, `CertificateResults]
