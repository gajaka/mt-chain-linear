/-
  A finite-read instance of the actual LUCES local-plan certificates.

  The runner evaluates the shared JSON comparisons after extracting a finite
  feature snapshot from each coupling. The candidate bank comes from one real
  boot320 transport problem. The exact binary64 ratios are imported separately;
  their numerical extraction is checked by the runner's provenance verifier.

  The proofs below derive locality from syntax and compute a successful repair
  from that bank. They do not assume FamilyLocal or ComponentChecked, and do
  not claim a verified implementation of NumPy, POT or a physical intervention.
-/

module

public import PPGraph.Integration.LucesObservedInputs
public import PPGraph.Integration.FiniteAsciiJson
public meta import PPGraph.Integration.IncludeAsciiBytes

@[expose] public section

namespace LucesCertificateRepair

open FiniteReadCertificates LucesObservedInputs

def decodeRatio : FiniteAsciiJson.Value → Option ℚ
  | .arr [.int n, .int d] => if 0 < d then some ((n : ℚ) / (d : ℚ)) else none
  | _ => none

def decodeField (name : List Nat) : Option Field :=
  if name = FiniteAsciiJson.chars "valid_rows" then some .validRows else
  if name = FiniteAsciiJson.chars "monge_fraction" then some .mongeFraction else
  if name = FiniteAsciiJson.chars "violations" then some .violations else
  if name = FiniteAsciiJson.chars "nnz" then some .nnz else
  if name = FiniteAsciiJson.chars "generator_cos" then some .generatorCos else
  if name = FiniteAsciiJson.chars "dataset_key" then some .datasetKey else none

def decodeCheck (j : FiniteAsciiJson.Value) : Option (Check Field) := do
  let op ← FiniteAsciiJson.get "op" j >>= FiniteAsciiJson.getString
  let name ← FiniteAsciiJson.get "field" j >>= FiniteAsciiJson.getString
  let field ← decodeField name
  let q ← FiniteAsciiJson.get "bound" j >>= decodeRatio
  if op = FiniteAsciiJson.chars "gt" then pure (.neg (.atom .le field q)) else
  if op = FiniteAsciiJson.chars "le" then pure (.atom .le field q) else
  if op = FiniteAsciiJson.chars "eq" then pure (.atom .eq field q) else none

def decodeContract (source : List Nat) : Option (List (Check Field)) := do
  let j ← FiniteAsciiJson.parseBytes source
  let schema ← FiniteAsciiJson.get "schema" j >>= FiniteAsciiJson.getInt
  if schema != 1 then none else do
    let entries ← FiniteAsciiJson.get "certificates" j >>= FiniteAsciiJson.getArray
    entries.mapM decodeCheck

def decodeRows (source : List Nat) : Option (List (List ℚ)) := do
  let j ← FiniteAsciiJson.parseBytes source
  let fields ← FiniteAsciiJson.get "fields" j >>= FiniteAsciiJson.getArray
  let names ← fields.mapM FiniteAsciiJson.getString
  if names != (["valid_rows", "monge_fraction", "violations", "nnz", "generator_cos", "dataset_key"].map FiniteAsciiJson.chars) then none else do
    let rows ← FiniteAsciiJson.get "snapshots" j >>= FiniteAsciiJson.getArray
    rows.mapM (fun row => do
      let values ← FiniteAsciiJson.getArray row
      if values.length = 6 then values.mapM decodeRatio else none)

def contractFileBytes : List Nat := include_ascii_bytes "../../artifacts/luces/local_plan.json"

def observedFileBytes : List Nat := include_ascii_bytes "../../artifacts/luces/local_plan_kernel_inputs.json"

theorem contract_source_bytes : contractFileBytes = contractBytes := rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem contract_source_decodes : decodeContract contractFileBytes = some baseChecks := by
  unfold decodeContract
  rw [contract_source_bytes]
  decide +kernel

set_option maxRecDepth 20000 in
theorem observed_source_bytes : observedFileBytes = kernelBytes := rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem observed_rows_decode : decodeRows observedFileBytes = some snapshotRows := by
  unfold decodeRows
  rw [observed_source_bytes]
  decide +kernel

/-- The conjunction is the runtime local invariant. Repeating the Monge
    comparison keeps a separate certificate position without changing its test. -/
def checks : List (Check Field) := baseChecks ++
  [baseChecks.foldr Check.both .truth, baseChecks[1]!,
    .neg (.atom .le .generatorCos 0), .atom .eq .datasetKey datasetKey]

def F : CertFamily (Field → ℚ) Unit := family checks

def vars : CertVars (CertificationDependency.Index F) Field := footprints checks

def target : CertificationDependency.Index F := ⟨4, by decide⟩

def duplicateMonge : CertificationDependency.Index F := ⟨5, by decide⟩

def generator : CertificationDependency.Index F := ⟨6, by decide⟩

def provenance : CertificationDependency.Index F := ⟨7, by decide⟩

theorem locality_derived : CertificationDependency.FamilyLocal F vars () :=
  family_local checks

theorem target_reads : vars target = {.validRows, .mongeFraction, .violations, .nnz} := by decide +kernel

theorem duplicate_preserved : (indexedCheck checks duplicateMonge) = baseChecks[1]! := by decide +kernel

theorem before_target_fails : ¬ CertificationDependency.holds F () target before := by
  apply (holds_iff_eval checks target before).not.mpr
  decide +kernel

theorem protected_generator_before : CertificationDependency.holds F () generator before := by
  apply (holds_iff_eval checks generator before).mpr
  decide +kernel

theorem protected_provenance_before : CertificationDependency.holds F () provenance before := by
  apply (holds_iff_eval checks provenance before).mpr
  decide +kernel

set_option maxRecDepth 10000 in
theorem finite_search_selects_candidate : search checks (vars target) before bank = some after := by decide +kernel

theorem selected_candidate_in_bank : after ∈ bank :=
  search_mem checks (vars target) before after bank finite_search_selects_candidate

theorem component_check_derived :
    CertificationDependency.ComponentChecked F vars () target before after :=
  search_component_checked checks target before after bank finite_search_selects_candidate

theorem selected_repair_restores_and_preserves :
    CertificationDependency.holds F () target after ∧
      ∀ C ∈ F.certs, C before () → C after () :=
  search_preserves_and_restores checks target before after bank finite_search_selects_candidate

theorem selected_repair_fully_certifies : fully_certified F after () :=
  (search_sound checks (vars target) before after bank finite_search_selects_candidate).2

theorem generator_and_provenance_fixed :
    before .generatorCos = after .generatorCos ∧ before .datasetKey = after .datasetKey := by decide +kernel

end LucesCertificateRepair

#check LucesCertificateRepair.contract_source_bytes
#check LucesCertificateRepair.contract_source_decodes
#check LucesCertificateRepair.observed_source_bytes
#check LucesCertificateRepair.observed_rows_decode
#check LucesCertificateRepair.locality_derived
#check LucesCertificateRepair.target_reads
#check LucesCertificateRepair.duplicate_preserved
#check LucesCertificateRepair.before_target_fails
#check LucesCertificateRepair.protected_generator_before
#check LucesCertificateRepair.protected_provenance_before
#check LucesCertificateRepair.finite_search_selects_candidate
#check LucesCertificateRepair.selected_candidate_in_bank
#check LucesCertificateRepair.component_check_derived
#check LucesCertificateRepair.selected_repair_restores_and_preserves
#check LucesCertificateRepair.selected_repair_fully_certifies
#check LucesCertificateRepair.generator_and_provenance_fixed
