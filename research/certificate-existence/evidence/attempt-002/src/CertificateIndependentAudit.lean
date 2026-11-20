module
import all CertificateResults
meta import Lean

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0

/-! Fresh research audit of explicit certificate existence, class-wide bounds,
embedding and same-process summary statements. Every root has an independently
stated expected proposition, and its actual private proof closure is inspected. -/

namespace CertificateIndependentAudit

open Lean Elab Command Meta Term

private meta def roots : Array Name := #[
  ``PotentialSeparation.Construction.certificate_exists,
  ``PotentialSeparation.Construction.pointwise_drift,
  ``NeighborSeparation.Embedding.certificate_exists,
  ``NeighborSeparation.Embedding.certificate_budget_eq,
  ``PotentialSeparation.Exponential.certificate_budget_exponential_lower,
  ``PotentialSeparation.Exponential.certificate_budget_floor_lower,
  ``PotentialSeparation.Construction.initial_budget_upper,
  ``CertificateStudy.nonvacuous_separable_separation,
  ``CertificateStudy.nonvacuous_neighbor_separation]

private meta def allowedAxioms : Array Name :=
  #[``propext, ``Classical.choice, ``Quot.sound]

private meta def namesJson (names : Array Name) : Json :=
  toJson (names.map Name.toString)

private meta def sortedNames (names : Array Name) : Array Name :=
  (NameSet.ofArray names).toArray.qsort Name.lt

private meta def serializeExpr (expression : Expr) : String :=
  (repr expression).pretty 1000000000

private meta def moduleOf (env : Environment) (name : Name) : Name :=
  match env.getModuleIdxFor? name with
  | some index => env.allImportedModuleNames[index.toNat]!
  | none => env.mainModule

private meta def kind (info : ConstantInfo) : String :=
  match info with
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

/-- Elaborate each expected proposition independently of the inspected type. -/
private meta def expectedType (name : Name) : TermElabM Expr := do
  let stx <-
    if name == ``PotentialSeparation.Construction.certificate_exists then
      `(forall {n : Nat}, 2 <= n -> Nonempty (PotentialSeparation.DriftCertificate n))
    else if name == ``PotentialSeparation.Construction.pointwise_drift then
      `(forall {n : Nat}, 2 <= n -> PotentialSeparation.PointwiseDrift (n := n)
        0 (PotentialSeparation.Construction.thresholdCost n)
          (PotentialSeparation.Construction.tacticCost n) 1)
    else if name == ``NeighborSeparation.Embedding.certificate_exists then
      `(forall {n : Nat}, 2 <= n -> Nonempty (NeighborSeparation.DriftCertificate n))
    else if name == ``NeighborSeparation.Embedding.certificate_budget_eq then
      `(forall {n : Nat}, forall C : PotentialSeparation.DriftCertificate n,
        NeighborSeparation.certificateBudget (NeighborSeparation.Embedding.certificate C) =
          PotentialSeparation.certificateBudget C)
    else if name == ``PotentialSeparation.Exponential.certificate_budget_exponential_lower then
      `(forall {n k : Nat}, 2 * k + 4 <= n ->
        forall C : PotentialSeparation.DriftCertificate n,
          ((5 : Real)^(k + 1) - 3) / 36 <= PotentialSeparation.certificateBudget C)
    else if name == ``PotentialSeparation.Exponential.certificate_budget_floor_lower then
      `(forall {n : Nat}, 4 <= n -> forall C : PotentialSeparation.DriftCertificate n,
        ((5 : Real)^((n - 4) / 2 + 1) - 3) / 36 <= PotentialSeparation.certificateBudget C)
    else if name == ``PotentialSeparation.Construction.initial_budget_upper then
      `(forall {n : Nat}, 2 <= n -> PotentialSeparation.initialBudget n
        0 (PotentialSeparation.Construction.thresholdCost n)
          (PotentialSeparation.Construction.tacticCost n) <= 3 * (9 : Real)^(n - 2) + 1)
    else if name == ``CertificateStudy.nonvacuous_separable_separation then
      `(forall {n : Nat}, 4 <= n -> And
        (Nonempty (PotentialSeparation.DriftCertificate n)) (And
        (forall C : PotentialSeparation.DriftCertificate n,
          ((5 : Real)^((n - 4) / 2 + 1) - 3) / 36 <= PotentialSeparation.certificateBudget C)
        (And (ENNReal.ofReal ((n : Real) / 18) <= MTChainFormal.expectedSteps n)
          (MTChainFormal.expectedSteps n <= ENNReal.ofReal (1054 * (n : Real))))))
    else if name == ``CertificateStudy.nonvacuous_neighbor_separation then
      `(forall {n : Nat}, 10 <= n -> And
        (Nonempty (NeighborSeparation.DriftCertificate n)) (And
        (forall C : NeighborSeparation.DriftCertificate n,
          (n : Real)^2 / 1248 <= NeighborSeparation.certificateBudget C)
        (And (ENNReal.ofReal ((n : Real) / 18) <= MTChainFormal.expectedSteps n)
          (MTChainFormal.expectedSteps n <= ENNReal.ofReal (1054 * (n : Real))))))
    else
      throwError "Unregistered theorem root {name}"
  let expression <- Term.elabType stx
  Term.synthesizeSyntheticMVarsNoPostponing
  let expression <- instantiateMVars expression
  if expression.hasMVar then
    throwError "Expected type of {name} contains unresolved metavariables"
  return expression

/-- Inspect explicit top-level binders without unfolding Not or other conclusions. -/
private meta def checkBinders (name : Name) (type : Expr) : TermElabM Json := do
  forallTelescope type fun xs _ => do
    let expectedCount :=
      if name == ``PotentialSeparation.Exponential.certificate_budget_exponential_lower then 4
      else if name == ``PotentialSeparation.Exponential.certificate_budget_floor_lower then 3
      else 2
    unless xs.size == expectedCount do
      throwError "Wrong binder count for {name}: {xs.size}, expected {expectedCount}"
    unless <- isDefEq (<- inferType xs[0]!) (mkConst ``Nat) do
      throwError "First binder of {name} is not Nat"
    -- The independently elaborated exact target checks every remaining domain.
    let mut binders : Array Json := #[]
    for x in xs do
      let declaration <- getFVarLocalDecl x
      binders := binders.push <| Json.mkObj [
        ("name", toJson declaration.userName.toString),
        ("type_ast", toJson (serializeExpr declaration.type)),
        ("binder_info", toJson (repr declaration.binderInfo).pretty)]
    return Json.mkObj [
      ("status", toJson "PASS"), ("count", toJson xs.size),
      ("expected_count", toJson expectedCount), ("binders", Json.arr binders)]

/-- Raw kernel dependencies, including inductive packages and recursor rules. -/
private meta def rawDependencies (info : ConstantInfo) : Array Name := Id.run do
  let mut dependencies := info.type.getUsedConstants
  if let some value := info.value? true then
    dependencies := dependencies ++ value.getUsedConstants
  match info with
  | .inductInfo value =>
    dependencies := dependencies ++ value.all.toArray ++ value.ctors.toArray
  | .ctorInfo value =>
    dependencies := dependencies.push value.induct
  | .recInfo value =>
    dependencies := dependencies ++ value.all.toArray
    for rule in value.rules do
      dependencies := (dependencies.push rule.ctor) ++ rule.rhs.getUsedConstants
  | .quotInfo _ =>
    dependencies := dependencies ++ #[``Eq, ``Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind]
  | _ => pure ()
  return sortedNames dependencies

private meta structure Closure where
  graph : NameMap (Array Name) := {}
  actualAxioms : NameSet := {}
  kindCounts : NameMap Nat := {}
  names : NameSet := {}

/-- Read every reachable kernel declaration once; never consult collectAxioms. -/
private meta def rawClosure (env : Environment) : CommandElabM Closure := do
  let kernel := env.checked.get
  let mut todo := roots
  let mut result : Closure := {}
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    if result.names.contains name then
      continue
    let some info := kernel.find? name
      | throwError "Actual proof closure has a missing kernel constant: {name}"
    if info.isUnsafe || info.isPartial then
      throwError "Actual proof closure contains unsafe/partial constant: {name}"
    if info.isAxiom then
      unless allowedAxioms.contains name do
        throwError "Forbidden actual transitive axiom: {name}"
      result := { result with actualAxioms := result.actualAxioms.insert name }
    let dependencies := rawDependencies info
    let kindName := Name.str .anonymous (kind info)
    let count := (result.kindCounts.find? kindName).getD 0
    result := { result with
      names := result.names.insert name
      graph := result.graph.insert name dependencies
      kindCounts := result.kindCounts.insert kindName (count + 1) }
    todo := todo ++ dependencies
  return result

/-- Per-root reachability uses the already inspected graph, not cached axiom metadata. -/
private meta def axiomsFor (closure : Closure) (root : Name) : CommandElabM (Array Name) := do
  let mut todo := #[root]
  let mut seen : NameSet := {}
  let mut axioms : NameSet := {}
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    if seen.contains name then
      continue
    seen := seen.insert name
    if closure.actualAxioms.contains name then
      axioms := axioms.insert name
    let some dependencies := closure.graph.find? name
      | throwError "Internal proof-closure graph is incomplete at {name}"
    todo := todo ++ dependencies
  return axioms.toArray.qsort Name.lt

private meta def audit : CommandElabM Unit := do
  let auditEnv <- getEnv
  let env <- liftIO <| Lean.importModules
    #[{ module := Name.mkSimple "CertificateResults" }] {}
    (loadExts := false) (level := .private)
  let env := env.setExporting false
  let kernel := env.checked.get
  unless roots.size == 9 && (sortedNames roots).size == 9 do
    throwError "The frozen theorem-root inventory must contain exactly 9 distinct names"
  let closure <- rawClosure env
  let mut declarations : Array Json := #[]
  for name in roots do
    let some info := kernel.find? name
      | throwError "Missing actual theorem root: {name}"
    unless info.isTheorem do
      throwError "The selected root is not an actual kernel theorem: {name}"
    let some value := info.value? true
      | throwError "The selected theorem has no actual proof body: {name}"
    let (expected, pretty, binderGate) <- liftTermElabM do
      let expected <- expectedType name
      unless <- isDefEq info.type expected do
        throwError "Actual theorem type differs from the independently stated target: {name}"
      let gate <- checkBinders name info.type
      return (expected, (<- ppExpr info.type).pretty, gate)
    let axioms <- axiomsFor closure name
    declarations := declarations.push <| Json.mkObj [
      ("name", toJson name.toString), ("module", toJson (moduleOf env name).toString),
      ("kind", toJson (kind info)), ("is_private", toJson (isPrivateName name)),
      ("is_unsafe", toJson info.isUnsafe), ("is_partial", toJson info.isPartial),
      ("level_params", namesJson info.levelParams.toArray),
      ("type_ast", toJson (serializeExpr info.type)), ("type_pretty", toJson pretty),
      ("expected_type_ast", toJson (serializeExpr expected)),
      ("exact_type_defeq", toJson true), ("binder_gate", binderGate),
      ("value_ast", toJson (serializeExpr value)), ("has_actual_proof_body", toJson true),
      ("axioms", namesJson axioms),
      ("type_dependencies", namesJson (sortedNames info.type.getUsedConstants)),
      ("value_dependencies", namesJson (sortedNames value.getUsedConstants))]
  let mut imports : Array Json := #[]
  let importedNames := sortedNames
    (auditEnv.allImportedModuleNames ++ env.allImportedModuleNames)
  for index in [:importedNames.size] do
    let moduleName := importedNames[index]!
    let moduleText := moduleName.toString
    if moduleText.startsWith "PPGraph" || moduleText.startsWith "PPG" ||
        moduleText.startsWith "PPChain" || moduleText.startsWith "Profile" ||
        moduleText.startsWith "PublicKernelBridge" then
      throwError "Forbidden PPG/profile wrapper import: {moduleName}"
    let file <- liftIO <| Lean.findOLean moduleName
    let privateFile : System.FilePath := file.toString ++ ".private"
    let serverFile : System.FilePath := file.toString ++ ".server"
    let hasPrivate <- liftIO privateFile.pathExists
    let hasServer <- liftIO serverFile.pathExists
    imports := imports.push <| Json.mkObj [
      ("index", toJson index), ("module", toJson moduleName.toString),
      ("olean", toJson file.toString),
      ("private_sidecar", if hasPrivate then toJson privateFile.toString else Json.null),
      ("server_sidecar", if hasServer then toJson serverFile.toString else Json.null)]
  let counts := closure.kindCounts.toList.map fun (name, count) =>
    (name.toString, toJson count)
  let report := Json.mkObj [
    ("schema_version", toJson (1 : Nat)), ("status", toJson "PASS"),
    ("main_module", toJson auditEnv.mainModule.toString),
    ("modules", namesJson #[Name.mkSimple "CertificateResults"]),
    ("root_count", toJson roots.size), ("root_names", namesJson roots),
    ("declarations", Json.arr declarations),
    ("raw_kernel_closure_count", toJson closure.names.toArray.size),
    ("raw_kernel_closure_kinds", Json.mkObj counts),
    ("raw_kernel_closure_axioms", namesJson (closure.actualAxioms.toArray.qsort Name.lt)),
    ("allowed_axioms", namesJson allowedAxioms),
    ("axiom_method", toJson "Actual env.checked constants: types, values, inductive packages, recursor rules; one shared raw traversal and per-root graph reachability; no collectAxioms cache"),
    ("audit_support_imported_module_count", toJson auditEnv.allImportedModuleNames.size),
    ("proof_imported_module_count", toJson env.allImportedModuleNames.size),
    ("import_inventory_method", toJson "Deduplicated union of auditor support imports and full-private proof imports"),
    ("imported_module_count", toJson imports.size),
    ("import_inventory", Json.arr imports)]
  logInfo m!"CERTIFICATE_INDEPENDENT_AUDIT {report.compress}"

run_cmd audit

end CertificateIndependentAudit
