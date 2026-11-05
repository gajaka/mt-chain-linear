module
import all TightnessResults
meta import Lean

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0

/-! Adapted raw-process audit: nine roots, no PPG/profile/recovery corollaries.
The imported TightnessResults is this standalone project's raw facade.
Original source hash and exact adaptation are recorded in ADAPTATION.json. -/

namespace ThetaIndependentAudit

open Lean Elab Command Meta Term

private meta def roots : Array Name := #[
  ``MTChainFormal.Tightness.expected_steps_ge_linear_refined,
  ``MTChainFormal.Tightness.expected_steps_ge_linear,
  ``MTChainFormal.Tightness.expected_steps_le_linear,
  ``MTChainFormal.Tightness.linear_work_bounds,
  ``MTChainFormal.Tightness.expected_steps_isTheta_linear,
  ``MTChainFormal.Tightness.expected_steps_not_quadratic_lower,
  ``MTChainFormal.Tightness.expected_steps_not_isTheta_quadratic,
  ``MTChainFormal.Tightness.no_positive_quadratic_lower_bound,
  ``MTChainFormal.Tightness.expected_invalidations_le_linear]

private meta def closedRoots : Array Name := #[
  ``MTChainFormal.Tightness.expected_steps_isTheta_linear,
  ``MTChainFormal.Tightness.expected_steps_not_quadratic_lower,
  ``MTChainFormal.Tightness.expected_steps_not_isTheta_quadratic,
  ``MTChainFormal.Tightness.no_positive_quadratic_lower_bound]

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
    if name == ``MTChainFormal.Tightness.expected_steps_ge_linear_refined then
      `(forall {n : Nat}, 2 <= n ->
        ENNReal.ofReal ((5 * (n : Real) - 6) / 36) <= MTChainFormal.expectedSteps n)
    else if name == ``MTChainFormal.Tightness.expected_steps_ge_linear then
      `(forall {n : Nat}, 2 <= n ->
        ENNReal.ofReal ((n : Real) / 18) <= MTChainFormal.expectedSteps n)
    else if name == ``MTChainFormal.Tightness.expected_steps_le_linear then
      `(forall {n : Nat}, 2 <= n ->
        MTChainFormal.expectedSteps n <= ENNReal.ofReal (1054 * (n : Real)))
    else if name == ``MTChainFormal.Tightness.linear_work_bounds then
      `(forall {n : Nat}, 2 <= n -> And
        (ENNReal.ofReal ((n : Real) / 18) <= MTChainFormal.expectedSteps n)
        (MTChainFormal.expectedSteps n <= ENNReal.ofReal (1054 * (n : Real))))
    else if name == ``MTChainFormal.Tightness.expected_steps_isTheta_linear then
      `(Asymptotics.IsTheta Filter.atTop
        (fun n : Nat => (MTChainFormal.expectedSteps n).toReal)
        (fun n : Nat => (n : Real)))
    else if name == ``MTChainFormal.Tightness.expected_steps_not_quadratic_lower then
      `(Not (Asymptotics.IsBigO Filter.atTop
        (fun n : Nat => (n : Real)^2)
        (fun n : Nat => (MTChainFormal.expectedSteps n).toReal)))
    else if name == ``MTChainFormal.Tightness.expected_steps_not_isTheta_quadratic then
      `(Not (Asymptotics.IsTheta Filter.atTop
        (fun n : Nat => (MTChainFormal.expectedSteps n).toReal)
        (fun n : Nat => (n : Real)^2)))
    else if name == ``MTChainFormal.Tightness.no_positive_quadratic_lower_bound then
      `(Not (Exists fun c : Real => Exists fun N : Nat => And (0 < c)
        (forall n : Nat, N <= n ->
          ENNReal.ofReal (c * (n : Real)^2) <= MTChainFormal.expectedSteps n)))
    else if name == ``MTChainFormal.Tightness.expected_invalidations_le_linear then
      `(forall {n : Nat}, 2 <= n ->
        MTChainFormal.expectedInvalidations n <= ENNReal.ofReal (2108 * (n : Real)))
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
    let expectedCount := if closedRoots.contains name then 0 else 2
    unless xs.size == expectedCount do
      throwError "Wrong binder count for {name}: {xs.size}, expected {expectedCount}"
    if expectedCount > 0 then
      unless <- isDefEq (<- inferType xs[0]!) (mkConst ``Nat) do
        throwError "First binder of {name} is not Nat"
      let lowerBound := mkApp2 (mkConst ``Nat.le) (mkNatLit 2) xs[0]!
      unless <- isDefEq (<- inferType xs[1]!) lowerBound do
        throwError "Second binder of {name} differs from 2 <= n"
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
  let env := (<- getEnv).setExporting false
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
  for index in [:env.allImportedModuleNames.size] do
    let moduleName := env.allImportedModuleNames[index]!
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
    ("main_module", toJson env.mainModule.toString),
    ("modules", namesJson #[Name.mkSimple "TightnessResults"]),
    ("root_count", toJson roots.size), ("root_names", namesJson roots),
    ("declarations", Json.arr declarations),
    ("raw_kernel_closure_count", toJson closure.names.toArray.size),
    ("raw_kernel_closure_kinds", Json.mkObj counts),
    ("raw_kernel_closure_axioms", namesJson (closure.actualAxioms.toArray.qsort Name.lt)),
    ("allowed_axioms", namesJson allowedAxioms),
    ("axiom_method", toJson "Actual env.checked constants: types, values, inductive packages, recursor rules; one shared raw traversal and per-root graph reachability; no collectAxioms cache"),
    ("imported_module_count", toJson imports.size),
    ("import_inventory", Json.arr imports)]
  logInfo m!"THETA_INDEPENDENT_AUDIT {report.compress}"

run_cmd audit

end ThetaIndependentAudit
