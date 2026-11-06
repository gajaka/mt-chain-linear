module

import all BiasedResults
import all BiasedControls
meta import Lean

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0

/-! Independently spelled statements and a raw transitive kernel-dependency
audit. The traversal follows the existing ThetaIndependentAudit technique;
the old audit and its historical receipt are not modified. -/

open MTChainFormal MTChainFormal.BiasedResampling
open scoped BigOperators ENNReal

example {n : ℕ} (hn : 2 ≤ n) (p : ℝ) (hp : (2 / 3 : ℝ) ≤ p) (hp1 : p ≤ 1)
    (s : ChainState n) (i : Fin n) (hf : passes s i = false) :
    1 + average p (fun u => potential (replace s i u)) ≤ potential s :=
  pointwise_drift hn p hp hp1 s i hf

example {n : ℕ} (hn : 2 ≤ n) (policy : HistoryPolicy n)
    (history : List (ChainState n)) (s : ChainState n) :
    adaptiveTotalWork policy history s ≤ ENNReal.ofReal (10 * (n : ℝ) - 6) :=
  adaptiveTotalWork_le_linear hn policy history s

example {n : ℕ} (hn : 2 ≤ n) (policy : HistoryPolicy n) :
    adaptiveInitialTotalWork policy (2 / 3) ≤ ENNReal.ofReal (3 * (n : ℝ) - 2) :=
  adaptive_biased_initial_upper hn policy

example {n : ℕ} (hn : 2 ≤ n) (policy : HistoryPolicy n) :
    adaptiveInitialTotalWork policy (1 / 3) ≤ ENNReal.ofReal (5 * (n : ℝ) - 4) :=
  adaptive_uniform_initial_upper hn policy

example (n : ℕ) : Nonempty (HistoryPolicy n) := ⟨staticPolicy staticBias⟩

example {n : ℕ} (hn : 2 ≤ n) :
    ENNReal.ofReal ((n : ℝ) / 24) ≤
        MTChainFormal.BiasedResampling.expectedSteps n ∧
      MTChainFormal.BiasedResampling.expectedSteps n ≤
        ENNReal.ofReal (3 * (n : ℝ) - 2) := static_linear_work_bounds hn

example : Asymptotics.IsTheta Filter.atTop
    (fun n : ℕ => (MTChainFormal.BiasedResampling.expectedSteps n).toReal)
    (fun n : ℕ => (n : ℝ)) :=
  MTChainFormal.BiasedResampling.expected_steps_isTheta_linear

namespace BiasedAudit

open Lean Elab Command Meta Term

private meta def allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

private meta def sortNames (ns : Array Name) : Array Name :=
  (NameSet.ofArray ns).toArray.qsort Name.lt

private meta def dependencies (ci : ConstantInfo) : Array Name := Id.run do
  let mut ds := ci.type.getUsedConstants
  if let some v := ci.value? true then ds := ds ++ v.getUsedConstants
  match ci with
  | .inductInfo v => ds := ds ++ v.all.toArray ++ v.ctors.toArray
  | .ctorInfo v => ds := ds.push v.induct
  | .recInfo v =>
      ds := ds ++ v.all.toArray
      for r in v.rules do ds := (ds.push r.ctor) ++ r.rhs.getUsedConstants
  | .quotInfo _ => ds := ds ++ #[``Eq, ``Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind]
  | _ => pure ()
  return sortNames ds

private meta def audit : CommandElabM Unit := do
  let env ← liftIO <| Lean.importModules
    #[{ module := `BiasedResults }, { module := `BiasedControls }] {}
    (loadExts := false) (level := .private)
  let env := env.setExporting false
  let kernel := env.checked.get
  let roots ← env.constants.foldM (init := (#[] : Array Name)) fun ns n ci => do
    if n.toString.startsWith "MTChainFormal.BiasedResampling." && ci.isTheorem then
      return ns.push n
    return ns
  let roots := sortNames roots
  unless roots.size ≥ 50 do throwError "Incomplete new-theorem inventory"
  let mut todo := roots
  let mut seen : NameSet := {}
  let mut actualAxioms : NameSet := {}
  let mut graph : NameMap (Array Name) := {}
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    let some ci := kernel.find? n | throwError "Missing raw kernel constant: {n}"
    if ci.isUnsafe || ci.isPartial then throwError "Unsafe or partial dependency: {n}"
    if n.toString.startsWith "MTChainFormal.Tightness.expected_steps" then
      throwError "Old runtime theorem is not a premise of this study: {n}"
    if ci.isAxiom then
      unless allowed.contains n do throwError "Forbidden transitive axiom: {n}"
      actualAxioms := actualAxioms.insert n
    let ds := dependencies ci
    seen := seen.insert n
    graph := graph.insert n ds
    todo := todo ++ ds
  let mut records : Array Json := #[]
  for root in roots do
    let some ci := kernel.find? root | throwError "Missing theorem root: {root}"
    unless ci.isTheorem && (ci.value? true).isSome do
      throwError "Root is not a theorem with a checked proof: {root}"
    let mut queue := #[root]
    let mut reached : NameSet := {}
    let mut axioms : NameSet := {}
    while !queue.isEmpty do
      let n := queue.back!
      queue := queue.pop
      if reached.contains n then continue
      reached := reached.insert n
      if actualAxioms.contains n then axioms := axioms.insert n
      let some ds := graph.find? n | throwError "Incomplete raw dependency graph: {n}"
      queue := queue ++ ds
    let pretty ← liftTermElabM do return (← ppExpr ci.type).pretty
    records := records.push <| Json.mkObj [
      ("name", toJson root.toString), ("type", toJson pretty),
      ("axioms", toJson ((sortNames axioms.toArray).map Name.toString)),
      ("has_checked_body", toJson true)]
  let forbiddenModules := #[`FinalQuadratic, `LinearPotential, `TightnessResults,
    `LowerBound, `ThetaIndependentAudit]
  let mut ownedImports : Array Json := #[]
  for m in env.allImportedModuleNames do
    if forbiddenModules.contains m then throwError "Old runtime module imported: {m}"
    if m.toString.startsWith "Biased" || m == `AdaptiveWork || m == `GenericLower then
      let file ← liftIO <| Lean.findOLean m
      ownedImports := ownedImports.push <| Json.mkObj [
        ("module", toJson m.toString), ("olean", toJson file.toString)]
  let report := Json.mkObj [
    ("status", toJson "PASS"),
    ("theorem_count", toJson roots.size),
    ("theorems", Json.arr records),
    ("raw_closure_count", toJson seen.toArray.size),
    ("raw_closure_axioms", toJson ((sortNames actualAxioms.toArray).map Name.toString)),
    ("owned_imports", Json.arr ownedImports),
    ("method", toJson "Raw checked constants, proof bodies, inductive bundles and recursor rules; no collectAxioms cache"),
    ("old_runtime_imports_excluded", toJson true)]
  logInfo m!"BIASED_RESAMPLING_AUDIT {report.compress}"

run_cmd audit

end BiasedAudit
