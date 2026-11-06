/-
  The effective limit of complete repair/refutation procedures on infinite states.
  Source: Carneiro, Formalizing Computability Theory via Partial Recursive
  Functions, ITP 2019 / arXiv:1810.08380, Sections 5.2--5.3.
  The halting and non-enumerability results are reused from Mathlib.

  The counter-family has decidable, uniformly primitive-recursive state checks
  and trivial transitions. A state is a successful bounded-evaluation budget.
  Thus the obstruction is not an uncomputable per-state specification.
  evaln's budget bounds intermediate values; it is not an exact step counter.
-/
module

public import PPGraph.Decision.ReachabilityRefutation
public import Mathlib.Computability.Halting

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace RepairFeasibility
namespace ComputabilityLimit

open Nat.Partrec (Code)

def boundedCheck (input : ℕ) (p : Code × ℕ) : Bool :=
  (Code.evaln p.2 p.1 input).isSome

def BoundedGood (input : ℕ) (c : Code) (budget : ℕ) : Prop :=
  boundedCheck input (c, budget) = true

instance (input : ℕ) (c : Code) : DecidablePred (BoundedGood input c) :=
  fun budget => inferInstanceAs (Decidable (boundedCheck input (c, budget) = true))

theorem boundedCheck_primrec (input : ℕ) : Primrec (boundedCheck input) :=
  Primrec.option_isSome.comp
    (Code.primrec_evaln.comp ((Primrec.snd.pair Primrec.fst).pair (Primrec.const input)))

theorem boundedGood_iff_evaln_mem (input : ℕ) (c : Code) (budget : ℕ) :
    BoundedGood input c budget ↔ ∃ value, value ∈ Code.evaln budget c input := by
  simp [BoundedGood, boundedCheck, Option.isSome_iff_exists]

theorem good_exists_iff_halting (input : ℕ) (c : Code) :
    (∃ budget, BoundedGood input c budget) ↔ (Code.eval c input).Dom := by
  simp only [boundedGood_iff_evaln_mem, Part.dom_iff_mem, Code.evaln_complete]
  exact exists_comm

/-- Every proposed budget is reachable in one step, independently of the program. -/
def budgetGraph (input : ℕ) (c : Code) : RepairGraph ℕ where
  edges := fun _ _ => True
  reach_rel := fun _ _ => True
  invariant_holds := BoundedGood input c

theorem budgetGraph_reach_iff_path (input : ℕ) (c : Code) (u v : ℕ) :
    (budgetGraph input c).reach_rel u v ↔
      Relation.ReflTransGen (budgetGraph input c).edges u v :=
  ⟨fun _ => Relation.ReflTransGen.single trivial, fun _ => trivial⟩

theorem reachable_good_iff_halting (input : ℕ) (c : Code) (start : ℕ) :
    (∃ w, (budgetGraph input c).reach_rel start w ∧
      (budgetGraph input c).invariant_holds w) ↔ (Code.eval c input).Dom := by
  simpa [budgetGraph] using good_exists_iff_halting input c

theorem noReachableGood_iff_nonhalting (input : ℕ) (c : Code) (start : ℕ) :
    NoReachableGood (budgetGraph input c) start ↔ ¬ (Code.eval c input).Dom :=
  not_congr (reachable_good_iff_halting input c start)

theorem repairability_re (input start : ℕ) :
    REPred (fun c => ∃ w, (budgetGraph input c).reach_rel start w ∧
      (budgetGraph input c).invariant_holds w) :=
  (ComputablePred.halting_problem_re input).of_eq
    (fun c => (reachable_good_iff_halting input c start).symm)

theorem repairability_not_computable (input start : ℕ) :
    ¬ ComputablePred (fun c => ∃ w, (budgetGraph input c).reach_rel start w ∧
      (budgetGraph input c).invariant_holds w) := by
  intro h
  exact ComputablePred.halting_problem input
    (h.of_eq (fun c => reachable_good_iff_halting input c start))

theorem infeasibility_not_re (input start : ℕ) :
    ¬ REPred (fun c => NoReachableGood (budgetGraph input c) start) := by
  intro h
  exact ComputablePred.halting_problem_not_re input
    (h.of_eq (fun c => noReachableGood_iff_nonhalting input c start))

theorem infeasibility_not_computable (input start : ℕ) :
    ¬ ComputablePred (fun c => NoReachableGood (budgetGraph input c) start) :=
  fun h => infeasibility_not_re input start h.to_re

/-- Finite certificates checked by a total computable checker are enumerable. -/
theorem checked_certificate_exists_re {Instance : Type} [Primcodable Instance]
    (check : Instance × ℕ → Bool) (hcheck : Computable check) :
    REPred (fun c => ∃ certificate, check (c, certificate) = true) := by
  have hsearch : Partrec (fun c => Nat.rfind (fun k => Part.some (check (c, k)))) :=
    Partrec.rfind hcheck.partrec
  exact hsearch.dom_re.of_eq (fun c => by simp [Nat.rfind_dom])

/-- No sound computable finite-certificate checker covers every impossible instance. -/
theorem no_complete_refutation_checker (input start : ℕ) :
    ¬ ∃ check : Code × ℕ → Bool, Computable check ∧
      (∀ c k, check (c, k) = true → NoReachableGood (budgetGraph input c) start) ∧
      (∀ c, NoReachableGood (budgetGraph input c) start → ∃ k, check (c, k) = true) := by
  rintro ⟨check, hc, hs, ht⟩
  apply infeasibility_not_re input start
  exact (checked_certificate_exists_re check hc).of_eq (fun c =>
    ⟨fun ⟨k, hk⟩ => hs c k hk, ht c⟩)

theorem no_total_impossibility_decider (input start : ℕ) :
    ¬ ∃ test : Code → Bool, Computable test ∧
      ∀ c, test c = true ↔ NoReachableGood (budgetGraph input c) start := by
  rintro ⟨test, ht, he⟩
  apply infeasibility_not_computable input start
  exact ComputablePred.computable_iff.mpr
    ⟨test, ht, funext (fun c => propext (he c).symm)⟩

theorem no_total_repairability_decider (input start : ℕ) :
    ¬ ∃ test : Code → Bool, Computable test ∧
      ∀ c, test c = true ↔ ∃ w, (budgetGraph input c).reach_rel start w ∧
        (budgetGraph input c).invariant_holds w := by
  rintro ⟨test, ht, he⟩
  apply repairability_not_computable input start
  exact ComputablePred.computable_iff.mpr
    ⟨test, ht, funext (fun c => propext (he c).symm)⟩

end ComputabilityLimit
end RepairFeasibility

#check @RepairFeasibility.ComputabilityLimit.boundedCheck_primrec
#check @RepairFeasibility.ComputabilityLimit.boundedGood_iff_evaln_mem
#check @RepairFeasibility.ComputabilityLimit.good_exists_iff_halting
#check @RepairFeasibility.ComputabilityLimit.budgetGraph_reach_iff_path
#check @RepairFeasibility.ComputabilityLimit.reachable_good_iff_halting
#check @RepairFeasibility.ComputabilityLimit.noReachableGood_iff_nonhalting
#check @RepairFeasibility.ComputabilityLimit.repairability_re
#check @RepairFeasibility.ComputabilityLimit.repairability_not_computable
#check @RepairFeasibility.ComputabilityLimit.infeasibility_not_re
#check @RepairFeasibility.ComputabilityLimit.infeasibility_not_computable
#check @RepairFeasibility.ComputabilityLimit.checked_certificate_exists_re
#check @RepairFeasibility.ComputabilityLimit.no_complete_refutation_checker
#check @RepairFeasibility.ComputabilityLimit.no_total_impossibility_decider
#check @RepairFeasibility.ComputabilityLimit.no_total_repairability_decider
