/-
  PPGraphBDDCost.lean
  "Graph governs map": the formal bridge connecting Blocking Dependency
  Decomposition (PPGraphBDD.lean) to cost-minimization instead of
  satisfaction-checking - the missing piece identified in session_state.md's
  2026-09-16 "TWO CLEAN FORWARD DIRECTIONS" note (direction 1, "the solid,
  low-risk path... just not yet written in transport terms").

  PPGraphBDD.lean already proves the SATISFACTION-CHECKING half of "graph
  governs map": `lll_feasible_iff_componentwise` (feasibility over B is
  exactly feasibility checked independently per component) and
  `repair_noninterference` (repairing one component cannot change whether a
  certificate in a different component is satisfied). Both are about a
  Boolean/Prop-valued question (does sat hold). This file proves the
  analogous fact for a REAL-VALUED cost - the actual mathematical content
  behind the "transport map factorizes over BDD components" claim that
  exp_transport_vs_bdd.py (v2) validated empirically on synthetic data:
  squared-distance cost decomposes additively over disjoint variable blocks,
  so the jointly-optimal cost equals the sum of independently-optimal
  per-component costs. That empirical finding is a special case (squared
  Euclidean norm) of the general fact proved here (any cost that is LOCAL to
  each certificate's own variables).

  Scope, deliberately: proved for ONE component (`compOf vars B c1`) versus
  "everything else in B" (`B \ compOf vars B c1`), mirroring
  `repair_noninterference`/`repair_noninterference_all`'s own one-component-
  vs-the-rest shape rather than building a full quotient-into-many-components
  machinery. Applying this once per component of a full partition recovers
  the "sum over ALL components" statement; a dedicated multi-way version is
  future work if the induction is ever needed as a single theorem.

  The optimization domain is kept FINITE (V, alpha both Fintype) rather than
  a continuous transport/Wasserstein space - this matches what was actually
  validated (exp_transport_vs_bdd.py's discrete permutation search over a
  finite candidate set, not continuous optimal transport), and lets the
  minimum be taken via `Finset.inf'` over `Finset.univ : Finset (V -> alpha)`,
  avoiding `sInf`/`iInf` junk-value issues over an unbounded continuous
  domain. A continuous-OT version, if ever wanted, is a separate, harder
  undertaking (real Wasserstein/Monge machinery, not attempted here).

  Author: Dragan Stosic, 2026.
-/

module

public import PPGraph.Dependency.Decomposition

@[expose] public section

open scoped Classical

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {C V α : Type} [DecidableEq C] [DecidableEq V] [Fintype V] [Fintype α] [Nonempty α]

-- Section 1: local cost and total cost.
-- `LocalCost` is the cost-valued counterpart of `Local` (PPGraphBDD.lean,
-- Section 3): instead of an iff on a Prop, an equality of a real number,
-- given the same "depends only on Vars(c)" hypothesis.

/-- A certificate's cost depends only on the instantiation restricted to its
    own variables - the same locality/frame condition `Local` states for
    `sat`, here for a real-valued cost instead of a Prop. -/
def LocalCost (vars : CertVars C V) (cost : C → (V → α) → Real) : Prop :=
  ∀ c, ∀ i1 i2 : V → α, (∀ v ∈ vars c, i1 v = i2 v) → cost c i1 = cost c i2

/-- Total cost of a blocking set under one instantiation: the sum of every
    certificate's own cost. This is the discrete analogue of a joint
    transport/assignment cost over all variables at once. -/
def totalCost (cost : C → (V → α) → Real) (B : Finset C) (i : V → α) : Real :=
  ∑ c ∈ B, cost c i

/-- The globally-optimal (minimum) total cost over EVERY possible
    instantiation - the finite-search analogue of an optimal transport/
    assignment cost. Well-defined without any boundedness hypothesis since
    the search domain `V → α` is a Fintype (via `V`, `α` both Fintype). -/
noncomputable def optCost (cost : C → (V → α) → Real) (B : Finset C) : Real :=
  Finset.univ.inf' Finset.univ_nonempty (totalCost cost B)

-- Section 2: the factorization theorem.
-- This is the literal "graph governs map" bridge: the globally-optimal cost
-- over the whole blocking set B decomposes EXACTLY (not just an inequality)
-- into the optimal cost achievable on one component plus the optimal cost
-- achievable on everything else - solving per-component and combining gives
-- the same answer as solving jointly. Matches exp_transport_vs_bdd.py's
-- `cost_joint_optimal = cost_B1_optimal + cost_B2_optimal` (equality case),
-- now as a theorem instead of an empirical observation on synthetic data.

theorem rest_eq_filter_not (vars : CertVars C V) (B : Finset C) (c1 : C) :
    B \ compOf vars B c1 = B.filter (fun c => ¬ SameComponent vars B c1 c) := by
  unfold compOf
  rw [Finset.filter_not]

theorem totalCost_split (vars : CertVars C V) (cost : C → (V → α) → Real)
    (B : Finset C) (c1 : C) (i : V → α) :
    totalCost cost B i =
      totalCost cost (compOf vars B c1) i + totalCost cost (B \ compOf vars B c1) i := by
  unfold totalCost
  rw [rest_eq_filter_not]
  unfold compOf
  exact (Finset.sum_filter_add_sum_filter_not B (SameComponent vars B c1) (fun c => cost c i)).symm

theorem optCost_ge_component_split (vars : CertVars C V) (cost : C → (V → α) → Real)
    (B : Finset C) (c1 : C) :
    optCost cost (compOf vars B c1) + optCost cost (B \ compOf vars B c1) ≤ optCost cost B := by
  apply Finset.le_inf'
  intro i _
  rw [totalCost_split vars cost B c1 i]
  have h1 : optCost cost (compOf vars B c1) ≤ totalCost cost (compOf vars B c1) i :=
    Finset.inf'_le _ (Finset.mem_univ i)
  have h2 : optCost cost (B \ compOf vars B c1) ≤ totalCost cost (B \ compOf vars B c1) i :=
    Finset.inf'_le _ (Finset.mem_univ i)
  linarith

theorem optCost_le_component_split (vars : CertVars C V) (cost : C → (V → α) → Real)
    (hloc : LocalCost vars cost) (B : Finset C) (c1 : C) :
    optCost cost B ≤ optCost cost (compOf vars B c1) + optCost cost (B \ compOf vars B c1) := by
  obtain ⟨i_f, -, hif⟩ :=
    Finset.exists_mem_eq_inf' Finset.univ_nonempty (totalCost cost (compOf vars B c1))
  obtain ⟨i_g, -, hig⟩ :=
    Finset.exists_mem_eq_inf' Finset.univ_nonempty (totalCost cost (B \ compOf vars B c1))
  set i_star : V → α := fun v => if v ∈ componentFootprint vars B c1 then i_f v else i_g v
    with hi_star_def
  have hf_agree : ∀ c ∈ compOf vars B c1, ∀ v ∈ vars c, i_star v = i_f v := by
    intro c hc v hv
    have hsame : SameComponent vars B c1 c := by
      simp only [compOf, Finset.mem_filter] at hc
      exact hc.2
    have hv_in : v ∈ componentFootprint vars B c1 := by
      rw [componentFootprint_eq_of_sameComponent vars B c1 c hsame]
      exact vars_subset_own_footprint vars B c (compOf_subset vars B c1 hc) hv
    simp [hi_star_def, hv_in]
  have hg_agree : ∀ c ∈ B \ compOf vars B c1, ∀ v ∈ vars c, i_star v = i_g v := by
    intro c hc v hv
    have hcB : c ∈ B := (Finset.mem_sdiff.mp hc).1
    have hnotcomp : c ∉ compOf vars B c1 := (Finset.mem_sdiff.mp hc).2
    have hdiff : ¬ SameComponent vars B c1 c := by
      intro hsame
      apply hnotcomp
      simp only [compOf, Finset.mem_filter]
      exact ⟨hcB, hsame⟩
    have hv_in_c : v ∈ componentFootprint vars B c := vars_subset_own_footprint vars B c hcB hv
    have hnotin : v ∉ componentFootprint vars B c1 := by
      intro hin
      have hboth : v ∈ componentFootprint vars B c1 ∩ componentFootprint vars B c := ⟨hin, hv_in_c⟩
      rw [footprint_disjoint_of_diff_component vars B c1 c hdiff] at hboth
      exact hboth
    simp [hi_star_def, hnotin]
  have h1 : totalCost cost (compOf vars B c1) i_star = totalCost cost (compOf vars B c1) i_f := by
    unfold totalCost
    exact Finset.sum_congr rfl (fun c hc => hloc c i_star i_f (hf_agree c hc))
  have h2 : totalCost cost (B \ compOf vars B c1) i_star
      = totalCost cost (B \ compOf vars B c1) i_g := by
    unfold totalCost
    exact Finset.sum_congr rfl (fun c hc => hloc c i_star i_g (hg_agree c hc))
  -- `hif`/`hig` come out of `exists_mem_eq_inf'` in raw `Finset.univ.inf' ...` form;
  -- re-typing them against `optCost` forces the defeq unfold once, up front, so the
  -- final `rw` below is a plain syntactic match instead of fighting `optCost`'s def.
  have hif' : optCost cost (compOf vars B c1) = totalCost cost (compOf vars B c1) i_f := hif
  have hig' : optCost cost (B \ compOf vars B c1) = totalCost cost (B \ compOf vars B c1) i_g := hig
  calc optCost cost B ≤ totalCost cost B i_star := Finset.inf'_le _ (Finset.mem_univ i_star)
    _ = totalCost cost (compOf vars B c1) i_star + totalCost cost (B \ compOf vars B c1) i_star :=
        totalCost_split vars cost B c1 i_star
    _ = totalCost cost (compOf vars B c1) i_f + totalCost cost (B \ compOf vars B c1) i_g := by
        rw [h1, h2]
    _ = optCost cost (compOf vars B c1) + optCost cost (B \ compOf vars B c1) := by rw [hif', hig']

/-- Main theorem: the "graph governs map" bridge. The globally-optimal cost
    over the whole blocking set B is EXACTLY the optimal cost on c1's
    component plus the optimal cost on everything else in B outside it -
    solving the cost-minimization problem per BDD component and adding the
    results gives the same answer as solving it jointly over all of B. This
    is the cost-minimization counterpart of `lll_feasible_iff_componentwise`
    (PPGraphBDD.lean): that theorem showed feasibility-checking localizes to
    components; this theorem shows the same for optimization. -/
theorem optCost_component_split (vars : CertVars C V) (cost : C → (V → α) → Real)
    (hloc : LocalCost vars cost) (B : Finset C) (c1 : C) :
    optCost cost B = optCost cost (compOf vars B c1) + optCost cost (B \ compOf vars B c1) :=
  le_antisymm (optCost_le_component_split vars cost hloc B c1)
    (optCost_ge_component_split vars cost B c1)

-- Verification
#check @LocalCost
#check @totalCost
#check @optCost
#check @rest_eq_filter_not
#check @totalCost_split
#check @optCost_ge_component_split
#check @optCost_le_component_split
#check @optCost_component_split
