/-
  PPGraphBDD.lean
  Blocking Dependency Decomposition: connected components of the dependency
  graph over a blocking set, and the non-interference guarantee that
  justifies treating different components as safely independent.

  Not from the book - original. Builds directly on PPGraphProbabilistic.lean's
  `CertVars`/`dependent`/`blocking_dep_graph`: the dependency graph on a
  blocking set already existed there (edge iff shared variable); what was
  missing is its decomposition into connected components and a proof that
  different components genuinely don't interfere under independent repair.

  Motivated by the 2026-09-05 structural experiments in
  ~/Desktop/lll-proof-search-papers/ (exp_b1_structural_bdd.py,
  exp_b3_real_lean_metavar.lean): synthetically and then Lean-elaborator-
  confirmed that naive "N open goals" tracking misjudges safe parallelism
  whenever goals/certificates share a resource (a metavariable, in the
  proof-search reading; an observable variable, in the original CPS
  reading here). This file formalizes the mechanism itself - a purely
  structural, graph-theoretic claim. Nothing here is a probabilistic
  statement, so nothing here depends on whether `lll_independence` or
  `lll_lopsidependence` hold for any domain; it is immune to the
  2026-09-04 finding that lopsidependence fails for structural
  metavariable coupling under a neutral synthetic model.

  Deliberately scoped as "non-interference", not "repair succeeds": this
  file proves that repairing one component never changes the evaluation of
  a certificate/obligation in a different component - it does NOT claim a
  repair exists or succeeds. Numerical LLL budget feasibility is a separate
  sufficient-criterion layer; semantic repair existence additionally needs
  its probability model and dependency hypotheses. This is the counterpart of
  the "hub" experiment (exp_b2 / `hub_conflict_demo` in exp_b1_structural_bdd.py):
  there, committing an instantiation that only respects one goal's own
  constraint broke a goal sharing its variable; here, the theorem says that
  can only happen WITHIN a component - a change confined to one component's
  footprint provably cannot break anything outside it.

  Section 4 (added same day) connects this to `lll_feasible` from
  PPGraphProbabilistic.lean: feasibility of the whole blocking set B is
  exactly feasibility checked independently per component - the formal
  reason "Blocking Dependency Decomposition" and "the Local Lemma" belong
  together (matching paper6.tex's section title), not just two facts that
  happen to sit in the same file.

  Author: Dragan Stosic, 2026.
-/

module

public import Mathlib.Tactic
public import Mathlib.Logic.Relation
public import PPGraph.Dependency.Probabilistic

@[expose] public section

open Relation
open scoped Classical

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {C V : Type} [DecidableEq C] [DecidableEq V]

-- Section 1: the same-component relation.
-- Reusing the running example from PPGraphProbabilistic.lean: B =
-- {c1,c2,c3,c5,c6}, vars(c1)={v1,v2}, vars(c2)={v2,v3}, vars(c5)={v1,v6},
-- vars(c6)={v2,v7}, vars(c3)={v4}. c1,c2,c5,c6 are all pairwise reachable
-- through shared variables (c1~c2 via v2, c1~c5 via v1, c1~c6 via v2), so
-- they form one component; c3 shares nothing with anyone and is its own
-- singleton component - matching `neighbors`/`dependent` already computed
-- there for this exact example.

/-- Two certificates in B are directly coupled if they share a variable -
    this is exactly `blocking_dep_graph`'s edge condition, restated as a
    plain binary relation (dropping the `c1 ≠ c2` clause, since it plays no
    role once we take the equivalence closure below - `dependent vars c c`
    is possible but harmless, reflexivity is added separately anyway). -/
def CoupledIn (vars : CertVars C V) (B : Finset C) (c1 c2 : C) : Prop :=
  c1 ∈ B ∧ c2 ∈ B ∧ dependent vars c1 c2

/-- c1 and c2 are in the same BDD component of B iff they are connected by
    some chain of shared-variable couplings within B - the smallest
    equivalence relation containing `CoupledIn`. This is what lets c1 and c3
    (in the running example) end up in different components even though
    the definition only ever looks at *direct* pairwise sharing: c1 reaches
    c2, c5, c6 this way, but nothing chains from any of them to c3. -/
def SameComponent (vars : CertVars C V) (B : Finset C) : C → C → Prop :=
  EqvGen (CoupledIn vars B)

theorem sameComponent_equivalence (vars : CertVars C V) (B : Finset C) :
    Equivalence (SameComponent vars B) :=
  EqvGen.is_equivalence (CoupledIn vars B)

theorem sameComponent_of_coupled (vars : CertVars C V) (B : Finset C) (c1 c2 : C)
    (h : CoupledIn vars B c1 c2) : SameComponent vars B c1 c2 :=
  EqvGen.rel _ _ h

-- Section 2: component footprints and their disjointness.
-- This is the structural core: it is what makes "different component"
-- mean something stronger than "not directly sharing a variable" - it
-- rules out the chain case too (Scenario 5 in exp_b1_structural_bdd.py:
-- G1-G2-G3-G4 overlapping pairwise, G1 and G4 sharing nothing directly,
-- yet still one component and hence one footprint).

/-- The full set of variables reachable from c's component within B - not
    just Vars(c) itself, but the union over every certificate B-reachable
    from c via shared-variable chains. -/
def componentFootprint (vars : CertVars C V) (B : Finset C) (c : C) : Set V :=
  {v : V | ∃ c' ∈ B, SameComponent vars B c c' ∧ v ∈ vars c'}

theorem vars_subset_own_footprint (vars : CertVars C V) (B : Finset C) (c : C)
    (hc : c ∈ B) : (vars c : Set V) ⊆ componentFootprint vars B c :=
  fun v hv => ⟨c, hc, EqvGen.refl c, hv⟩

/-- The key structural fact: two certificates in genuinely different
    components have completely disjoint footprints, not just disjoint
    Vars(·). Proof: a shared variable between any pair drawn from the two
    footprints would directly couple that pair, which - chained through
    each element's own path back to c1 and c2 respectively - would put c1
    and c2 in the same component after all, contradicting the hypothesis. -/
theorem footprint_disjoint_of_diff_component (vars : CertVars C V) (B : Finset C)
    (c1 c2 : C) (hdiff : ¬ SameComponent vars B c1 c2) :
    componentFootprint vars B c1 ∩ componentFootprint vars B c2 = ∅ := by
  ext v
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨c1', hc1'B, hc1'same, hv1⟩, ⟨c2', hc2'B, hc2'same, hv2⟩⟩
  apply hdiff
  have hshare : dependent vars c1' c2' :=
    ⟨v, Finset.mem_inter.mpr ⟨hv1, hv2⟩⟩
  have hcoupled : CoupledIn vars B c1' c2' := ⟨hc1'B, hc2'B, hshare⟩
  have hsame_c1'c2' : SameComponent vars B c1' c2' := EqvGen.rel _ _ hcoupled
  exact EqvGen.trans _ _ _ hc1'same (EqvGen.trans _ _ _ hsame_c1'c2' (EqvGen.symm _ _ hc2'same))

/-- Same-component elements have the same footprint - the Set-valued
    counterpart of `compOf_eq_of_sameComponent` below, needed wherever a
    caller only knows a certificate is *somewhere* in c1's component, not
    literally c1 itself (e.g. PPGraphBDDMoserTardos.lean, where the
    resampled index at time t is some component-mate of c1, not c1). -/
theorem componentFootprint_eq_of_sameComponent (vars : CertVars C V) (B : Finset C)
    (c1 c2 : C) (h : SameComponent vars B c1 c2) :
    componentFootprint vars B c1 = componentFootprint vars B c2 := by
  ext v
  simp only [componentFootprint, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨c', hc'B, hc1c', hv⟩
    exact ⟨c', hc'B, EqvGen.trans _ _ _ (EqvGen.symm _ _ h) hc1c', hv⟩
  · rintro ⟨c', hc'B, hc2c', hv⟩
    exact ⟨c', hc'B, EqvGen.trans _ _ _ h hc2c', hv⟩

-- Section 3: non-interference of repair across different components.
-- `sat` stands for whatever "this certificate/obligation currently holds"
-- means in a given domain - a physical certificate condition in the
-- original CPS reading, or "this Lean subgoal is closed" in the
-- proof-search reading (exp_b3's ?n/?m examples). `Local` is the frame/
-- locality hypothesis this needs, made an explicit premise rather than an
-- assumption: evaluating c must depend only on the coordinates in Vars(c),
-- nothing else - exactly the same shape as `IsCylinderOver` in
-- PPGraphVariableLLL.lean, here for an arbitrary value type instead of ℝ.

variable {α : Type}

/-- sat's evaluation of c depends only on the instantiation restricted to
    Vars(c) - the locality/frame condition non-interference is built on.
    Not free: it must be checked for whatever `sat` a given application
    actually uses, exactly as `dependent`/`independent` already had to be
    checked (not assumed) for the CPS domain. -/
def Local (vars : CertVars C V) (sat : C → (V → α) → Prop) : Prop :=
  ∀ c, ∀ i1 i2 : V → α, (∀ v ∈ vars c, i1 v = i2 v) → (sat c i1 ↔ sat c i2)

/-- Non-interference: if a repair changes the instantiation only within c1's
    component's footprint (agrees with the original everywhere else), then
    for any c2 in a *different* component, sat c2's truth value is
    completely unaffected. This is deliberately NOT a claim that a repair
    exists, succeeds, or finds a satisfying instantiation for c1 itself -
    only that whatever it does to c1's own component, it cannot silently
    break anything outside it. The formal counterpart of what
    `hub_conflict_demo` (exp_b1_structural_bdd.py) showed going wrong
    *inside* one component when this locality is violated across a shared
    variable. -/
theorem repair_noninterference (vars : CertVars C V) (B : Finset C)
    (sat : C → (V → α) → Prop) (hloc : Local vars sat)
    (c1 c2 : C) (hc2B : c2 ∈ B) (hdiff : ¬ SameComponent vars B c1 c2)
    (i1 i2 : V → α) (h_agree : ∀ v ∉ componentFootprint vars B c1, i1 v = i2 v) :
    sat c2 i1 ↔ sat c2 i2 := by
  apply hloc c2 i1 i2
  intro v hv
  refine h_agree v (fun hv_in_footprint1 => ?_)
  have hv_in_footprint2 : v ∈ componentFootprint vars B c2 := ⟨c2, hc2B, EqvGen.refl c2, hv⟩
  have hboth : v ∈ componentFootprint vars B c1 ∩ componentFootprint vars B c2 :=
    ⟨hv_in_footprint1, hv_in_footprint2⟩
  rw [footprint_disjoint_of_diff_component vars B c1 c2 hdiff] at hboth
  exact hboth

/-- The safety guarantee extends to ALL of B outside c1's component at
    once, not just one chosen c2 - the formal version of "different BDD
    components are safe to repair in parallel": a repair confined to c1's
    footprint leaves every other certificate/obligation in B, in a
    different component, evaluated identically, simultaneously. Matches
    what exp_b1_structural_bdd.py's Scenario 9 (20-goal mixed snapshot)
    demonstrated by direct count (12 safe units, not 20, but never fewer
    than the component count) - here as a proved guarantee, not a count. -/
theorem repair_noninterference_all (vars : CertVars C V) (B : Finset C)
    (sat : C → (V → α) → Prop) (hloc : Local vars sat)
    (c1 : C) (i1 i2 : V → α) (h_agree : ∀ v ∉ componentFootprint vars B c1, i1 v = i2 v) :
    ∀ c2 ∈ B, ¬ SameComponent vars B c1 c2 → (sat c2 i1 ↔ sat c2 i2) :=
  fun c2 hc2B hdiff => repair_noninterference vars B sat hloc c1 c2 hc2B hdiff i1 i2 h_agree

-- Section 4: feasibility localizes to components.
-- The point: `lll_feasible` (from PPGraphProbabilistic.lean) checked over
-- the whole blocking set B is exactly equivalent to checking it
-- independently, component by component - the formal reason "Blocking
-- Dependency Decomposition" and "the Local Lemma" belong in the same
-- breath, not just two facts that happen to sit in the same file. In the
-- running example, B = {c1,c2,c3,c5,c6} splits into {c1,c2,c5,c6} and
-- {c3}; this section says lll_feasible on all of B is exactly
-- lll_feasible on {c1,c2,c5,c6} together with lll_feasible on {c3}
-- separately - checking the whole blocking set was never actually buying
-- anything the component-by-component check didn't already give.

/-- The component of B containing c - everything in B reachable from c via
    shared-variable chains, as an actual Finset (needed to reuse it as a
    blocking set argument to `lll_feasible`/`neighbors`, unlike
    `componentFootprint` in Section 2, which only needed to be a Set of
    variables). Needs classical choice for decidability of the (in general
    undecidable) `SameComponent` predicate - fine, since this is never
    meant to be computed, only reasoned about. -/
noncomputable def compOf (vars : CertVars C V) (B : Finset C) (c : C) : Finset C :=
  B.filter (SameComponent vars B c)

theorem mem_compOf_self (vars : CertVars C V) (B : Finset C) (c : C) (hc : c ∈ B) :
    c ∈ compOf vars B c := by
  simp only [compOf, Finset.mem_filter]
  exact ⟨hc, EqvGen.refl c⟩

theorem compOf_subset (vars : CertVars C V) (B : Finset C) (c : C) :
    compOf vars B c ⊆ B :=
  Finset.filter_subset _ _

/-- Each component is a single, well-defined Finset regardless of which of
    its elements you compute it from - two members of the same component
    have the same compOf. -/
theorem compOf_eq_of_sameComponent (vars : CertVars C V) (B : Finset C) (c1 c2 : C)
    (h : SameComponent vars B c1 c2) : compOf vars B c1 = compOf vars B c2 := by
  simp only [compOf]
  ext c'
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hc'B, hc1c'⟩
    exact ⟨hc'B, EqvGen.trans _ _ _ (EqvGen.symm _ _ h) hc1c'⟩
  · rintro ⟨hc'B, hc2c'⟩
    exact ⟨hc'B, EqvGen.trans _ _ _ h hc2c'⟩

/-- The key localization fact: c's neighbors within B are exactly the same
    as c's neighbors within its own component - restricting attention to
    the component never loses or gains a neighbor, since every actual
    neighbor of c is (by definition of coupling) already inside c's
    component. -/
theorem neighbors_eq_neighbors_compOf (vars : CertVars C V) (B : Finset C) (c : C)
    (hc : c ∈ B) : neighbors vars B c = neighbors vars (compOf vars B c) c := by
  ext c'
  simp only [neighbors, Finset.mem_filter]
  constructor
  · rintro ⟨hc'B, hne, hdep⟩
    have hcoupled : CoupledIn vars B c c' := ⟨hc, hc'B, hdep⟩
    have hsame : SameComponent vars B c c' := EqvGen.rel _ _ hcoupled
    have hc'_in_compOf : c' ∈ compOf vars B c := by
      simp only [compOf, Finset.mem_filter]; exact ⟨hc'B, hsame⟩
    exact ⟨hc'_in_compOf, hne, hdep⟩
  · rintro ⟨hc'_in_compOf, hne, hdep⟩
    exact ⟨compOf_subset vars B c hc'_in_compOf, hne, hdep⟩

/-- lll_condition_at is identical whether checked against B or against c's
    own component - an immediate consequence of the neighbor sets
    agreeing. -/
theorem lll_condition_localizes (p : C → Real) (x : LLLAssignment C)
    (vars : CertVars C V) (B : Finset C) (c : C) (hc : c ∈ B) :
    lll_condition_at p x vars B c ↔ lll_condition_at p x vars (compOf vars B c) c := by
  unfold lll_condition_at
  rw [neighbors_eq_neighbors_compOf vars B c hc]

/-- Main theorem: feasibility over the whole blocking set B is exactly
    feasibility checked independently, component by component. This is the
    formal justification for decomposing before checking the Local Lemma's
    numerical condition, rather than checking it over all of B at once -
    the two checks are provably the same content, just organized
    differently. -/
theorem lll_feasible_iff_componentwise (p : C → Real) (x : LLLAssignment C)
    (vars : CertVars C V) (B : Finset C) :
    lll_feasible p x vars B ↔ ∀ c ∈ B, lll_feasible p x vars (compOf vars B c) := by
  constructor
  · rintro ⟨hbound, hcond⟩ c0 hc0
    refine ⟨fun c hc => hbound c (compOf_subset vars B c0 hc), fun c hc => ?_⟩
    have hcB : c ∈ B := compOf_subset vars B c0 hc
    have hsame : SameComponent vars B c0 c := by
      simp only [compOf, Finset.mem_filter] at hc
      exact hc.2
    rw [compOf_eq_of_sameComponent vars B c0 c hsame]
    exact (lll_condition_localizes p x vars B c hcB).mp (hcond c hcB)
  · intro h
    refine ⟨fun c hc => (h c hc).1 c (mem_compOf_self vars B c hc), fun c hc => ?_⟩
    exact (lll_condition_localizes p x vars B c hc).mpr
      ((h c hc).2 c (mem_compOf_self vars B c hc))

-- Verification

#check @sameComponent_equivalence
#check @sameComponent_of_coupled
#check @vars_subset_own_footprint
#check @footprint_disjoint_of_diff_component
#check @componentFootprint_eq_of_sameComponent
#check @repair_noninterference
#check @repair_noninterference_all
#check @compOf
#check @mem_compOf_self
#check @compOf_subset
#check @compOf_eq_of_sameComponent
#check @neighbors_eq_neighbors_compOf
#check @lll_condition_localizes
#check @lll_feasible_iff_componentwise
