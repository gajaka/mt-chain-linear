/-
  PPGraphBDDMoserTardos.lean
  Connects Blocking Dependency Decomposition (PPGraphBDD.lean) to the
  Moser-Tardos resampling process (PPGraphMoserTardosProcess.lean).

  Not from the book - original, same-day follow-up to PPGraphBDD.lean's
  Section 4 (which connected BDD to `lll_feasible`, the STATIC feasibility
  check). This file is the DYNAMIC analog: `lll_feasible_iff_componentwise`
  said checking feasibility over a whole blocking set is the same as
  checking it component by component; this file says RUNNING Moser-Tardos
  confined to one component provably never touches another.

  The connection turns out to already be half-built: PPGraphMoserTardosProcess.lean's
  `mt_step_preserves_unrelated` (resampling an event can't change whether a
  disjoint-footprint event is violated) is exactly the single-step version
  of the non-interference principle PPGraphBDD.lean formalizes generally.
  What was missing is the bridge - showing that "different BDD component"
  (SameComponent's negation) implies the footprint-disjointness
  `mt_step_preserves_unrelated` actually needs, and then iterating that
  single step across an entire trajectory.

  An `MTProcess`'s `footprint : ι → Finset V` field is literally a
  `CertVars ι V` (both are just `ι → Finset V`), so all of PPGraphBDD.lean's
  vocabulary (`SameComponent`, `compOf`, `componentFootprint`, ...) applies
  directly with C := ι and vars := P.footprint - no new dependency-graph
  machinery needed, just the bridge argument.

  Author: Dragan Stosic, 2026.
-/

module

public import Mathlib.Tactic
public import PPGraph.Dependency.Decomposition
public import PPGraph.MoserTardos.Process.Process

@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {V : Type} [DecidableEq V] {ι : Type} [DecidableEq ι]

/-- A log "stays within c1's component of B" if every index it ever
    resamples belongs to c1's BDD component (within B). -/
def StaysWithinComponent {S : VarSpaces V} (P : MTProcess S ι) (B : Finset ι)
    (log : ℕ → ι × MTState S) (c1 : ι) : Prop :=
  ∀ t, (log t).1 ∈ compOf P.footprint B c1

/-- The bridge: if the log stays within c1's component, then at any time
    step the index it resamples has a footprint disjoint from any j sitting
    in a genuinely different component. This is exactly the hypothesis
    `mt_step_preserves_unrelated` needs - the rest of this file is just
    iterating that single-step fact across a whole trajectory. -/
theorem stays_within_step_disjoint {S : VarSpaces V} (P : MTProcess S ι) (B : Finset ι)
    (log : ℕ → ι × MTState S) (c1 : ι) (h_stay : StaysWithinComponent P B log c1)
    (j : ι) (hjB : j ∈ B) (hdiff : ¬ SameComponent P.footprint B c1 j) (t : ℕ) :
    Disjoint (P.footprint (log t).1) (P.footprint j) := by
  rw [Finset.disjoint_left]
  intro v hv1 hv2
  have h_resampled_same : SameComponent P.footprint B c1 (log t).1 := by
    have h := h_stay t
    simp only [compOf, Finset.mem_filter] at h
    exact h.2
  have hv1' : v ∈ componentFootprint P.footprint B c1 := by
    rw [componentFootprint_eq_of_sameComponent P.footprint B c1 (log t).1 h_resampled_same]
    exact vars_subset_own_footprint P.footprint B (log t).1
      (compOf_subset P.footprint B c1 (h_stay t)) hv1
  have hv2' : v ∈ componentFootprint P.footprint B j :=
    vars_subset_own_footprint P.footprint B j hjB hv2
  have hboth : v ∈ componentFootprint P.footprint B c1 ∩ componentFootprint P.footprint B j :=
    ⟨hv1', hv2'⟩
  rw [footprint_disjoint_of_diff_component P.footprint B c1 j hdiff] at hboth
  exact hboth

/-- Main theorem, the dynamic analog of `lll_feasible_iff_componentwise`:
    if the log stays within c1's component, the trajectory's
    violated-status of any j in a genuinely different component never
    changes, at any time t - Moser-Tardos, confined to one BDD component,
    provably never touches another. -/
theorem mt_trajectory_localizes {S : VarSpaces V} (P : MTProcess S ι) (B : Finset ι)
    (log : ℕ → ι × MTState S) (ω0 : MTState S) (c1 : ι)
    (h_stay : StaysWithinComponent P B log c1)
    (j : ι) (hjB : j ∈ B) (hdiff : ¬ SameComponent P.footprint B c1 j) (t : ℕ) :
    (mtTrajectory P log ω0 t ∈ P.bad j) ↔ (mtTrajectory P log ω0 0 ∈ P.bad j) := by
  induction t with
  | zero => rfl
  | succ n ih =>
    have hstep := mt_step_preserves_unrelated P log ω0 n j
      (stays_within_step_disjoint P B log c1 h_stay j hjB hdiff n)
    exact hstep.symm.trans ih

-- Verification

#check @StaysWithinComponent
#check @stays_within_step_disjoint
#check @mt_trajectory_localizes
