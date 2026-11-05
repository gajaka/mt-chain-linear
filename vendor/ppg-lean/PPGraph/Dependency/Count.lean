/-
  PPGraphBDDCount.lean
  "Count of components = safe parallel units" - the corollary flagged as
  future work on 2026-09-05 (PPGraphBDD.lean), now cheap thanks to
  2026-09-20's PPGraphBDDLaplacian.lean: connects the SimpleGraph-based
  component COUNT (`Fintype.card (bddGraph vars B).ConnectedComponent`,
  which the Laplacian file already relates to the nullspace dimension) to
  the pre-existing, C-indexed `compOf` vocabulary that
  `repair_noninterference_all` (PPGraphBDD.lean Section 3) actually uses.

  The result: `repair_noninterference_all` already proves that repairs
  confined to two DIFFERENT compOf-groups never interfere. This file
  proves there are EXACTLY `Fintype.card (bddGraph vars B).ConnectedComponent`
  many such groups - so that count is not just an abstract spectral
  quantity (today's Laplacian-nullspace result), it is the precise number
  of independently, safely parallelizable repair units.

  Author: Dragan Stosic, 2026.
-/

module

public import PPGraph.Dependency.Decomposition
public import PPGraph.Dependency.Laplacian
public import Mathlib.Logic.Relation

@[expose] public section

open Relation
open scoped Classical

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {C V : Type} [DecidableEq C] [DecidableEq V] [Fintype V]

-- Section 1: compOf, as a Finset-valued function, is injective ACROSS
-- distinct components of B (the converse of `compOf_eq_of_sameComponent`,
-- restricted to members of B).

theorem sameComponent_of_compOf_eq (vars : CertVars C V) (B : Finset C) (c1 c2 : C)
    (hc1 : c1 ∈ B) (h : compOf vars B c1 = compOf vars B c2) :
    SameComponent vars B c1 c2 := by
  have h1 : c1 ∈ compOf vars B c1 := mem_compOf_self vars B c1 hc1
  rw [h] at h1
  exact EqvGen.symm _ _ (Finset.mem_filter.mp h1).2

-- Section 2: `compOf` lifts to the SimpleGraph quotient (well-defined on
-- Reachable-classes, via `compOf_eq_of_sameComponent` + today's
-- `reachable_iff_sameComponent` bridge), landing in the Finset
-- `B.image (compOf vars B)` - the set of ALL distinct component-groups.

/-- The component-group of a `ConnectedComponent`, as an element of
    `B.image (compOf vars B)` (bundled with its membership proof so the
    later bijection argument has a genuine Fintype on both sides). -/
noncomputable def compGroup (vars : CertVars C V) (B : Finset C) :
    (bddGraph vars B).ConnectedComponent → ↥(B.image (compOf vars B)) :=
  Quot.lift
    (fun c : ↥B => (⟨compOf vars B c.val,
        Finset.mem_image_of_mem _ c.property⟩ : ↥(B.image (compOf vars B))))
    (fun c1 c2 (h : (bddGraph vars B).Reachable c1 c2) => by
      have hsame : SameComponent vars B c1.val c2.val :=
        (reachable_iff_sameComponent vars B c1 c2).mp h
      exact Subtype.ext (compOf_eq_of_sameComponent vars B c1.val c2.val hsame))

theorem compGroup_injective (vars : CertVars C V) (B : Finset C) :
    Function.Injective (compGroup vars B) := by
  intro x y hxy
  induction x using Quot.ind with
  | _ c1 =>
    induction y using Quot.ind with
    | _ c2 =>
      have heq : compOf vars B c1.val = compOf vars B c2.val :=
        Subtype.ext_iff.mp hxy
      exact Quot.sound
        ((reachable_iff_sameComponent vars B c1 c2).mpr
          (sameComponent_of_compOf_eq vars B c1.val c2.val c1.property heq))

theorem compGroup_surjective (vars : CertVars C V) (B : Finset C) :
    Function.Surjective (compGroup vars B) := by
  rintro ⟨g, hg⟩
  rw [Finset.mem_image] at hg
  obtain ⟨c, hcB, hceq⟩ := hg
  refine ⟨(bddGraph vars B).connectedComponentMk ⟨c, hcB⟩, ?_⟩
  exact Subtype.ext hceq

theorem compGroup_bijective (vars : CertVars C V) (B : Finset C) :
    Function.Bijective (compGroup vars B) :=
  ⟨compGroup_injective vars B, compGroup_surjective vars B⟩

-- Section 3: THE COUNT. Exactly as many BDD components as distinct
-- compOf-groups - the concrete, repair-relevant restatement of today's
-- spectral component count.

/-- The number of BDD components equals the number of distinct
    `compOf`-groups partitioning `B` - i.e. the exact number of
    independently, safely parallelizable repair units guaranteed by
    `repair_noninterference_all`. Combined with
    `card_bddComponents_eq_finrank_ker_lapMatrix`
    (PPGraphBDDLaplacian.lean), this also equals the dimension of the
    dependency graph's Laplacian nullspace. -/
theorem card_bddComponents_eq_card_compOf_image (vars : CertVars C V) (B : Finset C) :
    Fintype.card (bddGraph vars B).ConnectedComponent = (B.image (compOf vars B)).card := by
  rw [← Fintype.card_coe (B.image (compOf vars B))]
  exact Fintype.card_of_bijective (compGroup_bijective vars B)

-- Section 4: packaging as "safe parallel units" - repairs confined to
-- DIFFERENT compOf-groups never interfere, and there are exactly
-- `card_bddComponents_eq_card_compOf_image`-many such groups.

variable {α : Type}

/-- The full statement: `B` splits into `Fintype.card
    (bddGraph vars B).ConnectedComponent`-many pairwise-disjoint,
    independently repairable groups. "Independently repairable" here means
    exactly what `repair_noninterference_all` guarantees: a repair
    confined to one group's footprint cannot affect `sat` for anything in
    a genuinely different group. This is the corollary flagged as future
    work on 2026-09-05, now closed. -/
theorem safe_parallel_units (vars : CertVars C V) (B : Finset C)
    (sat : C → (V → α) → Prop) (hloc : Local vars sat) (c1 : C)
    (i1 i2 : V → α) (h_agree : ∀ v ∉ componentFootprint vars B c1, i1 v = i2 v) :
    (∀ c2 ∈ B, ¬ SameComponent vars B c1 c2 → (sat c2 i1 ↔ sat c2 i2))
      ∧ Fintype.card (bddGraph vars B).ConnectedComponent = (B.image (compOf vars B)).card :=
  ⟨repair_noninterference_all vars B sat hloc c1 i1 i2 h_agree,
    card_bddComponents_eq_card_compOf_image vars B⟩

#check @card_bddComponents_eq_card_compOf_image
#check @safe_parallel_units

-- Explicit checks for all remaining helper theorems.
#check @compGroup_bijective
#check @compGroup_injective
#check @compGroup_surjective
#check @sameComponent_of_compOf_eq
