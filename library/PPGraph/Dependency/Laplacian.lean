/-
  PPGraphBDDLaplacian.lean
  Bridges BDD's own `SameComponent`/`compOf` vocabulary (PPGraphBDD.lean,
  built on `Relation.EqvGen` by deliberate 2026-09-05 design choice, to
  avoid `SimpleGraph`'s Decidable/Fintype overhead) to Mathlib's
  `SimpleGraph.ConnectedComponent`, so the already-proved
  `card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix`
  ("component count = dimension of the Laplacian's nullspace") becomes
  available for BDD components. Nothing here is a new mathematical fact;
  the content is entirely the transfer between the two formalisms.

  The graph lives on the subtype ↥B (certificates in the blocking set),
  built via `SimpleGraph.fromRel dependent` - `fromRel` symmetrizes and
  removes the diagonal automatically, so `dependent`'s own reflexivity
  (`dependent vars c c` can hold) is harmless.

  Author: Dragan Stosic, 2026.
-/

module

public import PPGraph.Dependency.Decomposition
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix

@[expose] public section

open scoped Classical Matrix

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {C V : Type} [DecidableEq C] [DecidableEq V] [Fintype V]

-- Section 1: the graph on ↥B and its relation to `dependent`/`CoupledIn`.

/-- The dependency graph on the certificates of `B`, as a genuine
    `SimpleGraph` on the subtype ↥B. `fromRel` handles symmetrization and
    irreflexivity, so we can feed it `dependent` directly. -/
def bddGraph (vars : CertVars C V) (B : Finset C) : SimpleGraph (↥B) :=
  SimpleGraph.fromRel (fun c1 c2 : ↥B => dependent vars c1.val c2.val)

noncomputable instance bddGraph_decidableRel (vars : CertVars C V) (B : Finset C) :
    DecidableRel (bddGraph vars B).Adj := by
  unfold bddGraph
  infer_instance

theorem bddGraph_adj_iff (vars : CertVars C V) (B : Finset C) (c1 c2 : ↥B) :
    (bddGraph vars B).Adj c1 c2 ↔ c1 ≠ c2 ∧ dependent vars c1.val c2.val := by
  unfold bddGraph
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, h | h⟩
    · exact ⟨hne, h⟩
    · exact ⟨hne, dependent_symm vars c2.val c1.val h⟩
  · rintro ⟨hne, h⟩
    exact ⟨hne, Or.inl h⟩

/-- `Adj` implies `dependent` on the underlying values - the easy half of
    the ReflTransGen bridge. -/
theorem adj_imp_dependent (vars : CertVars C V) (B : Finset C) (c1 c2 : ↥B)
    (h : (bddGraph vars B).Adj c1 c2) : dependent vars c1.val c2.val :=
  ((bddGraph_adj_iff vars B c1 c2).mp h).2

/-- `dependent` implies reachability-in-one-or-zero-steps of `Adj` - the
    harder half, handled by splitting on whether `c1 = c2`. -/
theorem dependent_imp_reflTransGen_adj (vars : CertVars C V) (B : Finset C) (c1 c2 : ↥B)
    (h : dependent vars c1.val c2.val) :
    Relation.ReflTransGen (bddGraph vars B).Adj c1 c2 := by
  by_cases heq : c1 = c2
  · exact heq ▸ Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single ((bddGraph_adj_iff vars B c1 c2).mpr ⟨heq, h⟩)

/-- The reflexive-transitive closure of `Adj` coincides with that of the
    underlying `dependent` relation (no diagonal exclusion needed once we
    take the closure) - `ReflTransGen.mono` one way, `mono` +
    `reflTransGen_idem` the other. -/
theorem reflTransGen_adj_eq_reflTransGen_dependent (vars : CertVars C V) (B : Finset C) :
    Relation.ReflTransGen (bddGraph vars B).Adj
      = Relation.ReflTransGen (fun c1 c2 : ↥B => dependent vars c1.val c2.val) := by
  apply le_antisymm
  · exact Relation.ReflTransGen.mono (adj_imp_dependent vars B)
  · calc Relation.ReflTransGen (fun c1 c2 : ↥B => dependent vars c1.val c2.val)
        ≤ Relation.ReflTransGen (Relation.ReflTransGen (bddGraph vars B).Adj) :=
          Relation.ReflTransGen.mono (dependent_imp_reflTransGen_adj vars B)
      _ = Relation.ReflTransGen (bddGraph vars B).Adj := Relation.reflTransGen_eq_self

-- Section 2: SameComponent (EqvGen on C, restricted to B) vs Reachable (on ↥B).

/-- Forward direction: reachability in the subtype graph implies
    `SameComponent` on the underlying values. By induction on the walk. -/
theorem reachable_imp_sameComponent (vars : CertVars C V) (B : Finset C) (c1 c2 : ↥B)
    (h : (bddGraph vars B).Reachable c1 c2) : SameComponent vars B c1.val c2.val := by
  rw [(bddGraph vars B).reachable_iff_reflTransGen, reflTransGen_adj_eq_reflTransGen_dependent] at h
  induction h with
  | refl => exact (sameComponent_equivalence vars B).refl c1.val
  | tail _ hstep ih =>
      exact (sameComponent_equivalence vars B).trans ih
        (sameComponent_of_coupled vars B _ _ ⟨(Finset.coe_mem _), (Finset.coe_mem _), hstep⟩)

/-- Every `SameComponent` pair is either both-in-B, or literally equal
    (the only way `EqvGen` reaches a pair without ever invoking `CoupledIn`,
    whose own definition forces both endpoints into `B`). This is what
    recovers the midpoint's membership in the `trans` case below, since
    `EqvGen.trans` only hands us the two sub-relations, not a membership
    proof for the point where they meet. -/
theorem sameComponent_mem_or_eq (vars : CertVars C V) (B : Finset C) :
    ∀ a b : C, SameComponent vars B a b → (a ∈ B ∧ b ∈ B) ∨ a = b := by
  intro a b h
  induction h with
  | rel a b hcoupled => exact Or.inl ⟨hcoupled.1, hcoupled.2.1⟩
  | refl a => exact Or.inr rfl
  | symm a b _ ih =>
      rcases ih with ⟨ha, hb⟩ | heq
      · exact Or.inl ⟨hb, ha⟩
      · exact Or.inr heq.symm
  | trans a b c _ _ ihab ihbc =>
      rcases ihab with ⟨ha, hb⟩ | hab
      · rcases ihbc with ⟨_, hc⟩ | hbc
        · exact Or.inl ⟨ha, hc⟩
        · exact Or.inl ⟨ha, hbc ▸ hb⟩
      · rcases ihbc with ⟨hb, hc⟩ | hbc
        · exact Or.inl ⟨hab ▸ hb, hc⟩
        · exact Or.inr (hab.trans hbc)

/-- Backward direction: `SameComponent` on values that both lie in `B`
    implies reachability in the subtype graph. By induction on the
    `EqvGen` derivation, generalizing over arbitrary endpoints (with their
    membership proofs) rather than the fixed `c1 c2 : ↥B` - this is what
    lets the `symm`/`trans` cases of `EqvGen` go through. -/
theorem sameComponent_imp_reachable (vars : CertVars C V) (B : Finset C) :
    ∀ a b : C, SameComponent vars B a b →
      ∀ (ha : a ∈ B) (hb : b ∈ B), (bddGraph vars B).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
  intro a b h
  induction h with
  | rel a b hcoupled =>
      intro ha hb
      exact ((bddGraph vars B).reachable_iff_reflTransGen ⟨a, ha⟩ ⟨b, hb⟩).mpr
        (dependent_imp_reflTransGen_adj vars B ⟨a, ha⟩ ⟨b, hb⟩ hcoupled.2.2)
  | refl a => intro ha hb; exact SimpleGraph.Reachable.refl (⟨a, ha⟩ : ↥B)
  | symm a b _ ih => intro ha hb; exact (ih hb ha).symm
  | trans a b c hab hbc ihab ihbc =>
      intro ha hc
      rcases sameComponent_mem_or_eq vars B a b hab with ⟨_, hb⟩ | heq
      · exact (ihab ha hb).trans (ihbc hb hc)
      · exact heq ▸ ihbc (heq ▸ ha) hc

/-- Combining both directions: reachability in the subtype graph is
    exactly `SameComponent` on the underlying values. -/
theorem reachable_iff_sameComponent (vars : CertVars C V) (B : Finset C) (c1 c2 : ↥B) :
    (bddGraph vars B).Reachable c1 c2 ↔ SameComponent vars B c1.val c2.val :=
  ⟨reachable_imp_sameComponent vars B c1 c2,
    fun h => sameComponent_imp_reachable vars B c1.val c2.val h c1.property c2.property⟩

-- Section 3: the result - component count is the Laplacian's nullspace dimension.

/-- THE SPECTRAL BRIDGE: the number of BDD components of `B` equals the
    dimension of the nullspace of the BDD dependency graph's Laplacian
    matrix. Free consequence of Mathlib's own
    `card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix`, applied to
    `bddGraph vars B`. -/
theorem card_bddComponents_eq_finrank_ker_lapMatrix (vars : CertVars C V) (B : Finset C) :
    Fintype.card (bddGraph vars B).ConnectedComponent
      = Module.finrank ℝ ((bddGraph vars B).lapMatrix ℝ).toLin'.ker :=
  (bddGraph vars B).card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix

#check @reachable_iff_sameComponent
#check @card_bddComponents_eq_finrank_ker_lapMatrix

-- Explicit checks for all remaining helper theorems.
#check @adj_imp_dependent
#check @bddGraph_adj_iff
#check @dependent_imp_reflTransGen_adj
#check @reachable_imp_sameComponent
#check @reflTransGen_adj_eq_reflTransGen_dependent
#check @sameComponent_imp_reachable
#check @sameComponent_mem_or_eq
