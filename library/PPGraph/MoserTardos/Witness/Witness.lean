/-
  PPGraphMoserTardosWitness.lean
  Algorithmic Lovász Local Lemma (Moser-Tardos)

  Layer 3, Part A: dependency graph + witness tree data structure.
  Builds on PPGraphMoserTardosProcess.lean (MTProcess, mtTrajectory,
  mt_new_violation_overlaps).

  The backward construction of τ_C(t) from a log, and the injectivity
  argument (N_A = number of distinct proper witness trees rooted at A
  occurring in C), are deliberately NOT attempted here -- that
  construction (attach a new child to the vertex of MAXIMUM DEPTH,
  among current vertices v with C(i) ∈ Γ+([v]), scanning the log
  backwards) needs an addressable/zipper tree representation, not the
  plain immutable rose tree below. This file only sets up the graph
  and the tree SHAPE that construction targets, checked directly
  against Moser & Tardos, "A constructive proof of the general Lovász
  Local Lemma" (arXiv:0903.0544v3), Section 2, Definition of witness
  tree and Lemma 2.1 -- NOT Alon-Spencer §5.7, which (3rd ed., ~2008)
  predates this algorithm and covers Beck's unrelated 1991 method
  instead.

  Witness tree, verbatim (Section 2): "A witness tree τ = (T, σ_T) is
  a finite rooted tree T together with a labelling σ_T : V(T) → 𝒜 of
  its vertices with events such that the children of a vertex
  u ∈ V(T) receive labels from Γ+(σ_T(u))." Γ+(A) := Γ(A) ∪ {A} is the
  INCLUSIVE neighborhood, so a child MAY repeat its parent's own
  label. "If distinct children of the same vertex always receive
  distinct labels we call the witness tree proper" -- properness is
  a SIBLING-distinctness condition, not global distinctness.

  Author: Dragan Stosic, 2026.
-/

module

public import Mathlib.Tactic
public import PPGraph.MoserTardos.Process.Process

@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {V : Type} [DecidableEq V]

-- -------------------------------------------------------------------
-- Dependency graph
-- -------------------------------------------------------------------

/-- Two events are neighbors when their footprints overlap -- the
    dependency graph the whole LLL / Moser-Tardos analysis is stated
    over. -/
def neighbor {S : VarSpaces V} {ι : Type} (P : MTProcess S ι) (i j : ι) : Prop :=
  ¬ Disjoint (P.footprint i) (P.footprint j)

theorem neighbor_symm {S : VarSpaces V} {ι : Type} (P : MTProcess S ι) (i j : ι) :
    neighbor P i j → neighbor P j i := by
  intro h hcontra
  exact h hcontra.symm

/-- `mt_new_violation_overlaps`, restated in dependency-graph language:
    a newly-violated event is a neighbor of the event just resampled. -/
theorem mt_new_violation_neighbor {S : VarSpaces V} {ι : Type} (P : MTProcess S ι)
    (log : ℕ → ι × MTState S) (ω0 : MTState S) (t : ℕ) (j : ι)
    (h_new : mtTrajectory P log ω0 t ∉ P.bad j)
    (h_now : mtTrajectory P log ω0 (t + 1) ∈ P.bad j) :
    neighbor P (log t).1 j :=
  mt_new_violation_overlaps P log ω0 t j h_new h_now

-- -------------------------------------------------------------------
-- Witness tree data structure
-- -------------------------------------------------------------------

/-- A witness tree: a finite rooted tree whose nodes are labeled by
    event indices. Pure shape only -- no requirement yet that it
    respects the dependency graph (`WellFormed` below adds that), and
    no link yet to an actual log. -/
inductive WTree (ι : Type) : Type
  | mk : ι → List (WTree ι) → WTree ι

/-- The label at the root of a witness tree. -/
def WTree.label {ι : Type} : WTree ι → ι
  | mk i _ => i

/-- The children of the root. -/
def WTree.children {ι : Type} : WTree ι → List (WTree ι)
  | mk _ cs => cs

/-- Number of nodes in the tree. -/
def WTree.size {ι : Type} : WTree ι → ℕ
  | mk _ cs => 1 + (cs.map WTree.size).sum

theorem WTree.size_pos {ι : Type} (τ : WTree ι) : 0 < τ.size := by
  cases τ with
  | mk i cs => simp only [WTree.size]; omega

/-- A witness tree is well-formed with respect to a Moser-Tardos
    instance P if every child's label lies in Γ+ of its own parent's
    label -- i.e. the child either REPEATS the parent's own event or
    is a genuine neighbor of it. This matches the paper's definition
    exactly (children draw labels from the INCLUSIVE neighborhood
    Γ+(σ_T(u)), not the exclusive one) -- a child equal to its parent
    is allowed; only siblings are constrained, by `Proper` below. -/
def WTree.WellFormed {S : VarSpaces V} {ι : Type} (P : MTProcess S ι) : WTree ι → Prop
  | mk i cs => (∀ c ∈ cs, c.label = i ∨ neighbor P i c.label) ∧
      ∀ c ∈ cs, WTree.WellFormed P c

/-- A single node with no children is trivially well-formed. -/
theorem WTree.wellFormed_singleton {S : VarSpaces V} {ι : Type} (P : MTProcess S ι) (i : ι) :
    WTree.WellFormed P (WTree.mk i []) := by
  simp [WTree.WellFormed]

/-- A witness tree is *proper* if, at every vertex, its children carry
    pairwise distinct labels -- a SIBLING condition only, per the
    paper's definition; it says nothing about non-sibling vertices
    sharing a label (which is common, since `WellFormed` explicitly
    allows a child to repeat its own parent's label). -/
def WTree.Proper {ι : Type} : WTree ι → Prop
  | mk _ cs => cs.Pairwise (fun a b => a.label ≠ b.label) ∧ ∀ c ∈ cs, WTree.Proper c

/-- A single node with no children is trivially proper. -/
theorem WTree.proper_singleton {ι : Type} (i : ι) :
    WTree.Proper (WTree.mk i ([] : List (WTree ι))) := by
  simp [WTree.Proper]

-- -------------------------------------------------------------------
-- Verification
-- -------------------------------------------------------------------

#check @neighbor
#check @neighbor_symm
#check @mt_new_violation_neighbor
#check @WTree
#check @WTree.label
#check @WTree.children
#check @WTree.size
#check @WTree.size_pos
#check @WTree.WellFormed
#check @WTree.wellFormed_singleton
#check @WTree.Proper
#check @WTree.proper_singleton
