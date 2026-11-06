/-
  PPGraphMoserTardosWeight.lean
  Algorithmic Lovász Local Lemma (Moser-Tardos)

  Layer 4, Part A: tree weight -- the purely combinatorial quantity
  p[T] from Alon-Spencer, "The Probabilistic Method", 4th ed., §5.7
  ("Moser's Fix-It Algorithm"), used in Theorem 5.7.1 and 5.7.3.

  Builds on PPGraphMoserTardosWitness.lean (WTree, WellFormed, Proper).
  "Weak Moser Tree" in the book's terminology = WTree.WellFormed ∧
  WTree.Proper here -- the book deliberately relaxes its stronger
  "Moser Tree" (same-depth distinctness) to exactly this weaker,
  sibling-only notion for the summation argument, matching what we
  already built.

  p[T] is defined, verbatim per the book: "the product of the p[α],
  where α ranges over the labels of the nodes... when α appears u
  times, the factor p[α] appears u times." The recursive w(D,α) =
  ∑_{T, depth ≤ D} p[T] sum (needed for Theorem 5.7.3's induction)
  requires enumerating weak Moser trees of bounded depth, which needs
  [Fintype ι] and tree-enumeration machinery -- NOT attempted yet;
  this file only sets up the weight function itself.

  Author: Dragan Stosic, 2026.
-/

module

public import Mathlib.Tactic
public import Mathlib.Basic.NNReal.Basic
public import PPGraph.MoserTardos.Witness.Witness

@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped NNReal

/-- The weight p[T] of a witness tree: the product of p over all node
    labels, with multiplicity. -/
def WTree.weight {ι : Type} (p : ι → ℝ≥0) : WTree ι → ℝ≥0
  | mk i cs => p i * (cs.map (WTree.weight p)).prod

theorem WTree.weight_singleton {ι : Type} (p : ι → ℝ≥0) (i : ι) :
    (WTree.mk i ([] : List (WTree ι))).weight p = p i := by
  simp [WTree.weight]

theorem WTree.weight_children {ι : Type} (p : ι → ℝ≥0) (i : ι) (cs : List (WTree ι)) :
    (WTree.mk i cs).weight p = p i * (cs.map (WTree.weight p)).prod := by
  simp [WTree.weight]

/-- Weight is monotone in `p`: if `p ≤ q` pointwise then every tree's
    weight under `p` is at most its weight under `q`. This is the
    structural fact behind substituting a bound `x ≥ p` into the
    weight and still getting a valid upper bound -- exactly what
    Theorem 5.7.3's hypothesis `x[α] ≥ p[α]` is used for. -/
theorem WTree.weight_mono {ι : Type} {p q : ι → ℝ≥0} (h : ∀ i, p i ≤ q i) :
    ∀ τ : WTree ι, τ.weight p ≤ τ.weight q
  | mk i cs => by
    rw [WTree.weight_children, WTree.weight_children]
    exact mul_le_mul (h i)
      (List.prod_le_prod (fun c _ => WTree.weight_mono h c))
      zero_le zero_le

#check @WTree.weight
#check @WTree.weight_singleton
#check @WTree.weight_children
#check @WTree.weight_mono
