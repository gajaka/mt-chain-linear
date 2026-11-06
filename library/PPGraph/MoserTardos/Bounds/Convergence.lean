/-
  PPGraphMoserTardosConvergence.lean
  Convergence bound for the Fix-It / Moser-Tardos algorithm.

  Alon-Spencer, The Probabilistic Method, 4th ed., §5.7 ("Moser's
  Fix-It Algorithm"), Theorem 5.7.3 (pp. 84-85; equation (5.9), which
  defines the recursion, is on p. 83).

  Here we formalize the ALGEBRAIC core of the convergence bound:
  w(D, α) ≤ x(α), assuming that x bounds the failure probabilities p
  and satisfies the self-consistency condition from (5.9)-(5.10).

  In the book, w(D, α) is the sum of p[T] over all "weak Moser trees"
  rooted at α with depth at most D. This sum is described through the
  recursive decomposition (5.9), since directly enumerating all such
  trees would be impractical.

  Here we define w(D, α) directly by that recursion (mtWeight below),
  rather than deriving it from an explicit sum over a Finset of
  trees. The proof of Theorem 5.7.3 in the book also works directly
  with the recursion (5.9)-(5.10), so explicit tree enumeration is
  not needed for this proof.

  This also means that [Fintype ι] and the tree-enumeration machinery
  marked as "NOT attempted yet" in PPGraphMoserTardosWeight.lean are
  not needed for tree enumeration here. We only need [Fintype ι] in
  the final corollary to sum x over all elements of ι.

  The probabilistic part is still missing, namely the connection
  between w(D, α) and the expected number of resamplings E[TLOG].

  The book handles this through Theorems 5.7.1 and 5.7.2. Theorem
  5.7.1 expresses E[TLOG] as a sum, over Moser trees T, of the
  probabilities that T appears as Tn for some n. Theorem 5.7.2 then
  shows that each such probability is at most p(T), using an
  injective encoding of the independent random choices made by the
  process. We still do not have a probability model for the random
  process that generates the log, so the connection to E[TLOG]
  remains open for now.

  The injective encoding part is already proved in
  PPGraphMoserTardosInjectivity.lean through
  τC_injective_on_occurrences. Here, sum_mtWeight_le gives us the
  algebraic part of the bound from Theorem 5.7.3. Therefore, the
  Σ x(α) part is proved. The remaining work is to connect it to the
  expected number of resamplings once the probabilistic model of the
  process is done and verified.

  We use MTProcess and the neighbor relation from
  PPGraphMoserTardosWitness.lean, together with the tree-weight
  results from PPGraphMoserTardosWeight.lean.

  Author: Dragan Stosic, 2026.
-/

module

public import Mathlib.Tactic
public import Mathlib.Basic.NNReal.Basic
public import PPGraph.MoserTardos.Witness.Weight

@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped NNReal

variable {V : Type} [DecidableEq V]

-- Section 1: Γ+, the inclusive neighborhood the (5.9) product ranges over

open Classical in
/-- Γ+(α) as a finite set: α itself together with every neighbor of α.
    The book's ∼ here is reflexive by construction (p.81: "Note that
    α ∼ α"), which is why the product in (5.9) already includes β = α
    without a separate case; we keep the disjunction explicit rather
    than lean on `neighbor` being reflexive, since that would need an
    extra side lemma (nonempty footprints) never stated elsewhere in
    this repository. -/
noncomputable def plusNeighbors {S : VarSpaces V} {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : MTProcess S ι) (α : ι) : Finset ι :=
  Finset.univ.filter (fun β => β = α ∨ neighbor P α β)

-- Section 2: w(D, α), the (5.9) recursion (book p.83)

/-- w(D,α), defined directly by the recursion (5.9) rather than as a
    sum over an explicit Finset of trees: w(0,α) = p(α) (the only
    depth-0 tree is the bare root, book p.83), and w(D+1,α) = p(α) ·
    ∏_{β∈Γ+(α)} (1 + w(D,β)) -- one factor per candidate child label,
    "1" for "no child with that label" and "w(D,β)" for "one child
    labelled β, summed over its own possible subtrees of depth ≤ D". -/
noncomputable def mtWeight {S : VarSpaces V} {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : MTProcess S ι) (p : ι → ℝ≥0) : ℕ → ι → ℝ≥0
  | 0, α => p α
  | D + 1, α => p α * ∏ β ∈ plusNeighbors P α, (1 + mtWeight P p D β)

-- Section 3: Theorem 5.7.3 (book p.84-85)

/-- Alon-Spencer, Theorem 5.7.3: if x ≥ p pointwise (5.10's own
    standing hypothesis) and x satisfies the same self-consistency
    inequality that (5.9) turns into an equality for w, then
    w(D,α) ≤ x(α) at every depth D. Proof is a direct induction on D
    mirroring the book's own two-line argument (p.84-85): the base
    case is exactly the hypothesis x ≥ p; the inductive step
    substitutes w(D,β) ≤ x(β) into every factor of the defining
    product, then closes with the (5.10) hypothesis on x itself. -/
theorem mtWeight_le {S : VarSpaces V} {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : MTProcess S ι) (p x : ι → ℝ≥0)
    (h_dom : ∀ α, p α ≤ x α)
    (h_self : ∀ α, p α * ∏ β ∈ plusNeighbors P α, (1 + x β) ≤ x α) :
    ∀ D α, mtWeight P p D α ≤ x α := by
  intro D
  induction D with
  -- w(0,α) = p(α) ≤ x(α): exactly the standing hypothesis h_dom [p.84]
  | zero => intro α; exact h_dom α
  | succ D ih =>
    intro α
    -- w(D+1,α) = p(α)·∏(1+w(D,β)) ≤ p(α)·∏(1+x(β)) ≤ x(α), chaining
    -- the induction hypothesis into every factor and then (5.10) [p.84]
    calc mtWeight P p (D + 1) α
        = p α * ∏ β ∈ plusNeighbors P α, (1 + mtWeight P p D β) := rfl
      _ ≤ p α * ∏ β ∈ plusNeighbors P α, (1 + x β) := by
          apply mul_le_mul_of_nonneg_left _ zero_le
          apply Finset.prod_le_prod
          intro β _
          gcongr
          exact ih β
      _ ≤ x α := h_self α

/-- Purely algebraic shadow of Theorem 5.7.3's closing clause
    "E[TLOG] ≤ Σ_α x(α)": summing the pointwise bound over all of ι.
    No E[TLOG] appears on the left because none has been constructed
    in this repository yet (see the file docstring) -- this is the
    inequality that statement would reduce to, once one is. -/
theorem sum_mtWeight_le {S : VarSpaces V} {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : MTProcess S ι) (p x : ι → ℝ≥0)
    (h_dom : ∀ α, p α ≤ x α)
    (h_self : ∀ α, p α * ∏ β ∈ plusNeighbors P α, (1 + x β) ≤ x α) (D : ℕ) :
    ∑ α, mtWeight P p D α ≤ ∑ α, x α :=
  Finset.sum_le_sum (fun α _ => mtWeight_le P p x h_dom h_self D α)

-- Verification

#check @plusNeighbors
#check @mtWeight
#check @mtWeight_le
#check @sum_mtWeight_le
