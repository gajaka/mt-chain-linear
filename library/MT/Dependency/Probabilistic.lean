/-
  PPGraphProbabilistic.lean
  Blocking Dependency Decomposition and LLL Feasibility

  The blocking set B(d,θ) has internal topology.
  G_B = (B, E_B) where (C_i, C_j) in E_B iff Vars(C_i) ∩ Vars(C_j) ≠ ∅.
  Connected components = shared dependency support.

  General LLL (Alon-Spencer, Lemma 5.1.1):
  Given events A_1,...,A_n with dependency graph G, if x_i in [0,1) satisfy
    Pr[A_i] ≤ x_i * ∏_{j in Γ(i)} (1 - x_j)  for all i
  then Pr[⋀ ¬A_i] > 0.

  A negative discriminant proves that no valid numerical LLL budget exists
  for the pair. It does not prove that a satisfying state or repair is absent.

  Author: Dragan Stosic, 2026.
-/

module

public import Mathlib.Tactic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Basic.Real.Basic

@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

-- Section 1: Dependency Graph

/- Running example for this whole file (same one used in PPGraphLLL.lean):
   certificates c1, c2, c3, c5, c6 with vars(c1)={v1,v2}, vars(c2)={v2,v3},
   vars(c5)={v1,v6}, vars(c6)={v2,v7}, vars(c3)={v4}. c1 and c2 share v2, c1
   and c5 share v1, c1 and c6 share v2 - all three are dependent on c1. c3
   shares nothing with c1 (or with c2, c5, c6) and is independent of all of
   them. This section just gives "shares a variable" a name; nothing here is
   drawn from the book itself - it's the concrete instantiation this project
   needs before Alon–Spencer's abstract dependency digraph D=(V,E) [Lemma
   5.1.1, p.70] can be applied to certificates at all. -/

variable {C V : Type} [DecidableEq C] [DecidableEq V]

/-- Vars(C): observable variables that certificate C depends on. -/
def CertVars (C V : Type) := C → Finset V

/-- C_i ~ C_j iff Vars(C_i) ∩ Vars(C_j) ≠ ∅. E.g. c1 ~ c2 via the shared
    variable v2. -/
def dependent (vars : CertVars C V) (c1 c2 : C) : Prop :=
  (vars c1 ∩ vars c2).Nonempty

/-- C_i ⊥ C_j iff Vars(C_i) ∩ Vars(C_j) = ∅. E.g. c1 ⊥ c3, since {v1,v2} and
    {v4} don't overlap. -/
def independent (vars : CertVars C V) (c1 c2 : C) : Prop :=
  vars c1 ∩ vars c2 = ∅

/-- Dependent iff not independent. -/
theorem dep_iff_not_indep (vars : CertVars C V) (c1 c2 : C) :
    dependent vars c1 c2 ↔ ¬ independent vars c1 c2 := by
  constructor
  · intro h
    simp [independent]
    exact Finset.Nonempty.ne_empty h
  · intro h
    simp [independent] at h
    exact Finset.nonempty_iff_ne_empty.mpr h

/-- Dependency is symmetric: c1 ~ c2 exactly when c2 ~ c1, since it only asks
    whether the two variable sets overlap. -/
theorem dependent_symm (vars : CertVars C V) (c1 c2 : C) :
    dependent vars c1 c2 → dependent vars c2 c1 := by
  simp [dependent]
  rw [Finset.inter_comm]
  exact id

-- Section 2: Blocking Set Topology

/-- Blocking set as a finite set of certificates. In the running example,
    B = {c1,c2,c3,c5,c6} - the certificates currently under scrutiny. -/
def BlockingSet (C : Type) := Finset C

/-- G_B restricted to blocking set: edge iff both in B, distinct, dependent.
    Plugging in the running example, c1 and c2 end up joined by an edge -
    they're both in B and share v2 - while c1 and c3 aren't, since c3
    doesn't touch any of c1's variables. Alon-Spencer leave the dependency
    digraph D=(V,E) abstract [p.70]; this is what it looks like once it's
    built from real certificates instead of just assumed as a given. -/
def blocking_dep_graph (vars : CertVars C V) (B : Finset C) (c1 c2 : C) : Prop :=
  c1 ∈ B ∧ c2 ∈ B ∧ c1 ≠ c2 ∧ dependent vars c1 c2

/-- v in shared support of S iff v in Vars(c) for all c in S. In the running
    example, v2 is in the shared support of {c1,c2,c6} - it's the one
    variable all three certificates have in common. -/
def in_shared_support (vars : CertVars C V) (S : Finset C) (v : V) : Prop :=
  ∀ c ∈ S, v ∈ vars c

/-- Membership in shared support implies membership in each component. -/
theorem shared_support_mem (vars : CertVars C V) (S : Finset C)
    (v : V) (c : C) (h_mem : c ∈ S) (h_shared : in_shared_support vars S v) :
    v ∈ vars c :=
  h_shared c h_mem

-- Section 3: General LLL (Alon-Spencer, Lemma 5.1.1)

/-- x : C → [0,1), one value per certificate - the "budget" x(c) from Lemma
    5.1.1 [p.70]. -/
def LLLAssignment (C : Type) := C → Real

/-- Γ(c) within B: certificates sharing at least one variable with c. For c1
    in the running example, neighbors vars B c1 = {c2,c5,c6}: everything in B
    that touches c1's variables, minus c1 itself. Alon-Spencer's dependency
    digraph [p.70] takes {j : (i,j) ∈ E} as given; here it's just read off
    from `dependent`. -/
def neighbors (vars : CertVars C V) (B : Finset C) (c : C) : Finset C :=
  B.filter (fun c' => c' ≠ c ∧ (vars c ∩ vars c').Nonempty)

/-- p(c) ≤ x(c) * ∏_{j ∈ Γ(c)} (1 - x(j)). This is Lemma 5.1.1's numerical
    hypothesis [p.70] for a single certificate c: e.g. for c1, it reads
    Pr[c1 fails] ≤ x(c1) · (1-x c2)(1-x c5)(1-x c6). -/
def lll_condition_at (p : C → Real) (x : LLLAssignment C)
    (vars : CertVars C V) (B : Finset C) (c : C) : Prop :=
  p c ≤ x c * (neighbors vars B c).prod (fun j => 1 - x j)

/-- All x in [0,1) and all conditions hold - the full hypothesis of Lemma
    5.1.1 [p.70], required for every certificate in B at once: a single
    budget x(c) ∈ [0,1) per certificate, satisfying lll_condition_at
    simultaneously for c1, c2, c3, c5, and c6. -/
def lll_feasible (p : C → Real) (x : LLLAssignment C)
    (vars : CertVars C V) (B : Finset C) : Prop :=
  (∀ c ∈ B, 0 ≤ x c ∧ x c < 1) ∧
  (∀ c ∈ B, lll_condition_at p x vars B c)

/-- If a feasible x assignment is given, it witnesses feasibility.
    This is the numerical layer only: it says a valid x exists.
    The probabilistic consequence (Pr[⋀ ¬A_i] > 0) requires
    a measure-theoretic argument not formalized here - that's exactly what
    PPGraphLLL.lean's `lll_positive_probability` supplies, reusing this same
    `lll_feasible` hypothesis. -/
theorem feasible_witness_exists (p : C → Real) (x : LLLAssignment C)
    (vars : CertVars C V) (B : Finset C)
    (h_feasible : lll_feasible p x vars B) :
    ∃ x : LLLAssignment C,
      (∀ c ∈ B, 0 ≤ x c ∧ x c < 1) ∧
      (∀ c ∈ B, lll_condition_at p x vars B c) :=
  ⟨x, h_feasible.1, h_feasible.2⟩

-- Section 4: Pair Infeasibility (Quadratic Discriminant)

/- Not from the book - this section is original: it asks a question Lemma
   5.1.1 never has to, namely "can lll_feasible ever actually FAIL for a
   given pair of certificates?" Take c1 and c2 from the running example
   (neighbors, since they share v2), restricted to just the two-certificate
   system p1 ≤ x1(1-x2), p2 ≤ x2(1-x1) (dropping c5, c6, c3 for the moment -
   this is the pairwise core of lll_condition_at when Γ(c1)∩B={c2} and
   Γ(c2)∩B={c1}). If Pr[c1 fails] = p1 = 0.5 and Pr[c2 fails] = p2 = 0.5,
   pair_discriminant 0.5 0.5 = (1-0.5+0.5)² - 4·0.5 = 1 - 2 = -1 < 0 - no
   budget (x1,x2) can make both LLL conditions hold at once. That's a
   genuine obstruction: c1 and c2 are too tightly coupled for this pairwise
   system to certify, no matter how the budgets are chosen. -/

/-- Discriminant of the quadratic a^2 - a(1-p1+p2) + p2 = 0.
    Arises from eliminating x1 in the pair system
    p1 ≤ x1(1-x2), p2 ≤ x2(1-x1). -/
def pair_discriminant (p1 p2 : Real) : Real :=
  (1 - p1 + p2)^2 - 4 * p2

/-- disc < 0 implies no (x1, x2) in [0,1)^2 satisfies both conditions. E.g.
    pair_discriminant 0.5 0.5 = -1 < 0, so no (x1,x2) can satisfy both
    0.5 ≤ x1(1-x2) and 0.5 ≤ x2(1-x1). This rules out the sufficient
    LLL budget system for that pair; it does not prove that no satisfying
    state or semantic repair exists. -/
theorem negative_disc_infeasible (p1 p2 : Real)
    (h_p1_pos : 0 < p1) (h_p2_pos : 0 < p2)
    (h_p1_lt : p1 < 1) (h_p2_lt : p2 < 1)
    (h_disc : pair_discriminant p1 p2 < 0) :
    ¬ ∃ (x1 x2 : Real), 0 ≤ x1 ∧ x1 < 1 ∧ 0 ≤ x2 ∧ x2 < 1 ∧
      p1 ≤ x1 * (1 - x2) ∧ p2 ≤ x2 * (1 - x1) := by
  intro ⟨x1, x2, hx1_lo, hx1_hi, hx2_lo, hx2_hi, h1, h2⟩
  unfold pair_discriminant at h_disc
  nlinarith [sq_nonneg (x2 - (1 - p1 + p2) / 2), sq_nonneg x1, sq_nonneg x2,
             mul_nonneg hx1_lo (by linarith : (0 : Real) ≤ 1 - x2),
             mul_nonneg hx2_lo (by linarith : (0 : Real) ≤ 1 - x1)]

-- Section 5: Repair Classification

/-- Numerical feasibility of the sufficient LLL budget conditions.
    For a singleton with p(c) < 1 and nonnegative p(c), choosing
    x(c) in [p(c),1) suffices. A probability model and its dependency
    hypotheses are separate from this numerical predicate. -/
def lll_budget_feasible (p : C → Real) (vars : CertVars C V)
    (component : Finset C) : Prop :=
  ∃ x : LLLAssignment C, lll_feasible p x vars component

/-- No assignment satisfies this sufficient LLL budget system. By
    Section 4's numbers, {c1,c2} is lll_budget_infeasible whenever
    Pr[c1 fails] = Pr[c2 fails] = 0.5 - negative_disc_infeasible rules out
    every (x1,x2), so no LLL budget can certify that pair. -/
def lll_budget_infeasible (p : C → Real) (vars : CertVars C V)
    (component : Finset C) : Prop :=
  ¬ lll_budget_feasible p vars component

/-- Classical exhaustiveness of numerical budget feasibility and its
    negation. This gives neither a decision procedure nor a refutation
    of semantic repairability when the sufficient criterion fails. -/
theorem lll_budget_feasible_or_infeasible (p : C → Real) (vars : CertVars C V)
    (component : Finset C) :
    lll_budget_feasible p vars component ∨ lll_budget_infeasible p vars component := by
  by_cases h : lll_budget_feasible p vars component
  · exact Or.inl h
  · exact Or.inr h


#check @dep_iff_not_indep
#check @dependent_symm
#check @shared_support_mem
#check @feasible_witness_exists
#check @negative_disc_infeasible
#check @lll_budget_feasible_or_infeasible
