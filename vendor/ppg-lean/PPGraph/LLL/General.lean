/-
  PPGraphLLL.lean
  Lovász Local Lemma for PPG Blocking Sets

  Proof follows Alon-Spencer Lemma 5.1.1.
  Structure: base case → denominator bound → inductive step → main theorem.

  Author: Dragan Stosic, 2026.
-/

module

public import Mathlib.Tactic
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.MeasureTheory.Measure.Basic
public import Mathlib.MeasureTheory.Measure.CompleteLattice
public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.MeasureTheory.Measure.Filter
public import Mathlib.MeasureTheory.Measure.Interval
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.Measure.OuterMeasure
public import Mathlib.MeasureTheory.Measure.Sum
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Prod
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Algebra.Order.LiminfLimsup
public import PPGraph.Dependency.Probabilistic

@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory

variable {Ω : Type} [MeasurableSpace Ω]
variable {C V : Type} [DecidableEq C] [DecidableEq V] [Fintype C]

-- Section 1: Events and Definitions

/-- Bad event assignment. -/
def BadEvents (C Ω : Type) [MeasurableSpace Ω] := C → Set Ω

/-- All bad events are measurable. -/
def all_measurable (A : BadEvents C Ω) : Prop :=
  ∀ c : C, MeasurableSet (A c)

/-- Pass event = complement of bad event. -/
def pass_event (A : BadEvents C Ω) (c : C) : Set Ω := (A c)ᶜ

/-- Intersection of pass events over a set S. -/
def all_pass (A : BadEvents C Ω) (S : Finset C) : Set Ω :=
  ⋂ c ∈ S, pass_event A c

/-- all_pass of empty set is univ. -/
theorem all_pass_empty (A : BadEvents C Ω) : all_pass A ∅ = Set.univ := by
  simp [all_pass]

/-- all_pass is monotone: larger S gives smaller set. -/
theorem all_pass_subset (A : BadEvents C Ω) (S T : Finset C) (h : S ⊆ T) :
    all_pass A T ⊆ all_pass A S := by
  intro ω hω
  simp [all_pass, pass_event] at *
  exact fun c hc => hω c (h hc)

/-- all_pass of union. -/
theorem all_pass_union (A : BadEvents C Ω) (S T : Finset C) :
    all_pass A (S ∪ T) = all_pass A S ∩ all_pass A T := by
  ext ω
  simp [all_pass, pass_event, Finset.mem_union]
  constructor
  · intro h
    exact ⟨fun c hc => h c (Or.inl hc), fun c hc => h c (Or.inr hc)⟩
  · intro ⟨h1, h2⟩ c hc
    cases hc with
    | inl h => exact h1 c h
    | inr h => exact h2 c h

/-- all_pass of insert. -/
theorem all_pass_insert (A : BadEvents C Ω) (S : Finset C) (c : C) (hc : c ∉ S) :
    all_pass A (insert c S) = pass_event A c ∩ all_pass A S := by
  rw [Finset.insert_eq]
  rw [all_pass_union]
  congr 1
  simp [all_pass, pass_event]

/-- all_pass is measurable if all events are. -/
theorem all_pass_measurable (A : BadEvents C Ω) (S : Finset C)
    (h_meas : all_measurable A) : MeasurableSet (all_pass A S) := by
  apply MeasurableSet.iInter
  intro c
  apply MeasurableSet.iInter
  intro _
  exact (h_meas c).compl

-- Section 2: Product Bounds for x values

/-- Product of (1-x_j) over a finset is positive when all x_j < 1. -/
theorem prod_one_sub_pos (x : C → Real) (S : Finset C)
    (h_bound : ∀ c ∈ S, 0 ≤ x c ∧ x c < 1) :
    0 < ∏ j ∈ S, (1 - x j) := by
  apply Finset.prod_pos
  intro j hj
  have := (h_bound j hj).2
  linarith

/-- Product of (1-x_j) over a finset is at most 1. -/
theorem prod_one_sub_le_one (x : C → Real) (S : Finset C)
    (h_bound : ∀ c ∈ S, 0 ≤ x c ∧ x c < 1) :
    ∏ j ∈ S, (1 - x j) ≤ 1 := by
  apply Finset.prod_le_one₀
  · intro j hj
    have := (h_bound j hj).2
    linarith
  · intro j hj
    have := (h_bound j hj).1
    linarith

/-- x_i * prod ≤ x_i when prod ≤ 1 and x_i ≥ 0. -/
theorem x_mul_prod_le (x : C → Real) (i : C) (S : Finset C)
    (h_xi_pos : 0 ≤ x i)
    (h_bound : ∀ c ∈ S, 0 ≤ x c ∧ x c < 1) :
    x i * ∏ j ∈ S, (1 - x j) ≤ x i := by
  have h_prod := prod_one_sub_le_one x S h_bound
  calc x i * ∏ j ∈ S, (1 - x j)
      ≤ x i * 1 := by apply mul_le_mul_of_nonneg_left h_prod h_xi_pos
    _ = x i := mul_one (x i)

-- Section 3: LLL Independence and Feasibility

/-- Probability of bad event c. -/
noncomputable def event_prob (A : BadEvents C Ω) (μ : Measure Ω) (c : C) : Real :=
  (μ (A c)).toReal

/-- LLL independence: A_i is independent of non-neighbors. -/
def lll_independence (A : BadEvents C Ω) (μ : Measure Ω)
    (vars : CertVars C V) (B : Finset C) : Prop :=
  ∀ c ∈ B, ∀ S₂ : Finset C,
    (∀ s ∈ S₂, s ∈ B ∧ s ≠ c ∧ independent vars c s) →
    μ (A c ∩ all_pass A S₂) = μ (A c) * μ (all_pass A S₂)

/-- The good event. -/
def good_event (A : BadEvents C Ω) (B : Finset C) : Set Ω :=
  all_pass A B

-- Section 4: Base Case (s = 0)

/-- Base case (s = 0) of the induction proving (5.1) [Alon–Spencer, Lemma 5.1.1
    proof, p.70]: Pr[Ai | ⋀_{j∈∅} ¬Aj] = Pr[Ai] ≤ xi · ∏_{(i,j)∈E}(1-xj) ≤ xi.
    Book: "This is certainly true for s = 0." - the product-bound step is left
    implicit there; spelled out here via `x_mul_prod_le`.

    In the running certificate example used from Section 5 onward (B =
    {c1,c2,c3,c5,c6}, i = c1), this is the case S = ∅: nothing has been
    conditioned on yet, so the claim is just the bare "Pr[c1 fails] ≤ x(c1)",
    before c2, c3, c5, c6 enter the picture at all. -/
theorem lll_base_case (A : BadEvents C Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (vars : CertVars C V) (B : Finset C)
    (x : LLLAssignment C)
    (h_feasible : lll_feasible (event_prob A μ) x vars B) :
    ∀ i ∈ B, (μ (A i)).toReal ≤ x i := by
  intro i hi
  -- s = 0 case of (5.1): S = ∅, so "Pr[Ai | ⋀_S ¬Aj]" has nothing to condition
  -- on and is just Pr[Ai]. The book waves this through as "certainly true"
  -- [p.70] - the actual content is the Lemma 5.1.1 hypothesis itself:
  -- Pr[Ai] ≤ xi · ∏_{(i,j)∈E}(1-xj) [p.70, unlabeled display].
  have h_cond := h_feasible.2 i hi
  unfold lll_condition_at at h_cond
  -- same hypothesis line [p.70]: 0 ≤ xj < 1 for every neighbor j - need this
  -- to know the product on the right is itself ≤ 1.
  have h_bound := h_feasible.1 i hi
  -- ∏(1-xj) ≤ 1, so xi·∏(1-xj) ≤ xi. This half-line of arithmetic is exactly
  -- what "certainly true" is quietly assuming the reader can fill in [p.70].
  have h_prod_le := x_mul_prod_le x i (neighbors vars B i) h_bound.1
    (fun c hc => by
      have hc_mem : c ∈ B := by
        simp [neighbors] at hc
        exact hc.1
      exact h_feasible.1 c hc_mem)
  unfold event_prob at h_cond
  -- chain the two: Pr[Ai] ≤ xi·∏(1-xj) ≤ xi - (5.1) holds at s = 0 [p.70].
  linarith

-- Section 5: Main Theorem

/- Before proceeding, here is a concrete example used throughout the rest of
   the file.

   Take B = {c1, c2, c3, c5, c6} with: vars(c1) = {v1, v2}, vars(c2) =
   {v2, v3}, vars(c5) = {v1, v6}, vars(c6) = {v2, v7}.

   Each of c2, c5, and c6 shares at least one variable with c1, so each is a
   neighbor of c1. In contrast, vars(c3) = {v4} shares no variable with c1,
   so c3 is independent of c1.

   The bad event A_c is the situation where certificate c fails, where the
   condition defining c is violated for some randomly chosen outcome ω.
   These events play the same role as the events A_1,...,A_n in the book.

   When we say "certificate i" in the text below, think about i = c1. Its
   neighbors Γ(i), written in Lean as `neighbors vars B i`, are all the
   certificates in B sharing at least one variable with it; in our example,
   Γ(c1) = {c2,c5,c6}. This corresponds to the book's dependency digraph,
   the set {j : (i,j) ∈ E} [p.70]. The difference here is that the
   dependency graph is not abstract; it is built concretely from shared
   variables.

   Every certificate c has a parameter, a "budget," x(c) ∈ [0, 1). It is
   fixed by the hypothesis h_feasible so that the probability of the bad
   event A_c never exceeds x(c) times the product of (1 - x(j)) over all
   neighbors j of c [p.70]. In other words, this is exactly the hypothesis
   of the General Lovász Local Lemma.

   The set S is not a fixed set. It is an arbitrary subset of B \ {i} that a
   theorem quantifies over. Intuitively, S stands for "the other
   certificates we're assuming have already passed." For example,
   S = {c2, c3, c5}. The theorem lll_key_bound proves its bound for every
   possible choice of S. Later theorems then use growing sets: ∅, then
   {c1}, then {c1,c2}, and so on, until all of B is covered.

   Wherever S1 and S2 appear, they are S split by whether its elements are
   neighbors of i. Therefore S1 = S ∩ Γ(i) holds the members of S that
   depend on i, while S2 = S \ S1 holds the members that aren't neighbors of
   i. If, for instance, S = {c2, c3, c5} and i = c1, then S1 = {c2, c5} and
   S2 = {c3}. This is the decomposition used right after equation (5.1)
   [p.70].

   all_pass S is the event that every certificate in S passes, i.e.
   ⋂_{c∈S} (A_c)ᶜ. all_pass B is therefore good_event, the event that every
   certificate in B passes at once.

   Finally, μ(X).toReal is just Pr[X] in Mathlib notation: μ is a
   probability measure, and .toReal converts its value to a real number. -/

-- Section 5a: splitting S by neighbor-of-i, named the way ppg_lll.pvs names it
-- (S1, S2 there are top-level functions too, not locally-scoped) - each piece
-- below is a standalone, separately re-checkable step of Alon-Spencer's
-- argument right after "certainly true for s=0" [p.70], instead of one long
-- nested proof term. Running example throughout: B={c1,c2,c3,c5,c6}, i=c1,
-- S={c2,c3,c5}, so S1_of vars B S i = {c2,c5} (shares a variable with c1) and
-- S2_of vars B S i = {c3} (doesn't).

/-- S1 = {j ∈ S : (i,j) ∈ E}, i's neighbors inside S [p.70]. -/
def S1_of (vars : CertVars C V) (B S : Finset C) (i : C) : Finset C :=
  S.filter (fun j => j ∈ neighbors vars B i)

/-- S2 = S \ S1, the members of S that don't share a variable with i [p.70]. -/
def S2_of (vars : CertVars C V) (B S : Finset C) (i : C) : Finset C :=
  S.filter (fun j => j ∉ neighbors vars B i)

theorem S_split_S1_S2 (vars : CertVars C V) (B S : Finset C) (i : C) :
    S = S1_of vars B S i ∪ S2_of vars B S i := by
  ext j
  simp only [S1_of, S2_of, Finset.mem_union, Finset.mem_filter]
  tauto

theorem S1_S2_disjoint (vars : CertVars C V) (B S : Finset C) (i : C) :
    Disjoint (S1_of vars B S i) (S2_of vars B S i) := by
  rw [Finset.disjoint_left]
  intro j hj1 hj2
  simp only [S1_of, Finset.mem_filter] at hj1
  simp only [S2_of, Finset.mem_filter] at hj2
  exact hj2.2 hj1.2

theorem S1_of_subset (vars : CertVars C V) (B S : Finset C) (i : C) :
    S1_of vars B S i ⊆ S := by
  unfold S1_of; exact Finset.filter_subset _ S

theorem S2_of_subset (vars : CertVars C V) (B S : Finset C) (i : C) :
    S2_of vars B S i ⊆ S := by
  unfold S2_of; exact Finset.filter_subset _ S

/-- Splits the conditioning event ⋀_S Aj into ⋀_S1 Aj ∧ ⋀_S2 Aj - the
    set-level shadow of the "⋀j∈S1 Aj | ⋀𝓁∈S2 A𝓁" grouping inside (5.2) [p.70]. -/
theorem all_pass_S_split (A : BadEvents C Ω) (vars : CertVars C V) (B S : Finset C) (i : C) :
    all_pass A S = all_pass A (S1_of vars B S i) ∩ all_pass A (S2_of vars B S i) := by
  conv_lhs => rw [S_split_S1_S2 vars B S i]
  exact all_pass_union A (S1_of vars B S i) (S2_of vars B S i)

theorem S1_subset_neighbors (vars : CertVars C V) (B S : Finset C) (i : C) :
    S1_of vars B S i ⊆ neighbors vars B i := by
  intro s hs
  simp only [S1_of, Finset.mem_filter] at hs
  exact hs.2

/-- Independence side-condition for i vs. S2: every s ∈ S2 is a genuine
    non-neighbor of i, hence independent of i in the CertVars sense. -/
theorem S2_indep_side (vars : CertVars C V) (B S : Finset C) (i : C)
    (hS_sub : S ⊆ B) (hi_notin : i ∉ S) :
    ∀ s ∈ S2_of vars B S i, s ∈ B ∧ s ≠ i ∧ independent vars i s := by
  intro s hs
  simp only [S2_of, Finset.mem_filter] at hs
  obtain ⟨hs_S, hs_not_nbr⟩ := hs
  have hs_ne : s ≠ i := fun heq => hi_notin (heq ▸ hs_S)
  have hs_B : s ∈ B := hS_sub hs_S
  refine ⟨hs_B, hs_ne, ?_⟩
  unfold independent
  by_contra h_ne_empty
  apply hs_not_nbr
  unfold neighbors
  rw [Finset.mem_filter]
  exact ⟨hs_B, hs_ne, Finset.nonempty_iff_ne_empty.mpr h_ne_empty⟩

/-- Second inequality of (5.4) [p.71]: "(1-xj1)⋯(1-xjr) ≥ ∏_{(i,j)∈E}(1-xj)".
    S1 ⊆ Γ(i) but may be missing some real neighbors (in the running example,
    c6 ∈ Γ(c1) but c6 ∉ S1 since c6 ∉ S) - each missing factor (1-x c6) ∈ (0,1]
    can only shrink the full product, so the S1-only product is ≥ it. -/
theorem prod_mono_S1 (x : LLLAssignment C) (vars : CertVars C V) (B S : Finset C) (i : C)
    (h_bound : ∀ c ∈ B, 0 ≤ x c ∧ x c < 1) :
    ∏ j ∈ neighbors vars B i, (1 - x j) ≤ ∏ j ∈ S1_of vars B S i, (1 - x j) := by
  apply Finset.prod_le_prod_of_subset_of_le_one₀ (S1_subset_neighbors vars B S i)
  · intro k hk
    have hk_B : k ∈ B := (Finset.mem_filter.mp hk).1
    linarith [(h_bound k hk_B).1, (h_bound k hk_B).2]
  · intro k hk _
    have hk_B : k ∈ B := (Finset.mem_filter.mp hk).1
    linarith [(h_bound k hk_B).1, (h_bound k hk_B).2]

/-- Numerator of (5.2), both halves of (5.3) [p.70]: dropping the ⋀S1 Aj
    conjunct only shrinks the set (⊆ step, "≤" in (5.3)), then lll_independence
    removes the S2 conditioning outright ("=" in (5.3)) - in the running
    example, "Pr[c1 fails ∧ c2,c3,c5 pass] ≤ Pr[c1 fails ∧ c3 passes] =
    Pr[c1 fails]·Pr[c3 passes]" since c3 is independent of c1. -/
theorem numerator_bound (A : BadEvents C Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (vars : CertVars C V) (B S : Finset C) (i : C)
    (h_indep : lll_independence A μ vars B)
    (hS_sub : S ⊆ B) (hi_B : i ∈ B) (hi_notin : i ∉ S) :
    (μ (A i ∩ all_pass A S)).toReal ≤
      (μ (A i)).toReal * (μ (all_pass A (S2_of vars B S i))).toReal := by
  have h_indep_i : μ (A i ∩ all_pass A (S2_of vars B S i)) =
      μ (A i) * μ (all_pass A (S2_of vars B S i)) :=
    h_indep i hi_B (S2_of vars B S i) (S2_indep_side vars B S i hS_sub hi_notin)
  have h_subset : A i ∩ all_pass A S ⊆ A i ∩ all_pass A (S2_of vars B S i) := by
    rw [all_pass_S_split A vars B S i]
    rintro ω ⟨hω1, _, hω3⟩
    exact ⟨hω1, hω3⟩
  calc (μ (A i ∩ all_pass A S)).toReal
      ≤ (μ (A i ∩ all_pass A (S2_of vars B S i))).toReal :=
        ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono h_subset)
    _ = (μ (A i)).toReal * (μ (all_pass A (S2_of vars B S i))).toReal := by
        rw [h_indep_i, ENNReal.toReal_mul]

/-- Tail of (5.3) [p.70]: "= Pr[Ai] ≤ xi·∏_{(i,j)∈E}(1-xj)" - the raw
    Lemma 5.1.1 hypothesis (h_feasible.2) for certificate i, unfolded. -/
theorem pi_bound (A : BadEvents C Ω) (μ : Measure Ω)
    (vars : CertVars C V) (B : Finset C) (x : LLLAssignment C) (i : C)
    (h_feasible : lll_feasible (event_prob A μ) x vars B) (hi_B : i ∈ B) :
    (μ (A i)).toReal ≤ x i * ∏ j ∈ neighbors vars B i, (1 - x j) := by
  have h := h_feasible.2 i hi_B
  unfold lll_condition_at event_prob at h
  exact h

/-- Generic telescoping step, independent of S/S1/S2/i entirely: given that
    Y is measurable-against-A_j and that Pr[Aj ∩ Y] ≤ xj·Pr[Y], conclude
    (1-xj)·Pr[Y] ≤ Pr[j passes ∧ Y]. This is the (1 - Pr[Ajk | ...]) factor
    from the book's telescope [p.71], division-free, split off from the
    Finset-membership bookkeeping so it can be checked as pure measure
    algebra on its own - matches the role of PVS's `pass_event_bound`. -/
theorem pass_event_measure_bound (A : BadEvents C Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (x : LLLAssignment C) (j : C) (Y : Set Ω) (h_meas_j : MeasurableSet (A j))
    (hj_bound : (μ (A j ∩ Y)).toReal ≤ x j * (μ Y).toReal) :
    (1 - x j) * (μ Y).toReal ≤ (μ (pass_event A j ∩ Y)).toReal := by
  have h_add : μ (Y ∩ A j) + μ (Y \ A j) = μ Y := measure_inter_add_sdiff _ h_meas_j
  have h_add_real : (μ (Y ∩ A j)).toReal + (μ (Y \ A j)).toReal = (μ Y).toReal := by
    rw [← ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _), h_add]
  have h_inter_comm : Y ∩ A j = A j ∩ Y := Set.inter_comm _ _
  have h_j_le : (μ (Y ∩ A j)).toReal ≤ x j * (μ Y).toReal := by
    rw [h_inter_comm]; exact hj_bound
  have h_pass_diff : pass_event A j ∩ Y = Y \ A j := by
    ext ω; simp only [pass_event, Set.mem_inter_iff, Set.mem_sdiff, Set.mem_compl_iff]
    tauto
  rw [h_pass_diff]
  nlinarith [h_add_real, h_j_le]

-- Membership/cardinality bookkeeping for the telescope step, split into
-- named lemmas the way ppg_lll.pvs does (S1_member_in_B,
-- telescope_union_subset, telescope_union_excludes, telescope_union_card) -
-- PVS needs these as separate lemmas because it recurses on decreasing
-- cardinality; telescope_union_ssub is the Lean analog using ⊂ directly,
-- since Finset.strongInduction's IH is already stated that way.

theorem S1_member_in_B (vars : CertVars C V) (B S : Finset C) (i c : C)
    (hc : c ∈ S1_of vars B S i) : c ∈ B := by
  have h := S1_subset_neighbors vars B S i hc
  exact (Finset.mem_filter.mp h).1

theorem telescope_union_subset (vars : CertVars C V) (B S T' : Finset C) (i : C)
    (hS_sub : S ⊆ B) (hT'_sub : T' ⊆ S1_of vars B S i) :
    T' ∪ S2_of vars B S i ⊆ B := by
  apply Finset.union_subset
  · exact fun c hc => S1_member_in_B vars B S i c (hT'_sub hc)
  · exact (S2_of_subset vars B S i).trans hS_sub

theorem telescope_union_excludes (vars : CertVars C V) (B S T' : Finset C) (i j : C)
    (hjT' : j ∉ T') (hT_sub : insert j T' ⊆ S1_of vars B S i) :
    j ∉ T' ∪ S2_of vars B S i := by
  have hj_S1 : j ∈ S1_of vars B S i := hT_sub (Finset.mem_insert_self j T')
  have hS_disj : Disjoint (S1_of vars B S i) (S2_of vars B S i) := S1_S2_disjoint vars B S i
  simp only [Finset.mem_union, not_or]
  exact ⟨hjT', fun hj_S2 => (Finset.disjoint_left.mp hS_disj hj_S1) hj_S2⟩

theorem telescope_union_ssub (vars : CertVars C V) (B S T' : Finset C) (i j : C)
    (hjT' : j ∉ T') (hT_sub : insert j T' ⊆ S1_of vars B S i) :
    T' ∪ S2_of vars B S i ⊂ S := by
  have hj_S1 : j ∈ S1_of vars B S i := hT_sub (Finset.mem_insert_self j T')
  have hT'_sub : T' ⊆ S1_of vars B S i := (Finset.insert_subset_iff.mp hT_sub).2
  have hj_S : j ∈ S := S1_of_subset vars B S i hj_S1
  have h_sub : T' ∪ S2_of vars B S i ⊆ S :=
    Finset.union_subset (hT'_sub.trans (S1_of_subset vars B S i)) (S2_of_subset vars B S i)
  exact (Finset.ssubset_iff_of_subset h_sub).mpr
    ⟨j, hj_S, telescope_union_excludes vars B S T' i j hjT' hT_sub⟩

/-- One insertion step of the denominator telescope (5.4) [p.71]: given the
    bound already established for T', extend it to insert j T', using the
    bookkeeping lemmas above to invoke the outer strong-induction hypothesis
    `ih` on j, and `pass_event_measure_bound` for the actual probability
    step - matches PVS's `denominator_telescope`. -/
theorem telescope_step (A : BadEvents C Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (vars : CertVars C V) (B S : Finset C) (x : LLLAssignment C) (i j : C) (T' : Finset C)
    (h_meas : all_measurable A)
    (h_feasible : lll_feasible (event_prob A μ) x vars B)
    (hS_sub : S ⊆ B) (hi_B : i ∈ B) (hi_notin : i ∉ S)
    (hjT' : j ∉ T')
    (hT_sub : insert j T' ⊆ S1_of vars B S i)
    (ih : ∀ S' ⊂ S, S' ⊆ B → ∀ k ∈ B, k ∉ S' →
      (μ (A k ∩ all_pass A S')).toReal ≤ x k * (μ (all_pass A S')).toReal)
    (h_ih_T : (∏ k ∈ T', (1 - x k)) * (μ (all_pass A (S2_of vars B S i))).toReal ≤
      (μ (all_pass A T' ∩ all_pass A (S2_of vars B S i))).toReal) :
    (∏ k ∈ insert j T', (1 - x k)) * (μ (all_pass A (S2_of vars B S i))).toReal ≤
      (μ (all_pass A (insert j T') ∩ all_pass A (S2_of vars B S i))).toReal := by
  have hj_B : j ∈ B := S1_member_in_B vars B S i j (hT_sub (Finset.mem_insert_self j T'))
  have h_ssub : T' ∪ S2_of vars B S i ⊂ S := telescope_union_ssub vars B S T' i j hjT' hT_sub
  have h_sub_B : T' ∪ S2_of vars B S i ⊆ B :=
    telescope_union_subset vars B S T' i hS_sub (Finset.insert_subset_iff.mp hT_sub).2
  have h_notin : j ∉ T' ∪ S2_of vars B S i := telescope_union_excludes vars B S T' i j hjT' hT_sub
  -- "bounded by the induction hypothesis" [p.70] - recursive call into the
  -- caller's outer strong induction, on the strictly smaller set T'∪S2.
  have hj_bound := ih (T' ∪ S2_of vars B S i) h_ssub h_sub_B j hj_B h_notin
  have h_Y_eq : all_pass A T' ∩ all_pass A (S2_of vars B S i) =
      all_pass A (T' ∪ S2_of vars B S i) := (all_pass_union A T' (S2_of vars B S i)).symm
  have h_step := pass_event_measure_bound A μ x j (all_pass A (T' ∪ S2_of vars B S i))
    (h_meas j) hj_bound
  have h_insert_eq : all_pass A (insert j T') ∩ all_pass A (S2_of vars B S i) =
      pass_event A j ∩ all_pass A (T' ∪ S2_of vars B S i) := by
    rw [all_pass_insert A T' j hjT', Set.inter_assoc, h_Y_eq]
  rw [h_insert_eq, Finset.prod_insert hjT']
  -- chains the inner induction hypothesis with h_step - one link of the
  -- telescope (1-xj1)⋯(1-xjr) ≥ ∏(1-xj) [p.71]
  calc ((1 - x j) * ∏ k ∈ T', (1 - x k)) * (μ (all_pass A (S2_of vars B S i))).toReal
      = (1 - x j) * ((∏ k ∈ T', (1 - x k)) * (μ (all_pass A (S2_of vars B S i))).toReal) := by ring
    _ ≤ (1 - x j) * (μ (all_pass A T' ∩ all_pass A (S2_of vars B S i))).toReal := by
        apply mul_le_mul_of_nonneg_left h_ih_T
        linarith [(h_feasible.1 j hj_B).2]
    _ = (1 - x j) * (μ (all_pass A (T' ∪ S2_of vars B S i))).toReal := by rw [h_Y_eq]
    _ ≤ (μ (pass_event A j ∩ all_pass A (T' ∪ S2_of vars B S i))).toReal := h_step

/-- Denominator bound (5.4) [p.71]: book telescopes
    Pr[Aj1∧⋯∧Ajr|⋀S2] = (1-Pr[Aj1|⋀S2])·(1-Pr[Aj2|Aj1∧⋀S2])⋯ ≥ ∏(1-xjk),
    peeling j1,...,jr off S1 one at a time via telescope_step. Unlike PVS
    (which has no built-in strong-induction principle and must prove the
    cardinality-decrease side conditions via separate lemmas), Lean gets that
    induction hypothesis for free from `Finset.strongInduction` in
    lll_key_bound below - it is threaded in here as the explicit `ih`
    parameter, playing exactly the role of the book's "by the induction
    hypothesis" phrase. With telescope_step doing the real work, this is now
    just the outer Finset.induction wrapper - matches PVS's own split between
    `denominator_telescope` and `denominator_bound`. -/
theorem denominator_bound (A : BadEvents C Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (vars : CertVars C V) (B S : Finset C) (x : LLLAssignment C) (i : C)
    (h_meas : all_measurable A)
    (h_feasible : lll_feasible (event_prob A μ) x vars B)
    (hS_sub : S ⊆ B) (hi_B : i ∈ B) (hi_notin : i ∉ S)
    (ih : ∀ S' ⊂ S, S' ⊆ B → ∀ k ∈ B, k ∉ S' →
      (μ (A k ∩ all_pass A S')).toReal ≤ x k * (μ (all_pass A S')).toReal) :
    (∏ j ∈ S1_of vars B S i, (1 - x j)) * (μ (all_pass A (S2_of vars B S i))).toReal ≤
      (μ (all_pass A (S1_of vars B S i) ∩ all_pass A (S2_of vars B S i))).toReal := by
  have key : ∀ (T : Finset C), T ⊆ S1_of vars B S i →
      (∏ j ∈ T, (1 - x j)) * (μ (all_pass A (S2_of vars B S i))).toReal ≤
        (μ (all_pass A T ∩ all_pass A (S2_of vars B S i))).toReal := by
    intro T
    induction T using Finset.induction with
    -- "If r = 0, then the denominator is 1" [p.70] - T = ∅ base case
    | empty => intro _; simp [all_pass_empty]
    | insert j T' hjT' ih_T =>
      intro hT_sub
      exact telescope_step A μ vars B S x i j T' h_meas h_feasible hS_sub hi_B hi_notin
        hjT' hT_sub ih (ih_T (Finset.insert_subset_iff.mp hT_sub).2)
  exact key (S1_of vars B S i) (le_refl _)

/-- Key inductive bound [Alon–Spencer, Lemma 5.1.1 proof, (5.1)-(5.4), pp.70-71]:
    for any S ⊆ B not containing i, μ(A_i ∩ all_pass(S)) ≤ x_i * μ(all_pass(S)).

    This is (5.1) itself - Pr[Ai | ⋀_S ¬Aj] ≤ xi - rewritten division-free as a
    multiplicative bound, so Mathlib's measure lemmas apply without ever having
    to worry whether μ(all_pass S) = 0 (conditional probability would choke there).

    In the running example above, with S = {c2,c3,c5}, this says "Pr[c1 fails
    AND c2,c3,c5 all pass] ≤ x(c1) · Pr[c2,c3,c5 all pass]" - conditioning on
    a pile of other certificates having passed, related to c1 or not, never
    pushes c1's failure chance above the x(c1) budget fixed by h_feasible.

    "Substituting (5.3) and (5.4) into (5.2)" [p.71]: numerator_bound is (5.3)'s
    numerator, pi_bound its tail, prod_mono_S1 trims Γ(i) down to S1, and
    denominator_bound is (5.4)'s denominator bound - this theorem just does the
    strong induction (supplying `ih` to denominator_bound) and chains the four
    pieces together, the way ppg_lll.pvs's own `lll_key_bound` assembles its
    already-proved helper lemmas at the end. -/
theorem lll_key_bound (A : BadEvents C Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (vars : CertVars C V) (B : Finset C) (x : LLLAssignment C)
    (h_meas : all_measurable A)
    (h_indep : lll_independence A μ vars B)
    (h_feasible : lll_feasible (event_prob A μ) x vars B) :
    ∀ (S : Finset C), S ⊆ B → ∀ i ∈ B, i ∉ S →
      (μ (A i ∩ all_pass A S)).toReal ≤ x i * (μ (all_pass A S)).toReal := by
  intro S
  -- strong induction on S mirrors the book's induction on s = |S| [p.70]; `ih`
  -- below plays the role of "the induction hypothesis" the book invokes by name
  -- when bounding the denominator of (5.2).
  induction S using Finset.strongInduction with
  | _ S ih =>
    intro hS_sub i hi_B hi_notin
    have h_num := numerator_bound A μ vars B S i h_indep hS_sub hi_B hi_notin
    have h_pi_bound := pi_bound A μ vars B x i h_feasible hi_B
    have h_prod_mono := prod_mono_S1 x vars B S i h_feasible.1
    have h_denom := denominator_bound A μ vars B S x i h_meas h_feasible hS_sub hi_B hi_notin ih
    have hAllPassSplit : all_pass A S =
        all_pass A (S1_of vars B S i) ∩ all_pass A (S2_of vars B S i) :=
      all_pass_S_split A vars B S i
    rw [hAllPassSplit]
    calc (μ (A i ∩ (all_pass A (S1_of vars B S i) ∩ all_pass A (S2_of vars B S i)))).toReal
        ≤ (μ (A i ∩ all_pass A S)).toReal := by rw [hAllPassSplit]
      _ ≤ (μ (A i)).toReal * (μ (all_pass A (S2_of vars B S i))).toReal := h_num
      _ ≤ (x i * ∏ j ∈ neighbors vars B i, (1 - x j)) * (μ (all_pass A (S2_of vars B S i))).toReal :=
          mul_le_mul_of_nonneg_right h_pi_bound ENNReal.toReal_nonneg
      _ = x i * ((∏ j ∈ neighbors vars B i, (1 - x j)) * (μ (all_pass A (S2_of vars B S i))).toReal) := by
          ring
      _ ≤ x i * ((∏ j ∈ S1_of vars B S i, (1 - x j)) * (μ (all_pass A (S2_of vars B S i))).toReal) := by
          apply mul_le_mul_of_nonneg_left _ (h_feasible.1 i hi_B).1
          exact mul_le_mul_of_nonneg_right h_prod_mono ENNReal.toReal_nonneg
      _ ≤ x i * (μ (all_pass A (S1_of vars B S i) ∩ all_pass A (S2_of vars B S i))).toReal :=
          mul_le_mul_of_nonneg_left h_denom (h_feasible.1 i hi_B).1

/-- Lower bound on good event probability [Alon–Spencer, Lemma 5.1.1 proof,
    final assertion, p.71]: μ(good_event) ≥ ∏_{i ∈ B} (1 - x_i).

    Book: "Pr[⋀ᵢAi] = (1-Pr[A1])·(1-Pr[A2|A1])⋯(1-Pr[An|⋀₁ⁿ⁻¹Ai]) ≥ ∏(1-xi)."

    In the running example, this says the chance that all five certificates
    c1,c2,c3,c5,c6 pass at once is at least (1-x c1)(1-x c2)(1-x c3)(1-x c5)
    (1-x c6). The proof peels B one certificate at a time, mirroring the
    book's chain of factors (1-Pr[A1]), (1-Pr[A2|A1]), ... - each new
    factor's bound comes straight from lll_key_bound applied to whichever
    certificates have been peeled off so far. -/
theorem lll_good_event_lower_bound (A : BadEvents C Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (vars : CertVars C V) (B : Finset C)
    (x : LLLAssignment C)
    (h_meas : all_measurable A)
    (h_indep : lll_independence A μ vars B)
    (h_feasible : lll_feasible (event_prob A μ) x vars B) :
    (μ (good_event A B)).toReal ≥ ∏ i ∈ B, (1 - x i) := by
  classical
  -- generalizes the final assertion to any prefix T ⊆ B, giving the
  -- Finset-induction telescope below something to induct on - same pattern
  -- as lll_key_bound's inner `key` over T ⊆ S1, just at the top level now:
  -- T grows through the running example as ∅, {c1}, {c1,c2}, ... up to all
  -- of B.
  have key : ∀ T ⊆ B, (∏ i ∈ T, (1 - x i)) ≤ (μ (all_pass A T)).toReal := by
    intro T
    induction T using Finset.induction with
    -- start of the telescope: nothing conditioned on yet, ∏_∅ = 1 and
    -- all_pass ∅ = univ has measure 1 (IsProbabilityMeasure) - the point
    -- before the book's first factor "(1-Pr[A1])" [p.71].
    | empty => intro _; simp [all_pass_empty]
    | insert i T' hiT' ih_T =>
      intro hT_sub
      have hi_B : i ∈ B := hT_sub (Finset.mem_insert_self i T')
      have hT'_sub : T' ⊆ B := (Finset.insert_subset_iff.mp hT_sub).2
      have hi_notin_T' : i ∉ T' := hiT'
      -- one factor of the book's chain: say i=c5, T'={c1,c2,c3} already
      -- peeled - h_key reuses lll_key_bound wholesale to get exactly
      -- "Pr[c5 fails | c1,c2,c3 all pass] ≤ x(c5)", the division-free stand-in
      -- for the book's "(1-Pr[A_c5 | A_c1∧A_c2∧A_c3])" factor [p.71].
      have h_key := lll_key_bound A μ vars B x h_meas h_indep h_feasible T' hT'_sub i hi_B hi_notin_T'
      have h_ih := ih_T hT'_sub
      rw [all_pass_insert A T' i hiT', Finset.prod_insert hiT']
      -- same division-free trick as lll_key_bound's h_denom: split
      -- μ(all_pass T') into its "i also passes" part and "i fails" part
      -- instead of dividing to form a conditional probability.
      have h_add : μ (all_pass A T' ∩ A i) + μ (all_pass A T' \ A i) = μ (all_pass A T') :=
        measure_inter_add_sdiff _ (h_meas i)
      have h_add_real : (μ (all_pass A T' ∩ A i)).toReal + (μ (all_pass A T' \ A i)).toReal =
          (μ (all_pass A T')).toReal := by
        rw [← ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _), h_add]
      have h_i_le : (μ (all_pass A T' ∩ A i)).toReal ≤ x i * (μ (all_pass A T')).toReal := by
        rw [Set.inter_comm]; exact h_key
      have h_pass_diff : pass_event A i ∩ all_pass A T' = all_pass A T' \ A i := by
        ext ω
        simp only [pass_event, Set.mem_inter_iff, Set.mem_sdiff, Set.mem_compl_iff]
        tauto
      rw [h_pass_diff]
      have h_x_bound := (h_feasible.1 i hi_B)
      -- chains the running product bound (h_ih, for T' peeled so far) with
      -- the new (1-x i) factor - one more link in the telescope ∏(1-xi) ≤
      -- μ(all_pass) building up toward all of B [p.71].
      calc (1 - x i) * ∏ j ∈ T', (1 - x j)
          ≤ (1 - x i) * (μ (all_pass A T')).toReal := by
            apply mul_le_mul_of_nonneg_left h_ih; linarith [h_x_bound.2]
        _ ≤ (μ (all_pass A T' \ A i)).toReal := by nlinarith [h_add_real, h_i_le]
  -- instantiate the general prefix bound at T = B - Lemma 5.1.1's stated
  -- conclusion, μ(good_event) ≥ ∏_{i∈B}(1-x_i) [p.70-71].
  exact key B (le_refl B)

/-- General LLL [Alon-Spencer, Lemma 5.1.1, p.70]: μ(good_event) > 0. The book
    tacks this onto the lemma statement itself, before the proof even starts:
    "In particular, with positive probability, no event Ai holds." For the
    running example, c1,c2,c3,c5,c6 all passing at once has to be strictly
    positive, since every factor (1-x c) in the lower bound is already
    positive - x c < 1 is baked into h_feasible from the start. -/
theorem lll_positive_probability (A : BadEvents C Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (vars : CertVars C V) (B : Finset C)
    (x : LLLAssignment C)
    (h_meas : all_measurable A)
    (h_indep : lll_independence A μ vars B)
    (h_feasible : lll_feasible (event_prob A μ) x vars B) :
    0 < μ (good_event A B) := by
  have h_lower := lll_good_event_lower_bound A μ vars B x h_meas h_indep h_feasible
  have h_prod_pos := prod_one_sub_pos x B h_feasible.1
  have h_toReal_pos : 0 < (μ (good_event A B)).toReal := by linarith
  exact pos_iff_ne_zero.mpr (fun h0 => by simp [h0] at h_toReal_pos)

/-- The book stops at "positive probability" [p.70]; this pushes one step
    further, to an actual outcome. A measure that's positive can't be
    sitting on the empty set, so somewhere out there is a real ω where
    c1,c2,c3,c5,c6 all pass at once - not just a probability statement, an
    honest witness. -/
theorem lll_good_state_exists (A : BadEvents C Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (vars : CertVars C V) (B : Finset C)
    (x : LLLAssignment C)
    (h_meas : all_measurable A)
    (h_indep : lll_independence A μ vars B)
    (h_feasible : lll_feasible (event_prob A μ) x vars B) :
    (good_event A B).Nonempty := by
  have h_pos := lll_positive_probability A μ vars B x h_meas h_indep h_feasible
  exact nonempty_of_measure_ne_zero (ne_of_gt h_pos)

-- Verification

#check @all_pass_empty
#check @all_pass_subset
#check @all_pass_union
#check @all_pass_insert
#check @all_pass_measurable
#check @prod_one_sub_pos
#check @prod_one_sub_le_one
#check @x_mul_prod_le
#check @lll_base_case
#check @S_split_S1_S2
#check @S1_S2_disjoint
#check @S1_of_subset
#check @S2_of_subset
#check @all_pass_S_split
#check @S1_subset_neighbors
#check @S2_indep_side
#check @prod_mono_S1
#check @numerator_bound
#check @pi_bound
#check @pass_event_measure_bound
#check @S1_member_in_B
#check @telescope_union_subset
#check @telescope_union_excludes
#check @telescope_union_ssub
#check @telescope_step
#check @denominator_bound
#check @lll_key_bound
#check @lll_good_event_lower_bound
#check @lll_positive_probability
#check @lll_good_state_exists
