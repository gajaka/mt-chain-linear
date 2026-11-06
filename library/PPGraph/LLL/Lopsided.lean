/-
  PPGraphLopsidedLLL.lean
  Lopsided Lovász Local Lemma for PPG Blocking Sets

  Erdős and Spencer's generalization of Lemma 5.1.1: independence of
  non-neighbors is not required, only that conditioning on non-neighbors
  not increasing hurt -- "lopsidependence" instead of independence.
  Reference: David G. Harris, "Lopsidependency in the Moser-Tardos
  framework: Beyond the Lopsided Lovász Local Lemma", arXiv:1610.02420,
  Section 1.2, equation (1): for a weighting μ, if
    μ(B) ≥ Pr[B] · ∏_{B'~B} (1 + μ(B'))
  for every bad event B, and the bad events are lopsidependent (not
  independent) along ~, then Pr[no bad event holds] > 0. Harris credits
  this form to Erdős and Spencer; his own new criterion (orderability,
  his Theorem 1.2) goes further and is not attempted here.

  This file does not re-derive the measure-theoretic machinery of
  PPGraphLLL.lean (all_pass, event_prob, good_event, the Finset lemmas):
  it imports them. The only change from PPGraphLLL.lean's proof is the
  hypothesis connecting a certificate to its non-neighbors: equality
  (`lll_independence`) becomes an inequality (`lll_lopsidependence`).
  Every genuine independence hypothesis trivially satisfies the weaker
  one, so this file's theorems are strictly more general than
  PPGraphLLL.lean's -- they subsume it rather than duplicate it.

  Where the proof actually changes: `lll_key_bound`'s numerator bound
  (h_num) is the only step that used independence, and it used it as an
  equality via `rw`. Under the weaker hypothesis that step becomes an
  extra `≤` link in the same calc chain (via ENNReal.toReal_mono and
  ENNReal.toReal_mul instead of a direct rewrite). Nothing else in the
  proof touches independence at all, including the base case and the
  denominator telescope, so they carry over unchanged -- lll_base_case
  is reused verbatim from PPGraphLLL.lean.

  Author: Dragan Stosic, 2026.
-/

module

public import Mathlib.Tactic
public import PPGraph.LLL.General

@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory

variable {Ω : Type} [MeasurableSpace Ω]
variable {C V : Type} [DecidableEq C] [DecidableEq V] [Fintype C]

-- Section 1: Lopsidependence

/-- Lopsidependence, Harris/Erdős-Spencer: conditioning on a set of
    non-neighbors passing does not INCREASE the chance a certificate
    fails -- an inequality, not the equality lll_independence demands.
    Any independent process satisfies this for free (equality implies
    ≤), so this hypothesis is strictly weaker and easier to establish
    for real dependency structure that isn't literally independent, only
    non-positively-correlated. -/
def lll_lopsidependence (A : BadEvents C Ω) (μ : Measure Ω)
    (vars : CertVars C V) (B : Finset C) : Prop :=
  ∀ c ∈ B, ∀ S₂ : Finset C,
    (∀ s ∈ S₂, s ∈ B ∧ s ≠ c ∧ independent vars c s) →
    μ (A c ∩ all_pass A S₂) ≤ μ (A c) * μ (all_pass A S₂)

/-- The claim that lopsidependence is strictly weaker than independence,
    checked rather than merely asserted: equality implies ≤, pointwise,
    so every lll_independence instance is automatically an
    lll_lopsidependence instance. The converse direction is exactly what
    fails for genuinely negatively correlated (not independent) bad
    events -- random permutations, matchings, Latin transversals, the
    examples Erdős and Spencer built the lopsided lemma for -- so this
    inclusion is one-way, not an equivalence in disguise. -/
theorem independence_implies_lopsidependence (A : BadEvents C Ω) (μ : Measure Ω)
    (vars : CertVars C V) (B : Finset C) :
    lll_independence A μ vars B → lll_lopsidependence A μ vars B := by
  intro h_indep c hc S₂ hS₂
  exact le_of_eq (h_indep c hc S₂ hS₂)

-- Section 2: Key Inductive Bound, under lopsidependence
--
-- Reuses S1_of, S2_of, S2_indep_side, all_pass_S_split, prod_mono_S1,
-- pi_bound, and denominator_bound verbatim from PPGraphLLL.lean -- none of
-- them ever touch independence, only h_meas/h_feasible/the outer strong-
-- induction hypothesis. The one place independence was used is the
-- numerator step, so that is the only new lemma needed here.

/-- Numerator bound under lopsidependence -- the ONE step that differs from
    numerator_bound in PPGraphLLL.lean. There, h_indep gave an equality
    closed by `rw`. Here h_lopsi only gives ≤ [Harris eq.(1)], so the gap is
    closed as an extra calc link via ENNReal.toReal_mono instead. -/
theorem lopsided_numerator_bound (A : BadEvents C Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (vars : CertVars C V) (B S : Finset C) (i : C)
    (h_lopsi : lll_lopsidependence A μ vars B)
    (hS_sub : S ⊆ B) (hi_B : i ∈ B) (hi_notin : i ∉ S) :
    (μ (A i ∩ all_pass A S)).toReal ≤
      (μ (A i)).toReal * (μ (all_pass A (S2_of vars B S i))).toReal := by
  have h_lopsi_i : μ (A i ∩ all_pass A (S2_of vars B S i)) ≤
      μ (A i) * μ (all_pass A (S2_of vars B S i)) :=
    h_lopsi i hi_B (S2_of vars B S i) (S2_indep_side vars B S i hS_sub hi_notin)
  have h_subset : A i ∩ all_pass A S ⊆ A i ∩ all_pass A (S2_of vars B S i) := by
    rw [all_pass_S_split A vars B S i]
    rintro ω ⟨hω1, _, hω3⟩
    exact ⟨hω1, hω3⟩
  have h_mul_ne_top : (μ (A i) * μ (all_pass A (S2_of vars B S i))) ≠ ⊤ :=
    ENNReal.mul_ne_top (measure_ne_top μ _) (measure_ne_top μ _)
  calc (μ (A i ∩ all_pass A S)).toReal
      ≤ (μ (A i ∩ all_pass A (S2_of vars B S i))).toReal :=
        ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono h_subset)
    _ ≤ (μ (A i) * μ (all_pass A (S2_of vars B S i))).toReal :=
        ENNReal.toReal_mono h_mul_ne_top h_lopsi_i
    _ = (μ (A i)).toReal * (μ (all_pass A (S2_of vars B S i))).toReal := ENNReal.toReal_mul

/-- Same statement as lll_key_bound, under the weaker lopsidependence
    hypothesis. Same assembly as PPGraphLLL.lean's own lll_key_bound, with
    lopsided_numerator_bound and h_lopsi in place of numerator_bound and
    h_indep -- everything else (pi_bound, prod_mono_S1, denominator_bound)
    is the identical shared lemma, unchanged. -/
theorem lopsided_lll_key_bound (A : BadEvents C Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (vars : CertVars C V) (B : Finset C) (x : LLLAssignment C)
    (h_meas : all_measurable A)
    (h_lopsi : lll_lopsidependence A μ vars B)
    (h_feasible : lll_feasible (event_prob A μ) x vars B) :
    ∀ (S : Finset C), S ⊆ B → ∀ i ∈ B, i ∉ S →
      (μ (A i ∩ all_pass A S)).toReal ≤ x i * (μ (all_pass A S)).toReal := by
  intro S
  induction S using Finset.strongInduction with
  | _ S ih =>
    intro hS_sub i hi_B hi_notin
    have h_num := lopsided_numerator_bound A μ vars B S i h_lopsi hS_sub hi_B hi_notin
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

-- Section 3: Downstream theorems, unchanged except which key_bound they call

/-- lll_good_event_lower_bound under lopsidependence. Its own proof never
    touches independence directly -- only through the call to key_bound --
    so this is that same proof with lopsided_lll_key_bound in place of
    lll_key_bound. -/
theorem lopsided_lll_good_event_lower_bound (A : BadEvents C Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (vars : CertVars C V) (B : Finset C)
    (x : LLLAssignment C)
    (h_meas : all_measurable A)
    (h_lopsi : lll_lopsidependence A μ vars B)
    (h_feasible : lll_feasible (event_prob A μ) x vars B) :
    (μ (good_event A B)).toReal ≥ ∏ i ∈ B, (1 - x i) := by
  classical
  have key : ∀ T ⊆ B, (∏ i ∈ T, (1 - x i)) ≤ (μ (all_pass A T)).toReal := by
    intro T
    induction T using Finset.induction with
    | empty => intro _; simp [all_pass_empty]
    | insert i T' hiT' ih_T =>
      intro hT_sub
      have hi_B : i ∈ B := hT_sub (Finset.mem_insert_self i T')
      have hT'_sub : T' ⊆ B := (Finset.insert_subset_iff.mp hT_sub).2
      have hi_notin_T' : i ∉ T' := hiT'
      have h_key := lopsided_lll_key_bound A μ vars B x h_meas h_lopsi h_feasible
        T' hT'_sub i hi_B hi_notin_T'
      have h_ih := ih_T hT'_sub
      rw [all_pass_insert A T' i hiT', Finset.prod_insert hiT']
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
      calc (1 - x i) * ∏ j ∈ T', (1 - x j)
          ≤ (1 - x i) * (μ (all_pass A T')).toReal := by
            apply mul_le_mul_of_nonneg_left h_ih; linarith [h_x_bound.2]
        _ ≤ (μ (all_pass A T' \ A i)).toReal := by nlinarith [h_add_real, h_i_le]
  exact key B (le_refl B)

/-- General Lopsided LLL: μ(good_event) > 0, under lopsidependence rather
    than independence. Same closing argument as lll_positive_probability. -/
theorem lopsided_lll_positive_probability (A : BadEvents C Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (vars : CertVars C V) (B : Finset C)
    (x : LLLAssignment C)
    (h_meas : all_measurable A)
    (h_lopsi : lll_lopsidependence A μ vars B)
    (h_feasible : lll_feasible (event_prob A μ) x vars B) :
    0 < μ (good_event A B) := by
  have h_lower := lopsided_lll_good_event_lower_bound A μ vars B x h_meas h_lopsi h_feasible
  have h_prod_pos := prod_one_sub_pos x B h_feasible.1
  have h_toReal_pos : 0 < (μ (good_event A B)).toReal := by linarith
  exact pos_iff_ne_zero.mpr (fun h0 => by simp [h0] at h_toReal_pos)

/-- Corollary: good state exists, under lopsidependence. -/
theorem lopsided_lll_good_state_exists (A : BadEvents C Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (vars : CertVars C V) (B : Finset C)
    (x : LLLAssignment C)
    (h_meas : all_measurable A)
    (h_lopsi : lll_lopsidependence A μ vars B)
    (h_feasible : lll_feasible (event_prob A μ) x vars B) :
    (good_event A B).Nonempty := by
  have h_pos := lopsided_lll_positive_probability A μ vars B x h_meas h_lopsi h_feasible
  exact nonempty_of_measure_ne_zero (ne_of_gt h_pos)

-- Verification

#check @lll_lopsidependence
#check @independence_implies_lopsidependence
#check @lopsided_lll_key_bound
#check @lopsided_lll_good_event_lower_bound
#check @lopsided_lll_positive_probability
#check @lopsided_lll_good_state_exists

-- Explicit checks for all remaining helper theorems.
#check @lopsided_numerator_bound
