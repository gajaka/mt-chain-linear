/-
  PPGraphShearer.lean

  The strict-interior, lopsided Shearer bound, with the dependency graph
  and component structure used by PPG.

  Source: N. J. A. Harvey and J. Vondrak, "Short proofs for generalizations
  of the Lovasz Local Lemma: Shearer's condition and cluster expansion",
  arXiv:1711.06797, Section 2, Lemma 1 and Claims 2--3.
  https://arxiv.org/abs/1711.06797

  Strict positivity is required on every induced-subgraph polynomial.
  This proves positive probability and existence; the boundary version,
  optimality construction, and algorithmic runtime bounds are separate
  results and are not assumed here. Failure of this sufficient test is
  not a proof that the particular event family has no good state.
-/

module

public import PPGraph.Shearer.Polynomial
public import PPGraph.Shearer.Induction
public import PPGraph.LLL.Lopsided
public import PPGraph.Shearer.BDD

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory

namespace Shearer

variable {C V Ω : Type} [DecidableEq C] [Fintype C] [DecidableEq V] [MeasurableSpace Ω]

/-- The probability of avoiding every bad event indexed by a finite set. -/
noncomputable def passProbability (A : BadEvents C Ω) (μ : Measure Ω)
    (T : Finset C) : ℝ := (μ (all_pass A T)).toReal

/-- Division-free form of Harvey--Vondrak's condition (1), allowing
probability upper bounds rather than requiring exact marginals. -/
def Lopsidependence (G : SimpleGraph C) (A : BadEvents C Ω) (μ : Measure Ω)
    (p : C → ℝ) (B : Finset C) : Prop :=
  ∀ a ∈ B, ∀ J : Finset C, J ⊆ B →
    (∀ j ∈ J, j ≠ a ∧ ¬ G.Adj a j) →
    (μ (A a ∩ all_pass A J)).toReal ≤ p a * passProbability A μ J

@[simp]
theorem passProbability_empty (A : BadEvents C Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] : passProbability A μ ∅ = 1 := by
  simp [passProbability, all_pass_empty]

theorem passProbability_nonneg (A : BadEvents C Ω) (μ : Measure Ω)
    (T : Finset C) : 0 ≤ passProbability A μ T := ENNReal.toReal_nonneg

/-- Claim 3: removing one event costs at most its probability bound times
the probability of passing its non-neighbors. -/
theorem fundamental_probability_inequality (G : SimpleGraph C)
    (A : BadEvents C Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : C → ℝ) (B T : Finset C) (a : C)
    (hmeas : all_measurable A) (hlop : Lopsidependence G A μ p B)
    (hT : T ⊆ B) (ha : a ∈ T) :
    passProbability A μ (T.erase a) - p a * passProbability A μ (remote G T a) ≤
      passProbability A μ T := by
  classical
  have hremote : remote G T a ⊆ T.erase a := remote_subset_erase G T a
  have hbound := hlop a (hT ha) (remote G T a)
    (hremote.trans ((Finset.erase_subset a T).trans hT))
    (by intro j hj; exact (Finset.mem_filter.mp hj).2)
  have hsub : A a ∩ all_pass A (T.erase a) ⊆ A a ∩ all_pass A (remote G T a) :=
    fun _ hω => ⟨hω.1, all_pass_subset A _ _ hremote hω.2⟩
  have hnum : (μ (all_pass A (T.erase a) ∩ A a)).toReal ≤
      p a * passProbability A μ (remote G T a) := by
    rw [Set.inter_comm]
    exact (ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono hsub)).trans hbound
  have hdiff : all_pass A (T.erase a) \ A a = all_pass A T := by
    conv_rhs => rw [← Finset.insert_erase ha,
      all_pass_insert A (T.erase a) a (Finset.notMem_erase a T)]
    ext ω
    simp only [pass_event, Set.mem_inter_iff, Set.mem_sdiff, Set.mem_compl_iff]
    tauto
  have hadd : μ (all_pass A (T.erase a) ∩ A a) + μ (all_pass A T) =
      μ (all_pass A (T.erase a)) := by
    rw [← hdiff]
    exact measure_inter_add_sdiff _ (hmeas a)
  have hreal : (μ (all_pass A (T.erase a) ∩ A a)).toReal + passProbability A μ T =
      passProbability A μ (T.erase a) := by
    unfold passProbability
    rw [← ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _), hadd]
  linarith

/-- The strict-interior version of the lopsided Shearer bound, on every
subfamily of the specified event family. -/
theorem good_event_lower_bound (G : SimpleGraph C)
    (A : BadEvents C Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : C → ℝ) (B : Finset C)
    (hmeas : all_measurable A) (hlop : Lopsidependence G A μ p B)
    (hp : ∀ a ∈ B, 0 ≤ p a) (hcriterion : StrictCriterion G p B)
    (T : Finset C) (hT : T ⊆ B) :
    polynomial G p T ≤ (μ (good_event A T)).toReal := by
  exact probability_ge B p (passProbability A μ) (polynomial G p) (remote G)
    (passProbability_empty A μ) (polynomial_empty G p) hp hcriterion
    (fun U _ a _ => remote_subset_erase G U a)
    (fun U _ a ha => polynomial_delete G p U a ha)
    (fun U hU a ha => fundamental_probability_inequality G A μ p B U a hmeas hlop hU ha)
    T hT

/-- Strict positivity of all induced polynomials gives positive measure
of the event in which all certificates pass. -/
theorem positive_probability (G : SimpleGraph C)
    (A : BadEvents C Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : C → ℝ) (B : Finset C)
    (hmeas : all_measurable A) (hlop : Lopsidependence G A μ p B)
    (hp : ∀ a ∈ B, 0 ≤ p a) (hcriterion : StrictCriterion G p B) :
    0 < μ (good_event A B) := by
  have hpos := (hcriterion B Finset.Subset.rfl).trans_le
    (good_event_lower_bound G A μ p B hmeas hlop hp hcriterion B Finset.Subset.rfl)
  exact pos_iff_ne_zero.mpr (fun hzero => by simp [hzero] at hpos)

/-- A sufficient certificate of existence, with no resampling or
termination assumption. -/
theorem good_state_exists (G : SimpleGraph C)
    (A : BadEvents C Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : C → ℝ) (B : Finset C)
    (hmeas : all_measurable A) (hlop : Lopsidependence G A μ p B)
    (hp : ∀ a ∈ B, 0 ≤ p a) (hcriterion : StrictCriterion G p B) :
    (good_event A B).Nonempty :=
  nonempty_of_measure_ne_zero
    (ne_of_gt (positive_probability G A μ p B hmeas hlop hp hcriterion))

/-- Existing PPG lopsidependence supplies the graph hypothesis, also when
`p` is an upper bound on the actual bad-event probabilities. -/
theorem lopsidependence_of_ppg
    (A : BadEvents C Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (vars : CertVars C V) (p : C → ℝ) (B : Finset C)
    (hlop : lll_lopsidependence A μ vars B)
    (hp : ∀ a ∈ B, event_prob A μ a ≤ p a) :
    Lopsidependence (dependencyGraph vars) A μ p B := by
  intro a ha J hJB hJ
  have hvars : ∀ j ∈ J, j ∈ B ∧ j ≠ a ∧ independent vars a j := by
    intro j hj
    obtain ⟨hne, hnadj⟩ := hJ j hj
    refine ⟨hJB hj, hne, ?_⟩
    by_contra hni
    exact hnadj ((dependencyGraph_adj_iff vars a j).mpr
      ⟨Ne.symm hne, (dep_iff_not_indep vars a j).mpr hni⟩)
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top (measure_ne_top μ _) (measure_ne_top μ _))
    (hlop a ha J hvars)
  rw [ENNReal.toReal_mul] at h
  exact h.trans (mul_le_mul_of_nonneg_right (hp a ha) ENNReal.toReal_nonneg)

/-- Shearer's lower bound for the existing PPG event and footprint model. -/
theorem ppg_good_event_lower_bound
    (A : BadEvents C Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (vars : CertVars C V) (p : C → ℝ) (B : Finset C)
    (hmeas : all_measurable A) (hlop : lll_lopsidependence A μ vars B)
    (hp : ∀ a ∈ B, event_prob A μ a ≤ p a)
    (hcriterion : StrictCriterion (dependencyGraph vars) p B) :
    polynomial (dependencyGraph vars) p B ≤ (μ (good_event A B)).toReal :=
  good_event_lower_bound (dependencyGraph vars) A μ p B hmeas
    (lopsidependence_of_ppg A μ vars p B hlop hp)
    (fun a ha => ENNReal.toReal_nonneg.trans (hp a ha)) hcriterion B Finset.Subset.rfl

/-- An ordinary dependency hypothesis is enough; users of the original
PPG LLL need only replace its numerical feasibility test. -/
theorem ppg_good_state_exists
    (A : BadEvents C Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (vars : CertVars C V) (p : C → ℝ) (B : Finset C)
    (hmeas : all_measurable A) (hindep : lll_independence A μ vars B)
    (hp : ∀ a ∈ B, event_prob A μ a ≤ p a)
    (hcriterion : StrictCriterion (dependencyGraph vars) p B) :
    (good_event A B).Nonempty :=
  good_state_exists (dependencyGraph vars) A μ p B hmeas
    (lopsidependence_of_ppg A μ vars p B
      (independence_implies_lopsidependence A μ vars B hindep) hp)
    (fun a ha => ENNReal.toReal_nonneg.trans (hp a ha)) hcriterion

end Shearer

#check @Shearer.passProbability_empty
#check @Shearer.passProbability_nonneg
#check @Shearer.fundamental_probability_inequality
#check @Shearer.good_event_lower_bound
#check @Shearer.positive_probability
#check @Shearer.good_state_exists
#check @Shearer.lopsidependence_of_ppg
#check @Shearer.ppg_good_event_lower_bound
#check @Shearer.ppg_good_state_exists
