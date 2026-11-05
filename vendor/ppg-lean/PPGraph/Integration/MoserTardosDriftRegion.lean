/-
  A symbolic separation between process convergence and the current
  graph/overlap criteria. No numerical example is instantiated.

  Full, nonempty footprints give a complete dependency graph. Its signed
  independence polynomial is 1 - sum p. Even the largest discount allowed
  by the current HLS overlap bounds leaves each weight at least p-p^2/17.
  If the sum of those floors is at least one, both current strict criteria
  fail, for every allowed matching and overlap vector. Positive mass of
  good states still proves finite expected MT work by full resampling.

  This is a sufficient description of a process-certified region. It is
  not a complete characterization outside Shearer/HLS, and makes no claim
  that positive good-state mass alone suffices for arbitrary footprints.
-/

module

public import PPGraph.MoserTardos.Process.FullResampling
public import PPGraph.Shearer.BDD
public import PPGraph.Shearer.Slack
public import PPGraph.HLS.DAG.Matching

@[expose] public section

set_option linter.unusedSectionVars false

open MeasureTheory Classical

namespace RepairDrift

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem remote_eq_empty_of_complete (G : SimpleGraph ι)
    (hcomplete : ∀ a b, a ≠ b → G.Adj a b) (T : Finset ι) (a : ι) :
    Shearer.remote G T a = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro b hb
  obtain ⟨_, hba, hnadj⟩ := Finset.mem_filter.mp hb
  exact hnadj (hcomplete a b hba.symm)

theorem polynomial_eq_one_sub_sum_of_complete (G : SimpleGraph ι)
    (hcomplete : ∀ a b, a ≠ b → G.Adj a b) (p : ι → ℝ) (T : Finset ι) :
    Shearer.polynomial G p T = 1 - ∑ i ∈ T, p i := by
  induction T using Finset.induction with
  | empty => simp
  | @insert a T ha ih =>
    rw [Shearer.polynomial_insert G p T a ha,
      remote_eq_empty_of_complete G hcomplete, Shearer.polynomial_empty,
      ih, Finset.sum_insert ha]
    ring

theorem not_strictCriterion_of_complete_sum (G : SimpleGraph ι)
    (hcomplete : ∀ a b, a ≠ b → G.Adj a b) (p : ι → ℝ)
    (hsum : 1 ≤ ∑ i, p i) : ¬ Shearer.StrictCriterion G p Finset.univ := by
  intro hc
  have hpos := hc Finset.univ (Finset.Subset.refl _)
  rw [polynomial_eq_one_sub_sum_of_complete G hcomplete] at hpos
  linarith

/-- A lower bound on every weight admitted by the current HLS criterion. -/
theorem hls_reduced_ge_floor (G : SimpleGraph ι) (p : ι → ℝ)
    (O : HLS.OverlapBounds G p) (i : ι) :
    p i - (p i)^2 / 17 ≤ O.reduced i := by
  have hp : 0 ≤ p i := (O.nonneg i).trans (O.le_prob i)
  have hsq : (O.delta i)^2 ≤ (p i)^2 := by
    nlinarith [O.nonneg i, O.le_prob i]
  unfold HLS.OverlapBounds.reduced HLS.reducedWeight
  nlinarith

theorem not_hlsCriterion_of_complete_floor_sum (G : SimpleGraph ι)
    (hcomplete : ∀ a b, a ≠ b → G.Adj a b) (p : ι → ℝ)
    (hsum : 1 ≤ ∑ i, (p i - (p i)^2 / 17))
    (O : HLS.OverlapBounds G p) :
    ¬ Shearer.StrictCriterion G O.reduced Finset.univ := by
  apply not_strictCriterion_of_complete_sum G hcomplete O.reduced
  exact hsum.trans (Finset.sum_le_sum (fun i _ => hls_reduced_ge_floor G p O i))

variable {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    {S : VarSpaces V} [Nonempty ι]

theorem fullResampling_dependencyGraph_complete (P : MTProcess S ι)
    (hfull : ∀ i, P.footprint i = Finset.univ) (a b : ι) (hne : a ≠ b) :
    (Shearer.dependencyGraph P.footprint).Adj a b := by
  apply (Shearer.dependencyGraph_adj_iff P.footprint a b).mpr
  refine ⟨hne, ?_⟩
  obtain ⟨v⟩ := ‹Nonempty V›
  exact ⟨v, by simp [hfull]⟩

/-- The probabilities are the actual event probabilities, not loose bounds. -/
theorem fullResampling_certified_outside_graph_region (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i))
    (hfull : ∀ i, P.footprint i = Finset.univ)
    (hgood : 0 < mtGoodProbability P) (p : ι → ℝ)
    (_hprob : ∀ i, (Measure.pi (fun v => S.measure v)).real (P.bad i) = p i)
    (hsum : 1 ≤ ∑ i, (p i - (p i)^2 / 17)) :
    randomInitETLog P < ⊤ ∧
      ¬ Shearer.StrictCriterion (Shearer.dependencyGraph P.footprint) p Finset.univ ∧
      (∀ O : HLS.OverlapBounds (Shearer.dependencyGraph P.footprint) p,
        ¬ Shearer.StrictCriterion (Shearer.dependencyGraph P.footprint)
          O.reduced Finset.univ) := by
  have hc := fullResampling_dependencyGraph_complete P hfull
  refine ⟨fullResampling_expected_work_lt_top P hbad hfull hgood, ?_, ?_⟩
  · apply not_strictCriterion_of_complete_sum _ hc p
    exact hsum.trans (Finset.sum_le_sum (fun i _ => by nlinarith [sq_nonneg (p i)]))
  · exact fun O => not_hlsCriterion_of_complete_floor_sum _ hc p hsum O

/-- A positive safe box can certify the same region without a state scan. -/
theorem fullResampling_box_certified_outside_graph_region (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i))
    (hfull : ∀ i, P.footprint i = Finset.univ)
    (box : ∀ v, Set (S.space v)) (hmeas : ∀ v, MeasurableSet (box v))
    (hpos : ∀ v, 0 < S.measure v (box v))
    (hsafe : ∀ s : MTState S, (∀ v, s v ∈ box v) → MTGood P s)
    (p : ι → ℝ)
    (hprob : ∀ i, (Measure.pi (fun v => S.measure v)).real (P.bad i) = p i)
    (hsum : 1 ≤ ∑ i, (p i - (p i)^2 / 17)) :
    randomInitETLog P < ⊤ ∧
      ¬ Shearer.StrictCriterion (Shearer.dependencyGraph P.footprint) p Finset.univ ∧
      (∀ O : HLS.OverlapBounds (Shearer.dependencyGraph P.footprint) p,
        ¬ Shearer.StrictCriterion (Shearer.dependencyGraph P.footprint)
          O.reduced Finset.univ) := by
  exact fullResampling_certified_outside_graph_region P hbad hfull
    (mtGoodProbability_pos_of_box P box hmeas hpos hsafe) p hprob hsum

end RepairDrift

#check @RepairDrift.remote_eq_empty_of_complete
#check @RepairDrift.polynomial_eq_one_sub_sum_of_complete
#check @RepairDrift.not_strictCriterion_of_complete_sum
#check @RepairDrift.hls_reduced_ge_floor
#check @RepairDrift.not_hlsCriterion_of_complete_floor_sum
#check @RepairDrift.fullResampling_dependencyGraph_complete
#check @RepairDrift.fullResampling_certified_outside_graph_region
#check @RepairDrift.fullResampling_box_certified_outside_graph_region
