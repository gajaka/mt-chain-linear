/-
  Explicit slack bounds for the existing random-initialized MT process.
  This is the Shearer portion of the final He--Li--Sun argument; the
  intersection-sensitive process bound requires its separate DAG bridge.
  Source: He--Li--Sun, arXiv:2111.06527, Lemma 3.14.
-/
module

public import PPGraph.Shearer.Slack
public import PPGraph.Shearer.Expectation

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped ENNReal

namespace Shearer

variable {V : Type} [DecidableEq V] [Fintype V] {S : VarSpaces V}
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem randomInitExpectedResamplingCount_le_inv_slack
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i))
    (p : ι → ℝ) (hp : ∀ i, event_prob P.bad (Measure.pi (fun v => S.measure v)) i ≤ p i)
    (ε : ℝ) (hε : 0 < ε)
    (hslack : StrictCriterion (dependencyGraph P.footprint) (fun i => (1 + ε) * p i)
      Finset.univ) (α : ι) :
    randomInitExpectedResamplingCount P α ≤ ENNReal.ofReal (1 / ε) := by
  have hn := (event_prob_bounds P p hp).1
  have hc := strictCriterion_mono_weights (dependencyGraph P.footprint) p _ Finset.univ
    (fun i _ => by nlinarith [hn i]) hslack
  exact (randomInitExpectedResamplingCount_le_stableBudget P hbad p hp hc α).trans
    (ENNReal.ofReal_le_ofReal (stableBudget_singleton_le_inv_slack
      (dependencyGraph P.footprint) p Finset.univ α (Finset.mem_univ _) ε hε
        (fun i _ => hn i) hslack))

theorem randomInitETLog_le_card_div_slack
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i))
    (p : ι → ℝ) (hp : ∀ i, event_prob P.bad (Measure.pi (fun v => S.measure v)) i ≤ p i)
    (ε : ℝ) (hε : 0 < ε)
    (hslack : StrictCriterion (dependencyGraph P.footprint) (fun i => (1 + ε) * p i)
      Finset.univ) :
    randomInitETLog P ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) / ε) := by
  have hn := (event_prob_bounds P p hp).1
  have hc := strictCriterion_mono_weights (dependencyGraph P.footprint) p _ Finset.univ
    (fun i _ => by nlinarith [hn i]) hslack
  exact (randomInitETLog_le_sum_stableBudget P hbad p hp hc).trans
    (ENNReal.ofReal_le_ofReal (by
      simpa only [Finset.card_univ] using sum_stableBudget_le_card_div_slack
        (dependencyGraph P.footprint) p Finset.univ ε hε (fun i _ => hn i) hslack))

end Shearer

#check @Shearer.randomInitExpectedResamplingCount_le_inv_slack
#check @Shearer.randomInitETLog_le_card_div_slack
