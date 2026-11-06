/- Pair-keyed fair coins and their relative orientation at either endpoint. -/
module

public import PPGraph.HLS.Probability.AugmentedSpace
public import PPGraph.HLS.DAG.PairKeys

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Classical MeasureTheory

namespace HLS

variable {ι : Type} [DecidableEq ι] [Nonempty ι] {G : SimpleGraph ι}

def swapCoin : OrientationCoin → OrientationCoin
  | .keep => .flip
  | .flip => .keep

theorem measurable_swapCoin : Measurable swapCoin := measurable_from_top

theorem map_swapCoin : fairOrientation.map swapCoin = fairOrientation := by
  unfold fairOrientation
  rw [ProbabilityTheory.map_bernoulliMeasure]
  simp only [swapCoin, ProbabilityTheory.bernoulliMeasure_def,
    coinParameter_toNNReal, coinParameter_symm_toNNReal]
  exact add_comm _ _

noncomputable def pairLeader (K : Finset ι) : ι :=
  if h : K.Nonempty then h.choose else Classical.choice inferInstance

theorem pairLeader_mem (K : Finset ι) (h : K.Nonempty) : pairLeader K ∈ K := by
  simp only [pairLeader, dite_eq_left h]
  exact h.choose_spec

noncomputable def relativeCoin (M : DependencyMatching G) (i : ι) (c : OrientationCoin) : OrientationCoin :=
  if pairLeader (M.pair i) = i then c else swapCoin c

noncomputable def coinLabel (M : DependencyMatching G) (K : Finset ι) : OrientationCoin → ι
  | .keep => pairLeader K
  | .flip => M.mate (pairLeader K)

theorem measurable_relativeCoin (M : DependencyMatching G) (i : ι) :
    Measurable (relativeCoin M i) := measurable_from_top

theorem map_relativeCoin (M : DependencyMatching G) (i : ι) :
    fairOrientation.map (relativeCoin M i) = fairOrientation := by
  unfold relativeCoin
  split_ifs
  · exact Measure.map_id
  · exact map_swapCoin

theorem coinLabel_target_iff_relative_flip (M : DependencyMatching G) (i : ι)
    (hi : M.mate i ≠ i) (c : OrientationCoin) :
    coinLabel M (M.pair i) c = M.mate i ↔ relativeCoin M i c = .flip := by
  have hleader := pairLeader_mem (M.pair i) ⟨i, M.mem_pair_self i⟩
  simp only [DependencyMatching.pair, Finset.mem_insert, Finset.mem_singleton] at hleader
  change pairLeader (M.pair i) = i ∨ pairLeader (M.pair i) = M.mate i at hleader
  rcases hleader with hl | hl
  · cases c <;> simp [coinLabel, relativeCoin, hl, hi.symm]
  · cases c <;> simp [coinLabel, relativeCoin, hl, hi, hi.symm, M.involutive i, swapCoin]

end HLS

#check @HLS.measurable_swapCoin
#check @HLS.map_swapCoin
#check @HLS.pairLeader_mem
#check @HLS.measurable_relativeCoin
#check @HLS.map_relativeCoin
#check @HLS.coinLabel_target_iff_relative_flip
