/-
  A dependency matching and its intersection-sensitive weight vectors.
  Fixed points of the involution are unmatched labels. All quantitative
  conclusions follow from the parameter algebra, not from a convergence
  premise. Source: He--Li--Sun, arXiv:2111.06527, Section 2.3.
  https://arxiv.org/abs/2111.06527
-/
module

public import PPGraph.HLS.Parameters
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace HLS

variable {ι : Type*}

structure DependencyMatching (G : SimpleGraph ι) where
  mate : ι → ι
  involutive : Function.Involutive mate
  adjacent : ∀ i, mate i ≠ i → G.Adj i (mate i)

structure OverlapBounds (G : SimpleGraph ι) (p : ι → ℝ) where
  matching : DependencyMatching G
  delta : ι → ℝ
  symmetric : ∀ i, delta (matching.mate i) = delta i
  unmatched : ∀ i, matching.mate i = i → delta i = 0
  nonneg : ∀ i, 0 ≤ delta i
  le_prob : ∀ i, delta i ≤ p i

namespace OverlapBounds

variable {G : SimpleGraph ι} {p : ι → ℝ} (D : OverlapBounds G p)

noncomputable def reduced (i : ι) : ℝ := reducedWeight (p i) (D.delta i)

noncomputable def prime (i : ι) : ℝ :=
  primeWeight (p i) (p (D.matching.mate i)) (D.delta i)

noncomputable def discount (i : ι) : ℝ :=
  savingFraction (p i) (p (D.matching.mate i)) (D.delta i)

noncomputable def splitUp (i : ι) : ℝ := D.prime i

noncomputable def splitDown (i : ι) : ℝ := D.reduced i - D.prime i

theorem mate_le_prob (i : ι) : D.delta i ≤ p (D.matching.mate i) := by
  simpa only [D.symmetric] using D.le_prob (D.matching.mate i)

theorem reduced_le (i : ι) : D.reduced i ≤ p i := reducedWeight_le _ _

theorem reduced_eq_unmatched (i : ι) (hi : D.matching.mate i = i) :
    D.reduced i = p i := by simp [reduced, reducedWeight, D.unmatched i hi]

theorem reduced_lt_of_overlap (i : ι) (hi : 0 < D.delta i) : D.reduced i < p i :=
  reducedWeight_lt _ _ hi

theorem reduced_pos (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i ≤ 1) (i : ι) :
    0 < D.reduced i := reducedWeight_pos _ _ _ (hp i) (hp _) (hp1 _)
      (D.nonneg i) (D.le_prob i) (D.mate_le_prob i)

theorem prime_pos (hp : ∀ i, 0 < p i) (i : ι) : 0 < D.prime i :=
  primeWeight_pos _ _ _ (hp i) (hp _) (D.nonneg i) (D.le_prob i) (D.mate_le_prob i)

theorem discount_nonneg (hp : ∀ i, 0 < p i) (i : ι) : 0 ≤ D.discount i :=
  savingFraction_nonneg _ _ _ (hp i) (hp _)

theorem discount_le (hp : ∀ i, 0 < p i) (i : ι) : D.discount i ≤ 1 / 8 :=
  savingFraction_le _ _ _ (hp i) (hp _) (D.nonneg i) (D.le_prob i) (D.mate_le_prob i)

theorem prime_eq_mul (hp : ∀ i, 0 < p i) (i : ι) :
    D.prime i = p i * (1 - D.discount i) :=
  primeWeight_eq_mul _ _ _ (hp i).ne' (hp _).ne'

theorem splitDown_nonneg (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i ≤ 1) (i : ι) :
    0 ≤ D.splitDown i := sub_nonneg.mpr
      (primeWeight_le_reducedWeight _ _ _ (hp _) (hp1 _))

theorem split_sum (i : ι) : D.splitUp i + D.splitDown i = D.reduced i := by
  unfold splitUp splitDown
  ring

/-- Fact 2.7 simultaneously at every matched or unmatched label. -/
theorem split_dominates (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i ≤ 1) (i : ι) :
    p i ≤ D.reduced i + D.reduced (D.matching.mate i) * D.splitDown i := by
  simpa only [reduced, splitDown, prime, D.symmetric] using
    splitWeight_dominates (p i) (p (D.matching.mate i)) (D.delta i)
      (hp _) (hp1 _) (D.nonneg i) (D.mate_le_prob i)

theorem four_choices_dominate (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i ≤ 1) (i : ι) :
    p i ≤ D.splitUp i + D.splitDown i +
      D.splitDown i * D.splitUp (D.matching.mate i) +
      D.splitDown i * D.splitDown (D.matching.mate i) := by
  calc
    p i ≤ D.reduced i + D.reduced (D.matching.mate i) * D.splitDown i :=
      D.split_dominates hp hp1 i
    _ = _ := by rw [← D.split_sum i, ← D.split_sum (D.matching.mate i)]; ring

end OverlapBounds
end HLS

#check @HLS.OverlapBounds.mate_le_prob
#check @HLS.OverlapBounds.reduced_le
#check @HLS.OverlapBounds.reduced_eq_unmatched
#check @HLS.OverlapBounds.reduced_lt_of_overlap
#check @HLS.OverlapBounds.reduced_pos
#check @HLS.OverlapBounds.prime_pos
#check @HLS.OverlapBounds.discount_nonneg
#check @HLS.OverlapBounds.discount_le
#check @HLS.OverlapBounds.prime_eq_mul
#check @HLS.OverlapBounds.splitDown_nonneg
#check @HLS.OverlapBounds.split_sum
#check @HLS.OverlapBounds.split_dominates
#check @HLS.OverlapBounds.four_choices_dominate
