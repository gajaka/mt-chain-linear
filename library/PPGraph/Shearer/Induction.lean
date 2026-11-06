/-
  PPGraphShearerInduction.lean

  The finite-set ratio induction behind the strict Shearer bound.
  Source: Harvey and Vondrak, arXiv:1711.06797, Section 2, Claims 2 and 3.
  https://arxiv.org/abs/1711.06797

  This file isolates the algebra. P is an avoidance probability, q is the
  corresponding Shearer polynomial, and R S a removes a and its relevant
  neighbors. The probability and polynomial recurrences are hypotheses here;
  their probabilistic/combinatorial justification belongs to a separate bridge.

  Strict positivity of q on every subset is essential to the ratio argument.
  No nonnegativity or termination hypothesis is imposed on P: normalization
  at the empty set and the recurrences imply the required positive lower bound.
-/

module

public import Mathlib.Tactic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Card

@[expose] public section

set_option autoImplicit false

namespace Shearer

variable {ι : Type*} [DecidableEq ι]

/-- The homogeneous form of the ratio induction. Normalization at the empty
set is not needed until this comparison is turned into an absolute bound. -/
theorem cross_ratio_le (B : Finset ι) (p : ι → ℝ) (P q : Finset ι → ℝ)
    (R : Finset ι → ι → Finset ι)
    (hp : ∀ a ∈ B, 0 ≤ p a)
    (hq_pos : ∀ S ⊆ B, 0 < q S)
    (hR : ∀ S ⊆ B, ∀ a ∈ S, R S a ⊆ S.erase a)
    (hq_rec : ∀ S ⊆ B, ∀ a ∈ S,
      q S = q (S.erase a) - p a * q (R S a))
    (hP_rec : ∀ S ⊆ B, ∀ a ∈ S,
      P (S.erase a) - p a * P (R S a) ≤ P S) :
    ∀ S ⊆ B, ∀ T ⊆ S, q S * P T ≤ P S * q T := by
  intro S
  refine Finset.strongInductionOn S ?_
  · intro S ih hSB T hTS
    by_cases heq : T = S
    · subst T
      exact le_of_eq (mul_comm _ _)
    have hstrict : T ⊂ S := lt_of_le_of_ne hTS heq
    obtain ⟨a, ha, hTE⟩ := Finset.ssubset_iff_exists_subset_erase.mp hstrict
    have hEB : S.erase a ⊆ B := (Finset.erase_subset a S).trans hSB
    have hqE : 0 < q (S.erase a) := hq_pos _ hEB
    have hqT : 0 < q T := hq_pos T (hTS.trans hSB)
    have hqS : 0 < q S := hq_pos S hSB
    have hER := ih (S.erase a) (Finset.erase_ssubset ha) hEB
      (R S a) (hR S hSB a ha)
    have hET := ih (S.erase a) (Finset.erase_ssubset ha) hEB T hTE
    have hrec := mul_le_mul_of_nonneg_right (hP_rec S hSB a ha) hqE.le
    have hratio := mul_le_mul_of_nonneg_left hER (hp a (hSB ha))
    have hedge : q S * P (S.erase a) ≤ P S * q (S.erase a) := by
      rw [hq_rec S hSB a ha]
      nlinarith only [hrec, hratio]
    have hleft := mul_le_mul_of_nonneg_left hET hqS.le
    have hright := mul_le_mul_of_nonneg_right hedge hqT.le
    have hscaled : (q S * P T) * q (S.erase a) ≤
        (P S * q T) * q (S.erase a) := by
      nlinarith only [hleft, hright]
    exact le_of_mul_le_mul_right hscaled hqE

#check @cross_ratio_le

/-- P/q is monotone under inclusion wherever the strict Shearer condition holds. -/
theorem ratio_mono (B : Finset ι) (p : ι → ℝ) (P q : Finset ι → ℝ)
    (R : Finset ι → ι → Finset ι)
    (hp : ∀ a ∈ B, 0 ≤ p a)
    (hq_pos : ∀ S ⊆ B, 0 < q S)
    (hR : ∀ S ⊆ B, ∀ a ∈ S, R S a ⊆ S.erase a)
    (hq_rec : ∀ S ⊆ B, ∀ a ∈ S,
      q S = q (S.erase a) - p a * q (R S a))
    (hP_rec : ∀ S ⊆ B, ∀ a ∈ S,
      P (S.erase a) - p a * P (R S a) ≤ P S)
    (S T : Finset ι) (hSB : S ⊆ B) (hTS : T ⊆ S) :
    P T / q T ≤ P S / q S := by
  apply (div_le_div_iff₀ (hq_pos T (hTS.trans hSB)) (hq_pos S hSB)).mpr
  simpa only [mul_comm] using cross_ratio_le B p P q R hp hq_pos hR hq_rec hP_rec S hSB T hTS

#check @ratio_mono

/-- Normalized recurrences imply the strict Shearer lower bound on every subset. -/
theorem probability_ge (B : Finset ι) (p : ι → ℝ) (P q : Finset ι → ℝ)
    (R : Finset ι → ι → Finset ι)
    (hP_empty : P ∅ = 1) (hq_empty : q ∅ = 1)
    (hp : ∀ a ∈ B, 0 ≤ p a)
    (hq_pos : ∀ S ⊆ B, 0 < q S)
    (hR : ∀ S ⊆ B, ∀ a ∈ S, R S a ⊆ S.erase a)
    (hq_rec : ∀ S ⊆ B, ∀ a ∈ S,
      q S = q (S.erase a) - p a * q (R S a))
    (hP_rec : ∀ S ⊆ B, ∀ a ∈ S,
      P (S.erase a) - p a * P (R S a) ≤ P S)
    (S : Finset ι) (hSB : S ⊆ B) : q S ≤ P S := by
  simpa only [hP_empty, hq_empty, mul_one] using
    cross_ratio_le B p P q R hp hq_pos hR hq_rec hP_rec S hSB ∅ (Finset.empty_subset S)

#check @probability_ge

/-- The strict polynomial condition certifies positive avoidance probability. -/
theorem probability_pos (B : Finset ι) (p : ι → ℝ) (P q : Finset ι → ℝ)
    (R : Finset ι → ι → Finset ι)
    (hP_empty : P ∅ = 1) (hq_empty : q ∅ = 1)
    (hp : ∀ a ∈ B, 0 ≤ p a)
    (hq_pos : ∀ S ⊆ B, 0 < q S)
    (hR : ∀ S ⊆ B, ∀ a ∈ S, R S a ⊆ S.erase a)
    (hq_rec : ∀ S ⊆ B, ∀ a ∈ S,
      q S = q (S.erase a) - p a * q (R S a))
    (hP_rec : ∀ S ⊆ B, ∀ a ∈ S,
      P (S.erase a) - p a * P (R S a) ≤ P S)
    (S : Finset ι) (hSB : S ⊆ B) : 0 < P S :=
  (hq_pos S hSB).trans_le
    (probability_ge B p P q R hP_empty hq_empty hp hq_pos hR hq_rec hP_rec S hSB)

#check @probability_pos

/-- The conditional avoidance ratio is bounded below by its polynomial ratio. -/
theorem conditional_ratio_le (B : Finset ι) (p : ι → ℝ) (P q : Finset ι → ℝ)
    (R : Finset ι → ι → Finset ι)
    (hP_empty : P ∅ = 1) (hq_empty : q ∅ = 1)
    (hp : ∀ a ∈ B, 0 ≤ p a)
    (hq_pos : ∀ S ⊆ B, 0 < q S)
    (hR : ∀ S ⊆ B, ∀ a ∈ S, R S a ⊆ S.erase a)
    (hq_rec : ∀ S ⊆ B, ∀ a ∈ S,
      q S = q (S.erase a) - p a * q (R S a))
    (hP_rec : ∀ S ⊆ B, ∀ a ∈ S,
      P (S.erase a) - p a * P (R S a) ≤ P S)
    (S T : Finset ι) (hSB : S ⊆ B) (hTS : T ⊆ S) :
    q S / q T ≤ P S / P T := by
  have hPT := probability_pos B p P q R hP_empty hq_empty hp hq_pos hR hq_rec hP_rec
    T (hTS.trans hSB)
  exact (div_le_div_iff₀ (hq_pos T (hTS.trans hSB)) hPT).mpr
    (cross_ratio_le B p P q R hp hq_pos hR hq_rec hP_rec S hSB T hTS)

#check @conditional_ratio_le

end Shearer
