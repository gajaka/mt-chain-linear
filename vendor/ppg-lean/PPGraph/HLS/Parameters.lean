/-
  Parameter algebra for He--Li--Sun, arXiv:2111.06527,
  Section 2.3 (Fact 2.7) and the estimate in Lemma 3.4.
  https://arxiv.org/abs/2111.06527

  The constants below belong to the general theorem. No concrete instance
  or numerical example is used. This file does not assert MT convergence.
-/
module

public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false

namespace HLS

noncomputable def savingFraction (a b δ : ℝ) : ℝ := δ ^ 2 / (8 * a * b)

noncomputable def primeWeight (a b δ : ℝ) : ℝ := a - δ ^ 2 / (8 * b)

noncomputable def reducedWeight (a δ : ℝ) : ℝ := a - δ ^ 2 / 17

theorem overlap_sq_le_product (a b δ : ℝ)
    (hδ : 0 ≤ δ) (haδ : δ ≤ a) (hbδ : δ ≤ b) : δ ^ 2 ≤ a * b := by
  simpa [pow_two] using mul_le_mul haδ hbδ hδ (hδ.trans haδ)

theorem savingFraction_nonneg (a b δ : ℝ) (ha : 0 < a) (hb : 0 < b) :
    0 ≤ savingFraction a b δ := by
  unfold savingFraction
  positivity

theorem savingFraction_le (a b δ : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hδ : 0 ≤ δ) (haδ : δ ≤ a) (hbδ : δ ≤ b) :
    savingFraction a b δ ≤ 1 / 8 := by
  unfold savingFraction
  apply (div_le_iff₀ (by positivity : 0 < 8 * a * b)).mpr
  have h := overlap_sq_le_product a b δ hδ haδ hbδ
  nlinarith

theorem primeWeight_eq_mul (a b δ : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    primeWeight a b δ = a * (1 - savingFraction a b δ) := by
  unfold primeWeight savingFraction
  field_simp

theorem primeWeight_pos (a b δ : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hδ : 0 ≤ δ) (haδ : δ ≤ a) (hbδ : δ ≤ b) :
    0 < primeWeight a b δ := by
  rw [primeWeight_eq_mul a b δ ha.ne' hb.ne']
  have h := savingFraction_le a b δ ha hb hδ haδ hbδ
  exact mul_pos ha (by linarith)

theorem primeWeight_le_reducedWeight (a b δ : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) :
    primeWeight a b δ ≤ reducedWeight a δ := by
  unfold primeWeight reducedWeight
  have hdiv : δ ^ 2 / 17 ≤ δ ^ 2 / (8 * b) := by
    apply div_le_div_of_nonneg_left (sq_nonneg δ) (by positivity)
    linarith
  linarith

theorem reducedWeight_pos (a b δ : ℝ) (ha : 0 < a) (hb : 0 < b) (hb1 : b ≤ 1)
    (hδ : 0 ≤ δ) (haδ : δ ≤ a) (hbδ : δ ≤ b) :
    0 < reducedWeight a δ :=
  (primeWeight_pos a b δ ha hb hδ haδ hbδ).trans_le
    (primeWeight_le_reducedWeight a b δ hb hb1)

theorem reducedWeight_le (a δ : ℝ) : reducedWeight a δ ≤ a := by
  unfold reducedWeight
  nlinarith [sq_nonneg δ]

theorem reducedWeight_lt (a δ : ℝ) (hδ : 0 < δ) : reducedWeight a δ < a := by
  unfold reducedWeight
  nlinarith [sq_pos_of_pos hδ]

/-- Fact 2.7: the four split-node choices dominate the original label weight. -/
theorem splitWeight_dominates (a b δ : ℝ) (hb : 0 < b) (hb1 : b ≤ 1)
    (hδ : 0 ≤ δ) (hbδ : δ ≤ b) :
    a ≤ reducedWeight a δ +
      reducedWeight b δ * (reducedWeight a δ - primeWeight a b δ) := by
  have hδ1 : δ ≤ 1 := hbδ.trans hb1
  have hs : δ ^ 2 ≤ b := by
    nlinarith [mul_nonneg hδ (sub_nonneg.mpr hbδ)]
  have hsb : δ ^ 2 * b ≤ b := by
    nlinarith [mul_nonneg hb.le (show 0 ≤ 1 - δ ^ 2 by nlinarith)]
  unfold reducedWeight primeWeight
  apply (mul_le_mul_iff_right₀ hb).mp
  field_simp
  nlinarith [sq_nonneg (δ ^ 2), mul_nonneg (sq_nonneg δ) (sub_nonneg.mpr hb1)]

/-- The coin-averaged two-event saving controls both endpoint discounts. -/
theorem pair_saving_le_discounted (a b δ : ℝ) (ha : 0 < a) (hb : 0 < b) :
    a * b - δ ^ 2 / 2 ≤
      a * b * (1 - 2 * savingFraction a b δ) *
        (1 - 2 * savingFraction b a δ) := by
  unfold savingFraction
  have hden : a * b ≠ 0 := mul_ne_zero ha.ne' hb.ne'
  apply (mul_le_mul_iff_right₀ (mul_pos ha hb)).mp
  field_simp
  nlinarith [sq_nonneg (δ ^ 2)]

/-- Integer form of the half-cover estimate; no fractional powers are needed. -/
theorem half_cover_discount (c : ℝ) (hc : 0 ≤ c) (hc2 : c ≤ 1 / 2)
    (k n : ℕ) (hcover : n ≤ 2 * k) :
    (1 - 2 * c) ^ k ≤ (1 - c) ^ n := by
  have h0 : 0 ≤ 1 - 2 * c := by linarith
  have h1 : 0 ≤ 1 - c := by linarith
  calc
    (1 - 2 * c) ^ k ≤ ((1 - c) ^ 2) ^ k := by
      apply pow_le_pow_left₀ h0
      nlinarith [sq_nonneg c]
    _ = (1 - c) ^ (2 * k) := by rw [pow_mul]
    _ ≤ (1 - c) ^ n := by
      apply pow_le_pow_of_le_one h1 (by linarith) hcover

end HLS

#check @HLS.overlap_sq_le_product
#check @HLS.savingFraction_nonneg
#check @HLS.savingFraction_le
#check @HLS.primeWeight_eq_mul
#check @HLS.primeWeight_pos
#check @HLS.primeWeight_le_reducedWeight
#check @HLS.reducedWeight_pos
#check @HLS.reducedWeight_le
#check @HLS.reducedWeight_lt
#check @HLS.splitWeight_dominates
#check @HLS.pair_saving_le_discounted
#check @HLS.half_cover_discount
