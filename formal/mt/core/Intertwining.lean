import KernelWork

set_option autoImplicit false

namespace MTChainFormal

open scoped BigOperators ENNReal
open Filter

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

/-- Averaging a raw-state function through an explicitly supplied completion law. -/
noncomputable def disaggregate (D : A → B → ℝ) (f : B → ℝ) (a : A) : ℝ :=
  ∑ b, D a b * f b

/-- The concrete finite matrix identity D P = Q D. -/
def Intertwines (Q : FiniteKernel A) (P : FiniteKernel B) (D : A → B → ℝ) : Prop :=
  ∀ a b, (∑ u, D a u * P.weight u b) = ∑ v, Q.weight a v * D v b

omit [Fintype A] in
theorem disaggregate_comp (D : A → B → ℝ) (E : B → C → ℝ) (f : C → ℝ) (a : A) :
    disaggregate D (fun b => disaggregate E f b) a =
      disaggregate (fun a c => ∑ b, D a b * E b c) f a := by
  unfold disaggregate
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem expect_disaggregate (Q : FiniteKernel A) (P : FiniteKernel B)
    (D : A → B → ℝ) (hDP : Intertwines Q P D) (f : B → ℝ) (a : A) :
    expect Q (fun v => disaggregate D f v) a =
      disaggregate D (fun u => expect P f u) a := by
  change disaggregate Q.weight (fun v => disaggregate D f v) a =
    disaggregate D (fun u => disaggregate P.weight f u) a
  rw [disaggregate_comp, disaggregate_comp]
  apply Finset.sum_congr rfl
  intro b _
  exact congrArg (fun x : ℝ => x * f b) (hDP a b).symm

omit [Fintype A] in
theorem disaggregate_add (D : A → B → ℝ) (f g : B → ℝ) (a : A) :
    disaggregate D (fun b => f b + g b) a = disaggregate D f a + disaggregate D g a := by
  simp [disaggregate, mul_add, Finset.sum_add_distrib]

omit [Fintype A] in
theorem disaggregate_eq_of_support (D : A → B → ℝ) (f : B → ℝ) (g : A → ℝ)
    (hnorm : ∀ a, ∑ b, D a b = 1)
    (hsupport : ∀ a b, D a b ≠ 0 → f b = g a) (a : A) :
    disaggregate D f a = g a := by
  calc
    disaggregate D f a = ∑ b, D a b * g a := by
      apply Finset.sum_congr rfl
      intro b _
      by_cases hz : D a b = 0
      · simp [hz]
      · rw [hsupport a b hz]
    _ = g a := by rw [← Finset.sum_mul, hnorm a, one_mul]

theorem work_transport (Q : FiniteKernel A) (P : FiniteKernel B)
    (D : A → B → ℝ) (hDP : Intertwines Q P D) (cQ : A → ℝ) (cP : B → ℝ)
    (hcost : ∀ a, cQ a = disaggregate D cP a) (m : ℕ) (a : A) :
    work Q cQ m a = disaggregate D (work P cP m) a := by
  induction m generalizing a with
  | zero => simp [disaggregate]
  | succ m ih =>
      change cQ a + expect Q (work Q cQ m) a =
        disaggregate D (fun b => cP b + expect P (work P cP m) b) a
      have hfun : work Q cQ m = fun v => disaggregate D (work P cP m) v := funext ih
      rw [hfun, expect_disaggregate Q P D hDP, disaggregate_add, hcost]

/-- Push an initial observation law forward through the completion matrix. -/
noncomputable def pushedLaw (ν : A → ℝ) (D : A → B → ℝ) (b : B) : ℝ :=
  ∑ a, ν a * D a b

omit [Fintype B] in
theorem pushedLaw_nonneg (ν : A → ℝ) (D : A → B → ℝ)
    (hν : ∀ a, 0 ≤ ν a) (hD : ∀ a b, 0 ≤ D a b) (b : B) :
    0 ≤ pushedLaw ν D b := by
  exact Finset.sum_nonneg (fun a _ => mul_nonneg (hν a) (hD a b))

theorem pushedLaw_sum (ν : A → ℝ) (D : A → B → ℝ)
    (hν : ∑ a, ν a = 1) (hD : ∀ a, ∑ b, D a b = 1) :
    ∑ b, pushedLaw ν D b = 1 := by
  unfold pushedLaw
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hD, mul_one]
  exact hν

theorem weighted_disaggregate (ν : A → ℝ) (D : A → B → ℝ) (f : B → ℝ) :
    (∑ a, ν a * disaggregate D f a) = ∑ b, pushedLaw ν D b * f b := by
  unfold disaggregate pushedLaw
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem initialWork_transport (Q : FiniteKernel A) (P : FiniteKernel B)
    (D : A → B → ℝ) (hDP : Intertwines Q P D) (cQ : A → ℝ) (cP : B → ℝ)
    (hcost : ∀ a, cQ a = disaggregate D cP a) (ν : A → ℝ) (μ : B → ℝ)
    (hlaw : ∀ b, μ b = pushedLaw ν D b) (m : ℕ) :
    initialWork Q ν cQ m = initialWork P μ cP m := by
  unfold initialWork
  simp_rw [work_transport Q P D hDP cQ cP hcost, hlaw]
  exact weighted_disaggregate ν D (work P cP m)

theorem initialTotalWork_transport (Q : FiniteKernel A) (P : FiniteKernel B)
    (D : A → B → ℝ) (hDP : Intertwines Q P D) (cQ : A → ℝ) (cP : B → ℝ)
    (hcost : ∀ a, cQ a = disaggregate D cP a) (ν : A → ℝ) (μ : B → ℝ)
    (hlaw : ∀ b, μ b = pushedLaw ν D b) :
    initialTotalWork Q ν cQ = initialTotalWork P μ cP := by
  apply iSup_congr
  intro m
  rw [initialWork_transport Q P D hDP cQ cP hcost ν μ hlaw]

theorem transported_initialTotalWork_le (Q : FiniteKernel A) (P : FiniteKernel B)
    (D : A → B → ℝ) (hDP : Intertwines Q P D) (cQ : A → ℝ) (cP : B → ℝ)
    (hcost : ∀ a, cQ a = disaggregate D cP a) (ν : A → ℝ) (μ : B → ℝ)
    (hlaw : ∀ b, μ b = pushedLaw ν D b) (hν : ∀ a, 0 ≤ ν a)
    (V : A → ℝ) (hV : ∀ a, 0 ≤ V a)
    (hstep : ∀ a, cQ a + expect Q V a ≤ V a) :
    initialTotalWork P μ cP ≤ ENNReal.ofReal (∑ a, ν a * V a) := by
  rw [← initialTotalWork_transport Q P D hDP cQ cP hcost ν μ hlaw]
  exact initialTotalWork_le_supersolution Q ν cQ V hν hV hstep

theorem transported_initialTotalWork_le_uniform (Q : FiniteKernel A) (P : FiniteKernel B)
    (D : A → B → ℝ) (hDP : Intertwines Q P D) (cQ : A → ℝ) (cP : B → ℝ)
    (hcost : ∀ a, cQ a = disaggregate D cP a) (ν : A → ℝ) (μ : B → ℝ)
    (hlaw : ∀ b, μ b = pushedLaw ν D b) (hν : ∀ a, 0 ≤ ν a)
    (hnorm : ∑ a, ν a = 1) (V : A → ℝ) (hV : ∀ a, 0 ≤ V a)
    (hstep : ∀ a, cQ a + expect Q V a ≤ V a) (M : ℝ) (hM : ∀ a, V a ≤ M) :
    initialTotalWork P μ cP ≤ ENNReal.ofReal M := by
  rw [← initialTotalWork_transport Q P D hDP cQ cP hcost ν μ hlaw]
  exact initialTotalWork_le_uniform Q ν cQ V hν hnorm hV hstep M hM

theorem transported_initialTotalWork_lt_top (Q : FiniteKernel A) (P : FiniteKernel B)
    (D : A → B → ℝ) (hDP : Intertwines Q P D) (cQ : A → ℝ) (cP : B → ℝ)
    (hcost : ∀ a, cQ a = disaggregate D cP a) (ν : A → ℝ) (μ : B → ℝ)
    (hlaw : ∀ b, μ b = pushedLaw ν D b) (hν : ∀ a, 0 ≤ ν a)
    (V : A → ℝ) (hV : ∀ a, 0 ≤ V a)
    (hstep : ∀ a, cQ a + expect Q V a ≤ V a) :
    initialTotalWork P μ cP < ∞ := by
  exact lt_of_le_of_lt
    (transported_initialTotalWork_le Q P D hDP cQ cP hcost ν μ hlaw hν V hV hstep)
    ENNReal.ofReal_lt_top

theorem transported_initialReward_tendsto_zero (Q : FiniteKernel A) (P : FiniteKernel B)
    (D : A → B → ℝ) (hDP : Intertwines Q P D) (cQ : A → ℝ) (cP : B → ℝ)
    (hcost : ∀ a, cQ a = disaggregate D cP a) (ν : A → ℝ) (μ : B → ℝ)
    (hlaw : ∀ b, μ b = pushedLaw ν D b) (hν : ∀ a, 0 ≤ ν a)
    (hD : ∀ a b, 0 ≤ D a b) (hcP : ∀ b, 0 ≤ cP b)
    (V : A → ℝ) (hV : ∀ a, 0 ≤ V a)
    (hstep : ∀ a, cQ a + expect Q V a ≤ V a) :
    Tendsto (fun t : ℕ => ENNReal.ofReal (initialRewardAt P μ cP t)) atTop (nhds 0) := by
  apply initialRewardAt_tendsto_zero P μ cP _ hcP
    (transported_initialTotalWork_lt_top Q P D hDP cQ cP hcost ν μ hlaw hν V hV hstep)
  intro b
  rw [hlaw b]
  exact pushedLaw_nonneg ν D hν hD b

end MTChainFormal
