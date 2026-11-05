/-
  Downward closure of the strict Shearer region and the slack budget bound.
  The singleton bound is Lemma 3.14 of He--Li--Sun, arXiv:2111.06527,
  attributed there to Kolipaka--Szegedy. The proof here uses only the
  already proved deletion identity and finite coordinate updates.
  https://arxiv.org/abs/2111.06527
-/
module

public import PPGraph.Shearer.Stable
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Classical

namespace Shearer

variable {ι : Type*} [DecidableEq ι]

theorem polynomial_congr (G : SimpleGraph ι) (p q : ι → ℝ) (B : Finset ι)
    (h : ∀ i ∈ B, p i = q i) : polynomial G p B = polynomial G q B := by
  unfold polynomial
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.prod_congr rfl
  intro i hi
  rw [h i (Finset.mem_powerset.mp (Finset.mem_filter.mp hI).1 hi)]

theorem strictCriterion_congr (G : SimpleGraph ι) (p q : ι → ℝ) (B : Finset ι)
    (h : ∀ i ∈ B, p i = q i) : StrictCriterion G p B ↔ StrictCriterion G q B := by
  unfold StrictCriterion
  have heq (T : Finset ι) (hT : T ⊆ B) : polynomial G p T = polynomial G q T :=
    polynomial_congr G p q T (fun i hi => h i (hT hi))
  constructor <;> intro hc T hT
  · rw [← heq T hT]
    exact hc T hT
  · rw [heq T hT]
    exact hc T hT

theorem polynomial_update_of_notMem (G : SimpleGraph ι) (p : ι → ℝ)
    (B : Finset ι) (a : ι) (x : ℝ) (ha : a ∉ B) :
    polynomial G (Function.update p a x) B = polynomial G p B := by
  apply polynomial_congr
  intro i hi
  have hia : i ≠ a := fun h => ha (h ▸ hi)
  exact Function.update_of_ne hia _ _

theorem polynomial_update_of_mem (G : SimpleGraph ι) (p : ι → ℝ)
    (B : Finset ι) (a : ι) (x : ℝ) (ha : a ∈ B) :
    polynomial G (Function.update p a x) B =
      polynomial G p B + (p a - x) * polynomial G p (remote G B a) := by
  have har : a ∉ remote G B a := by simp [remote]
  rw [polynomial_delete G (Function.update p a x) B a ha,
    polynomial_update_of_notMem G p (B.erase a) a x (Finset.notMem_erase _ _),
    polynomial_update_of_notMem G p (remote G B a) a x har,
    Function.update_self, polynomial_delete G p B a ha]
  ring

/-- Decreasing a coordinate preserves strict positivity on every subset. -/
theorem strictCriterion_update_le (G : SimpleGraph ι) (p : ι → ℝ)
    (B : Finset ι) (a : ι) (x : ℝ) (hc : StrictCriterion G p B)
    (hx : a ∈ B → x ≤ p a) : StrictCriterion G (Function.update p a x) B := by
  intro T hT
  by_cases ha : a ∈ T
  · rw [polynomial_update_of_mem G p T a x ha]
    exact add_pos_of_pos_of_nonneg (hc T hT)
      (mul_nonneg (sub_nonneg.mpr (hx (hT ha)))
        (hc _ ((remote_subset G T a).trans hT)).le)
  · rw [polynomial_update_of_notMem G p T a x ha]
    exact hc T hT

/-- The strict region is downward closed, proved by finite coordinate updates. -/
theorem strictCriterion_mono_weights (G : SimpleGraph ι) (p q : ι → ℝ)
    (B : Finset ι) (hle : ∀ i ∈ B, p i ≤ q i)
    (hc : StrictCriterion G q B) : StrictCriterion G p B := by
  have hchange (U : Finset ι) :
      StrictCriterion G (fun i => if i ∈ U then p i else q i) B := by
    induction U using Finset.induction with
    | empty => simpa using hc
    | @insert a U ha ih =>
      have heq : (fun i => if i ∈ insert a U then p i else q i) =
          Function.update (fun i => if i ∈ U then p i else q i) a (p a) := by
        funext i
        by_cases hi : i = a
        · subst i
          simp
        · simp [hi]
      rw [heq]
      apply strictCriterion_update_le G _ B a (p a) ih
      intro haB
      simpa [ha] using hle a haB
  exact (strictCriterion_congr G (fun i => if i ∈ B then p i else q i) p B
    (fun i hi => ite_eq_left hi)).mp (hchange B)

theorem coefficient_singleton (G : SimpleGraph ι) (p : ι → ℝ)
    (B : Finset ι) (a : ι) (ha : a ∈ B) :
    coefficient G p B {a} = p a * polynomial G p (remote G B a) := by
  have hind : Independent G {a} := by simp [Independent]
  have hout : outside G B {a} = remote G B a := by
    ext i
    simp [mem_outside, remote]
  rw [coefficient_factor G p B {a} (Finset.singleton_subset_iff.mpr ha) hind, hout]
  simp

/-- Increasing just a single coordinate by the available slack leaves a
positive polynomial. Its linear dependence bounds that label's budget. -/
theorem stableBudget_singleton_lt_inv_slack (G : SimpleGraph ι) (p : ι → ℝ)
    (B : Finset ι) (a : ι) (ha : a ∈ B) (ε : ℝ) (hε : 0 < ε)
    (hp : ∀ i ∈ B, 0 ≤ p i)
    (hslack : StrictCriterion G (fun i => (1 + ε) * p i) B) :
    stableBudget G p B {a} < 1 / ε := by
  have hc : StrictCriterion G p B := strictCriterion_mono_weights G p _ B
    (fun i hi => by nlinarith [hp i hi]) hslack
  have hsingle : StrictCriterion G (Function.update p a ((1 + ε) * p a)) B := by
    apply strictCriterion_mono_weights G _ _ B ?_ hslack
    intro i hi
    by_cases hia : i = a
    · subst i
      simp
    · rw [Function.update_of_ne hia]
      nlinarith [hp i hi]
  have hpositive := hsingle B Finset.Subset.rfl
  rw [polynomial_update_of_mem G p B a ((1 + ε) * p a) ha] at hpositive
  rw [stableBudget, coefficient_singleton G p B a ha]
  apply (div_lt_div_iff₀ (hc B Finset.Subset.rfl) hε).mpr
  nlinarith only [hpositive]

theorem stableBudget_singleton_le_inv_slack (G : SimpleGraph ι) (p : ι → ℝ)
    (B : Finset ι) (a : ι) (ha : a ∈ B) (ε : ℝ) (hε : 0 < ε)
    (hp : ∀ i ∈ B, 0 ≤ p i)
    (hslack : StrictCriterion G (fun i => (1 + ε) * p i) B) :
    stableBudget G p B {a} ≤ 1 / ε :=
  (stableBudget_singleton_lt_inv_slack G p B a ha ε hε hp hslack).le

/-- Lemma 3.14: summing the per-label bound gives the explicit work budget. -/
theorem sum_stableBudget_le_card_div_slack (G : SimpleGraph ι) (p : ι → ℝ)
    (B : Finset ι) (ε : ℝ) (hε : 0 < ε) (hp : ∀ i ∈ B, 0 ≤ p i)
    (hslack : StrictCriterion G (fun i => (1 + ε) * p i) B) :
    (∑ i ∈ B, stableBudget G p B {i}) ≤ (B.card : ℝ) / ε := by
  calc
    (∑ i ∈ B, stableBudget G p B {i}) ≤ ∑ _i ∈ B, (1 : ℝ) / ε :=
      Finset.sum_le_sum (fun i hi =>
        stableBudget_singleton_le_inv_slack G p B i hi ε hε hp hslack)
    _ = (B.card : ℝ) / ε := by simp [div_eq_mul_inv]

end Shearer

#check @Shearer.polynomial_congr
#check @Shearer.strictCriterion_congr
#check @Shearer.polynomial_update_of_notMem
#check @Shearer.polynomial_update_of_mem
#check @Shearer.strictCriterion_update_le
#check @Shearer.strictCriterion_mono_weights
#check @Shearer.coefficient_singleton
#check @Shearer.stableBudget_singleton_lt_inv_slack
#check @Shearer.stableBudget_singleton_le_inv_slack
#check @Shearer.sum_stableBudget_le_card_div_slack
