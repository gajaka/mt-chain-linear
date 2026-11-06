/-
  Soundness of Farkas infeasibility certificates and an exact rational checker.
  Dlask--Werner, Bounding Linear Programs by Constraint Propagation (CP 2020),
  Theorem 1, Section 2.1. Only the certificate => infeasible direction is
  asserted here; existence/completeness of Farkas multipliers is not assumed.
  https://cmp.felk.cvut.cz/~dlaskto2/papers/Dlask-Werner-CP2020a.pdf
-/
module

public import PPGraph.Decision.Infeasibility

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RepairFeasibility

variable {C V : Type} [Fintype C] [Fintype V]

def LinearFeasible (A : C → V → ℝ) (b : C → ℝ) (x : V → ℝ) : Prop :=
  ∀ i, ∑ j, A i j * x j ≤ b i

def FarkasCertificate (A : C → V → ℝ) (b y : C → ℝ) : Prop :=
  (∀ i, 0 ≤ y i) ∧ (∀ j, ∑ i, y i * A i j = 0) ∧ ∑ i, y i * b i < 0

theorem weighted_linear_sum (A : C → V → ℝ) (y : C → ℝ) (x : V → ℝ) :
    (∑ i, y i * ∑ j, A i j * x j) = ∑ j, (∑ i, y i * A i j) * x j := by
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_mul]

theorem linear_combination_valid (A : C → V → ℝ) (b y : C → ℝ)
    (hy : ∀ i, 0 ≤ y i) (x : V → ℝ) (hx : LinearFeasible A b x) :
    ∑ j, (∑ i, y i * A i j) * x j ≤ ∑ i, y i * b i := by
  rw [← weighted_linear_sum]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hx i) (hy i)

theorem farkasCertificate_no_solution (A : C → V → ℝ) (b y : C → ℝ)
    (h : FarkasCertificate A b y) : ¬ ∃ x, LinearFeasible A b x := by
  rintro ⟨x, hx⟩
  have hw := linear_combination_valid A b y h.1 x hx
  simp only [h.2.1, zero_mul, Finset.sum_const_zero] at hw
  exact (not_lt_of_ge hw) h.2.2

/-- All certificate arithmetic is rational and decidable, including strict negativity. -/
def farkasCheck (A : C → V → ℚ) (b y : C → ℚ) : Bool :=
  decide ((∀ i, 0 ≤ y i) ∧ (∀ j, ∑ i, y i * A i j = 0) ∧ ∑ i, y i * b i < 0)

theorem farkasCheck_sound (A : C → V → ℚ) (b y : C → ℚ)
    (h : farkasCheck A b y = true) :
    FarkasCertificate (fun i j => (A i j : ℝ)) (fun i => (b i : ℝ)) (fun i => (y i : ℝ)) := by
  have hc : (∀ i, 0 ≤ y i) ∧ (∀ j, ∑ i, y i * A i j = 0) ∧ ∑ i, y i * b i < 0 := by
    simpa only [farkasCheck, decide_eq_true_eq] using h
  refine ⟨?_, ?_, ?_⟩
  · intro i
    change 0 ≤ (y i : ℝ)
    exact_mod_cast hc.1 i
  · intro j
    change (∑ i, (y i : ℝ) * (A i j : ℝ)) = 0
    exact_mod_cast hc.2.1 j
  · change (∑ i, (y i : ℝ) * (b i : ℝ)) < 0
    exact_mod_cast hc.2.2

theorem farkasCheck_no_real_solution (A : C → V → ℚ) (b y : C → ℚ)
    (h : farkasCheck A b y = true) :
    ¬ ∃ x : V → ℝ, LinearFeasible (fun i j => (A i j : ℝ)) (fun i => (b i : ℝ)) x :=
  farkasCertificate_no_solution _ _ _ (farkasCheck_sound A b y h)

/-- A sound linear relaxation suffices: every good state must satisfy its rows. -/
theorem farkasCertificate_noReachableGood {State : Type} (G : RepairGraph State)
    (A : C → V → ℝ) (b y : C → ℝ) (coordinates : State → V → ℝ)
    (hmodel : ∀ z, G.invariant_holds z → LinearFeasible A b (coordinates z))
    (h : FarkasCertificate A b y) (v : State) : NoReachableGood G v := by
  rintro ⟨w, _, hw⟩
  exact farkasCertificate_no_solution A b y h ⟨coordinates w, hmodel w hw⟩

theorem farkasCheck_noReachableGood {State : Type} (G : RepairGraph State)
    (A : C → V → ℚ) (b y : C → ℚ) (coordinates : State → V → ℝ)
    (hmodel : ∀ z, G.invariant_holds z →
      LinearFeasible (fun i j => (A i j : ℝ)) (fun i => (b i : ℝ)) (coordinates z))
    (h : farkasCheck A b y = true) (v : State) : NoReachableGood G v :=
  farkasCertificate_noReachableGood G _ _ _ coordinates hmodel (farkasCheck_sound A b y h) v

end RepairFeasibility

#check @RepairFeasibility.weighted_linear_sum
#check @RepairFeasibility.linear_combination_valid
#check @RepairFeasibility.farkasCertificate_no_solution
#check @RepairFeasibility.farkasCheck_sound
#check @RepairFeasibility.farkasCheck_no_real_solution
#check @RepairFeasibility.farkasCertificate_noReachableGood
#check @RepairFeasibility.farkasCheck_noReachableGood
