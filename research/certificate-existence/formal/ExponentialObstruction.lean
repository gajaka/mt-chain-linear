module

public import SeparationResults

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1800000

/-!
An exponential obstruction for stopped coordinate-separable potentials.
The remote final failure keeps all local witnesses active after every redraw.
The argument uses exact positive combinations of genuine pointwise drift
inequalities; it makes no claim about unrestricted potentials or novelty.
-/

namespace PotentialSeparation.Exponential

open MTChainFormal
open scoped BigOperators

noncomputable def centered (f : ThresholdCosts) (j : ℕ) (a : Fin 3) : ℝ :=
  f j a - mean3 (f j)

noncomputable def labelBias (g : TacticCosts) (j : ℕ) : ℝ :=
  (g j 1 - mean4 (g j)) / 3

theorem centered_sum (f : ThresholdCosts) (j : ℕ) :
    centered f j 0 + centered f j 1 + centered f j 2 = 0 := by
  norm_num [centered, mean3, Fin.sum_univ_succ]
  ring

theorem witness_selected_local {n j : ℕ} (hn : 4 ≤ n) (hj : 1 ≤ j)
    (hjn : j + 1 ≤ n - 2) (a b : Fin 3) (r : Fin 4)
    (hfail : MTChainProof.bridgePass a b r = false) :
    firstFailure (witness n j a b r) = some ⟨j, by omega⟩ := by
  apply firstFailure_of_failed_prefix
  · have ha := witness_value hn hj hjn a b r j (by omega)
    have hb := witness_value hn hj hjn a b r (j + 1) (by omega)
    simp only [show j ≠ 0 by omega, lt_self_iff_false, ↓reduceIte] at ha
    simp only [show j + 1 ≠ 0 by omega, show ¬j + 1 < j by omega,
      show j + 1 ≠ j by omega, ↓reduceIte] at hb
    have ht : (witness n j a b r).tactic ⟨j, by omega⟩ = r := by
      simp [witness, show j ≠ n - 1 by omega]
    simpa only [passes, ha, hb, ht] using hfail
  · intro k hk
    change k.val < j at hk
    have hfirst := witness_value hn hj hjn a b r k.val k.isLt
    have ht : (witness n j a b r).tactic k = 0 := by
      simp [witness, show k.val ≠ n - 1 by omega, show k.val ≠ j by omega]
    have hin : value (witness n j a b r) k.val = 2 := by
      rw [hfirst]
      split_ifs <;> simp_all
    simp only [passes, hin, ht, MTChainProof.bridgePass]
    simpa using Fin.le_last (value (witness n j a b r) (k.val + 1))

theorem local_drift {n j : ℕ} (hn : 4 ≤ n) (hj : 1 ≤ j)
    (hjn : j + 1 ≤ n - 2) (c : ℝ) (f : ThresholdCosts) (g : TacticCosts)
    (δ : ℝ) (hd : PointwiseDrift (n := n) c f g δ)
    (a b : Fin 3) (r : Fin 4) (hfail : MTChainProof.bridgePass a b r = false) :
    δ ≤ centered f j a + centered f (j + 1) b + g j r - mean4 (g j) := by
  have h := hd (witness n j a b r) ⟨j, by omega⟩
    (witness_selected_local hn hj hjn a b r hfail)
  rw [potential_of_active c f g _ (remote_active (by omega) _
    (witness_remote hn hj hjn a b r))] at h
  have hrep (u : Draw) :
      potential c f g (replace (witness n j a b r) ⟨j, by omega⟩ u) =
        rawScore c f g (replace (witness n j a b r) ⟨j, by omega⟩ u) :=
    potential_of_active c f g _ (remote_active (by omega) _
      (witness_replaced_remote hn hj hjn a b r u))
  simp_rw [hrep] at h
  rw [average_rawScore_replace hn hj hjn c f g] at h
  have ha := witness_value hn hj hjn a b r j (by omega)
  have hb := witness_value hn hj hjn a b r (j + 1) (by omega)
  have ht : (witness n j a b r).tactic ⟨j, by omega⟩ = r := by
    simp [witness, show j ≠ n - 1 by omega]
  simp only [show j ≠ 0 by omega, lt_self_iff_false, ↓reduceIte] at ha
  simp only [show j + 1 ≠ 0 by omega, show ¬j + 1 < j by omega,
    show j + 1 ≠ j by omega, ↓reduceIte] at hb
  rw [ha, hb, ht] at h
  unfold centered
  linarith

theorem weak_pair {n j : ℕ} (hn : 4 ≤ n) (hj : 1 ≤ j)
    (hjn : j + 1 ≤ n - 2) (c : ℝ) (f : ThresholdCosts) (g : TacticCosts)
    (δ : ℝ) (hd : PointwiseDrift (n := n) c f g δ)
    (a b : Fin 3) (hab : a ≠ b) :
    δ ≤ centered f j a + centered f (j + 1) b + 3 * labelBias g j := by
  have h := local_drift hn hj hjn c f g δ hd a b 1
    (by simp [MTChainProof.bridgePass, hab])
  unfold labelBias
  linarith

theorem strong_pair {n j : ℕ} (hn : 4 ≤ n) (hj : 1 ≤ j)
    (hjn : j + 1 ≤ n - 2) (c : ℝ) (f : ThresholdCosts) (g : TacticCosts)
    (δ : ℝ) (hd : PointwiseDrift (n := n) c f g δ)
    (a b : Fin 3) (hab : a < b) :
    δ ≤ centered f j a + centered f (j + 1) b - labelBias g j := by
  have h0 := witness_drift hn hj hjn c f g δ hd a b hab 0
  have h2 := witness_drift hn hj hjn c f g δ hd a b hab 2
  have h3 := witness_drift hn hj hjn c f g δ hd a b hab 3
  norm_num [centered, labelBias, mean4, Fin.sum_univ_succ] at h0 h2 h3 ⊢
  linarith

theorem labelBias_ge {n j : ℕ} (hn : 4 ≤ n) (hj : 1 ≤ j)
    (hjn : j + 1 ≤ n - 2) (c : ℝ) (f : ThresholdCosts) (g : TacticCosts)
    (δ : ℝ) (hd : PointwiseDrift (n := n) c f g δ) :
    δ / 3 ≤ labelBias g j := by
  have h01 := weak_pair hn hj hjn c f g δ hd 0 1 (by decide)
  have h02 := weak_pair hn hj hjn c f g δ hd 0 2 (by decide)
  have h10 := weak_pair hn hj hjn c f g δ hd 1 0 (by decide)
  have h12 := weak_pair hn hj hjn c f g δ hd 1 2 (by decide)
  have h20 := weak_pair hn hj hjn c f g δ hd 2 0 (by decide)
  have h21 := weak_pair hn hj hjn c f g δ hd 2 1 (by decide)
  have z := centered_sum f j
  have z' := centered_sum f (j + 1)
  linarith

/-- Weights 3,3,1,1 eliminate the tactic term exactly. -/
theorem left_transfer {n j : ℕ} (hn : 4 ≤ n) (hj : 1 ≤ j)
    (hjn : j + 1 ≤ n - 2) (c : ℝ) (f : ThresholdCosts) (g : TacticCosts)
    (δ : ℝ) (hd : PointwiseDrift (n := n) c f g δ) :
    centered f j 2 - 2 * δ ≤ 5 * (centered f (j + 1) 2 - 2 * δ) := by
  have s02 := strong_pair hn hj hjn c f g δ hd 0 2 (by decide)
  have s12 := strong_pair hn hj hjn c f g δ hd 1 2 (by decide)
  have w20 := weak_pair hn hj hjn c f g δ hd 2 0 (by decide)
  have w21 := weak_pair hn hj hjn c f g δ hd 2 1 (by decide)
  have z := centered_sum f j
  have z' := centered_sum f (j + 1)
  linarith

theorem right_transfer {n j : ℕ} (hn : 4 ≤ n) (hj : 1 ≤ j)
    (hjn : j + 1 ≤ n - 2) (c : ℝ) (f : ThresholdCosts) (g : TacticCosts)
    (δ : ℝ) (hd : PointwiseDrift (n := n) c f g δ) :
    centered f (j + 1) 0 - 2 * δ ≤ 5 * (centered f j 0 - 2 * δ) := by
  have s01 := strong_pair hn hj hjn c f g δ hd 0 1 (by decide)
  have s02 := strong_pair hn hj hjn c f g δ hd 0 2 (by decide)
  have w10 := weak_pair hn hj hjn c f g δ hd 1 0 (by decide)
  have w20 := weak_pair hn hj hjn c f g δ hd 2 0 (by decide)
  have z := centered_sum f j
  have z' := centered_sum f (j + 1)
  linarith

theorem crossing {n j : ℕ} (hn : 4 ≤ n) (hj : 1 ≤ j)
    (hjn : j + 1 ≤ n - 2) (c : ℝ) (f : ThresholdCosts) (g : TacticCosts)
    (δ : ℝ) (hd : PointwiseDrift (n := n) c f g δ) :
    centered f j 2 + centered f (j + 1) 0 ≤ -(8 / 3 : ℝ) * δ := by
  have s01 := strong_pair hn hj hjn c f g δ hd 0 1 (by decide)
  have s12 := strong_pair hn hj hjn c f g δ hd 1 2 (by decide)
  have hv := labelBias_ge hn hj hjn c f g δ hd
  have z := centered_sum f j
  have z' := centered_sum f (j + 1)
  linarith

theorem iterate_left (x : ℕ → ℝ) (m : ℕ)
    (hstep : ∀ j, 1 ≤ j → j + 1 ≤ m → x j ≤ 5 * x (j + 1))
    (j : ℕ) (hj : 1 ≤ j) (k : ℕ) :
    j + k ≤ m → x j ≤ (5 : ℝ)^k * x (j + k) := by
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have hp := ih (by omega : j + k ≤ m)
    have hs := hstep (j + k) (by omega) (by omega)
    have ht := mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ 5^k)
    calc
      x j ≤ (5 : ℝ)^k * x (j + k) := hp
      _ ≤ (5 : ℝ)^k * (5 * x (j + k + 1)) := ht
      _ = (5 : ℝ)^(k + 1) * x (j + (k + 1)) := by
        have heq : j + k + 1 = j + (k + 1) := by omega
        rw [pow_succ, heq]
        ring

theorem iterate_right (x : ℕ → ℝ) (m : ℕ)
    (hstep : ∀ j, 1 ≤ j → j + 1 ≤ m → x (j + 1) ≤ 5 * x j)
    (j : ℕ) (hj : 1 ≤ j) (k : ℕ) :
    j + k ≤ m → x (j + k) ≤ (5 : ℝ)^k * x j := by
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have hp := ih (by omega : j + k ≤ m)
    have hs := hstep (j + k) (by omega) (by omega)
    have ht := mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 5)
    have heq : j + (k + 1) = j + k + 1 := by omega
    rw [heq]
    calc
      x (j + k + 1) ≤ 5 * x (j + k) := hs
      _ ≤ 5 * ((5 : ℝ)^k * x j) := ht
      _ = (5 : ℝ)^(k + 1) * x j := by rw [pow_succ]; ring

theorem value_le_high (f : ThresholdCosts) (j : ℕ) (a : Fin 3) :
    f j a ≤ high (f j) := by
  unfold high
  exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩)

theorem oscillation_nonneg (f : ThresholdCosts) (j : ℕ) : 0 ≤ oscillation f j := by
  have hl := low_le (f j) 0
  have hh := value_le_high f j 0
  change 0 ≤ high (f j) - low (f j)
  linarith

theorem oscillation_ge_centered (f : ThresholdCosts) (j : ℕ) (a : Fin 3) :
    -(3 / 2 : ℝ) * centered f j a ≤ oscillation f j := by
  have hl := low_le (f j) a
  have h0 := value_le_high f j 0
  have h1 := value_le_high f j 1
  have h2 := value_le_high f j 2
  change -(3 / 2 : ℝ) * (f j a - mean3 (f j)) ≤ high (f j) - low (f j)
  fin_cases a <;> norm_num [mean3, Fin.sum_univ_succ] at * <;> linarith

theorem single_oscillation_le_sum {n : ℕ} (f : ThresholdCosts) (j : ℕ)
    (hj : 1 ≤ j) (hjn : j ≤ n - 2) :
    oscillation f j ≤ ∑ i : Fin (n - 2), oscillation f (i.val + 1) := by
  classical
  let i : Fin (n - 2) := ⟨j - 1, by omega⟩
  have h := Finset.single_le_sum
    (fun k (_ : k ∈ (Finset.univ : Finset (Fin (n - 2)))) => oscillation_nonneg f (k.val + 1))
    (Finset.mem_univ i)
  simpa only [i, show j - 1 + 1 = j by omega] using h

theorem large_oscillation {n k : ℕ} (hk : 2 * k + 4 ≤ n)
    (c : ℝ) (f : ThresholdCosts) (g : TacticCosts) (δ : ℝ)
    (hd : PointwiseDrift (n := n) c f g δ) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ n - 2 ∧
      δ * ((5 : ℝ)^(k + 1) - 3) ≤ oscillation f j := by
  have hn : 4 ≤ n := by omega
  have cross := crossing hn (j := k + 1) (by omega) (by omega) c f g δ hd
  have hp : (0 : ℝ) ≤ 5^k := by positivity
  by_cases hl : centered f (k + 1) 2 ≤ -(4 / 3 : ℝ) * δ
  · have hs (j : ℕ) (hj : 1 ≤ j) (hjn : j + 1 ≤ n - 2) :=
      left_transfer hn hj hjn c f g δ hd
    have hi := iterate_left (fun j => centered f j 2 - 2 * δ) (n - 2) hs 1
      (by omega) k (by omega)
    have hm := mul_le_mul_of_nonneg_left hl hp
    have ho := oscillation_ge_centered f 1 2
    refine ⟨1, by omega, by omega, ?_⟩
    have heq : 1 + k = k + 1 := by omega
    simp only [heq] at hi
    rw [pow_succ]
    nlinarith
  · have hr : centered f (k + 2) 0 ≤ -(4 / 3 : ℝ) * δ := by
      have hl' := lt_of_not_ge hl
      linarith
    have hs (j : ℕ) (hj : 1 ≤ j) (hjn : j + 1 ≤ n - 2) :=
      right_transfer hn hj hjn c f g δ hd
    have hi := iterate_right (fun j => centered f j 0 - 2 * δ) (n - 2) hs
      (k + 2) (by omega) k (by omega)
    have hm := mul_le_mul_of_nonneg_left hr hp
    have ho := oscillation_ge_centered f (2 * k + 2) 0
    refine ⟨2 * k + 2, by omega, by omega, ?_⟩
    have heq : k + 2 + k = 2 * k + 2 := by omega
    simp only [heq] at hi
    rw [pow_succ]
    nlinarith

/-- Every admitted stopped separable certificate pays exponentially in k.
There is room for k steps on each side whenever 2*k+4 <= n. -/
theorem budget_exponential_lower {n k : ℕ} (hk : 2 * k + 4 ≤ n)
    (c : ℝ) (f : ThresholdCosts) (g : TacticCosts) (δ : ℝ) (hδ : 0 < δ)
    (hnonneg : ∀ s : ChainState n, 0 ≤ potential c f g s)
    (hd : PointwiseDrift (n := n) c f g δ) :
    ((5 : ℝ)^(k + 1) - 3) / 36 ≤ initialBudget n c f g / δ := by
  obtain ⟨j, hj, hjn, ho⟩ := large_oscillation hk c f g δ hd
  have hs := single_oscillation_le_sum (n := n) f j hj hjn
  have hb := initial_budget_oscillation (by omega : 4 ≤ n) c f g hnonneg
  apply (le_div_iff₀ hδ).mpr
  nlinarith

theorem certificate_budget_exponential_lower {n k : ℕ} (hk : 2 * k + 4 ≤ n)
    (C : DriftCertificate n) :
    ((5 : ℝ)^(k + 1) - 3) / 36 ≤ certificateBudget C := by
  exact budget_exponential_lower hk C.offset C.thresholdCosts C.tacticCosts C.delta
    C.delta_positive C.nonnegative C.pointwise_drift

theorem certificate_budget_floor_lower {n : ℕ} (hn : 4 ≤ n)
    (C : DriftCertificate n) :
    ((5 : ℝ)^((n - 4) / 2 + 1) - 3) / 36 ≤ certificateBudget C := by
  apply certificate_budget_exponential_lower
  omega

end PotentialSeparation.Exponential

#print axioms PotentialSeparation.Exponential.budget_exponential_lower
#print axioms PotentialSeparation.Exponential.certificate_budget_floor_lower
