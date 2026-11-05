module

public import FilteredKernel

@[expose] public section

/-!
Finite-history filtering without conditioning on zero-mass events.
The joint law is built by actual transition and observation restriction at
each step. Its factorization follows from a completion matrix supported on
observation fibers and an intertwining identity; the concrete chain instance
uses the separately proved identity rather than assuming it.
-/

set_option autoImplicit false

namespace MTChainFormal
namespace HistoryFiltering

open scoped BigOperators

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]

noncomputable def restrict (observe : B → A) (μ : B → ℝ) (q : A) (b : B) : ℝ :=
  if observe b = q then μ b else 0

noncomputable def restrictedStep (P : FiniteKernel B) (observe : B → A)
    (μ : B → ℝ) (q : A) (b : B) : ℝ :=
  if observe b = q then ∑ a, μ a * P.weight a b else 0

noncomputable def followRaw (P : FiniteKernel B) (observe : B → A) :
    (B → ℝ) → List A → B → ℝ
  | μ, [] => μ
  | μ, q :: qs => followRaw P observe (restrictedStep P observe μ q) qs

def lastObservation : A → List A → A
  | q, [] => q
  | _, p :: ps => lastObservation p ps

noncomputable def pathMass (Q : FiniteKernel A) : A → List A → ℝ
  | _, [] => 1
  | q, p :: ps => Q.weight q p * pathMass Q p ps

omit [Fintype A] in
theorem restrictedStep_scale (P : FiniteKernel B) (observe : B → A)
    (μ : B → ℝ) (c : ℝ) (q : A) :
    restrictedStep P observe (fun b => c * μ b) q =
      fun b => c * restrictedStep P observe μ q b := by
  funext b
  unfold restrictedStep
  split_ifs
  · simp_rw [mul_assoc]
    rw [Finset.mul_sum]
  · ring

omit [Fintype A] in
theorem followRaw_scale (P : FiniteKernel B) (observe : B → A)
    (μ : B → ℝ) (c : ℝ) (qs : List A) (b : B) :
    followRaw P observe (fun a => c * μ a) qs b = c * followRaw P observe μ qs b := by
  induction qs generalizing μ with
  | nil => rfl
  | cons q qs ih =>
    simp only [followRaw, restrictedStep_scale]
    exact ih (restrictedStep P observe μ q)

omit [Fintype B] in
theorem restrict_mixture (observe : B → A) (D : A → B → ℝ)
    (hsupport : ∀ q b, D q b ≠ 0 → observe b = q) (mass : A → ℝ) (q : A) (b : B) :
    (if observe b = q then ∑ p, mass p * D p b else 0) = mass q * D q b := by
  classical
  by_cases hobs : observe b = q
  · rw [ite_eq_left hobs]
    apply Finset.sum_eq_single q
    · intro p _ hpq
      by_cases hz : D p b = 0
      · simp [hz]
      · have heq : p = q := (hsupport p b hz).symm.trans hobs
        exact (hpq heq).elim
    · intro hq
      exact (hq (Finset.mem_univ q)).elim
  · have hz : D q b = 0 := by
      by_contra hne
      exact hobs (hsupport q b hne)
    simp [hobs, hz]

theorem restrictedStep_completion (Q : FiniteKernel A) (P : FiniteKernel B)
    (observe : B → A) (D : A → B → ℝ)
    (hsupport : ∀ q b, D q b ≠ 0 → observe b = q)
    (hDP : Intertwines Q P D) (q p : A) (b : B) :
    restrictedStep P observe (D q) p b = Q.weight q p * D p b := by
  unfold restrictedStep
  rw [hDP q b]
  exact restrict_mixture observe D hsupport (Q.weight q) p b

theorem history_factorization (Q : FiniteKernel A) (P : FiniteKernel B)
    (observe : B → A) (D : A → B → ℝ)
    (hsupport : ∀ q b, D q b ≠ 0 → observe b = q)
    (hDP : Intertwines Q P D) (q : A) (qs : List A) (b : B) :
    followRaw P observe (D q) qs b =
      pathMass Q q qs * D (lastObservation q qs) b := by
  induction qs generalizing q with
  | nil => simp [followRaw, pathMass, lastObservation]
  | cons p ps ih =>
    simp only [followRaw]
    have hstep : restrictedStep P observe (D q) p = fun b => Q.weight q p * D p b := by
      funext a
      exact restrictedStep_completion Q P observe D hsupport hDP q p a
    rw [hstep, followRaw_scale, ih p]
    simp only [pathMass, lastObservation, mul_assoc]

omit [Fintype B] in
theorem initial_restriction (observe : B → A) (D : A → B → ℝ)
    (hsupport : ∀ q b, D q b ≠ 0 → observe b = q)
    (ν : A → ℝ) (μ : B → ℝ) (hlaw : ∀ b, μ b = pushedLaw ν D b)
    (q : A) (b : B) : restrict observe μ q b = ν q * D q b := by
  unfold restrict
  rw [hlaw b]
  exact restrict_mixture observe D hsupport ν q b

theorem initial_history_factorization (Q : FiniteKernel A) (P : FiniteKernel B)
    (observe : B → A) (D : A → B → ℝ)
    (hsupport : ∀ q b, D q b ≠ 0 → observe b = q)
    (hDP : Intertwines Q P D) (ν : A → ℝ) (μ : B → ℝ)
    (hlaw : ∀ b, μ b = pushedLaw ν D b) (q : A) (qs : List A) (b : B) :
    followRaw P observe (restrict observe μ q) qs b =
      (ν q * pathMass Q q qs) * D (lastObservation q qs) b := by
  have hstart : restrict observe μ q = fun b => ν q * D q b := by
    funext a
    exact initial_restriction observe D hsupport ν μ hlaw q a
  rw [hstart, followRaw_scale, history_factorization Q P observe D hsupport hDP]
  ring

theorem initial_history_total_mass (Q : FiniteKernel A) (P : FiniteKernel B)
    (observe : B → A) (D : A → B → ℝ)
    (hsupport : ∀ q b, D q b ≠ 0 → observe b = q)
    (hDP : Intertwines Q P D) (hnorm : ∀ q, ∑ b, D q b = 1)
    (ν : A → ℝ) (μ : B → ℝ) (hlaw : ∀ b, μ b = pushedLaw ν D b)
    (q : A) (qs : List A) :
    (∑ b, followRaw P observe (restrict observe μ q) qs b) = ν q * pathMass Q q qs := by
  simp_rw [initial_history_factorization Q P observe D hsupport hDP ν μ hlaw]
  rw [← Finset.mul_sum, hnorm, mul_one]

theorem initial_history_conditional (Q : FiniteKernel A) (P : FiniteKernel B)
    (observe : B → A) (D : A → B → ℝ)
    (hsupport : ∀ q b, D q b ≠ 0 → observe b = q)
    (hDP : Intertwines Q P D) (ν : A → ℝ) (μ : B → ℝ)
    (hlaw : ∀ b, μ b = pushedLaw ν D b) (q : A) (qs : List A) (b : B)
    (hpositive : ν q * pathMass Q q qs ≠ 0) :
    followRaw P observe (restrict observe μ q) qs b /
        (ν q * pathMass Q q qs) = D (lastObservation q qs) b := by
  rw [initial_history_factorization Q P observe D hsupport hDP ν μ hlaw]
  exact mul_div_cancel_left₀ _ hpositive

end HistoryFiltering

namespace Filtering

open scoped BigOperators

/-- The joint endpoint law after an arbitrary finite history of actual
    prefix observations. The equality includes histories of zero mass. -/
theorem actual_history_factorization {n : ℕ} (hn : 2 ≤ n)
    (q : ObservedState n) (qs : List (ObservedState n)) (a : KilledState n) :
    HistoryFiltering.followRaw (chainKernel n) killedObservation
        (HistoryFiltering.restrict killedObservation initialLaw q) qs a =
      (initialObserved q * HistoryFiltering.pathMass (observedKernel n) q qs) *
        completionWeight (HistoryFiltering.lastObservation q qs) a :=
  HistoryFiltering.initial_history_factorization (observedKernel n) (chainKernel n)
    killedObservation completionWeight completionWeight_support (actual_intertwining hn)
    initialObserved initialLaw (initialLaw_completion n) q qs a

/-- Summing the concrete raw endpoint law gives exactly the observed path
    mass, including after terminal observations. -/
theorem actual_history_mass {n : ℕ} (hn : 2 ≤ n)
    (q : ObservedState n) (qs : List (ObservedState n)) :
    (∑ a : KilledState n,
      HistoryFiltering.followRaw (chainKernel n) killedObservation
        (HistoryFiltering.restrict killedObservation initialLaw q) qs a) =
      initialObserved q * HistoryFiltering.pathMass (observedKernel n) q qs :=
  HistoryFiltering.initial_history_total_mass (observedKernel n) (chainKernel n)
    killedObservation completionWeight completionWeight_support (actual_intertwining hn)
    completionWeight_sum initialObserved initialLaw (initialLaw_completion n) q qs

theorem actual_history_conditional {n : ℕ} (hn : 2 ≤ n)
    (q : ObservedState n) (qs : List (ObservedState n)) (a : KilledState n)
    (hpositive : initialObserved q * HistoryFiltering.pathMass (observedKernel n) q qs ≠ 0) :
    HistoryFiltering.followRaw (chainKernel n) killedObservation
        (HistoryFiltering.restrict killedObservation initialLaw q) qs a /
      (initialObserved q * HistoryFiltering.pathMass (observedKernel n) q qs) =
      completionWeight (HistoryFiltering.lastObservation q qs) a :=
  HistoryFiltering.initial_history_conditional (observedKernel n) (chainKernel n)
    killedObservation completionWeight completionWeight_support (actual_intertwining hn)
    initialObserved initialLaw (initialLaw_completion n) q qs a hpositive

/-- After every positive-mass finite observation history ending actively,
    the conditional raw law is the constructed fresh product completion.
    No assertion is made about individual Good microstates. -/
theorem actual_history_fresh_tail {n : ℕ} (hn : 2 ≤ n)
    (q : ObservedState n) (qs : List (ObservedState n)) (p : ActivePrefix n)
    (hlast : HistoryFiltering.lastObservation q qs = some p) (a : ActiveState n)
    (hpositive : initialObserved q * HistoryFiltering.pathMass (observedKernel n) q qs ≠ 0) :
    HistoryFiltering.followRaw (chainKernel n) killedObservation
        (HistoryFiltering.restrict killedObservation initialLaw q) qs (some a) /
      (initialObserved q * HistoryFiltering.pathMass (observedKernel n) q qs) =
      rawCompletion p.val a.val := by
  rw [actual_history_conditional hn q qs (some a) hpositive, hlast,
    completionWeight_some_some]

end Filtering
end MTChainFormal
