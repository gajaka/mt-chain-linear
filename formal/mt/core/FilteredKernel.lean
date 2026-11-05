module

public import Filtering
public import ChainKernel
public import Intertwining
public import RefreshDensity

@[expose] public section

/-!
The actual finite prefix process and its concrete completion matrix.
Good raw states and Good observations are each collapsed to one terminal point.
No intertwining identity is postulated in these definitions.
-/

set_option autoImplicit false

namespace MTChainFormal
namespace Filtering

open scoped BigOperators

abbrev ActivePrefix (n : ℕ) := {q : PrefixDatum n // ValidDatum q}

noncomputable instance activePrefixFintype (n : ℕ) : Fintype (ActivePrefix n) :=
  Fintype.ofFinite _

abbrev ObservedState (n : ℕ) := Option (ActivePrefix n)

noncomputable def observe {n : ℕ} (s : ChainState n) : ObservedState n :=
  match h : observeRaw s with
  | none => none
  | some q => some ⟨q, observeRaw_valid s q h⟩

theorem observe_eq_some_iff {n : ℕ} (s : ChainState n) (q : ActivePrefix n) :
    observe s = some q ↔ observeRaw s = some q.val := by
  classical
  unfold observe
  split
  next h => simp [h]
  next p h => simp [h, Subtype.ext_iff]

theorem observe_eq_none_iff {n : ℕ} (s : ChainState n) :
    observe s = none ↔ firstFailure s = none := by
  classical
  have hraw : observe s = none ↔ observeRaw s = none := by
    unfold observe
    split <;> simp_all
  rw [hraw]
  cases h : firstFailure s <;> simp [observeRaw, h]

theorem observe_some_of_completion {n : ℕ} (q : ActivePrefix n) (s : ChainState n)
    (hs : rawCompletion q.val s ≠ 0) : observe s = some q :=
  (observe_eq_some_iff s q).mpr (rawCompletion_support q.val q.property s hs)

noncomputable def completionWeight {n : ℕ} : ObservedState n → KilledState n → ℝ
  | none, a => if a = none then 1 else 0
  | some q, a => ∑ s, if kill s = a then rawCompletion q.val s else 0

theorem completionWeight_nonneg {n : ℕ} (q : ObservedState n) (a : KilledState n) :
    0 ≤ completionWeight q a := by
  classical
  cases q with
  | none => simp only [completionWeight]; split_ifs <;> norm_num
  | some q =>
    apply Finset.sum_nonneg
    intro s _
    split_ifs
    · exact rawCompletion_nonneg q.val s
    · norm_num

theorem completionWeight_sum {n : ℕ} (q : ObservedState n) :
    ∑ a, completionWeight q a = 1 := by
  classical
  cases q with
  | none => simp [completionWeight]
  | some q =>
    simp only [completionWeight]
    rw [Finset.sum_comm]
    simpa using rawCompletion_sum q.val

@[simp] theorem completionWeight_none {n : ℕ} (a : KilledState n) :
    completionWeight (none : ObservedState n) a = if a = none then 1 else 0 := rfl

@[simp] theorem completionWeight_some_some {n : ℕ} (q : ActivePrefix n)
    (a : ActiveState n) : completionWeight (some q) (some a) = rawCompletion q.val a.val := by
  classical
  simp [completionWeight, kill_eq_some_iff]

@[simp] theorem completionWeight_some_none {n : ℕ} (q : ActivePrefix n) :
    completionWeight (some q) (none : KilledState n) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro s _
  split_ifs with hkill
  · by_contra hne
    have hobs := rawCompletion_support q.val q.property s hne
    have hfirst : firstFailure s = none :=
      (no_failure_iff s).mpr ((kill_eq_none_iff s).mp hkill)
    simp [observeRaw, hfirst] at hobs
  · rfl

theorem completionWeight_expect {n : ℕ} (q : ActivePrefix n) (f : KilledState n → ℝ) :
    (∑ a, completionWeight (some q) a * f a) =
      ∑ s, rawCompletion q.val s * f (kill s) := by
  classical
  simp only [completionWeight, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  simp

noncomputable def postDensity {n : ℕ} (q : ActivePrefix n) (s : ChainState n) : ℝ :=
  ProductFiltering.density (postWeight q.val) (toCoords s)

theorem postDensity_nonneg {n : ℕ} (q : ActivePrefix n) (s : ChainState n) :
    0 ≤ postDensity q s := by
  unfold postDensity ProductFiltering.density
  apply Finset.prod_nonneg
  intro c _
  exact postWeight_nonneg q.val c (toCoords s c)

theorem postDensity_sum {n : ℕ} (q : ActivePrefix n) : ∑ s, postDensity q s = 1 := by
  classical
  calc
    _ = ∑ x, ProductFiltering.density (postWeight q.val) x := (coordinateEquiv n).sum_comp _
    _ = 1 := ProductFiltering.density_sum _ (postWeight_sum q.val)

noncomputable def observedWeight {n : ℕ} : ObservedState n → ObservedState n → ℝ
  | none, p => if p = none then 1 else 0
  | some q, p => ∑ s, if observe s = p then postDensity q s else 0

theorem observedWeight_nonneg {n : ℕ} (q p : ObservedState n) :
    0 ≤ observedWeight q p := by
  classical
  cases q with
  | none => simp only [observedWeight]; split_ifs <;> norm_num
  | some q =>
    apply Finset.sum_nonneg
    intro s _
    split_ifs
    · exact postDensity_nonneg q s
    · norm_num

theorem observedWeight_sum {n : ℕ} (q : ObservedState n) :
    ∑ p, observedWeight q p = 1 := by
  classical
  cases q with
  | none => simp [observedWeight]
  | some q =>
    simp only [observedWeight]
    rw [Finset.sum_comm]
    simpa using postDensity_sum q

noncomputable def observedKernel (n : ℕ) : FiniteKernel (ObservedState n) where
  weight := observedWeight
  nonneg := observedWeight_nonneg
  sum_eq_one := observedWeight_sum

@[simp] theorem observedWeight_none {n : ℕ} (p : ObservedState n) :
    observedWeight (none : ObservedState n) p = if p = none then 1 else 0 := rfl

theorem observedWeight_some_some {n : ℕ} (q p : ActivePrefix n) :
    observedWeight (some q) (some p) = postPrefixMass q.val p.val := by
  classical
  simp only [observedWeight, observe_eq_some_iff]
  exact post_observation_mass q.val p.val p.property

theorem expect_observedKernel {n : ℕ} (q : ActivePrefix n) (f : ObservedState n → ℝ) :
    expect (observedKernel n) f (some q) =
      ∑ s, postDensity q s * f (observe s) := by
  classical
  unfold expect observedKernel observedWeight
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  simp

theorem observe_active_ne_none {n : ℕ} (a : ActiveState n) : observe a.val ≠ none := by
  intro h
  have hnone := (observe_eq_none_iff a.val).mp h
  rw [activeSelected_firstFailure a] at hnone
  simp at hnone

theorem reconstruction_at_active {n : ℕ} (mass : ActivePrefix n → ℝ)
    (fullDensity : ChainState n → ℝ)
    (hfactor : ∀ p : ActivePrefix n, ∀ s,
      (if observeRaw s = some p.val then fullDensity s else 0) =
        mass p * rawCompletion p.val s) (a : ActiveState n) :
    (∑ p : ActivePrefix n, mass p * rawCompletion p.val a.val) = fullDensity a.val := by
  classical
  cases hobs : observe a.val with
  | none => exact (observe_active_ne_none a hobs).elim
  | some p =>
    calc
      _ = mass p * rawCompletion p.val a.val := by
        apply Finset.sum_eq_single p
        · intro b _ hbp
          by_cases hz : rawCompletion b.val a.val = 0
          · simp [hz]
          · have hb := observe_some_of_completion b a.val hz
            have heq : b = p := Option.some.inj (hb.symm.trans hobs)
            exact (hbp heq).elim
        · intro hp
          exact (hp (Finset.mem_univ p)).elim
      _ = fullDensity a.val := by
        have hraw := (observe_eq_some_iff a.val p).mp hobs
        simpa [hraw] using (hfactor p a.val).symm

theorem postDensity_reconstruction {n : ℕ} (q : ActivePrefix n) (a : ActiveState n) :
    (∑ p : ActivePrefix n, postPrefixMass q.val p.val * rawCompletion p.val a.val) =
      postDensity q a.val :=
  reconstruction_at_active (fun p => postPrefixMass q.val p.val) (postDensity q)
    (fun p s => post_observation_factor q.val p.val q.property p.property s) a

theorem completion_after_observed_at_active {n : ℕ} (q : ActivePrefix n) (a : ActiveState n) :
    (∑ p : ObservedState n, observedWeight (some q) p * completionWeight p (some a)) =
      postDensity q a.val := by
  classical
  simp only [Fintype.sum_option, completionWeight_none, Option.some_ne_none, ite_false,
    mul_zero, zero_add, completionWeight_some_some, observedWeight_some_some]
  exact postDensity_reconstruction q a

noncomputable def initialObserved {n : ℕ} (q : ObservedState n) : ℝ :=
  ∑ s, if observe s = q then initialFull s else 0

theorem initialObserved_nonneg {n : ℕ} (q : ObservedState n) :
    0 ≤ initialObserved q := by
  classical
  apply Finset.sum_nonneg
  intro s _
  split_ifs
  · exact initialFull_nonneg s
  · norm_num

theorem initialObserved_sum (n : ℕ) : ∑ q : ObservedState n, initialObserved q = 1 := by
  classical
  unfold initialObserved
  rw [Finset.sum_comm]
  simpa using initialFull_sum n

theorem initialObserved_some {n : ℕ} (q : ActivePrefix n) :
    initialObserved (some q) = initialPrefixMass q.val := by
  classical
  unfold initialObserved
  simp only [observe_eq_some_iff]
  have hinitial (s : ChainState n) : initialFull s = rawInitialDensity s :=
    (rawInitialDensity_uniform s).symm
  simp_rw [hinitial]
  exact initial_observation_mass q.val q.property

theorem initial_reconstruction_at_active {n : ℕ} (a : ActiveState n) :
    (∑ q : ObservedState n, initialObserved q * completionWeight q (some a)) = initialFull a.val := by
  classical
  simp only [Fintype.sum_option, completionWeight_none, Option.some_ne_none, ite_false,
    mul_zero, zero_add, completionWeight_some_some, initialObserved_some]
  have h := reconstruction_at_active (fun p : ActivePrefix n => initialPrefixMass p.val)
    rawInitialDensity (fun p s => initial_cylinder_factor p.val p.property s) a
  simpa only [rawInitialDensity_uniform, initialFull] using h

theorem option_law_ext {A : Type*} [Fintype A] (μ ν : Option A → ℝ)
    (hμ : ∑ a, μ a = 1) (hν : ∑ a, ν a = 1)
    (hsome : ∀ a, μ (some a) = ν (some a)) : μ = ν := by
  funext a
  cases a with
  | some a => exact hsome a
  | none =>
    simp only [Fintype.sum_option] at hμ hν
    have hsum : (∑ a, μ (some a)) = ∑ a, ν (some a) := by
      apply Finset.sum_congr rfl
      intro a _
      exact hsome a
    rw [hsum] at hμ
    linarith

theorem initialLaw_some {n : ℕ} (a : ActiveState n) :
    initialLaw (some a) = initialFull a.val := by
  classical
  simp [initialLaw, kill_eq_some_iff]

theorem initialLaw_completion (n : ℕ) (a : KilledState n) :
    initialLaw a = pushedLaw initialObserved completionWeight a := by
  have hright :
      (∑ a : KilledState n, pushedLaw initialObserved completionWeight a) = 1 :=
    pushedLaw_sum initialObserved completionWeight (initialObserved_sum n) completionWeight_sum
  have heq := option_law_ext (initialLaw : KilledState n → ℝ)
    (pushedLaw initialObserved completionWeight) (initialLaw_sum n) hright (fun a => by
      rw [initialLaw_some]
      exact (initial_reconstruction_at_active a).symm)
  exact congrFun heq a

def observedActive {n : ℕ} : ObservedState n → Bool
  | none => false
  | some _ => true

theorem completion_active_cost {n : ℕ} (q : ObservedState n) :
    activeCost observedActive q = disaggregate completionWeight (activeCost killedActive) q := by
  classical
  symm
  apply disaggregate_eq_of_support completionWeight (activeCost killedActive)
    (activeCost observedActive) completionWeight_sum
  intro p a h
  cases p <;> cases a <;> simp_all [activeCost, killedActive, observedActive]

theorem observedKernel_inactive_absorbing (n : ℕ) :
    InactiveAbsorbing (observedKernel n) observedActive := by
  classical
  intro p q hp hq
  cases p <;> cases q <;>
    simp_all [observedActive, observedKernel, observedWeight]

theorem firstFailure_of_completion {n : ℕ} (q : ActivePrefix n) (s : ChainState n)
    (hs : rawCompletion q.val s ≠ 0) : firstFailure s = some q.val.1 := by
  have hobs := rawCompletion_support q.val q.property s hs
  have hagree := (observeRaw_fiber q.val q.property s).mp hobs
  exact firstFailure_eq_of_agrees q.val.2 s q.val.1 q.property.1 _ le_rfl hagree

theorem chainWeight_kill_selected {n : ℕ} (s : ChainState n) (i : Fin n)
    (hi : firstFailure s = some i) (a : ActiveState n) :
    chainWeight (kill s) (some a) =
      drawAverage (fun u => if replace s i u = a.val then (1 : ℝ) else 0) := by
  classical
  have hbad : (badIndices s).Nonempty :=
    ⟨i, (mem_badIndices s i).mpr (selected_failed s i hi)⟩
  let source : ActiveState n := ⟨s, hbad⟩
  have hkill : kill s = some source := kill_of_bad source
  have hselected : activeSelected source = i :=
    Option.some.inj ((activeSelected_firstFailure source).symm.trans hi)
  rw [hkill]
  simp only [chainWeight, killedStep_some, hselected, kill_eq_some_iff, drawAverage]
  apply Finset.sum_congr rfl
  intro u _
  by_cases heq : replace s i u = a.val <;> simp [source, heq]

theorem completion_chain_at_active {n : ℕ} (q : ActivePrefix n) (a : ActiveState n) :
    (∑ u : KilledState n, completionWeight (some q) u * chainWeight u (some a)) =
      ∑ s : ChainState n, rawCompletion q.val s *
        drawAverage (fun u => if replace s q.val.1 u = a.val then (1 : ℝ) else 0) := by
  rw [completionWeight_expect]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : rawCompletion q.val s = 0
  · simp [hs]
  · rw [chainWeight_kill_selected s q.val.1 (firstFailure_of_completion q s hs) a]

noncomputable def killedObservation {n : ℕ} : KilledState n → ObservedState n
  | none => none
  | some a => observe a.val

theorem completionWeight_support {n : ℕ} (q : ObservedState n) (a : KilledState n)
    (h : completionWeight q a ≠ 0) : killedObservation a = q := by
  classical
  cases q with
  | none =>
    cases a with
    | none => rfl
    | some a => simp at h
  | some q =>
    cases a with
    | none => simp at h
    | some a => exact observe_some_of_completion q a.val (by simpa using h)

theorem actual_intertwining_all (n : ℕ) :
    Intertwines (observedKernel n) (chainKernel n) completionWeight := by
  classical
  intro q a
  change (∑ u, completionWeight q u * chainWeight u a) =
    ∑ p, observedWeight q p * completionWeight p a
  have hleft :
      (∑ a : KilledState n, ∑ u, completionWeight q u * chainWeight u a) = 1 := by
    exact pushedLaw_sum (completionWeight q) (chainKernel n).weight
      (completionWeight_sum q) (chainKernel n).sum_eq_one
  have hright :
      (∑ a : KilledState n, ∑ p, observedWeight q p * completionWeight p a) = 1 := by
    exact pushedLaw_sum (observedWeight q) completionWeight
      (observedWeight_sum q) completionWeight_sum
  have hactive (b : ActiveState n) :
      (∑ u, completionWeight q u * chainWeight u (some b)) =
        ∑ p, observedWeight q p * completionWeight p (some b) := by
    cases q with
    | none => simp [chainWeight_none]
    | some q =>
      calc
        _ = ∑ s, rawCompletion q.val s * drawAverage
            (fun u => if replace s q.val.1 u = b.val then (1 : ℝ) else 0) :=
          completion_chain_at_active q b
        _ = postDensity q b.val := raw_replace_density q.val b.val
        _ = _ := (completion_after_observed_at_active q b).symm
  exact congrFun (option_law_ext _ _ hleft hright hactive) a

/-- The model-domain wrapper used by the all-n work theorem. The matrix
    identity itself is proved for every n, including the terminal-only case. -/
theorem actual_intertwining {n : ℕ} (_hn : 2 ≤ n) :
    Intertwines (observedKernel n) (chainKernel n) completionWeight :=
  actual_intertwining_all n

theorem expect_observedKernel_replace {n : ℕ} (q : ActivePrefix n)
    (f : ObservedState n → ℝ) :
    expect (observedKernel n) f (some q) =
      ∑ s, rawCompletion q.val s * drawAverage (fun u => f (observe (replace s q.val.1 u))) := by
  rw [expect_observedKernel]
  exact (raw_replace_expectation q.val (fun s => f (observe s))).symm

end Filtering
end MTChainFormal
