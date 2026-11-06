module

public import BiasedDefinitions
public import RefreshDensity

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace MTChainFormal.BiasedResampling

open scoped BigOperators

theorem thresholdWeight_nonneg (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (a : Fin 3) : 0 ≤ thresholdWeight p a := by
  unfold thresholdWeight
  split_ifs
  · exact hp0
  · positivity

theorem thresholdWeight_sum (p : ℝ) : ∑ a, thresholdWeight p a = 1 := by
  norm_num [thresholdWeight, Fin.sum_univ_succ]
  ring

theorem drawWeight_nonneg (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (u : Draw) : 0 ≤ drawWeight p u := by
  unfold drawWeight
  exact mul_nonneg (mul_nonneg (thresholdWeight_nonneg p hp0 hp1 _)
    (thresholdWeight_nonneg p hp0 hp1 _)) (by norm_num)

theorem drawWeight_sum (p : ℝ) : ∑ u, drawWeight p u = 1 := by
  norm_num [drawWeight, thresholdWeight, Fintype.sum_prod_type, Fin.sum_univ_succ]
  ring

theorem average_const (p a : ℝ) : average p (fun _ => a) = a := by
  rw [average, ← Finset.sum_mul, drawWeight_sum, one_mul]

theorem average_nonneg (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f : Draw → ℝ) (hf : ∀ u, 0 ≤ f u) : 0 ≤ average p f := by
  exact Finset.sum_nonneg (fun u _ => mul_nonneg
    (drawWeight_nonneg p hp0 hp1 u) (hf u))

theorem average_mono (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {f g : Draw → ℝ} (hfg : ∀ u, f u ≤ g u) : average p f ≤ average p g := by
  exact Finset.sum_le_sum (fun u _ => mul_le_mul_of_nonneg_left (hfg u)
    (drawWeight_nonneg p hp0 hp1 u))

theorem average_congr (p : ℝ) {f g : Draw → ℝ} (hfg : ∀ u, f u = g u) :
    average p f = average p g := by
  unfold average
  apply Finset.sum_congr rfl
  intro u _
  rw [hfg u]

theorem average_add (p : ℝ) (f g : Draw → ℝ) :
    average p (fun u => f u + g u) = average p f + average p g := by
  simp only [average, mul_add, Finset.sum_add_distrib]

theorem average_sub (p : ℝ) (f g : Draw → ℝ) :
    average p (fun u => f u - g u) = average p f - average p g := by
  simp only [average, mul_sub, Finset.sum_sub_distrib]

theorem average_mul_const (p : ℝ) (f : Draw → ℝ) (a : ℝ) :
    average p (fun u => f u * a) = average p f * a := by
  unfold average
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro u _
  ring

theorem average_const_mul (p a : ℝ) (f : Draw → ℝ) :
    average p (fun u => a * f u) = a * average p f := by
  simp only [average, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  ring

theorem average_incoming_thresholdCost (p : ℝ) :
    average p (fun u => thresholdCost u.1) = 6 * (1 - p) := by
  norm_num [average, drawWeight, thresholdWeight, thresholdCost,
    Fintype.sum_prod_type, Fin.sum_univ_succ]
  ring

theorem average_outgoing_thresholdCost (p : ℝ) :
    average p (fun u => thresholdCost u.2.1) = 6 * (1 - p) := by
  norm_num [average, drawWeight, thresholdWeight, thresholdCost,
    Fintype.sum_prod_type, Fin.sum_univ_succ]
  ring

theorem average_tacticCost (p : ℝ) :
    average p (fun u => tacticCost u.2.2) = 1 := by
  norm_num [average, drawWeight, thresholdWeight, tacticCost,
    Fintype.sum_prod_type, Fin.sum_univ_succ]
  ring

theorem thresholdCost_nonneg (a : Fin 3) : 0 ≤ thresholdCost a := by
  unfold thresholdCost
  split_ifs <;> norm_num

theorem thresholdCost_le (a : Fin 3) : thresholdCost a ≤ 6 := by
  unfold thresholdCost
  split_ifs <;> norm_num

theorem tacticCost_nonneg (r : Fin 4) : 0 ≤ tacticCost r := by
  unfold tacticCost
  split_ifs <;> norm_num

theorem tacticCost_le (r : Fin 4) : tacticCost r ≤ 4 := by
  unfold tacticCost
  split_ifs <;> norm_num

theorem potential_nonneg {n : ℕ} (s : ChainState n) : 0 ≤ potential s := by
  exact add_nonneg (Finset.sum_nonneg (fun _ _ => thresholdCost_nonneg _))
    (Finset.sum_nonneg (fun _ _ => tacticCost_nonneg _))

theorem potential_eq_counts {n : ℕ} (s : ChainState n) :
    potential s = 6 * (nonMaxCount s : ℝ) + 4 * (weakCount s : ℝ) := by
  classical
  have ht : (∑ j, thresholdCost (s.values j)) = 6 * (nonMaxCount s : ℝ) := by
    unfold thresholdCost nonMaxCount
    rw [Finset.card_filter]
    simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp_all
  have hr : (∑ i, tacticCost (s.tactic i)) = 4 * (weakCount s : ℝ) := by
    unfold tacticCost weakCount
    rw [Finset.card_filter]
    simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp_all
  exact congrArg₂ (· + ·) ht hr

theorem potential_le {n : ℕ} (hn : 2 ≤ n) (s : ChainState n) :
    potential s ≤ 10 * (n : ℝ) - 6 := by
  have ht : (∑ j, thresholdCost (s.values j)) ≤ 6 * (n - 1 : ℕ) := by
    calc
      _ ≤ ∑ _j : Fin (n - 1), (6 : ℝ) :=
        Finset.sum_le_sum (fun _ _ => thresholdCost_le _)
      _ = _ := by simp [mul_comm]
  have hr : (∑ i, tacticCost (s.tactic i)) ≤ 4 * (n : ℝ) := by
    calc
      _ ≤ ∑ _i : Fin n, (4 : ℝ) :=
        Finset.sum_le_sum (fun _ _ => tacticCost_le _)
      _ = _ := by simp [mul_comm]
  have hn1 : 1 ≤ n := by omega
  rw [Nat.cast_sub hn1, Nat.cast_one] at ht
  unfold potential
  linarith

theorem coordinateWeight_nonneg {n : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (c : Filtering.Coord n) (x : Filtering.Alphabet c) :
    0 ≤ coordinateWeight p c x := by
  cases c with
  | inl j => exact thresholdWeight_nonneg p hp0 hp1 x
  | inr i => norm_num [coordinateWeight]

theorem coordinateWeight_sum {n : ℕ} (p : ℝ) (c : Filtering.Coord n) :
    ∑ x, coordinateWeight p c x = 1 := by
  cases c with
  | inl j => exact thresholdWeight_sum p
  | inr i =>
      change (∑ _x : Fin 4, (1 / 4 : ℝ)) = 1
      norm_num

theorem initialWeight_nonneg {n : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (s : ChainState n) : 0 ≤ initialWeight p s := by
  unfold initialWeight ProductFiltering.density
  exact Finset.prod_nonneg (fun c _ => coordinateWeight_nonneg p hp0 hp1 c _)

theorem initialWeight_sum (n : ℕ) (p : ℝ) : ∑ s : ChainState n, initialWeight p s = 1 := by
  classical
  calc
    _ = ∑ x, ProductFiltering.density (coordinateWeight p) x :=
      (Filtering.coordinateEquiv n).sum_comp _
    _ = 1 := ProductFiltering.density_sum _ (coordinateWeight_sum p)

section ProductMoments

variable {ι : Type*} {κ : ι → Type*}
variable [Fintype ι] [DecidableEq ι]
variable [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

theorem density_coordinate_mean (w : ∀ i, κ i → ℝ)
    (hw : ∀ i, ∑ x, w i x = 1) (i : ι) (f : κ i → ℝ) :
    (∑ state, ProductFiltering.density w state * f (state i)) = ∑ x, w i x * f x := by
  classical
  have h := RefreshDensity.update_density_expectation w i (w i)
    (fun state => f (state i)) hw
  simp only [Function.update_self] at h
  have hu : Function.update w i (w i) = w := Function.update_eq_self i w
  rw [hu] at h
  rw [← Finset.sum_mul, ProductFiltering.density_sum w hw, one_mul] at h
  exact h.symm

end ProductMoments

theorem initial_coordinate_mean {n : ℕ} (p : ℝ) (c : Filtering.Coord n)
    (f : Filtering.Alphabet c → ℝ) :
    (∑ s : ChainState n, initialWeight p s * f (Filtering.toCoords s c)) =
      ∑ x, coordinateWeight p c x * f x := by
  classical
  calc
    _ = ∑ x, ProductFiltering.density (coordinateWeight p) x * f (x c) :=
      (Filtering.coordinateEquiv n).sum_comp _
    _ = _ := density_coordinate_mean _ (coordinateWeight_sum p) c f

theorem initial_thresholdCost {n : ℕ} (p : ℝ) (j : Fin (n - 1)) :
    (∑ s : ChainState n, initialWeight p s * thresholdCost (s.values j)) =
      6 * (1 - p) := by
  have h := initial_coordinate_mean p (Sum.inl j) thresholdCost
  change (∑ s : ChainState n, initialWeight p s * thresholdCost (s.values j)) =
    ∑ x, thresholdWeight p x * thresholdCost x at h
  rw [h]
  norm_num [thresholdWeight, thresholdCost, Fin.sum_univ_succ]
  ring

theorem initial_tacticCost {n : ℕ} (p : ℝ) (i : Fin n) :
    (∑ s : ChainState n, initialWeight p s * tacticCost (s.tactic i)) = 1 := by
  have h := initial_coordinate_mean p (Sum.inr i) tacticCost
  change (∑ s : ChainState n, initialWeight p s * tacticCost (s.tactic i)) =
    ∑ x : Fin 4, (1 / 4 : ℝ) * tacticCost x at h
  rw [h]
  norm_num [tacticCost, Fin.sum_univ_succ]

theorem initial_potential_mean (n : ℕ) (p : ℝ) :
    (∑ s : ChainState n, initialWeight p s * potential s) =
      6 * (n - 1 : ℕ) * (1 - p) + n := by
  classical
  have ht : (∑ s : ChainState n, initialWeight p s *
      ∑ j, thresholdCost (s.values j)) = (n - 1 : ℕ) * (6 * (1 - p)) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [initial_thresholdCost]
    simp
  have hr : (∑ s : ChainState n, initialWeight p s *
      ∑ i, tacticCost (s.tactic i)) = (n : ℝ) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [initial_tacticCost]
    simp
  simp only [potential, mul_add, Finset.sum_add_distrib]
  rw [ht, hr]
  ring

theorem initial_static_potential_mean {n : ℕ} (hn : 2 ≤ n) :
    (∑ s : ChainState n, initialWeight (2 / 3) s * potential s) = 3 * (n : ℝ) - 2 := by
  rw [initial_potential_mean]
  have hn1 : 1 ≤ n := by omega
  rw [Nat.cast_sub hn1, Nat.cast_one]
  ring

theorem initial_uniform_potential_mean {n : ℕ} (hn : 2 ≤ n) :
    (∑ s : ChainState n, initialWeight (1 / 3) s * potential s) = 5 * (n : ℝ) - 4 := by
  rw [initial_potential_mean]
  have hn1 : 1 ≤ n := by omega
  rw [Nat.cast_sub hn1, Nat.cast_one]
  ring

theorem coordinateWeight_uniform {n : ℕ} :
    coordinateWeight (n := n) (1 / 3) = Filtering.freshWeight := by
  funext c x
  cases c with
  | inl j =>
      change thresholdWeight (1 / 3) x = (1 / 3 : ℝ)
      unfold thresholdWeight
      split_ifs <;> norm_num
  | inr i => rfl

theorem initialWeight_uniform {n : ℕ} (s : ChainState n) :
    initialWeight (1 / 3) s = initialFull s := by
  unfold initialWeight
  rw [coordinateWeight_uniform]
  exact Filtering.rawInitialDensity_uniform s

theorem average_nested (p : ℝ) (f : Draw → ℝ) :
    average p f = ∑ a : Fin 3, thresholdWeight p a *
      ∑ b : Fin 3, thresholdWeight p b * ∑ r : Fin 4, (1 / 4 : ℝ) * f (a, b, r) := by
  simp only [average, drawWeight, Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro r _
  ring

section RefreshMoments

open Filtering RefreshDensity

private theorem incoming_same_expectation {n : ℕ} (p : ℝ) (i : Fin n)
    (f : (∀ c : Coord n, Alphabet c) → ℝ) :
    (∑ x, ProductFiltering.density (coordinateWeight p) x *
      ∑ a, thresholdWeight p a * f (incomingUpdate i x a)) =
      ∑ x, ProductFiltering.density (coordinateWeight p) x * f x := by
  classical
  unfold incomingUpdate
  split_ifs with hi
  · have h := update_density_expectation (coordinateWeight p) (.inl (incomingSite i hi))
      (thresholdWeight p) f (coordinateWeight_sum p)
    have hu : Function.update (coordinateWeight p) (.inl (incomingSite i hi))
        (thresholdWeight p) = coordinateWeight p := Function.update_eq_self _ _
    rw [hu] at h
    convert h using 1
    apply Finset.sum_congr rfl
    intro x hx
    congr 1
  · simp only [← Finset.sum_mul, thresholdWeight_sum, one_mul]

private theorem outgoing_same_expectation {n : ℕ} (p : ℝ) (i : Fin n)
    (f : (∀ c : Coord n, Alphabet c) → ℝ) :
    (∑ x, ProductFiltering.density (coordinateWeight p) x *
      ∑ b, thresholdWeight p b * f (outgoingUpdate i x b)) =
      ∑ x, ProductFiltering.density (coordinateWeight p) x * f x := by
  classical
  unfold outgoingUpdate
  split_ifs with hi
  · have h := update_density_expectation (coordinateWeight p) (.inl (outgoingSite i hi))
      (thresholdWeight p) f (coordinateWeight_sum p)
    have hu : Function.update (coordinateWeight p) (.inl (outgoingSite i hi))
        (thresholdWeight p) = coordinateWeight p := Function.update_eq_self _ _
    rw [hu] at h
    convert h using 1
    apply Finset.sum_congr rfl
    intro x hx
    congr 1
  · simp only [← Finset.sum_mul, thresholdWeight_sum, one_mul]

private theorem tactic_same_expectation {n : ℕ} (p : ℝ) (i : Fin n)
    (f : (∀ c : Coord n, Alphabet c) → ℝ) :
    (∑ x, ProductFiltering.density (coordinateWeight p) x *
      ∑ r : Fin 4, (1 / 4 : ℝ) * f (tacticUpdate i x r)) =
      ∑ x, ProductFiltering.density (coordinateWeight p) x * f x := by
  classical
  have h := update_density_expectation (coordinateWeight p) (.inr i)
    (fun _ : Fin 4 => (1 / 4 : ℝ)) f (coordinateWeight_sum p)
  have hu : Function.update (coordinateWeight p) (.inr i)
      (fun _ : Fin 4 => (1 / 4 : ℝ)) = coordinateWeight p := Function.update_eq_self _ _
  simp only [tacticUpdate]
  rw [hu] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro x hx
  congr 1

/-- A fixed local refresh preserves its matching product law. No claim that
    the failure-selected process is stationary is used here. -/
theorem fixed_refresh_expectation {n : ℕ} (p : ℝ) (i : Fin n) (f : ChainState n → ℝ) :
    (∑ s, initialWeight p s * average p (fun u => f (replace s i u))) =
      ∑ s, initialWeight p s * f s := by
  classical
  let fC := fun x : ∀ c : Coord n, Alphabet c => f (fromCoords x)
  have hreplace (s : ChainState n) (u : Draw) : replace s i u =
      fromCoords (tacticUpdate i (outgoingUpdate i (incomingUpdate i (toCoords s) u.1)
        u.2.1) u.2.2) := by
    have h := congrArg fromCoords (toCoords_replace s i u)
    simpa only [fromCoords_toCoords] using h
  have hc : (∑ x, ProductFiltering.density (coordinateWeight p) x *
      ∑ a : Fin 3, thresholdWeight p a * ∑ b : Fin 3, thresholdWeight p b *
        ∑ r : Fin 4, (1 / 4 : ℝ) *
          fC (tacticUpdate i (outgoingUpdate i (incomingUpdate i x a) b) r)) =
      ∑ x, ProductFiltering.density (coordinateWeight p) x * fC x := by
    calc
      _ = ∑ x, ProductFiltering.density (coordinateWeight p) x *
          ∑ b : Fin 3, thresholdWeight p b * ∑ r : Fin 4, (1 / 4 : ℝ) *
            fC (tacticUpdate i (outgoingUpdate i x b) r) :=
        incoming_same_expectation p i
          (fun x => ∑ b : Fin 3, thresholdWeight p b * ∑ r : Fin 4, (1 / 4 : ℝ) *
            fC (tacticUpdate i (outgoingUpdate i x b) r))
      _ = ∑ x, ProductFiltering.density (coordinateWeight p) x *
          ∑ r : Fin 4, (1 / 4 : ℝ) * fC (tacticUpdate i x r) :=
        outgoing_same_expectation p i
          (fun x => ∑ r : Fin 4, (1 / 4 : ℝ) * fC (tacticUpdate i x r))
      _ = _ := tactic_same_expectation p i fC
  calc
    _ = ∑ x, ProductFiltering.density (coordinateWeight p) x *
        ∑ a : Fin 3, thresholdWeight p a * ∑ b : Fin 3, thresholdWeight p b *
          ∑ r : Fin 4, (1 / 4 : ℝ) *
            fC (tacticUpdate i (outgoingUpdate i (incomingUpdate i x a) b) r) := by
      simp_rw [average_nested, hreplace]
      exact (coordinateEquiv n).sum_comp
        (fun x => ProductFiltering.density (coordinateWeight p) x *
          ∑ a : Fin 3, thresholdWeight p a * ∑ b : Fin 3, thresholdWeight p b *
            ∑ r : Fin 4, (1 / 4 : ℝ) *
              fC (tacticUpdate i (outgoingUpdate i (incomingUpdate i x a) b) r))
    _ = ∑ x, ProductFiltering.density (coordinateWeight p) x * fC x := hc
    _ = _ := by
      have h := (coordinateEquiv n).sum_comp
        (fun x => ProductFiltering.density (coordinateWeight p) x * fC x)
      exact h.symm

end RefreshMoments

def badIndicator {n : ℕ} (s : ChainState n) (i : Fin n) : ℝ :=
  if passes s i then 0 else 1

theorem refreshed_static_failure_average {n : ℕ} (hn : 2 ≤ n)
    (s : ChainState n) (i : Fin n) :
    average (2 / 3) (fun u => badIndicator (replace s i u) i) =
      if i.val = 0 then 1 / 12 else if i.val + 1 = n then 5 / 24 else 5 / 16 := by
  by_cases hfirst : i.val = 0
  · have hinter : i.val + 1 < n := by omega
    have hp (u : Draw) : passes (replace s i u) i =
        MTChainProof.bridgePass 2 u.2.1 u.2.2 := by
      simp only [passes, hfirst, value_zero, replace_tactic_same]
      simpa only [hfirst] using congrArg
        (fun a => MTChainProof.bridgePass 2 a u.2.2) (replace_outgoing hn s i u hinter)
    simp_rw [badIndicator, hp]
    norm_num [average, drawWeight, thresholdWeight, Fintype.sum_prod_type,
      Fin.sum_univ_succ, MTChainProof.bridgePass, hfirst]
  · have hip : 0 < i.val := by omega
    by_cases hlast : i.val + 1 = n
    · have hp (u : Draw) : passes (replace s i u) i =
          MTChainProof.bridgePass u.1 0 u.2.2 := by
        simp only [passes, replace_incoming hn s i u hip, hlast,
          value_right (by omega : 0 < n), replace_tactic_same]
      simp_rw [badIndicator, hp]
      norm_num [average, drawWeight, thresholdWeight, Fintype.sum_prod_type,
        Fin.sum_univ_succ, MTChainProof.bridgePass, hfirst, hlast]
    · have hinter : i.val + 1 < n := by omega
      have hp (u : Draw) : passes (replace s i u) i =
          MTChainProof.bridgePass u.1 u.2.1 u.2.2 := by
        simp only [passes, replace_incoming hn s i u hip,
          replace_outgoing hn s i u hinter, replace_tactic_same]
      simp_rw [badIndicator, hp]
      norm_num [average, drawWeight, thresholdWeight, Fintype.sum_prod_type,
        Fin.sum_univ_succ, MTChainProof.bridgePass, hfirst, hlast]

theorem initial_static_failure_probability {n : ℕ} (hn : 2 ≤ n) (i : Fin n) :
    (∑ s : ChainState n, initialWeight (2 / 3) s * badIndicator s i) =
      if i.val = 0 then 1 / 12 else if i.val + 1 = n then 5 / 24 else 5 / 16 := by
  rw [← fixed_refresh_expectation (2 / 3) i (fun s => badIndicator s i)]
  simp_rw [refreshed_static_failure_average hn]
  rw [← Finset.sum_mul, initialWeight_sum n (2 / 3), one_mul]

theorem bad_card_eq_sum_indicator {n : ℕ} (s : ChainState n) :
    ((badIndices s).card : ℝ) = ∑ i : Fin n, badIndicator s i := by
  classical
  rw [badIndices, Finset.card_filter]
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, badIndicator]
  apply Finset.sum_congr rfl
  intro i _
  cases h : passes s i <;> simp

theorem initial_static_bad_moment {n : ℕ} (hn : 2 ≤ n) :
    (∑ s : ChainState n, initialWeight (2 / 3) s * ((badIndices s).card : ℝ)) =
      (15 * (n : ℝ) - 16) / 48 := by
  classical
  simp_rw [bad_card_eq_sum_indicator, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [initial_static_failure_probability hn]
  have hpoint (i : Fin n) :
      (if i.val = 0 then (1 / 12 : ℝ) else
        if i.val + 1 = n then 5 / 24 else 5 / 16) =
      5 / 16 - (if i.val = 0 then 11 / 48 else 0) -
        (if i.val + 1 = n then 5 / 48 else 0) := by
    by_cases hfirst : i.val = 0
    · have hn1 : (1 : ℕ) ≠ n := by omega
      norm_num [hfirst, hn1]
    · by_cases hlast : i.val + 1 = n <;> norm_num [hfirst, hlast]
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have hf : ∀ i : Fin n, i.val = 0 ↔ i = ⟨0, by omega⟩ := by
    intro i
    simp only [Fin.ext_iff]
  have hl : ∀ i : Fin n, i.val + 1 = n ↔ i = ⟨n - 1, by omega⟩ := by
    intro i
    simp only [Fin.ext_iff]
    omega
  simp_rw [hf, hl]
  simp
  ring

end MTChainFormal.BiasedResampling
