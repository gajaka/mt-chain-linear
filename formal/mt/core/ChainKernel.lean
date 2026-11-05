module

public import Chain
public import KernelWork

@[expose] public section

set_option autoImplicit false

namespace MTChainFormal

open scoped BigOperators ENNReal

/-- Nonterminal raw configurations. Good configurations are collapsed to none. -/
abbrev ActiveState (n : ℕ) := {s : ChainState n // (badIndices s).Nonempty}

abbrev KilledState (n : ℕ) := Option (ActiveState n)

noncomputable def kill {n : ℕ} (s : ChainState n) : KilledState n :=
  if h : (badIndices s).Nonempty then some ⟨s, h⟩ else none

noncomputable def activeSelected {n : ℕ} (s : ActiveState n) : Fin n :=
  (badIndices s.val).min' s.property

theorem activeSelected_firstFailure {n : ℕ} (s : ActiveState n) :
    firstFailure s.val = some (activeSelected s) := by
  exact firstFailure_eq_some s.val s.property

theorem activeSelected_failed {n : ℕ} (s : ActiveState n) :
    passes s.val (activeSelected s) = false := by
  exact selected_failed s.val (activeSelected s) (activeSelected_firstFailure s)

theorem activeSelected_prefix {n : ℕ} (s : ActiveState n) :
    PrefixHolds s.val (activeSelected s).val := by
  exact selected_prefix s.val (activeSelected s) (activeSelected_firstFailure s)

@[simp] theorem kill_of_bad {n : ℕ} (s : ActiveState n) : kill s.val = some s := by
  simp [kill, s.property]

theorem kill_eq_none_iff {n : ℕ} (s : ChainState n) :
    kill s = none ↔ ∀ i, passes s i = true := by
  classical
  rw [← no_failure_iff]
  by_cases h : (badIndices s).Nonempty <;> simp [kill, firstFailure, h]

theorem kill_eq_some_iff {n : ℕ} (s : ChainState n) (a : ActiveState n) :
    kill s = some a ↔ s = a.val := by
  constructor
  · intro h
    unfold kill at h
    split at h
    next hbad => exact congrArg Subtype.val (Option.some.inj h)
    next hbad => simp at h
  · intro h
    subst s
    exact kill_of_bad a

/-- One registered update. Draws for fixed endpoints are unused dummy draws. -/
noncomputable def killedStep {n : ℕ} : KilledState n → Draw → KilledState n
  | none, _ => none
  | some s, u => kill (replace s.val (activeSelected s) u)

@[simp] theorem killedStep_none {n : ℕ} (u : Draw) :
    killedStep (none : KilledState n) u = none := rfl

@[simp] theorem killedStep_some {n : ℕ} (s : ActiveState n) (u : Draw) :
    killedStep (some s) u = kill (replace s.val (activeSelected s) u) := rfl

theorem card_Draw : Fintype.card Draw = 36 := by
  norm_num [Draw, Fintype.card_prod]

noncomputable def drawAverage (f : Draw → ℝ) : ℝ := ∑ u, (1 / 36 : ℝ) * f u

theorem drawAverage_const (a : ℝ) : drawAverage (fun _ => a) = a := by
  simp [drawAverage, Finset.sum_const]

theorem drawAverage_nonneg (f : Draw → ℝ) (hf : ∀ u, 0 ≤ f u) :
    0 ≤ drawAverage f := by
  exact Finset.sum_nonneg (fun u _ => mul_nonneg (by norm_num) (hf u))

theorem drawAverage_mono {f g : Draw → ℝ} (hfg : ∀ u, f u ≤ g u) :
    drawAverage f ≤ drawAverage g := by
  exact Finset.sum_le_sum (fun u _ => mul_le_mul_of_nonneg_left (hfg u) (by norm_num))

noncomputable def chainWeight {n : ℕ} (s t : KilledState n) : ℝ :=
  ∑ u : Draw, if killedStep s u = t then (1 / 36 : ℝ) else 0

theorem chainWeight_nonneg {n : ℕ} (s t : KilledState n) : 0 ≤ chainWeight s t := by
  classical
  apply Finset.sum_nonneg
  intro u _
  split_ifs <;> norm_num

theorem chainWeight_sum {n : ℕ} (s : KilledState n) : ∑ t, chainWeight s t = 1 := by
  classical
  unfold chainWeight
  rw [Finset.sum_comm]
  simp

/-- The actual uniform-36-draw transition kernel on killed raw configurations. -/
noncomputable def chainKernel (n : ℕ) : FiniteKernel (KilledState n) where
  weight := chainWeight
  nonneg := chainWeight_nonneg
  sum_eq_one := chainWeight_sum

@[simp] theorem chainWeight_none {n : ℕ} (t : KilledState n) :
    chainWeight none t = if t = none then 1 else 0 := by
  classical
  cases t <;> simp [chainWeight, killedStep]

theorem expect_chainKernel {n : ℕ} (f : KilledState n → ℝ) (s : KilledState n) :
    expect (chainKernel n) f s = drawAverage (fun u => f (killedStep s u)) := by
  classical
  unfold expect chainKernel chainWeight drawAverage
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  simp

def killedActive {n : ℕ} : KilledState n → Bool
  | none => false
  | some _ => true

@[simp] theorem killedActive_none {n : ℕ} : killedActive (none : KilledState n) = false := rfl

@[simp] theorem killedActive_some {n : ℕ} (s : ActiveState n) :
    killedActive (some s) = true := rfl

theorem chainKernel_inactive_absorbing (n : ℕ) :
    InactiveAbsorbing (chainKernel n) killedActive := by
  classical
  intro s t hs ht
  cases s <;> cases t <;> simp_all [killedActive, chainKernel, chainWeight, killedStep]

/-- The raw record is exactly the Cartesian product used by the initial draw. -/
def chainStateEquiv (n : ℕ) :
    ChainState n ≃ (Fin (n - 1) → Fin 3) × (Fin n → Fin 4) where
  toFun s := (s.values, s.tactic)
  invFun p := ⟨p.1, p.2⟩
  left_inv s := by cases s; rfl
  right_inv p := by cases p; rfl

theorem card_ChainState (n : ℕ) :
    Fintype.card (ChainState n) = 3 ^ (n - 1) * 4 ^ n := by
  rw [Fintype.card_congr (chainStateEquiv n)]
  simp [Fintype.card_prod]

noncomputable def initialFull {n : ℕ} (_s : ChainState n) : ℝ :=
  1 / (Fintype.card (ChainState n) : ℝ)

theorem initialFull_nonneg {n : ℕ} (s : ChainState n) : 0 ≤ initialFull s := by
  unfold initialFull
  positivity

theorem initialFull_sum (n : ℕ) : ∑ s : ChainState n, initialFull s = 1 := by
  have hc : (Fintype.card (ChainState n) : ℝ) ≠ 0 := by
    rw [card_ChainState]
    positivity
  simp [initialFull, Finset.sum_const, nsmul_eq_mul, hc]

theorem initialFull_product_density {n : ℕ} (s : ChainState n) :
    initialFull s = (1 / 3 : ℝ) ^ (n - 1) * (1 / 4 : ℝ) ^ n := by
  simp [initialFull, card_ChainState, one_div, inv_pow, mul_comm]

theorem initialFull_coordinate_density {n : ℕ} (s : ChainState n) :
    initialFull s = (∏ _j : Fin (n - 1), (1 / 3 : ℝ)) *
      (∏ _i : Fin n, (1 / 4 : ℝ)) := by
  simpa using initialFull_product_density s

/-- The actual killed initial law is the pushforward of the uniform raw law. -/
noncomputable def initialLaw {n : ℕ} (t : KilledState n) : ℝ :=
  ∑ s : ChainState n, if kill s = t then initialFull s else 0

theorem initialLaw_nonneg {n : ℕ} (t : KilledState n) : 0 ≤ initialLaw t := by
  classical
  apply Finset.sum_nonneg
  intro s _
  split_ifs
  · exact initialFull_nonneg s
  · exact le_rfl

theorem initialLaw_sum (n : ℕ) : ∑ t : KilledState n, initialLaw t = 1 := by
  classical
  unfold initialLaw
  rw [Finset.sum_comm]
  simpa using initialFull_sum n

theorem initialLaw_expect (n : ℕ) (f : KilledState n → ℝ) :
    (∑ t, initialLaw t * f t) = ∑ s : ChainState n, initialFull s * f (kill s) := by
  classical
  unfold initialLaw
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  simp

/-- Every individual passing-to-failing certificate transition is counted. -/
def invalidatedIndices {n : ℕ} (before after : ChainState n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => passes before j = true ∧ passes after j = false)

@[simp] theorem mem_invalidatedIndices {n : ℕ} (before after : ChainState n) (j : Fin n) :
    j ∈ invalidatedIndices before after ↔
      passes before j = true ∧ passes after j = false := by
  simp [invalidatedIndices]

theorem replacement_invalidated_near {n : ℕ} (hn : 2 ≤ n)
    (s : ActiveState n) (u : Draw) (j : Fin n)
    (hbefore : passes s.val j = true)
    (hafter : passes (replace s.val (activeSelected s) u) j = false) :
    j.val = (activeSelected s).val - 1 ∨ j.val = (activeSelected s).val + 1 := by
  have hne : j ≠ activeSelected s := by
    intro h
    subst j
    rw [activeSelected_failed s] at hbefore
    cases hbefore
  have hval : j.val ≠ (activeSelected s).val := by
    intro h
    exact hne (Fin.ext h)
  have hnotfar : ¬ (j.val + 1 < (activeSelected s).val ∨
      (activeSelected s).val + 1 < j.val) := by
    intro hfar
    rw [replace_pass_unchanged hn s.val (activeSelected s) j u hfar, hbefore] at hafter
    cases hafter
  omega

theorem replacement_invalidations_le_two {n : ℕ} (hn : 2 ≤ n)
    (s : ActiveState n) (u : Draw) :
    (invalidatedIndices s.val (replace s.val (activeSelected s) u)).card ≤ 2 := by
  classical
  let bad := invalidatedIndices s.val (replace s.val (activeSelected s) u)
  have hsubset : bad.image (fun j => j.val) ⊆
      {(activeSelected s).val - 1, (activeSelected s).val + 1} := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hb, ha⟩ := (mem_invalidatedIndices _ _ j).mp hj
    simpa only [Finset.mem_insert, Finset.mem_singleton] using
      replacement_invalidated_near hn s u j hb ha
  have hcard : (bad.image (fun j => j.val)).card = bad.card :=
    Finset.card_image_of_injective bad Fin.val_injective
  rw [← hcard]
  exact (Finset.card_le_card hsubset).trans Finset.card_le_two

/-- Hazard reward of the actual raw update before its result is killed. -/
noncomputable def drawInvalidations {n : ℕ} : KilledState n → Draw → ℝ
  | none, _ => 0
  | some s, u => (invalidatedIndices s.val (replace s.val (activeSelected s) u)).card

theorem drawInvalidations_nonneg {n : ℕ} (s : KilledState n) (u : Draw) :
    0 ≤ drawInvalidations s u := by
  cases s <;> simp [drawInvalidations]

theorem drawInvalidations_le_two_active {n : ℕ} (hn : 2 ≤ n)
    (s : KilledState n) (u : Draw) :
    drawInvalidations s u ≤ activeCost killedActive s * 2 := by
  cases s with
  | none => simp [drawInvalidations, activeCost, killedActive]
  | some s =>
      simpa [drawInvalidations, activeCost, killedActive] using
        (Nat.cast_le.mpr (replacement_invalidations_le_two hn s u) :
          ((invalidatedIndices s.val (replace s.val (activeSelected s) u)).card : ℝ) ≤ 2)

noncomputable def expectedHazardCost {n : ℕ} (s : KilledState n) : ℝ :=
  drawAverage (drawInvalidations s)

theorem expectedHazardCost_nonneg {n : ℕ} (s : KilledState n) :
    0 ≤ expectedHazardCost s := drawAverage_nonneg _ (drawInvalidations_nonneg s)

theorem expectedHazardCost_le_two_active {n : ℕ} (hn : 2 ≤ n) (s : KilledState n) :
    expectedHazardCost s ≤ activeCost killedActive s * 2 := by
  exact (drawAverage_mono (drawInvalidations_le_two_active hn s)).trans_eq (drawAverage_const _)

theorem totalHazardWork_le_two_active {n : ℕ} (hn : 2 ≤ n) (s : KilledState n) :
    totalWork (chainKernel n) expectedHazardCost s ≤
      totalWork (chainKernel n) (activeCost killedActive) s * 2 := by
  simpa using totalWork_le_mul (chainKernel n) expectedHazardCost
    (activeCost killedActive) 2 (by norm_num) (expectedHazardCost_le_two_active hn) s

theorem initialTotalHazardWork_le_two_active {n : ℕ} (hn : 2 ≤ n) :
    initialTotalWork (chainKernel n) initialLaw expectedHazardCost ≤
      initialTotalWork (chainKernel n) initialLaw (activeCost killedActive) * 2 := by
  simpa using initialTotalWork_le_mul (chainKernel n) initialLaw expectedHazardCost
    (activeCost killedActive) initialLaw_nonneg 2 (by norm_num)
    (expectedHazardCost_le_two_active hn)

end MTChainFormal
