/-
  From an accepted finite drift witness to an actual random process.

  Realization states only adaptation and the one-step conditional transition
  probabilities of the supplied rational kernel. It contains no potential,
  drift, termination or expected-work conclusion. The potential's conditional
  expectation is derived by a finite indicator expansion, then connected to
  the existing additive-drift theorem.

  The first-hit count is stopped at the first good state. No LLL/Shearer/HLS
  premise is used. Providing a faithful transition law for an MT trajectory
  or a physical controller remains a separate model-specific obligation.
-/

module

public import PPGraph.Finite.Drift.Basic

@[expose] public section

set_option linter.unusedSectionVars false

open MeasureTheory
open scoped ENNReal NNReal

namespace FiniteDrift

variable {S Ω : Type*} [Fintype S] [DecidableEq S]
    [MeasurableSpace S] [MeasurableSingletonClass S] [mΩ : MeasurableSpace Ω]

noncomputable def stateIndicator (X : Ω → S) (t : S) : Ω → ℝ :=
  {ω | X ω = t}.indicator (fun _ => 1)

def activeEvent (M : Model S) (X : ℕ → Ω → S) (n : ℕ) : Set Ω :=
  {ω | M.good (X n ω) = false}

/-- The process uses these transition probabilities, conditional on its history. -/
structure Realization (M : Model S) (μ : Measure Ω)
    (history : Filtration ℕ mΩ) (X : ℕ → Ω → S) : Prop where
  adapted : ∀ n, Measurable[history n] (X n)
  transition : ∀ n t,
    μ[stateIndicator (X (n + 1)) t | history n] =ᵐ[μ]
      fun ω => (M.transition (X n ω) t : ℝ)

theorem finite_value_expansion (f : S → ℝ) (X : Ω → S) :
    (fun ω => f (X ω)) = ∑ t, f t • stateIndicator X t := by
  funext ω
  simp [stateIndicator, Finset.sum_apply, Set.indicator_apply, eq_comm]

theorem integrable_finite_value (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : S → ℝ) (X : Ω → S) (hX : Measurable X) :
    Integrable (fun ω => f (X ω)) μ := by
  rw [finite_value_expansion]
  apply integrable_finsetSum'
  intro t _
  exact ((integrable_const (1 : ℝ)).indicator (hX (measurableSet_singleton t))).smul _

theorem realization_measurable (M : Model S) (μ : Measure Ω)
    (history : Filtration ℕ mΩ) (X : ℕ → Ω → S)
    (L : Realization M μ history X) (n : ℕ) : Measurable (X n) :=
  (L.adapted n).mono (history.le n) le_rfl

theorem activeEvent_measurable_history (M : Model S) (μ : Measure Ω)
    (history : Filtration ℕ mΩ) (X : ℕ → Ω → S)
    (L : Realization M μ history X) (n : ℕ) :
    MeasurableSet[history n] (activeEvent M X n) := by
  exact L.adapted n (Set.toFinite {s : S | M.good s = false}).measurableSet

/-- The conditional expectation of any finite state function follows from the law. -/
theorem conditional_next_value (M : Model S) (μ : Measure Ω) [IsFiniteMeasure μ]
    (history : Filtration ℕ mΩ) (X : ℕ → Ω → S)
    (L : Realization M μ history X) (f : S → ℝ) (n : ℕ) :
    μ[(fun ω => f (X (n + 1) ω)) | history n] =ᵐ[μ]
      fun ω => ∑ t, (M.transition (X n ω) t : ℝ) * f t := by
  rw [finite_value_expansion]
  have hi (t : S) : Integrable (f t • stateIndicator (X (n + 1)) t) μ :=
    ((integrable_const (1 : ℝ)).indicator
      (realization_measurable M μ history X L (n + 1)
        (measurableSet_singleton t))).smul _
  have hsum := condExp_finsetSum (fun t (_ : t ∈ Finset.univ) => hi t) (history n)
  have hterm (t : S) :
      μ[f t • stateIndicator (X (n + 1)) t | history n] =ᵐ[μ]
        fun ω => f t * (M.transition (X n ω) t : ℝ) := by
    filter_upwards [condExp_smul (f t) (stateIndicator (X (n + 1)) t) (history n),
      L.transition n t] with ω hsm htr
    simp only [hsm, Pi.smul_apply, smul_eq_mul, htr]
  filter_upwards [hsum, ae_all_iff.mpr hterm] with ω hs ht
  simp only [Finset.sum_apply] at hs
  rw [hs]
  apply Finset.sum_congr rfl
  intro t _
  rw [ht t, mul_comm]

noncomputable def rate (W : Witness S) : ℝ≥0 := Real.toNNReal (W.delta : ℝ)

theorem rate_coe (M : Model S) (W : Witness S) (h : check M W = true) :
    (rate W : ℝ) = (W.delta : ℝ) := by
  have hd : (0 : ℝ) ≤ (W.delta : ℝ) := by
    exact_mod_cast (delta_positive M W h).le
  simp only [rate, Real.toNNReal_of_nonneg hd, NNReal.coe_mk]

theorem rate_positive (M : Model S) (W : Witness S) (h : check M W = true) :
    0 < rate W := by
  have hp : (0 : ℝ) < (W.delta : ℝ) := by exact_mod_cast delta_positive M W h
  rw [← rate_coe M W h] at hp
  exact_mod_cast hp

/-- The checked rational inequalities discharge the existing conditional certificate. -/
noncomputable def conditionalCertificate (M : Model S) (W : Witness S)
    (h : check M W = true) (μ : Measure Ω) [IsFiniteMeasure μ]
    (history : Filtration ℕ mΩ) (X : ℕ → Ω → S)
    (L : Realization M μ history X) :
    RepairDrift.ConditionalCertificate μ (activeEvent M X) history (rate W) where
  value n ω := (W.potential (X n ω) : ℝ)
  integrable n := integrable_finite_value μ (fun s => (W.potential s : ℝ))
    (X n) (realization_measurable M μ history X L n)
  nonnegative n := Filter.Eventually.of_forall (fun ω => by
    change (0 : ℝ) ≤ (W.potential (X n ω) : ℝ)
    exact_mod_cast potential_nonnegative M W h (X n ω))
  adapted n := ((measurable_of_finite (fun s => (W.potential s : ℝ))).comp
    (L.adapted n)).stronglyMeasurable
  active_measurable n := activeEvent_measurable_history M μ history X L n
  decrease n := by
    filter_upwards [conditional_next_value M μ history X L
      (fun s => (W.potential s : ℝ)) n] with ω hc
    rw [hc]
    have hd := real_local_decrease M W h (X n ω)
    rw [rate_coe M W h]
    cases hg : M.good (X n ω) <;>
      simpa only [activeEvent, Set.indicator_apply, Set.mem_ofPred_eq,
        hg, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte] using hd

theorem expectedActiveCount_le (M : Model S) (W : Witness S)
    (h : check M W = true) (μ : Measure Ω) [IsFiniteMeasure μ]
    (history : Filtration ℕ mΩ) (X : ℕ → Ω → S)
    (L : Realization M μ history X) :
    RepairDrift.expectedActiveCount μ (activeEvent M X) ≤
      ENNReal.ofReal (∫ ω, (W.potential (X 0 ω) : ℝ) ∂μ) /
        ENNReal.ofReal (W.delta : ℝ) := by
  have hb := (conditionalCertificate M W h μ history X L).expectedActiveCount_le
    (rate_positive M W h)
  simpa only [conditionalCertificate, rate, ENNReal.ofReal] using hb

theorem expectedActiveCount_lt_top (M : Model S) (W : Witness S)
    (h : check M W = true) (μ : Measure Ω) [IsFiniteMeasure μ]
    (history : Filtration ℕ mΩ) (X : ℕ → Ω → S)
    (L : Realization M μ history X) :
    RepairDrift.expectedActiveCount μ (activeEvent M X) < ⊤ :=
  (conditionalCertificate M W h μ history X L).expectedActiveCount_lt_top
    (rate_positive M W h)

/-- Active before the first good state, including the current state. -/
def runningEvent (M : Model S) (X : ℕ → Ω → S) (n : ℕ) : Set Ω :=
  {ω | ∀ k ≤ n, M.good (X k ω) = false}

noncomputable def hitCount (M : Model S) (X : ℕ → Ω → S) : Ω → ℝ≥0∞ :=
  RepairDrift.activeCount (runningEvent M X)

noncomputable def expectedHitCount (M : Model S) (μ : Measure Ω)
    (X : ℕ → Ω → S) : ℝ≥0∞ := ∫⁻ ω, hitCount M X ω ∂μ

theorem runningEvent_measurable (M : Model S) (X : ℕ → Ω → S)
    (hX : ∀ n, Measurable (X n)) (n : ℕ) : MeasurableSet (runningEvent M X n) := by
  have heq : runningEvent M X n = ⋂ k ∈ Finset.range (n + 1), activeEvent M X k := by
    ext ω
    simp only [runningEvent, activeEvent, Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_range]
    simp only [Nat.lt_succ_iff]
  rw [heq]
  exact Finset.measurableSet_biInter _ (fun k _ =>
    hX k (Set.toFinite {s : S | M.good s = false}).measurableSet)

theorem measurable_hitCount (M : Model S) (X : ℕ → Ω → S)
    (hX : ∀ n, Measurable (X n)) : Measurable (hitCount M X) :=
  RepairDrift.measurable_activeCount _ (runningEvent_measurable M X hX)

theorem hitCount_le_activeCount (M : Model S) (X : ℕ → Ω → S) (ω : Ω) :
    hitCount M X ω ≤ RepairDrift.activeCount (activeEvent M X) ω := by
  apply ENNReal.tsum_le_tsum
  intro n
  by_cases hr : ω ∈ runningEvent M X n
  · have ha : ω ∈ activeEvent M X n := hr n le_rfl
    rw [Set.indicator_of_mem hr, Set.indicator_of_mem ha]
  · rw [Set.indicator_of_notMem hr]
    exact zero_le

theorem hitCount_le_of_good (M : Model S) (X : ℕ → Ω → S)
    (ω : Ω) (T : ℕ) (hgood : M.good (X T ω) = true) : hitCount M X ω ≤ T := by
  classical
  have hstop : ∀ n, T ≤ n → ω ∉ runningEvent M X n := by
    intro n hn hr
    have hh := hr T hn
    simp only [hgood, Bool.true_eq_false] at hh
  have hz : ∀ n ∉ Finset.range T,
      (runningEvent M X n).indicator (fun _ => (1 : ℝ≥0∞)) ω = 0 := by
    intro n hn
    exact Set.indicator_of_notMem (hstop n (Nat.le_of_not_gt (by
      simpa only [Finset.mem_range] using hn))) _
  unfold hitCount RepairDrift.activeCount
  rw [tsum_eq_sum hz]
  calc
    (∑ n ∈ Finset.range T, (runningEvent M X n).indicator (fun _ => (1 : ℝ≥0∞)) ω) ≤
        ∑ _n ∈ Finset.range T, (1 : ℝ≥0∞) := by
      apply Finset.sum_le_sum
      intro n _
      by_cases hn : ω ∈ runningEvent M X n
      · rw [Set.indicator_of_mem hn]
      · rw [Set.indicator_of_notMem hn]
        exact zero_le
    _ = T := by simp

theorem hitCount_lt_top_iff_exists_good (M : Model S) (X : ℕ → Ω → S) (ω : Ω) :
    hitCount M X ω < ⊤ ↔ ∃ T, M.good (X T ω) = true := by
  constructor
  · intro hf
    by_contra hn
    have hb (n : ℕ) : M.good (X n ω) = false := by
      cases hg : M.good (X n ω)
      · rfl
      · exact False.elim (hn ⟨n, hg⟩)
    have hi : hitCount M X ω = ⊤ := by
      unfold hitCount RepairDrift.activeCount
      calc
        (∑' n, (runningEvent M X n).indicator (fun _ => (1 : ℝ≥0∞)) ω) =
            ∑' _n : ℕ, (1 : ℝ≥0∞) := by
          apply tsum_congr
          intro n
          have hmem : ω ∈ runningEvent M X n := fun k _ => hb k
          exact Set.indicator_of_mem hmem _
        _ = ⊤ := ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero
    exact hf.ne hi
  · rintro ⟨T, hT⟩
    exact lt_of_le_of_lt (hitCount_le_of_good M X ω T hT) (by simp)

theorem expectedHitCount_le (M : Model S) (W : Witness S)
    (h : check M W = true) (μ : Measure Ω) [IsFiniteMeasure μ]
    (history : Filtration ℕ mΩ) (X : ℕ → Ω → S)
    (L : Realization M μ history X) :
    expectedHitCount M μ X ≤
      ENNReal.ofReal (∫ ω, (W.potential (X 0 ω) : ℝ) ∂μ) /
        ENNReal.ofReal (W.delta : ℝ) := by
  exact (lintegral_mono (hitCount_le_activeCount M X)).trans
    (expectedActiveCount_le M W h μ history X L)

theorem expectedHitCount_lt_top (M : Model S) (W : Witness S)
    (h : check M W = true) (μ : Measure Ω) [IsFiniteMeasure μ]
    (history : Filtration ℕ mΩ) (X : ℕ → Ω → S)
    (L : Realization M μ history X) : expectedHitCount M μ X < ⊤ :=
  lt_of_le_of_lt (lintegral_mono (hitCount_le_activeCount M X))
    (expectedActiveCount_lt_top M W h μ history X L)

theorem expectedHitCount_fixed_le (M : Model S) (W : Witness S)
    (h : check M W = true) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (history : Filtration ℕ mΩ) (X : ℕ → Ω → S)
    (L : Realization M μ history X) (s₀ : S) (hinit : ∀ ω, X 0 ω = s₀) :
    expectedHitCount M μ X ≤ ENNReal.ofReal (W.potential s₀ : ℝ) /
      ENNReal.ofReal (W.delta : ℝ) := by
  simpa only [hinit, integral_const, probReal_univ, one_smul] using
    expectedHitCount_le M W h μ history X L

theorem hitCount_eq_first_good (M : Model S) (X : ℕ → Ω → S)
    (ω : Ω) (T : ℕ) (hgood : M.good (X T ω) = true)
    (hbefore : ∀ k < T, M.good (X k ω) = false) : hitCount M X ω = T := by
  apply le_antisymm (hitCount_le_of_good M X ω T hgood)
  have hsum : (∑ n ∈ Finset.range T,
      (runningEvent M X n).indicator (fun _ => (1 : ℝ≥0∞)) ω) = T := by
    calc
      _ = ∑ _n ∈ Finset.range T, (1 : ℝ≥0∞) := by
        apply Finset.sum_congr rfl
        intro n hn
        have hmem : ω ∈ runningEvent M X n := fun k hk =>
          hbefore k (lt_of_le_of_lt hk (Finset.mem_range.mp hn))
        exact Set.indicator_of_mem hmem _
      _ = T := by simp
  rw [← hsum]
  exact ENNReal.sum_le_tsum (Finset.range T)

theorem ae_exists_good (M : Model S) (W : Witness S)
    (h : check M W = true) (μ : Measure Ω) [IsFiniteMeasure μ]
    (history : Filtration ℕ mΩ) (X : ℕ → Ω → S)
    (L : Realization M μ history X) : ∀ᵐ ω ∂μ, ∃ T, M.good (X T ω) = true := by
  have hf := MeasureTheory.ae_lt_top
    (measurable_hitCount M X (realization_measurable M μ history X L))
    (expectedHitCount_lt_top M W h μ history X L).ne
  filter_upwards [hf] with ω hω
  exact (hitCount_lt_top_iff_exists_good M X ω).mp hω

theorem measure_success_eq_one (M : Model S) (W : Witness S)
    (h : check M W = true) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (history : Filtration ℕ mΩ) (X : ℕ → Ω → S)
    (L : Realization M μ history X) : μ {ω | ∃ T, M.good (X T ω) = true} = 1 := by
  have hm : MeasurableSet {ω | ∃ T, M.good (X T ω) = true} := by
    have heq : {ω | ∃ T, M.good (X T ω) = true} =
        ⋃ T : ℕ, {ω | M.good (X T ω) = true} := by
      ext ω
      simp
    rw [heq]
    exact MeasurableSet.iUnion (fun T =>
      realization_measurable M μ history X L T
        (Set.toFinite {s : S | M.good s = true}).measurableSet)
  have hs := (ae_iff_measure_eq hm.nullMeasurableSet).mp (ae_exists_good M W h μ history X L)
  simpa only [measure_univ] using hs

end FiniteDrift

#check @FiniteDrift.finite_value_expansion
#check @FiniteDrift.integrable_finite_value
#check @FiniteDrift.realization_measurable
#check @FiniteDrift.activeEvent_measurable_history
#check @FiniteDrift.conditional_next_value
#check @FiniteDrift.rate_coe
#check @FiniteDrift.rate_positive
#check @FiniteDrift.expectedActiveCount_le
#check @FiniteDrift.expectedActiveCount_lt_top
#check @FiniteDrift.runningEvent_measurable
#check @FiniteDrift.measurable_hitCount
#check @FiniteDrift.hitCount_le_activeCount
#check @FiniteDrift.hitCount_le_of_good
#check @FiniteDrift.hitCount_lt_top_iff_exists_good
#check @FiniteDrift.expectedHitCount_le
#check @FiniteDrift.expectedHitCount_lt_top
#check @FiniteDrift.expectedHitCount_fixed_le
#check @FiniteDrift.hitCount_eq_first_good
#check @FiniteDrift.ae_exists_good
#check @FiniteDrift.measure_success_eq_one
