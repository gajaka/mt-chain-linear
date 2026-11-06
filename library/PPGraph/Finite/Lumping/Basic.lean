/-
  Exact probabilistic reduction of finite repair models.

  Source: Levin--Peres, Markov Chains and Mixing Times, second edition,
  Section 2.3.1, Lemma 2.5 and equation (2.10), printed p. 25.
  The sum of transition masses into each projected fiber must depend only
  on the projected current state. The good-state test must also factor.

  These are local obligations, not assumptions about termination or mean
  work. Checked potentials, exact means, first-hit tails and negative
  certificates transfer from the smaller model. A reachability abstraction
  alone does not justify any of these probability identities.
  No method that always discovers a small projection is claimed.
-/

module

public import PPGraph.Finite.Potential.TailCertificate

@[expose] public section

set_option linter.unusedSectionVars false

open MeasureTheory
open scoped ENNReal NNReal

namespace FiniteLumping

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

def Compatible (M : FiniteDrift.Model S) (N : FiniteDrift.Model A)
    (project : S → A) : Prop :=
  (∀ s, M.good s = N.good (project s)) ∧
  ∀ s a, (∑ t, if project t = a then M.transition s t else 0) =
    N.transition (project s) a

instance compatibleDecidable (M : FiniteDrift.Model S) (N : FiniteDrift.Model A)
    (project : S → A) : Decidable (Compatible M N project) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Exact rational checking of a proposed projection and its fiber masses. -/
def check (M : FiniteDrift.Model S) (N : FiniteDrift.Model A)
    (project : S → A) : Bool := decide (Compatible M N project)

theorem check_iff (M : FiniteDrift.Model S) (N : FiniteDrift.Model A)
    (project : S → A) : check M N project = true ↔ Compatible M N project :=
  decide_eq_true_iff

theorem weighted_projection (M : FiniteDrift.Model S) (N : FiniteDrift.Model A)
    (p : S → A) (h : Compatible M N p) (f : A → ℚ) (s : S) :
    (∑ t, M.transition s t * f (p t)) = ∑ a, N.transition (p s) a * f a := by
  calc
    _ = ∑ t, ∑ a, if p t = a then M.transition s t * f a else 0 := by simp
    _ = ∑ a, ∑ t, if p t = a then M.transition s t * f a else 0 :=
      Finset.sum_comm
    _ = ∑ a, (∑ t, if p t = a then M.transition s t else 0) * f a := by
      simp only [Finset.sum_mul, ite_mul, zero_mul]
    _ = _ := by simp only [h.2]

/-- Surjectivity is needed only to infer structural properties on every abstract row. -/
theorem stochastic_projected (M : FiniteDrift.Model S) (N : FiniteDrift.Model A)
    (p : S → A) (h : Compatible M N p) (hp : Function.Surjective p)
    (hm : FinitePotential.Stochastic M) : FinitePotential.Stochastic N := by
  constructor
  · intro a b
    obtain ⟨s, rfl⟩ := hp a
    rw [← h.2 s b]
    apply Finset.sum_nonneg
    intro t _
    split_ifs
    · exact hm.1 s t
    · exact le_rfl
  · intro a
    obtain ⟨s, rfl⟩ := hp a
    have hh := weighted_projection M N p h (fun _ => 1) s
    simp only [mul_one] at hh
    exact hh.symm.trans (hm.2 s)

def pullWitness (p : S → A) (W : FiniteDrift.Witness A) : FiniteDrift.Witness S :=
  ⟨fun s => W.potential (p s), W.delta⟩

theorem witness_checked (M : FiniteDrift.Model S) (N : FiniteDrift.Model A)
    (p : S → A) (h : Compatible M N p) (hm : FinitePotential.Stochastic M)
    (W : FiniteDrift.Witness A) (hw : FiniteDrift.check N W = true) :
    FiniteDrift.check M (pullWitness p W) = true := by
  have hc := FiniteDrift.check_sound N W hw
  apply FiniteDrift.check_complete
  refine ⟨hm.1, hm.2, fun s => hc.2.2.1 (p s),
    fun s hs => hc.2.2.2.1 (p s) (by rwa [← h.1 s]), hc.2.2.2.2.1, ?_⟩
  intro s
  simpa only [FiniteDrift.localExpectation, pullWitness, h.1 s,
    weighted_projection M N p h W.potential s] using hc.2.2.2.2.2 (p s)

theorem equations_pullback (M : FiniteDrift.Model S) (N : FiniteDrift.Model A)
    (p : S → A) (h : Compatible M N p) (f : A → ℚ)
    (hf : FinitePotential.Equations N f) :
    FinitePotential.Equations M (fun s => f (p s)) := by
  refine ⟨fun s hs => hf.1 (p s) (by rwa [← h.1 s]), ?_⟩
  intro s hs
  rw [weighted_projection M N p h f s]
  exact hf.2 (p s) (by rwa [← h.1 s])

theorem survival_projection (M : FiniteDrift.Model S) (N : FiniteDrift.Model A)
    (p : S → A) (h : Compatible M N p) (n : ℕ) (s : S) :
    FinitePotential.survival M n s = FinitePotential.survival N n (p s) := by
  induction n generalizing s with
  | zero => simp only [FinitePotential.survival, h.1 s]
  | succ n ih =>
    simp only [FinitePotential.survival, h.1 s, ih,
      weighted_projection M N p h (FinitePotential.survival N n) s]

theorem closedBad_pullback (M : FiniteDrift.Model S) (N : FiniteDrift.Model A)
    (p : S → A) (h : Compatible M N p) (hm : FinitePotential.Stochastic M)
    (U : A → Bool) (hu : FinitePotential.ClosedBad N U)
    (s₀ : S) (hs₀ : U (p s₀) = true) :
    FinitePotential.ClosedBad M (fun s => U (p s)) := by
  refine ⟨⟨s₀, hs₀⟩, fun s hs => (h.1 s).trans (hu.2.1 (p s) hs), ?_⟩
  intro s t hs ht
  have hz := hu.2.2 (p s) (p t) hs ht
  have hle : M.transition s t ≤ ∑ u, if p u = p t then M.transition s u else 0 := by
    have hh := Finset.single_le_sum (s := Finset.univ) (a := t)
      (f := fun u => if p u = p t then M.transition s u else 0)
      (fun u _ => by split_ifs; exact hm.1 s u; exact le_rfl) (Finset.mem_univ t)
    simpa using hh
  rw [h.2 s (p t), hz] at hle
  exact le_antisymm hle (hm.1 s t)

theorem checkedClosedBad_refutes (M : FiniteDrift.Model S) (N : FiniteDrift.Model A)
    (p : S → A) (h : Compatible M N p) (hm : FinitePotential.Stochastic M)
    (U : A → Bool) (hu : FinitePotential.checkClosedBad N U = true)
    (s₀ : S) (hs₀ : U (p s₀) = true) : ¬ FinitePotential.ReachesGood M s₀ :=
  FinitePotential.closedBad_not_reachesGood M _
    (closedBad_pullback M N p h hm U ((FinitePotential.checkClosedBad_iff N U).mp hu)
      s₀ hs₀) s₀ hs₀

section Process

variable {Ω : Type*} [MeasurableSpace S] [MeasurableSingletonClass S]
    [MeasurableSpace A] [MeasurableSingletonClass A] [mΩ : MeasurableSpace Ω]

theorem realization_projected (M : FiniteDrift.Model S) (N : FiniteDrift.Model A)
    (p : S → A) (h : Compatible M N p) (μ : Measure Ω) [IsFiniteMeasure μ]
    (history : Filtration ℕ mΩ) (X : ℕ → Ω → S)
    (L : FiniteDrift.Realization M μ history X) :
    FiniteDrift.Realization N μ history (fun n ω => p (X n ω)) where
  adapted n := (measurable_of_finite p).comp (L.adapted n)
  transition n a := by
    have hh := FiniteDrift.conditional_next_value M μ history X L
      (fun s => if p s = a then (1 : ℝ) else 0) n
    have hi : (fun ω => if p (X (n + 1) ω) = a then (1 : ℝ) else 0) =
        FiniteDrift.stateIndicator (fun ω => p (X (n + 1) ω)) a := by
      funext ω
      simp [FiniteDrift.stateIndicator, Set.indicator_apply]
    rw [hi] at hh
    filter_upwards [hh] with ω hω
    rw [hω, ← h.2 (X n ω) a]
    simp only [Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro s _
    split_ifs <;> simp

theorem runningEvent_projection (M : FiniteDrift.Model S) (N : FiniteDrift.Model A)
    (p : S → A) (h : Compatible M N p) (X : ℕ → Ω → S) (n : ℕ) :
    FiniteDrift.runningEvent M X n =
      FiniteDrift.runningEvent N (fun k ω => p (X k ω)) n := by
  ext ω
  simp only [FiniteDrift.runningEvent, Set.mem_ofPred_eq, h.1]

theorem hitCount_projection (M : FiniteDrift.Model S) (N : FiniteDrift.Model A)
    (p : S → A) (h : Compatible M N p) (X : ℕ → Ω → S) (ω : Ω) :
    FiniteDrift.hitCount M X ω =
      FiniteDrift.hitCount N (fun k ω => p (X k ω)) ω := by
  simp only [FiniteDrift.hitCount, RepairDrift.activeCount, runningEvent_projection M N p h X]

theorem expectedHitCount_projection (M : FiniteDrift.Model S) (N : FiniteDrift.Model A)
    (p : S → A) (h : Compatible M N p) (μ : Measure Ω) (X : ℕ → Ω → S) :
    FiniteDrift.expectedHitCount M μ X =
      FiniteDrift.expectedHitCount N μ (fun k ω => p (X k ω)) := by
  simp only [FiniteDrift.expectedHitCount, hitCount_projection M N p h X]

theorem timeout_fixed_projected (M : FiniteDrift.Model S) (N : FiniteDrift.Model A)
    (p : S → A) (h : Compatible M N p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (history : Filtration ℕ mΩ) (X : ℕ → Ω → S)
    (L : FiniteDrift.Realization M μ history X) (a₀ : A)
    (hi : ∀ ω, p (X 0 ω) = a₀) (n : ℕ) :
    μ (FiniteDrift.runningEvent M X n) =
      ENNReal.ofReal (FinitePotential.survival N n a₀ : ℝ) := by
  rw [runningEvent_projection M N p h X]
  exact FinitePotential.running_measure_fixed_eq_survival N μ history _
    (realization_projected M N p h μ history X L) a₀ hi n

theorem mean_fixed_projected (M : FiniteDrift.Model S) (N : FiniteDrift.Model A)
    (p : S → A) (h : Compatible M N p)
    (hn : FinitePotential.Stochastic N) (ha : FinitePotential.Absorbing N)
    (f : A → ℚ) (hf : FinitePotential.Equations N f)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (history : Filtration ℕ mΩ)
    (X : ℕ → Ω → S) (L : FiniteDrift.Realization M μ history X)
    (a₀ : A) (hi : ∀ ω, p (X 0 ω) = a₀) :
    FiniteDrift.expectedHitCount M μ X = ENNReal.ofReal (f a₀ : ℝ) := by
  rw [expectedHitCount_projection M N p h μ X]
  exact FinitePotential.expectedHitCount_fixed_eq_of_equations N f hn ha hf μ history _
    (realization_projected M N p h μ history X L) a₀ hi

theorem checkedTable_timeout_fixed (M : FiniteDrift.Model S) (N : FiniteDrift.Model A)
    (p : S → A) (h : Compatible M N p) (F : ℕ → A → ℚ) (H : ℕ)
    (hc : FinitePotential.checkSurvivalTable N F H = true)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (history : Filtration ℕ mΩ)
    (X : ℕ → Ω → S) (L : FiniteDrift.Realization M μ history X)
    (a₀ : A) (hi : ∀ ω, p (X 0 ω) = a₀) :
    μ (FiniteDrift.runningEvent M X H) = ENNReal.ofReal (F H a₀ : ℝ) := by
  rw [timeout_fixed_projected M N p h μ history X L a₀ hi H,
    ← FinitePotential.checkedSurvivalTable_exact N F H hc a₀]

end Process
end FiniteLumping

#check @FiniteLumping.check_iff
#check @FiniteLumping.weighted_projection
#check @FiniteLumping.stochastic_projected
#check @FiniteLumping.witness_checked
#check @FiniteLumping.equations_pullback
#check @FiniteLumping.survival_projection
#check @FiniteLumping.closedBad_pullback
#check @FiniteLumping.checkedClosedBad_refutes
#check @FiniteLumping.realization_projected
#check @FiniteLumping.runningEvent_projection
#check @FiniteLumping.hitCount_projection
#check @FiniteLumping.expectedHitCount_projection
#check @FiniteLumping.timeout_fixed_projected
#check @FiniteLumping.mean_fixed_projected
#check @FiniteLumping.checkedTable_timeout_fixed
