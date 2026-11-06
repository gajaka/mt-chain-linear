/-
  Probabilistic reduction certified from the update itself.

  The concrete state space need not be finite. The input law and the
  projected state space are finite. The source and reduced updates share
  the input mass, preserve the good test, and commute with projection.
  These local identities prove identical projected trajectories, the
  smaller conditional law, exact first-hit work, means and timeout tails.

  Source: Levin--Peres, Markov Chains and Mixing Times, second edition,
  Section 2.3.1, Lemma 2.5. Update commutation is a sufficient structural
  condition for that lemma's fiber-mass identity, not a necessary one.
  The existing independently sampled input measure supplies freshness.
  No finite enumeration of the concrete states or termination premise is
  required by the update-level bridge. Finding a suitable projection and
  relating the source update/input law to hardware remain separate work.
-/

module

public import PPGraph.Finite.Lumping.Basic
public import PPGraph.Finite.Update.IID

@[expose] public section

set_option linter.unusedSectionVars false

open MeasureTheory
open scoped ENNReal NNReal

namespace FiniteLumpingUpdate

variable {S A I : Type*} [DecidableEq S] [Fintype A] [DecidableEq A]
    [Fintype I] [DecidableEq I]

def Commutes (R : FiniteUpdate.Rule S I) (Q : FiniteUpdate.Rule A I)
    (p : S → A) : Prop :=
  (∀ i, R.mass i = Q.mass i) ∧
  (∀ s, R.good s = Q.good (p s)) ∧
  ∀ s i, p (R.update s i) = Q.update (p s) i

theorem valid_iff (R : FiniteUpdate.Rule S I) (Q : FiniteUpdate.Rule A I)
    (p : S → A) (h : Commutes R Q p) : FiniteUpdate.Valid R ↔ FiniteUpdate.Valid Q := by
  simp only [FiniteUpdate.Valid, h.1]

theorem trajectory_projection (R : FiniteUpdate.Rule S I) (Q : FiniteUpdate.Rule A I)
    (p : S → A) (h : Commutes R Q p) (s₀ : S) (n : ℕ) (ω : ℕ → I) :
    p (FiniteUpdate.iidTrajectory R s₀ n ω) =
      FiniteUpdate.iidTrajectory Q (p s₀) n ω := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [FiniteUpdate.iidTrajectory, h.2.2, ih]

/-- Derive the book's fiber-mass identity; no exported full matrix is trusted. -/
theorem compatible_of_commutes [Fintype S]
    (R : FiniteUpdate.Rule S I) (Q : FiniteUpdate.Rule A I)
    (p : S → A) (h : Commutes R Q p) :
    FiniteLumping.Compatible (FiniteUpdate.model R) (FiniteUpdate.model Q) p := by
  refine ⟨h.2.1, ?_⟩
  intro s a
  change (∑ t, if p t = a then FiniteUpdate.kernel R s t else 0) =
    FiniteUpdate.kernel Q (p s) a
  calc
    _ = ∑ t, FiniteUpdate.kernel R s t * (if p t = a then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro t _
      split_ifs <;> simp
    _ = ∑ i, R.mass i * (if p (R.update s i) = a then 1 else 0) :=
      FiniteUpdate.weighted_next_value R _ s
    _ = _ := by
      simp only [FiniteUpdate.kernel, h.1, h.2.2]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp

theorem kernel_le_projected (R : FiniteUpdate.Rule S I) (Q : FiniteUpdate.Rule A I)
    (p : S → A) (h : Commutes R Q p) (hq : FiniteUpdate.Valid Q) (s t : S) :
    FiniteUpdate.kernel R s t ≤ FiniteUpdate.kernel Q (p s) (p t) := by
  unfold FiniteUpdate.kernel
  apply Finset.sum_le_sum
  intro i _
  by_cases he : R.update s i = t
  · have hp : Q.update (p s) i = p t := (h.2.2 s i).symm.trans (congrArg p he)
    simp only [he, hp, ↓reduceIte, h.1 i]
    exact le_rfl
  · simp only [he, ↓reduceIte]
    split_ifs
    · exact hq.1 i
    · exact le_rfl

theorem positive_step_projects (R : FiniteUpdate.Rule S I) (Q : FiniteUpdate.Rule A I)
    (p : S → A) (h : Commutes R Q p) (hq : FiniteUpdate.Valid Q) (s t : S)
    (hs : 0 < FiniteUpdate.kernel R s t) : 0 < FiniteUpdate.kernel Q (p s) (p t) :=
  hs.trans_le (kernel_le_projected R Q p h hq s t)

theorem reachable_good_projects (R : FiniteUpdate.Rule S I) (Q : FiniteUpdate.Rule A I)
    (p : S → A) (h : Commutes R Q p) (hq : FiniteUpdate.Valid Q) (s₀ : S)
    (hr : FinitePotential.ReachesGood (FiniteUpdate.model R) s₀) :
    FinitePotential.ReachesGood (FiniteUpdate.model Q) (p s₀) := by
  obtain ⟨g, hg, hpath⟩ := hr
  refine ⟨p g, ?_, ?_⟩
  · simpa only [FiniteUpdate.model, h.2.1] using hg
  · exact Relation.ReflTransGen.lift p (positive_step_projects R Q p h hq) _ _ hpath

theorem positive_step_lifts (R : FiniteUpdate.Rule S I) (Q : FiniteUpdate.Rule A I)
    (p : S → A) (h : Commutes R Q p) (hr : FiniteUpdate.Valid R)
    (hq : FiniteUpdate.Valid Q) (s : S) (a : A)
    (ha : 0 < FiniteUpdate.kernel Q (p s) a) :
    ∃ t, 0 < FiniteUpdate.kernel R s t ∧ p t = a := by
  have hn : ∀ i ∈ Finset.univ, 0 ≤ (if Q.update (p s) i = a then Q.mass i else 0) := by
    intro i _
    split_ifs
    · exact hq.1 i
    · exact le_rfl
  obtain ⟨i, _, hi⟩ := (Finset.sum_pos_iff_of_nonneg hn).mp ha
  have he : Q.update (p s) i = a := by
    by_contra hh
    simp only [hh, ↓reduceIte, lt_self_iff_false] at hi
  have hm : 0 < R.mass i := by simpa only [he, ↓reduceIte, h.1 i] using hi
  have hle : R.mass i ≤ FiniteUpdate.kernel R s (R.update s i) := by
    have hh := Finset.single_le_sum (s := Finset.univ) (a := i)
      (f := fun j => if R.update s j = R.update s i then R.mass j else 0)
      (fun j _ => by split_ifs; exact hr.1 j; exact le_rfl) (Finset.mem_univ i)
    simpa only [FiniteUpdate.kernel, ↓reduceIte] using hh
  exact ⟨R.update s i, hm.trans_le hle, (h.2.2 s i).trans he⟩

theorem reachable_lifts (R : FiniteUpdate.Rule S I) (Q : FiniteUpdate.Rule A I)
    (p : S → A) (h : Commutes R Q p) (hr : FiniteUpdate.Valid R)
    (hq : FiniteUpdate.Valid Q) (s₀ : S) (a : A)
    (ha : Relation.ReflTransGen (fun b c => 0 < FiniteUpdate.kernel Q b c) (p s₀) a) :
    ∃ t, Relation.ReflTransGen (fun s t => 0 < FiniteUpdate.kernel R s t) s₀ t ∧ p t = a := by
  induction ha with
  | refl => exact ⟨s₀, Relation.ReflTransGen.refl, rfl⟩
  | @tail b a _ hstep ih =>
    obtain ⟨s, hs, hp⟩ := ih
    obtain ⟨t, ht, he⟩ := positive_step_lifts R Q p h hr hq s a (by rwa [hp])
    exact ⟨t, hs.tail ht, he⟩

theorem reachable_good_iff (R : FiniteUpdate.Rule S I) (Q : FiniteUpdate.Rule A I)
    (p : S → A) (h : Commutes R Q p) (hr : FiniteUpdate.Valid R)
    (hq : FiniteUpdate.Valid Q) (s₀ : S) :
    FinitePotential.ReachesGood (FiniteUpdate.model R) s₀ ↔
      FinitePotential.ReachesGood (FiniteUpdate.model Q) (p s₀) := by
  constructor
  · exact reachable_good_projects R Q p h hq s₀
  · rintro ⟨a, hg, hpath⟩
    obtain ⟨t, ht, he⟩ := reachable_lifts R Q p h hr hq s₀ a hpath
    refine ⟨t, ?_, ht⟩
    simpa only [FiniteUpdate.model, h.2.1, he] using hg

theorem checkedClosedBad_no_path (R : FiniteUpdate.Rule S I) (Q : FiniteUpdate.Rule A I)
    (p : S → A) (h : Commutes R Q p) (hq : FiniteUpdate.Valid Q) (s₀ : S)
    (U : A → Bool) (hu : FinitePotential.checkClosedBad (FiniteUpdate.model Q) U = true)
    (hs : U (p s₀) = true) : ¬ FinitePotential.ReachesGood (FiniteUpdate.model R) s₀ := by
  intro hr
  exact FinitePotential.checkedClosedBad_not_reachesGood (FiniteUpdate.model Q) U hu
    (p s₀) hs (reachable_good_projects R Q p h hq s₀ hr)

theorem runningEvent_projection (R : FiniteUpdate.Rule S I) (Q : FiniteUpdate.Rule A I)
    (p : S → A) (h : Commutes R Q p) (s₀ : S) (n : ℕ) :
    FiniteDrift.runningEvent (FiniteUpdate.model R) (FiniteUpdate.iidTrajectory R s₀) n =
      FiniteDrift.runningEvent (FiniteUpdate.model Q) (FiniteUpdate.iidTrajectory Q (p s₀)) n := by
  ext ω
  simp only [FiniteDrift.runningEvent, FiniteUpdate.model, Set.mem_ofPred_eq,
    h.2.1, trajectory_projection R Q p h s₀]

theorem hitCount_projection (R : FiniteUpdate.Rule S I) (Q : FiniteUpdate.Rule A I)
    (p : S → A) (h : Commutes R Q p) (s₀ : S) (ω : ℕ → I) :
    FiniteDrift.hitCount (FiniteUpdate.model R) (FiniteUpdate.iidTrajectory R s₀) ω =
      FiniteDrift.hitCount (FiniteUpdate.model Q) (FiniteUpdate.iidTrajectory Q (p s₀)) ω := by
  simp only [FiniteDrift.hitCount, RepairDrift.activeCount,
    runningEvent_projection R Q p h s₀]

section Measure

variable [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace I] [MeasurableSingletonClass I]

theorem inputPMF_eq (R : FiniteUpdate.Rule S I) (Q : FiniteUpdate.Rule A I)
    (p : S → A) (h : Commutes R Q p) (hr : FiniteUpdate.Valid R)
    (hq : FiniteUpdate.Valid Q) :
    FiniteUpdate.inputPMF R hr = FiniteUpdate.inputPMF Q hq := by
  ext i
  simp only [FiniteUpdate.inputPMF, PMF.ofFintype_apply, h.1]

theorem iidMeasure_eq (R : FiniteUpdate.Rule S I) (Q : FiniteUpdate.Rule A I)
    (p : S → A) (h : Commutes R Q p) (hr : FiniteUpdate.Valid R)
    (hq : FiniteUpdate.Valid Q) :
    FiniteUpdate.iidMeasure R hr = FiniteUpdate.iidMeasure Q hq := by
  simp only [FiniteUpdate.iidMeasure, inputPMF_eq R Q p h hr hq]

theorem projected_iidRealization (R : FiniteUpdate.Rule S I) (Q : FiniteUpdate.Rule A I)
    (p : S → A) (h : Commutes R Q p) (hr : FiniteUpdate.Valid R)
    (hq : FiniteUpdate.Valid Q) (s₀ : S) :
    FiniteDrift.Realization (FiniteUpdate.model Q) (FiniteUpdate.iidMeasure R hr)
      (FiniteUpdate.inputHistory (A := I))
      (fun n ω => p (FiniteUpdate.iidTrajectory R s₀ n ω)) := by
  have ht : (fun n ω => p (FiniteUpdate.iidTrajectory R s₀ n ω)) =
      FiniteUpdate.iidTrajectory Q (p s₀) := by
    funext n ω
    exact trajectory_projection R Q p h s₀ n ω
  rw [ht, iidMeasure_eq R Q p h hr hq]
  exact FiniteUpdate.iidRealization Q hq (p s₀)

theorem expectedHitCount_projection (R : FiniteUpdate.Rule S I) (Q : FiniteUpdate.Rule A I)
    (p : S → A) (h : Commutes R Q p) (hr : FiniteUpdate.Valid R)
    (hq : FiniteUpdate.Valid Q) (s₀ : S) :
    FiniteDrift.expectedHitCount (FiniteUpdate.model R) (FiniteUpdate.iidMeasure R hr)
        (FiniteUpdate.iidTrajectory R s₀) =
      FiniteDrift.expectedHitCount (FiniteUpdate.model Q) (FiniteUpdate.iidMeasure Q hq)
        (FiniteUpdate.iidTrajectory Q (p s₀)) := by
  simp only [FiniteDrift.expectedHitCount, hitCount_projection R Q p h s₀,
    iidMeasure_eq R Q p h hr hq]

theorem timeout_exact (R : FiniteUpdate.Rule S I) (Q : FiniteUpdate.Rule A I)
    (p : S → A) (h : Commutes R Q p) (hr : FiniteUpdate.Valid R)
    (hq : FiniteUpdate.Valid Q) (s₀ : S) (n : ℕ) :
    (FiniteUpdate.iidMeasure R hr)
        (FiniteDrift.runningEvent (FiniteUpdate.model R) (FiniteUpdate.iidTrajectory R s₀) n) =
      ENNReal.ofReal (FinitePotential.survival (FiniteUpdate.model Q) n (p s₀) : ℝ) := by
  rw [runningEvent_projection R Q p h s₀, iidMeasure_eq R Q p h hr hq]
  exact FinitePotential.running_measure_fixed_eq_survival (FiniteUpdate.model Q)
    (FiniteUpdate.iidMeasure Q hq) FiniteUpdate.inputHistory _
    (FiniteUpdate.iidRealization Q hq (p s₀)) (p s₀) (fun _ => rfl) n

theorem checkedTable_timeout_exact (R : FiniteUpdate.Rule S I) (Q : FiniteUpdate.Rule A I)
    (p : S → A) (h : Commutes R Q p) (hr : FiniteUpdate.Valid R)
    (hq : FiniteUpdate.Valid Q) (s₀ : S) (F : ℕ → A → ℚ) (H : ℕ)
    (hc : FinitePotential.checkSurvivalTable (FiniteUpdate.model Q) F H = true) :
    (FiniteUpdate.iidMeasure R hr)
        (FiniteDrift.runningEvent (FiniteUpdate.model R) (FiniteUpdate.iidTrajectory R s₀) H) =
      ENNReal.ofReal (F H (p s₀) : ℝ) := by
  rw [timeout_exact R Q p h hr hq s₀ H,
    ← FinitePotential.checkedSurvivalTable_exact (FiniteUpdate.model Q) F H hc (p s₀)]

theorem mean_exact (R : FiniteUpdate.Rule S I) (Q : FiniteUpdate.Rule A I)
    (p : S → A) (h : Commutes R Q p) (hr : FiniteUpdate.Valid R)
    (hq : FiniteUpdate.Valid Q) (s₀ : S) (f : A → ℚ)
    (ha : FinitePotential.Absorbing (FiniteUpdate.model Q))
    (hf : FinitePotential.Equations (FiniteUpdate.model Q) f) :
    FiniteDrift.expectedHitCount (FiniteUpdate.model R) (FiniteUpdate.iidMeasure R hr)
        (FiniteUpdate.iidTrajectory R s₀) = ENNReal.ofReal (f (p s₀) : ℝ) := by
  rw [expectedHitCount_projection R Q p h hr hq s₀]
  exact FinitePotential.expectedHitCount_fixed_eq_of_equations (FiniteUpdate.model Q) f
    ⟨FiniteUpdate.kernel_nonnegative Q hq, FiniteUpdate.kernel_normalized Q hq⟩ ha hf
    (FiniteUpdate.iidMeasure Q hq) FiniteUpdate.inputHistory _
    (FiniteUpdate.iidRealization Q hq (p s₀)) (p s₀) (fun _ => rfl)

theorem checked_mean_bound (R : FiniteUpdate.Rule S I) (Q : FiniteUpdate.Rule A I)
    (p : S → A) (h : Commutes R Q p) (hr : FiniteUpdate.Valid R)
    (hq : FiniteUpdate.Valid Q) (s₀ : S) (W : FiniteDrift.Witness A)
    (hc : FiniteUpdate.check Q W = true) :
    FiniteDrift.expectedHitCount (FiniteUpdate.model R) (FiniteUpdate.iidMeasure R hr)
        (FiniteUpdate.iidTrajectory R s₀) ≤
      ENNReal.ofReal (W.potential (p s₀) : ℝ) / ENNReal.ofReal (W.delta : ℝ) := by
  rw [expectedHitCount_projection R Q p h hr hq s₀]
  exact FiniteDrift.expectedHitCount_fixed_le (FiniteUpdate.model Q) W hc
    (FiniteUpdate.iidMeasure Q hq) FiniteUpdate.inputHistory _
    (FiniteUpdate.iidRealization Q hq (p s₀)) (p s₀) (fun _ => rfl)

theorem checked_ae_success (R : FiniteUpdate.Rule S I) (Q : FiniteUpdate.Rule A I)
    (p : S → A) (h : Commutes R Q p) (hr : FiniteUpdate.Valid R)
    (hq : FiniteUpdate.Valid Q) (s₀ : S) (W : FiniteDrift.Witness A)
    (hc : FiniteUpdate.check Q W = true) :
    ∀ᵐ ω ∂FiniteUpdate.iidMeasure R hr, ∃ n, R.good (FiniteUpdate.iidTrajectory R s₀ n ω) = true := by
  rw [iidMeasure_eq R Q p h hr hq]
  have hh := FiniteDrift.ae_exists_good (FiniteUpdate.model Q) W hc
    (FiniteUpdate.iidMeasure Q hq) FiniteUpdate.inputHistory _
    (FiniteUpdate.iidRealization Q hq (p s₀))
  filter_upwards [hh] with ω hω
  obtain ⟨n, hn⟩ := hω
  exact ⟨n, by simpa only [FiniteUpdate.model, h.2.1, trajectory_projection R Q p h s₀] using hn⟩

theorem geometric_timeout_bound (R : FiniteUpdate.Rule S I) (Q : FiniteUpdate.Rule A I)
    (p : S → A) (h : Commutes R Q p) (hr : FiniteUpdate.Valid R)
    (hq : FiniteUpdate.Valid Q) (s₀ : S) (H : ℕ) (b : ℚ) (hb0 : 0 ≤ b)
    (hb : ∀ a, FinitePotential.survival (FiniteUpdate.model Q) H a ≤ b) (k : ℕ) :
    (FiniteUpdate.iidMeasure R hr)
        (FiniteDrift.runningEvent (FiniteUpdate.model R) (FiniteUpdate.iidTrajectory R s₀) (k * H)) ≤
      ENNReal.ofReal (b ^ k : ℝ) := by
  rw [timeout_exact R Q p h hr hq s₀ (k * H)]
  apply ENNReal.ofReal_le_ofReal
  exact_mod_cast FinitePotential.survival_blocks_le (FiniteUpdate.model Q)
    ⟨FiniteUpdate.kernel_nonnegative Q hq, FiniteUpdate.kernel_normalized Q hq⟩ H b hb0 hb k (p s₀)

theorem checkedClosedBad_ae_failure (R : FiniteUpdate.Rule S I) (Q : FiniteUpdate.Rule A I)
    (p : S → A) (h : Commutes R Q p) (hr : FiniteUpdate.Valid R)
    (hq : FiniteUpdate.Valid Q) (s₀ : S) (U : A → Bool)
    (hu : FinitePotential.checkClosedBad (FiniteUpdate.model Q) U = true)
    (hs : U (p s₀) = true) :
    ∀ᵐ ω ∂FiniteUpdate.iidMeasure R hr, ∀ n, R.good (FiniteUpdate.iidTrajectory R s₀ n ω) = false := by
  rw [iidMeasure_eq R Q p h hr hq]
  have hh := FinitePotential.ae_never_good_closedBad (FiniteUpdate.model Q)
    ⟨FiniteUpdate.kernel_nonnegative Q hq, FiniteUpdate.kernel_normalized Q hq⟩ U hu
    (FiniteUpdate.iidMeasure Q hq) FiniteUpdate.inputHistory _
    (FiniteUpdate.iidRealization Q hq (p s₀)) (p s₀) hs (fun _ => rfl)
  filter_upwards [hh] with ω hω
  intro n
  simpa only [FiniteUpdate.model, h.2.1, trajectory_projection R Q p h s₀] using hω n

theorem checkedClosedBad_mean_infinite (R : FiniteUpdate.Rule S I) (Q : FiniteUpdate.Rule A I)
    (p : S → A) (h : Commutes R Q p) (hr : FiniteUpdate.Valid R)
    (hq : FiniteUpdate.Valid Q) (s₀ : S) (U : A → Bool)
    (hu : FinitePotential.checkClosedBad (FiniteUpdate.model Q) U = true)
    (hs : U (p s₀) = true) :
    FiniteDrift.expectedHitCount (FiniteUpdate.model R) (FiniteUpdate.iidMeasure R hr)
        (FiniteUpdate.iidTrajectory R s₀) = ⊤ := by
  rw [expectedHitCount_projection R Q p h hr hq s₀]
  exact FinitePotential.expectedHitCount_closedBad_eq_top (FiniteUpdate.model Q)
    ⟨FiniteUpdate.kernel_nonnegative Q hq, FiniteUpdate.kernel_normalized Q hq⟩ U hu
    (FiniteUpdate.iidMeasure Q hq) FiniteUpdate.inputHistory _
    (FiniteUpdate.iidRealization Q hq (p s₀)) (p s₀) hs (fun _ => rfl)

end Measure

/-- Arbitrarily large or infinite passive state, without a joint transition table. -/
def withPassive {J : Type*} (Q : FiniteUpdate.Rule A I) (advance : A → J → I → J) :
    FiniteUpdate.Rule (A × J) I where
  mass := Q.mass
  update s i := (Q.update s.1 i, advance s.1 s.2 i)
  good s := Q.good s.1

theorem withPassive_commutes {J : Type*} (Q : FiniteUpdate.Rule A I)
    (advance : A → J → I → J) : Commutes (withPassive Q advance) Q Prod.fst :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

end FiniteLumpingUpdate

#check @FiniteLumpingUpdate.valid_iff
#check @FiniteLumpingUpdate.trajectory_projection
#check @FiniteLumpingUpdate.compatible_of_commutes
#check @FiniteLumpingUpdate.kernel_le_projected
#check @FiniteLumpingUpdate.positive_step_projects
#check @FiniteLumpingUpdate.reachable_good_projects
#check @FiniteLumpingUpdate.positive_step_lifts
#check @FiniteLumpingUpdate.reachable_lifts
#check @FiniteLumpingUpdate.reachable_good_iff
#check @FiniteLumpingUpdate.checkedClosedBad_no_path
#check @FiniteLumpingUpdate.runningEvent_projection
#check @FiniteLumpingUpdate.hitCount_projection
#check @FiniteLumpingUpdate.inputPMF_eq
#check @FiniteLumpingUpdate.iidMeasure_eq
#check @FiniteLumpingUpdate.projected_iidRealization
#check @FiniteLumpingUpdate.expectedHitCount_projection
#check @FiniteLumpingUpdate.timeout_exact
#check @FiniteLumpingUpdate.checkedTable_timeout_exact
#check @FiniteLumpingUpdate.mean_exact
#check @FiniteLumpingUpdate.checked_mean_bound
#check @FiniteLumpingUpdate.checked_ae_success
#check @FiniteLumpingUpdate.geometric_timeout_bound
#check @FiniteLumpingUpdate.checkedClosedBad_ae_failure
#check @FiniteLumpingUpdate.checkedClosedBad_mean_infinite
#check @FiniteLumpingUpdate.withPassive_commutes
