/-
  A finite product resampling rule and its exact rational transition matrix.

  Every variable has its own finite domain and rational distribution. A
  state-dependent footprint selects the coordinates resampled. Successful
  states are stopped. This covers any deterministic memoryless selection
  of violated events, once its admissibility is proved; it does not impose
  full footprints or an LLL/Shearer/HLS probability condition.

  The kernel is the pushforward of the product law through the existing
  coordinate resampling operation. Its closed form multiplies only the
  selected-coordinate probabilities, and is zero if an unselected
  coordinate changes. Source: Moser--Tardos, arXiv:0903.0544v3, Algorithm 1.1.
-/

module

public import PPGraph.Finite.Update.IID
public import PPGraph.MoserTardos.Process.Process
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

set_option linter.unusedSectionVars false

open MeasureTheory
open scoped ENNReal NNReal

namespace FiniteResampling

variable {V : Type} [Fintype V] [DecidableEq V]
  {D : V → Type} [∀ v, Fintype (D v)] [∀ v, DecidableEq (D v)]

abbrev State (D : V → Type) := ∀ v, D v

structure Marginals (D : V → Type) where
  mass : ∀ v, D v → ℚ

def Valid (Q : Marginals D) : Prop :=
  (∀ v x, 0 ≤ Q.mass v x) ∧ ∀ v, ∑ x, Q.mass v x = 1

instance validDecidable (Q : Marginals D) : Decidable (Valid Q) :=
  inferInstanceAs (Decidable (_ ∧ _))

def productMass (Q : Marginals D) (fresh : State D) : ℚ :=
  ∏ v, Q.mass v (fresh v)

theorem productMass_nonnegative (Q : Marginals D) (h : Valid Q) (fresh : State D) :
    0 ≤ productMass Q fresh := Finset.prod_nonneg (fun v _ => h.1 v (fresh v))

theorem productMass_normalized (Q : Marginals D) (h : Valid Q) :
    ∑ fresh : State D, productMass Q fresh = 1 := by
  change (∑ fresh : ∀ v, D v, ∏ v, Q.mass v (fresh v)) = 1
  rw [← Fintype.prod_sum]
  simp [h.2]

def coordinateUpdate (F : Finset V) (s fresh : State D) : State D :=
  fun v => if v ∈ F then fresh v else s v

theorem coordinateUpdate_selected (F : Finset V) (s fresh : State D)
    (v : V) (hv : v ∈ F) : coordinateUpdate F s fresh v = fresh v := by
  simp [coordinateUpdate, hv]

theorem coordinateUpdate_unselected (F : Finset V) (s fresh : State D)
    (v : V) (hv : v ∉ F) : coordinateUpdate F s fresh v = s v := by
  simp [coordinateUpdate, hv]

theorem coordinateUpdate_eq_resample (S : VarSpaces V) (F : Finset V)
    (s fresh : MTState S) : coordinateUpdate F s fresh = resample F s fresh := rfl

structure Policy (D : V → Type) where
  good : State D → Bool
  footprint : State D → Finset V

def activeFootprint (P : Policy D) (s : State D) : Finset V :=
  if P.good s then ∅ else P.footprint s

def rule (Q : Marginals D) (P : Policy D) : FiniteUpdate.Rule (State D) (State D) where
  mass := productMass Q
  update s fresh := coordinateUpdate (activeFootprint P s) s fresh
  good := P.good

theorem rule_valid (Q : Marginals D) (h : Valid Q) (P : Policy D) :
    FiniteUpdate.Valid (rule Q P) :=
  ⟨productMass_nonnegative Q h, productMass_normalized Q h⟩

/-- Validate the sampling distribution as well as the update-derived drift witness. -/
def check (Q : Marginals D) (P : Policy D) (W : FiniteDrift.Witness (State D)) : Bool :=
  decide (Valid Q) && FiniteUpdate.check (rule Q P) W

theorem check_eq_true_iff (Q : Marginals D) (P : Policy D)
    (W : FiniteDrift.Witness (State D)) :
    check Q P W = true ↔ Valid Q ∧ FiniteUpdate.check (rule Q P) W = true := by
  simp only [check, Bool.and_eq_true, decide_eq_true_iff]

theorem check_sound (Q : Marginals D) (P : Policy D)
    (W : FiniteDrift.Witness (State D)) (h : check Q P W = true) :
    Valid Q ∧ FiniteUpdate.check (rule Q P) W = true :=
  (check_eq_true_iff Q P W).mp h

theorem rule_update_good (Q : Marginals D) (P : Policy D) (s fresh : State D)
    (hs : P.good s = true) : (rule Q P).update s fresh = s := by
  funext v
  simp [rule, coordinateUpdate, activeFootprint, hs]

theorem rule_update_bad (Q : Marginals D) (P : Policy D) (s fresh : State D)
    (hs : P.good s = false) :
    (rule Q P).update s fresh = coordinateUpdate (P.footprint s) s fresh := by
  simp [rule, activeFootprint, hs]

theorem kernel_good (Q : Marginals D) (h : Valid Q) (P : Policy D) (s t : State D)
    (hs : P.good s = true) :
    FiniteUpdate.kernel (rule Q P) s t = if s = t then 1 else 0 :=
  FiniteUpdate.kernel_eq_pure_of_fixed (rule Q P) (rule_valid Q h P) s
    (rule_update_good Q P s · hs) t

theorem kernel_zero_unselected (Q : Marginals D) (P : Policy D) (s t : State D)
    (v : V) (hv : v ∉ activeFootprint P s) (hne : s v ≠ t v) :
    FiniteUpdate.kernel (rule Q P) s t = 0 := by
  apply FiniteUpdate.kernel_zero_of_unreachable
  intro fresh heq
  have hc := congrFun heq v
  exact hne (by simpa [rule, coordinateUpdate, hv] using hc)

/-- Factorization of the fiber indicator over the finite variable set. -/
theorem coordinate_fiber_product (Q : Marginals D) (F : Finset V)
    (s t fresh : State D) :
    (if coordinateUpdate F s fresh = t then productMass Q fresh else 0) =
      ∏ v, if (if v ∈ F then fresh v else s v) = t v then Q.mass v (fresh v) else 0 := by
  by_cases heq : coordinateUpdate F s fresh = t
  · have hv (v : V) : (if v ∈ F then fresh v else s v) = t v := congrFun heq v
    simp only [heq, ↓reduceIte, hv, productMass]
  · have hnot : ¬ ∀ v, (if v ∈ F then fresh v else s v) = t v := by
      intro hh
      exact heq (funext hh)
    obtain ⟨v, hv⟩ := not_forall.mp hnot
    rw [ite_eq_right heq]
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ v) (ite_eq_right hv)

/-- A closed form: unchanged outside the footprint; product law inside it. -/
theorem kernel_eq_coordinate_product (Q : Marginals D) (h : Valid Q) (P : Policy D)
    (s t : State D) :
    FiniteUpdate.kernel (rule Q P) s t =
      ∏ v, if v ∈ activeFootprint P s then Q.mass v (t v)
        else if s v = t v then 1 else 0 := by
  change (∑ fresh : State D,
      if coordinateUpdate (activeFootprint P s) s fresh = t then productMass Q fresh else 0) = _
  simp_rw [coordinate_fiber_product]
  rw [← Fintype.prod_sum (fun (v : V) (x : D v) =>
    if (if v ∈ activeFootprint P s then x else s v) = t v then Q.mass v x else 0)]
  apply Finset.prod_congr rfl
  intro v _
  by_cases hv : v ∈ activeFootprint P s
  · simp [hv]
  · simp [hv, Finset.sum_ite_irrel, h.2]

/-- Every event depends on its declared coordinates; selection changes no contract. -/
structure Problem (D : V → Type) (I : Type) where
  bad : I → State D → Bool
  footprint : I → Finset V
  depends : ∀ i s t, (∀ v ∈ footprint i, s v = t v) → bad i s = bad i t

variable {I : Type} [Fintype I]

def allGood (B : Problem D I) (s : State D) : Bool :=
  decide (∀ i, B.bad i s = false)

def Admissible (B : Problem D I) (choose : State D → I) : Prop :=
  ∀ s, allGood B s = false → B.bad (choose s) s = true

def selectedPolicy (B : Problem D I) (choose : State D → I) : Policy D where
  good := allGood B
  footprint s := B.footprint (choose s)

theorem allGood_eq_true_iff (B : Problem D I) (s : State D) :
    allGood B s = true ↔ ∀ i, B.bad i s = false := decide_eq_true_iff

theorem selected_rule_resamples_violated (Q : Marginals D) (B : Problem D I)
    (choose : State D → I) (hc : Admissible B choose) (s fresh : State D)
    (hs : allGood B s = false) :
    B.bad (choose s) s = true ∧
      (rule Q (selectedPolicy B choose)).update s fresh =
        coordinateUpdate (B.footprint (choose s)) s fresh :=
  ⟨hc s hs, rule_update_bad Q (selectedPolicy B choose) s fresh hs⟩

theorem selected_rule_preserves_unrelated (Q : Marginals D) (B : Problem D I)
    (choose : State D → I) (s fresh : State D) (j : I)
    (hd : Disjoint (activeFootprint (selectedPolicy B choose) s) (B.footprint j)) :
    B.bad j ((rule Q (selectedPolicy B choose)).update s fresh) = B.bad j s := by
  apply B.depends
  intro v hv
  have hnot : v ∉ activeFootprint (selectedPolicy B choose) s := by
    intro hmem
    exact Finset.disjoint_left.mp hd hmem hv
  exact coordinateUpdate_unselected _ s fresh v hnot

section IndependentExecution

variable [∀ v, MeasurableSpace (D v)] [∀ v, MeasurableSingletonClass (D v)]

noncomputable def marginalPMF (Q : Marginals D) (h : Valid Q) (v : V) : PMF (D v) :=
  PMF.ofFintype (fun x => ENNReal.ofReal (Q.mass v x : ℝ)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg]
    · have hn : (∑ x, (Q.mass v x : ℝ)) = 1 := by exact_mod_cast h.2 v
      rw [hn, ENNReal.ofReal_one]
    · intro x _
      exact_mod_cast h.1 v x)

noncomputable def varSpaces (Q : Marginals D) (h : Valid Q) : VarSpaces V where
  space := D
  measSpace _v := inferInstance
  measure v := (marginalPMF Q h v).toMeasure
  isProb _v := inferInstance

theorem marginalPMF_apply (Q : Marginals D) (h : Valid Q) (v : V) (x : D v) :
    marginalPMF Q h v x = ENNReal.ofReal (Q.mass v x : ℝ) := rfl

/-- The fresh-row law is exactly the declared product of the variable laws. -/
theorem inputMeasure_eq_product (Q : Marginals D) (h : Valid Q) (P : Policy D) :
    (FiniteUpdate.inputPMF (rule Q P) (rule_valid Q h P)).toMeasure =
      Measure.pi (fun v => (marginalPMF Q h v).toMeasure) := by
  apply Measure.ext_of_singleton
  intro fresh
  rw [PMF.toMeasure_apply_singleton _ fresh (measurableSet_singleton fresh),
    Measure.pi_singleton]
  change ENNReal.ofReal ((productMass Q fresh : ℚ) : ℝ) = _
  simp only [productMass, Rat.cast_prod]
  rw [ENNReal.ofReal_prod_of_nonneg]
  · apply Finset.prod_congr rfl
    intro v _
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), marginalPMF_apply]
  · intro v _
    exact_mod_cast h.1 v (fresh v)

/-- Embed the very same Boolean events and footprints in the existing MT framework. -/
noncomputable def mtProcess (Q : Marginals D) (h : Valid Q) (B : Problem D I) :
    MTProcess (varSpaces Q h) I where
  bad i := {s | B.bad i s = true}
  footprint := B.footprint
  dep i s t hagree := by
    change B.bad i s = true ↔ B.bad i t = true
    rw [B.depends i s t hagree]

theorem mtProcess_bad_iff (Q : Marginals D) (h : Valid Q) (B : Problem D I)
    (i : I) (s : State D) : s ∈ (mtProcess Q h B).bad i ↔ B.bad i s = true := Iff.rfl

theorem allGood_iff_no_mt_violation (Q : Marginals D) (h : Valid Q) (B : Problem D I)
    (s : State D) : allGood B s = true ↔ violated (mtProcess Q h B) s = ∅ := by
  rw [allGood_eq_true_iff]
  simp only [violated, mtProcess, Set.eq_empty_iff_forall_notMem, Set.mem_ofPred_eq]
  exact forall_congr' (fun i => Bool.eq_false_iff)

theorem selected_update_eq_mt_resample (Q : Marginals D) (h : Valid Q)
    (B : Problem D I) (choose : State D → I) (s fresh : State D)
    (hs : allGood B s = false) :
    (rule Q (selectedPolicy B choose)).update s fresh =
      resample (S := varSpaces Q h) ((mtProcess Q h B).footprint (choose s)) s fresh := by
  rw [rule_update_bad Q (selectedPolicy B choose) s fresh hs]
  rfl

/-- A concrete law derived from the resampling rule, with no realization premise. -/
theorem resampling_iid_realization (Q : Marginals D) (h : Valid Q) (P : Policy D)
    (s₀ : State D) :
    FiniteDrift.Realization (FiniteUpdate.model (rule Q P))
      (FiniteUpdate.iidMeasure (rule Q P) (rule_valid Q h P))
      (FiniteUpdate.inputHistory (A := State D))
      (FiniteUpdate.iidTrajectory (rule Q P) s₀) :=
  FiniteUpdate.iidRealization (rule Q P) (rule_valid Q h P) s₀

theorem resampling_iid_expectedHitCount_le (Q : Marginals D) (h : Valid Q)
    (P : Policy D) (W : FiniteDrift.Witness (State D))
    (hc : FiniteUpdate.check (rule Q P) W = true) (s₀ : State D) :
    FiniteDrift.expectedHitCount (FiniteUpdate.model (rule Q P))
      (FiniteUpdate.iidMeasure (rule Q P) (rule_valid Q h P))
      (FiniteUpdate.iidTrajectory (rule Q P) s₀) ≤
      ENNReal.ofReal (W.potential s₀ : ℝ) / ENNReal.ofReal (W.delta : ℝ) :=
  FiniteUpdate.iid_expectedHitCount_le (rule Q P) (rule_valid Q h P) W hc s₀

theorem resampling_iid_expectedHitCount_lt_top (Q : Marginals D) (h : Valid Q)
    (P : Policy D) (W : FiniteDrift.Witness (State D))
    (hc : FiniteUpdate.check (rule Q P) W = true) (s₀ : State D) :
    FiniteDrift.expectedHitCount (FiniteUpdate.model (rule Q P))
      (FiniteUpdate.iidMeasure (rule Q P) (rule_valid Q h P))
      (FiniteUpdate.iidTrajectory (rule Q P) s₀) < ⊤ :=
  FiniteUpdate.iid_expectedHitCount_lt_top (rule Q P) (rule_valid Q h P) W hc s₀

theorem resampling_iid_ae_exists_good (Q : Marginals D) (h : Valid Q)
    (P : Policy D) (W : FiniteDrift.Witness (State D))
    (hc : FiniteUpdate.check (rule Q P) W = true) (s₀ : State D) :
    ∀ᵐ ω ∂FiniteUpdate.iidMeasure (rule Q P) (rule_valid Q h P),
      ∃ T, P.good (FiniteUpdate.iidTrajectory (rule Q P) s₀ T ω) = true :=
  FiniteUpdate.iid_ae_exists_good (rule Q P) (rule_valid Q h P) W hc s₀

/-- With an admissible policy, every active step really resamples a violated event. -/
theorem selected_iid_active_step (Q : Marginals D) (B : Problem D I)
    (choose : State D → I) (hc : Admissible B choose) (s₀ : State D)
    (n : ℕ) (ω : ℕ → State D)
    (hs : allGood B (FiniteUpdate.iidTrajectory (rule Q (selectedPolicy B choose))
      s₀ n ω) = false) :
    let s := FiniteUpdate.iidTrajectory (rule Q (selectedPolicy B choose)) s₀ n ω
    B.bad (choose s) s = true ∧
      FiniteUpdate.iidTrajectory (rule Q (selectedPolicy B choose)) s₀ (n + 1) ω =
        coordinateUpdate (B.footprint (choose s)) s (ω n) :=
  selected_rule_resamples_violated Q B choose hc _ (ω n) hs

theorem selected_iid_ae_avoids_all (Q : Marginals D) (h : Valid Q)
    (B : Problem D I) (choose : State D → I) (W : FiniteDrift.Witness (State D))
    (hc : FiniteUpdate.check (rule Q (selectedPolicy B choose)) W = true)
    (s₀ : State D) :
    ∀ᵐ ω ∂FiniteUpdate.iidMeasure (rule Q (selectedPolicy B choose))
        (rule_valid Q h (selectedPolicy B choose)),
      ∃ T, ∀ i, B.bad i (FiniteUpdate.iidTrajectory
        (rule Q (selectedPolicy B choose)) s₀ T ω) = false := by
  filter_upwards [resampling_iid_ae_exists_good Q h (selectedPolicy B choose) W hc s₀]
    with ω hω
  obtain ⟨T, hT⟩ := hω
  exact ⟨T, (allGood_eq_true_iff B _).mp hT⟩

theorem checked_resampling_expectedHitCount_le (Q : Marginals D) (P : Policy D)
    (W : FiniteDrift.Witness (State D)) (hc : check Q P W = true) (s₀ : State D) :
    FiniteDrift.expectedHitCount (FiniteUpdate.model (rule Q P))
      (FiniteUpdate.iidMeasure (rule Q P) (rule_valid Q (check_sound Q P W hc).1 P))
      (FiniteUpdate.iidTrajectory (rule Q P) s₀) ≤
      ENNReal.ofReal (W.potential s₀ : ℝ) / ENNReal.ofReal (W.delta : ℝ) :=
  resampling_iid_expectedHitCount_le Q (check_sound Q P W hc).1 P W
    (check_sound Q P W hc).2 s₀

theorem checked_resampling_expectedHitCount_lt_top (Q : Marginals D) (P : Policy D)
    (W : FiniteDrift.Witness (State D)) (hc : check Q P W = true) (s₀ : State D) :
    FiniteDrift.expectedHitCount (FiniteUpdate.model (rule Q P))
      (FiniteUpdate.iidMeasure (rule Q P) (rule_valid Q (check_sound Q P W hc).1 P))
      (FiniteUpdate.iidTrajectory (rule Q P) s₀) < ⊤ :=
  resampling_iid_expectedHitCount_lt_top Q (check_sound Q P W hc).1 P W
    (check_sound Q P W hc).2 s₀

theorem checked_resampling_ae_exists_good (Q : Marginals D) (P : Policy D)
    (W : FiniteDrift.Witness (State D)) (hc : check Q P W = true) (s₀ : State D) :
    ∀ᵐ ω ∂FiniteUpdate.iidMeasure (rule Q P)
        (rule_valid Q (check_sound Q P W hc).1 P),
      ∃ T, P.good (FiniteUpdate.iidTrajectory (rule Q P) s₀ T ω) = true :=
  resampling_iid_ae_exists_good Q (check_sound Q P W hc).1 P W
    (check_sound Q P W hc).2 s₀

end IndependentExecution

end FiniteResampling

#check @FiniteResampling.productMass_nonnegative
#check @FiniteResampling.productMass_normalized
#check @FiniteResampling.coordinateUpdate_selected
#check @FiniteResampling.coordinateUpdate_unselected
#check @FiniteResampling.coordinateUpdate_eq_resample
#check @FiniteResampling.rule_valid
#check @FiniteResampling.check_eq_true_iff
#check @FiniteResampling.check_sound
#check @FiniteResampling.rule_update_good
#check @FiniteResampling.rule_update_bad
#check @FiniteResampling.kernel_good
#check @FiniteResampling.kernel_zero_unselected
#check @FiniteResampling.coordinate_fiber_product
#check @FiniteResampling.kernel_eq_coordinate_product
#check @FiniteResampling.allGood_eq_true_iff
#check @FiniteResampling.selected_rule_resamples_violated
#check @FiniteResampling.selected_rule_preserves_unrelated
#check @FiniteResampling.marginalPMF_apply
#check @FiniteResampling.inputMeasure_eq_product
#check @FiniteResampling.mtProcess_bad_iff
#check @FiniteResampling.allGood_iff_no_mt_violation
#check @FiniteResampling.selected_update_eq_mt_resample
#check @FiniteResampling.resampling_iid_realization
#check @FiniteResampling.resampling_iid_expectedHitCount_le
#check @FiniteResampling.resampling_iid_expectedHitCount_lt_top
#check @FiniteResampling.resampling_iid_ae_exists_good
#check @FiniteResampling.selected_iid_active_step
#check @FiniteResampling.selected_iid_ae_avoids_all
#check @FiniteResampling.checked_resampling_expectedHitCount_le
#check @FiniteResampling.checked_resampling_expectedHitCount_lt_top
#check @FiniteResampling.checked_resampling_ae_exists_good
