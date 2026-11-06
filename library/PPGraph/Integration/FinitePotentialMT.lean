/-
  Automatically synthesized potentials for the existing finite MT process.

  The model matrix is derived from the actual coordinate resampling rule.
  Rational marginals, finite domains and a deterministic memoryless policy
  are required. Good states stop resampling. Positive-mass accessibility
  from every state is sufficient AND necessary for a global checked drift
  witness for this fixed kernel. This is not a claim about other policies.

  The counter-table law and TLog bridge are reused, so the expected-work
  conclusion concerns the existing MT process, not only an exported matrix.
  No LLL/Shearer/HLS condition or externally supplied potential is used.
-/

module

public import PPGraph.Finite.Potential.Basic
public import PPGraph.Integration.FiniteMTDrift

@[expose] public section

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped ENNReal NNReal

namespace FiniteResampling

variable {V : Type} [Fintype V] [DecidableEq V]
  {D : V → Type} [∀ v, Fintype (D v)] [∀ v, DecidableEq (D v)]

def synthesizePotential (Q : Marginals D) (P : Policy D) :
    Option (FiniteDrift.Witness (State D)) :=
  if decide (Valid Q) then FinitePotential.synthesize (FiniteUpdate.model (rule Q P)) else none

theorem model_stochastic (Q : Marginals D) (h : Valid Q) (P : Policy D) :
    FinitePotential.Stochastic (FiniteUpdate.model (rule Q P)) :=
  ⟨FiniteUpdate.kernel_nonnegative _ (rule_valid Q h P),
    FiniteUpdate.kernel_normalized _ (rule_valid Q h P)⟩

theorem model_absorbing (Q : Marginals D) (h : Valid Q) (P : Policy D) :
    FinitePotential.Absorbing (FiniteUpdate.model (rule Q P)) := by
  intro s t hs ht
  change FiniteUpdate.kernel (rule Q P) s t = 0
  change P.good s = true at hs
  change P.good t = false at ht
  rw [kernel_good Q h P s t hs]
  have hne : s ≠ t := by
    intro he
    subst t
    exact Bool.false_ne_true (ht.symm.trans hs)
  simp [hne]

theorem candidate_check_of_accessible (Q : Marginals D) (h : Valid Q) (P : Policy D)
    (hr : FinitePotential.Accessible (FiniteUpdate.model (rule Q P))) :
    check Q P (FinitePotential.candidate (FiniteUpdate.model (rule Q P))) = true := by
  apply (check_eq_true_iff Q P _).mpr
  exact ⟨h, (FinitePotential.candidate_checked_iff_accessible _
    (model_stochastic Q h P) (model_absorbing Q h P)).mpr hr⟩

theorem synthesizePotential_sound (Q : Marginals D) (P : Policy D)
    (W : FiniteDrift.Witness (State D)) (hs : synthesizePotential Q P = some W) :
    check Q P W = true := by
  unfold synthesizePotential at hs
  split_ifs at hs with hv
  apply (check_eq_true_iff Q P W).mpr
  exact ⟨of_decide_eq_true hv, FinitePotential.synthesize_sound _ W hs⟩

theorem synthesizePotential_complete (Q : Marginals D) (h : Valid Q) (P : Policy D)
    (hr : FinitePotential.Accessible (FiniteUpdate.model (rule Q P))) :
    synthesizePotential Q P = some (FinitePotential.candidate (FiniteUpdate.model (rule Q P))) := by
  simp only [synthesizePotential, h, decide_true, ↓reduceIte]
  exact FinitePotential.synthesize_complete _ (model_stochastic Q h P) (model_absorbing Q h P) hr

theorem synthesizePotential_iff_accessible (Q : Marginals D) (h : Valid Q) (P : Policy D) :
    (∃ W, synthesizePotential Q P = some W) ↔
      FinitePotential.Accessible (FiniteUpdate.model (rule Q P)) := by
  constructor
  · rintro ⟨W, hs⟩
    exact FinitePotential.checked_accessible _ W (check_sound _ _ _
      (synthesizePotential_sound Q P W hs)).2
  · intro hr
    exact ⟨_, synthesizePotential_complete Q h P hr⟩

variable [∀ v, MeasurableSpace (D v)] [∀ v, MeasurableSingletonClass (D v)]
  {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]

theorem synthesized_ETLog_le (Q : Marginals D) (h : Valid Q) (B : Problem D I)
    (W : FiniteDrift.Witness (State D))
    (hs : synthesizePotential Q (firstPolicy Q h B) = some W) (s₀ : State D) :
    ETLog (mtProcess Q h B) s₀ ≤
      ENNReal.ofReal (W.potential s₀ : ℝ) / ENNReal.ofReal (W.delta : ℝ) :=
  checked_ETLog_le Q h B W (synthesizePotential_sound _ _ _ hs) s₀

theorem synthesized_ETLog_lt_top (Q : Marginals D) (h : Valid Q) (B : Problem D I)
    (W : FiniteDrift.Witness (State D))
    (hs : synthesizePotential Q (firstPolicy Q h B) = some W) (s₀ : State D) :
    ETLog (mtProcess Q h B) s₀ < ⊤ :=
  checked_ETLog_lt_top Q h B W (synthesizePotential_sound _ _ _ hs) s₀

theorem synthesized_randomInitETLog_le (Q : Marginals D) (h : Valid Q) (B : Problem D I)
    (W : FiniteDrift.Witness (State D))
    (hs : synthesizePotential Q (firstPolicy Q h B) = some W) :
    randomInitETLog (mtProcess Q h B) ≤
      ENNReal.ofReal (∫ ω, (W.potential (initialStateFromLog ω) : ℝ)
        ∂logMeasure (varSpaces Q h)) / ENNReal.ofReal (W.delta : ℝ) :=
  checked_randomInitETLog_le Q h B W (synthesizePotential_sound _ _ _ hs)

theorem synthesized_randomInitETLog_lt_top (Q : Marginals D) (h : Valid Q) (B : Problem D I)
    (W : FiniteDrift.Witness (State D))
    (hs : synthesizePotential Q (firstPolicy Q h B) = some W) :
    randomInitETLog (mtProcess Q h B) < ⊤ :=
  checked_randomInitETLog_lt_top Q h B W (synthesizePotential_sound _ _ _ hs)

theorem accessible_ETLog_le_potential (Q : Marginals D) (h : Valid Q) (B : Problem D I)
    (hr : FinitePotential.Accessible (FiniteUpdate.model (rule Q (firstPolicy Q h B))))
    (s₀ : State D) :
    ETLog (mtProcess Q h B) s₀ ≤ ENNReal.ofReal
      (FinitePotential.potential (FiniteUpdate.model (rule Q (firstPolicy Q h B))) s₀ : ℝ) := by
  have hb := checked_ETLog_le Q h B _ (candidate_check_of_accessible Q h _ hr) s₀
  simpa [FinitePotential.candidate] using hb

theorem accessible_randomInitETLog_lt_top (Q : Marginals D) (h : Valid Q) (B : Problem D I)
    (hr : FinitePotential.Accessible (FiniteUpdate.model (rule Q (firstPolicy Q h B)))) :
    randomInitETLog (mtProcess Q h B) < ⊤ :=
  checked_randomInitETLog_lt_top Q h B _ (candidate_check_of_accessible Q h _ hr)

theorem accessible_randomInitETLog_le_potential (Q : Marginals D) (h : Valid Q)
    (B : Problem D I)
    (hr : FinitePotential.Accessible (FiniteUpdate.model (rule Q (firstPolicy Q h B)))) :
    randomInitETLog (mtProcess Q h B) ≤ ENNReal.ofReal
      (∫ ω, (FinitePotential.potential (FiniteUpdate.model (rule Q (firstPolicy Q h B)))
        (initialStateFromLog ω) : ℝ) ∂logMeasure (varSpaces Q h)) := by
  have hb := checked_randomInitETLog_le Q h B _ (candidate_check_of_accessible Q h _ hr)
  simpa [FinitePotential.candidate] using hb

theorem accessible_randTraj_ae_exists_good (Q : Marginals D) (h : Valid Q)
    (B : Problem D I)
    (hr : FinitePotential.Accessible (FiniteUpdate.model (rule Q (firstPolicy Q h B))))
    (s₀ : State D) :
    ∀ᵐ ω ∂logMeasure (varSpaces Q h),
      ∃ T, MTGood (mtProcess Q h B) (randTraj (mtProcess Q h B) s₀ ω T) :=
  checked_randTraj_ae_exists_good Q h B _ (candidate_check_of_accessible Q h _ hr) s₀

theorem accessible_randomInit_randTraj_ae_exists_good (Q : Marginals D) (h : Valid Q)
    (B : Problem D I)
    (hr : FinitePotential.Accessible (FiniteUpdate.model (rule Q (firstPolicy Q h B)))) :
    ∀ᵐ ω ∂logMeasure (varSpaces Q h), ∃ T, MTGood (mtProcess Q h B)
      (randTraj (mtProcess Q h B) (initialStateFromLog ω) ω T) :=
  checked_randomInit_randTraj_ae_exists_good Q h B _ (candidate_check_of_accessible Q h _ hr)

end FiniteResampling

#check @FiniteResampling.model_stochastic
#check @FiniteResampling.model_absorbing
#check @FiniteResampling.candidate_check_of_accessible
#check @FiniteResampling.synthesizePotential_sound
#check @FiniteResampling.synthesizePotential_complete
#check @FiniteResampling.synthesizePotential_iff_accessible
#check @FiniteResampling.synthesized_ETLog_le
#check @FiniteResampling.synthesized_ETLog_lt_top
#check @FiniteResampling.synthesized_randomInitETLog_le
#check @FiniteResampling.synthesized_randomInitETLog_lt_top
#check @FiniteResampling.accessible_ETLog_le_potential
#check @FiniteResampling.accessible_randomInitETLog_lt_top
#check @FiniteResampling.accessible_randomInitETLog_le_potential
#check @FiniteResampling.accessible_randTraj_ae_exists_good
#check @FiniteResampling.accessible_randomInit_randTraj_ae_exists_good
