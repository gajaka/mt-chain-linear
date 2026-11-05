/-
  Automatic exact potential synthesis by first-step hitting-time equations.

  Sources: Mitzenmacher--Upfal, Probability and Computing, 2nd ed.,
  Section 7.1.1, pp. 173--174, and Exercise 7.25, p. 202;
  Levin--Peres, Markov Chains and Mixing Times, 2nd ed., Exercise 10.22,
  p. 149. Good states have value zero. At a bad state the value is one
  plus its transition-weighted successor values.

  Rational Cramer's rule computes a candidate. Every returned witness
  passes the existing exact drift checker. Its soundness does not trust
  an external linear-system solver. These are finite model statements;
  they do not identify a physical controller's transition law.
-/

module

public import PPGraph.Finite.Drift.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Data.Finset.Max
public import Mathlib.Logic.Relation

@[expose] public section

set_option linter.unusedSectionVars false

open scoped Matrix

namespace FinitePotential

variable {S : Type*} [Fintype S] [DecidableEq S]

def Stochastic (M : FiniteDrift.Model S) : Prop :=
  (∀ s t, 0 ≤ M.transition s t) ∧ ∀ s, ∑ t, M.transition s t = 1

def Absorbing (M : FiniteDrift.Model S) : Prop :=
  ∀ s t, M.good s = true → M.good t = false → M.transition s t = 0

def Equations (M : FiniteDrift.Model S) (f : S → ℚ) : Prop :=
  (∀ s, M.good s = true → f s = 0) ∧
  ∀ s, M.good s = false → f s = 1 + ∑ t, M.transition s t * f t

def systemMatrix (M : FiniteDrift.Model S) : Matrix S S ℚ :=
  fun s t => if M.good s then (if s = t then 1 else 0)
    else (if s = t then 1 else 0) - M.transition s t

def systemRHS (M : FiniteDrift.Model S) : S → ℚ :=
  fun s => if M.good s then 0 else 1

/-- Executable rational Cramer's rule; no noncomputable matrix inverse. -/
def potential (M : FiniteDrift.Model S) : S → ℚ :=
  (systemMatrix M).det⁻¹ • (systemMatrix M).cramer (systemRHS M)

def candidate (M : FiniteDrift.Model S) : FiniteDrift.Witness S :=
  ⟨potential M, 1⟩

/-- A failed attempt returns no witness, never a no-repair verdict. -/
def synthesize (M : FiniteDrift.Model S) : Option (FiniteDrift.Witness S) :=
  if FiniteDrift.check M (candidate M) then some (candidate M) else none

theorem systemMatrix_mulVec (M : FiniteDrift.Model S) (f : S → ℚ) (s : S) :
    (systemMatrix M *ᵥ f) s =
      if M.good s then f s else f s - ∑ t, M.transition s t * f t := by
  cases hs : M.good s <;>
    simp [systemMatrix, Matrix.mulVec, dotProduct, hs, sub_mul,
      Finset.sum_sub_distrib]

theorem matrix_equations_iff (M : FiniteDrift.Model S) (f : S → ℚ) :
    systemMatrix M *ᵥ f = systemRHS M ↔ Equations M f := by
  constructor
  · intro he
    constructor
    · intro s hs
      have hh := congrFun he s
      simpa [systemMatrix_mulVec, systemRHS, hs] using hh
    · intro s hs
      have hh := congrFun he s
      simp only [systemMatrix_mulVec, systemRHS, hs, Bool.false_eq_true,
        ↓reduceIte] at hh
      linarith
  · intro he
    funext s
    rw [systemMatrix_mulVec]
    cases hs : M.good s
    · have hh := he.2 s hs
      simp only [systemRHS, hs, Bool.false_eq_true, ↓reduceIte]
      linarith
    · simpa [systemRHS, hs] using he.1 s hs

theorem potential_solves (M : FiniteDrift.Model S)
    (hd : (systemMatrix M).det ≠ 0) :
    systemMatrix M *ᵥ potential M = systemRHS M := by
  rw [potential, Matrix.mulVec_smul, Matrix.mulVec_cramer, smul_smul,
    inv_mul_cancel₀ hd, one_smul]

theorem potential_equations (M : FiniteDrift.Model S)
    (hd : (systemMatrix M).det ≠ 0) : Equations M (potential M) :=
  (matrix_equations_iff M _).mp (potential_solves M hd)

/-- A finite solution cannot have a negative minimum. -/
theorem solution_nonnegative (M : FiniteDrift.Model S) (hm : Stochastic M)
    (f : S → ℚ) (he : Equations M f) (s : S) : 0 ≤ f s := by
  by_contra hn
  have hs : f s < 0 := lt_of_not_ge hn
  obtain ⟨m, _, hmin⟩ := Finset.exists_min_image Finset.univ f
    ⟨s, Finset.mem_univ s⟩
  have hms : f m ≤ f s := hmin s (Finset.mem_univ s)
  have hbad : M.good m = false := by
    cases hh : M.good m
    · rfl
    · have hz := he.1 m hh
      linarith
  have hsum : f m ≤ ∑ t, M.transition m t * f t := by
    calc
      f m = ∑ t, M.transition m t * f m := by rw [← Finset.sum_mul, hm.2 m, one_mul]
      _ ≤ _ := Finset.sum_le_sum (fun t _ =>
        mul_le_mul_of_nonneg_left (hmin t (Finset.mem_univ t)) (hm.1 m t))
  have heq := he.2 m hbad
  linarith

theorem solution_checked (M : FiniteDrift.Model S) (hm : Stochastic M)
    (ha : Absorbing M) (f : S → ℚ) (he : Equations M f) :
    FiniteDrift.check M ⟨f, 1⟩ = true := by
  apply FiniteDrift.check_complete
  refine ⟨hm.1, hm.2, solution_nonnegative M hm f he, he.1, by norm_num, ?_⟩
  intro s
  cases hs : M.good s
  · have hh := he.2 s hs
    simp only [FiniteDrift.localExpectation, Bool.false_eq_true, ↓reduceIte]
    change (∑ t, M.transition s t * f t) + 1 ≤ f s
    linarith
  · have hz : ∑ t, M.transition s t * f t = 0 := by
      apply Finset.sum_eq_zero
      intro t _
      cases ht : M.good t
      · rw [ha s t hs ht, zero_mul]
      · rw [he.1 t ht, mul_zero]
    simp [FiniteDrift.localExpectation, hz, he.1 s hs]

theorem candidate_checked (M : FiniteDrift.Model S) (hm : Stochastic M)
    (ha : Absorbing M) (hd : (systemMatrix M).det ≠ 0) :
    FiniteDrift.check M (candidate M) = true :=
  solution_checked M hm ha _ (potential_equations M hd)

theorem synthesize_sound (M : FiniteDrift.Model S) (W : FiniteDrift.Witness S)
    (hs : synthesize M = some W) : FiniteDrift.check M W = true := by
  unfold synthesize at hs
  split_ifs at hs with hc
  · cases Option.some.inj hs
    exact hc

theorem synthesize_eq_some_candidate (M : FiniteDrift.Model S)
    (hm : Stochastic M) (ha : Absorbing M) (hd : (systemMatrix M).det ≠ 0) :
    synthesize M = some (candidate M) := by
  simp [synthesize, candidate_checked M hm ha hd]

theorem solution_unique (M : FiniteDrift.Model S) (hd : (systemMatrix M).det ≠ 0)
    (f : S → ℚ) (he : Equations M f) : f = potential M := by
  have hu : IsUnit (systemMatrix M) :=
    (Matrix.isUnit_iff_isUnit_det (systemMatrix M)).mpr (isUnit_iff_ne_zero.mpr hd)
  apply Matrix.mulVec_injective_iff_isUnit.mpr hu
  rw [(matrix_equations_iff M f).mpr he, potential_solves M hd]

/-- Accessibility uses strictly positive transition mass, not merely allowed updates. -/
def ReachesGood (M : FiniteDrift.Model S) (s : S) : Prop :=
  ∃ g, M.good g = true ∧ Relation.ReflTransGen (fun a b => 0 < M.transition a b) s g

def Accessible (M : FiniteDrift.Model S) : Prop := ∀ s, ReachesGood M s

def Harmonic (M : FiniteDrift.Model S) (f : S → ℚ) : Prop :=
  (∀ s, M.good s = true → f s = 0) ∧
  ∀ s, M.good s = false → f s = ∑ t, M.transition s t * f t

theorem good_reachesGood (M : FiniteDrift.Model S) (s : S) (hs : M.good s = true) :
    ReachesGood M s := ⟨s, hs, Relation.ReflTransGen.refl⟩

theorem reachesGood_of_step (M : FiniteDrift.Model S) (s t : S)
    (he : 0 < M.transition s t) (hr : ReachesGood M t) : ReachesGood M s := by
  obtain ⟨g, hg, hp⟩ := hr
  exact ⟨g, hg, hp.head he⟩

theorem matrix_harmonic_iff (M : FiniteDrift.Model S) (f : S → ℚ) :
    systemMatrix M *ᵥ f = 0 ↔ Harmonic M f := by
  constructor
  · intro he
    constructor
    · intro s hs
      have hh := congrFun he s
      simpa [systemMatrix_mulVec, hs] using hh
    · intro s hs
      have hh := congrFun he s
      simp only [systemMatrix_mulVec, hs, Bool.false_eq_true, ↓reduceIte,
        Pi.zero_apply] at hh
      linarith
  · intro he
    funext s
    rw [systemMatrix_mulVec]
    cases hs : M.good s
    · have hh := he.2 s hs
      simp only [Bool.false_eq_true, ↓reduceIte, Pi.zero_apply]
      linarith
    · simpa using he.1 s hs

/-- A harmonic minimum propagates along every positive-mass edge. -/
theorem minimum_step (M : FiniteDrift.Model S) (hm : Stochastic M)
    (f : S → ℚ) (c : ℚ) (hmin : ∀ u, c ≤ f u) (s t : S)
    (hs : f s = c) (hh : f s = ∑ u, M.transition s u * f u)
    (hedge : 0 < M.transition s t) : f t = c := by
  have hz : ∑ u, M.transition s u * (f u - c) = 0 := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hm.2 s, one_mul, ← hh, hs, sub_self]
  have hn (u : S) : 0 ≤ M.transition s u * (f u - c) :=
    mul_nonneg (hm.1 s u) (sub_nonneg.mpr (hmin u))
  have ht := Finset.single_le_sum (fun u _ => hn u) (Finset.mem_univ t)
  rw [hz] at ht
  have htc := hmin t
  nlinarith

theorem harmonic_nonnegative (M : FiniteDrift.Model S) (hm : Stochastic M)
    (hr : Accessible M) (f : S → ℚ) (he : Harmonic M f) (s : S) : 0 ≤ f s := by
  by_contra hn
  have hs : f s < 0 := lt_of_not_ge hn
  obtain ⟨m, _, hmin⟩ := Finset.exists_min_image Finset.univ f ⟨s, Finset.mem_univ s⟩
  have hmn : f m < 0 := lt_of_le_of_lt (hmin s (Finset.mem_univ s)) hs
  obtain ⟨g, hg, hp⟩ := hr m
  have hprop : f g = f m := by
    clear hg
    induction hp with
    | refl => rfl
    | @tail b c hp hedge ih =>
      have hb : M.good b = false := by
        cases hgb : M.good b
        · rfl
        · have hz := he.1 b hgb
          linarith
      exact minimum_step M hm f (f m) (fun u => hmin u (Finset.mem_univ u))
        b c ih (he.2 b hb) hedge
  have hz := he.1 g hg
  linarith

theorem harmonic_neg (M : FiniteDrift.Model S) (f : S → ℚ) (he : Harmonic M f) :
    Harmonic M (-f) := by
  constructor
  · intro s hs
    simp [he.1 s hs]
  · intro s hs
    simpa only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib] using congrArg Neg.neg (he.2 s hs)

theorem harmonic_zero (M : FiniteDrift.Model S) (hm : Stochastic M)
    (hr : Accessible M) (f : S → ℚ) (he : Harmonic M f) : f = 0 := by
  funext s
  have hp := harmonic_nonnegative M hm hr f he s
  have hn := harmonic_nonnegative M hm hr (-f) (harmonic_neg M f he) s
  change 0 ≤ -f s at hn
  change f s = 0
  linarith

theorem matrix_injective (M : FiniteDrift.Model S) (hm : Stochastic M)
    (hr : Accessible M) : Function.Injective (systemMatrix M).mulVec := by
  intro f g heq
  have hz : systemMatrix M *ᵥ (f - g) = 0 := by
    rw [Matrix.mulVec_sub, heq, sub_self]
  have hh := harmonic_zero M hm hr (f - g) ((matrix_harmonic_iff M _).mp hz)
  exact sub_eq_zero.mp hh

theorem det_ne_zero_of_accessible (M : FiniteDrift.Model S) (hm : Stochastic M)
    (hr : Accessible M) : (systemMatrix M).det ≠ 0 := by
  apply isUnit_iff_ne_zero.mp
  apply (Matrix.isUnit_iff_isUnit_det (systemMatrix M)).mp
  exact Matrix.mulVec_injective_iff_isUnit.mp (matrix_injective M hm hr)

/-- Global drift acceptance rules out a closed set of inaccessible bad states. -/
theorem checked_accessible (M : FiniteDrift.Model S) (W : FiniteDrift.Witness S)
    (hc : FiniteDrift.check M W = true) : Accessible M := by
  classical
  intro s
  by_contra hs
  let U : Finset S := Finset.univ.filter (fun u => ¬ ReachesGood M u)
  have hsU : s ∈ U := by simp [U, hs]
  obtain ⟨m, hmU, hmin⟩ := Finset.exists_min_image U W.potential ⟨s, hsU⟩
  have hm : ¬ ReachesGood M m := (Finset.mem_filter.mp hmU).2
  have hbad : M.good m = false := Bool.eq_false_iff.mpr (fun hg => hm (good_reachesGood M m hg))
  have hterm (t : S) : M.transition m t * W.potential m ≤ M.transition m t * W.potential t := by
    by_cases hp : 0 < M.transition m t
    · have ht : ¬ ReachesGood M t := fun hr => hm (reachesGood_of_step M m t hp hr)
      exact mul_le_mul_of_nonneg_left (hmin t (by simp [U, ht])) hp.le
    · have hz : M.transition m t = 0 := le_antisymm (le_of_not_gt hp)
        (FiniteDrift.transition_nonnegative M W hc m t)
      simp [hz]
  have hsum : W.potential m ≤ FiniteDrift.localExpectation M W m := by
    calc
      W.potential m = ∑ t, M.transition m t * W.potential m := by
        rw [← Finset.sum_mul, FiniteDrift.transition_normalized M W hc m, one_mul]
      _ ≤ _ := Finset.sum_le_sum (fun t _ => hterm t)
  have hd := FiniteDrift.local_decrease M W hc m
  have hp := FiniteDrift.delta_positive M W hc
  simp only [hbad, Bool.false_eq_true, ↓reduceIte] at hd
  linarith

theorem det_ne_zero_iff_accessible (M : FiniteDrift.Model S)
    (hm : Stochastic M) (ha : Absorbing M) :
    (systemMatrix M).det ≠ 0 ↔ Accessible M :=
  ⟨fun hd => checked_accessible M _ (candidate_checked M hm ha hd),
    det_ne_zero_of_accessible M hm⟩

theorem candidate_checked_iff_accessible (M : FiniteDrift.Model S)
    (hm : Stochastic M) (ha : Absorbing M) :
    FiniteDrift.check M (candidate M) = true ↔ Accessible M :=
  ⟨checked_accessible M _, fun hr => candidate_checked M hm ha (det_ne_zero_of_accessible M hm hr)⟩

theorem synthesize_complete (M : FiniteDrift.Model S)
    (hm : Stochastic M) (ha : Absorbing M) (hr : Accessible M) :
    synthesize M = some (candidate M) :=
  synthesize_eq_some_candidate M hm ha (det_ne_zero_of_accessible M hm hr)

theorem synthesize_iff_accessible (M : FiniteDrift.Model S)
    (hm : Stochastic M) (ha : Absorbing M) :
    (∃ W, synthesize M = some W) ↔ Accessible M := by
  constructor
  · rintro ⟨W, hW⟩
    exact checked_accessible M W (synthesize_sound M W hW)
  · intro hr
    exact ⟨candidate M, synthesize_complete M hm ha hr⟩

theorem checked_witness_iff_accessible (M : FiniteDrift.Model S)
    (hm : Stochastic M) (ha : Absorbing M) :
    (∃ W, FiniteDrift.check M W = true) ↔ Accessible M := by
  constructor
  · rintro ⟨W, hW⟩
    exact checked_accessible M W hW
  · intro hr
    exact ⟨candidate M, (candidate_checked_iff_accessible M hm ha).mpr hr⟩

theorem synthesize_none_iff_not_accessible (M : FiniteDrift.Model S)
    (hm : Stochastic M) (ha : Absorbing M) :
    synthesize M = none ↔ ¬ Accessible M := by
  constructor
  · intro hn hr
    have hs := synthesize_complete M hm ha hr
    rw [hn] at hs
    contradiction
  · intro hn
    cases hs : synthesize M with
    | none => rfl
    | some W =>
      exact False.elim (hn (checked_accessible M W (synthesize_sound M W hs)))

/-- This excludes a global witness for this kernel, not repair under another policy. -/
theorem synthesize_none_no_global_witness (M : FiniteDrift.Model S)
    (hm : Stochastic M) (ha : Absorbing M) (hn : synthesize M = none) :
    ¬ ∃ W, FiniteDrift.check M W = true := by
  intro hw
  exact (synthesize_none_iff_not_accessible M hm ha).mp hn
    ((checked_witness_iff_accessible M hm ha).mp hw)

end FinitePotential

#check @FinitePotential.systemMatrix_mulVec
#check @FinitePotential.matrix_equations_iff
#check @FinitePotential.potential_solves
#check @FinitePotential.potential_equations
#check @FinitePotential.solution_nonnegative
#check @FinitePotential.solution_checked
#check @FinitePotential.candidate_checked
#check @FinitePotential.synthesize_sound
#check @FinitePotential.synthesize_eq_some_candidate
#check @FinitePotential.solution_unique
#check @FinitePotential.good_reachesGood
#check @FinitePotential.reachesGood_of_step
#check @FinitePotential.matrix_harmonic_iff
#check @FinitePotential.minimum_step
#check @FinitePotential.harmonic_nonnegative
#check @FinitePotential.harmonic_neg
#check @FinitePotential.harmonic_zero
#check @FinitePotential.matrix_injective
#check @FinitePotential.det_ne_zero_of_accessible
#check @FinitePotential.checked_accessible
#check @FinitePotential.det_ne_zero_iff_accessible
#check @FinitePotential.candidate_checked_iff_accessible
#check @FinitePotential.synthesize_complete
#check @FinitePotential.synthesize_iff_accessible
#check @FinitePotential.checked_witness_iff_accessible
#check @FinitePotential.synthesize_none_iff_not_accessible
#check @FinitePotential.synthesize_none_no_global_witness
