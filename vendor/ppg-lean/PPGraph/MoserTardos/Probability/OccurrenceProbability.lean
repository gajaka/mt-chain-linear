/-
  PPGraphMoserTardosOccurrenceProbability.lean

  Step 3: bound the occurrence probability of a fixed canonical witness
  by its tree weight. If the shape occurs, one realized raw τC tree is
  fixed once as its representative. Canonical check invariance then
  transports every occurrence to that representative's check event.

  The representative is fixed before applying the product-measure
  theorem; it does not vary with the sample being integrated.
-/

module

public import PPGraph.MoserTardos.Witness.Occurrence
public import PPGraph.MoserTardos.Witness.CheckBridge
public import PPGraph.MoserTardos.Witness.CheckShape
public import PPGraph.MoserTardos.Probability.ProbabilityGeneral
public import Mathlib.Basic.ENNReal.BigOperators

@[expose] public section

set_option autoImplicit false

open MeasureTheory Classical
open scoped NNReal ENNReal

variable {V : Type} [DecidableEq V] {S : VarSpaces V} {ι : Type}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The canonical witness has the same weight as its original
    address-indexed τC tree, with node multiplicities preserved. -/
theorem randomInitWitness_weight_eq_prod (P : MTProcess S ι) (p : ι → ℝ≥0)
    (ω : LogSpace S) (s : ℕ) :
    (randomInitWitness P ω s).weight p =
      ∏ w ∈ (τC P (shiftedC P (initialStateFromLog ω) ω) (s + 1)).dom,
        p ((τC P (shiftedC P (initialStateFromLog ω) ω) (s + 1)).lab w) := by
  have hraw := τC_toWTree_wellFormed_proper P
    (shiftedC P (initialStateFromLog ω) ω) (s + 1)
  have hcanonical := WTree.canonicalize_mem_wtreesUpTo P p
    ((τC P (shiftedC P (initialStateFromLog ω) ω) (s + 1)).toWTree [])
    hraw.2.1 hraw.2.2.1
  calc
    (randomInitWitness P ω s).weight p =
        ((τC P (shiftedC P (initialStateFromLog ω) ω) (s + 1)).toWTree []).weight p :=
      hcanonical.2.1
    _ = _ := GrowingTree.toWTree_weight_eq_prod _
      (τC_valid P (shiftedC P (initialStateFromLog ω) ω) (s + 1)) p
      (τC_root_mem P (shiftedC P (initialStateFromLog ω) ω) (s + 1))

/-- Any shape that occurs lies in the canonical finite-depth family.
    The enumeration counts each sibling ordering only once. -/
theorem witnessOccurrence_nonempty_mem_wtreesUpTo (P : MTProcess S ι)
    (α : ι) (U : WTree ι) (hocc : (witnessOccurrence P α U).Nonempty) :
    ∃ D : ℕ, U ∈ wtreesUpTo P D α := by
  obtain ⟨ω, s, hs, hshape⟩ := hocc
  have hraw := τC_toWTree_wellFormed_proper P
    (shiftedC P (initialStateFromLog ω) ω) (s + 1)
  have hcanonical := WTree.canonicalize_mem_wtreesUpTo P (fun _ => 0)
    ((τC P (shiftedC P (initialStateFromLog ω) ω) (s + 1)).toWTree [])
    hraw.2.1 hraw.2.2.1
  have hlabel :
      ((τC P (shiftedC P (initialStateFromLog ω) ω) (s + 1)).toWTree []).label = α :=
    hraw.1.trans ((shiftedC_succ P (initialStateFromLog ω) ω s).trans hs.2)
  have hcanonicalShape : WTree.canonicalize
      ((τC P (shiftedC P (initialStateFromLog ω) ω) (s + 1)).toWTree []) = U := hshape
  refine ⟨((τC P (shiftedC P (initialStateFromLog ω) ω) (s + 1)).toWTree []).depth, ?_⟩
  rw [← hcanonicalShape, ← hlabel]
  exact hcanonical.2.2

/-- Fix one raw witness whose canonical shape is U. Every occurrence
    of U passes this same fixed representative's check on its own log. -/
theorem witnessOccurrence_subset_τCheck_of_witness (P : MTProcess S ι)
    (α : ι) (U : WTree ι) (ωrep : LogSpace S) (srep : ℕ)
    (hrep : randomInitWitness P ωrep srep = U) :
    witnessOccurrence P α U ⊆
      {ω | τCheck P
        (τC P (shiftedC P (initialStateFromLog ωrep) ωrep) (srep + 1)) ω} := by
  intro ω hω
  obtain ⟨s, hs, hshape⟩ := hω
  have hpass := τCheck_holds_of_randomInit_trajectory P ω (s + 1) (by omega) hs.1
  have hraw := τC_toWTree_wellFormed_proper P
    (shiftedC P (initialStateFromLog ω) ω) (s + 1)
  have hrepRaw := τC_toWTree_wellFormed_proper P
    (shiftedC P (initialStateFromLog ωrep) ωrep) (srep + 1)
  have heq :
      WTree.canonicalize
          ((τC P (shiftedC P (initialStateFromLog ω) ω) (s + 1)).toWTree []) =
        WTree.canonicalize
          ((τC P (shiftedC P (initialStateFromLog ωrep) ωrep) (srep + 1)).toWTree []) :=
    hshape.trans hrep.symm
  apply (τC_tauCheck_iff_WTree_tauCheck P
    (shiftedC P (initialStateFromLog ωrep) ωrep) (srep + 1) ω).mpr
  apply (WTree.tauCheck_congr_of_canonicalize_eq P ω _ _
    hraw.2.2.1 hrepRaw.2.2.1 heq).mp
  exact (τC_tauCheck_iff_WTree_tauCheck P
    (shiftedC P (initialStateFromLog ω) ω) (s + 1) ω).mp hpass

/-- A fixed canonical witness occurs with probability at most its
    tree weight. The base probabilities may be replaced by upper bounds p. -/
theorem logMeasure_witnessOccurrence_le_weight [Fintype V]
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i))
    (p : ι → ℝ≥0)
    (hp : ∀ i, Measure.pi (fun v => S.measure v) (P.bad i) ≤ (p i : ℝ≥0∞))
    (α : ι) (U : WTree ι) :
    logMeasure S (witnessOccurrence P α U) ≤ (U.weight p : ℝ≥0∞) := by
  by_cases hocc : (witnessOccurrence P α U).Nonempty
  · obtain ⟨ωrep, srep, hsrep, hrep⟩ := hocc
    let C : ℕ → ι := shiftedC P (initialStateFromLog ωrep) ωrep
    have hsub : witnessOccurrence P α U ⊆ {ω | τCheck P (τC P C (srep + 1)) ω} :=
      witnessOccurrence_subset_τCheck_of_witness P α U ωrep srep hrep
    have hweight : U.weight p =
        ∏ w ∈ (τC P C (srep + 1)).dom, p ((τC P C (srep + 1)).lab w) := by
      have h := randomInitWitness_weight_eq_prod P p ωrep srep
      rw [hrep] at h
      exact h
    calc
      logMeasure S (witnessOccurrence P α U) ≤
          logMeasure S {ω | τCheck P (τC P C (srep + 1)) ω} := measure_mono hsub
      _ = ∏ w ∈ (τC P C (srep + 1)).dom,
          Measure.pi (fun v => S.measure v) (P.bad ((τC P C (srep + 1)).lab w)) :=
        logMeasure_τCheck_eq_prod_p_of_τC P hbad C (srep + 1)
      _ ≤ ∏ w ∈ (τC P C (srep + 1)).dom,
          (p ((τC P C (srep + 1)).lab w) : ℝ≥0∞) :=
        Finset.prod_le_prod (fun w _ => hp ((τC P C (srep + 1)).lab w))
      _ = (U.weight p : ℝ≥0∞) := by
        rw [← ENNReal.ofNNReal_finsetProd, ← hweight]
  · rw [Set.not_nonempty_iff_eq_empty.mp hocc, measure_empty]
    exact bot_le

-- -------------------------------------------------------------------
-- Verification
-- -------------------------------------------------------------------

#check @randomInitWitness_weight_eq_prod
#check @witnessOccurrence_nonempty_mem_wtreesUpTo
#check @witnessOccurrence_subset_τCheck_of_witness
#check @logMeasure_witnessOccurrence_le_weight
